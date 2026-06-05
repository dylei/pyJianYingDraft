"""
爆款智剪 — 左侧草稿列表，右侧详情与时间轴预览（轨道与片段按时间排列）；
明文 draft_content.json 下可在时间轴音视频片段上右键「替换素材…」弹窗替换（按原片段时长截断或缩短）；
Windows 下可将单个素材文件或素材文件夹从资源管理器拖到时间轴片段彩色条上，效果与弹窗中保存「单个文件」或「素材目录」一致（需安装 windnd）；
每个导出槽位仅保留最后一次配置：「单个文件」与「素材目录」互斥，后保存的生效；可设新素材截取起点（片头 / 随机 / 自定义秒）。
下拉「(默认)」表示使用本稿槽位工作台（working_pool），与命名预设一样可编辑并持久化到本地；旧版曾显示为「(保持原样)」，程序会自动识别。命名预设下改动会写回该预设。「导出生成子草稿」默认勾选：导出 MP4 时复制为子草稿并在子稿上套用预设，底稿不动；取消勾选时会在**每次导出前**对当前草稿临时套用槽位/花字/贴纸配置再导出，随后**自动还原** draft_content.json，不增加子文件夹（与「生成草稿」按钮无关，该按钮仍会复制子稿）。花字/贴纸请在时间轴点轨道名或片段后使用「替换…」配置。
父子关系索引与导出 MP4 区选项（备份、字幕、子草稿、条数、文件名前缀等）记忆在 %LOCALAPPDATA%\\pyJianYingDraft_browser\\（export_mp4_ui_preference.json），草稿文件夹仍在剪映根目录下平铺。
音频槽选视频时自动用 ffmpeg 抽音轨为 MP3。
运行: pip install customtkinter Send2Trash requests windnd && python draft_browser_app.py
"""

from __future__ import annotations

import hashlib
import json
import copy
import os
from collections import OrderedDict
import random
import uuid
import re
import time
import shutil
import subprocess
import sys
import threading
import tkinter as tk
import tkinter.font as tkfont
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple

try:
    from send2trash import send2trash as _send2trash_impl
except ImportError:
    _send2trash_impl = None

_TUTORIAL_MEDIA = ("audio.mp3", "video.mp4", "sticker.gif")

_VIDEO_REPLACE_EXTS = frozenset({".mp4", ".m4v", ".mov", ".mkv", ".avi", ".gif", ".webm"})
# 音频槽也可选常见视频后缀（走 ffmpeg 抽音轨）
_AUDIO_REPLACE_EXTS = frozenset(
    {".mp3", ".wav", ".m4a", ".aac", ".flac", ".mp4", ".m4v", ".mov", ".mkv", ".avi", ".webm"}
)


def list_replace_candidates_in_dir(dir_path: str, track_type: str) -> List[str]:
    """目录内可作为替换候选的文件路径，按文件名（不区分大小写）排序。"""
    if not dir_path or not os.path.isdir(dir_path):
        return []
    exts = _VIDEO_REPLACE_EXTS if track_type == "video" else _AUDIO_REPLACE_EXTS
    found: List[str] = []
    try:
        for name in os.listdir(dir_path):
            fp = os.path.join(dir_path, name)
            if not os.path.isfile(fp):
                continue
            ext = os.path.splitext(name)[1].lower()
            if ext in exts:
                found.append(fp)
    except OSError:
        return []
    found.sort(key=lambda p: os.path.basename(p).lower())
    return found


@dataclass
class MediaSegmentRef:
    """可替换的音视频轨道片段（用于界面与 replace_material_by_seg）。"""

    track_type: str  # "video" | "audio"
    track_name: str
    segment_index: int
    combo_label: str
    current_path: str
    material_id: str
    # draft 轨道 id（JSON track.id），空名轨道区分与配置键稳定用
    track_id: str = ""
    # 同类型导入轨道中的顺序下标（与 ScriptFile.get_imported_track 的 index 一致，0 为最下层）
    track_type_index: int = 0
    # draft_content「tracks」数组中第几条音视频轨道（仅 video/audio），与时间轴 dict 引用对齐用
    media_ordinal: int = -1


@dataclass
class StyleSegmentRef:
    """可配置花字/贴纸替换的字幕或贴纸轨道片段（与时间轴右键、导出槽位配置联动）。"""

    track_type: str  # "text" | "sticker"
    track_name: str
    segment_index: int
    combo_label: str
    material_id: str
    track_id: str = ""
    current_resource_id: str = ""


STYLE_KIND_TEXT_EFFECT = "text_effect"
STYLE_KIND_STICKER = "sticker"
STYLE_MODE_RANDOM = "random"
STYLE_MODE_FIXED = "fixed"


def segment_export_pool_key(draft_name: str, ref: MediaSegmentRef) -> str:
    """按草稿名 + 轨道 id + 片段下标定位（轨道名为空时也不冲突）。无 track_id 时回退旧格式。"""
    tid = (ref.track_id or "").strip()
    if tid:
        return f"{draft_name}\0{tid}\0{ref.segment_index}"
    return f"{draft_name}\0{ref.track_type}\0{ref.track_name}\0{ref.track_type_index}\0{ref.segment_index}"


def segment_style_pool_key(draft_name: str, ref: StyleSegmentRef) -> str:
    """花字/贴纸槽位键：与音视频槽同规则（草稿 + 轨道 id + 片段下标）。"""
    tid = (ref.track_id or "").strip()
    if tid:
        return f"{draft_name}\0{tid}\0{ref.segment_index}"
    return f"{draft_name}\0{ref.track_type}\0{ref.track_name}\0{ref.segment_index}"


VIDEO_REPLACE_SOURCE_HEAD = "head"
VIDEO_REPLACE_SOURCE_RANDOM = "random"
VIDEO_REPLACE_SOURCE_CUSTOM = "custom"


def normalize_replace_source_start_mode(raw: Any) -> str:
    s = str(raw or "").strip().lower()
    if s in (VIDEO_REPLACE_SOURCE_RANDOM, "随机"):
        return VIDEO_REPLACE_SOURCE_RANDOM
    if s in (VIDEO_REPLACE_SOURCE_CUSTOM, "自定义"):
        return VIDEO_REPLACE_SOURCE_CUSTOM
    return VIDEO_REPLACE_SOURCE_HEAD


def parse_replace_source_start_sec(raw: Any) -> float:
    try:
        return float(str(raw).strip().replace(",", "."))
    except (TypeError, ValueError):
        return 0.0


def segment_replace_status_lines(
    draft_name: str, ref: Optional[MediaSegmentRef], pool: Dict[str, Any]
) -> List[str]:
    """根据本地 segment_export_pool 生成「替换目录/替换文件/花字/贴纸」说明行（用于时间轴下方信息区）。"""
    out: List[str] = []
    if not ref or not (draft_name or "").strip():
        return out
    k = segment_export_pool_key(draft_name.strip(), ref)
    cfg = pool.get(k) or {}
    if not isinstance(cfg, dict):
        return out
    d = str(cfg.get("dir", "") or "").strip()
    rf = str(cfg.get("replace_file", "") or "").strip()
    if d:
        od = cfg.get("order", "random")
        oz = "顺序（按文件名）" if od == "sequential" else "随机"
        out.append(f"替换目录：{d}（导出时选取：{oz}）")
    if rf:
        out.append(f"替换文件：{rf}")
    sm = normalize_replace_source_start_mode(cfg.get("replace_source_start_mode"))
    if (d or rf) and sm != VIDEO_REPLACE_SOURCE_HEAD:
        if sm == VIDEO_REPLACE_SOURCE_RANDOM:
            out.append("素材起点：随机（整秒）")
        else:
            out.append(f"素材起点：自定义 {parse_replace_source_start_sec(cfg.get('replace_source_start_sec')):g} 秒")
    return out


_MATERIAL_EXPORT_POOL_KEYS = frozenset(
    {
        "dir",
        "order",
        "replace_file",
        "replace_source_start_mode",
        "replace_source_start_sec",
    }
)


def clear_material_keys_from_segment_export_pool_entry(raw: Any) -> Optional[Dict[str, Any]]:
    """从槽位配置移除音视频素材替换项；若同槽还有花字/贴纸配置则保留。"""
    if not isinstance(raw, dict):
        return None
    style_piece = normalize_style_pool_config(raw)
    if style_piece:
        return dict(style_piece)
    if any(k in raw for k in _MATERIAL_EXPORT_POOL_KEYS):
        return None
    return None


def normalize_style_pool_config(raw: Any) -> Optional[Dict[str, Any]]:
    if not isinstance(raw, dict):
        return None
    kind = str(raw.get("style_kind") or "").strip()
    if kind not in (STYLE_KIND_TEXT_EFFECT, STYLE_KIND_STICKER):
        return None
    mode = str(raw.get("style_mode") or STYLE_MODE_RANDOM).strip()
    if mode not in (STYLE_MODE_RANDOM, STYLE_MODE_FIXED):
        mode = STYLE_MODE_RANDOM
    rid = str(raw.get("style_resource_id") or "").strip()
    if mode == STYLE_MODE_FIXED and not rid:
        return None
    out: Dict[str, Any] = {"style_kind": kind, "style_mode": mode}
    if mode == STYLE_MODE_FIXED:
        out["style_resource_id"] = rid
    return out


def segment_style_status_lines(
    draft_name: str, ref: Optional[StyleSegmentRef], pool: Dict[str, Any]
) -> List[str]:
    out: List[str] = []
    if not ref or not (draft_name or "").strip():
        return out
    k = segment_style_pool_key(draft_name.strip(), ref)
    cfg = normalize_style_pool_config(pool.get(k))
    if not cfg:
        return out
    kind = cfg.get("style_kind")
    mode = cfg.get("style_mode")
    rid = str(cfg.get("style_resource_id") or "").strip()
    if kind == STYLE_KIND_TEXT_EFFECT:
        if mode == STYLE_MODE_FIXED and rid:
            out.append(f"花字：指定 id {rid}")
        else:
            out.append("花字：导出时从池随机")
    elif kind == STYLE_KIND_STICKER:
        if mode == STYLE_MODE_FIXED and rid:
            out.append(f"贴纸：指定 id {rid}")
        else:
            out.append("贴纸：导出时从池随机")
    return out


def segment_has_style_config(
    draft_name: str, ref: Optional[StyleSegmentRef], pool: Dict[str, Any]
) -> bool:
    return bool(segment_style_status_lines(draft_name, ref, pool))


def segment_export_pool_enforce_exclusive_sources(pool: Optional[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    """每个槽只保留一种来源：单文件与素材目录互斥。

    写入 UI 已保证「最后一次」只留一类；若历史数据仍并存，与导出逻辑一致保留 replace_file 并去掉 dir/order。
    """
    if not isinstance(pool, dict):
        return {}
    out: Dict[str, Dict[str, Any]] = {}
    for k, v in pool.items():
        if not isinstance(v, dict):
            continue
        d = str(v.get("dir", "") or "").strip()
        rf = str(v.get("replace_file", "") or "").strip()
        piece = dict(v)
        if rf and d:
            piece.pop("dir", None)
            piece.pop("order", None)
        out[str(k)] = piece
    return out


def segment_has_replace_config(
    draft_name: str, ref: Optional[MediaSegmentRef], pool: Dict[str, Any]
) -> bool:
    return bool(segment_replace_status_lines(draft_name, ref, pool))


def draft_has_any_segment_export_pool(draft_name: str, pool: Optional[Dict[str, Any]]) -> bool:
    """该草稿在 segment_export_pool 中是否配置了替换目录/文件或花字/贴纸槽（导出 MP4 时可套用）。"""
    dn = (draft_name or "").strip()
    if not dn or not isinstance(pool, dict):
        return False
    pfx = dn + "\0"
    for sk, sv in pool.items():
        if not isinstance(sk, str) or not sk.startswith(pfx):
            continue
        if not isinstance(sv, dict):
            continue
        if str(sv.get("dir", "") or "").strip() or str(sv.get("replace_file", "") or "").strip():
            return True
        if normalize_style_pool_config(sv):
            return True
    return False


def _segment_export_pool_has_saveable_config(seg: Optional[Dict[str, Any]]) -> bool:
    """槽位是否含可持久化配置：素材目录/文件，或花字/贴纸随机/指定 id。"""
    if not isinstance(seg, dict):
        return False
    for sv in seg.values():
        if not isinstance(sv, dict):
            continue
        if str(sv.get("dir", "") or "").strip() or str(sv.get("replace_file", "") or "").strip():
            return True
        if normalize_style_pool_config(sv):
            return True
    return False


def _segment_export_pool_for_preset_disk(seg_in: Dict[str, Any]) -> Dict[str, Dict[str, Any]]:
    """写入命名预设时保留素材目录/单文件与花字/贴纸槽（供导出/生成子稿套用）。"""
    out: Dict[str, Dict[str, Any]] = {}
    for sk, sv in (seg_in or {}).items():
        if not isinstance(sv, dict):
            continue
        piece: Dict[str, Any] = {}
        d = str(sv.get("dir", "") or "").strip()
        if d:
            od = sv.get("order", "random")
            if od not in ("random", "sequential"):
                od = "random"
            piece["dir"] = d
            piece["order"] = od
        rf = str(sv.get("replace_file", "") or "").strip()
        if rf:
            piece["replace_file"] = rf
        style_piece = normalize_style_pool_config(sv)
        if style_piece:
            piece.update(style_piece)
        if piece:
            sm = normalize_replace_source_start_mode(sv.get("replace_source_start_mode"))
            piece["replace_source_start_mode"] = sm
            piece["replace_source_start_sec"] = (
                float(parse_replace_source_start_sec(sv.get("replace_source_start_sec")))
                if sm == VIDEO_REPLACE_SOURCE_CUSTOM
                else 0.0
            )
            out[str(sk)] = piece
    return out


def _app_dir() -> Path:
    return Path(__file__).resolve().parent


def _repo_root() -> Path:
    """pyJianYingDraft 仓库根（内含 pyJianYingDraft 包与 readme_assets）。"""
    if getattr(sys, "frozen", False):
        return Path(getattr(sys, "_MEIPASS", _app_dir()))
    here = _app_dir()
    if (here / "pyJianYingDraft" / "__init__.py").is_file():
        return here
    nested = here / "pyJianYingDraft"
    if (nested / "pyJianYingDraft" / "__init__.py").is_file():
        return nested
    return here


def _ensure_local_pyjianyingdraft_on_path() -> None:
    """优先使用本仓库里的包，避免 site-packages 中旧版 wheel 缺少 IntroType 等导出。"""
    if getattr(sys, "frozen", False):
        return
    root = str(_repo_root())
    if root not in sys.path:
        sys.path.insert(0, root)
    for key in list(sys.modules):
        if key == "pyJianYingDraft" or key.startswith("pyJianYingDraft."):
            del sys.modules[key]


def tutorial_assets_dir() -> Path:
    return _repo_root() / "readme_assets" / "tutorial"


def check_tutorial_assets() -> List[str]:
    """返回缺失的例程文件名列表（空表示齐全）。"""
    d = tutorial_assets_dir()
    return [f for f in _TUTORIAL_MEDIA if not (d / f).is_file()]


def generate_sample_draft(draft_root: str, draft_name: str, *, allow_replace: bool) -> None:
    """与 demo.py 相同：在指定草稿根目录下生成一份可明文打开的示例草稿。"""
    _ensure_local_pyjianyingdraft_on_path()
    import pyJianYingDraft as draft
    from pyJianYingDraft.metadata import IntroType, TransitionType
    from pyJianYingDraft.time_util import trange, tim

    missing = check_tutorial_assets()
    if missing:
        raise FileNotFoundError(
            "缺少例程素材: " + ", ".join(missing) + f"\n目录应为: {tutorial_assets_dir()}"
        )

    tdir = tutorial_assets_dir()
    draft_folder = draft.DraftFolder(draft_root)
    script = draft_folder.create_draft(draft_name, 1920, 1080, allow_replace=allow_replace)

    script.add_track(draft.TrackType.audio).add_track(draft.TrackType.video).add_track(draft.TrackType.text)

    audio_segment = draft.AudioSegment(
        str(tdir / "audio.mp3"), trange("0s", "5s"), volume=0.6
    )
    audio_segment.add_fade("1s", "0s")

    video_segment = draft.VideoSegment(str(tdir / "video.mp4"), trange("0s", "4.2s"))
    video_segment.add_animation(IntroType.斜切)

    gif_material = draft.VideoMaterial(str(tdir / "sticker.gif"))
    gif_segment = draft.VideoSegment(gif_material, trange(video_segment.end, gif_material.duration))
    gif_segment.add_background_filling("blur", 0.0625)

    video_segment.add_transition(TransitionType.信号故障)

    script.add_segment(audio_segment).add_segment(video_segment).add_segment(gif_segment)

    text_segment = draft.TextSegment(
        "据说pyJianYingDraft效果还不错?",
        video_segment.target_timerange,
        font=draft.FontType.文轩体,
        style=draft.TextStyle(color=(1.0, 1.0, 0.0)),
        clip_settings=draft.ClipSettings(transform_y=-0.8),
    )
    text_segment.add_animation(draft.TextOutro.故障闪动, duration=tim("1s"))
    text_segment.add_bubble("361595", "6742029398926430728")
    text_segment.add_effect("7296357486490144036")
    script.add_segment(text_segment)

    script.save()


def _sanitize_draft_name(name: str) -> Optional[str]:
    name = name.strip()
    if not name or re.search(r'[<>:"/\\|?*]', name) or name in (".", ".."):
        return None
    return name


def _default_draft_roots() -> List[str]:
    roots: List[str] = []
    local = os.environ.get("LOCALAPPDATA", "")
    if local:
        roots.extend(
            [
                os.path.join(local, "JianyingPro", "User Data", "Projects", "com.lveditor.draft"),
                os.path.join(local, "CapCut", "User Data", "Projects", "com.lveditor.draft"),
            ]
        )
    return [p for p in roots if os.path.isdir(p)]


def _fmt_duration_us(us: Optional[int]) -> str:
    if not us:
        return "—"
    sec = us / 1_000_000.0
    if sec < 60:
        return f"{sec:.2f} 秒"
    m, s = divmod(sec, 60)
    h, m = divmod(int(m), 60)
    if h:
        return f"{h}:{m:02d}:{s:05.2f}"
    return f"{m}:{s:05.2f}"


def _safe_read_json(path: str) -> Optional[Dict[str, Any]]:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return None


def _write_draft_content_json(path: str, data: Dict[str, Any]) -> None:
    """将 ``draft_content.json`` 写回磁盘（UTF-8，带缩进），用于导出后还原底稿。"""
    parent = os.path.dirname(path)
    tmp = os.path.join(parent, f".draft_content_tmp_{os.getpid()}_{random.randint(0, 1_000_000_000)}.json")
    try:
        with open(tmp, "w", encoding="utf-8", newline="\n") as f:
            json.dump(data, f, ensure_ascii=False, indent=4)
        os.replace(tmp, path)
    finally:
        try:
            if os.path.isfile(tmp):
                os.remove(tmp)
        except OSError:
            pass


def _file_exists_nonempty(path: str) -> bool:
    try:
        return os.path.isfile(path) and os.path.getsize(path) > 0
    except OSError:
        return False


def _looks_like_jianying_encrypted(path: str) -> bool:
    """剪映专业版保存后常为密文，文件存在但首字符不是 JSON 的 { 或 [。"""
    if not _file_exists_nonempty(path):
        return False
    try:
        with open(path, "rb") as f:
            chunk = f.read(64)
    except OSError:
        return False
    stripped = chunk.lstrip()
    if not stripped:
        return False
    return stripped[0:1] not in (b"{", b"[")


@dataclass
class DraftSummary:
    folder_name: str
    folder_path: str
    meta_ok: bool
    content_ok: bool
    lines: List[str]
    content: Optional[Dict[str, Any]] = None


def summarize_draft(draft_dir: str) -> DraftSummary:
    name = os.path.basename(draft_dir.rstrip("\\/"))
    meta_path = os.path.join(draft_dir, "draft_meta_info.json")
    content_path = os.path.join(draft_dir, "draft_content.json")

    lines: List[str] = []
    meta = _safe_read_json(meta_path)
    content = _safe_read_json(content_path)

    lines.append("【基本信息】")
    lines.append(f"名称: {name}")
    lines.append(f"路径: {draft_dir}")

    if meta:
        lines.append(f"草稿 ID: {meta.get('draft_id', '—')}")
        lines.append(f"Meta 时长: {_fmt_duration_us(meta.get('tm_duration'))}")
    else:
        if _looks_like_jianying_encrypted(meta_path):
            lines.append("Meta: 文件存在，但内容不是明文 JSON（剪映专业版通常会在保存后加密 draft_meta_info.json）。")
        elif os.path.isfile(meta_path):
            lines.append("Meta: 无法解析为 JSON（格式异常或编码问题）。")
        else:
            lines.append("Meta: 未找到 draft_meta_info.json。")

    lines.append("")
    lines.append("【画布与时间线】")

    if not content:
        if _looks_like_jianying_encrypted(content_path):
            lines.append("draft_content.json: 文件存在，但已加密或二进制封装，本工具无法直接解析。")
            lines.append("")
            lines.append("【说明】")
            lines.append("· 在剪映里打开并保存过的草稿，往往会变成密文；只有未加密时的 JSON 才能列出轨道与素材路径。")
            lines.append("· 用 pyJianYingDraft 写好并保存后，若仅在资源管理器里查看、尚未经剪映改写，有时仍是明文。")
            lines.append("· 需要改素材时，可优先用库在「明文草稿」上改 draft_content.json，或用剪映导出/另存等官方流程。")
        elif os.path.isfile(content_path):
            lines.append("draft_content.json: 无法解析为 JSON。")
        else:
            lines.append("draft_content.json: 文件不存在。")
        return DraftSummary(name, draft_dir, meta is not None, False, lines, content=None)

    cc = content.get("canvas_config") or {}
    w, h = cc.get("width"), cc.get("height")
    fps = content.get("fps")
    dur = content.get("duration")
    lines.append(f"分辨率: {w} × {h}" if w and h else "分辨率: —")
    lines.append(f"帧率: {fps}" if fps is not None else "帧率: —")
    lines.append(f"时间线时长: {_fmt_duration_us(dur)}")

    plat = content.get("platform") or content.get("last_modified_platform") or {}
    if plat:
        lines.append(
            f"保存平台: {plat.get('app_version', '?')} ({plat.get('os', '?')}, {plat.get('app_source', '')})"
        )

    lines.append("")
    lines.append("【轨道】")
    tracks = content.get("tracks") or []
    if not tracks:
        lines.append("（无轨道）")
    else:
        for i, tr in enumerate(tracks):
            tname = tr.get("name", f"轨道{i + 1}")
            ttype = tr.get("type", "?")
            segs = tr.get("segments") or []
            lines.append(f"· {tname}  [{ttype}]  — {len(segs)} 个片段")

    mats = content.get("materials") or {}

    def collect_paths(key: str) -> List[str]:
        out: List[str] = []
        for item in mats.get(key) or []:
            if isinstance(item, dict):
                p = item.get("path")
                if p and isinstance(p, str) and p.strip():
                    out.append(p.replace("/", os.sep))
        return out

    vids = collect_paths("videos")
    auds = collect_paths("audios")

    lines.append("")
    lines.append("【本地素材路径】")
    lines.append("（明文草稿可在下方「替换素材」滚动区按槽位逐行替换音视频）")
    if vids:
        lines.append(f"— 视频素材 ({len(vids)}) —")
        lines.extend(f"  {p}" for p in vids)
    if auds:
        lines.append(f"— 音频素材 ({len(auds)}) —")
        lines.extend(f"  {p}" for p in auds)
    if not vids and not auds:
        lines.append("（未在 materials 中发现带 path 的视频/音频；可能为内置素材或结构不同）")

    return DraftSummary(name, draft_dir, meta is not None, True, lines, content=content)


def _fmt_tc_us(start_us: int, end_us: int) -> str:
    def part(us: int) -> str:
        s = us / 1_000_000.0
        m, sec = divmod(s, 60.0)
        if m >= 60:
            h, m = divmod(int(m), 60)
            return f"{h}:{int(m):02d}:{sec:05.2f}"
        return f"{int(m):02d}:{sec:05.2f}"

    return f"{part(start_us)} – {part(end_us)}"


def list_replaceable_media_segments_from_script(script: Any) -> List[MediaSegmentRef]:
    """从已加载的 ``ScriptFile`` 解析可替换音视频片段（与 ``load_template`` / ``load_from_parsed_json`` 均可）。"""
    _ensure_local_pyjianyingdraft_on_path()
    # 注意：本函数会先 _ensure_local_pyjianyingdraft_on_path() 并可能卸载重载 pyJianYingDraft，
    # 不得再用 isinstance(..., ImportedMediaTrack)，否则与 ScriptFile 加载时创建的轨道类对象不一致，导致列表恒为空。

    out: List[MediaSegmentRef] = []
    mats = script.imported_materials
    vi, ai = 0, 0
    media_ordinal = 0

    for tr in script.imported_tracks:
        tt = getattr(tr, "track_type", None)
        kind = getattr(tt, "name", "") if tt is not None else ""
        if kind not in ("video", "audio"):
            continue
        tix = vi if kind == "video" else ai
        if kind == "video":
            vi += 1
        else:
            ai += 1
        tid = str(getattr(tr, "track_id", "") or "")
        mat_key = "videos" if kind == "video" else "audios"
        for i, seg in enumerate(tr.segments):
            mid = seg.material_id
            info: Optional[Dict[str, Any]] = None
            for item in mats.get(mat_key) or []:
                if isinstance(item, dict) and item.get("id") == mid:
                    info = item
                    break
            path = ""
            if info:
                path = (info.get("path") or "").replace("/", os.sep)
            name_hint = os.path.basename(path) if path else mid[:8]
            t0, t1 = seg.target_timerange.start, seg.target_timerange.end
            label = f"[{kind}] {tr.name} · 片段{i + 1} · {_fmt_tc_us(t0, t1)} · {name_hint}"
            out.append(
                MediaSegmentRef(
                    track_type=kind,
                    track_name=tr.name,
                    segment_index=i,
                    combo_label=label,
                    current_path=path,
                    material_id=mid,
                    track_id=tid,
                    track_type_index=tix,
                    media_ordinal=media_ordinal,
                )
            )
        media_ordinal += 1
    return out


def list_replaceable_media_segments(content_json_path: str) -> List[MediaSegmentRef]:
    """从明文 draft_content.json 解析可替换的音视频片段列表。"""
    _ensure_local_pyjianyingdraft_on_path()
    from pyJianYingDraft.script_file import ScriptFile

    script = ScriptFile.load_template(content_json_path)
    return list_replaceable_media_segments_from_script(script)


def _text_effect_id_from_material(mat: Dict[str, Any]) -> str:
    snap = _extract_text_style_snapshot(mat)
    if snap and snap.get("effect_id"):
        return str(snap["effect_id"]).strip()
    return ""


def _sticker_resource_id_from_material(mat: Dict[str, Any]) -> str:
    return str(mat.get("resource_id") or mat.get("sticker_id") or "").strip()


def list_style_segments_from_content(content: Dict[str, Any]) -> List[StyleSegmentRef]:
    """从 draft_content 解析可配置花字/贴纸的文本与贴纸轨片段。"""
    out: List[StyleSegmentRef] = []
    if not isinstance(content, dict):
        return out
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    texts_by_id = {
        str(m.get("id")): m
        for m in (materials.get("texts") or [])
        if isinstance(m, dict) and m.get("id")
    }
    stickers_by_id = {
        str(m.get("id")): m
        for m in (materials.get("stickers") or [])
        if isinstance(m, dict) and m.get("id")
    }
    for tr in content.get("tracks") or []:
        if not isinstance(tr, dict):
            continue
        ttype = str(tr.get("type", "")).strip().lower()
        if ttype not in ("text", "sticker"):
            continue
        tid = str(tr.get("id") or "")
        nm_raw = tr.get("name", "")
        tname = "" if nm_raw is None else (nm_raw if isinstance(nm_raw, str) else str(nm_raw))
        tname = tname.strip()
        segs = tr.get("segments") or []
        for i, seg in enumerate(segs):
            if not isinstance(seg, dict):
                continue
            mid = str(seg.get("material_id") or "").strip()
            if not mid:
                continue
            trng = seg.get("target_timerange") or {}
            try:
                t0 = int(trng.get("start", 0))
                t1 = t0 + int(trng.get("duration", 0))
            except (TypeError, ValueError):
                t0, t1 = 0, 0
            if ttype == "text":
                mat = texts_by_id.get(mid) or {}
                cur_rid = _text_effect_id_from_material(mat)
                lab = _timeline_segment_label(seg, materials)
                label = f"[text] {tname} · 片段{i + 1} · {_fmt_tc_us(t0, t1)} · {lab}"
            else:
                mat = stickers_by_id.get(mid) or {}
                cur_rid = _sticker_resource_id_from_material(mat)
                hint = cur_rid[:16] if cur_rid else mid[:8]
                label = f"[sticker] {tname} · 片段{i + 1} · {_fmt_tc_us(t0, t1)} · {hint}"
            out.append(
                StyleSegmentRef(
                    track_type=ttype,
                    track_name=tname,
                    segment_index=i,
                    combo_label=label,
                    material_id=mid,
                    track_id=tid,
                    current_resource_id=cur_rid,
                )
            )
    return out


def find_ffmpeg() -> Optional[str]:
    """查找 ffmpeg 可执行文件：环境变量 FFMPEG → PATH → 本程序目录下 bin\\ffmpeg.exe。"""
    env = os.environ.get("FFMPEG", "").strip().strip('"')
    if env:
        if os.path.isfile(env):
            return env
        w = shutil.which(env)
        if w:
            return w
    w = shutil.which("ffmpeg")
    if w:
        return w
    here = Path(__file__).resolve().parent
    for candidate in (here / "bin" / "ffmpeg.exe", here / "tools" / "ffmpeg.exe"):
        if candidate.is_file():
            return str(candidate)
    return None


def find_ffplay() -> Optional[str]:
    """查找 ffplay（通常与 ffmpeg 同目录）。"""
    ff = find_ffmpeg()
    if ff:
        d = os.path.dirname(ff)
        for name in ("ffplay.exe", "ffplay"):
            p = os.path.join(d, name)
            if os.path.isfile(p):
                return p
    return shutil.which("ffplay")


def find_ffprobe() -> Optional[str]:
    """查找 ffprobe（通常与 ffmpeg 同目录）。"""
    ff = find_ffmpeg()
    if ff:
        d = os.path.dirname(ff)
        for name in ("ffprobe.exe", "ffprobe"):
            p = os.path.join(d, name)
            if os.path.isfile(p):
                return p
    return shutil.which("ffprobe")


def _ffmpeg_input_has_stream(path: str, stream: str) -> bool:
    """检测文件是否含 video/audio 流；失败时保守返回 False（audio）或 True（video）。"""
    path_abs = os.path.abspath(path)
    if not os.path.isfile(path_abs):
        return False
    fp = find_ffprobe()
    if fp:
        try:
            proc = subprocess.run(
                [
                    fp,
                    "-hide_banner",
                    "-loglevel",
                    "error",
                    "-select_streams",
                    f"{stream[0]}",
                    "-show_entries",
                    "stream=codec_type",
                    "-of",
                    "csv=p=0",
                    path_abs,
                ],
                capture_output=True,
                timeout=8,
            )
            out = (proc.stdout or b"").decode("utf-8", errors="replace").strip().lower()
            if proc.returncode == 0 and stream in out:
                return True
            if proc.returncode == 0 and not out:
                return False
        except Exception:
            pass
    ff = find_ffmpeg()
    if not ff:
        return stream == "video"
    try:
        proc = subprocess.run(
            [ff, "-hide_banner", "-loglevel", "error", "-i", path_abs],
            capture_output=True,
            timeout=8,
        )
        text = (proc.stderr or b"").decode("utf-8", errors="replace")
        if stream == "audio":
            return "Audio:" in text
        return "Video:" in text
    except Exception:
        return stream == "video"


def _media_has_video_track(path: str) -> bool:
    try:
        from pymediainfo import MediaInfo

        can = getattr(MediaInfo, "can_parse", None)
        if callable(can) and not can():
            return False
        info = MediaInfo.parse(os.path.abspath(path))
        return len(info.video_tracks) > 0
    except Exception:
        return False


def _media_has_audio_track(path: str) -> bool:
    try:
        from pymediainfo import MediaInfo

        can = getattr(MediaInfo, "can_parse", None)
        if callable(can) and not can():
            return True
        info = MediaInfo.parse(os.path.abspath(path))
        return len(info.audio_tracks) > 0
    except Exception:
        return False


def _media_maybe_has_audio(path: str) -> bool:
    """检测文件是否可能有音轨；不确定时仍尝试播放。"""
    if _media_has_audio_track(path):
        return True
    ff = find_ffmpeg()
    if not ff:
        return True
    try:
        proc = subprocess.run(
            [ff, "-hide_banner", "-loglevel", "error", "-i", os.path.abspath(path)],
            capture_output=True,
            timeout=8,
        )
        text = (proc.stderr or proc.stdout or b"").decode("utf-8", errors="replace")
        return "Audio:" in text
    except Exception:
        return True


def _extract_audio_to_mp3_with_ffmpeg(ffmpeg_exe: str, src: str) -> str:
    """从含视频的文件抽取音轨，编码为 MP3（有损），输出在与源文件同目录：`<stem>_jy_audio.mp3`。"""
    src_abs = os.path.abspath(src)
    base, _ext = os.path.splitext(src_abs)
    dst = base + "_jy_audio.mp3"
    cmd = [
        ffmpeg_exe,
        "-y",
        "-i",
        src_abs,
        "-vn",
        "-acodec",
        "libmp3lame",
        "-q:a",
        "2",
        dst,
    ]
    proc = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        err = (proc.stderr or proc.stdout or "").strip()[:1200]
        raise RuntimeError(f"ffmpeg 抽取音频失败（退出码 {proc.returncode}）:\n{err}")
    if not os.path.isfile(dst) or os.path.getsize(dst) == 0:
        raise RuntimeError("ffmpeg 未生成有效的 mp3 文件（可能源文件无音轨）。")
    return dst


_SPATIAL_CLIP_KF_TYPES = frozenset(
    {
        "KFTypeScaleX",
        "KFTypeScaleY",
        "UNIFORM_SCALE",
        "KFTypePositionX",
        "KFTypePositionY",
    }
)


def _video_display_pixel_size(width: int, height: int, rotation_deg: float = 0.0) -> Tuple[int, int]:
    """按 rotation 元数据推算显示宽高（后备方案，部分文件元数据不准）。"""
    w, h = int(width), int(height)
    try:
        rot = float(rotation_deg or 0.0) % 360.0
    except (TypeError, ValueError):
        rot = 0.0
    if int(abs(rot)) % 180 == 90:
        w, h = h, w
    return max(w, 0), max(h, 0)


_video_display_size_cache: Dict[Tuple[str, float], Tuple[int, int]] = {}


def _parse_ppm_dimensions(ppm_bytes: bytes) -> Optional[Tuple[int, int]]:
    """从 ffmpeg ``image2pipe`` 输出的 PPM/PGM 头解析宽高。"""
    if len(ppm_bytes) < 8:
        return None
    if ppm_bytes[0:1] != b"P":
        return None
    i = 2
    tokens: List[str] = []
    while i < min(len(ppm_bytes), 256) and len(tokens) < 2:
        while i < len(ppm_bytes) and ppm_bytes[i : i + 1] in (b" ", b"\t", b"\r", b"\n"):
            i += 1
        if i >= len(ppm_bytes):
            break
        if ppm_bytes[i : i + 1] == b"#":
            while i < len(ppm_bytes) and ppm_bytes[i : i + 1] not in (b"\n", b"\r"):
                i += 1
            continue
        j = i
        while j < len(ppm_bytes) and ppm_bytes[j : j + 1] not in (b" ", b"\t", b"\r", b"\n"):
            j += 1
        tok = ppm_bytes[i:j].decode("ascii", errors="ignore")
        if tok:
            tokens.append(tok)
        i = j
    if len(tokens) < 2:
        return None
    try:
        w, h = int(tokens[0]), int(tokens[1])
    except ValueError:
        return None
    if w <= 0 or h <= 0:
        return None
    return w, h


def _probe_video_display_size_ffmpeg_frame(path: str) -> Optional[Tuple[int, int]]:
    """用 ffmpeg 解码一帧（默认 autorotate）得到实际画面宽高，比 rotation 元数据更可靠。"""
    ff = find_ffmpeg()
    if not ff:
        return None
    path_abs = os.path.abspath(path)
    if not os.path.isfile(path_abs):
        return None

    def _run(extra_input_args: List[str]) -> Optional[Tuple[int, int]]:
        cmd = [
            ff,
            "-hide_banner",
            "-loglevel",
            "error",
            *extra_input_args,
            "-i",
            path_abs,
            "-frames:v",
            "1",
            "-an",
            "-f",
            "image2pipe",
            "-vcodec",
            "ppm",
            "pipe:1",
        ]
        try:
            proc = subprocess.run(cmd, capture_output=True, timeout=25)
        except (subprocess.TimeoutExpired, OSError):
            return None
        if proc.returncode != 0 or not proc.stdout:
            return None
        return _parse_ppm_dimensions(proc.stdout)

    out = _run(["-ss", "0.1"])
    if out:
        return out
    return _run([])


def _resolve_video_display_pixel_size(
    path: str,
    fallback_w: int,
    fallback_h: int,
    rotation_deg: float = 0.0,
) -> Tuple[int, int]:
    """优先 ffmpeg 抽帧测显示比例；失败再退回 rotation + 容器宽高。"""
    path_abs = os.path.abspath(path)
    try:
        mtime = os.path.getmtime(path_abs)
    except OSError:
        mtime = 0.0
    cache_key = (path_abs, float(mtime))
    cached = _video_display_size_cache.get(cache_key)
    if cached:
        return cached

    probed = _probe_video_display_size_ffmpeg_frame(path_abs)
    if probed:
        _video_display_size_cache[cache_key] = probed
        return probed

    meta = _video_display_pixel_size(fallback_w, fallback_h, rotation_deg)
    _video_display_size_cache[cache_key] = meta
    return meta


def _compute_cover_uniform_zoom(canvas_w: int, canvas_h: int, mat_w: int, mat_h: int) -> float:
    """相对剪映默认「整段素材完整放进画布」的缩放，再放大到 **cover 铺满** 所需的等比倍数。

    即 ``max(cw/mw, ch/mh) / min(cw/mw, ch/mh)``，与 ``object-fit: cover`` / contain 的缩放比一致；
    宽高比已与画布一致时为 ``1.0``。``mat_w/mat_h`` 应为显示方向像素（见 ``_video_display_pixel_size``）。
    """
    cw, ch = float(canvas_w), float(canvas_h)
    mw, mh = float(mat_w), float(mat_h)
    if cw <= 0 or ch <= 0 or mw <= 0 or mh <= 0:
        return 1.0
    rw = cw / mw
    rh = ch / mh
    lo = min(rw, rh)
    hi = max(rw, rh)
    if lo <= 1e-12:
        return 1.0
    return float(hi / lo)


def _apply_clip_cover_scale_transform(
    clip: Dict[str, Any],
    zoom: float,
    *,
    transform_x: float = 0.0,
    transform_y: float = 0.0,
) -> None:
    """写入 ``clip`` 的等比缩放与位移。兼容剪映草稿中两种常见结构：

    - 库/py 常用：顶层 ``clip.scale`` + ``clip.transform`` 仅 ``x/y``；
    - 部分版本/轨道：缩放写在 ``clip.transform.scale`` 里；若只写顶层 ``scale`` 会导致仍读旧嵌套值而出现「缩小、错位」。
    """
    tf = clip.get("transform")
    if isinstance(tf, dict) and isinstance(tf.get("scale"), dict):
        nd = dict(tf)
        nd["scale"] = {"x": float(zoom), "y": float(zoom)}
        nd["x"] = float(transform_x)
        nd["y"] = float(transform_y)
        clip["transform"] = nd
        clip.pop("scale", None)
    else:
        clip["scale"] = {"x": float(zoom), "y": float(zoom)}
        clip["transform"] = {"x": float(transform_x), "y": float(transform_y)}


def _patch_replaced_video_segment_clip_center_cover(
    seg: Any,
    *,
    canvas_w: int,
    canvas_h: int,
    material_path: str,
    mat_w: int,
    mat_h: int,
    mat_rotation_deg: float = 0.0,
) -> None:
    """替换素材后重写片段 ``clip``：等比铺满画布（cover）；旋转归零；去掉与缩放/位置冲突的关键帧。

    缩放按 ffmpeg 解码首帧得到的**实际画面**宽高计算（失败时才用 rotation 元数据）。
    """
    raw = getattr(seg, "raw_data", None)
    if not isinstance(raw, dict):
        return
    disp_w, disp_h = _resolve_video_display_pixel_size(
        material_path, mat_w, mat_h, mat_rotation_deg
    )
    zoom = _compute_cover_uniform_zoom(canvas_w, canvas_h, disp_w, disp_h)
    old_clip = raw.get("clip")
    clip: Dict[str, Any] = dict(old_clip) if isinstance(old_clip, dict) else {}
    flip = clip.get("flip")
    if not isinstance(flip, dict):
        flip = {"horizontal": False, "vertical": False}
    al = clip.get("alpha", 1.0)
    if not isinstance(al, (int, float)):
        al = 1.0
    clip["alpha"] = float(al)
    clip["flip"] = dict(flip)
    clip["rotation"] = 0.0
    _apply_clip_cover_scale_transform(clip, zoom, transform_x=0.0, transform_y=0.0)
    raw["clip"] = clip
    raw["uniform_scale"] = {"on": True, "value": 1.0}
    kfs = raw.get("common_keyframes")
    if isinstance(kfs, list):
        raw["common_keyframes"] = [
            k
            for k in kfs
            if isinstance(k, dict) and str(k.get("property_type") or "") not in _SPATIAL_CLIP_KF_TYPES
        ]


def apply_single_material_replace(
    content_json_path: str,
    ref: MediaSegmentRef,
    new_file_path: str,
    *,
    source_start_mode: str = VIDEO_REPLACE_SOURCE_HEAD,
    source_start_sec: float = 0.0,
) -> Optional[str]:
    """将指定片段的素材替换为本地文件。

    时长处理（与 ``replace_material_by_seg`` / ``ShrinkMode.cut_tail``、``ExtendMode.cut_material_tail`` 一致）：
    新素材**更长**时，只使用素材前段，轨道上片段时长仍与原片段一致（截断素材尾部）；
    新素材**更短**时，轨道上该片段的**目标时长会缩短**为与素材长度一致（不是拉长时间轴上的空白）。

    ``source_start_mode``：``head`` 从片头截取；``random`` 在合法范围内按**整秒**随机起点（0s、1s、…）；``custom`` 从 ``source_start_sec`` 秒处起算（超出则钳位）。

    若替换的是**音频轨**且所选文件带视频画面，则自动调用 ffmpeg 生成同目录下的 ``*_jy_audio.mp3`` 再引用。

    **视频轨**：替换后会按画布与素材**实际画面**像素重写 ``clip``（**cover**；优先 ffmpeg 抽帧测比例，元数据 rotation 仅作后备；兼容 ``transform.scale`` 嵌套结构）。

    Returns:
        若有自动转码，返回提示文案；否则返回 None。
    """
    _ensure_local_pyjianyingdraft_on_path()
    from pyJianYingDraft import AudioMaterial, VideoMaterial
    from pyJianYingDraft.script_file import ScriptFile
    from pyJianYingDraft.template_mode import ExtendMode, ShrinkMode
    from pyJianYingDraft.time_util import SEC, Timerange
    from pyJianYingDraft.track import TrackType

    script = ScriptFile.load_template(content_json_path)
    tt = TrackType.video if ref.track_type == "video" else TrackType.audio
    track = script.get_imported_track(tt, name=None, index=ref.track_type_index)

    extra_note: Optional[str] = None
    if ref.track_type == "video":
        material: Any = VideoMaterial(os.path.abspath(new_file_path))
    else:
        audio_path = os.path.abspath(new_file_path)
        if _media_has_video_track(audio_path):
            ff = find_ffmpeg()
            if not ff:
                raise RuntimeError(
                    "所选文件包含视频画面，作为音频轨需要先抽取音轨为 MP3。\n"
                    "未找到 ffmpeg，请任选其一：\n"
                    "· 安装 ffmpeg 并加入系统 PATH；\n"
                    "· 设置环境变量 FFMPEG 为 ffmpeg.exe 的完整路径；\n"
                    "· 将 ffmpeg.exe 放到本程序目录下的 bin 文件夹（bin\\ffmpeg.exe）。\n"
                    "无需把 ffmpeg 拷进项目也可，只要 PATH 或 FFMPEG 能指向它。"
                )
            audio_path = _extract_audio_to_mp3_with_ffmpeg(ff, audio_path)
            extra_note = (
                "已用 ffmpeg 从视频中抽取音轨并生成 MP3（有损编码）：\n"
                f"{audio_path}\n\n"
                "草稿已指向该文件；请勿随意删除，否则剪映会丢素材。"
            )
        material = AudioMaterial(audio_path)

    mode = normalize_replace_source_start_mode(source_start_mode)
    src_tr: Optional[Timerange] = None
    if ref.track_type == "video" and isinstance(material, VideoMaterial) and material.material_type == "photo":
        src_tr = None
    else:
        seg = track.segments[ref.segment_index]
        clip_us = int(seg.duration)
        mat_dur = int(material.duration)
        max_start = max(0, mat_dur - clip_us)
        if mode == VIDEO_REPLACE_SOURCE_RANDOM:
            if max_start <= 0:
                start_us = 0
            else:
                max_sec = int(max_start // SEC)
                sec_pick = random.randint(0, max_sec)
                start_us = min(sec_pick * SEC, max_start)
        elif mode == VIDEO_REPLACE_SOURCE_CUSTOM:
            start_us = int(round(float(source_start_sec) * SEC))
            start_us = max(0, min(start_us, max_start))
        else:
            start_us = 0
        src_tr = Timerange(start_us, clip_us)

    script.replace_material_by_seg(
        track,
        ref.segment_index,
        material,
        source_timerange=src_tr,
        handle_shrink=ShrinkMode.cut_tail,
        handle_extend=ExtendMode.cut_material_tail,
    )
    if ref.track_type == "video" and isinstance(material, VideoMaterial):
        try:
            mw = int(material.width)
            mh = int(material.height)
        except (TypeError, ValueError):
            mw, mh = 0, 0
        if mw > 0 and mh > 0:
            seg_done = track.segments[ref.segment_index]
            rot_deg = float(getattr(material, "rotation", 0.0) or 0.0)
            _patch_replaced_video_segment_clip_center_cover(
                seg_done,
                canvas_w=int(script.width),
                canvas_h=int(script.height),
                material_path=str(material.path),
                mat_w=mw,
                mat_h=mh,
                mat_rotation_deg=rot_deg,
            )
    script.save()
    return extra_note


def apply_per_segment_export_pools_to_draft(
    content_json_path: str,
    draft_name: str,
    segment_pool: Dict[str, Dict[str, Any]],
    sequential_cursor: Dict[str, int],
) -> Tuple[int, int, List[str], int]:
    """对 segment_pool 中已配置的片段套用素材：单文件与目录二选一；有 replace_file 则用文件，否则从 dir 目录按规则选一文件。

    每个片段可配置 order: "random" | "sequential"；顺序模式用 sequential_cursor[片段键] 在多轮导出间延续。
    返回 (成功数, 因目录内无匹配文件跳过数, 错误信息列表, 已配置目录的片段数)。
    """
    errs: List[str] = []
    refs = list_replaceable_media_segments(content_json_path)
    ok = 0
    skip = 0
    configured = 0
    pool_use = segment_export_pool_enforce_exclusive_sources(
        dict(segment_pool) if isinstance(segment_pool, dict) else {}
    )
    for ref in refs:
        key = segment_export_pool_key(draft_name, ref)
        cfg = pool_use.get(key) or {}
        sm = normalize_replace_source_start_mode(cfg.get("replace_source_start_mode"))
        sec = parse_replace_source_start_sec(cfg.get("replace_source_start_sec"))
        repl_file = str(cfg.get("replace_file") or "").strip()
        if repl_file:
            if not os.path.isfile(repl_file):
                errs.append(f"{ref.combo_label}: 预设替换文件不存在或已不是文件\n{repl_file}")
                continue
            try:
                apply_single_material_replace(
                    content_json_path,
                    ref,
                    repl_file,
                    source_start_mode=sm,
                    source_start_sec=sec,
                )
                ok += 1
            except Exception as e:
                errs.append(f"{ref.combo_label}: {e}")
            continue

        pool_dir = (cfg.get("dir") or "").strip()
        if not pool_dir:
            continue
        configured += 1
        if not os.path.isdir(pool_dir):
            errs.append(f"{ref.combo_label}: 素材目录无效或不存在")
            continue
        order = cfg.get("order", "random")
        if order not in ("random", "sequential"):
            order = "random"
        files = list_replace_candidates_in_dir(pool_dir, ref.track_type)
        if not files:
            skip += 1
            continue
        if order == "sequential":
            seq_i = int(sequential_cursor.get(key, 0))
            pick = files[seq_i % len(files)]
            sequential_cursor[key] = seq_i + 1
        else:
            pick = random.choice(files)
        try:
            print(
                f"[套素材] {ref.combo_label} <- {os.path.basename(pick)} "
                f"(order={order}, 候选 {len(files)} 个)"
            )
            apply_single_material_replace(
                content_json_path,
                ref,
                pick,
                source_start_mode=sm,
                source_start_sec=sec,
            )
            ok += 1
        except Exception as e:
            errs.append(f"{ref.combo_label}: {e}")
    return ok, skip, errs, configured


# 子草稿随机字幕样式：免费字体 resource_id + 常用色 + 可选花字（剪映内置素材 id）
_SUBTITLE_FONT_RESOURCE_IDS: Tuple[str, ...] = (
    "7290445778273702455",  # 文轩体
    "6740499188347310605",  # 综艺体
    "7265595305163231781",  # HarmonyOS Sans SC Regular
    "7068207165277737502",  # 优设标题黑
    "6740513279296147982",  # 宋体
    "7130644288047682085",  # 研宋体
    "7203638484756599333",  # 妙黑体
    "7265609486646121018",  # 站酷酷黑体
    "6807743192671195655",  # 思源中宋
    "7265610359807939132",  # 优设好身体
)
_SUBTITLE_COLOR_RGB: Tuple[Tuple[float, float, float], ...] = (
    (1.0, 1.0, 1.0),
    (1.0, 0.96, 0.35),
    (1.0, 0.82, 0.15),
    (0.95, 0.98, 1.0),
    (0.35, 0.95, 0.98),
    (1.0, 0.38, 0.38),
    (0.55, 1.0, 0.58),
    (0.92, 0.78, 1.0),
)
_SUBTITLE_TEXT_EFFECT_IDS: Tuple[str, ...] = (
    "7296357486490144036",
)


def _text_effect_pool_pref_path() -> Path:
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    d = Path(ada) / "pyJianYingDraft_browser"
    d.mkdir(parents=True, exist_ok=True)
    return d / "text_effect_pool.json"


def _jianying_artist_effect_cache_roots() -> List[str]:
    local = os.environ.get("LOCALAPPDATA", "")
    roots: List[str] = []
    for app_name in ("JianyingPro", "CapCut"):
        p = os.path.join(local, app_name, "User Data", "Cache", "artistEffect")
        if os.path.isdir(p):
            roots.append(p)
    return roots


def _artist_effect_subdir_kind(subdir: str) -> Optional[str]:
    """判断 artistEffect 单条缓存类型：``sdftext`` / ``text_style`` / ``sticker`` / 未知。"""
    if not os.path.isdir(subdir):
        return None
    cfg_path = os.path.join(subdir, "config.json")
    link_types: List[str] = []
    if os.path.isfile(cfg_path):
        try:
            with open(cfg_path, "r", encoding="utf-8") as f:
                cfg = json.load(f)
            link = (cfg.get("effect") or {}).get("Link") or []
            if isinstance(link, list):
                for item in link:
                    if isinstance(item, dict):
                        t = str(item.get("type") or "").strip()
                        if t:
                            link_types.append(t)
        except (OSError, json.JSONDecodeError, TypeError):
            pass
    prefab_path = os.path.join(subdir, "effect.prefab")
    if os.path.isfile(prefab_path):
        try:
            with open(prefab_path, "rb") as f:
                if b"SDFText" in f.read(256_000):
                    return "sdftext"
        except OSError:
            pass
    if "TextStyle" in link_types and os.path.isfile(os.path.join(subdir, "effectStyle.json")):
        return "text_style"
    if "InfoSticker" in link_types:
        return "sticker"
    return None


def _classify_subtitle_flower_effect_id(effect_id: str) -> Optional[str]:
    """字幕可用花字：旧版 ``SDFText`` prefab，或 5.9+ ``TextStyle`` + ``effectStyle.json``。"""
    eid = str(effect_id or "").strip()
    if not eid.isdigit():
        return None
    found_sdftext = False
    found_text_style = False
    for root in _jianying_artist_effect_cache_roots():
        base = os.path.join(root, eid)
        if not os.path.isdir(base):
            continue
        try:
            for sub in os.listdir(base):
                kind = _artist_effect_subdir_kind(os.path.join(base, sub))
                if kind == "sdftext":
                    found_sdftext = True
                elif kind == "text_style":
                    found_text_style = True
        except OSError:
            pass
    if found_sdftext:
        return "sdftext"
    if found_text_style:
        return "text_style"
    return None


def _subtitle_flower_effect_id_is_usable(effect_id: str) -> bool:
    return _classify_subtitle_flower_effect_id(effect_id) is not None


def _subtitle_flower_effect_prefab_has_sdftext(effect_id: str) -> bool:
    """兼容旧调用：是否 SDFText 类花字。"""
    return _classify_subtitle_flower_effect_id(effect_id) == "sdftext"


def _resolve_subtitle_flower_effect_style_path(effect_id: str) -> str:
    """``effectStyle.path``：指向本机已缓存花字目录（SDFText 或 TextStyle），否则 ``C:``。"""
    eid = str(effect_id or "").strip()
    sdftext_path: Optional[str] = None
    text_style_path: Optional[str] = None
    for root in _jianying_artist_effect_cache_roots():
        base = os.path.join(root, eid)
        if not os.path.isdir(base):
            continue
        try:
            for sub in os.listdir(base):
                subp = os.path.join(base, sub)
                kind = _artist_effect_subdir_kind(subp)
                if kind == "sdftext" and not sdftext_path:
                    sdftext_path = os.path.join(base, sub).replace("\\", "/")
                elif kind == "text_style" and not text_style_path:
                    text_style_path = os.path.join(base, sub).replace("\\", "/")
        except OSError:
            pass
    return sdftext_path or text_style_path or "C:"


def filter_valid_subtitle_flower_effect_ids(
    effect_ids: Iterable[str],
) -> Tuple[List[str], List[str]]:
    """区分可作用于字幕的花字 id 与 artistEffect 里误收的贴纸/无效 id。"""
    valid: List[str] = []
    invalid: List[str] = []
    seen: set[str] = set()
    for raw in effect_ids:
        eid = str(raw or "").strip()
        if not eid or eid in seen:
            continue
        seen.add(eid)
        if _subtitle_flower_effect_id_is_usable(eid):
            valid.append(eid)
        else:
            invalid.append(eid)
    return valid, invalid


def load_user_text_effect_id_pool() -> List[str]:
    """读取用户维护的花字 id 列表（``text_effect_pool.json`` 的 ``effect_ids``）。"""
    path = _text_effect_pool_pref_path()
    if not path.is_file():
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError, TypeError):
        return []
    raw = data.get("effect_ids") if isinstance(data, dict) else data
    if not isinstance(raw, list):
        return []
    out: List[str] = []
    seen: set[str] = set()
    for item in raw:
        eid = str(item or "").strip()
        if eid and eid not in seen:
            seen.add(eid)
            out.append(eid)
    return out


def load_text_effect_display_name_overrides() -> Dict[str, str]:
    """读取用户在 ``text_effect_pool.json`` 里维护的花字别名（``effect_names``）。"""
    path = _text_effect_pool_pref_path()
    if not path.is_file():
        return {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError, TypeError):
        return {}
    raw = data.get("effect_names") if isinstance(data, dict) else None
    if not isinstance(raw, dict):
        return {}
    out: Dict[str, str] = {}
    for key, val in raw.items():
        eid = str(key or "").strip()
        name = str(val or "").strip()
        if eid and name:
            out[eid] = name
    return out


def _merge_text_effect_display_name_maps(*maps: Dict[str, str]) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for mp in maps:
        for raw_id, raw_name in mp.items():
            eid = str(raw_id or "").strip()
            name = str(raw_name or "").strip()
            if not eid or not name:
                continue
            prev = out.get(eid, "")
            if not prev or len(name) > len(prev):
                out[eid] = name
    return out


def _iter_local_draft_content_json_paths(extra_draft_root: Optional[str] = None) -> Iterable[str]:
    """遍历本机剪映/CapCut 草稿与回收站中的 ``draft_content.json``。"""
    seen: set[str] = set()
    local = os.environ.get("LOCALAPPDATA", "")

    def _scan_root(root: str) -> None:
        root = str(root or "").strip()
        if not root or not os.path.isdir(root):
            return
        for sub in ("", ".recycle_bin"):
            base = os.path.join(root, sub) if sub else root
            if not os.path.isdir(base):
                continue
            try:
                names = os.listdir(base)
            except OSError:
                continue
            for name in names:
                p = os.path.abspath(os.path.join(base, name, "draft_content.json"))
                if p in seen or not os.path.isfile(p):
                    continue
                seen.add(p)
                yield p

    for app_name in ("JianyingPro", "CapCut"):
        yield from _scan_root(os.path.join(local, app_name, "User Data", "Projects", "com.lveditor.draft"))
    if extra_draft_root:
        yield from _scan_root(str(extra_draft_root).strip())


def harvest_text_effect_display_names_from_drafts(
    extra_draft_root: Optional[str] = None,
) -> Dict[str, str]:
    """从本机草稿 ``materials.effects[type=text_effect].name`` 收集花字显示名。"""
    out: Dict[str, str] = {}
    for p in _iter_local_draft_content_json_paths(extra_draft_root):
        data = _safe_read_json(p)
        if not isinstance(data, dict):
            continue
        materials = data.get("materials")
        if not isinstance(materials, dict):
            continue
        for eff in materials.get("effects") or []:
            if not isinstance(eff, dict) or eff.get("type") != "text_effect":
                continue
            eid = str(eff.get("effect_id") or eff.get("resource_id") or "").strip()
            ename = str(eff.get("name") or "").strip()
            if not eid or not ename:
                continue
            prev = out.get(eid, "")
            if not prev or len(ename) > len(prev):
                out[eid] = ename
    return out


def persist_harvested_text_effect_display_names(harvested: Dict[str, str]) -> int:
    """把扫描到的花字名称合并写入 ``text_effect_pool.json`` 的 ``effect_names``。"""
    if not harvested:
        return 0
    path = _text_effect_pool_pref_path()
    payload: Dict[str, Any] = {}
    if path.is_file():
        try:
            with open(path, "r", encoding="utf-8") as f:
                prev = json.load(f)
            if isinstance(prev, dict):
                payload = dict(prev)
        except (OSError, json.JSONDecodeError, TypeError):
            payload = {}
    names_raw = payload.get("effect_names")
    names: Dict[str, str] = {}
    if isinstance(names_raw, dict):
        for key, val in names_raw.items():
            eid = str(key or "").strip()
            nm = str(val or "").strip()
            if eid and nm:
                names[eid] = nm
    changed = 0
    for eid, nm in harvested.items():
        eid = str(eid or "").strip()
        nm = str(nm or "").strip()
        if not eid or not nm:
            continue
        prev = names.get(eid, "")
        if prev != nm and (not prev or len(nm) >= len(prev)):
            names[eid] = nm
            changed += 1
    if changed <= 0:
        return 0
    payload["effect_names"] = dict(sorted(names.items(), key=lambda kv: kv[0]))
    try:
        tmp = path.with_suffix(".json.tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
    except OSError:
        return 0
    return changed


def ensure_text_effect_pool_template_file() -> str:
    """若用户花字池文件不存在则写入模板，返回绝对路径。"""
    path = _text_effect_pool_pref_path()
    if path.is_file():
        return str(path)
    tmpl = {
        "_comment": "effect_ids：花字 effect_id。effect_names：可选别名（下拉显示「名称 · id」）；程序会从剪映草稿自动合并名称，也可手动填写。",
        "effect_ids": list(_SUBTITLE_TEXT_EFFECT_IDS),
        "effect_names": {},
    }
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(tmpl, f, ensure_ascii=False, indent=2)
    except OSError:
        pass
    return str(path)


def harvest_local_text_effect_ids() -> List[str]:
    """从本机剪映/CapCut 草稿、文本预设、artistEffect 缓存自动收集花字 effect_id。

    说明：剪映没有公开「全部花字列表」API；缓存里一般是你在剪映里预览/用过的花字。
    想在池子里更多样，可在剪映「花字」面板里多浏览几种，再重启本程序或重新生成子稿。
    """
    found: List[str] = []
    seen: set[str] = set()
    local = os.environ.get("LOCALAPPDATA", "")

    def _add(eid: str) -> None:
        e = str(eid or "").strip()
        if e.isdigit() and len(e) >= 10 and e not in seen:
            seen.add(e)
            found.append(e)

    for app_name in ("JianyingPro", "CapCut"):
        draft_root = os.path.join(local, app_name, "User Data", "Projects", "com.lveditor.draft")
        if not os.path.isdir(draft_root):
            continue
        try:
            for name in os.listdir(draft_root):
                p = os.path.join(draft_root, name, "draft_content.json")
                if not os.path.isfile(p):
                    continue
                data = _safe_read_json(p)
                if not isinstance(data, dict):
                    continue
                materials = data.get("materials") if isinstance(data.get("materials"), dict) else {}
                for eff in materials.get("effects") or []:
                    if isinstance(eff, dict) and eff.get("type") == "text_effect":
                        _add(str(eff.get("effect_id") or eff.get("resource_id") or ""))
                for mat in materials.get("texts") or []:
                    if not isinstance(mat, dict):
                        continue
                    snap = _extract_text_style_snapshot(mat)
                    if snap:
                        _add(str(snap.get("effect_id") or ""))

        except OSError:
            pass

        app_base = os.path.join(local, app_name)
        for preset_sub in ("User Data/Presets/Text", "User Data/Presets/TextV2", "User Data/Presets/TextPresetV2"):
            preset_root = os.path.join(app_base, *preset_sub.split("/"))
            if not os.path.isdir(preset_root):
                continue
            try:
                for dirpath, _dirnames, filenames in os.walk(preset_root):
                    for fn in filenames:
                        fp = os.path.join(dirpath, fn)
                        try:
                            if os.path.getsize(fp) > 3_000_000:
                                continue
                            with open(fp, "r", encoding="utf-8", errors="ignore") as f:
                                txt = f.read()
                        except OSError:
                            continue
                        if "flower" not in txt.lower() and "text_effect" not in txt:
                            continue
                        try:
                            data = json.loads(txt)
                        except json.JSONDecodeError:
                            data = None
                        if isinstance(data, dict):
                            for res in data.get("resources") or []:
                                if not isinstance(res, dict):
                                    continue
                                if str(res.get("panel") or "").lower() in ("flower", "text_effect", "huazi"):
                                    _add(str(res.get("resource_id") or ""))
                        for m in re.finditer(
                            r'"panel"\s*:\s*"flower"[^}]{0,500}?"resource_id"\s*:\s*"(\d{10,})"',
                            txt,
                        ):
                            _add(m.group(1))
            except OSError:
                pass

        cache_root = os.path.join(app_base, "User Data", "Cache", "artistEffect")
        if os.path.isdir(cache_root):
            try:
                for name in os.listdir(cache_root):
                    if name.isdigit() and len(name) >= 10:
                        if _subtitle_flower_effect_id_is_usable(name):
                            _add(name)
            except OSError:
                pass

    return found


def sync_harvested_text_effects_to_pool_file() -> Tuple[int, str]:
    """把本机扫描到的花字 id 合并写入 text_effect_pool.json（只追加、不删用户已有项）。"""
    path = _text_effect_pool_pref_path()
    harvested = harvest_local_text_effect_ids()
    existing = load_user_text_effect_id_pool()
    seen = set(existing)
    merged = list(existing)
    added = 0
    for eid in harvested:
        if eid not in seen:
            seen.add(eid)
            merged.append(eid)
            added += 1
    if not path.is_file() and not merged:
        merged = list(_SUBTITLE_TEXT_EFFECT_IDS)
    payload: Dict[str, Any] = {
        "_comment": (
            "effect_ids：花字 effect_id（与 resource_id 相同）。"
            "程序启动时会从本机剪映草稿/文本预设/artistEffect 缓存自动追加新 id。"
            "也可手动添加。在剪映花字面板多预览几种可扩充缓存。"
        ),
        "effect_ids": merged if merged else list(_SUBTITLE_TEXT_EFFECT_IDS),
    }
    if harvested:
        payload["_auto_harvested_count"] = len(harvested)
    try:
        tmp = path.with_suffix(".json.tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
    except OSError:
        return added, str(path)
    _invalidate_text_effect_display_name_cache()
    try:
        persist_harvested_text_effect_display_names(harvest_text_effect_display_names_from_drafts())
    except OSError:
        pass
    return added, str(path)


def build_text_effect_id_pool(parent_content_path: str) -> Tuple[List[str], List[str]]:
    """从用户花字池、内置、本机 harvest、父稿已用花字合并去重，并过滤非字幕花字 id。"""
    pool: List[str] = []
    seen: set[str] = set()
    for src in (
        load_user_text_effect_id_pool(),
        list(_SUBTITLE_TEXT_EFFECT_IDS),
        harvest_local_text_effect_ids(),
    ):
        for eid in src:
            e = str(eid or "").strip()
            if e and e not in seen:
                seen.add(e)
                pool.append(e)
    data = _safe_read_json(parent_content_path)
    if isinstance(data, dict):
        materials = data.get("materials") if isinstance(data.get("materials"), dict) else {}
        for eff in materials.get("effects") or []:
            if not isinstance(eff, dict) or eff.get("type") != "text_effect":
                continue
            eid = str(eff.get("effect_id") or eff.get("resource_id") or "").strip()
            if eid and eid not in seen:
                seen.add(eid)
                pool.append(eid)
        for mat in materials.get("texts") or []:
            if not isinstance(mat, dict):
                continue
            snap = _extract_text_style_snapshot(mat)
            if not snap:
                continue
            eid = str(snap.get("effect_id") or "").strip()
            if eid and eid not in seen:
                seen.add(eid)
                pool.append(eid)
    valid, invalid = filter_valid_subtitle_flower_effect_ids(pool)
    if not valid:
        valid = list(_SUBTITLE_TEXT_EFFECT_IDS)
    return valid, invalid


def build_text_effect_pool_report(
    parent_content_json: Optional[str] = None,
    *,
    resync: bool = False,
) -> Dict[str, Any]:
    """汇总花字池：配置文件条目、可用/无效 id（可用=SDFText 或 TextStyle 花字，非贴纸）。"""
    added = 0
    if resync:
        try:
            added, _ = sync_harvested_text_effects_to_pool_file()
        except OSError:
            pass
    pool_path = ensure_text_effect_pool_template_file()
    listed = load_user_text_effect_id_pool()
    parent_p = (
        parent_content_json
        if parent_content_json and os.path.isfile(parent_content_json)
        else ""
    )
    if parent_p:
        valid, invalid = build_text_effect_id_pool(parent_p)
    else:
        pool_raw: List[str] = []
        seen: set[str] = set()
        for src in (
            listed,
            list(_SUBTITLE_TEXT_EFFECT_IDS),
            harvest_local_text_effect_ids(),
        ):
            for eid in src:
                e = str(eid or "").strip()
                if e and e not in seen:
                    seen.add(e)
                    pool_raw.append(e)
        valid, invalid = filter_valid_subtitle_flower_effect_ids(pool_raw)
        if not valid:
            valid = list(_SUBTITLE_TEXT_EFFECT_IDS)
    return {
        "pool_path": pool_path,
        "added_on_sync": added,
        "listed_count": len(listed),
        "valid_ids": valid,
        "invalid_ids": invalid,
        "valid_count": len(valid),
        "invalid_count": len(invalid),
    }


def format_text_effect_pool_report_text(report: Dict[str, Any]) -> str:
    lines = [
        "花字池检测报告",
        "",
        f"配置文件：{report.get('pool_path', '')}",
        f"配置中记录：{report.get('listed_count', 0)} 个 id",
        f"可用（本机已缓存、可用于字幕花字）：{report.get('valid_count', 0)} 个",
        f"无效（贴纸等，子稿随机时会忽略）：{report.get('invalid_count', 0)} 个",
    ]
    added = int(report.get("added_on_sync") or 0)
    if added > 0:
        lines.append(f"本次同步新写入配置：{added} 个 id")
    lines.extend(
        [
            "",
            "【可用 id】",
        ]
    )
    valid_ids = report.get("valid_ids") or []
    if valid_ids:
        names = get_text_effect_display_names()
        named_n = sum(1 for eid in valid_ids if names.get(str(eid)))
        lines.append(f"有中文名：{named_n} / {len(valid_ids)} 个（其余仅 id 或类型标签）")
        lines.append("")
        for eid in valid_ids:
            kind = _classify_subtitle_flower_effect_id(str(eid)) or "?"
            tag = "SDFText" if kind == "sdftext" else ("TextStyle" if kind == "text_style" else kind)
            label = text_effect_picker_label_for_id(str(eid), names)
            lines.append(f"  · {label}  ({tag})")
    else:
        lines.append("  （无）")
    lines.append("")
    lines.append("【无效 id（仅记录在配置里，不会用于随机花字）】")
    invalid_ids = report.get("invalid_ids") or []
    if invalid_ids:
        show = invalid_ids[:24]
        lines.extend(f"  · {eid}" for eid in show)
        if len(invalid_ids) > len(show):
            lines.append(f"  … 另有 {len(invalid_ids) - len(show)} 个未列出")
    else:
        lines.append("  （无）")
    lines.extend(
        [
            "",
            "如何扩充可用花字：",
            "1. 剪映 5.9 → 选中字幕 → 右侧「花字」面板多预览/应用到字幕；",
            "2. 回到本程序点「检测花字池」→「同步并刷新」，或重启程序；",
            "3. 可用 ≥2 个时，时间轴选中字幕轨并点「替换…」配置池随机，生成多条子稿才容易各不相同。",
            "",
            "关于中文名：只有剪映把花字应用到字幕时写入 draft 的 name 才会自动出现；",
            "程序同步时会写入配置文件 effect_names。无名称的可在配置里手动填别名，",
            "例如 \"7296357486490144036\": \"我的花字1\"。",
        ]
    )
    return "\n".join(lines)


def print_text_effect_pool_startup_summary(parent_content_json: Optional[str] = None) -> None:
    """启动时在终端打印花字池概况（与导出时的 [花字] 日志一致口径）。"""
    try:
        rep = build_text_effect_pool_report(parent_content_json, resync=False)
    except OSError:
        return
    n = int(rep.get("valid_count") or 0)
    listed = int(rep.get("listed_count") or 0)
    inv = int(rep.get("invalid_count") or 0)
    print(f"[花字] 启动：可用 {n} 个（配置 {listed} 个 id，忽略无效 {inv} 个）")
    print(f"[花字] 配置：{rep.get('pool_path', '')}")
    if n < 2:
        print("[花字] 提示：可用花字偏少，多个子稿可能一样；请在剪映花字面板多预览几种后点「检测花字池」同步。")


def open_text_effect_pool_inspector(
    parent: Any,
    *,
    get_draft_root: Any,
    get_selected_draft_name: Any,
    on_status_update: Optional[Any] = None,
) -> None:
    """弹窗展示花字池检测结果，并可触发扫描写入配置。"""
    import customtkinter as ctk
    from tkinter import messagebox

    def _parent_content_json() -> str:
        dr = (get_draft_root() or "").strip()
        nm = (get_selected_draft_name() or "").strip()
        if dr and nm:
            p = os.path.join(dr, nm, "draft_content.json")
            if os.path.isfile(p):
                return p
        return ""

    win = ctk.CTkToplevel(parent)
    win.title("花字池检测")
    win.geometry("560x480")
    win.minsize(480, 360)
    win.transient(parent)

    main = ctk.CTkFrame(win, fg_color="transparent")
    main.pack(fill="both", expand=True, padx=14, pady=12)
    ctk.CTkLabel(
        main,
        text="检测本机可用于替换花字的素材 id",
        font=ctk.CTkFont(size=13, weight="bold"),
        anchor="w",
    ).pack(fill="x", pady=(0, 8))

    box = ctk.CTkTextbox(main, font=ctk.CTkFont(family="Consolas", size=12))
    box.pack(fill="both", expand=True, pady=(0, 10))

    def _reload(*, resync: bool) -> None:
        try:
            rep = build_text_effect_pool_report(_parent_content_json(), resync=resync)
        except OSError as e:
            messagebox.showerror("花字池", f"检测失败：\n{e}", parent=win)
            return
        box.delete("1.0", "end")
        box.insert("1.0", format_text_effect_pool_report_text(rep))
        if callable(on_status_update):
            try:
                on_status_update()
            except Exception:
                pass
        if resync:
            n = int(rep.get("valid_count") or 0)
            named = sum(1 for eid in (rep.get("valid_ids") or []) if get_text_effect_display_names().get(str(eid)))
            messagebox.showinfo(
                "花字池",
                f"已同步扫描。\n可用花字：{n} 个。\n其中已记录中文名：{named} 个。",
                parent=win,
            )

    btn_row = ctk.CTkFrame(main, fg_color="transparent")
    btn_row.pack(fill="x")
    ctk.CTkButton(
        btn_row,
        text="同步并刷新",
        width=110,
        command=lambda: _reload(resync=True),
    ).pack(side="left", padx=(0, 8))

    def _open_pool_file() -> None:
        try:
            p = ensure_text_effect_pool_template_file()
            if sys.platform == "win32":
                os.startfile(p)  # type: ignore[attr-defined]
            else:
                messagebox.showinfo("花字池", p, parent=win)
        except OSError as e:
            messagebox.showerror("花字池", str(e), parent=win)

    ctk.CTkButton(
        btn_row,
        text="打开配置文件",
        width=110,
        fg_color=("gray70", "gray38"),
        command=_open_pool_file,
    ).pack(side="left", padx=(0, 8))
    ctk.CTkButton(btn_row, text="关闭", width=72, fg_color="transparent", border_width=1, command=win.destroy).pack(
        side="right"
    )

    _reload(resync=False)
    win.grab_set()
    win.focus_force()


def _sticker_pool_pref_path() -> Path:
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    d = Path(ada) / "pyJianYingDraft_browser"
    d.mkdir(parents=True, exist_ok=True)
    return d / "sticker_pool.json"


def _sticker_cache_sticker_subdir(resource_id: str) -> Optional[str]:
    """本机 artistEffect 中 InfoSticker 缓存子目录（绝对路径）。"""
    eid = str(resource_id or "").strip()
    if not eid.isdigit():
        return None
    for root in _jianying_artist_effect_cache_roots():
        base = os.path.join(root, eid)
        if not os.path.isdir(base):
            continue
        try:
            for sub in os.listdir(base):
                subp = os.path.join(base, sub)
                if _artist_effect_subdir_kind(subp) == "sticker":
                    return subp
        except OSError:
            pass
    return None


def _sticker_cache_is_text_template(resource_id: str) -> bool:
    """TextTemplate 复合贴纸（内含文字/多资源），不能按普通贴纸只换 id。"""
    subp = _sticker_cache_sticker_subdir(resource_id)
    if not subp:
        return False
    content_path = os.path.join(subp, "content.json")
    if not os.path.isfile(content_path):
        return False
    try:
        with open(content_path, "r", encoding="utf-8") as f:
            body = json.load(f)
        return str((body or {}).get("type") or "").strip() == "TextTemplate"
    except (OSError, json.JSONDecodeError, TypeError):
        return False


def _sticker_cache_has_heycan_info(resource_id: str) -> bool:
    """贴纸缓存是否含 heycanInfo.json（完整下载，非空壳目录）。"""
    subp = _sticker_cache_sticker_subdir(resource_id)
    if not subp:
        return False
    try:
        for root, _dirs, files in os.walk(subp):
            if "heycanInfo.json" in files:
                return True
    except OSError:
        pass
    return False


def _sticker_resource_id_in_trusted_draft_templates(resource_id: str) -> bool:
    """草稿中曾成功引用且路径匹配的贴纸（有完整素材记录）。"""
    rid = str(resource_id or "").strip()
    if not rid:
        return False
    templates, trusted = _get_sticker_material_templates()
    if rid not in trusted:
        return False
    mat = templates.get(rid)
    return isinstance(mat, dict) and _sticker_material_path_matches(rid, mat)


def _classify_sticker_resource_id(resource_id: str) -> Optional[str]:
    """贴纸素材：InfoSticker 完整缓存，或草稿已验证；排除花字/TextTemplate/过短 id。"""
    if _classify_subtitle_flower_effect_id(resource_id):
        return None
    if _sticker_cache_is_text_template(resource_id):
        return None
    eid = str(resource_id or "").strip()
    if not eid.isdigit() or len(eid) < 19:
        return None
    if not _sticker_cache_sticker_subdir(eid):
        return None
    if _sticker_cache_has_heycan_info(eid):
        return "sticker"
    if _sticker_resource_id_in_trusted_draft_templates(eid):
        return "sticker"
    return None


def _sticker_resource_id_is_usable(resource_id: str) -> bool:
    return _classify_sticker_resource_id(resource_id) == "sticker"


def load_user_sticker_resource_id_pool() -> List[str]:
    path = _sticker_pool_pref_path()
    if not path.is_file():
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError, TypeError):
        return []
    raw = data.get("resource_ids") if isinstance(data, dict) else data
    if not isinstance(raw, list):
        return []
    out: List[str] = []
    seen: set[str] = set()
    for item in raw:
        rid = str(item or "").strip()
        if rid and rid not in seen:
            seen.add(rid)
            out.append(rid)
    return out


def ensure_sticker_pool_template_file() -> str:
    path = _sticker_pool_pref_path()
    if path.is_file():
        return str(path)
    tmpl = {
        "_comment": "贴纸 resource_id（与 sticker_id 相同）。程序会从本机草稿与 artistEffect 缓存自动追加。",
        "resource_ids": [],
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(tmpl, f, ensure_ascii=False, indent=2)
    return str(path)


def harvest_local_sticker_resource_ids() -> List[str]:
    """从本机剪映/CapCut 草稿与 artistEffect 缓存收集贴纸 resource_id。"""
    found: List[str] = []
    seen: set[str] = set()
    local = os.environ.get("LOCALAPPDATA", "")

    def _add(rid: str) -> None:
        r = str(rid or "").strip()
        if r.isdigit() and len(r) >= 19 and r not in seen:
            seen.add(r)
            found.append(r)

    for app_name in ("JianyingPro", "CapCut"):
        draft_root = os.path.join(local, app_name, "User Data", "Projects", "com.lveditor.draft")
        if os.path.isdir(draft_root):
            try:
                for name in os.listdir(draft_root):
                    p = os.path.join(draft_root, name, "draft_content.json")
                    if not os.path.isfile(p):
                        continue
                    data = _safe_read_json(p)
                    if not isinstance(data, dict):
                        continue
                    for stk in (data.get("materials") or {}).get("stickers") or []:
                        if not isinstance(stk, dict):
                            continue
                        _add(str(stk.get("resource_id") or stk.get("sticker_id") or ""))
            except OSError:
                pass
        cache_root = os.path.join(local, app_name, "User Data", "Cache", "artistEffect")
        if os.path.isdir(cache_root):
            try:
                for name in os.listdir(cache_root):
                    if name.isdigit() and len(name) >= 19 and _sticker_resource_id_is_usable(name):
                        _add(name)
            except OSError:
                pass
    return found


def sync_harvested_stickers_to_pool_file() -> Tuple[int, int, str]:
    """合并本机扫描到的贴纸 id 写入配置，并移除无效项。返回 (新增数, 移除无效数, 配置路径)。"""
    path = _sticker_pool_pref_path()
    harvested = harvest_local_sticker_resource_ids()
    existing = load_user_sticker_resource_id_pool()
    seen = set(existing)
    merged = list(existing)
    added = 0
    for rid in harvested:
        if rid not in seen:
            seen.add(rid)
            merged.append(rid)
            added += 1
    valid, invalid = filter_valid_sticker_resource_ids(merged)
    removed_invalid = len(invalid)
    payload: Dict[str, Any] = {
        "_comment": (
            "resource_ids：剪映贴纸 resource_id（与 sticker_id 相同）。"
            "程序启动时会从本机草稿/artistEffect 缓存自动追加，并移除无效 id。"
            "在剪映「贴纸」面板多预览几种可扩充缓存。"
        ),
        "resource_ids": valid,
    }
    if harvested:
        payload["_auto_harvested_count"] = len(harvested)
    if removed_invalid:
        payload["_pruned_invalid_count"] = removed_invalid
    try:
        tmp = path.with_suffix(".json.tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
    except OSError:
        return added, removed_invalid, str(path)
    _invalidate_sticker_material_template_cache()
    return added, removed_invalid, str(path)


def _resolve_sticker_cache_path(resource_id: str) -> str:
    """贴纸 ``materials.stickers[].path``：指向本机 artistEffect 缓存目录。"""
    subp = _sticker_cache_sticker_subdir(resource_id)
    if subp:
        return subp.replace("\\", "/")
    return "C:"


def _sticker_material_path_matches(resource_id: str, mat: Dict[str, Any]) -> bool:
    rid = str(resource_id or "").strip()
    if not rid:
        return False
    path = str(mat.get("path") or "").replace("\\", "/")
    return rid in path


def _sticker_original_size_from_cache(resource_id: str) -> List[Any]:
    subp = _sticker_cache_sticker_subdir(resource_id)
    if not subp:
        return []
    try:
        for root, _dirs, files in os.walk(subp):
            if "heycanInfo.json" not in files:
                continue
            with open(os.path.join(root, "heycanInfo.json"), "r", encoding="utf-8") as f:
                info = json.load(f)
            if not isinstance(info, dict):
                continue
            w = info.get("bigWidth") or info.get("singleWidth")
            h = info.get("bigHeight") or info.get("singleHeight")
            if w and h:
                return [int(w), int(h)]
    except (OSError, json.JSONDecodeError, TypeError, ValueError):
        pass
    return []


_STICKER_MATERIAL_TEMPLATE_CACHE: Optional[Dict[str, Dict[str, Any]]] = None
_STICKER_MATERIAL_TEMPLATE_TRUSTED: Optional[set[str]] = None


def _invalidate_sticker_material_template_cache() -> None:
    global _STICKER_MATERIAL_TEMPLATE_CACHE, _STICKER_MATERIAL_TEMPLATE_TRUSTED
    _STICKER_MATERIAL_TEMPLATE_CACHE = None
    _STICKER_MATERIAL_TEMPLATE_TRUSTED = None
    _invalidate_text_effect_display_name_cache()


def _sticker_material_template_score(mat: Dict[str, Any]) -> int:
    score = 0
    for key in ("name", "icon_url", "preview_cover_url", "request_id", "path"):
        if str(mat.get(key) or "").strip():
            score += 1
    return score


def harvest_sticker_material_templates() -> Tuple[Dict[str, Dict[str, Any]], set[str]]:
    """从本机草稿收集贴纸素材模板；返回 (resource_id→素材, 可信 id 集合)。"""
    templates: Dict[str, Dict[str, Any]] = {}
    local = os.environ.get("LOCALAPPDATA", "")
    for app_name in ("JianyingPro", "CapCut"):
        draft_root = os.path.join(local, app_name, "User Data", "Projects", "com.lveditor.draft")
        if not os.path.isdir(draft_root):
            continue
        try:
            for name in os.listdir(draft_root):
                p = os.path.join(draft_root, name, "draft_content.json")
                if not os.path.isfile(p):
                    continue
                data = _safe_read_json(p)
                if not isinstance(data, dict):
                    continue
                for stk in (data.get("materials") or {}).get("stickers") or []:
                    if not isinstance(stk, dict):
                        continue
                    rid = str(stk.get("resource_id") or stk.get("sticker_id") or "").strip()
                    if not rid.isdigit() or not _sticker_material_path_matches(rid, stk):
                        continue
                    prev = templates.get(rid)
                    if prev is None or _sticker_material_template_score(stk) > _sticker_material_template_score(prev):
                        templates[rid] = copy.deepcopy(stk)
        except OSError:
            pass

    name_to_rids: Dict[str, List[str]] = {}
    icon_to_rids: Dict[str, List[str]] = {}
    for rid, mat in templates.items():
        name = str(mat.get("name") or "").strip()
        if name:
            name_to_rids.setdefault(name, []).append(rid)
        icon = str(mat.get("icon_url") or "").strip()
        if icon:
            icon_to_rids.setdefault(icon, []).append(rid)

    suspicious: set[str] = set()
    for group in list(name_to_rids.values()) + list(icon_to_rids.values()):
        if len(group) > 1:
            suspicious.update(group)

    trusted = {rid for rid in templates if rid not in suspicious}
    return templates, trusted


def _get_sticker_material_templates() -> Tuple[Dict[str, Dict[str, Any]], set[str]]:
    global _STICKER_MATERIAL_TEMPLATE_CACHE, _STICKER_MATERIAL_TEMPLATE_TRUSTED
    if _STICKER_MATERIAL_TEMPLATE_CACHE is None or _STICKER_MATERIAL_TEMPLATE_TRUSTED is None:
        _STICKER_MATERIAL_TEMPLATE_CACHE, _STICKER_MATERIAL_TEMPLATE_TRUSTED = harvest_sticker_material_templates()
    return _STICKER_MATERIAL_TEMPLATE_CACHE, _STICKER_MATERIAL_TEMPLATE_TRUSTED


def _build_sticker_material_for_replace(
    resource_id: str,
    material_id: str,
    source_mat: Dict[str, Any],
) -> Optional[Dict[str, Any]]:
    """生成可写入 draft 的完整贴纸素材（保留片段 material_id）。"""
    rid = str(resource_id or "").strip()
    if not rid or _sticker_cache_is_text_template(rid):
        return None
    cache_path = _resolve_sticker_cache_path(rid)
    if cache_path == "C:":
        return None

    templates, trusted = _get_sticker_material_templates()
    tpl = templates.get(rid)
    if tpl is not None and rid in trusted:
        mat = copy.deepcopy(tpl)
    else:
        mat = copy.deepcopy(source_mat)
        for key in ("name", "icon_url", "preview_cover_url", "request_id"):
            mat[key] = ""

    mat["id"] = material_id
    mat["resource_id"] = rid
    mat["sticker_id"] = rid
    mat["path"] = cache_path
    mat["type"] = "sticker"
    if not mat.get("source_platform"):
        mat["source_platform"] = 1
    if not mat.get("platform"):
        mat["platform"] = "all"
    if mat.get("check_flag") is None:
        mat["check_flag"] = 1
    if not mat.get("category_id"):
        mat["category_id"] = "heycan_search_sticker"
    if not mat.get("category_name"):
        mat["category_name"] = mat.get("category_id") or "heycan_search_sticker"
    if not mat.get("aigc_type"):
        mat["aigc_type"] = "none"
    osz = _sticker_original_size_from_cache(rid)
    if osz:
        mat["original_size"] = osz
    elif mat.get("original_size") is None:
        mat["original_size"] = []
    return mat


def build_sticker_resource_id_pool(parent_content_path: str) -> Tuple[List[str], List[str]]:
    """从贴纸池配置、本机 harvest、父稿已用贴纸合并，并过滤无效 id。"""
    pool_raw: List[str] = []
    seen: set[str] = set()
    for src in (load_user_sticker_resource_id_pool(), harvest_local_sticker_resource_ids()):
        for rid in src:
            r = str(rid or "").strip()
            if r and r not in seen:
                seen.add(r)
                pool_raw.append(r)
    data = _safe_read_json(parent_content_path)
    if isinstance(data, dict):
        for stk in (data.get("materials") or {}).get("stickers") or []:
            if not isinstance(stk, dict):
                continue
            r = str(stk.get("resource_id") or stk.get("sticker_id") or "").strip()
            if r and r not in seen:
                seen.add(r)
                pool_raw.append(r)
    return filter_valid_sticker_resource_ids(pool_raw)


def filter_valid_sticker_resource_ids(resource_ids: Iterable[str]) -> Tuple[List[str], List[str]]:
    valid: List[str] = []
    invalid: List[str] = []
    seen: set[str] = set()
    for raw in resource_ids:
        rid = str(raw or "").strip()
        if not rid or rid in seen:
            continue
        seen.add(rid)
        if _sticker_resource_id_is_usable(rid):
            valid.append(rid)
        else:
            invalid.append(rid)
    return valid, invalid


def sanitize_segment_export_pool_styles(
    pool: Dict[str, Dict[str, Any]],
    parent_content_json: str = "",
) -> Tuple[Dict[str, Dict[str, Any]], List[str]]:
    """导出前修正无效的「指定花字/贴纸 id」为池随机；不删除槽位配置。"""
    if not isinstance(pool, dict):
        return {}, []
    if not pool:
        return {}, []
    out: Dict[str, Dict[str, Any]] = {}
    notes: List[str] = []
    for sk, sv in pool.items():
        if not isinstance(sv, dict):
            continue
        piece = dict(sv)
        cfg = normalize_style_pool_config(piece)
        if cfg and cfg.get("style_mode") == STYLE_MODE_FIXED:
            kind = cfg.get("style_kind")
            rid = str(cfg.get("style_resource_id") or "").strip()
            invalid = False
            pool_name = ""
            if kind == STYLE_KIND_STICKER:
                pool_name = "贴纸"
                invalid = not _sticker_resource_id_is_usable(rid)
            elif kind == STYLE_KIND_TEXT_EFFECT:
                pool_name = "花字"
                invalid = not _subtitle_flower_effect_id_is_usable(rid)
            if invalid and pool_name:
                slot_hint = str(sk).split("\0")[-1] if "\0" in str(sk) else str(sk)
                piece["style_kind"] = kind
                piece["style_mode"] = STYLE_MODE_RANDOM
                piece.pop("style_resource_id", None)
                notes.append(
                    f"{pool_name} 片段#{slot_hint}：指定 id {rid} 无效或未缓存，导出时改为池随机"
                )
        if piece:
            out[str(sk)] = piece
    return out, notes


def prune_invalid_sticker_ids_from_pool_file() -> Tuple[int, int]:
    """从 sticker_pool.json 移除无效 resource_id。返回 (移除数, 保留数)。"""
    path = _sticker_pool_pref_path()
    listed = load_user_sticker_resource_id_pool()
    if not listed:
        return 0, 0
    valid, invalid = filter_valid_sticker_resource_ids(listed)
    if not invalid:
        return 0, len(valid)
    payload: Dict[str, Any] = {
        "_comment": (
            "resource_ids：剪映贴纸 resource_id（与 sticker_id 相同）。"
            "程序启动时会从本机草稿/artistEffect 缓存自动追加，并移除无效 id。"
            "在剪映「贴纸」面板多预览几种可扩充缓存。"
        ),
        "resource_ids": valid,
        "_pruned_invalid_count": len(invalid),
    }
    try:
        if path.is_file():
            try:
                with open(path, "r", encoding="utf-8") as f:
                    prev = json.load(f)
                if isinstance(prev, dict):
                    for k, v in prev.items():
                        if k.startswith("_") and k not in payload:
                            payload[k] = v
            except (OSError, json.JSONDecodeError, TypeError):
                pass
        tmp = path.with_suffix(".json.tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
    except OSError:
        return 0, len(valid)
    _invalidate_sticker_material_template_cache()
    return len(invalid), len(valid)


def build_sticker_pool_report(
    parent_content_json: Optional[str] = None,
    *,
    resync: bool = False,
) -> Dict[str, Any]:
    added = 0
    removed_invalid = 0
    if resync:
        try:
            added, removed_invalid, _ = sync_harvested_stickers_to_pool_file()
        except OSError:
            pass
    pool_path = ensure_sticker_pool_template_file()
    listed = load_user_sticker_resource_id_pool()
    pool_raw: List[str] = []
    seen: set[str] = set()
    for src in (listed, harvest_local_sticker_resource_ids()):
        for rid in src:
            r = str(rid or "").strip()
            if r and r not in seen:
                seen.add(r)
                pool_raw.append(r)
    parent_p = (
        parent_content_json
        if parent_content_json and os.path.isfile(parent_content_json)
        else ""
    )
    if parent_p:
        data = _safe_read_json(parent_p)
        if isinstance(data, dict):
            for stk in (data.get("materials") or {}).get("stickers") or []:
                if not isinstance(stk, dict):
                    continue
                r = str(stk.get("resource_id") or stk.get("sticker_id") or "").strip()
                if r and r not in seen:
                    seen.add(r)
                    pool_raw.append(r)
    valid, invalid = filter_valid_sticker_resource_ids(pool_raw)
    return {
        "pool_path": pool_path,
        "added_on_sync": added,
        "pruned_invalid_count": removed_invalid,
        "listed_count": len(listed),
        "valid_ids": valid,
        "invalid_ids": invalid,
        "valid_count": len(valid),
        "invalid_count": len(invalid),
    }


def format_sticker_pool_report_text(report: Dict[str, Any]) -> str:
    lines = [
        "贴纸池检测报告",
        "",
        f"配置文件：{report.get('pool_path', '')}",
        f"配置中记录：{report.get('listed_count', 0)} 个 id",
        f"可用（本机已完整缓存或草稿已验证）：{report.get('valid_count', 0)} 个",
        f"无效（空壳缓存/非贴纸/id 过短）：{report.get('invalid_count', 0)} 个",
    ]
    added = int(report.get("added_on_sync") or 0)
    if added > 0:
        lines.append(f"本次同步新写入配置：{added} 个 id")
    pruned = int(report.get("pruned_invalid_count") or 0)
    if pruned > 0:
        lines.append(f"本次已从配置文件清理无效 id：{pruned} 个")
    lines.extend(["", "【可用贴纸 id】"])
    valid_ids = report.get("valid_ids") or []
    if valid_ids:
        names = get_sticker_display_names()
        for rid in valid_ids:
            label = style_resource_picker_label_for_id(str(rid), names.get(str(rid), ""))
            lines.append(f"  · {label}  (InfoSticker)")
    else:
        lines.append("  （无）")
    lines.append("")
    lines.append("【无效 id】")
    invalid_ids = report.get("invalid_ids") or []
    if invalid_ids:
        show = invalid_ids[:24]
        lines.extend(f"  · {rid}" for rid in show)
        if len(invalid_ids) > len(show):
            lines.append(f"  … 另有 {len(invalid_ids) - len(show)} 个未列出")
    else:
        lines.append("  （无）")
    lines.extend(
        [
            "",
            "说明：贴纸与字幕花字是不同素材；花字池里的「无效」项很多其实是贴纸 id。",
            "TextTemplate 复合贴纸（缓存 content.json 含文字模板）不会纳入可用池。",
            "仅含 InfoSticker 空壳目录、无 heycanInfo.json 且草稿未用过的 id 视为无效。",
            "如何扩充：剪映 5.9 →「贴纸」面板多预览/添加到时间轴 → 本程序「检测贴纸池」→「同步并刷新」。",
            "导出区贴纸请在时间轴选中贴纸轨并点「替换…」配置。",
        ]
    )
    return "\n".join(lines)


_TEXT_EFFECT_DISPLAY_NAME_CACHE: Optional[Dict[str, str]] = None


def harvest_text_effect_display_names(
    extra_draft_root: Optional[str] = None,
) -> Dict[str, str]:
    """花字 effect_id → 显示名（草稿扫描 + 配置文件 ``effect_names``）。"""
    return get_text_effect_display_names(extra_draft_root=extra_draft_root)


def get_text_effect_display_names(
    extra_draft_root: Optional[str] = None,
) -> Dict[str, str]:
    global _TEXT_EFFECT_DISPLAY_NAME_CACHE
    if _TEXT_EFFECT_DISPLAY_NAME_CACHE is not None and not extra_draft_root:
        return _TEXT_EFFECT_DISPLAY_NAME_CACHE
    harvested = harvest_text_effect_display_names_from_drafts(extra_draft_root)
    overrides = load_text_effect_display_name_overrides()
    merged = _merge_text_effect_display_name_maps(harvested, overrides)
    if not extra_draft_root:
        _TEXT_EFFECT_DISPLAY_NAME_CACHE = merged
    return merged


def text_effect_picker_label_for_id(effect_id: str, name_map: Optional[Dict[str, str]] = None) -> str:
    """下拉项：优先中文名；无名称时标注花字类型 + id。"""
    eid = str(effect_id or "").strip()
    if not eid:
        return ""
    name_map = name_map or {}
    name = str(name_map.get(eid) or "").strip()
    if name:
        return style_resource_picker_label_for_id(eid, name)
    kind = _classify_subtitle_flower_effect_id(eid)
    tag = "SDFText" if kind == "sdftext" else ("TextStyle" if kind == "text_style" else "花字")
    return f"{tag} · {eid}"


def _invalidate_text_effect_display_name_cache() -> None:
    global _TEXT_EFFECT_DISPLAY_NAME_CACHE
    _TEXT_EFFECT_DISPLAY_NAME_CACHE = None


def get_sticker_display_names() -> Dict[str, str]:
    """贴纸 resource_id → 显示名（来自本机草稿贴纸素材）。"""
    templates, _ = _get_sticker_material_templates()
    out: Dict[str, str] = {}
    for rid, mat in templates.items():
        name = str(mat.get("name") or "").strip()
        if name:
            out[str(rid)] = name
    return out


def _truncate_style_resource_label(text: str, *, max_len: int = 36) -> str:
    t = " ".join(str(text or "").split())
    if len(t) <= max_len:
        return t
    return t[: max_len - 1].rstrip() + "…"


def style_resource_picker_label_for_id(resource_id: str, display_name: str = "") -> str:
    rid = str(resource_id or "").strip()
    if not rid:
        return ""
    name = _truncate_style_resource_label(str(display_name or "").strip())
    if name:
        return f"{name} · {rid}"
    return rid


def build_style_resource_picker_choices(
    valid_ids: Iterable[str],
    name_map: Optional[Dict[str, str]] = None,
    *,
    empty_label: str = "（请选择）",
) -> Tuple[List[str], Dict[str, str]]:
    """构建下拉显示项与 label→resource_id 映射（label 含名称与 id）。"""
    name_map = name_map or {}
    labels: List[str] = [empty_label]
    label_to_id: Dict[str, str] = {empty_label: ""}
    seen_labels: set[str] = {empty_label}
    for raw in valid_ids:
        rid = str(raw or "").strip()
        if not rid:
            continue
        label = style_resource_picker_label_for_id(rid, name_map.get(rid, ""))
        if label in seen_labels:
            n = 2
            while f"{label}#{n}" in seen_labels:
                n += 1
            label = f"{label}#{n}"
        labels.append(label)
        label_to_id[label] = rid
        seen_labels.add(label)
    return labels, label_to_id


def build_text_effect_picker_choices(
    valid_ids: Iterable[str],
    name_map: Optional[Dict[str, str]] = None,
    *,
    empty_label: str = "（请选择）",
) -> Tuple[List[str], Dict[str, str]]:
    """花字下拉：有中文名则「名称 · id」，否则「TextStyle/SDFText · id」。"""
    name_map = name_map or {}
    labels: List[str] = [empty_label]
    label_to_id: Dict[str, str] = {empty_label: ""}
    seen_labels: set[str] = {empty_label}
    for raw in valid_ids:
        rid = str(raw or "").strip()
        if not rid:
            continue
        label = text_effect_picker_label_for_id(rid, name_map)
        if label in seen_labels:
            n = 2
            while f"{label}#{n}" in seen_labels:
                n += 1
            label = f"{label}#{n}"
        labels.append(label)
        label_to_id[label] = rid
        seen_labels.add(label)
    return labels, label_to_id


def open_sticker_pool_inspector(
    parent: Any,
    *,
    get_draft_root: Any,
    get_selected_draft_name: Any,
    on_status_update: Optional[Any] = None,
) -> None:
    import customtkinter as ctk
    from tkinter import messagebox

    def _parent_content_json() -> str:
        dr = (get_draft_root() or "").strip()
        nm = (get_selected_draft_name() or "").strip()
        if dr and nm:
            p = os.path.join(dr, nm, "draft_content.json")
            if os.path.isfile(p):
                return p
        return ""

    win = ctk.CTkToplevel(parent)
    win.title("贴纸池检测")
    win.geometry("560x480")
    win.minsize(480, 360)
    win.transient(parent)

    main = ctk.CTkFrame(win, fg_color="transparent")
    main.pack(fill="both", expand=True, padx=14, pady=12)
    ctk.CTkLabel(
        main,
        text="检测本机可用贴纸 resource_id（InfoSticker 缓存）",
        font=ctk.CTkFont(size=13, weight="bold"),
        anchor="w",
    ).pack(fill="x", pady=(0, 8))

    box = ctk.CTkTextbox(main, font=ctk.CTkFont(family="Consolas", size=12))
    box.pack(fill="both", expand=True, pady=(0, 10))

    def _reload(*, resync: bool) -> None:
        try:
            rep = build_sticker_pool_report(_parent_content_json(), resync=resync)
        except OSError as e:
            messagebox.showerror("贴纸池", f"检测失败：\n{e}", parent=win)
            return
        box.delete("1.0", "end")
        box.insert("1.0", format_sticker_pool_report_text(rep))
        if callable(on_status_update):
            try:
                on_status_update()
            except Exception:
                pass
        if resync:
            n = int(rep.get("valid_count") or 0)
            pruned = int(rep.get("pruned_invalid_count") or 0)
            msg = f"已同步扫描。\n可用贴纸：{n} 个。"
            if pruned > 0:
                msg += f"\n已从配置清理无效 id：{pruned} 个。"
            messagebox.showinfo("贴纸池", msg, parent=win)

    btn_row = ctk.CTkFrame(main, fg_color="transparent")
    btn_row.pack(fill="x")
    ctk.CTkButton(btn_row, text="同步并刷新", width=110, command=lambda: _reload(resync=True)).pack(
        side="left", padx=(0, 8)
    )

    def _open_pool_file() -> None:
        try:
            p = ensure_sticker_pool_template_file()
            if sys.platform == "win32":
                os.startfile(p)  # type: ignore[attr-defined]
            else:
                messagebox.showinfo("贴纸池", p, parent=win)
        except OSError as e:
            messagebox.showerror("贴纸池", str(e), parent=win)

    ctk.CTkButton(
        btn_row,
        text="打开配置文件",
        width=110,
        fg_color=("gray70", "gray38"),
        command=_open_pool_file,
    ).pack(side="left", padx=(0, 8))
    ctk.CTkButton(btn_row, text="关闭", width=72, fg_color="transparent", border_width=1, command=win.destroy).pack(
        side="right"
    )

    _reload(resync=False)
    win.grab_set()
    win.focus_force()


def _pick_text_effect_id(pool: List[str], used_in_batch: Optional[set[str]] = None) -> str:
    """从池中抽取花字 id；同一批次内优先不重复。"""
    if not pool:
        raise ValueError("花字池为空")
    if used_in_batch is not None:
        available = [x for x in pool if x not in used_in_batch]
        if not available:
            available = list(pool)
        pick = random.choice(available)
        used_in_batch.add(pick)
        return pick
    return random.choice(pool)


def _text_material_ids_on_text_tracks(content: Dict[str, Any]) -> List[str]:
    out: List[str] = []
    seen: set[str] = set()
    for tr in content.get("tracks") or []:
        if str(tr.get("type", "")) != "text":
            continue
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            mid = str(seg.get("material_id") or "").strip()
            if mid and mid not in seen:
                seen.add(mid)
                out.append(mid)
    return out


def _subtitle_text_material_ids(content: Dict[str, Any]) -> List[str]:
    """文本轨道上字幕素材 id；若无 type=subtitle 则退回该轨全部文本。"""
    track_ids = _text_material_ids_on_text_tracks(content)
    mats = {
        str(m.get("id")): m
        for m in (content.get("materials") or {}).get("texts") or []
        if isinstance(m, dict) and m.get("id")
    }
    subs = [mid for mid in track_ids if str(mats.get(mid, {}).get("type", "")) == "subtitle"]
    return subs if subs else track_ids


def _extract_text_style_snapshot(mat: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    raw = mat.get("content")
    if not isinstance(raw, str) or not raw.strip().startswith("{"):
        return None
    try:
        content = json.loads(raw)
    except json.JSONDecodeError:
        return None
    styles = content.get("styles")
    if not isinstance(styles, list) or not styles:
        return None
    st0 = styles[0] if isinstance(styles[0], dict) else {}
    color: Tuple[float, float, float] = (1.0, 1.0, 1.0)
    try:
        solid = st0["fill"]["content"]["solid"]["color"]
        color = (float(solid[0]), float(solid[1]), float(solid[2]))
    except (KeyError, TypeError, IndexError, ValueError):
        pass
    font_id: Optional[str] = None
    font = st0.get("font")
    if isinstance(font, dict):
        font_id = str(font.get("id") or "").strip() or None
    effect_id: Optional[str] = None
    es = st0.get("effectStyle")
    if isinstance(es, dict):
        effect_id = str(es.get("id") or "").strip() or None
    try:
        size = float(st0.get("size") or 5.0)
    except (TypeError, ValueError):
        size = 5.0
    return {
        "size": size,
        "color": color,
        "font_id": font_id,
        "effect_id": effect_id,
        "bold": bool(st0.get("bold")),
        "italic": bool(st0.get("italic")),
        "underline": bool(st0.get("underline")),
        "strokes": copy.deepcopy(st0.get("strokes") if isinstance(st0.get("strokes"), list) else []),
        "alignment": mat.get("alignment"),
    }


def _subtitle_style_preset_key(preset: Dict[str, Any]) -> Tuple[Any, ...]:
    return (
        preset.get("font_id"),
        tuple(preset.get("color") or ()),
        preset.get("effect_id"),
        preset.get("size"),
    )


def _random_builtin_subtitle_style() -> Dict[str, Any]:
    effect_id: Optional[str] = None
    if _SUBTITLE_TEXT_EFFECT_IDS and random.random() < 0.42:
        effect_id = random.choice(_SUBTITLE_TEXT_EFFECT_IDS)
    strokes: List[Any] = []
    if random.random() < 0.28:
        strokes = [
            {
                "content": {"solid": {"alpha": 1.0, "color": [0.0, 0.0, 0.0]}},
                "width": 0.08,
            }
        ]
    return {
        "size": random.choice([4.5, 5.0, 5.5, 6.0, 6.5, 7.0, 8.0]),
        "color": random.choice(_SUBTITLE_COLOR_RGB),
        "font_id": random.choice(_SUBTITLE_FONT_RESOURCE_IDS),
        "effect_id": effect_id,
        "bold": random.random() < 0.18,
        "italic": False,
        "underline": False,
        "strokes": strokes,
        "alignment": 1,
    }


def build_subtitle_style_presets(parent_content_path: str, *, min_pool: int = 10) -> List[Dict[str, Any]]:
    """从父草稿已有字幕/文本样式抽取预设，并补足内置随机组合供子稿抽取。"""
    presets: List[Dict[str, Any]] = []
    seen: set[Tuple[Any, ...]] = set()
    data = _safe_read_json(parent_content_path)
    if isinstance(data, dict):
        mats = {
            str(m.get("id")): m
            for m in (data.get("materials") or {}).get("texts") or []
            if isinstance(m, dict) and m.get("id")
        }
        for mid in _subtitle_text_material_ids(data):
            mat = mats.get(mid)
            if not isinstance(mat, dict):
                continue
            snap = _extract_text_style_snapshot(mat)
            if not snap:
                continue
            key = _subtitle_style_preset_key(snap)
            if key in seen:
                continue
            seen.add(key)
            presets.append(snap)
    while len(presets) < max(min_pool, 8):
        cand = _random_builtin_subtitle_style()
        key = _subtitle_style_preset_key(cand)
        if key in seen:
            continue
        seen.add(key)
        presets.append(cand)
    return presets


def _subtitle_style_preset_label(preset: Dict[str, Any]) -> str:
    parts: List[str] = []
    if preset.get("font_id"):
        parts.append(f"字体={preset['font_id']}")
    col = preset.get("color")
    if isinstance(col, (list, tuple)) and len(col) >= 3:
        parts.append(
            "颜色=({:.2f},{:.2f},{:.2f})".format(float(col[0]), float(col[1]), float(col[2]))
        )
    try:
        parts.append(f"字号={float(preset.get('size') or 5):g}")
    except (TypeError, ValueError):
        pass
    if preset.get("effect_id"):
        parts.append(f"花字={preset['effect_id']}")
    return "，".join(parts) if parts else "随机样式"


def _text_decor_effect_global_ids(materials: Dict[str, Any]) -> set[str]:
    out: set[str] = set()
    for eff in materials.get("effects") or []:
        if not isinstance(eff, dict):
            continue
        if eff.get("type") in ("text_effect", "text_shape"):
            gid = str(eff.get("id") or "").strip()
            if gid:
                out.add(gid)
    return out


def _prune_text_effects_except(materials: Dict[str, Any], keep_gid: str) -> None:
    """去掉多余的 text_effect 条目，避免复制子稿后 effects 列表膨胀。"""
    effects = materials.get("effects")
    if not isinstance(effects, list):
        return
    keep = str(keep_gid or "").strip()
    materials["effects"] = [
        eff
        for eff in effects
        if not (
            isinstance(eff, dict)
            and eff.get("type") == "text_effect"
            and str(eff.get("id") or "").strip() != keep
        )
    ]


def _ensure_text_effect_material(materials: Dict[str, Any], effect_id: str) -> str:
    """在 materials.effects 中确保存在花字条目，返回其 global id。"""
    effects = materials.setdefault("effects", [])
    if not isinstance(effects, list):
        effects = []
        materials["effects"] = effects
    for eff in effects:
        if not isinstance(eff, dict):
            continue
        if eff.get("type") == "text_effect" and str(eff.get("effect_id") or "") == effect_id:
            gid = str(eff.get("id") or "").strip()
            if gid:
                return gid
    gid = uuid.uuid4().hex
    effects.append(
        {
            "apply_target_type": 0,
            "effect_id": effect_id,
            "id": gid,
            "resource_id": effect_id,
            "type": "text_effect",
            "value": 1.0,
            "source_platform": 1,
        }
    )
    return gid


def _text_effect_global_ids(materials: Dict[str, Any]) -> set[str]:
    """仅花字（text_effect）实例 id，不含气泡 text_shape。"""
    out: set[str] = set()
    for eff in materials.get("effects") or []:
        if not isinstance(eff, dict):
            continue
        if eff.get("type") == "text_effect":
            gid = str(eff.get("id") or "").strip()
            if gid:
                out.add(gid)
    return out


def _apply_text_effect_id_to_content(
    content: Dict[str, Any],
    effect_id: str,
    material_ids: List[str],
) -> int:
    """仅替换花字：改 content.styles[].effectStyle 与 segment.extra_material_refs，不动字体/颜色/字号。"""
    materials = content.setdefault("materials", {})
    if not isinstance(materials, dict):
        return 0
    texts = materials.get("texts")
    if not isinstance(texts, list):
        return 0
    mat_by_id = {str(m.get("id")): m for m in texts if isinstance(m, dict) and m.get("id")}
    effect_gid = _ensure_text_effect_material(materials, effect_id)
    _prune_text_effects_except(materials, effect_gid)
    remove_effect_gids = _text_effect_global_ids(materials) - {effect_gid}
    style_path = _resolve_subtitle_flower_effect_style_path(effect_id)

    seg_by_mat: Dict[str, List[Dict[str, Any]]] = {}
    for tr in content.get("tracks") or []:
        if str(tr.get("type", "")) != "text":
            continue
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            mid = str(seg.get("material_id") or "").strip()
            if mid in material_ids:
                seg_by_mat.setdefault(mid, []).append(seg)

    n = 0
    for mid in material_ids:
        mat = mat_by_id.get(mid)
        if not isinstance(mat, dict):
            continue
        raw = mat.get("content")
        if not isinstance(raw, str) or not raw.strip().startswith("{"):
            continue
        try:
            body = json.loads(raw)
        except json.JSONDecodeError:
            continue
        styles = body.get("styles")
        if not isinstance(styles, list) or not styles:
            text = str(body.get("text") or "")
            styles = [{"range": [0, len(text)]}]
            body["styles"] = styles
        for st in styles:
            if isinstance(st, dict):
                st["effectStyle"] = {"id": effect_id, "path": style_path}
        mat["content"] = json.dumps(body, ensure_ascii=False)
        for seg in seg_by_mat.get(mid, []):
            refs = [str(r) for r in (seg.get("extra_material_refs") or []) if r]
            refs = [r for r in refs if r not in remove_effect_gids]
            if effect_gid not in refs:
                refs.append(effect_gid)
            seg["extra_material_refs"] = refs
        n += 1
    return n


def _apply_sticker_resource_id_to_content(
    content: Dict[str, Any],
    resource_id: str,
    material_ids: List[str],
) -> int:
    """子稿内贴纸轨素材整段替换（含 name/icon/path 等），片段 clip 不变。"""
    materials = content.setdefault("materials", {})
    if not isinstance(materials, dict):
        return 0
    stickers = materials.get("stickers")
    if not isinstance(stickers, list):
        return 0
    mat_by_id = {str(m.get("id")): m for m in stickers if isinstance(m, dict) and m.get("id")}
    n = 0
    for mid in material_ids:
        mat = mat_by_id.get(mid)
        if not isinstance(mat, dict):
            continue
        new_mat = _build_sticker_material_for_replace(resource_id, mid, mat)
        if not isinstance(new_mat, dict):
            continue
        for i, item in enumerate(stickers):
            if isinstance(item, dict) and str(item.get("id")) == mid:
                stickers[i] = new_mat
                n += 1
                break
    return n


def apply_per_segment_style_pools_to_draft(
    content_json_path: str,
    draft_name: str,
    style_pool: Dict[str, Dict[str, Any]],
    style_refs: List[StyleSegmentRef],
    *,
    text_effect_id_pool: Optional[List[str]] = None,
    sticker_id_pool: Optional[List[str]] = None,
    used_fx_batch: Optional[set[str]] = None,
    used_sticker_batch: Optional[set[str]] = None,
) -> Tuple[int, List[str]]:
    """对 segment_export_pool 中已配置的花字/贴纸槽，在导出或生成子稿时套用。"""
    style_pool, sanitize_notes = sanitize_segment_export_pool_styles(
        dict(style_pool) if isinstance(style_pool, dict) else {},
        content_json_path,
    )
    for note in sanitize_notes:
        print(f"[槽位修正] {note}")
    data = _safe_read_json(content_json_path)
    if not isinstance(data, dict):
        return 0, ["无法读取 draft_content.json"]
    dn = (draft_name or "").strip()
    if not dn or not isinstance(style_pool, dict):
        return 0, []
    text_pool = [str(x).strip() for x in (text_effect_id_pool or []) if str(x).strip()]
    sticker_pool = [str(x).strip() for x in (sticker_id_pool or []) if str(x).strip()]
    if not text_pool:
        text_pool, _ = build_text_effect_id_pool(content_json_path)
    if not sticker_pool:
        sticker_pool, _ = build_sticker_resource_id_pool(content_json_path)
    ref_by_key = {segment_style_pool_key(dn, r): r for r in style_refs}
    n = 0
    errors: List[str] = []
    pfx = dn + "\0"
    for sk, raw_cfg in style_pool.items():
        if not isinstance(sk, str) or not sk.startswith(pfx):
            continue
        cfg = normalize_style_pool_config(raw_cfg)
        if not cfg:
            continue
        ref = ref_by_key.get(sk)
        if ref is None:
            continue
        kind = cfg.get("style_kind")
        mode = cfg.get("style_mode")
        fixed_id = str(cfg.get("style_resource_id") or "").strip()
        if kind == STYLE_KIND_TEXT_EFFECT:
            if mode == STYLE_MODE_FIXED:
                if not fixed_id:
                    errors.append(f"{ref.combo_label}：未指定花字 id")
                    continue
                if not _subtitle_flower_effect_id_is_usable(fixed_id):
                    errors.append(f"{ref.combo_label}：花字 id {fixed_id} 无效或未缓存")
                    continue
                rid = fixed_id
            else:
                if not text_pool:
                    errors.append(f"{ref.combo_label}：花字池为空")
                    continue
                rid = _pick_text_effect_id(text_pool, used_fx_batch)
            applied = _apply_text_effect_id_to_content(data, rid, [ref.material_id])
        elif kind == STYLE_KIND_STICKER:
            if mode == STYLE_MODE_FIXED:
                if not fixed_id:
                    errors.append(f"{ref.combo_label}：未指定贴纸 id")
                    continue
                if not _sticker_resource_id_is_usable(fixed_id):
                    errors.append(f"{ref.combo_label}：贴纸 id {fixed_id} 无效或未缓存")
                    continue
                rid = fixed_id
            else:
                if not sticker_pool:
                    errors.append(f"{ref.combo_label}：贴纸池为空")
                    continue
                tried: set[str] = set()
                applied = 0
                rid = ""
                while len(tried) < len(sticker_pool):
                    pick = _pick_text_effect_id(sticker_pool, used_sticker_batch)
                    if pick in tried:
                        break
                    tried.add(pick)
                    applied = _apply_sticker_resource_id_to_content(data, pick, [ref.material_id])
                    if applied > 0:
                        rid = pick
                        break
                if applied <= 0:
                    errors.append(f"{ref.combo_label}：未能从贴纸池套用")
                    continue
            if mode == STYLE_MODE_FIXED:
                applied = _apply_sticker_resource_id_to_content(data, rid, [ref.material_id])
        else:
            continue
        if applied <= 0:
            errors.append(f"{ref.combo_label}：未能套用样式")
            continue
        n += applied
    if n > 0:
        _write_draft_content_json(content_json_path, data)
        _invalidate_sticker_material_template_cache()
    return n, errors


def apply_segment_style_pools_or_raise(
    content_json_path: str,
    draft_name: str,
    pool: Dict[str, Dict[str, Any]],
    *,
    text_effect_id_pool: Optional[List[str]] = None,
    sticker_id_pool: Optional[List[str]] = None,
    used_fx_batch: Optional[set[str]] = None,
    used_sticker_batch: Optional[set[str]] = None,
) -> int:
    data = _safe_read_json(content_json_path)
    if not isinstance(data, dict):
        return 0
    refs = list_style_segments_from_content(data)
    n, errs = apply_per_segment_style_pools_to_draft(
        content_json_path,
        draft_name,
        pool,
        refs,
        text_effect_id_pool=text_effect_id_pool,
        sticker_id_pool=sticker_id_pool,
        used_fx_batch=used_fx_batch,
        used_sticker_batch=used_sticker_batch,
    )
    if errs:
        raise RuntimeError("花字/贴纸槽位套用失败：\n" + "\n".join(errs[:12]))
    return n


def _apply_subtitle_style_preset_to_content(
    content: Dict[str, Any],
    preset: Dict[str, Any],
    material_ids: List[str],
) -> int:
    materials = content.setdefault("materials", {})
    if not isinstance(materials, dict):
        return 0
    texts = materials.setdefault("texts", [])
    if not isinstance(texts, list):
        return 0
    mat_by_id = {str(m.get("id")): m for m in texts if isinstance(m, dict) and m.get("id")}
    decor_ids = _text_decor_effect_global_ids(materials)
    effect_gid: Optional[str] = None
    effect_id = str(preset.get("effect_id") or "").strip() or None
    if effect_id:
        effect_gid = _ensure_text_effect_material(materials, effect_id)
        decor_ids = _text_decor_effect_global_ids(materials)

    seg_by_mat: Dict[str, List[Dict[str, Any]]] = {}
    for tr in content.get("tracks") or []:
        if str(tr.get("type", "")) != "text":
            continue
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            mid = str(seg.get("material_id") or "").strip()
            if mid in material_ids:
                seg_by_mat.setdefault(mid, []).append(seg)

    n = 0
    color = preset.get("color") or (1.0, 1.0, 1.0)
    if not isinstance(color, (list, tuple)) or len(color) < 3:
        color = (1.0, 1.0, 1.0)
    color_list = [float(color[0]), float(color[1]), float(color[2])]

    for mid in material_ids:
        mat = mat_by_id.get(mid)
        if not isinstance(mat, dict):
            continue
        raw = mat.get("content")
        if not isinstance(raw, str) or not raw.strip().startswith("{"):
            continue
        try:
            body = json.loads(raw)
        except json.JSONDecodeError:
            continue
        text = str(body.get("text") or "")
        styles = body.get("styles")
        if not isinstance(styles, list) or not styles:
            styles = [{"range": [0, len(text)]}]
            body["styles"] = styles
        for st in styles:
            if not isinstance(st, dict):
                continue
            if "range" not in st:
                st["range"] = [0, len(text)]
            st["size"] = float(preset.get("size") or st.get("size") or 5.0)
            st["bold"] = bool(preset.get("bold"))
            st["italic"] = bool(preset.get("italic"))
            st["underline"] = bool(preset.get("underline"))
            fill = st.setdefault("fill", {})
            if not isinstance(fill, dict):
                fill = {}
                st["fill"] = fill
            fill_content = fill.setdefault("content", {})
            if not isinstance(fill_content, dict):
                fill_content = {}
                fill["content"] = fill_content
            fill_content["render_type"] = "solid"
            solid = fill_content.setdefault("solid", {})
            if not isinstance(solid, dict):
                solid = {}
                fill_content["solid"] = solid
            solid["alpha"] = 1.0
            solid["color"] = color_list
            fill["alpha"] = 1.0
            font_id = str(preset.get("font_id") or "").strip()
            if font_id:
                st["font"] = {"id": font_id, "path": "D:"}
            else:
                st.pop("font", None)
            if effect_id:
                st["effectStyle"] = {"id": effect_id, "path": "C:"}
            else:
                st.pop("effectStyle", None)
            if "strokes" in preset:
                st["strokes"] = copy.deepcopy(preset.get("strokes") or [])
        mat["content"] = json.dumps(body, ensure_ascii=False)
        if preset.get("alignment") is not None:
            mat["alignment"] = preset.get("alignment")
        for seg in seg_by_mat.get(mid, []):
            refs = [str(r) for r in (seg.get("extra_material_refs") or []) if r]
            refs = [r for r in refs if r not in decor_ids]
            if effect_gid:
                refs.append(effect_gid)
            seg["extra_material_refs"] = refs
        n += 1
    return n


def apply_random_subtitle_style_to_draft(
    content_json_path: str,
    style_presets: Optional[List[Dict[str, Any]]] = None,
) -> Tuple[int, str]:
    """为子草稿随机套用一套字幕样式（同子稿内全部字幕统一）。返回 (改动条数, 描述)。"""
    data = _safe_read_json(content_json_path)
    if not isinstance(data, dict):
        return 0, ""
    material_ids = _subtitle_text_material_ids(data)
    if not material_ids:
        return 0, ""
    pool = list(style_presets or [])
    if not pool:
        pool = [_random_builtin_subtitle_style()]
    preset = random.choice(pool)
    n = _apply_subtitle_style_preset_to_content(data, preset, material_ids)
    if n <= 0:
        return 0, ""
    _write_draft_content_json(content_json_path, data)
    return n, _subtitle_style_preset_label(preset)


def backup_plaintext_draft(draft_root: str, draft_name: str) -> str:
    """将草稿整夹复制到草稿根目录下「<草稿文件夹名>_bak」，避免剪映导出保存后加密覆盖原稿。

    返回备份目录路径。
    """
    src = os.path.join(draft_root, draft_name)
    if not os.path.isdir(src):
        raise FileNotFoundError(f"找不到草稿目录:\n{src}")
    dest = os.path.join(draft_root, f"{draft_name}_bak")
    if os.path.isdir(dest):
        shutil.rmtree(dest)
    shutil.copytree(src, dest)
    return dest


def _safe_mp4_name_prefix(raw: str) -> str:
    """导出多条时的文件名前缀，生成「前缀+序号+.mp4」。非法路径字符替换为下划线。"""
    s = (raw or "").strip()
    if not s:
        s = "video_"
    for c in '<>:"/\\|?*':
        s = s.replace(c, "_")
    s = s.rstrip(". ")
    if not s:
        s = "video_"
    return s


def _batch_mp4_paths_with_suffix_on_collision(folder: str, prefix: str, n: int) -> List[str]:
    """第 k 条优先「前缀k.mp4」；若已存在则用「前缀k_1.mp4」「前缀k_2.mp4」… 直至找到空名。"""
    if n < 1:
        return []
    folder_norm = os.path.normpath(folder)
    out: List[str] = []
    for k in range(1, n + 1):
        primary = os.path.join(folder_norm, f"{prefix}{k}.mp4")
        try:
            free = not os.path.exists(primary)
        except OSError:
            free = False
        if free:
            out.append(primary)
            continue
        for s in range(1, 100001):
            cand = os.path.join(folder_norm, f"{prefix}{k}_{s}.mp4")
            try:
                if not os.path.exists(cand):
                    out.append(cand)
                    break
            except OSError:
                continue
        else:
            raise RuntimeError(
                f"无法为第 {k} 条导出分配空闲文件名（已尝试 {prefix}{k}.mp4 与 {prefix}{k}_1 …）。"
            )
    return out


def _center_toplevel_on_root(child: Any, parent: Any, width: int, height: int) -> None:
    """将子窗口置于父窗口（主程序）中心；父窗口尺寸无效时退化为屏幕居中。"""
    parent.update_idletasks()
    child.update_idletasks()
    try:
        rw = parent.winfo_width()
        rh = parent.winfo_height()
        if rw > 1 and rh > 1:
            x = parent.winfo_rootx() + max(0, (rw - width) // 2)
            y = parent.winfo_rooty() + max(0, (rh - height) // 2)
        else:
            sw = child.winfo_screenwidth()
            sh = child.winfo_screenheight()
            x = max(0, (sw - width) // 2)
            y = max(0, (sh - height) // 2)
    except tk.TclError:
        sw = child.winfo_screenwidth()
        sh = child.winfo_screenheight()
        x = max(0, (sw - width) // 2)
        y = max(0, (sh - height) // 2)
    child.geometry(f"{width}x{height}+{int(x)}+{int(y)}")


def _center_window_on_screen(win: Any, width: int, height: int) -> None:
    """将窗口置于当前主屏幕可见区域大致居中（启动时用）。"""
    try:
        win.update_idletasks()
        sw = int(win.winfo_screenwidth())
        sh = int(win.winfo_screenheight())
    except tk.TclError:
        return
    x = max(0, (sw - width) // 2)
    y = max(0, (sh - height) // 2)
    win.geometry(f"{width}x{height}+{x}+{y}")


def _center_ctk_input_dialog_on_parent(dlg: Any, parent: Any) -> None:
    """CTkInputDialog 在 after 中创建子控件，需在尺寸稳定后相对主窗口居中。"""
    attempts = {"n": 0}

    def _try() -> None:
        attempts["n"] += 1
        try:
            dlg.update_idletasks()
            w = max(int(dlg.winfo_width()), int(dlg.winfo_reqwidth()))
            h = max(int(dlg.winfo_height()), int(dlg.winfo_reqheight()))
        except tk.TclError:
            return
        if w < 50 or h < 50:
            if attempts["n"] < 20:
                dlg.after(40, _try)
            return
        try:
            _center_toplevel_on_root(dlg, parent, w, h)
        except tk.TclError:
            pass

    dlg.after(30, _try)


def _move_paths_to_trash(paths: List[str]) -> None:
    """将多个路径一次移入回收站（依赖 Send2Trash）。

    Windows 上应对**整份列表调用一次** send2trash：内部用单次 IFileOperation / SHFileOperation，
    与资源管理器多选删除相近。若对每个文件夹分别调用，会重复初始化 COM 并多次 PerformOperations，
    会明显变慢。
    """
    if not paths:
        return
    if _send2trash_impl is None:
        raise RuntimeError("未安装 Send2Trash，无法移入回收站。请执行：pip install Send2Trash")
    _send2trash_impl(paths)


def _open_containing_folder(path: str) -> None:
    """在系统文件管理器中打开 path 所在目录（path 可为文件或文件夹）。"""
    p = os.path.abspath(os.path.normpath(path))
    folder = p if os.path.isdir(p) else os.path.dirname(p)
    if not folder or not os.path.isdir(folder):
        return
    try:
        if sys.platform == "win32":
            os.startfile(folder)  # type: ignore[attr-defined]
        elif sys.platform == "darwin":
            subprocess.run(["open", folder], check=False)
        else:
            subprocess.run(["xdg-open", folder], check=False)
    except OSError:
        pass


def _jianying_exe_pref_path() -> Path:
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    d = Path(ada) / "pyJianYingDraft_browser"
    d.mkdir(parents=True, exist_ok=True)
    return d / "jianying_exe_preference.json"


def load_jianying_exe_preference() -> Optional[str]:
    path = _jianying_exe_pref_path()
    if not path.is_file():
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        exe = str((data or {}).get("exe") or "").strip()
        return exe if exe else None
    except (OSError, json.JSONDecodeError, TypeError):
        return None


def save_jianying_exe_preference(exe: str) -> None:
    path = _jianying_exe_pref_path()
    tmp = path.with_suffix(".json.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump({"exe": os.path.normpath(exe)}, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def _draft_root_pref_path() -> Path:
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    d = Path(ada) / "pyJianYingDraft_browser"
    d.mkdir(parents=True, exist_ok=True)
    return d / "draft_root_preference.json"


def load_draft_root_preference() -> Optional[str]:
    path = _draft_root_pref_path()
    if not path.is_file():
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        root_p = str((data or {}).get("draft_root") or "").strip()
        return root_p if root_p else None
    except (OSError, json.JSONDecodeError, TypeError):
        return None


def save_draft_root_preference(root_p: str) -> None:
    path = _draft_root_pref_path()
    tmp = path.with_suffix(".json.tmp")
    norm = os.path.normpath(str(root_p).strip())
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump({"draft_root": norm}, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def _export_mp4_ui_pref_path() -> Path:
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    d = Path(ada) / "pyJianYingDraft_browser"
    d.mkdir(parents=True, exist_ok=True)
    return d / "export_mp4_ui_preference.json"


def load_export_mp4_ui_preferences() -> Dict[str, Any]:
    """读取导出 MP4 区已保存的 UI 选项（无效或缺失的键由调用方用默认值处理）。"""
    path = _export_mp4_ui_pref_path()
    if not path.is_file():
        return {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return dict(data) if isinstance(data, dict) else {}
    except (OSError, json.JSONDecodeError, TypeError):
        return {}


def _export_ui_pref_bool(blob: Dict[str, Any], key: str, default: bool) -> bool:
    v = blob.get(key)
    return bool(v) if isinstance(v, bool) else default


def _export_ui_pref_repeat(blob: Dict[str, Any]) -> str:
    v = blob.get("export_repeat", "1")
    if isinstance(v, bool):
        return "1"
    if isinstance(v, int):
        n = v
    else:
        s = str(v).strip() if v is not None else ""
        if not s:
            return "1"
        try:
            n = int(s)
        except ValueError:
            return "1"
    if n < 1:
        return "1"
    if n > 200:
        return "200"
    return str(n)


def _export_ui_pref_name_prefix(blob: Dict[str, Any]) -> str:
    v = blob.get("name_prefix")
    if isinstance(v, str):
        return v
    return "video_"


def save_export_mp4_ui_preferences(updates: Dict[str, Any]) -> None:
    """合并写入 export_mp4_ui_preference.json（只覆盖 updates 中的键）。"""
    path = _export_mp4_ui_pref_path()
    merged: Dict[str, Any] = {}
    if path.is_file():
        try:
            with open(path, "r", encoding="utf-8") as f:
                prev = json.load(f)
            if isinstance(prev, dict):
                merged = dict(prev)
        except (OSError, json.JSONDecodeError, TypeError):
            pass
    for k, v in updates.items():
        merged[k] = v
    tmp = path.with_suffix(".json.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(merged, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def initial_draft_root_for_ui() -> str:
    """启动时草稿根目录：上次保存的路径优先，否则常见剪映/CapCut 默认目录中第一个存在的。"""
    saved = load_draft_root_preference()
    if saved:
        return saved
    defaults = _default_draft_roots()
    return defaults[0] if defaults else ""


def list_jianying_pro_installations() -> List[Tuple[str, str]]:
    """枚举本机剪映专业版安装：(展示名, JianyingPro.exe 绝对路径)，按文件夹 mtime 新→旧。"""
    if sys.platform != "win32":
        return []
    seen: set[str] = set()
    rows: List[Tuple[str, str, float]] = []
    local = os.environ.get("LOCALAPPDATA", "")
    if local:
        apps_root = os.path.join(local, "JianyingPro", "Apps")
        if os.path.isdir(apps_root):
            try:
                for name in os.listdir(apps_root):
                    sub = os.path.join(apps_root, name)
                    if not os.path.isdir(sub):
                        continue
                    exe = os.path.join(sub, "JianyingPro.exe")
                    if not os.path.isfile(exe):
                        continue
                    key = os.path.normcase(os.path.abspath(exe))
                    if key in seen:
                        continue
                    seen.add(key)
                    try:
                        mt = os.path.getmtime(exe)
                    except OSError:
                        mt = 0.0
                    label = f"剪映 {name}" if (name or "").strip() else "剪映（Apps）"
                    rows.append((label, os.path.abspath(exe), mt))
            except OSError:
                pass
        flat = os.path.join(local, "JianyingPro", "JianyingPro.exe")
        if os.path.isfile(flat):
            key = os.path.normcase(os.path.abspath(flat))
            if key not in seen:
                seen.add(key)
                try:
                    mt = os.path.getmtime(flat)
                except OSError:
                    mt = 0.0
                rows.append(("剪映（本地单目录）", os.path.abspath(flat), mt))
    for envkey, tag in (("PROGRAMFILES", "Program Files"), ("PROGRAMFILES(X86)", "Program Files (x86)")):
        base = os.environ.get(envkey, "")
        if not base:
            continue
        exe = os.path.join(base, "JianyingPro", "JianyingPro.exe")
        if not os.path.isfile(exe):
            continue
        key = os.path.normcase(os.path.abspath(exe))
        if key in seen:
            continue
        seen.add(key)
        try:
            mt = os.path.getmtime(exe)
        except OSError:
            mt = 0.0
        rows.append((f"剪映（{tag}）", os.path.abspath(exe), mt))
    rows.sort(key=lambda x: x[2], reverse=True)
    return [(a, b) for a, b, _ in rows]


def _find_jianying_pro_exe() -> Optional[str]:
    """默认使用的剪映 exe：有有效「记住的版本」则用其，否则用最新修改时间的安装。"""
    inst = list_jianying_pro_installations()
    if not inst:
        return None
    pref = load_jianying_exe_preference()
    if pref:
        pn = os.path.normcase(os.path.normpath(pref))
        for _lb, ep in inst:
            if os.path.normcase(os.path.normpath(ep)) == pn:
                return ep
    return inst[0][1]


def show_jianying_install_picker(parent: Any, installs: List[Tuple[str, str]]) -> Optional[str]:
    """多版本时弹出选择；确定返回 exe 路径，取消返回 None。依赖 CustomTkinter。"""
    try:
        import customtkinter as ctk_p
    except ImportError:
        return installs[0][1] if installs else None

    from tkinter import IntVar

    picked: List[Optional[str]] = [None]
    win = ctk_p.CTkToplevel(parent)
    win.title("选择剪映版本")
    win.transient(parent)
    win.resizable(False, False)
    dlg_w, dlg_h = 420, min(120 + len(installs) * 44, 420)
    win.geometry(f"{dlg_w}x{dlg_h}")

    ctk_p.CTkLabel(
        win,
        text="检测到多个剪映安装，请选择用于「打开剪映 / 导出 MP4」的版本：",
        wraplength=380,
        font=ctk_p.CTkFont(size=12),
        anchor="w",
        justify="left",
    ).pack(fill="x", padx=18, pady=(16, 10))

    body = ctk_p.CTkScrollableFrame(win, height=min(len(installs) * 40 + 8, 220))
    body.pack(fill="both", expand=True, padx=14, pady=(0, 8))

    var = IntVar(value=0)
    pref = load_jianying_exe_preference()
    for i, (_lb, ep) in enumerate(installs):
        if pref and os.path.normcase(os.path.normpath(ep)) == os.path.normcase(os.path.normpath(pref)):
            var.set(i)
            break

    for i, (lbl, ep) in enumerate(installs):
        row = ctk_p.CTkFrame(body, fg_color="transparent")
        row.pack(fill="x", pady=4)
        ctk_p.CTkRadioButton(row, text=lbl, variable=var, value=i, font=ctk_p.CTkFont(size=12)).pack(anchor="w")
        ctk_p.CTkLabel(row, text=ep, font=ctk_p.CTkFont(size=10), text_color=("gray40", "gray60"), anchor="w").pack(
            fill="x", padx=(24, 0)
        )

    def on_ok() -> None:
        i = int(var.get())
        if 0 <= i < len(installs):
            picked[0] = installs[i][1]
        try:
            win.grab_release()
        except tk.TclError:
            pass
        win.destroy()

    def on_cancel() -> None:
        try:
            win.grab_release()
        except tk.TclError:
            pass
        win.destroy()

    btn_row = ctk_p.CTkFrame(win, fg_color="transparent")
    btn_row.pack(fill="x", padx=18, pady=(8, 14))
    ctk_p.CTkButton(btn_row, text="取消", width=100, fg_color=("gray70", "gray38"), command=on_cancel).pack(
        side="left", padx=(0, 8)
    )
    ctk_p.CTkButton(btn_row, text="确定", width=100, command=on_ok).pack(side="right")

    win.protocol("WM_DELETE_WINDOW", on_cancel)
    _center_toplevel_on_root(win, parent, dlg_w, dlg_h)
    win.lift()
    win.focus_force()
    try:
        win.grab_set()
    except tk.TclError:
        pass
    parent.wait_window(win)
    return picked[0]


def ensure_jianying_exe_for_ui(parent: Any, *, force_dialog: bool = False) -> Optional[str]:
    """主线程调用：解析要启动的 JianyingPro.exe；多版本时弹窗或沿用已保存选择。"""
    inst = list_jianying_pro_installations()
    if not inst:
        return None
    if len(inst) == 1:
        save_jianying_exe_preference(inst[0][1])
        return inst[0][1]
    pref = load_jianying_exe_preference()
    if not force_dialog and pref:
        pn = os.path.normcase(os.path.normpath(pref))
        for _lb, ep in inst:
            if os.path.normcase(os.path.normpath(ep)) == pn:
                return ep
    choice = show_jianying_install_picker(parent, inst)
    if choice:
        save_jianying_exe_preference(choice)
    return choice


def launch_jianying_pro(exe_path: Optional[str] = None) -> bool:
    """启动本机剪映专业版；成功返回 True。"""
    exe = exe_path or _find_jianying_pro_exe()
    if not exe:
        return False
    try:
        os.startfile(exe)  # type: ignore[attr-defined]
        return True
    except OSError:
        return False


def start_jianying_pro_process(exe_path: Optional[str] = None) -> bool:
    """用子进程启动剪映（便于在启动后继续等待窗口并自动化）；成功返回 True。"""
    exe = exe_path or _find_jianying_pro_exe()
    if not exe:
        return False
    try:
        cwd = os.path.dirname(exe)
        subprocess.Popen([exe], cwd=cwd if cwd else None, close_fds=True)
        return True
    except OSError:
        return False


def wait_jianying_controller_or_launch_process(
    *,
    first_wait_s: float = 5.0,
    after_launch_wait_s: float = 90.0,
    exe_path: Optional[str] = None,
) -> Any:
    """等待或启动剪映；若指定 ``exe_path`` 则只绑定该安装，不抢占其它已运行版本的主窗口。"""
    _ensure_local_pyjianyingdraft_on_path()
    from pyJianYingDraft.exceptions import AutomationError
    from pyJianYingDraft.jianying_controller import wait_for_jianying_controller

    try:
        return wait_for_jianying_controller(timeout=first_wait_s, poll=0.4, exe_path=exe_path)
    except AutomationError:
        if not start_jianying_pro_process(exe_path):
            raise AutomationError("无法启动剪映进程。")
        return wait_for_jianying_controller(timeout=after_launch_wait_s, poll=0.5, exe_path=exe_path)


def _ensure_jianying_home_before_draft_json_write(ctrl: Any) -> None:
    """写入 draft_content.json 前先回到剪映首页。

    若剪映正在编辑同一草稿，直接改磁盘 JSON 后 ``export_draft`` 会 ``switch_to_home`` 关闭工程，
    剪映退出时可能把**内存里的旧稿**写回磁盘，覆盖刚套上的随机素材（子草稿路径不受影响）。
    """
    try:
        ctrl.get_window()
        if ctrl.app_status == "edit":
            ctrl.switch_to_home()
            time.sleep(1.5)
    except Exception:
        pass


def list_draft_folders(root: str) -> List[Tuple[str, float]]:
    """返回 (文件夹名, mtime) 按修改时间倒序"""
    out: List[Tuple[str, float]] = []
    try:
        for name in os.listdir(root):
            p = os.path.join(root, name)
            if os.path.isdir(p):
                try:
                    out.append((name, os.path.getmtime(p)))
                except OSError:
                    out.append((name, 0.0))
    except OSError:
        pass
    out.sort(key=lambda x: x[1], reverse=True)
    return out


_CHILD_DRAFT_SUFFIX_RE = re.compile(r"_(\d+)$")


def _draft_list_sort_key(draft_root: str, folder_name: str) -> Tuple[float, int]:
    """左侧列表排序：按草稿主文件的磁盘修改时间（draft_content.json / draft_meta_info.json 中取较新），否则文件夹 mtime；再按末尾「_N」编号 tie-break。"""
    folder_path = os.path.join(draft_root, folder_name)
    ts = 0.0
    for fname in ("draft_content.json", "draft_meta_info.json"):
        fp = os.path.join(folder_path, fname)
        if not _file_exists_nonempty(fp):
            continue
        try:
            ts = max(ts, os.path.getmtime(fp))
        except OSError:
            pass
    if ts <= 0:
        try:
            ts = os.path.getmtime(folder_path)
        except OSError:
            ts = 0.0
    suffix = 0
    m = _CHILD_DRAFT_SUFFIX_RE.search(folder_name)
    if m:
        try:
            suffix = int(m.group(1))
        except ValueError:
            suffix = 0
    return (ts, suffix)


_DRAFT_LIST_COLORS: Dict[str, Tuple[Tuple[str, str], Tuple[str, str]]] = {
    "leaf": (("gray80", "gray20"), ("gray70", "gray30")),
    "parent": (("gray78", "gray22"), ("gray68", "gray32")),
    "selected": (("#3B8ED0", "#1F538D"), ("#36719F", "#14375E")),
}


def _draft_list_item_wraplength(*, indent: int, reserved_right: int = 0) -> int:
    """左侧栏约 280px，扣除边距/缩进/折叠按钮后为草稿名换行宽度。"""
    return max(96, 236 - max(0, indent) - max(0, reserved_right))


def _bind_draft_name_tooltip(widget: Any, full_name: str) -> None:
    """悬停显示完整草稿名（换行后仍过长时可用）。"""
    tip_ref: List[Optional[Any]] = [None]

    def _hide(_event: Any = None) -> None:
        tw = tip_ref[0]
        if tw is not None:
            try:
                tw.destroy()
            except tk.TclError:
                pass
            tip_ref[0] = None

    def _show(_event: Any) -> None:
        if tip_ref[0] is not None or not str(full_name or "").strip():
            return
        try:
            x = int(widget.winfo_rootx())
            y = int(widget.winfo_rooty()) + int(widget.winfo_height()) + 2
        except tk.TclError:
            return
        tw = tk.Toplevel(widget)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{x}+{y}")
        tk.Label(
            tw,
            text=str(full_name),
            justify="left",
            wraplength=420,
            bg="#ffffe0",
            fg="#111111",
            relief="solid",
            borderwidth=1,
            font=("Segoe UI", 9),
            padx=6,
            pady=4,
        ).pack()
        tip_ref[0] = tw

    widget.bind("<Enter>", _show, add="+")
    widget.bind("<Leave>", _hide, add="+")
    widget.bind("<Button-1>", _hide, add="+")


def _panel_paned_sash_bg() -> str:
    """三栏 PanedWindow 分割条背景，与 CTk 主题一致。"""
    import customtkinter as ctk

    try:
        mode = ctk.get_appearance_mode()
        idx = 1 if str(mode).lower() == "dark" else 0
        return ctk.ThemeManager.theme["CTkFrame"]["fg_color"][idx]
    except (KeyError, IndexError, TypeError):
        return "#2b2b2b"


def _create_three_column_layout(
    parent: Any,
    *,
    left_width: int = 280,
    preview_width: int = 280,
    min_side: int = 168,
    min_center: int = 300,
) -> Tuple[tk.PanedWindow, Any, Any, Any]:
    """左（草稿箱）| 中（时间轴）| 右（播放器），分割条可拖拽调宽。"""
    import customtkinter as ctk

    paned = tk.PanedWindow(
        parent,
        orient=tk.HORIZONTAL,
        sashwidth=6,
        sashrelief=tk.FLAT,
        opaqueresize=True,
        showhandle=False,
        bd=0,
        bg=_panel_paned_sash_bg(),
        sashpad=0,
    )
    left = ctk.CTkFrame(paned, corner_radius=12)
    center = ctk.CTkFrame(paned, corner_radius=12)
    preview_col = ctk.CTkFrame(paned, corner_radius=12)
    paned.add(left, minsize=min_side, width=left_width, stretch="never")
    paned.add(center, minsize=min_center, stretch="always")
    paned.add(preview_col, minsize=min_side, width=preview_width, stretch="never")
    return paned, left, center, preview_col


def _make_draft_list_click_box(
    parent: Any,
    folder_name: str,
    *,
    row_kind: str,
    on_click: Any,
    wraplength: int,
    subtitle: str = "",
) -> Any:
    """可点击、长名自动换行的草稿列表项。"""
    import customtkinter as ctk

    fg, hover = _DRAFT_LIST_COLORS.get(row_kind, _DRAFT_LIST_COLORS["leaf"])
    box = ctk.CTkFrame(parent, fg_color=fg, corner_radius=6, cursor="hand2")
    lbl = ctk.CTkLabel(
        box,
        text=folder_name,
        anchor="w",
        justify="left",
        wraplength=wraplength,
        font=ctk.CTkFont(size=13),
    )
    lbl.pack(fill="x", padx=8, pady=(6, 4 if subtitle else 6))
    if subtitle:
        sub = ctk.CTkLabel(
            box,
            text=subtitle,
            anchor="w",
            font=ctk.CTkFont(size=11),
            text_color=("gray48", "gray58"),
        )
        sub.pack(fill="x", padx=8, pady=(0, 6))
    else:
        sub = None

    box._name = folder_name  # type: ignore[attr-defined]
    box._row_kind = row_kind  # type: ignore[attr-defined]
    box._selected = False  # type: ignore[attr-defined]
    box._base_fg = fg  # type: ignore[attr-defined]
    box._hover_fg = hover  # type: ignore[attr-defined]

    def _click(_event: Any = None) -> None:
        on_click()

    def _enter(_event: Any = None) -> None:
        if not getattr(box, "_selected", False):
            box.configure(fg_color=hover)

    def _leave(_event: Any = None) -> None:
        if getattr(box, "_selected", False):
            box.configure(fg_color=_DRAFT_LIST_COLORS["selected"][0])
        else:
            box.configure(fg_color=fg)

    for w in (box, lbl) + ((sub,) if sub is not None else ()):
        w.bind("<Button-1>", _click)
        w.bind("<Enter>", _enter)
        w.bind("<Leave>", _leave)
    _bind_draft_name_tooltip(box, folder_name)
    return box


def _normalized_draft_root_key(draft_root: str) -> str:
    return os.path.normcase(os.path.normpath(os.path.abspath(draft_root)))


def _draft_families_store_path(draft_root: str) -> Path:
    digest = hashlib.sha256(_normalized_draft_root_key(draft_root).encode("utf-8")).hexdigest()[:24]
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    root = Path(ada) / "pyJianYingDraft_browser"
    root.mkdir(parents=True, exist_ok=True)
    return root / f"draft_families_{digest}.json"


def load_draft_families(draft_root: str) -> Dict[str, Any]:
    path = _draft_families_store_path(draft_root)
    if not path.is_file():
        return {"version": 1, "draft_root": _normalized_draft_root_key(draft_root), "by_parent": {}}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return {"version": 1, "draft_root": _normalized_draft_root_key(draft_root), "by_parent": {}}
    if not isinstance(data, dict):
        return {"version": 1, "draft_root": _normalized_draft_root_key(draft_root), "by_parent": {}}
    bp = data.get("by_parent") or {}
    if not isinstance(bp, dict):
        bp = {}
    clean: Dict[str, List[str]] = {}
    for k, v in bp.items():
        if isinstance(v, list):
            seen: List[str] = []
            for c in v:
                c = str(c)
                if c not in seen:
                    seen.append(c)
            clean[str(k)] = seen
        else:
            clean[str(k)] = []
    data["by_parent"] = clean
    return data


def save_draft_families(draft_root: str, data: Dict[str, Any]) -> None:
    path = _draft_families_store_path(draft_root)
    bp_in = data.get("by_parent") or {}
    by_parent: Dict[str, List[str]] = {}
    if isinstance(bp_in, dict):
        for p, kids in bp_in.items():
            if isinstance(kids, list):
                seen: List[str] = []
                for c in kids:
                    c = str(c)
                    if c not in seen:
                        seen.append(c)
                by_parent[str(p)] = seen
            else:
                by_parent[str(p)] = []
    payload = {
        "version": 1,
        "draft_root": _normalized_draft_root_key(draft_root),
        "by_parent": by_parent,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


POOL_EXPORT_PRESET_DEFAULT = "(默认)"
_LEGACY_POOL_EXPORT_PRESET_MENU_NAMES = frozenset({"(保持原样)"})


def is_pool_export_default_menu_preset(choice: Optional[str]) -> bool:
    """下拉中的「默认」项；兼容磁盘里仍存为「(保持原样)」的旧数据。"""
    s = (str(choice).strip() if choice is not None else "") or ""
    if not s:
        return True
    if s == POOL_EXPORT_PRESET_DEFAULT:
        return True
    if s in _LEGACY_POOL_EXPORT_PRESET_MENU_NAMES:
        return True
    return False


def normalize_pool_export_last_preset_value(choice: Any) -> str:
    """写入 last_preset 时统一为「(默认)」，旧名映射过来。"""
    if is_pool_export_default_menu_preset(choice):
        return POOL_EXPORT_PRESET_DEFAULT
    t = str(choice).strip() if choice is not None else ""
    return t if t else POOL_EXPORT_PRESET_DEFAULT


def _pool_export_presets_store_path(draft_root: str) -> Path:
    digest = hashlib.sha256(_normalized_draft_root_key(draft_root).encode("utf-8")).hexdigest()[:24]
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    root = Path(ada) / "pyJianYingDraft_browser"
    root.mkdir(parents=True, exist_ok=True)
    return root / f"export_pool_presets_{digest}.json"


def _clean_export_pool_presets_dict(raw: Any) -> Dict[str, Dict[str, Any]]:
    """规范化预设名 -> { segment_export_pool, export_pool_sequential_cursor }。"""
    if not isinstance(raw, dict):
        return {}
    clean: Dict[str, Dict[str, Any]] = {}
    for pname, blob in raw.items():
        name = str(pname).strip()
        if not name or is_pool_export_default_menu_preset(name):
            continue
        if not isinstance(blob, dict):
            continue
        seg_in = blob.get("segment_export_pool")
        cur_in = blob.get("export_pool_sequential_cursor")
        seg = _segment_export_pool_for_preset_disk(seg_in if isinstance(seg_in, dict) else {})
        cur: Dict[str, int] = {}
        if isinstance(cur_in, dict):
            for ck, cv in cur_in.items():
                try:
                    cur[str(ck)] = int(cv)
                except (TypeError, ValueError):
                    cur[str(ck)] = 0
        if not seg and not cur:
            continue
        clean[name] = {"segment_export_pool": seg, "export_pool_sequential_cursor": cur}
    return clean


def _merge_export_pool_preset_dicts(a: Dict[str, Dict[str, Any]], b: Dict[str, Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    out = dict(a)
    out.update(b)
    return out


def _filter_export_pool_preset_blob_for_draft(blob: Dict[str, Any], draft_name: str) -> Dict[str, Any]:
    """只保留 segment 键属于指定草稿文件夹名的条目（键前缀为 draft_name + NUL）。"""
    dn = (draft_name or "").strip()
    if not dn:
        return {"segment_export_pool": {}, "export_pool_sequential_cursor": {}}
    prefix = dn + "\0"
    seg_in = blob.get("segment_export_pool") or {}
    cur_in = blob.get("export_pool_sequential_cursor") or {}
    seg: Dict[str, Any] = {}
    if isinstance(seg_in, dict):
        for k, v in seg_in.items():
            if isinstance(k, str) and k.startswith(prefix) and isinstance(v, dict):
                seg[k] = dict(v)
    cur: Dict[str, Any] = {}
    if isinstance(cur_in, dict):
        for k, v in cur_in.items():
            if isinstance(k, str) and k.startswith(prefix):
                try:
                    cur[k] = int(v)
                except (TypeError, ValueError):
                    cur[k] = 0
    return {"segment_export_pool": seg, "export_pool_sequential_cursor": cur}


def load_export_pool_store(draft_root: str) -> Dict[str, Any]:
    """读取槽位预设存储：v2 按草稿文件夹分桶；兼容 v1 顶层 presets 为 legacy_presets。"""
    rk = _normalized_draft_root_key(draft_root)
    path = _pool_export_presets_store_path(draft_root)
    if not path.is_file():
        return {"version": 2, "draft_root": rk, "legacy_presets": {}, "by_draft": {}}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return {"version": 2, "draft_root": rk, "legacy_presets": {}, "by_draft": {}}
    if not isinstance(data, dict):
        return {"version": 2, "draft_root": rk, "legacy_presets": {}, "by_draft": {}}

    by_draft: Dict[str, Any] = {}
    raw_bd = data.get("by_draft")
    if isinstance(raw_bd, dict):
        for dn, bucket in raw_bd.items():
            dname = str(dn).strip()
            if not dname:
                continue
            if not isinstance(bucket, dict):
                continue
            presets_raw = bucket.get("presets")
            clean_pr = _clean_export_pool_presets_dict(presets_raw if isinstance(presets_raw, dict) else {})
            lp = bucket.get("last_preset")
            if not isinstance(lp, str) or not lp.strip():
                lp = POOL_EXPORT_PRESET_DEFAULT
            else:
                lp = normalize_pool_export_last_preset_value(lp.strip())
            entry: Dict[str, Any] = {"presets": clean_pr, "last_preset": lp}
            wp = bucket.get("working_pool")
            if isinstance(wp, dict):
                entry["working_pool"] = wp
            by_draft[dname] = entry

    legacy = _clean_export_pool_presets_dict(data.get("legacy_presets") if isinstance(data.get("legacy_presets"), dict) else {})
    top_presets = data.get("presets")
    if isinstance(top_presets, dict):
        legacy = _merge_export_pool_preset_dicts(legacy, _clean_export_pool_presets_dict(top_presets))

    return {"version": 2, "draft_root": rk, "legacy_presets": legacy, "by_draft": by_draft}


def save_export_pool_store(draft_root: str, data: Dict[str, Any]) -> None:
    path = _pool_export_presets_store_path(draft_root)
    rk = _normalized_draft_root_key(draft_root)
    by_in = data.get("by_draft")
    if not isinstance(by_in, dict):
        by_in = {}
    leg_in = data.get("legacy_presets")
    if not isinstance(leg_in, dict):
        leg_in = {}
    out_by: Dict[str, Any] = {}
    for dn, bucket in by_in.items():
        dname = str(dn).strip()
        if not dname:
            continue
        if not isinstance(bucket, dict):
            continue
        pr = _clean_export_pool_presets_dict(bucket.get("presets") if isinstance(bucket.get("presets"), dict) else {})
        lp = bucket.get("last_preset")
        if not isinstance(lp, str) or not lp.strip():
            lp = POOL_EXPORT_PRESET_DEFAULT
        else:
            lp = normalize_pool_export_last_preset_value(lp.strip())
        out_entry: Dict[str, Any] = {"presets": pr, "last_preset": lp}
        wp = bucket.get("working_pool")
        if isinstance(wp, dict):
            out_entry["working_pool"] = wp
        out_by[dname] = out_entry
    payload = {
        "version": 2,
        "draft_root": rk,
        "legacy_presets": _clean_export_pool_presets_dict(leg_in),
        "by_draft": out_by,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def _normalize_export_pool_cursor_dict(cur_in: Any) -> Dict[str, int]:
    cur_out: Dict[str, int] = {}
    if isinstance(cur_in, dict):
        for ck, cv in cur_in.items():
            try:
                cur_out[str(ck)] = int(cv)
            except (TypeError, ValueError):
                cur_out[str(ck)] = 0
    return cur_out


def persist_working_export_pool_snapshot(draft_root: str, draft_folder_name: str, replace_state: Dict[str, Any]) -> None:
    """将当前草稿的槽位配置（含单个文件替换）写入本地 store，供下拉「(默认)」时恢复。"""
    dn = (draft_folder_name or "").strip()
    dr = (draft_root or "").strip()
    if not dn or not dr:
        return
    store = load_export_pool_store(dr)
    b = _export_pool_by_draft_bucket_mut(store, dn)
    seg_raw = replace_state.get("segment_export_pool") or {}
    seg = segment_export_pool_enforce_exclusive_sources(seg_raw if isinstance(seg_raw, dict) else {})
    replace_state["segment_export_pool"] = seg
    b["working_pool"] = {
        "segment_export_pool": dict(seg),
        "export_pool_sequential_cursor": _normalize_export_pool_cursor_dict(
            replace_state.get("export_pool_sequential_cursor")
        ),
    }
    save_export_pool_store(dr, store)


def sanitize_replace_state_export_pool_styles(
    replace_state: Dict[str, Any],
    draft_root: str,
    draft_folder_name: str,
    *,
    persist: bool = False,
) -> List[str]:
    """导出前在内存中修正无效指定 id（默认不写回磁盘，避免误删用户配置）。"""
    dr = (draft_root or "").strip()
    dn = (draft_folder_name or "").strip()
    seg_raw = replace_state.get("segment_export_pool") or {}
    parent_json = os.path.join(dr, dn, "draft_content.json") if dr and dn else ""
    cleaned, notes = sanitize_segment_export_pool_styles(
        dict(seg_raw) if isinstance(seg_raw, dict) else {},
        parent_json,
    )
    if not notes:
        return []
    replace_state["segment_export_pool"] = segment_export_pool_enforce_exclusive_sources(cleaned)
    if persist and dr and dn:
        try:
            persist_working_export_pool_snapshot(dr, dn, replace_state)
        except OSError:
            pass
    for note in notes:
        print(f"[槽位修正] {note}")
    return notes


def _export_pool_by_draft_bucket_mut(store: Dict[str, Any], draft_folder_name: str) -> Dict[str, Any]:
    bd = store.setdefault("by_draft", {})
    if not isinstance(bd, dict):
        store["by_draft"] = {}
        bd = store["by_draft"]
    b = bd.setdefault(draft_folder_name, {})
    if not isinstance(b, dict):
        b = {}
        bd[draft_folder_name] = b
    pr = b.setdefault("presets", {})
    if not isinstance(pr, dict):
        b["presets"] = {}
    if "last_preset" not in b or not isinstance(b.get("last_preset"), str):
        b["last_preset"] = POOL_EXPORT_PRESET_DEFAULT
    return b


def export_pool_preset_names_for_draft(draft_root: str, draft_folder_name: str) -> List[str]:
    """当前草稿可选预设名：本稿保存的；旧版全局预设仅当其中含本稿槽位键时才出现（避免每个草稿都看到同一批名字）。"""
    if not draft_root or not os.path.isdir(draft_root):
        return []
    store = load_export_pool_store(draft_root)
    names: set[str] = set()
    dn = (draft_folder_name or "").strip()
    if dn:
        b = (store.get("by_draft") or {}).get(dn) or {}
        pr = b.get("presets") if isinstance(b, dict) else None
        if isinstance(pr, dict):
            names.update(
                k for k in pr if isinstance(k, str) and k.strip() and not is_pool_export_default_menu_preset(k)
            )
    leg = store.get("legacy_presets") or {}
    if isinstance(leg, dict) and dn:
        for k, lb in leg.items():
            if not isinstance(k, str) or not k.strip() or is_pool_export_default_menu_preset(k):
                continue
            if not isinstance(lb, dict):
                continue
            filtered = _filter_export_pool_preset_blob_for_draft(lb, dn)
            if filtered.get("segment_export_pool"):
                names.add(k)
    return sorted(names)


def get_export_pool_preset_blob_for_draft(draft_root: str, draft_folder_name: str, choice: str) -> Optional[Dict[str, Any]]:
    """取某草稿下要应用的预设数据；本稿优先，其次 legacy 中按草稿名过滤后的条目。"""
    if not choice or is_pool_export_default_menu_preset(choice):
        return None
    dn = (draft_folder_name or "").strip()
    if not dn or not draft_root or not os.path.isdir(draft_root):
        return None
    store = load_export_pool_store(draft_root)
    b = (store.get("by_draft") or {}).get(dn) or {}
    pr = b.get("presets") if isinstance(b, dict) else None
    blob = pr.get(choice) if isinstance(pr, dict) else None
    if isinstance(blob, dict) and blob.get("segment_export_pool"):
        return blob
    leg = store.get("legacy_presets") or {}
    lb = leg.get(choice) if isinstance(leg, dict) else None
    if not isinstance(lb, dict):
        return None
    filtered = _filter_export_pool_preset_blob_for_draft(lb, dn)
    if not (filtered.get("segment_export_pool") or {}):
        return None
    return filtered


def persist_export_pool_last_preset_choice(draft_root: str, draft_folder_name: str, choice: str) -> None:
    dn = (draft_folder_name or "").strip()
    if not dn or not draft_root or not os.path.isdir(draft_root):
        return
    store = load_export_pool_store(draft_root)
    b = _export_pool_by_draft_bucket_mut(store, dn)
    b["last_preset"] = normalize_pool_export_last_preset_value(choice)
    save_export_pool_store(draft_root, store)


def persist_active_named_export_pool_preset(
    draft_root: str,
    draft_folder_name: str,
    preset_choice: str,
    replace_state: Dict[str, Any],
) -> None:
    """下拉里为已命名预设时，把当前槽位与顺序光标写回该预设，避免只写入 working_pool 后切换预设丢失。"""
    if is_pool_export_default_menu_preset(preset_choice):
        return
    dn = (draft_folder_name or "").strip()
    dr = (draft_root or "").strip()
    if not dn or not dr or not os.path.isdir(dr):
        return
    seg = replace_state.get("segment_export_pool") or {}
    if not isinstance(seg, dict):
        return
    seg = segment_export_pool_enforce_exclusive_sources(seg)
    replace_state["segment_export_pool"] = seg
    if not _segment_export_pool_has_saveable_config(seg):
        return
    store = load_export_pool_store(dr)
    bucket = _export_pool_by_draft_bucket_mut(store, dn)
    presets = bucket.setdefault("presets", {})
    if not isinstance(presets, dict):
        bucket["presets"] = {}
        presets = bucket["presets"]
    presets[preset_choice] = {
        "segment_export_pool": _segment_export_pool_for_preset_disk(dict(seg)),
        "export_pool_sequential_cursor": _normalize_export_pool_cursor_dict(
            replace_state.get("export_pool_sequential_cursor")
        ),
    }
    bucket["last_preset"] = preset_choice
    save_export_pool_store(dr, store)


def clear_material_export_pool_for_ref(
    replace_state: Dict[str, Any],
    draft_root: str,
    draft_name: str,
    ref: MediaSegmentRef,
    preset_choice: str,
) -> bool:
    """清除单个音视频片段的素材替换配置（不写 draft_content.json）。"""
    dn = (draft_name or "").strip()
    dr = (draft_root or "").strip()
    if not dn:
        return False
    pool_mut: Dict[str, Dict[str, Any]] = replace_state.setdefault("segment_export_pool", {})
    if not segment_has_replace_config(dn, ref, pool_mut):
        return False
    k = segment_export_pool_key(dn, ref)
    kept = clear_material_keys_from_segment_export_pool_entry(pool_mut.get(k))
    if kept:
        pool_mut[k] = kept
    else:
        pool_mut.pop(k, None)
    if dr:
        persist_working_export_pool_snapshot(dr, dn, replace_state)
        persist_active_named_export_pool_preset(dr, dn, preset_choice, replace_state)
    return True


def clear_style_export_pool_for_refs(
    replace_state: Dict[str, Any],
    draft_root: str,
    draft_name: str,
    refs: Iterable[StyleSegmentRef],
    preset_choice: str,
) -> bool:
    """清除一个或多个片段的花字/贴纸导出配置（不写 draft_content.json）。"""
    dn = (draft_name or "").strip()
    dr = (draft_root or "").strip()
    if not dn:
        return False
    pool_mut: Dict[str, Dict[str, Any]] = replace_state.setdefault("segment_export_pool", {})
    changed = False
    for ref in refs:
        if not segment_has_style_config(dn, ref, pool_mut):
            continue
        k = segment_style_pool_key(dn, ref)
        if k in pool_mut:
            pool_mut.pop(k, None)
            changed = True
    if not changed:
        return False
    if dr:
        persist_working_export_pool_snapshot(dr, dn, replace_state)
        persist_active_named_export_pool_preset(dr, dn, preset_choice, replace_state)
    return True


def prune_draft_families(draft_root: str, data: Dict[str, Any]) -> Dict[str, Any]:
    names = {n for n, _ in list_draft_folders(draft_root)}
    bp = data.get("by_parent") or {}
    new_bp: Dict[str, List[str]] = {}
    if isinstance(bp, dict):
        for p, kids in bp.items():
            if p not in names:
                continue
            if not isinstance(kids, list):
                continue
            alive = [c for c in kids if c in names]
            if alive:
                new_bp[p] = alive
    data = dict(data)
    data["by_parent"] = new_bp
    return data


def register_child_draft(draft_root: str, parent_name: str, child_name: str) -> None:
    data = prune_draft_families(draft_root, load_draft_families(draft_root))
    kids = list(data["by_parent"].get(parent_name, []))
    if child_name not in kids:
        kids.append(child_name)
    data["by_parent"][parent_name] = kids
    save_draft_families(draft_root, data)


def unregister_child_draft(draft_root: str, child_name: str) -> None:
    data = prune_draft_families(draft_root, load_draft_families(draft_root))
    bp = data["by_parent"]
    for p, kids in list(bp.items()):
        if child_name in kids:
            bp[p] = [c for c in kids if c != child_name]
            if not bp[p]:
                del bp[p]
    save_draft_families(draft_root, data)


def unregister_parent_group(draft_root: str, parent_name: str) -> None:
    data = load_draft_families(draft_root)
    data["by_parent"].pop(parent_name, None)
    save_draft_families(draft_root, data)


def remap_draft_keyed_map(mapping: Dict[str, Any], parent_name: str, child_name: str) -> Dict[str, Any]:
    old_p = parent_name + "\0"
    new_c = child_name + "\0"
    out: Dict[str, Any] = {}
    for k, v in (mapping or {}).items():
        if isinstance(k, str) and k.startswith(old_p):
            out[new_c + k[len(old_p) :]] = v
    return out


def resolve_lineage_parent_for_nested_draft(draft_root: str, draft_name: str) -> str:
    """左侧树分组用的父模板名：已登记为子则返回其父；否则匹配「父名_N」或旧版「父名_子_NNN」且父文件夹存在则返回父名；否则返回自身。"""
    data = prune_draft_families(draft_root, load_draft_families(draft_root))
    bp = data.get("by_parent") or {}
    if isinstance(bp, dict):
        for p, kids in bp.items():
            if draft_name in kids:
                return str(p)
    m_old = re.match(r"^(.+)_子_(\d{3})$", draft_name)
    if m_old:
        cand = m_old.group(1)
        if cand and os.path.isdir(os.path.join(draft_root, cand)):
            return cand
    m = re.match(r"^(.+)_(\d+)$", draft_name)
    if m:
        cand = m.group(1)
        if cand and os.path.isdir(os.path.join(draft_root, cand)):
            return cand
    return draft_name


def sync_by_parent_with_folder_name_inference(
    draft_root: str, fam: Dict[str, Any], all_names: set[str]
) -> bool:
    """把符合「父_子_NNN」「父_N」且父文件夹存在的子草稿补进 by_parent（仅增补，不写删），并保存。

    避免子文件夹已存在但未写入 draft_families 时，在左侧跑到顶层、与已登记兄弟分列。
    """
    bp: Dict[str, List[str]] = {}
    raw = fam.get("by_parent") or {}
    if isinstance(raw, dict):
        for pk, kids in raw.items():
            p = str(pk)
            if p not in all_names:
                continue
            lst = list(kids) if isinstance(kids, list) else []
            seen: set[str] = set()
            merged: List[str] = []
            for c in lst:
                if isinstance(c, str) and c in all_names and c not in seen:
                    seen.add(c)
                    merged.append(c)
            bp[p] = merged
    child_set: set[str] = set()
    for kids in bp.values():
        child_set.update(kids)

    changed = False
    for n in all_names:
        if n in child_set:
            continue
        p = resolve_lineage_parent_for_nested_draft(draft_root, n)
        if p == n or p not in all_names:
            continue
        bp.setdefault(p, [])
        if n not in bp[p]:
            bp[p].append(n)
            child_set.add(n)
            changed = True

    if changed:
        fam["by_parent"] = bp
        save_draft_families(draft_root, fam)
    return changed


def merge_remapped_pool_and_cursor_into_replace_state(
    replace_state: Dict[str, Any],
    remapped_pool: Dict[str, Any],
    cursor_ints: Dict[str, int],
) -> None:
    seg = replace_state.setdefault("segment_export_pool", {})
    if isinstance(seg, dict):
        for k, v in remapped_pool.items():
            seg[k] = dict(v) if isinstance(v, dict) else v
    cur = replace_state.setdefault("export_pool_sequential_cursor", {})
    if isinstance(cur, dict):
        cur.update(cursor_ints)
    coerced = segment_export_pool_enforce_exclusive_sources(replace_state.get("segment_export_pool") or {})
    replace_state["segment_export_pool"] = coerced


def _export_parent_for_new_child(selected_draft_name: str) -> str:
    """导出/生成子稿时，以**当前选中的草稿文件夹名**为父，而非追溯到根模板。

    例：选中 ``A_1`` 并勾选「导出生成子草稿」→ 生成 ``A_1_1``、``A_1_2``（不是与 ``A_1`` 平级的 ``A_2``）。
    """
    return (selected_draft_name or "").strip()


def _next_generated_child_name(draft_root: str, parent_name: str) -> str:
    existing = {n for n, _ in list_draft_folders(draft_root)}
    for n in range(1, 10000):
        cand = f"{parent_name}_{n}"
        if cand not in existing:
            return cand
    raise RuntimeError("无法分配子草稿文件夹名（请清理旧草稿后重试）。")


def _timeline_end_us(content: Dict[str, Any]) -> int:
    d = int(content.get("duration") or 0)
    for tr in content.get("tracks") or []:
        for seg in tr.get("segments") or []:
            t = seg.get("target_timerange") or {}
            end = int(t.get("start", 0)) + int(t.get("duration", 0))
            d = max(d, end)
    return max(d, 1)


_TIMELINE_LABEL_W = 118
_TIMELINE_PAD = 6
_TIMELINE_FX_EXTRA_KINDS = frozenset(
    {"effects", "video_effects", "material_animations", "filters", "transitions"}
)


def _calc_timeline_fit_pps(content: Dict[str, Any], viewport_px: int) -> float:
    """按可视宽度计算 pps，使整段草稿能一屏看完（下限 14）。"""
    total_us = _timeline_end_us(content)
    total_sec = max(total_us / 1_000_000.0, 0.001)
    usable = max(160, int(viewport_px) - _TIMELINE_LABEL_W - _TIMELINE_PAD * 2)
    return max(14.0, min(420.0, usable / total_sec))


def _build_material_kind_index(materials: Dict[str, Any]) -> Dict[str, str]:
    idx: Dict[str, str] = {}
    for mkey, arr in materials.items():
        if not isinstance(arr, list):
            continue
        for m in arr:
            if isinstance(m, dict) and m.get("id"):
                idx[str(m["id"])] = str(mkey)
    return idx


def _segment_extra_material_kinds(seg: Dict[str, Any], mat_kind_by_id: Dict[str, str]) -> set:
    kinds: set = set()
    for ref in seg.get("extra_material_refs") or []:
        k = mat_kind_by_id.get(str(ref), "")
        if k:
            kinds.add(k)
    return kinds


def _segment_has_timeline_fx(seg: Dict[str, Any], mat_kind_by_id: Dict[str, str]) -> bool:
    return bool(_segment_extra_material_kinds(seg, mat_kind_by_id) & _TIMELINE_FX_EXTRA_KINDS)


def _timeline_ruler_step_us(total_us: int) -> int:
    total_sec = total_us / 1_000_000.0
    if total_sec > 180:
        return 30_000_000
    if total_sec > 90:
        return 10_000_000
    if total_sec > 45:
        return 5_000_000
    if total_sec > 20:
        return 2_000_000
    return 1_000_000


def _timeline_segment_label(seg: Dict[str, Any], materials: Dict[str, Any]) -> str:
    mid = (seg.get("material_id") or "").strip()
    mats = materials if isinstance(materials, dict) else {}
    for key in ("videos", "audios", "texts", "stickers"):
        for m in mats.get(key) or []:
            if not isinstance(m, dict) or m.get("id") != mid:
                continue
            if key == "texts":
                raw = m.get("content")
                if isinstance(raw, str) and raw.strip().startswith("{"):
                    try:
                        c = json.loads(raw)
                        tx = (c.get("text") or "").replace("\n", " ").strip()
                        return (tx[:28] + "…") if len(tx) > 28 else (tx or "文本")
                    except (json.JSONDecodeError, TypeError):
                        pass
                return "文本"
            if key == "stickers":
                rid = str(m.get("resource_id") or m.get("sticker_id") or "").strip()
                name = str(m.get("name") or "").strip()
                hint = name or rid or mid[:10]
                return (hint[:28] + "…") if len(hint) > 28 else (hint or "贴纸")
            name = m.get("material_name") or m.get("name") or ""
            pth = m.get("path") or ""
            base = os.path.basename(pth.replace("/", os.sep)) if pth else ""
            hint = base or name or mid[:10]
            return (hint[:32] + "…") if len(hint) > 32 else hint
    return (mid[:10] + "…") if len(mid) > 10 else (mid or "—")


def _track_render_index(tr: Dict[str, Any]) -> int:
    segs = tr.get("segments") or []
    if not segs:
        return 0
    try:
        return int(segs[0].get("render_index", 0))
    except (TypeError, ValueError):
        return 0


def _track_index_in_content(content: Dict[str, Any], track: Dict[str, Any]) -> Optional[int]:
    """定位 ``track`` 在 ``content['tracks']`` 中的下标（优先同一 dict 引用，否则按 id）。"""
    trs = content.get("tracks") or []
    for i, tr in enumerate(trs):
        if tr is track:
            return i
    tid = track.get("id")
    if tid is None or tid == "":
        return None
    ts = str(tid)
    for i, tr in enumerate(trs):
        if str(tr.get("id", "") or "") == ts:
            return i
    return None


def _media_track_ordinal_at_index(content: Dict[str, Any], track_idx: int) -> Optional[int]:
    """``tracks`` 数组中第 ``track_idx`` 条若为 video/audio，返回其为第几条音视频轨（0-based）。"""
    trs = content.get("tracks") or []
    if track_idx < 0 or track_idx >= len(trs):
        return None
    if str(trs[track_idx].get("type", "")) not in ("video", "audio"):
        return None
    mo = 0
    for j in range(track_idx):
        if str(trs[j].get("type", "")) in ("video", "audio"):
            mo += 1
    return mo


def find_replace_ref_for_timeline_segment(
    refs: List[MediaSegmentRef],
    track: Dict[str, Any],
    segment_index_raw: int,
    content: Optional[Dict[str, Any]] = None,
) -> Optional[MediaSegmentRef]:
    """时间轴轨道片段（JSON 内 segment 下标）与下方「素材槽」列表项对应。"""
    tid = str(track.get("id", "") or "").strip()
    if tid:
        for r in refs:
            rt = str(r.track_id or "").strip()
            if rt and rt == tid and r.segment_index == segment_index_raw:
                return r
    nm_raw = track.get("name", "")
    tname = "" if nm_raw is None else (nm_raw if isinstance(nm_raw, str) else str(nm_raw))
    tname = tname.strip()
    ty_raw = track.get("type", "")
    ttype = str(ty_raw).strip().lower() if ty_raw is not None else ""
    for r in refs:
        rn = (r.track_name or "").strip()
        rt = (r.track_type or "").strip().lower()
        if rn == tname and rt == ttype and r.segment_index == segment_index_raw:
            return r
    if content and isinstance(content, dict):
        tidx = _track_index_in_content(content, track)
        if tidx is not None:
            mo = _media_track_ordinal_at_index(content, tidx)
            if mo is not None:
                for r in refs:
                    if r.media_ordinal == mo and r.segment_index == segment_index_raw:
                        return r
    raw_segs = list(track.get("segments") or [])
    if 0 <= segment_index_raw < len(raw_segs):
        seg = raw_segs[segment_index_raw]
        if isinstance(seg, dict):
            mid = str((seg.get("material_id") or "")).strip()
            if mid:
                same = [
                    r
                    for r in refs
                    if r.segment_index == segment_index_raw
                    and str((r.material_id or "")).strip() == mid
                ]
                if len(same) == 1:
                    return same[0]
                for r in same:
                    if (r.track_type or "").strip().lower() == ttype:
                        return r
                if same:
                    return same[0]
    return None


def _style_segment_ref_from_timeline(
    content: Dict[str, Any],
    track: Dict[str, Any],
    segment_index_raw: int,
) -> Optional[StyleSegmentRef]:
    """由时间轴上的轨道 + 片段下标直接构造花字/贴纸槽引用（不依赖预构建列表）。"""
    ttype = str(track.get("type", "")).strip().lower()
    if ttype not in ("text", "sticker"):
        return None
    segs = track.get("segments") or []
    if segment_index_raw < 0 or segment_index_raw >= len(segs):
        return None
    seg = segs[segment_index_raw]
    if not isinstance(seg, dict):
        return None
    mid = str(seg.get("material_id") or "").strip()
    if not mid:
        return None
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    trng = seg.get("target_timerange") or {}
    try:
        t0 = int(trng.get("start", 0))
        t1 = t0 + int(trng.get("duration", 0))
    except (TypeError, ValueError):
        t0, t1 = 0, 0
    tid = str(track.get("id") or "")
    nm_raw = track.get("name", "")
    tname = "" if nm_raw is None else (nm_raw if isinstance(nm_raw, str) else str(nm_raw))
    tname = tname.strip()
    if ttype == "text":
        mat: Dict[str, Any] = {}
        for m in materials.get("texts") or []:
            if isinstance(m, dict) and str(m.get("id")) == mid:
                mat = m
                break
        cur_rid = _text_effect_id_from_material(mat) if mat else ""
        lab = _timeline_segment_label(seg, materials)
        label = f"[text] {tname} · 片段{segment_index_raw + 1} · {_fmt_tc_us(t0, t1)} · {lab}"
    else:
        mat = {}
        for m in materials.get("stickers") or []:
            if isinstance(m, dict) and str(m.get("id")) == mid:
                mat = m
                break
        cur_rid = _sticker_resource_id_from_material(mat) if mat else ""
        hint = cur_rid[:16] if cur_rid else mid[:8]
        label = f"[sticker] {tname} · 片段{segment_index_raw + 1} · {_fmt_tc_us(t0, t1)} · {hint}"
    return StyleSegmentRef(
        track_type=ttype,
        track_name=tname,
        segment_index=segment_index_raw,
        combo_label=label,
        material_id=mid,
        track_id=tid,
        current_resource_id=cur_rid,
    )


def list_style_segment_refs_for_track(
    content: Dict[str, Any],
    track: Dict[str, Any],
) -> List[StyleSegmentRef]:
    """列出某条文本/贴纸轨道上全部可配置花字/贴纸的片段引用。"""
    ttype = str(track.get("type", "")).strip().lower()
    if ttype not in ("text", "sticker") or not isinstance(content, dict):
        return []
    segs = track.get("segments") or []
    out: List[StyleSegmentRef] = []
    for i in range(len(segs)):
        ref = _style_segment_ref_from_timeline(content, track, i)
        if ref is not None:
            out.append(ref)
    return out


def find_style_ref_for_timeline_segment(
    refs: List[StyleSegmentRef],
    track: Dict[str, Any],
    segment_index_raw: int,
    content: Optional[Dict[str, Any]] = None,
) -> Optional[StyleSegmentRef]:
    """时间轴文本/贴纸片段与花字/贴纸槽列表项对应。"""
    if content and isinstance(content, dict):
        built = _style_segment_ref_from_timeline(content, track, segment_index_raw)
        if built is not None:
            return built
    tid = str(track.get("id", "") or "").strip()
    if tid:
        for r in refs:
            rt = str(r.track_id or "").strip()
            if rt and rt == tid and r.segment_index == segment_index_raw:
                return r
    nm_raw = track.get("name", "")
    tname = "" if nm_raw is None else (nm_raw if isinstance(nm_raw, str) else str(nm_raw))
    tname = tname.strip()
    ty_raw = track.get("type", "")
    ttype = str(ty_raw).strip().lower() if ty_raw is not None else ""
    for r in refs:
        rn = (r.track_name or "").strip()
        rt = (r.track_type or "").strip().lower()
        if rn == tname and rt == ttype and r.segment_index == segment_index_raw:
            return r
    raw_segs = list(track.get("segments") or [])
    if 0 <= segment_index_raw < len(raw_segs):
        seg = raw_segs[segment_index_raw]
        if isinstance(seg, dict):
            mid = str((seg.get("material_id") or "")).strip()
            if mid:
                same = [
                    r
                    for r in refs
                    if r.segment_index == segment_index_raw
                    and str((r.material_id or "")).strip() == mid
                ]
                if len(same) == 1:
                    return same[0]
                for r in same:
                    if (r.track_type or "").strip().lower() == ttype:
                        return r
                if same:
                    return same[0]
    return None


def _local_media_path_for_segment(seg: Dict[str, Any], materials: Dict[str, Any]) -> str:
    """片段引用的视频/音频素材在 materials 中的本地 path（若无则空字符串）。"""
    mid = (seg.get("material_id") or "").strip()
    if not mid or not isinstance(materials, dict):
        return ""
    for key in ("videos", "audios"):
        for m in materials.get(key) or []:
            if isinstance(m, dict) and m.get("id") == mid:
                p = (m.get("path") or "").strip()
                return p.replace("/", os.sep) if p else ""
    return ""


def _fmt_us_as_timecode(us: int) -> str:
    if us < 0:
        us = 0
    total_s = us / 1_000_000.0
    m, sec = divmod(total_s, 60.0)
    h, m = divmod(m, 60.0)
    if h >= 1:
        return f"{int(h)}:{int(m):02d}:{sec:05.2f}"
    return f"{int(m)}:{sec:05.2f}"


def _draft_preview_fps(content: Optional[Dict[str, Any]]) -> float:
    if not isinstance(content, dict):
        return 30.0
    try:
        fps = float(content.get("fps") or 30.0)
    except (TypeError, ValueError):
        fps = 30.0
    return max(1.0, min(120.0, fps))


def _fmt_player_timecode(us: int, *, fps: float = 30.0) -> str:
    """剪映风格 HH:MM:SS:FF 时间码。"""
    if us < 0:
        us = 0
    fps_i = max(1, int(round(fps)))
    total_frames = int(round(us * fps_i / 1_000_000.0))
    ff = total_frames % fps_i
    total_sec = total_frames // fps_i
    s = total_sec % 60
    m = (total_sec // 60) % 60
    h = total_sec // 3600
    return f"{h:02d}:{m:02d}:{s:02d}:{ff:02d}"


@dataclass(frozen=True)
class VideoPlayheadHit:
    path: str
    source_us: int
    seg_label: str


@dataclass(frozen=True)
class PreviewVideoLayer:
    path: str
    source_us: int
    render_index: int
    label: str
    speed: float = 1.0


@dataclass(frozen=True)
class PreviewAudioLayer:
    path: str
    source_us: int
    render_index: int
    label: str
    speed: float = 1.0
    timeline_remaining_us: int = 0
    volume: float = 1.0


@dataclass(frozen=True)
class PreviewTextLayer:
    text: str
    font_size: int
    color: str
    render_index: int


@dataclass(frozen=True)
class PreviewPlan:
    playhead_us: int
    videos: Tuple[PreviewVideoLayer, ...]
    texts: Tuple[PreviewTextLayer, ...]
    sticker_count: int
    info: str


def _segment_source_us_at_playhead(seg: Dict[str, Any], playhead_us: int) -> Optional[int]:
    trng = seg.get("target_timerange") or {}
    try:
        st = int(trng.get("start", 0))
        du = int(trng.get("duration", 0))
    except (TypeError, ValueError):
        return None
    if du <= 0 or not (st <= playhead_us < st + du):
        return None
    src_tr = seg.get("source_timerange") or {}
    try:
        src_start = int(src_tr.get("start", 0))
        src_dur = int(src_tr.get("duration", du))
    except (TypeError, ValueError):
        src_start, src_dur = 0, du
    off = playhead_us - st
    if du > 0 and src_dur > 0:
        src_us = src_start + int(off * src_dur / du)
    else:
        src_us = src_start + off
    return max(0, src_us)


def _segment_timeline_remaining_us(seg: Dict[str, Any], playhead_us: int) -> int:
    """片段在时间轴上还剩多少微秒（用于限制预览音频播放时长）。"""
    trng = seg.get("target_timerange") or {}
    try:
        st = int(trng.get("start", 0))
        du = int(trng.get("duration", 0))
    except (TypeError, ValueError):
        return 0
    if du <= 0:
        return 0
    end_us = st + du
    ph = max(0, int(playhead_us))
    if ph >= end_us:
        return 0
    return max(0, end_us - ph)


def _segment_speed(seg: Dict[str, Any]) -> float:
    try:
        spd = float(seg.get("speed", 1.0))
    except (TypeError, ValueError):
        spd = 1.0
    return max(0.1, min(10.0, spd))


def _segment_audio_playback_rate(seg: Dict[str, Any]) -> float:
    """源素材秒 / 时间轴秒，与 _segment_source_us_at_playhead 映射一致。"""
    trng = seg.get("target_timerange") or {}
    src_tr = seg.get("source_timerange") or {}
    try:
        du = int(trng.get("duration", 0))
        src_dur = int(src_tr.get("duration", du))
    except (TypeError, ValueError):
        du, src_dur = 0, 0
    if du > 0 and src_dur > 0:
        return max(0.1, min(10.0, src_dur / du))
    return _segment_speed(seg)


def _atempo_filter_for_speed(speed: float) -> Optional[str]:
    """ffmpeg atempo 链（单段仅支持 0.5~2.0，需串联）。"""
    if abs(speed - 1.0) < 0.02:
        return None
    parts: List[str] = []
    remaining = speed
    while remaining > 2.001:
        parts.append("atempo=2")
        remaining /= 2.0
    while remaining < 0.499:
        parts.append("atempo=0.5")
        remaining /= 0.5
    if abs(remaining - 1.0) >= 0.02:
        parts.append(f"atempo={remaining:.6f}")
    return ",".join(parts) if parts else None


PREVIEW_AUDIO_FINE_SEEK_SEC = 0.15


def _ffplay_audio_seek_args(path_abs: str, sec: float) -> List[str]:
    """混合 seek：粗定位在 -i 前（快），余量在 -i 后（准），避免关键帧导致口播落后字幕。"""
    if sec < 0.001:
        return ["-i", path_abs]
    fine_window = min(PREVIEW_AUDIO_FINE_SEEK_SEC, sec)
    coarse = max(0.0, sec - fine_window)
    fine = sec - coarse
    args: List[str] = []
    if coarse >= 0.001:
        args.extend(["-ss", f"{coarse:.6f}"])
    args.extend(["-i", path_abs])
    if fine >= 0.001:
        args.extend(["-ss", f"{fine:.6f}"])
    return args


def _ffplay_audio_args(layer: PreviewAudioLayer, path_abs: str, sec: float) -> List[str]:
    args: List[str] = ["-nodisp", "-autoexit", "-loglevel", "quiet"]
    args.extend(_ffplay_audio_seek_args(path_abs, sec))
    af_parts = _ffmpeg_audio_post_filters(layer)
    if af_parts:
        args.extend(["-af", ",".join(af_parts)])
    return args


def _color_from_jianying_fill(fill: Any) -> str:
    if not isinstance(fill, dict):
        return "#FFFFFF"
    content = fill.get("content")
    if isinstance(content, dict):
        solid = content.get("solid")
        if isinstance(solid, dict):
            rgb = solid.get("color")
            if isinstance(rgb, (list, tuple)) and len(rgb) >= 3:
                try:
                    r, g, b = (max(0, min(255, int(float(c) * 255))) for c in rgb[:3])
                    return f"#{r:02x}{g:02x}{b:02x}"
                except (TypeError, ValueError):
                    pass
    raw = fill.get("color")
    if isinstance(raw, str) and raw.startswith("#"):
        return raw
    return "#FFFFFF"


def _text_layer_from_segment(seg: Dict[str, Any], mat: Dict[str, Any]) -> Optional[PreviewTextLayer]:
    raw = mat.get("content")
    if not isinstance(raw, str) or not raw.strip().startswith("{"):
        return None
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, TypeError):
        return None
    text = str(payload.get("text") or "").replace("\n", " ").strip()
    if not text:
        return None
    styles = payload.get("styles") or []
    style0 = styles[0] if styles and isinstance(styles[0], dict) else {}
    try:
        font_size = max(8, int(style0.get("size") or 14))
    except (TypeError, ValueError):
        font_size = 14
    color = _color_from_jianying_fill(style0.get("fill"))
    try:
        render_index = int(seg.get("render_index", 0))
    except (TypeError, ValueError):
        render_index = 0
    return PreviewTextLayer(text=text, font_size=font_size, color=color, render_index=render_index)


def build_preview_plan(content: Dict[str, Any], playhead_us: int) -> PreviewPlan:
    """预览（只读）：收集时间轴 T 上的 video/text/sticker，供画面与字幕叠加。"""
    tracks_raw = list(content.get("tracks") or [])
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    ph = max(0, int(playhead_us))
    videos: List[PreviewVideoLayer] = []
    texts: List[PreviewTextLayer] = []
    sticker_count = 0
    texts_by_id = {
        str(m.get("id")): m for m in (materials.get("texts") or []) if isinstance(m, dict) and m.get("id")
    }

    for tr in tracks_raw:
        ttype = str(tr.get("type", "")).strip().lower()
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            if _segment_source_us_at_playhead(seg, ph) is None:
                continue
            if ttype == "video":
                path = _local_media_path_for_segment(seg, materials)
                if not path or not os.path.isfile(path):
                    continue
                src_us = _segment_source_us_at_playhead(seg, ph) or 0
                try:
                    ri = int(seg.get("render_index", 0))
                except (TypeError, ValueError):
                    ri = 0
                videos.append(
                    PreviewVideoLayer(
                        path=path,
                        source_us=src_us,
                        render_index=ri,
                        label=_timeline_segment_label(seg, materials),
                        speed=_segment_speed(seg),
                    )
                )
            elif ttype == "text":
                mid = str(seg.get("material_id") or "").strip()
                mat = texts_by_id.get(mid) or {}
                layer = _text_layer_from_segment(seg, mat)
                if layer is not None:
                    texts.append(layer)
            elif ttype == "sticker":
                sticker_count += 1

    videos.sort(key=lambda v: v.render_index)
    texts.sort(key=lambda t: t.render_index)

    info_parts: List[str] = []
    if videos:
        info_parts.append(" · ".join(v.label[:20] for v in videos))
    if texts:
        info_parts.append("字幕: " + " / ".join(t.text[:18] + ("…" if len(t.text) > 18 else "") for t in texts[:2]))
        if len(texts) > 2:
            info_parts.append(f"等 {len(texts)} 条")
    if sticker_count:
        info_parts.append(f"贴纸×{sticker_count}")
    info = " · ".join(info_parts) if info_parts else "（无画面内容）"
    return PreviewPlan(
        playhead_us=ph,
        videos=tuple(videos),
        texts=tuple(texts),
        sticker_count=sticker_count,
        info=info,
    )


def find_video_at_playhead(content: Dict[str, Any], playhead_us: int) -> Optional[VideoPlayheadHit]:
    """按 render_index 从高到低找当前时间最前景的视频片段。"""
    plan = build_preview_plan(content, playhead_us)
    if not plan.videos:
        return None
    top = plan.videos[-1]
    return VideoPlayheadHit(path=top.path, source_us=top.source_us, seg_label=top.label)


def find_audio_layers_at_playhead(content: Dict[str, Any], playhead_us: int) -> Tuple[PreviewAudioLayer, ...]:
    """收集当前时间点的音频层（底→顶）。"""
    tracks_raw = list(content.get("tracks") or [])
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    ph = max(0, int(playhead_us))
    audios: List[PreviewAudioLayer] = []
    for tr in tracks_raw:
        if str(tr.get("type", "")).strip().lower() != "audio":
            continue
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            src_us = _segment_source_us_at_playhead(seg, ph)
            if src_us is None:
                continue
            path = _local_media_path_for_segment(seg, materials)
            if not path or not os.path.isfile(path):
                continue
            try:
                ri = int(seg.get("render_index", 0))
            except (TypeError, ValueError):
                ri = 0
            audios.append(
                PreviewAudioLayer(
                    path=path,
                    source_us=src_us,
                    render_index=ri,
                    label=_timeline_segment_label(seg, materials),
                    speed=_segment_audio_playback_rate(seg),
                    timeline_remaining_us=_segment_timeline_remaining_us(seg, ph),
                    volume=_preview_playback_volume(seg),
                )
            )
    audios.sort(key=lambda a: a.render_index)
    return tuple(audios)


def _segment_playback_key(seg: Dict[str, Any], path: str) -> Tuple[str, int, int]:
    """片段在时间轴上的稳定标识（播放中 source_us 会变，但 key 不变）。"""
    trng = seg.get("target_timerange") or {}
    try:
        st = int(trng.get("start", 0))
        du = int(trng.get("duration", 0))
    except (TypeError, ValueError):
        st, du = 0, 0
    return (os.path.abspath(path), st, du)


def _segment_playback_identity(seg: Dict[str, Any], path: str, *, kind: str) -> Tuple[str, ...]:
    seg_id = str(seg.get("id") or "").strip()
    if seg_id:
        return (kind, seg_id)
    return (kind, *_segment_playback_key(seg, path))


def _segment_volume(seg: Dict[str, Any]) -> float:
    try:
        vol = float(seg.get("volume", 1.0))
    except (TypeError, ValueError):
        vol = 1.0
    return max(0.0, vol)


def _preview_playback_volume(seg: Dict[str, Any]) -> float:
    """片段音量（与后台混音预览一致，剪映常见 0~8 线性倍率）。"""
    return max(0.0, min(8.0, _segment_volume(seg)))


def _ffmpeg_audio_post_filters(layer: PreviewAudioLayer) -> List[str]:
    """atempo + volume，供 ffplay -af 或 ffmpeg filter_complex 链接。"""
    parts: List[str] = []
    af = _atempo_filter_for_speed(layer.speed)
    if af:
        parts.extend(af.split(","))
    vol = max(0.0, min(8.0, float(layer.volume)))
    if abs(vol - 1.0) >= 0.001:
        parts.append(f"volume={vol:.4f}")
    return parts


def _draft_config_video_mute(content: Dict[str, Any]) -> bool:
    """草稿 config.video_mute：全局关闭所有视频轨原声。"""
    cfg = content.get("config")
    if not isinstance(cfg, dict):
        return False
    return bool(cfg.get("video_mute"))


def _track_is_muted(tr: Dict[str, Any]) -> bool:
    """轨道 attribute=1 表示整条轨道静音（剪映轨道喇叭图标）。"""
    try:
        return int(tr.get("attribute", 0)) != 0
    except (TypeError, ValueError):
        return False


def _segment_on_muted_track(seg: Dict[str, Any]) -> bool:
    """片段 track_attribute=1 表示所属轨道已静音。"""
    try:
        return int(seg.get("track_attribute", 0)) != 0
    except (TypeError, ValueError):
        return False


def _is_playback_audio_audible(
    content: Dict[str, Any],
    tr: Dict[str, Any],
    seg: Dict[str, Any],
    *,
    track_type: str,
) -> bool:
    if _track_is_muted(tr):
        return False
    if _segment_on_muted_track(seg):
        return False
    if _segment_volume(seg) <= 0.001:
        return False
    if track_type == "video" and _draft_config_video_mute(content):
        return False
    return True


def _append_playback_audio_hit(
    hits: List[Tuple[PreviewAudioLayer, Tuple[str, ...]]],
    seen: set,
    *,
    seg: Dict[str, Any],
    path: str,
    source_us: int,
    render_index: int,
    label: str,
    kind: str,
    playhead_us: int,
) -> None:
    identity = _segment_playback_identity(seg, path, kind=kind)
    if identity in seen:
        return
    seen.add(identity)
    hits.append(
        (
            PreviewAudioLayer(
                path=path,
                source_us=source_us,
                render_index=render_index,
                label=label,
                speed=_segment_audio_playback_rate(seg),
                timeline_remaining_us=_segment_timeline_remaining_us(seg, playhead_us),
                volume=_preview_playback_volume(seg),
            ),
            identity,
        )
    )


def _playback_audio_hits(
    content: Dict[str, Any], playhead_us: int
) -> Tuple[Tuple[PreviewAudioLayer, Tuple[str, ...]], ...]:
    """预览 A 方案（只读草稿）：时间轴 T 上所有可听见的 audio 轨 + video 内嵌声。

    尊重轨道/片段 mute、volume、speed；不写 draft、不改轨道。
    """
    tracks_raw = list(content.get("tracks") or [])
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    ph = max(0, int(playhead_us))
    hits: List[Tuple[PreviewAudioLayer, Tuple[str, ...]]] = []
    seen: set = set()

    for tr in tracks_raw:
        ttype = str(tr.get("type", "")).strip().lower()
        if ttype not in ("audio", "video"):
            continue
        if _track_is_muted(tr):
            continue
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            if not _is_playback_audio_audible(content, tr, seg, track_type=ttype):
                continue
            src_us = _segment_source_us_at_playhead(seg, ph)
            if src_us is None:
                continue
            path = _local_media_path_for_segment(seg, materials)
            if not path or not os.path.isfile(path):
                continue
            if ttype == "video" and not _media_maybe_has_audio(path):
                continue
            try:
                ri = int(seg.get("render_index", 0))
            except (TypeError, ValueError):
                ri = 0
            _append_playback_audio_hit(
                hits,
                seen,
                seg=seg,
                path=path,
                source_us=src_us,
                render_index=ri,
                label=_timeline_segment_label(seg, materials),
                kind=ttype,
                playhead_us=ph,
            )

    hits.sort(key=lambda item: (item[0].render_index, item[1]))
    return tuple(hits)


def find_playback_audio_layers(content: Dict[str, Any], playhead_us: int) -> Tuple[PreviewAudioLayer, ...]:
    """播放用音频层列表（不含片段 key）。"""
    return tuple(layer for layer, _key in _playback_audio_hits(content, playhead_us))


def _playback_audio_signature(
    hits: Tuple[Tuple[PreviewAudioLayer, Tuple[str, ...]], ...],
) -> Tuple[Tuple[str, ...], ...]:
    """按片段边界判断是否需要重启音频（播放过程中 source_us 递增但 identity 不变）。"""
    return tuple(key for _layer, key in hits)


def _terminate_subprocess(proc: subprocess.Popen) -> None:
    try:
        proc.terminate()
    except OSError:
        pass
    try:
        proc.wait(timeout=0.8)
        return
    except (subprocess.TimeoutExpired, OSError):
        pass
    try:
        proc.kill()
    except OSError:
        pass
    try:
        proc.wait(timeout=1.2)
    except (subprocess.TimeoutExpired, OSError):
        pass


def kill_playback_audio_procs(procs: Optional[List[subprocess.Popen]]) -> None:
    for proc in procs or []:
        if proc is not None and proc.poll() is None:
            _terminate_subprocess(proc)


def _ffmpeg_playback_layer_filter(index: int, layer: PreviewAudioLayer) -> str:
    """单轨：源素材精确 atrim + atempo + volume，输出时长与时间轴片段剩余一致。"""
    sec = max(0.0, layer.source_us / 1_000_000.0)
    src_span = max(0.001, (layer.timeline_remaining_us / 1_000_000.0) * layer.speed)
    end_sec = sec + src_span
    chain = f"[{index}:a]atrim=start={sec:.6f}:end={end_sec:.6f},asetpts=PTS-STARTPTS"
    for filt in _ffmpeg_audio_post_filters(layer):
        chain += f",{filt}"
    return f"{chain}[a{index}]"


def _spawn_playback_audio_mixed_pipe(
    playable: List[PreviewAudioLayer],
    *,
    ffplay: str,
    ffmpeg: str,
    devnull: Any,
) -> List[subprocess.Popen]:
    """ffmpeg 混音 → 单路 ffplay，避免多 ffplay 启动时差。"""
    cmd: List[str] = [ffmpeg, "-hide_banner", "-loglevel", "error"]
    for layer in playable:
        cmd.extend(["-i", os.path.abspath(layer.path)])
    n = len(playable)
    filters = [_ffmpeg_playback_layer_filter(i, layer) for i, layer in enumerate(playable)]
    if n == 1:
        cmd.extend(["-filter_complex", filters[0], "-map", "[a0]"])
    else:
        ins = "".join(f"[a{i}]" for i in range(n))
        filters.append(f"{ins}amix=inputs={n}:duration=longest:dropout_transition=0[aout]")
        cmd.extend(["-filter_complex", ";".join(filters), "-map", "[aout]"])
    cmd.extend(["-vn", "-f", "wav", "pipe:1"])
    ffmpeg_proc = None
    try:
        ffmpeg_proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=devnull)
        ffplay_proc = subprocess.Popen(
            [
                ffplay,
                "-nodisp",
                "-autoexit",
                "-loglevel",
                "quiet",
                "-i",
                "pipe:0",
            ],
            stdin=ffmpeg_proc.stdout,
            stdout=devnull,
            stderr=subprocess.PIPE,
        )
        if ffmpeg_proc.stdout is not None:
            ffmpeg_proc.stdout.close()
        return [ffmpeg_proc, ffplay_proc]
    except OSError:
        kill_playback_audio_procs([ffmpeg_proc] if ffmpeg_proc is not None else [])
        return []


def spawn_playback_audio(layers: Tuple[PreviewAudioLayer, ...]) -> List[subprocess.Popen]:
    """单路混音播放：ffmpeg atrim 精确 seek + 片段剩余时长，pipe 进一个 ffplay。"""
    playable = [
        layer
        for layer in layers
        if layer.path and os.path.isfile(layer.path) and layer.timeline_remaining_us > 0
    ]
    if not playable:
        return []

    ffplay = find_ffplay()
    ffmpeg = find_ffmpeg()
    devnull = subprocess.DEVNULL

    if ffmpeg and ffplay:
        procs = _spawn_playback_audio_mixed_pipe(
            playable, ffplay=ffplay, ffmpeg=ffmpeg, devnull=devnull
        )
        if procs:
            return procs

    if len(playable) == 1 and ffplay:
        layer = playable[0]
        sec = max(0.0, layer.source_us / 1_000_000.0)
        timeline_sec = max(0.001, layer.timeline_remaining_us / 1_000_000.0)
        path_abs = os.path.abspath(layer.path)
        args: List[str] = [
            "-nodisp",
            "-autoexit",
            "-loglevel",
            "quiet",
            "-t",
            f"{timeline_sec:.6f}",
        ]
        args.extend(_ffplay_audio_seek_args(path_abs, sec))
        af_parts = _ffmpeg_audio_post_filters(layer)
        if af_parts:
            args.extend(["-af", ",".join(af_parts)])
        try:
            proc = subprocess.Popen([ffplay, *args], stdout=devnull, stderr=subprocess.PIPE)
        except OSError:
            return []
        return [proc]

    return []


# ffplay 周期性刷新 stderr 状态行；aq=NNKB（NN>0）表示音频队列已有数据（开始缓冲/播放）
_FFPLAY_AUDIO_QUEUE_RE = re.compile(r"aq=\s*[1-9]\d*KB", re.I)


def watch_ffplay_audio_output_ready(
    proc: subprocess.Popen,
    on_ready: Callable[[], None],
    *,
    timeout_sec: float = 2.5,
) -> None:
    """后台读 ffplay stderr，见到音频队列非空即回调 on_ready（须在 UI 线程再改状态）。"""
    if proc is None:
        on_ready()
        return

    fired = threading.Event()

    def _fire() -> None:
        if fired.is_set():
            return
        fired.set()
        on_ready()

    stderr = proc.stderr
    if stderr is None:
        def _fallback() -> None:
            time.sleep(min(0.15, timeout_sec * 0.1))
            _fire()

        threading.Thread(target=_fallback, daemon=True, name="ffplay-ready-fallback").start()
        return

    def _reader() -> None:
        deadline = time.time() + timeout_sec
        try:
            while time.time() < deadline and proc.poll() is None:
                raw = stderr.readline()
                if not raw:
                    break
                text = raw.decode("utf-8", errors="replace")
                if _FFPLAY_AUDIO_QUEUE_RE.search(text):
                    _fire()
                    return
        except OSError:
            pass
        if proc.poll() is None:
            _fire()

    threading.Thread(target=_reader, daemon=True, name="ffplay-ready-watch").start()


# --- 预览：临时低规格多轨合并（从 playhead 起窗口内一次 ffmpeg 出片，单文件播放对齐时间轴）---
PREVIEW_MERGE_CHUNK_US = 10_000_000  # 每段合成 10s
PREVIEW_MERGE_PREFETCH_LEAD_US = 4_000_000  # 距段末 4s 开始后台渲下一段
PREVIEW_MERGE_WINDOW_US = PREVIEW_MERGE_CHUNK_US
PREVIEW_MERGE_CACHE_MAX_AGE_SEC = 7200  # 启动时清除超过 2h 的临时预览
PREVIEW_MERGE_WIDTH = 480  # 合成宽度；最终仍可按 PREVIEW_MAX_WIDTH 缩小显示
PREVIEW_MERGE_ENABLED = False
PREVIEW_MERGE_MIN_TRIM_US = 80_000  # trim 最短 80ms，避免 aac 收不到 packet
PREVIEW_MERGE_FFPLAY_TITLE_PREFIX = "jyDraftPrev_"
PREVIEW_SUB_BAR_HEIGHT = 100  # ffplay 播放时底部字幕条高度
PREVIEW_MERGE_SUBTITLE_LAG_US = 0
PREVIEW_MERGE_SYNC_HOLD_MS = 180
PREVIEW_AUDIO_CHUNK_US = 8_000_000
PREVIEW_AUDIO_PREFETCH_LEAD_US = 2_000_000
PREVIEW_AUDIO_LATE_ATTACH_US = 250_000


def _preview_merge_chunk_end_us(content: Dict[str, Any], t0_us: int, window_us: int) -> int:
    return min(int(t0_us + window_us), _timeline_end_us(content))


@dataclass(frozen=True)
class _PreviewVideoSlice:
    path: str
    source_start_us: int
    source_duration_us: int
    timeline_duration_us: int
    playback_rate: float


@dataclass(frozen=True)
class _PreviewAudioClip:
    path: str
    source_start_us: int
    source_duration_us: int
    timeline_offset_us: int
    volume: float
    playback_rate: float


def _preview_merge_target_size(content: Dict[str, Any]) -> Tuple[int, int]:
    """合成预览统一画布（竖屏 1080×1920 → 480×854），concat 要求宽高完全一致。"""
    cfg = content.get("canvas_config") if isinstance(content.get("canvas_config"), dict) else {}
    try:
        cw = int(cfg.get("width") or content.get("width") or 1080)
        ch = int(cfg.get("height") or content.get("height") or 1920)
    except (TypeError, ValueError):
        cw, ch = 1080, 1920
    if cw <= 0:
        cw = 1080
    if ch <= 0:
        ch = 1920
    tw = PREVIEW_MERGE_WIDTH
    th = max(2, int(round(tw * ch / cw)) // 2 * 2)
    return tw, th


def _preview_content_fingerprint(content: Dict[str, Any]) -> str:
    parts: List[str] = [str(_timeline_end_us(content))]
    for tr in content.get("tracks") or []:
        ttype = str(tr.get("type", "")).strip().lower()
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            trng = seg.get("target_timerange") or {}
            parts.append(
                "|".join(
                    (
                        ttype,
                        str(tr.get("attribute", 0)),
                        str(seg.get("material_id", "")),
                        str(trng.get("start", 0)),
                        str(trng.get("duration", 0)),
                        str(seg.get("speed", 1.0)),
                        str(seg.get("volume", 1.0)),
                    )
                )
            )
    return hashlib.sha1("\n".join(parts).encode("utf-8", errors="replace")).hexdigest()[:24]


def _preview_merge_cache_dir() -> Path:
    d = Path(os.environ.get("TEMP") or ".") / "jy_preview_cache"
    d.mkdir(parents=True, exist_ok=True)
    return d


def _preview_merge_cache_path(
    content: Dict[str, Any],
    t0_us: int,
    window_us: int,
    *,
    extra: str = "",
) -> Path:
    fp = _preview_content_fingerprint(content)
    bucket = int(max(0, t0_us) // 100_000)
    tw, th = _preview_merge_target_size(content)
    name = f"m_{fp}_{bucket}_{window_us // 1_000_000}_{tw}x{th}{extra}.mp4"
    return _preview_merge_cache_dir() / name


def _preview_merge_cache_usable(path: Path) -> bool:
    try:
        if not path.is_file() or path.stat().st_size < 2048:
            return False
    except OSError:
        return False
    return _ffmpeg_input_has_stream(str(path), "video")


def _preview_audio_cache_path(
    content: Dict[str, Any],
    t0_us: int,
    window_us: int,
) -> Path:
    fp = _preview_content_fingerprint(content)
    bucket = int(max(0, t0_us) // 100_000)
    name = f"a_{fp}_{bucket}_{window_us // 1_000_000}.m4a"
    return _preview_merge_cache_dir() / name


def _preview_audio_cache_usable(path: Path) -> bool:
    try:
        if not path.is_file() or path.stat().st_size < 256:
            return False
    except OSError:
        return False
    return _ffmpeg_input_has_stream(str(path), "audio")


def _build_preview_audio_window_ffmpeg_cmd(
    content: Dict[str, Any],
    t0_us: int,
    window_us: int,
    out_path: str,
) -> Tuple[Optional[List[str]], Optional[str]]:
    """构建时间轴窗口 [t0, t0+window] 的混音（adelay 对齐时间轴 T，仅音频）。"""
    ff = find_ffmpeg()
    if not ff:
        return None, "未找到 ffmpeg"
    t0 = max(0, int(t0_us))
    t1 = min(int(t0 + window_us), _timeline_end_us(content))
    if t1 <= t0:
        return None, "音频窗口无效"
    window_sec = (t1 - t0) / 1_000_000.0
    a_clips = _collect_preview_audio_clips(content, t0, t1)

    cmd: List[str] = [ff, "-hide_banner", "-loglevel", "error", "-y"]
    a_filters: List[str] = []
    ai = 0
    for clip in a_clips:
        if clip.timeline_offset_us >= int(window_us):
            continue
        if not _ffmpeg_input_has_stream(clip.path, "audio"):
            continue
        delay_ms = max(0, int(clip.timeline_offset_us // 1000))
        if delay_ms >= int(window_sec * 1000):
            continue
        idx, fine = _ffmpeg_add_seek_input(cmd, clip.path, clip.source_start_us)
        src_dur_sec = clip.source_duration_us / 1_000_000.0
        vol = max(0.0, min(8.0, clip.volume))
        chain = (
            f"[{idx}:a]atrim=start={fine:.6f}:duration={src_dur_sec:.6f},"
            f"asetpts=PTS-STARTPTS{_atempo_chain_suffix(clip.playback_rate)},"
            f"volume={vol:.4f},adelay={delay_ms}|{delay_ms},"
            f"aformat=sample_fmts=fltp:channel_layouts=mono:sample_rates=22050[pa{ai}]"
        )
        a_filters.append(chain)
        ai += 1

    if ai == 1:
        a_out_label = "[pa0]"
    elif ai > 1:
        ins = "".join(f"[pa{i}]" for i in range(ai))
        a_filters.append(
            f"{ins}amix=inputs={ai}:duration=longest:dropout_transition=0,"
            f"aformat=sample_fmts=fltp:channel_layouts=mono:sample_rates=22050[aout]"
        )
        a_out_label = "[aout]"
    if ai == 0:
        cmd.extend(["-f", "lavfi", "-i", f"anullsrc=r=22050:cl=mono:d={window_sec:.3f}"])
        cmd.extend(
            [
                "-map",
                "0:a",
                "-t",
                f"{window_sec:.6f}",
                "-c:a",
                "aac",
                "-b:a",
                "64k",
                "-ar",
                "22050",
                "-ac",
                "1",
                out_path,
            ]
        )
        return cmd, None

    cmd.extend(
        [
            "-filter_complex",
            ";".join(a_filters),
            "-map",
            a_out_label,
            "-t",
            f"{window_sec:.6f}",
            "-c:a",
            "aac",
            "-b:a",
            "64k",
            "-ar",
            "22050",
            "-ac",
            "1",
            out_path,
        ]
    )
    return cmd, None


def render_preview_audio_window(
    content: Dict[str, Any],
    t0_us: int,
    *,
    window_us: int = PREVIEW_AUDIO_CHUNK_US,
) -> Tuple[Optional[str], Optional[str]]:
    """按时间轴混音渲染预览音频段；命中缓存则秒开。"""
    cache_path = _preview_audio_cache_path(content, t0_us, window_us)
    if _preview_audio_cache_usable(cache_path):
        return str(cache_path), None
    part = cache_path.with_suffix(".part.m4a")
    try:
        if part.is_file():
            part.unlink()
    except OSError:
        pass
    cmd, err = _build_preview_audio_window_ffmpeg_cmd(content, t0_us, window_us, str(part))
    if not cmd:
        return None, err or "无法构建音频命令"
    try:
        proc = subprocess.run(cmd, capture_output=True, timeout=max(60, int(window_us / 1_000_000) * 6 + 20))
    except (subprocess.TimeoutExpired, OSError) as ex:
        return None, str(ex)
    if proc.returncode != 0 or not part.is_file() or part.stat().st_size < 128:
        err_tail = (proc.stderr or b"").decode("utf-8", errors="replace")[-800:]
        try:
            if part.is_file():
                part.unlink()
        except OSError:
            pass
        return None, f"时间轴音频渲染失败：{err_tail or proc.returncode}"
    try:
        os.replace(str(part), str(cache_path))
    except OSError:
        return str(part), None
    return str(cache_path), None


def _delete_merge_preview_file(path: Optional[str]) -> None:
    """删除 jy_preview_cache 下的单段合成预览 MP4。"""
    if not path:
        return
    try:
        p = Path(path).resolve()
        cache_root = _preview_merge_cache_dir().resolve()
        if p.parent != cache_root:
            return
        if p.is_file():
            p.unlink()
    except OSError:
        pass


def _cleanup_stale_preview_merge_cache(*, max_age_sec: int = PREVIEW_MERGE_CACHE_MAX_AGE_SEC) -> None:
    """清除过期的合成预览缓存与残留 .part 文件。"""
    d = _preview_merge_cache_dir()
    if not d.is_dir():
        return
    cutoff = time.time() - max(60, int(max_age_sec))
    for f in d.glob("m_*.part.mp4"):
        _delete_merge_preview_file(str(f))
    for f in d.glob("m_*.mp4"):
        try:
            if f.stat().st_mtime < cutoff:
                f.unlink()
        except OSError:
            pass


def _find_top_video_seg_at(content: Dict[str, Any], playhead_us: int) -> Optional[Dict[str, Any]]:
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    ph = max(0, int(playhead_us))
    best: Optional[Dict[str, Any]] = None
    best_ri = -1
    for tr in content.get("tracks") or []:
        if str(tr.get("type", "")).strip().lower() != "video":
            continue
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            if _segment_source_us_at_playhead(seg, ph) is None:
                continue
            try:
                ri = int(seg.get("render_index", 0))
            except (TypeError, ValueError):
                ri = 0
            if ri >= best_ri:
                best_ri = ri
                best = seg
    return best


def _collect_preview_video_slices(content: Dict[str, Any], t0_us: int, t1_us: int) -> List[_PreviewVideoSlice]:
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    t0 = int(t0_us)
    t1 = int(t1_us)
    boundaries = {t0, t1}
    for tr in content.get("tracks") or []:
        if str(tr.get("type", "")).strip().lower() != "video":
            continue
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            trng = seg.get("target_timerange") or {}
            try:
                st = int(trng.get("start", 0))
                du = int(trng.get("duration", 0))
            except (TypeError, ValueError):
                continue
            if du <= 0:
                continue
            en = st + du
            if en <= t0 or st >= t1:
                continue
            boundaries.add(max(st, t0))
            boundaries.add(min(en, t1))
    bounds = sorted(boundaries)
    slices: List[_PreviewVideoSlice] = []
    for i in range(len(bounds) - 1):
        a, b = bounds[i], bounds[i + 1]
        if b <= a:
            continue
        timeline_dur_us = b - a
        if timeline_dur_us < PREVIEW_MERGE_MIN_TRIM_US:
            continue
        mid = (a + b) // 2
        seg = _find_top_video_seg_at(content, mid)
        if seg is None:
            continue
        path = _local_media_path_for_segment(seg, materials)
        if not path or not os.path.isfile(path):
            continue
        if not _ffmpeg_input_has_stream(path, "video"):
            continue
        src_a = _segment_source_us_at_playhead(seg, a)
        if src_a is None:
            continue
        rate = _segment_audio_playback_rate(seg)
        src_dur = max(PREVIEW_MERGE_MIN_TRIM_US, int(timeline_dur_us * rate))
        slices.append(
            _PreviewVideoSlice(
                path=path,
                source_start_us=int(src_a),
                source_duration_us=int(src_dur),
                timeline_duration_us=int(timeline_dur_us),
                playback_rate=float(rate),
            )
        )
    return slices


def _coalesce_preview_video_slices(slices: List[_PreviewVideoSlice]) -> List[_PreviewVideoSlice]:
    if not slices:
        return []
    out: List[_PreviewVideoSlice] = [slices[0]]
    for sl in slices[1:]:
        prev = out[-1]
        if (
            prev.path == sl.path
            and abs(prev.playback_rate - sl.playback_rate) < 0.02
            and prev.source_start_us + prev.source_duration_us == sl.source_start_us
        ):
            out[-1] = _PreviewVideoSlice(
                path=prev.path,
                source_start_us=prev.source_start_us,
                source_duration_us=prev.source_duration_us + sl.source_duration_us,
                timeline_duration_us=prev.timeline_duration_us + sl.timeline_duration_us,
                playback_rate=prev.playback_rate,
            )
        else:
            out.append(sl)
    return out


def _collect_preview_audio_clips(content: Dict[str, Any], t0_us: int, t1_us: int) -> List[_PreviewAudioClip]:
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    t0 = int(t0_us)
    t1 = int(t1_us)
    clips: List[_PreviewAudioClip] = []
    for tr in content.get("tracks") or []:
        ttype = str(tr.get("type", "")).strip().lower()
        if ttype not in ("audio", "video"):
            continue
        if _track_is_muted(tr):
            continue
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            if not _is_playback_audio_audible(content, tr, seg, track_type=ttype):
                continue
            trng = seg.get("target_timerange") or {}
            try:
                st = int(trng.get("start", 0))
                du = int(trng.get("duration", 0))
            except (TypeError, ValueError):
                continue
            if du <= 0:
                continue
            en = st + du
            if en <= t0 or st >= t1:
                continue
            overlap_a = max(st, t0)
            overlap_b = min(en, t1)
            timeline_dur_us = overlap_b - overlap_a
            if timeline_dur_us < PREVIEW_MERGE_MIN_TRIM_US:
                continue
            path = _local_media_path_for_segment(seg, materials)
            if not path or not os.path.isfile(path):
                continue
            if ttype == "video" and not _media_maybe_has_audio(path):
                continue
            if not _ffmpeg_input_has_stream(path, "audio"):
                continue
            src_a = _segment_source_us_at_playhead(seg, overlap_a)
            if src_a is None:
                continue
            rate = _segment_audio_playback_rate(seg)
            src_dur = max(PREVIEW_MERGE_MIN_TRIM_US, int(timeline_dur_us * rate))
            clips.append(
                _PreviewAudioClip(
                    path=path,
                    source_start_us=int(src_a),
                    source_duration_us=int(src_dur),
                    timeline_offset_us=int(overlap_a - t0),
                    volume=_segment_volume(seg),
                    playback_rate=float(rate),
                )
            )
    return clips


def _ffmpeg_add_seek_input(cmd: List[str], path: str, source_start_us: int) -> Tuple[int, float]:
    """追加带粗 seek 的输入，返回 (input_index, fine_trim_start_sec)。"""
    path_abs = os.path.abspath(path)
    sec = max(0.0, source_start_us / 1_000_000.0)
    coarse = max(0.0, sec - PREVIEW_AUDIO_FINE_SEEK_SEC)
    fine = sec - coarse
    if coarse >= 0.001:
        cmd.extend(["-ss", f"{coarse:.6f}"])
    cmd.extend(["-i", path_abs])
    idx = sum(1 for i, x in enumerate(cmd) if x == "-i") - 1
    return idx, fine


def _atempo_chain_suffix(rate: float) -> str:
    af = _atempo_filter_for_speed(rate)
    return f",{af}" if af else ""


def _build_preview_merge_ffmpeg_cmd(
    content: Dict[str, Any],
    t0_us: int,
    window_us: int,
    out_path: str,
) -> Tuple[Optional[List[str]], Optional[str]]:
    """构建窗口 [t0, t0+window] 的低规格多轨合并命令（一次 pass）。"""
    ff = find_ffmpeg()
    if not ff:
        return None, "未找到 ffmpeg"
    t0 = max(0, int(t0_us))
    t1 = min(int(t0 + window_us), _timeline_end_us(content))
    if t1 <= t0:
        return None, "预览窗口无效"
    window_sec = (t1 - t0) / 1_000_000.0
    fps = _draft_preview_fps(content)
    merge_w, merge_h = _preview_merge_target_size(content)

    v_slices = _coalesce_preview_video_slices(_collect_preview_video_slices(content, t0, t1))
    if not v_slices:
        return None, "当前时间无视频"
    a_clips = _collect_preview_audio_clips(content, t0, t1)

    cmd: List[str] = [ff, "-hide_banner", "-loglevel", "error", "-y"]
    v_filters: List[str] = []
    a_filters: List[str] = []

    for si, sl in enumerate(v_slices):
        idx, fine = _ffmpeg_add_seek_input(cmd, sl.path, sl.source_start_us)
        src_dur_sec = sl.source_duration_us / 1_000_000.0
        chain = f"trim=start={fine:.6f}:duration={src_dur_sec:.6f},setpts=PTS-STARTPTS"
        if abs(sl.playback_rate - 1.0) >= 0.02:
            chain += f",setpts=PTS/{sl.playback_rate:.6f}"
        chain += (
            f",scale={merge_w}:{merge_h}:force_original_aspect_ratio=decrease,"
            f"pad={merge_w}:{merge_h}:(ow-iw)/2:(oh-ih)/2:black,"
            f"setsar=1,fps={fps:.3f},format=yuv420p"
        )
        v_filters.append(f"[{idx}:v]{chain}[pv{si}]")

    if len(v_slices) == 1:
        v_out_label = "[pv0]"
    else:
        ins = "".join(f"[pv{i}]" for i in range(len(v_slices)))
        v_filters.append(f"{ins}concat=n={len(v_slices)}:v=1:a=0[vout]")
        v_out_label = "[vout]"

    a_out_label = ""
    ai = 0
    for clip in a_clips:
        if clip.timeline_offset_us >= int(window_us):
            continue
        if not _ffmpeg_input_has_stream(clip.path, "audio"):
            continue
        delay_ms = max(0, int(clip.timeline_offset_us // 1000))
        if delay_ms >= int(window_sec * 1000):
            continue
        idx, fine = _ffmpeg_add_seek_input(cmd, clip.path, clip.source_start_us)
        src_dur_sec = clip.source_duration_us / 1_000_000.0
        vol = max(0.0, min(8.0, clip.volume))
        chain = (
            f"[{idx}:a]atrim=start={fine:.6f}:duration={src_dur_sec:.6f},"
            f"asetpts=PTS-STARTPTS{_atempo_chain_suffix(clip.playback_rate)},"
            f"volume={vol:.4f},adelay={delay_ms}|{delay_ms},"
            f"aformat=sample_fmts=fltp:channel_layouts=mono:sample_rates=22050[pa{ai}]"
        )
        a_filters.append(chain)
        ai += 1

    if ai == 1:
        a_out_label = "[pa0]"
    elif ai > 1:
        ins = "".join(f"[pa{i}]" for i in range(ai))
        a_filters.append(
            f"{ins}amix=inputs={ai}:duration=longest:dropout_transition=0,"
            f"aformat=sample_fmts=fltp:channel_layouts=mono:sample_rates=22050[aout]"
        )
        a_out_label = "[aout]"
    if not a_out_label:
        cmd.extend(["-f", "lavfi", "-i", f"anullsrc=r=22050:cl=mono:d={window_sec:.3f}"])
        n_in = sum(1 for x in cmd if x == "-i") - 1
        a_out_label = f"[{n_in}:a]"

    filters = v_filters + a_filters
    cmd.extend(
        [
            "-filter_complex",
            ";".join(filters),
            "-map",
            v_out_label,
            "-map",
            a_out_label,
            "-t",
            f"{window_sec:.6f}",
            "-c:v",
            "libx264",
            "-preset",
            "ultrafast",
            "-tune",
            "zerolatency",
            "-crf",
            "28",
            "-pix_fmt",
            "yuv420p",
            "-c:a",
            "aac",
            "-b:a",
            "64k",
            "-ar",
            "22050",
            "-ac",
            "1",
            "-movflags",
            "+faststart",
            out_path,
        ]
    )
    return cmd, None


def render_preview_merge_window(
    content: Dict[str, Any],
    t0_us: int,
    *,
    window_us: int = PREVIEW_MERGE_WINDOW_US,
) -> Tuple[Optional[str], Optional[str]]:
    """渲染预览窗口 MP4；命中缓存则秒开。返回 (path, error)。"""
    cache_path = _preview_merge_cache_path(content, t0_us, window_us)
    if _preview_merge_cache_usable(cache_path):
        return str(cache_path), None
    part = cache_path.with_suffix(".part.mp4")
    try:
        if part.is_file():
            part.unlink()
    except OSError:
        pass
    cmd, err = _build_preview_merge_ffmpeg_cmd(content, t0_us, window_us, str(part))
    if not cmd:
        return None, err or "无法构建合成命令"
    try:
        proc = subprocess.run(cmd, capture_output=True, timeout=max(120, int(window_us / 1_000_000) * 8 + 30))
    except (subprocess.TimeoutExpired, OSError) as ex:
        return None, str(ex)
    if proc.returncode != 0 or not part.is_file() or part.stat().st_size < 512:
        err_tail = (proc.stderr or b"").decode("utf-8", errors="replace")[-800:]
        try:
            if part.is_file():
                part.unlink()
        except OSError:
            pass
        return None, f"预览合成失败：{err_tail or proc.returncode}"
    try:
        os.replace(str(part), str(cache_path))
    except OSError:
        return str(part), None
    return str(cache_path), None


def spawn_merged_preview_audio(
    merge_path: str,
    *,
    start_sec: float = 0.0,
) -> List[subprocess.Popen]:
    """仅音频 ffplay（非 Windows 或嵌入失败时的回退）。"""
    ffplay = find_ffplay()
    if not ffplay or not merge_path or not os.path.isfile(merge_path):
        return []
    devnull = subprocess.DEVNULL
    cmd: List[str] = [
        ffplay,
        "-nodisp",
        "-autoexit",
        "-loglevel",
        "error",
        "-volume",
        "100",
        "-probesize",
        "32768",
        "-analyzeduration",
        "0",
    ]
    seek = max(0.0, float(start_sec))
    if seek >= 0.05:
        cmd.extend(["-ss", f"{seek:.3f}"])
    cmd.extend(["-i", os.path.abspath(merge_path)])
    try:
        creationflags = subprocess.CREATE_NO_WINDOW if sys.platform == "win32" else 0
        proc = subprocess.Popen(
            cmd,
            stdout=devnull,
            stderr=devnull,
            creationflags=creationflags,
        )
    except OSError:
        return []
    return [proc]


def _merge_preview_ffplay_title(token: str) -> str:
    return f"{PREVIEW_MERGE_FFPLAY_TITLE_PREFIX}{token}"


def _win_find_window_title_contains(substr: str) -> Optional[int]:
    if sys.platform != "win32" or not substr:
        return None
    import ctypes

    user32 = ctypes.windll.user32
    found: List[int] = []

    def _callback(hwnd: int, _lparam: int) -> bool:
        if not user32.IsWindowVisible(hwnd):
            return True
        length = user32.GetWindowTextLengthW(hwnd)
        if length <= 0:
            return True
        buf = ctypes.create_unicode_buffer(length + 1)
        user32.GetWindowTextW(hwnd, buf, length + 1)
        if substr in buf.value:
            found.append(int(hwnd))
            return False
        return True

    WNDENUMPROC = ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.c_void_p, ctypes.c_void_p)
    user32.EnumWindows(WNDENUMPROC(_callback), 0)
    return found[0] if found else None


def _win_embed_child_window(child_hwnd: int, parent_hwnd: int, width: int, height: int) -> None:
    import ctypes

    user32 = ctypes.windll.user32
    gwl_style = -16
    ws_child = 0x40000000
    ws_visible = 0x10000000
    ws_caption = 0x00C00000
    ws_thickframe = 0x00040000
    ws_popup = 0x80000000
    swp_no_zorder = 0x0004
    swp_showwindow = 0x0040
    user32.SetParent(child_hwnd, parent_hwnd)
    style = user32.GetWindowLongW(child_hwnd, gwl_style)
    style &= ~(ws_popup | ws_caption | ws_thickframe)
    style |= ws_child | ws_visible
    user32.SetWindowLongW(child_hwnd, gwl_style, style)
    user32.SetWindowPos(
        child_hwnd,
        0,
        0,
        0,
        max(40, int(width)),
        max(40, int(height)),
        swp_no_zorder | swp_showwindow,
    )


def _win_resize_embedded_window(child_hwnd: int, width: int, height: int) -> None:
    import ctypes

    user32 = ctypes.windll.user32
    user32.SetWindowPos(
        child_hwnd,
        0,
        0,
        0,
        max(40, int(width)),
        max(40, int(height)),
        0x0004,
    )


def spawn_merged_preview_player(
    merge_path: str,
    *,
    window_title: str,
    width: int,
    height: int,
    start_sec: float = 0.0,
) -> Optional[subprocess.Popen]:
    """ffplay 单路播放合成 MP4（音画一体，窗口标题用于嵌入 Tk）。"""
    ffplay = find_ffplay()
    if not ffplay or not merge_path or not os.path.isfile(merge_path):
        return None
    devnull = subprocess.DEVNULL
    cmd: List[str] = [
        ffplay,
        "-autoexit",
        "-loglevel",
        "quiet",
        "-window_title",
        window_title,
        "-x",
        str(max(80, int(width))),
        "-y",
        str(max(80, int(height))),
        "-probesize",
        "32",
        "-analyzeduration",
        "0",
        "-fflags",
        "nobuffer",
        "-flags",
        "low_delay",
    ]
    seek = max(0.0, float(start_sec))
    if seek >= 0.05:
        cmd.extend(["-ss", f"{seek:.3f}"])
    cmd.extend(["-i", os.path.abspath(merge_path)])
    try:
        return subprocess.Popen(cmd, stdout=devnull, stderr=devnull)
    except OSError:
        return None


def _merge_preview_prime_frame(
    merge_path: str,
    content: Dict[str, Any],
    merge_t0_us: int,
) -> Optional[Tuple[bytes, PreviewPlan]]:
    """读取合成预览首帧（暂停态缩略图，不启动播放）。"""
    reader = _MergedPreviewReader()
    if not reader.open(merge_path):
        return None
    reader.sync_file_us(0, force=True)
    ppm = reader.read_ppm()
    reader.close()
    if not ppm:
        return None
    return ppm, build_preview_plan(content, int(merge_t0_us))


class _MergedPreviewFfplaySession:
    """合成预览：ffplay 单窗口音画 + 外部 timeline 驱动字幕。"""

    __slots__ = ("proc", "hwnd", "window_title")

    def __init__(self) -> None:
        self.proc: Optional[subprocess.Popen] = None
        self.hwnd: Optional[int] = None
        self.window_title: str = ""

    def close(self) -> None:
        if self.proc is not None:
            _terminate_subprocess(self.proc)
        self.proc = None
        self.hwnd = None
        self.window_title = ""

    def alive(self) -> bool:
        return self.proc is not None and self.proc.poll() is None

    def spawn(
        self,
        merge_path: str,
        *,
        window_title: str,
        width: int,
        height: int,
        start_sec: float = 0.0,
    ) -> bool:
        self.close()
        proc = spawn_merged_preview_player(
            merge_path,
            window_title=window_title,
            width=width,
            height=height,
            start_sec=start_sec,
        )
        if proc is None:
            return False
        self.proc = proc
        self.window_title = window_title
        self.hwnd = None
        return True

    def try_embed(self, parent_hwnd: int, width: int, height: int) -> bool:
        if not self.alive():
            return False
        if sys.platform != "win32":
            return True
        if self.hwnd:
            _win_resize_embedded_window(self.hwnd, width, height)
            return True
        hwnd = _win_find_window_title_contains(self.window_title)
        if hwnd is None:
            return False
        _win_embed_child_window(hwnd, parent_hwnd, width, height)
        self.hwnd = hwnd
        return True


class _MergedPreviewReader:
    """读取已合成的预览 MP4（文件 0s = 草稿 timeline t0）。"""

    __slots__ = ("_cap", "_path", "_max_w", "_last_file_us", "_lock")

    def __init__(self, max_width: int = 280) -> None:
        self._cap: Any = None
        self._path = ""
        self._max_w = max_width
        self._last_file_us: Optional[int] = None
        self._lock = threading.Lock()

    def close(self) -> None:
        with self._lock:
            if self._cap is not None:
                try:
                    self._cap.release()
                except Exception:
                    pass
                self._cap = None
            self._path = ""
            self._last_file_us = None

    def open(self, path: str) -> bool:
        import cv2

        with self._lock:
            if self._cap is not None:
                try:
                    self._cap.release()
                except Exception:
                    pass
                self._cap = None
            path_abs = os.path.abspath(path)
            cap = cv2.VideoCapture(path_abs)
            if not cap.isOpened():
                self._path = ""
                self._last_file_us = None
                return False
            self._cap = cap
            self._path = path_abs
            self._last_file_us = 0
            return True

    def sync_file_us(self, file_us: int, *, force: bool = False) -> None:
        import cv2

        with self._lock:
            if self._cap is None or not self._cap.isOpened():
                return
            want = max(0, int(file_us))
            drift = abs(want - self._last_file_us) if self._last_file_us is not None else 999_999_999
            if force or drift > 120_000:
                try:
                    self._cap.set(cv2.CAP_PROP_POS_MSEC, want / 1000.0)
                except Exception:
                    pass
                self._last_file_us = want

    def read_ppm(self) -> Optional[bytes]:
        import cv2

        with self._lock:
            if self._cap is None or not self._cap.isOpened():
                return None
            ok, frame = self._cap.read()
            if not ok or frame is None:
                return None
            try:
                self._last_file_us = int(self._cap.get(cv2.CAP_PROP_POS_MSEC) * 1000)
            except (TypeError, ValueError):
                pass
            h, w = frame.shape[:2]
            if w > self._max_w and w > 0:
                nh = max(1, int(h * self._max_w / w))
                frame = cv2.resize(frame, (self._max_w, nh), interpolation=cv2.INTER_LINEAR)
            rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            ih, iw = rgb.shape[:2]
            return f"P6\n{iw} {ih}\n255\n".encode("ascii") + rgb.tobytes()


class _MergedPreviewVideoWorker:
    """播放合成预览：单 MP4 顺序读帧 + 字幕仍按草稿 timeline T 叠加。"""

    __slots__ = ("_reader", "_thread", "_stop", "_lock", "_latest", "_content", "_merge_t0_us")

    def __init__(self) -> None:
        self._reader = _MergedPreviewReader()
        self._thread: Optional[threading.Thread] = None
        self._stop = threading.Event()
        self._lock = threading.Lock()
        self._latest: Optional[Tuple[bytes, PreviewPlan, int, int]] = None
        self._content: Optional[Dict[str, Any]] = None
        self._merge_t0_us = 0

    def close(self) -> None:
        self._stop.set()
        th = self._thread
        if th is not None and th.is_alive():
            th.join(timeout=1.5)
        self._thread = None
        self._reader.close()
        with self._lock:
            self._latest = None
        self._content = None

    def prime_first_frame(
        self,
        merge_path: str,
        content: Dict[str, Any],
        merge_t0_us: int,
        *,
        gen: int,
    ) -> Optional[PreviewPlan]:
        if not self._reader.open(merge_path):
            return None
        self._content = content
        self._merge_t0_us = int(merge_t0_us)
        self._reader.sync_file_us(0, force=True)
        ppm = self._reader.read_ppm()
        plan = build_preview_plan(content, int(merge_t0_us))
        if ppm:
            with self._lock:
                self._latest = (ppm, plan, int(merge_t0_us), int(gen))
        return plan

    def start(
        self,
        *,
        get_state: Callable[[], Optional[Tuple[float, int, int]]],
        fps: float,
    ) -> None:
        self._stop.clear()
        step_us = max(1, int(1_000_000.0 / fps))
        stop_ev = self._stop
        content = self._content

        def _run() -> None:
            last_frame_idx = -1
            while not stop_ev.is_set():
                st = get_state()
                if st is None or content is None:
                    stop_ev.wait(0.02)
                    continue
                wall_t0, start_us, gen = st
                merge_t0 = int(self._merge_t0_us)
                elapsed_us = int(max(0.0, time.time() - wall_t0) * 1_000_000)
                timeline_us = start_us + elapsed_us
                file_us = max(0, timeline_us - merge_t0)
                frame_idx = timeline_us // step_us
                if frame_idx <= last_frame_idx:
                    next_t = wall_t0 + (last_frame_idx + 1) * step_us / 1_000_000.0
                    delay = next_t - time.time()
                    if delay > 0:
                        stop_ev.wait(min(delay, 0.04))
                    continue
                self._reader.sync_file_us(file_us, force=(last_frame_idx < 0))
                ppm = self._reader.read_ppm()
                plan = build_preview_plan(content, timeline_us)
                if ppm:
                    with self._lock:
                        self._latest = (ppm, plan, timeline_us, gen)
                    last_frame_idx = frame_idx
                else:
                    stop_ev.wait(0.01)

        self._thread = threading.Thread(target=_run, daemon=True, name="preview-merge-play")
        self._thread.start()

    def take_latest(self) -> Optional[Tuple[bytes, PreviewPlan, int, int]]:
        with self._lock:
            item = self._latest
            self._latest = None
            return item

    def switch_chunk(self, merge_path: str, merge_t0_us: int, *, file_us: int = 0) -> bool:
        """切换到下一段已合成 MP4（file 0s = 新段 timeline t0）。"""
        if not self._reader.open(merge_path):
            return False
        self._merge_t0_us = int(merge_t0_us)
        self._reader.sync_file_us(max(0, int(file_us)), force=True)
        return True


SCRUB_THUMB_FPS = 2.5
SCRUB_THUMB_STEP_US = int(1_000_000 / SCRUB_THUMB_FPS)
PREVIEW_MAX_WIDTH = 256
SCRUB_THUMB_WIDTH = 256
PREVIEW_WARM_INITIAL_SEC = 30.0
PREVIEW_WARM_WINDOW_SEC = 50.0
PREVIEW_WARM_SCRUB_FOLLOW_SEC = 12.0
PREVIEW_WARM_SCRUB_THROTTLE_MS = 220
PREVIEW_WARM_IDLE_MS = 1200
PREVIEW_PLAY_SYNC_HOLD_MS = 160
PREVIEW_PLAY_SYNC_TIMEOUT_MS = 2500


class _PlaybackVideoReader:
    """播放时用 OpenCV 顺序读帧，避免每帧启动 ffmpeg。"""

    __slots__ = ("_cap", "_path", "_max_w", "_last_source_us")

    def __init__(self, max_width: int = PREVIEW_MAX_WIDTH) -> None:
        self._cap: Any = None
        self._path = ""
        self._max_w = max_width
        self._last_source_us: Optional[int] = None

    def close(self) -> None:
        if self._cap is not None:
            try:
                self._cap.release()
            except Exception:
                pass
            self._cap = None
        self._path = ""
        self._last_source_us = None

    def sync_layer(
        self,
        layer: PreviewVideoLayer,
        *,
        fps: float,
        step_us: int,
        force_seek: bool = False,
    ) -> None:
        import cv2

        path = os.path.abspath(layer.path)
        want_us = int(layer.source_us)
        if self._path != path or self._cap is None or not self._cap.isOpened():
            self.close()
            self._path = path
            cap = cv2.VideoCapture(path)
            if not cap.isOpened():
                self._cap = None
                return
            cap.set(cv2.CAP_PROP_POS_MSEC, max(0.0, want_us / 1000.0))
            self._cap = cap
            self._last_source_us = want_us
            return
        drift = abs(want_us - self._last_source_us) if self._last_source_us is not None else step_us * 3
        if force_seek or drift > max(step_us * 2, 80_000) or abs(layer.speed - 1.0) >= 0.02:
            try:
                self._cap.set(cv2.CAP_PROP_POS_MSEC, max(0.0, want_us / 1000.0))
            except Exception:
                pass
            self._last_source_us = want_us

    def read_ppm(self) -> Optional[bytes]:
        import cv2

        if self._cap is None or not self._cap.isOpened():
            return None
        ok, frame = self._cap.read()
        if not ok or frame is None:
            return None
        h, w = frame.shape[:2]
        if w > self._max_w and w > 0:
            nh = max(1, int(h * self._max_w / w))
            frame = cv2.resize(frame, (self._max_w, nh), interpolation=cv2.INTER_LINEAR)
        rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
        ih, iw = rgb.shape[:2]
        return f"P6\n{iw} {ih}\n255\n".encode("ascii") + rgb.tobytes()


class _PlaybackVideoWorker:
    """后台按帧率解码视频，主线程只负责贴图，减轻卡顿并让字幕与画面同源。"""

    __slots__ = ("_reader", "_thread", "_stop", "_lock", "_latest")

    def __init__(self) -> None:
        self._reader = _PlaybackVideoReader()
        self._thread: Optional[threading.Thread] = None
        self._stop = threading.Event()
        self._lock = threading.Lock()
        self._latest: Optional[Tuple[bytes, PreviewPlan, int, int]] = None

    def close(self) -> None:
        self._stop.set()
        th = self._thread
        if th is not None and th.is_alive():
            th.join(timeout=1.5)
        self._thread = None
        self._reader.close()
        with self._lock:
            self._latest = None

    def prime_first_frame(
        self,
        content: Dict[str, Any],
        timeline_us: int,
        *,
        fps: float,
        gen: int,
    ) -> Optional[PreviewPlan]:
        step_us = max(1, int(1_000_000.0 / fps))
        plan = build_preview_plan(content, max(0, int(timeline_us)))
        if not plan.videos:
            return None
        top = plan.videos[-1]
        self._reader.sync_layer(top, fps=fps, step_us=step_us, force_seek=True)
        ppm = self._reader.read_ppm()
        if ppm:
            with self._lock:
                self._latest = (ppm, plan, int(timeline_us), int(gen))
        return plan

    def start(
        self,
        content: Dict[str, Any],
        *,
        get_state: Callable[[], Optional[Tuple[float, int, int]]],
        fps: float,
    ) -> None:
        self._stop.clear()
        step_us = max(1, int(1_000_000.0 / fps))
        stop_ev = self._stop

        def _run() -> None:
            last_frame_idx = -1
            while not stop_ev.is_set():
                st = get_state()
                if st is None:
                    stop_ev.wait(0.02)
                    continue
                wall_t0, start_us, gen = st
                elapsed_us = int(max(0.0, time.time() - wall_t0) * 1_000_000)
                timeline_us = start_us + elapsed_us
                frame_idx = timeline_us // step_us
                if frame_idx <= last_frame_idx:
                    next_t = wall_t0 + (last_frame_idx + 1) * step_us / 1_000_000.0
                    delay = next_t - time.time()
                    if delay > 0:
                        stop_ev.wait(min(delay, 0.04))
                    continue
                plan = build_preview_plan(content, timeline_us)
                if not plan.videos:
                    stop_ev.wait(0.02)
                    continue
                top = plan.videos[-1]
                self._reader.sync_layer(top, fps=fps, step_us=step_us, force_seek=True)
                ppm = self._reader.read_ppm()
                if ppm:
                    with self._lock:
                        self._latest = (ppm, plan, timeline_us, gen)
                    last_frame_idx = frame_idx
                else:
                    stop_ev.wait(0.01)

        self._thread = threading.Thread(target=_run, daemon=True, name="preview-play-video")
        self._thread.start()

    def take_latest(self) -> Optional[Tuple[bytes, PreviewPlan, int, int]]:
        with self._lock:
            item = self._latest
            self._latest = None
            return item


class _PreviewFrameCache:
    """LRU 帧缓存；时间按 100ms 分桶以提高拖动命中率。"""

    __slots__ = ("_max", "_data")

    def __init__(self, max_items: int = 64) -> None:
        self._max = max(8, max_items)
        self._data: OrderedDict[Tuple[str, int], bytes] = OrderedDict()

    def get(self, path: str, source_us: int) -> Optional[bytes]:
        key = (path, int(source_us // 100_000))
        v = self._data.get(key)
        if v is not None:
            self._data.move_to_end(key)
        return v

    def put(self, path: str, source_us: int, img: bytes) -> None:
        key = (path, int(source_us // 100_000))
        self._data[key] = img
        self._data.move_to_end(key)
        while len(self._data) > self._max:
            self._data.popitem(last=False)

    def clear(self) -> None:
        self._data.clear()


def _ffmpeg_seek_input_args(path_abs: str, sec: float) -> List[str]:
    """前几秒用精确 seek，避免 fast seek 黑帧。"""
    if sec < 0.8:
        return ["-i", path_abs, "-ss", f"{max(0.0, sec):.3f}"]
    return ["-ss", f"{sec:.3f}", "-i", path_abs]


def _extract_one_ppm_frame(buf: bytes) -> Tuple[Optional[bytes], bytes]:
    """从字节流切出一帧完整 PPM/PGM（P5/P6），返回 (frame, remainder)。"""
    if len(buf) < 8 or buf[0:1] != b"P":
        return None, buf
    i = 2
    tokens: List[str] = []
    while i < min(len(buf), 4096) and len(tokens) < 3:
        while i < len(buf) and buf[i : i + 1] in (b" ", b"\t", b"\r", b"\n"):
            i += 1
        if i >= len(buf):
            break
        if buf[i : i + 1] == b"#":
            while i < len(buf) and buf[i : i + 1] not in (b"\n", b"\r"):
                i += 1
            continue
        j = i
        while j < len(buf) and buf[j : j + 1] not in (b" ", b"\t", b"\r", b"\n"):
            j += 1
        tok = buf[i:j].decode("ascii", errors="ignore")
        if tok:
            tokens.append(tok)
        i = j
    if len(tokens) < 2:
        return None, buf
    try:
        w, h = int(tokens[0]), int(tokens[1])
        maxval = int(tokens[2]) if len(tokens) >= 3 else 255
    except ValueError:
        return None, buf[1:]
    if w <= 0 or h <= 0:
        return None, buf[1:]
    while i < len(buf) and buf[i : i + 1] in (b" ", b"\t", b"\r", b"\n"):
        i += 1
    if i < len(buf) and buf[i : i + 1] == b"#":
        while i < len(buf) and buf[i : i + 1] not in (b"\n", b"\r"):
            i += 1
        while i < len(buf) and buf[i : i + 1] in (b" ", b"\t", b"\r", b"\n"):
            i += 1
    is_gray = buf[1:2] == b"5"
    depth = 1 if is_gray else 3
    bytes_per_sample = 2 if maxval > 255 else 1
    body = w * h * depth * bytes_per_sample
    total = i + body
    if len(buf) < total:
        return None, buf
    return buf[:total], buf[total:]


class _ThumbnailStripCache:
    """每素材按固定步长预生成的缩略图条，拖动时 O(1) 取最近帧。"""

    __slots__ = ("_step_us", "_data", "_warming", "_gen", "_procs")

    def __init__(self, step_us: int = SCRUB_THUMB_STEP_US) -> None:
        self._step_us = max(50_000, int(step_us))
        self._data: Dict[str, Dict[int, bytes]] = {}
        self._warming: set = set()
        self._gen = 0
        self._procs: Dict[str, Any] = {}

    def clear(self) -> None:
        self.interrupt_warming()
        self._gen += 1
        self._data.clear()
        self._warming.clear()

    def generation(self) -> int:
        return self._gen

    def register_proc(self, path: str, proc: Any) -> None:
        self._procs[os.path.abspath(path)] = proc

    def unregister_proc(self, path: str) -> None:
        self._procs.pop(os.path.abspath(path), None)

    def interrupt_warming(self) -> None:
        """终止正在跑的预热 ffmpeg（如开始拖动时），不阻止后续按需预热。"""
        for proc in list(self._procs.values()):
            try:
                proc.kill()
            except OSError:
                pass
        self._procs.clear()

    def put(self, path: str, source_us: int, ppm: bytes) -> None:
        p = os.path.abspath(path)
        bucket = int(source_us // self._step_us) * self._step_us
        self._data.setdefault(p, {})[bucket] = ppm

    def has_bucket(self, path: str, source_us: int) -> bool:
        p = os.path.abspath(path)
        frames = self._data.get(p)
        if not frames:
            return False
        bucket = int(source_us // self._step_us) * self._step_us
        return bucket in frames

    def nearest(self, path: str, source_us: int) -> Optional[bytes]:
        p = os.path.abspath(path)
        frames = self._data.get(p)
        if not frames:
            return None
        bucket = int(source_us // self._step_us) * self._step_us
        if bucket in frames:
            return frames[bucket]
        keys = sorted(frames.keys())
        if not keys:
            return None
        best = min(keys, key=lambda k: abs(k - bucket))
        return frames.get(best)

    def has_path(self, path: str) -> bool:
        return bool(self._data.get(os.path.abspath(path)))

    def mark_warming(self, path: str) -> bool:
        p = os.path.abspath(path)
        if p in self._warming:
            return False
        self._warming.add(p)
        return True

    def mark_done(self, path: str) -> None:
        p = os.path.abspath(path)
        self._warming.discard(p)
        self._procs.pop(p, None)


def _warm_video_thumbnail_strip(
    path: str,
    cache: _ThumbnailStripCache,
    *,
    cache_gen: int,
    fps: float = SCRUB_THUMB_FPS,
    max_width: int = SCRUB_THUMB_WIDTH,
    start_sec: float = 0.0,
    duration_sec: Optional[float] = None,
) -> None:
    ff = find_ffmpeg()
    path_abs = os.path.abspath(path)
    if not ff or not os.path.isfile(path_abs):
        cache.mark_done(path)
        return
    start_sec = max(0.0, float(start_sec))
    cmd: List[str] = [
        ff,
        "-hide_banner",
        "-loglevel",
        "error",
        "-ss",
        f"{start_sec:.3f}",
        "-i",
        path_abs,
    ]
    if duration_sec is not None and duration_sec > 0:
        cmd.extend(["-t", f"{float(duration_sec):.3f}"])
    cmd.extend(
        [
            "-an",
            "-vf",
            f"fps={fps:.3f},scale={max_width}:-2:flags=fast_bilinear,format=rgb24",
            "-f",
            "image2pipe",
            "-vcodec",
            "ppm",
            "pipe:1",
        ]
    )
    step_us = int(1_000_000 / fps)
    base_us = int(start_sec * 1_000_000)
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    except OSError:
        cache.mark_done(path)
        return
    if proc.stdout is None:
        cache.mark_done(path)
        return
    cache.register_proc(path, proc)
    buf = b""
    idx = 0
    try:
        while cache.generation() == cache_gen:
            chunk = proc.stdout.read(65536)
            if not chunk:
                break
            buf += chunk
            while cache.generation() == cache_gen:
                frame, buf = _extract_one_ppm_frame(buf)
                if frame is None:
                    break
                cache.put(path, base_us + idx * step_us, frame)
                idx += 1
    finally:
        cache.unregister_proc(path)
        try:
            proc.kill()
        except OSError:
            pass
        try:
            proc.wait(timeout=2)
        except (subprocess.TimeoutExpired, OSError):
            pass
        cache.mark_done(path)


def _start_warm_path(
    path: str,
    cache: _ThumbnailStripCache,
    *,
    start_sec: float = 0.0,
    duration_sec: Optional[float] = None,
) -> None:
    if not cache.mark_warming(path):
        return
    cache_gen = cache.generation()

    def _worker(p: str = path, g: int = cache_gen, st: float = start_sec, dur: Optional[float] = duration_sec) -> None:
        _warm_video_thumbnail_strip(p, cache, cache_gen=g, start_sec=st, duration_sec=dur)

    threading.Thread(target=_worker, daemon=True).start()


def start_preview_thumbnail_warm(content: Optional[Dict[str, Any]], cache: _ThumbnailStripCache) -> None:
    """加载草稿后仅预热各视频开头一小段，避免全片扫描占用资源。"""
    if not isinstance(content, dict):
        return
    for path in _collect_preview_video_paths(content):
        _start_warm_path(path, cache, start_sec=0.0, duration_sec=PREVIEW_WARM_INITIAL_SEC)


def start_preview_foreground_warm_on_load(content: Dict[str, Any], cache: _ThumbnailStripCache) -> None:
    """草稿加载后预热前景视频缩略图条（拖动预览主要依赖此缓存）。"""
    plan = build_preview_plan(content, 0)
    if not plan.videos:
        return
    top = plan.videos[-1]
    total_sec = max(8.0, _timeline_end_us(content) / 1_000_000.0)
    duration_sec = min(PREVIEW_WARM_INITIAL_SEC, total_sec)
    _start_warm_path(top.path, cache, start_sec=0.0, duration_sec=duration_sec)
    fg_abs = os.path.abspath(top.path)
    for path in _collect_preview_video_paths(content):
        if os.path.abspath(path) == fg_abs:
            continue
        _start_warm_path(path, cache, start_sec=0.0, duration_sec=min(12.0, duration_sec))


def warm_preview_strip_near_plan(
    plan: PreviewPlan,
    cache: _ThumbnailStripCache,
    *,
    window_sec: float = PREVIEW_WARM_SCRUB_FOLLOW_SEC,
) -> None:
    """拖动时在播放头附近按需补预热缩略图条。"""
    if not plan.videos:
        return
    top = plan.videos[-1]
    if cache.has_bucket(top.path, top.source_us):
        return
    half = max(4.0, float(window_sec)) / 2.0
    center_sec = max(0.0, top.source_us / 1_000_000.0)
    start_sec = max(0.0, center_sec - half)
    _start_warm_path(top.path, cache, start_sec=start_sec, duration_sec=float(window_sec))


def warm_preview_for_plan(plan: PreviewPlan, cache: _ThumbnailStripCache) -> None:
    """仅预热最前景视频层（与预览显示一致）。"""
    if not plan.videos:
        return
    top = plan.videos[-1]
    if cache.has_bucket(top.path, top.source_us):
        return
    half = PREVIEW_WARM_WINDOW_SEC / 2.0
    center_sec = max(0.0, top.source_us / 1_000_000.0)
    start_sec = max(0.0, center_sec - half)
    _start_warm_path(top.path, cache, start_sec=start_sec, duration_sec=PREVIEW_WARM_WINDOW_SEC)


def warm_preview_near_playhead(
    content: Dict[str, Any],
    cache: _ThumbnailStripCache,
    playhead_us: int,
) -> None:
    """空闲时在播放头附近补预热。"""
    warm_preview_for_plan(build_preview_plan(content, playhead_us), cache)


def _collect_preview_video_paths(content: Dict[str, Any]) -> List[str]:
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    seen: set = set()
    out: List[str] = []
    for tr in content.get("tracks") or []:
        if str(tr.get("type", "")).strip().lower() != "video":
            continue
        for seg in tr.get("segments") or []:
            if not isinstance(seg, dict):
                continue
            p = _local_media_path_for_segment(seg, materials)
            if not p or not os.path.isfile(p):
                continue
            pa = os.path.abspath(p)
            if pa in seen:
                continue
            seen.add(pa)
            out.append(p)
    return out


def fetch_instant_scrub_frame(plan: PreviewPlan, thumb_cache: _ThumbnailStripCache) -> Optional[bytes]:
    """拖动时从缩略图条取最近帧（仅最前景视频层，不回落到底层）。"""
    if not plan.videos:
        return None
    top = plan.videos[-1]
    return thumb_cache.nearest(top.path, top.source_us)


def fetch_scrub_frame_fast(
    plan: PreviewPlan,
    *,
    max_width: int = SCRUB_THUMB_WIDTH,
    frame_cache: Optional[_PreviewFrameCache] = None,
) -> Optional[bytes]:
    """拖动时的快速单帧：仅最前景视频，低分辨率 PPM + fast seek。"""
    if not plan.videos:
        return None
    layer = plan.videos[-1]
    ff = find_ffmpeg()
    if not ff or not os.path.isfile(layer.path):
        return None
    if frame_cache is not None:
        hit = frame_cache.get(layer.path, layer.source_us)
        if hit:
            return hit
    path_abs = os.path.abspath(layer.path)
    sec = max(0.0, layer.source_us / 1_000_000.0)
    cmd = [
        ff,
        "-hide_banner",
        "-loglevel",
        "error",
        "-ss",
        f"{sec:.3f}",
        "-i",
        path_abs,
        "-frames:v",
        "1",
        "-an",
        "-vf",
        f"scale={max_width}:-2:flags=fast_bilinear,format=rgb24",
        "-f",
        "image2pipe",
        "-vcodec",
        "ppm",
        "pipe:1",
    ]
    try:
        proc = subprocess.run(cmd, capture_output=True, timeout=12)
    except (subprocess.TimeoutExpired, OSError):
        return None
    if proc.returncode != 0 or not proc.stdout or proc.stdout[0:1] != b"P":
        return None
    if frame_cache is not None:
        frame_cache.put(layer.path, layer.source_us, proc.stdout)
    return proc.stdout


def _ppm_pixel_offset(ppm_bytes: bytes) -> Optional[int]:
    """P6 头三行后的像素数据起始偏移。"""
    if len(ppm_bytes) < 8 or ppm_bytes[0:2] != b"P6":
        return None
    line = 0
    i = 2
    n = len(ppm_bytes)
    while i < n and line < 3:
        if ppm_bytes[i : i + 1] == b"\n":
            line += 1
            if line == 3:
                return i + 1
        i += 1
    return None


def _scale_ppm_to_fit(ppm_bytes: bytes, avail_w: int, avail_h: int) -> bytes:
    """等比缩放 PPM 以适应预览区（可放大/缩小）。"""
    dims = _parse_ppm_dimensions(ppm_bytes)
    if dims is None or avail_w <= 0 or avail_h <= 0:
        return ppm_bytes
    iw, ih = dims
    off = _ppm_pixel_offset(ppm_bytes)
    if off is None or off + iw * ih * 3 > len(ppm_bytes):
        return ppm_bytes
    scale = min(avail_w / iw, avail_h / ih)
    nw = max(1, int(iw * scale))
    nh = max(1, int(ih * scale))
    if nw == iw and nh == ih:
        return ppm_bytes
    try:
        import cv2
        import numpy as np
    except ImportError:
        return ppm_bytes
    rgb = np.frombuffer(ppm_bytes[off : off + iw * ih * 3], dtype=np.uint8).reshape((ih, iw, 3))
    resized = cv2.resize(rgb, (nw, nh), interpolation=cv2.INTER_LINEAR)
    return f"P6\n{nw} {nh}\n255\n".encode("ascii") + resized.tobytes()


def _fit_photoimage_to_area(photo: tk.PhotoImage, avail_w: int, avail_h: int) -> tk.PhotoImage:
    """仅缩小过大图片；不做放大（zoom 会阻塞主线程导致卡死）。"""
    iw, ih = photo.width(), photo.height()
    if iw <= 0 or ih <= 0 or avail_w <= 0 or avail_h <= 0:
        return photo
    scale = min(avail_w / iw, avail_h / ih)
    if scale <= 0.8:
        s = max(1, int(1.0 / scale + 0.5))
        return photo.subsample(s, s)
    return photo


def _draw_preview_subtitle_overlays(
    canvas: tk.Canvas,
    texts: Tuple[PreviewTextLayer, ...],
    img_w: int,
    img_h: int,
    *,
    offset_x: int = 0,
    offset_y: int = 0,
) -> None:
    """预览字幕：底部水平居中，经典黑边黄字。"""
    canvas.delete("preview_sub")
    if not texts or img_w <= 0 or img_h <= 0:
        return
    fill = "#FFE135"
    stroke = "#000000"
    stroke_w = 2
    line_gap = 10
    lines: List[Tuple[str, int]] = []
    for layer in reversed(texts[:4]):
        line = (layer.text or "").strip()
        if not line:
            continue
        fs = max(11, min(20, layer.font_size))
        lines.append((line, fs))
    if not lines:
        return
    total_h = sum(fs for _, fs in lines) + line_gap * max(0, len(lines) - 1)
    cx = offset_x + img_w // 2
    y_top = offset_y + img_h - 8 - total_h
    tw = max(40, img_w - 16)
    tags = ("preview_sub",)
    for line, fs in lines:
        cy = y_top + fs // 2
        font = ("Microsoft YaHei UI", fs, "bold")
        for dx in range(-stroke_w, stroke_w + 1):
            for dy in range(-stroke_w, stroke_w + 1):
                if dx == 0 and dy == 0:
                    continue
                canvas.create_text(
                    cx + dx,
                    cy + dy,
                    text=line,
                    fill=stroke,
                    font=font,
                    width=tw,
                    anchor="center",
                    justify="center",
                    tags=tags,
                )
        canvas.create_text(
            cx,
            cy,
            text=line,
            fill=fill,
            font=font,
            width=tw,
            anchor="center",
            justify="center",
            tags=tags,
        )
        y_top += fs + line_gap


def timeline_segment_selection_status_parts(
    content: Dict[str, Any],
    *,
    ti: int,
    vis_i: int,
    orig_i: int,
    replace_state: Dict[str, Any],
) -> Optional[Tuple[str, str]]:
    """时间轴选中片段时：(主信息区正文, 底部高亮区「替换目录/替换文件」多行文案)。"""
    tracks_raw = list(content.get("tracks") or [])
    if not tracks_raw:
        return None
    tracks_sorted = sorted(tracks_raw, key=_track_render_index, reverse=True)
    if ti < 0 or ti >= len(tracks_sorted):
        return None
    tr = tracks_sorted[ti]
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    raw_segs = list(tr.get("segments") or [])
    if orig_i < 0 or orig_i >= len(raw_segs):
        return None
    seg = raw_segs[orig_i]
    trng = seg.get("target_timerange") or {}
    try:
        st = int(trng.get("start", 0))
        du = int(trng.get("duration", 0))
    except (TypeError, ValueError):
        return None
    lab = _timeline_segment_label(seg, materials)
    refs_list = replace_state.get("refs") or []
    ref = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i, content)
    style_refs_list = replace_state.get("style_refs") or []
    style_ref = find_style_ref_for_timeline_segment(style_refs_list, tr, orig_i, content)
    draft_nm = (replace_state.get("timeline_draft_name") or "").strip()
    pool_ui: Dict[str, Any] = replace_state.get("segment_export_pool") or {}
    if not isinstance(pool_ui, dict):
        pool_ui = {}
    rep_lines = segment_replace_status_lines(draft_nm, ref, pool_ui)
    rep_lines.extend(segment_style_status_lines(draft_nm, style_ref, pool_ui))
    src_path = ""
    if ref and (ref.current_path or "").strip():
        src_path = ref.current_path.strip()
    elif str(tr.get("type", "")) in ("video", "audio"):
        src_path = _local_media_path_for_segment(seg, materials)
    main_lines: List[str] = [
        f"已选片段：{tr.get('name')} [{tr.get('type')}] · 时间序第 {vis_i + 1} 段 · "
        f"{st/1e6:.2f}s—{(st+du)/1e6:.2f}s · {lab}",
    ]
    if style_ref and (style_ref.current_resource_id or "").strip():
        if style_ref.track_type == "text":
            main_lines.append(f"当前花字 id：{style_ref.current_resource_id.strip()}")
        else:
            main_lines.append(f"当前贴纸 id：{style_ref.current_resource_id.strip()}")
    if src_path:
        src_dir = os.path.dirname(src_path)
        src_file = os.path.basename(src_path)
        if src_dir:
            main_lines.append(f"源目录：{src_dir}")
        if src_file:
            main_lines.append(f"文件名：{src_file}")
    main = "\n".join(main_lines)
    highlight = "\n".join(rep_lines) if rep_lines else ""
    return (main, highlight)


def _ctk_readonly_text_set(widget: Any, text: str) -> None:
    """将 ``CTkTextbox`` 设为只读并替换全文（按控件宽度自动换行，避免与右侧工具条重叠）。"""
    try:
        widget.configure(state="normal")
        widget.delete("1.0", "end")
        widget.insert("1.0", text)
        widget.configure(state="disabled")
    except Exception:
        pass


def _timeline_status_set_text(widget: Any, text: str, *, ctk_mod: Any) -> None:
    """时间轴说明区：支持 ``CTkTextbox`` 与旧版 ``CTkLabel``。"""
    if widget is None:
        return
    try:
        if isinstance(widget, ctk_mod.CTkTextbox):
            _ctk_readonly_text_set(widget, text)
        else:
            widget.configure(text=text)
    except Exception:
        pass


def populate_timeline_panel(
    parent: Any,
    content: Optional[Dict[str, Any]],
    *,
    selection: Optional[Dict[str, Any]] = None,
    status_label: Any = None,
    status_replace_highlight_label: Any = None,
    replace_state: Optional[Dict[str, Any]] = None,
    pixels_per_second: float = 68.0,
    wheel_zoom_step: Optional[Any] = None,
) -> None:
    """在 parent（CTkFrame）内绘制类剪映的横向时间轴：轨道按层级排序，片段按时间排序；可点击选择轨道或片段。"""
    import customtkinter as ctk_mod

    for w in parent.winfo_children():
        w.destroy()

    sel = selection if selection is not None else {"kind": "none", "ti": None, "si": None, "summary": ""}
    rs = replace_state if replace_state is not None else {}
    if isinstance(content, dict):
        try:
            rs["style_refs"] = list_style_segments_from_content(content)
        except Exception:
            pass

    def _set_status(text: str, *, replace_highlight: str = "") -> None:
        sel["summary"] = text + (f"\n\n{replace_highlight}" if replace_highlight else "")
        _timeline_status_set_text(status_label, text, ctk_mod=ctk_mod)
        _timeline_status_set_text(status_replace_highlight_label, replace_highlight, ctk_mod=ctk_mod)

    if not content:
        ctk_mod.CTkLabel(parent, text="（无明文草稿，无法显示时间轴）", text_color=("gray45", "gray60")).pack(
            pady=16, padx=12
        )
        _set_status("—", replace_highlight="")
        return

    tracks_raw = list(content.get("tracks") or [])
    if not tracks_raw:
        ctk_mod.CTkLabel(parent, text="（无轨道）", text_color=("gray45", "gray60")).pack(pady=16, padx=12)
        _set_status("—", replace_highlight="")
        return

    # 高 render_index 在上（前景），低在下（主轨常见）
    tracks_sorted = sorted(tracks_raw, key=_track_render_index, reverse=True)
    materials = content.get("materials") if isinstance(content.get("materials"), dict) else {}
    mat_kind_by_id = _build_material_kind_index(materials)

    total_us = _timeline_end_us(content)
    total_sec = total_us / 1_000_000.0
    time_px = max(int(total_sec * pixels_per_second), 280)
    label_w = _TIMELINE_LABEL_W
    ruler_h = 28
    row_h = 34
    row_gap = 5
    pad = _TIMELINE_PAD
    canvas_w = label_w + time_px + pad * 2
    canvas_h = ruler_h + len(tracks_sorted) * (row_h + row_gap) + pad

    bg = "#252526"
    ruler_bg = "#2d2d2d"
    label_bg = "#2f2f32"
    colors = {
        "video": ("#2f5f8f", "#8cc8ff"),
        "audio": ("#2f6f4f", "#8ceeb0"),
        "text": ("#6a6220", "#eee08c"),
        "sticker": ("#5a3d7a", "#d4b0ff"),
        "effect": ("#555555", "#cccccc"),
        "filter": ("#555555", "#cccccc"),
    }

    shell = tk.Frame(parent, bg=bg, highlightthickness=0)
    shell.pack(fill="both", expand=True)

    def _viewport_height() -> int:
        try:
            parent.update_idletasks()
            ph = int(parent.winfo_height())
        except (tk.TclError, ValueError, TypeError):
            ph = 0
        pad = 10
        avail = max(120, ph - pad) if ph >= 48 else 320
        # 内容矮时用内容高度；内容高时用可用高度并配合纵向滚动
        return min(max(canvas_h, 120), avail) if canvas_h <= avail else max(120, avail)

    view_h = _viewport_height()
    need_vscroll = canvas_h > view_h

    body = tk.Frame(shell, bg=bg, highlightthickness=0)
    body.pack(fill="both", expand=True)

    canvas = tk.Canvas(
        body,
        bg=bg,
        highlightthickness=0,
        scrollregion=(0, 0, canvas_w, canvas_h),
        height=view_h,
        width=860,
        takefocus=True,
    )
    if need_vscroll:
        vbar = tk.Scrollbar(body, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vbar.set)
        vbar.pack(side="right", fill="y")
    canvas.pack(side="left", fill="both", expand=True)

    _last_fit_vh: List[int] = [-1]

    def _fit_timeline_canvas(_event: Optional[tk.Event] = None) -> None:
        try:
            parent.update_idletasks()
            ph = int(parent.winfo_height())
        except (tk.TclError, ValueError, TypeError):
            return
        if ph < 48:
            return
        pad = 10
        avail = max(120, ph - pad)
        vh = min(max(canvas_h, 120), avail) if canvas_h <= avail else max(120, avail)
        if vh == _last_fit_vh[0]:
            return
        _last_fit_vh[0] = vh
        try:
            canvas.configure(height=vh)
            canvas.configure(scrollregion=(0, 0, canvas_w, canvas_h))
        except tk.TclError:
            pass

    parent.bind("<Configure>", _fit_timeline_canvas, add="+")
    parent.after_idle(_fit_timeline_canvas)

    if wheel_zoom_step is not None and content:
        _wz_last: List[int] = [0]

        def _vertical_scroll_needed() -> bool:
            """轨道总高度超过画布可视高度时可纵向滚动（右侧滚动条 + 滚轮）。"""
            try:
                sr = canvas.cget("scrollregion")
                parts = sr.split()
                if len(parts) >= 4:
                    total_h = int(float(parts[3]))
                    ch = int(canvas.winfo_height())
                    return total_h > ch + 2
            except (tk.TclError, ValueError, TypeError):
                pass
            return False

        def _wheel_zoom_handler(event: Any) -> str:
            try:
                st = int(event.state)
            except (TypeError, ValueError, tk.TclError):
                st = 0
            if (st & 0x4) != 0:
                now = int(time.time() * 1000)
                if now - _wz_last[0] < 35:
                    return "break"
                _wz_last[0] = now
                delta = getattr(event, "delta", 0)
                if sys.platform == "darwin":
                    steps = -1 if delta > 0 else 1
                else:
                    steps = 1 if delta > 0 else -1
                try:
                    wheel_zoom_step(steps)
                except Exception:
                    pass
                return "break"
            if _vertical_scroll_needed():
                delta = getattr(event, "delta", 0)
                if delta:
                    try:
                        canvas.yview_scroll(int(-delta / 120), "units")
                    except tk.TclError:
                        pass
                return "break"
            return ""

        def _wheel_linux_up(_event: Any) -> str:
            try:
                st = int(_event.state)
            except (TypeError, ValueError, tk.TclError):
                st = 0
            if (st & 0x4) != 0:
                try:
                    wheel_zoom_step(1)
                except Exception:
                    pass
                return "break"
            if _vertical_scroll_needed():
                try:
                    canvas.yview_scroll(-3, "units")
                except tk.TclError:
                    pass
                return "break"
            return ""

        def _wheel_linux_down(_event: Any) -> str:
            try:
                st = int(_event.state)
            except (TypeError, ValueError, tk.TclError):
                st = 0
            if (st & 0x4) != 0:
                try:
                    wheel_zoom_step(-1)
                except Exception:
                    pass
                return "break"
            if _vertical_scroll_needed():
                try:
                    canvas.yview_scroll(3, "units")
                except tk.TclError:
                    pass
                return "break"
            return ""

        canvas.bind("<MouseWheel>", _wheel_zoom_handler)
        canvas.bind("<Button-4>", _wheel_linux_up)
        canvas.bind("<Button-5>", _wheel_linux_down)

    hbar = tk.Scrollbar(shell, orient="horizontal", command=canvas.xview)
    canvas.configure(xscrollcommand=hbar.set)
    hbar.pack(side="bottom", fill="x")

    label_rect_ids: Dict[int, int] = {}
    seg_rect_ids: Dict[Tuple[int, int], int] = {}
    # 同轨重叠片段时，后绘制的在上层 —— 拖放命中取 paint 序最大者
    seg_hit_z: Dict[Tuple[int, int], int] = {}
    seg_paint_counter: List[int] = [0]
    # 每轨按时间排序的可见片段 (vis_i, orig_i)，供方向键左右与上下（按条序对齐）
    track_visible_segs: Dict[int, List[Tuple[int, int]]] = {}

    def _x_for_us(us: int) -> float:
        return label_w + pad + (us / total_us) * time_px

    def apply_selection_visual() -> None:
        for ti, rid in label_rect_ids.items():
            canvas.itemconfig(rid, outline="#555", width=1)
        for key, rid in seg_rect_ids.items():
            canvas.itemconfig(rid, outline="#141414", width=1)
        k = sel.get("kind", "none")
        if k == "track" and sel.get("ti") is not None:
            ti = int(sel["ti"])
            if ti in label_rect_ids:
                canvas.itemconfig(label_rect_ids[ti], outline="#e8c547", width=2)
        elif k == "seg" and sel.get("ti") is not None and sel.get("orig_i") is not None:
            ti = int(sel["ti"])
            oi = int(sel["orig_i"])
            if (ti, oi) in seg_rect_ids:
                canvas.itemconfig(seg_rect_ids[(ti, oi)], outline="#e8c547", width=3)
            if ti in label_rect_ids:
                canvas.itemconfig(label_rect_ids[ti], outline="#777", width=1)

    def _notify_timeline_selection_ui() -> None:
        cb = rs.get("_on_timeline_selection_ui")
        if callable(cb):
            try:
                cb()
            except Exception:
                pass

    def on_select_track(ti: int) -> None:
        tr = tracks_sorted[ti]
        nseg = len(tr.get("segments") or [])
        sel["kind"] = "track"
        sel["ti"] = ti
        sel["si"] = None
        sel.pop("orig_i", None)
        sel.pop("vis_i", None)
        sel.pop("replace_ref", None)
        sel.pop("style_ref", None)
        ttype = str(tr.get("type", "")).strip().lower()
        if ttype in ("text", "sticker") and isinstance(content, dict):
            track_refs = list_style_segment_refs_for_track(content, tr)
            if track_refs:
                sel["track_style_refs"] = track_refs
            else:
                sel.pop("track_style_refs", None)
        else:
            sel.pop("track_style_refs", None)
        nm_raw = tr.get("name", "")
        tname = "" if nm_raw is None else (nm_raw if isinstance(nm_raw, str) else str(nm_raw))
        tname = tname.strip()
        sel["track_summary"] = f"{tname or ttype} [{ttype}] · 共 {nseg} 个片段"
        _set_status(f"已选轨道：{tr.get('name')} [{tr.get('type')}] · 共 {nseg} 个片段", replace_highlight="")
        apply_selection_visual()
        _notify_timeline_selection_ui()

    def on_select_seg(ti: int, vis_i: int, orig_i: int) -> None:
        tr = tracks_sorted[ti]
        sel["kind"] = "seg"
        sel["ti"] = ti
        sel["vis_i"] = vis_i
        sel["orig_i"] = orig_i
        sel.pop("track_style_refs", None)
        sel.pop("track_summary", None)
        refs_list = rs.get("refs") or []
        ref = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i, content)
        if ref is not None:
            sel["replace_ref"] = ref
        else:
            sel.pop("replace_ref", None)
        style_refs_list = rs.get("style_refs") or []
        style_ref = find_style_ref_for_timeline_segment(style_refs_list, tr, orig_i, content)
        if style_ref is not None:
            sel["style_ref"] = style_ref
        else:
            sel.pop("style_ref", None)
        apply_selection_visual()
        content_for_status: Dict[str, Any] = content if isinstance(content, dict) else {}
        try:
            parts = timeline_segment_selection_status_parts(
                content_for_status, ti=ti, vis_i=vis_i, orig_i=orig_i, replace_state=rs
            )
            if parts is not None:
                _set_status(parts[0], replace_highlight=parts[1])
        except Exception:
            pass
        _notify_timeline_selection_ui()

    def on_seg_context_menu(event: Any, ti: int, vis_i: int, orig_i: int) -> None:
        from tkinter import Menu

        tr = tracks_sorted[ti]
        refs_list = rs.get("refs") or []
        ref = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i, content)
        style_refs_list = rs.get("style_refs") or []
        style_ref = find_style_ref_for_timeline_segment(style_refs_list, tr, orig_i, content)
        m = Menu(canvas, tearoff=0, bg="#2b2b2b", fg="#e0e0e0", activebackground="#3d3d3d")

        def _open_replace_win() -> None:
            if not ref:
                return
            on_select_seg(ti, vis_i, orig_i)
            od = rs.get("_open_replace_dialog")
            if callable(od):
                od(ref)

        def _open_style_win() -> None:
            if not style_ref:
                return
            on_select_seg(ti, vis_i, orig_i)
            od = rs.get("_open_style_dialog")
            if callable(od):
                od(style_ref)

        draft_nm = (rs.get("timeline_draft_name") or "").strip()
        pool_ui = rs.get("segment_export_pool") or {}
        has_material_cfg = bool(ref and segment_has_replace_config(draft_nm, ref, pool_ui))
        has_style_cfg = bool(style_ref and segment_has_style_config(draft_nm, style_ref, pool_ui))

        def _clear_seg_config() -> None:
            on_select_seg(ti, vis_i, orig_i)
            if has_material_cfg and ref:
                cb = rs.get("_clear_material_config")
                if callable(cb):
                    cb(ref)
            elif has_style_cfg and style_ref:
                cb = rs.get("_clear_style_config")
                if callable(cb):
                    cb(style_ref)

        if ref:
            m.add_command(label="替换素材…", command=_open_replace_win)
        elif style_ref:
            label = "替换花字…" if style_ref.track_type == "text" else "替换贴纸…"
            m.add_command(label=label, command=_open_style_win)
        else:
            m.add_command(label="（此片段不可配置替换）", state="disabled")
        if has_material_cfg or has_style_cfg:
            m.add_command(label="清除配置", command=_clear_seg_config)
        try:
            m.tk_popup(int(event.x_root), int(event.y_root))
        finally:
            try:
                m.grab_release()
            except Exception:
                pass

    # 标尺
    canvas.create_rectangle(0, 0, canvas_w, ruler_h, fill=ruler_bg, outline="")
    canvas.create_line(label_w, 0, label_w, canvas_h, fill="#555", width=1)
    step_us = _timeline_ruler_step_us(total_us)
    t = 0
    while t <= total_us:
        x = _x_for_us(t)
        sec = t // 1_000_000
        is_major = (t % 5_000_000 == 0) or sec == 0
        canvas.create_line(x, ruler_h - (18 if is_major else 10), x, ruler_h, fill="#777", width=1)
        if is_major or sec == 0:
            canvas.create_text(
                x + 3,
                ruler_h // 2,
                text=f"{sec}s",
                fill="#bbb",
                anchor="w",
                font=("Segoe UI", 9),
            )
        t += step_us

    y0 = ruler_h + row_gap
    for ti, tr in enumerate(tracks_sorted):
        track_visible_segs[ti] = []
        y = y0 + ti * (row_h + row_gap)
        tname = str(tr.get("name", "?"))
        ttype = str(tr.get("type", "?"))
        label_txt = f"{tname}\n[{ttype}]"
        tag_t = f"tid{ti}"
        lr = canvas.create_rectangle(
            0,
            y,
            label_w,
            y + row_h,
            fill=label_bg,
            outline="#555",
            width=1,
            tags=("ttrack", tag_t),
        )
        label_rect_ids[ti] = lr
        canvas.create_text(
            6,
            y + row_h // 2,
            text=label_txt[:40],
            fill="#ddd",
            anchor="w",
            font=("Segoe UI", 9),
            tags=("ttrack", tag_t),
        )
        canvas.tag_bind(tag_t, "<Button-1>", lambda _e, idx=ti: on_select_track(idx))
        canvas.tag_bind(tag_t, "<Enter>", lambda _e: canvas.configure(cursor="hand2"))
        canvas.tag_bind(tag_t, "<Leave>", lambda _e: canvas.configure(cursor=""))

        raw_segs = list(tr.get("segments") or [])
        order = sorted(
            range(len(raw_segs)),
            key=lambda i: int((raw_segs[i].get("target_timerange") or {}).get("start", 0)),
        )

        fill_c, text_c = colors.get(ttype, ("#4a4a4a", "#e0e0e0"))
        draft_nm = (rs.get("timeline_draft_name") or "").strip()
        pool_ui: Dict[str, Any] = rs.get("segment_export_pool") or {}
        if not isinstance(pool_ui, dict):
            pool_ui = {}
        refs_list = rs.get("refs") or []
        for vis_i, orig_i in enumerate(order):
            seg = raw_segs[orig_i]
            trng = seg.get("target_timerange") or {}
            try:
                st = int(trng.get("start", 0))
                du = int(trng.get("duration", 0))
            except (TypeError, ValueError):
                continue
            if du <= 0:
                continue
            x1 = _x_for_us(st)
            x2 = _x_for_us(st + du)
            bar_w = x2 - x1
            min_bar = max(4.0, min(10.0, bar_w))
            if bar_w < min_bar:
                x2 = x1 + min_bar
                bar_w = min_bar
            tag_s = f"sid{ti}_{orig_i}"
            seg_fill, seg_text = fill_c, text_c
            has_fx = _segment_has_timeline_fx(seg, mat_kind_by_id)
            if has_fx and ttype in ("text", "sticker"):
                seg_fill, seg_text = ("#7a4a18", "#ffe8b0")
            elif has_fx and ttype == "video":
                seg_fill, seg_text = ("#4a3a7a", "#dcc8ff")
            r_here = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i, content)
            style_here = find_style_ref_for_timeline_segment(
                rs.get("style_refs") or [], tr, orig_i, content
            )
            if draft_nm and (
                segment_has_replace_config(draft_nm, r_here, pool_ui)
                or segment_has_style_config(draft_nm, style_here, pool_ui)
            ):
                seg_fill, seg_text = ("#257a42", "#d4ffe3")
            rid = canvas.create_rectangle(
                x1,
                y + 2,
                x2,
                y + row_h - 2,
                fill=seg_fill,
                outline="#141414",
                width=1,
                tags=("sseg", tag_s),
            )
            seg_rect_ids[(ti, orig_i)] = rid
            seg_hit_z[(ti, orig_i)] = seg_paint_counter[0]
            seg_paint_counter[0] += 1
            track_visible_segs[ti].append((vis_i, orig_i))
            lab = _timeline_segment_label(seg, materials)
            idx_label = f"#{vis_i + 1}"
            if has_fx:
                idx_label = f"{idx_label} FX"
            title = f"{idx_label} {lab}"
            if bar_w > 28:
                canvas.create_text(
                    x1 + 4,
                    y + row_h // 2,
                    text=title[:28] + ("…" if len(title) > 28 else ""),
                    fill=seg_text,
                    anchor="w",
                    font=("Segoe UI", 8),
                    tags=("sseg", tag_s),
                )
            elif bar_w > 8:
                canvas.create_text(
                    (x1 + x2) / 2,
                    y + row_h // 2,
                    text=idx_label,
                    fill=seg_text,
                    font=("Segoe UI", 7),
                    tags=("sseg", tag_s),
                )
            if has_fx:
                canvas.create_rectangle(
                    x1,
                    y + row_h - 7,
                    x2,
                    y + row_h - 2,
                    fill="#ff9933",
                    outline="",
                    tags=("sseg", tag_s),
                )
            canvas.tag_bind(
                tag_s, "<Button-1>", lambda _e, a=ti, vi=vis_i, oi=orig_i: on_select_seg(a, vi, oi)
            )
            canvas.tag_bind(
                tag_s,
                "<Button-3>",
                lambda e, a=ti, vi=vis_i, oi=orig_i: on_seg_context_menu(e, a, vi, oi),
            )
            canvas.tag_bind(tag_s, "<Enter>", lambda _e: canvas.configure(cursor="hand2"))
            canvas.tag_bind(tag_s, "<Leave>", lambda _e: canvas.configure(cursor=""))

    playhead_us = max(0, min(int(sel.get("playhead_us") or rs.get("playhead_us") or 0), total_us))
    sel["playhead_us"] = playhead_us
    rs["playhead_us"] = playhead_us
    playhead_ids: List[int] = []
    _scrubbing = [False]
    rs["_playhead_scrubbing"] = _scrubbing

    def _us_from_canvas_x(cx: float) -> int:
        x_time = cx - label_w - pad
        if time_px <= 0:
            return 0
        frac = max(0.0, min(1.0, x_time / float(time_px)))
        return int(frac * total_us)

    def _draw_playhead() -> None:
        x = _x_for_us(playhead_us)
        if len(playhead_ids) >= 2:
            try:
                canvas.coords(playhead_ids[0], x, 0, x, canvas_h)
                canvas.coords(playhead_ids[1], x - 6, 0, x + 6, 0, x, 10)
                canvas.tag_raise("playhead")
                return
            except tk.TclError:
                pass
        for iid in playhead_ids:
            try:
                canvas.delete(iid)
            except tk.TclError:
                pass
        playhead_ids.clear()
        lh = canvas.create_line(x, 0, x, canvas_h, fill="#ff4444", width=2, tags=("playhead",))
        tri = canvas.create_polygon(
            x - 6, 0, x + 6, 0, x, 10, fill="#ff4444", outline="#aa2222", tags=("playhead",)
        )
        playhead_ids.extend([lh, tri])
        try:
            canvas.tag_raise("playhead")
        except tk.TclError:
            pass

    def _set_playhead(us: int, *, notify: bool = True, redraw: bool = True) -> None:
        nonlocal playhead_us
        playhead_us = max(0, min(int(us), total_us))
        sel["playhead_us"] = playhead_us
        rs["playhead_us"] = playhead_us
        if redraw:
            _draw_playhead()
        if notify:
            cb = rs.get("_on_playhead_change")
            if callable(cb):
                try:
                    cb(playhead_us)
                except Exception:
                    pass

    rs["_set_playhead"] = _set_playhead

    def _event_hits_segment(event: tk.Event) -> bool:
        try:
            cx = float(canvas.canvasx(event.x))
            cy = float(canvas.canvasy(event.y))
            hits = canvas.find_overlapping(cx - 2, cy - 2, cx + 2, cy + 2)
            for iid in hits:
                if "sseg" in canvas.gettags(iid):
                    return True
        except tk.TclError:
            pass
        return False

    def _on_playhead_press(event: tk.Event) -> Optional[str]:
        try:
            cx = float(canvas.canvasx(event.x))
        except (TypeError, ValueError, tk.TclError):
            return None
        if cx < label_w:
            return None
        if _event_hits_segment(event):
            return None
        stop_play = rs.get("_stop_preview_playback")
        if callable(stop_play):
            try:
                stop_play()
            except Exception:
                pass
        _scrubbing[0] = True
        _set_playhead(_us_from_canvas_x(cx))
        return None

    def _on_playhead_motion(event: tk.Event) -> Optional[str]:
        if not _scrubbing[0]:
            return None
        try:
            cx = float(canvas.canvasx(event.x))
        except (TypeError, ValueError, tk.TclError):
            return None
        if cx < label_w:
            cx = float(label_w)
        _set_playhead(_us_from_canvas_x(cx))
        return "break"

    def _on_playhead_release(_event: tk.Event) -> None:
        _scrubbing[0] = False
        kick = rs.get("_on_playhead_preview_flush")
        if callable(kick):
            try:
                kick(int(playhead_us))
            except Exception:
                pass

    _draw_playhead()
    canvas.bind("<Button-1>", _on_playhead_press, add="+")
    canvas.bind("<B1-Motion>", _on_playhead_motion, add="+")
    canvas.bind("<ButtonRelease-1>", _on_playhead_release, add="+")

    def _timeline_canvas_vscrolls() -> bool:
        try:
            sr = canvas.cget("scrollregion")
            parts = sr.split()
            if len(parts) >= 4:
                total_h = int(float(parts[3]))
                ch = int(canvas.winfo_height())
                return total_h > ch + 2
        except (tk.TclError, ValueError, TypeError):
            pass
        return False

    def _timeline_focus_canvas(_event: Optional[tk.Event] = None) -> None:
        try:
            canvas.focus_set()
        except tk.TclError:
            pass

    shell.bind("<Button-1>", _timeline_focus_canvas, add="+")
    hbar.bind("<Button-1>", _timeline_focus_canvas, add="+")
    canvas.bind("<Button-1>", _timeline_focus_canvas, add="+")
    if need_vscroll:
        try:
            vbar.bind("<Button-1>", _timeline_focus_canvas, add="+")
        except tk.TclError:
            pass

    def _scroll_seg_into_view(ti_v: int, orig_v: int) -> None:
        key_v = (ti_v, orig_v)
        if key_v not in seg_rect_ids:
            return
        bb = canvas.bbox(seg_rect_ids[key_v])
        if not bb or len(bb) < 4:
            return
        x1, _y1, x2, _y2 = float(bb[0]), float(bb[1]), float(bb[2]), float(bb[3])
        try:
            w = max(1, int(canvas.winfo_width()))
        except tk.TclError:
            return
        margin = 48.0
        total = float(max(1, canvas_w))
        cleft = float(canvas.canvasx(0))
        cright = float(canvas.canvasx(w))
        if x1 < cleft + margin:
            fr = max(0.0, min(1.0, (x1 - margin) / total))
            try:
                canvas.xview_moveto(fr)
            except tk.TclError:
                pass
        elif x2 > cright - margin:
            fr = max(0.0, min(1.0, (x2 - float(w) + margin) / total))
            try:
                canvas.xview_moveto(fr)
            except tk.TclError:
                pass

    def _scroll_seg_left_edge_into_view(ti_v: int, orig_v: int) -> None:
        """上下换轨时横向滚到当前片段矩形左缘（时间轴上素材起点一侧），与 _scroll_seg_into_view 的保守滚动不同。"""
        key_v = (ti_v, orig_v)
        if key_v not in seg_rect_ids:
            return
        bb = canvas.bbox(seg_rect_ids[key_v])
        if not bb or len(bb) < 4:
            return
        x1 = float(bb[0])
        margin = 8.0
        total = float(max(1, canvas_w))
        fr = max(0.0, min(1.0, (x1 - margin) / total))
        try:
            canvas.xview_moveto(fr)
        except tk.TclError:
            pass

    def _scroll_track_row_into_view(ti_v: int) -> None:
        if not _timeline_canvas_vscrolls():
            return
        try:
            total_h = float(canvas_h)
            ch = max(1, int(canvas.winfo_height()))
        except tk.TclError:
            return
        y_row = float(ruler_h + row_gap + ti_v * (row_h + row_gap))
        y_bot = y_row + float(row_h)
        try:
            top_frac, bot_frac = canvas.yview()
        except tk.TclError:
            return
        vis_top = top_frac * total_h
        vis_bot = bot_frac * total_h
        margin = 8.0
        if y_row < vis_top + margin:
            fr = max(0.0, (y_row - margin) / max(1.0, total_h))
            try:
                canvas.yview_moveto(fr)
            except tk.TclError:
                pass
        elif y_bot > vis_bot - margin:
            span = max(1.0, total_h - ch)
            fr = max(0.0, min(1.0, (y_bot - float(ch) + margin) / span))
            try:
                canvas.yview_moveto(fr)
            except tk.TclError:
                pass

    def on_timeline_arrow_key(event: Any) -> str:
        ks = str(getattr(event, "keysym", "") or "")
        if ks not in ("Up", "Down", "Left", "Right"):
            return ""
        ntr = len(tracks_sorted)
        if ntr <= 0:
            return "break"

        def _first_nonempty_seg() -> Optional[Tuple[int, int, int]]:
            for ti_a in range(ntr):
                lst_a = track_visible_segs.get(ti_a) or []
                if lst_a:
                    v0, o0 = lst_a[0]
                    return (ti_a, v0, o0)
            return None

        def _last_nonempty_seg() -> Optional[Tuple[int, int, int]]:
            for ti_a in range(ntr - 1, -1, -1):
                lst_a = track_visible_segs.get(ti_a) or []
                if lst_a:
                    v0, o0 = lst_a[-1]
                    return (ti_a, v0, o0)
            return None

        knd = str(sel.get("kind", "none") or "none")
        if knd == "none":
            hit = _first_nonempty_seg() if ks in ("Down", "Right") else _last_nonempty_seg()
            if hit:
                on_select_seg(hit[0], hit[1], hit[2])
                _scroll_seg_into_view(hit[0], hit[2])
            else:
                ti0 = 0 if ks in ("Down", "Right") else max(0, ntr - 1)
                on_select_track(ti0)
                _scroll_track_row_into_view(ti0)
            return "break"

        if knd == "track":
            try:
                ti = int(sel.get("ti", 0))
            except (TypeError, ValueError):
                ti = 0
            ti = max(0, min(ntr - 1, ti))
            if ks == "Up":
                if ti > 0:
                    on_select_track(ti - 1)
                    _scroll_track_row_into_view(ti - 1)
            elif ks == "Down":
                if ti + 1 < ntr:
                    on_select_track(ti + 1)
                    _scroll_track_row_into_view(ti + 1)
            elif ks == "Right":
                lst = track_visible_segs.get(ti) or []
                if lst:
                    v0, o0 = lst[0]
                    on_select_seg(ti, v0, o0)
                    _scroll_seg_into_view(ti, o0)
            elif ks == "Left":
                lst = track_visible_segs.get(ti) or []
                if lst:
                    v0, o0 = lst[-1]
                    on_select_seg(ti, v0, o0)
                    _scroll_seg_into_view(ti, o0)
            return "break"

        if knd == "seg":
            try:
                ti = int(sel.get("ti", 0))
                oi = int(sel.get("orig_i", 0))
                vi = int(sel.get("vis_i", 0))
            except (TypeError, ValueError):
                return "break"
            ti = max(0, min(ntr - 1, ti))
            lst = track_visible_segs.get(ti) or []
            idx: Optional[int] = None
            for j, pair in enumerate(lst):
                if pair == (vi, oi):
                    idx = j
                    break
            if idx is None and lst:
                idx = 0
                vi, oi = lst[0]
            if ks in ("Left", "Right") and lst and idx is not None:
                if ks == "Left" and idx > 0:
                    v2, o2 = lst[idx - 1]
                    on_select_seg(ti, v2, o2)
                    _scroll_seg_into_view(ti, o2)
                elif ks == "Right" and idx + 1 < len(lst):
                    v2, o2 = lst[idx + 1]
                    on_select_seg(ti, v2, o2)
                    _scroll_seg_into_view(ti, o2)
            elif ks in ("Up", "Down"):
                if ks == "Up" and ti > 0:
                    nt = ti - 1
                elif ks == "Down" and ti + 1 < ntr:
                    nt = ti + 1
                else:
                    return "break"
                lst_tgt = track_visible_segs.get(nt) or []
                if not lst_tgt:
                    on_select_track(nt)
                    _scroll_track_row_into_view(nt)
                    return "break"
                # 与当前轨「从左数第几条可见片段」对齐，目标轨更短时落在最后一条
                col = int(idx if idx is not None else 0)
                col = max(0, min(col, len(lst_tgt) - 1))
                v2, o2 = lst_tgt[col]
                on_select_seg(nt, v2, o2)
                _scroll_seg_left_edge_into_view(nt, o2)
            return "break"

        return "break"

    for _keyseq in ("<Up>", "<Down>", "<Left>", "<Right>"):
        canvas.bind(_keyseq, on_timeline_arrow_key)

    apply_selection_visual()
    if sel.get("kind") == "seg" and sel.get("ti") is not None and sel.get("orig_i") is not None:
        try:
            ti_rs = int(sel["ti"])
            oi_rs = int(sel["orig_i"])
            vi_rs = int(sel.get("vis_i", 0))
            if 0 <= ti_rs < len(tracks_sorted):
                on_select_seg(ti_rs, vi_rs, oi_rs)
        except (TypeError, ValueError):
            pass
    elif sel.get("kind") == "none":
        _set_status(
            "提示：点击左侧轨道名选中轨道；点击彩色条选中片段；"
            "音视频可右键「替换素材…」；字幕/贴纸可点轨道名选中整轨后点「替换…」，或点片段右键配置花字/贴纸"
            "（Windows 下也可将单个文件或素材文件夹从资源管理器拖到片段条上，与弹窗保存一致）。"
            " 时间轴区域点一下后可用方向键：左右切换同轨片段，上下换轨（保持同序）且横滚对齐片段左缘；"
            "轨道多时可滚轮上下浏览或拖右侧竖条；Ctrl+滚轮或标题栏「+/−」横向缩放；"
            "点击或拖动顶部标尺、轨道空白处或红色播放头，可定位并预览对应画面。",
            replace_highlight="",
        )

    if sys.platform == "win32":
        try:
            import windnd  # type: ignore[import-untyped]
        except Exception:
            windnd = None  # type: ignore[assignment]
        if windnd is not None:

            def _decode_shell_path(p: Any) -> str:
                if isinstance(p, bytes):
                    for enc in ("utf-8", sys.getfilesystemencoding() or "utf-8", "gbk"):
                        try:
                            return p.decode(enc).strip("\0").strip()
                        except UnicodeDecodeError:
                            continue
                    return p.decode("utf-8", errors="replace").strip("\0").strip()
                return str(p).strip("\0").strip()

            def _vis_index_for_segment(ti2: int, orig_i2: int) -> int:
                tr2 = tracks_sorted[ti2]
                raw2 = list(tr2.get("segments") or [])
                order2 = sorted(
                    range(len(raw2)),
                    key=lambda i: int((raw2[i].get("target_timerange") or {}).get("start", 0)),
                )
                try:
                    return order2.index(orig_i2)
                except ValueError:
                    return 0

            def _timeline_hit_segment(cx: float, cy: float) -> Optional[Tuple[int, int]]:
                if not seg_rect_ids:
                    return None
                hits: List[Tuple[int, int, int]] = []
                for (ti2, oi2), rid in seg_rect_ids.items():
                    bb = canvas.bbox(rid)
                    if not bb or len(bb) < 4:
                        continue
                    x1, y1, x2, y2 = float(bb[0]), float(bb[1]), float(bb[2]), float(bb[3])
                    if x1 <= cx <= x2 and y1 <= cy <= y2:
                        z = int(seg_hit_z.get((ti2, oi2), 0))
                        hits.append((z, ti2, oi2))
                if not hits:
                    return None
                hits.sort(key=lambda t: (t[0], t[1], t[2]))
                return (hits[-1][1], hits[-1][2])

            def _on_windnd_drop(paths_raw: Any) -> None:
                ls = paths_raw if isinstance(paths_raw, (list, tuple)) else []
                paths: List[str] = []
                for x in ls:
                    s = _decode_shell_path(x)
                    if s:
                        paths.append(os.path.normpath(s))
                if not paths:
                    return
                try:
                    px = int(canvas.winfo_pointerx())
                    py = int(canvas.winfo_pointery())
                    rx = int(canvas.winfo_rootx())
                    ry = int(canvas.winfo_rooty())
                except tk.TclError:
                    return
                cx = float(canvas.canvasx(px - rx))
                cy = float(canvas.canvasy(py - ry))
                hit = _timeline_hit_segment(cx, cy)
                h = rs.get("_timeline_shell_drop_handler")
                if not callable(h):
                    return
                if hit is None:
                    h(None, paths)
                    return
                ti2, oi2 = hit
                vi2 = _vis_index_for_segment(ti2, oi2)
                try:
                    on_select_seg(ti2, vi2, oi2)
                except Exception:
                    pass
                h(sel.get("replace_ref"), paths)

            try:
                windnd.hook_dropfiles(canvas, _on_windnd_drop, force_unicode=True)
            except Exception:
                pass

    canvas.configure(scrollregion=(0, 0, canvas_w, canvas_h))


def run_app() -> None:
    try:
        import customtkinter as ctk
    except ImportError:
        print("请先安装: pip install customtkinter", file=sys.stderr)
        sys.exit(1)

    ctk.set_appearance_mode("dark")
    ctk.set_default_color_theme("dark-blue")

    root = ctk.CTk()
    root.title("爆款智剪")
    win_w, win_h = 1320, 680
    root.minsize(920, 480)
    root.geometry(f"{win_w}x{win_h}")
    root.update_idletasks()
    _center_window_on_screen(root, win_w, win_h)
    threading.Thread(target=_cleanup_stale_preview_merge_cache, daemon=True, name="preview-cache-cleanup").start()

    _ensure_local_pyjianyingdraft_on_path()
    auth_client: Any = None
    _auth_api_error_message: Any = None
    try:
        from shared.browser_auth_client import BrowserAuthClient as _BAC
        from shared.browser_auth_client import auth_api_error_message as _auth_api_error_message

        auth_client = _BAC()
    except ImportError:
        auth_client = None
        _auth_api_error_message = None

    top_bar = ctk.CTkFrame(root, fg_color="transparent")
    top_bar.pack(fill="x", padx=12, pady=(4, 0))
    auth_status_var = ctk.StringVar(value="未登录（导出 MP4 需登录）")

    def open_auth_dialog(*, mandatory: bool = False) -> bool:
        """打开登录对话框。mandatory=True 时模态阻塞，主窗在背后且无法操作；取消或关窗返回 False。成功登录返回 True。"""
        from tkinter import messagebox

        if not auth_client:
            messagebox.showerror("登录", "认证模块不可用（请从仓库根目录运行，并 pip install requests）。")
            return False
        win = ctk.CTkToplevel(root)
        win.title("登录 - 爆款智剪" if mandatory else "登录 / 注册")
        win.transient(root)
        win.resizable(False, False)
        dlg_w, dlg_h = 400, 380 if mandatory else 360
        win.geometry(f"{dlg_w}x{dlg_h}")
        mode_var = ctk.StringVar(value="login")

        ctk.CTkLabel(win, text="账号", anchor="w").pack(fill="x", padx=20, pady=(18, 4))
        user_e = ctk.CTkEntry(win, placeholder_text="用户名", height=34)
        user_e.pack(fill="x", padx=20)
        ctk.CTkLabel(win, text="密码", anchor="w").pack(fill="x", padx=20, pady=(12, 4))
        pwd_e = ctk.CTkEntry(win, placeholder_text="密码", height=34, show="*")
        pwd_e.pack(fill="x", padx=20)
        remember_var = ctk.BooleanVar(value=True)
        ctk.CTkCheckBox(win, text="记住账号密码（本地加密存储）", variable=remember_var).pack(anchor="w", padx=20, pady=(14, 8))
        hint = ctk.CTkLabel(win, text="", text_color=("gray40", "gray65"), font=ctk.CTkFont(size=11))
        hint.pack(pady=(0, 6))

        def apply_mode() -> None:
            m = mode_var.get()
            hint.configure(text="使用 leiyuantech 账号登录" if m == "login" else "注册新账号（成功后自动登录）")

        row = ctk.CTkFrame(win, fg_color="transparent")
        row.pack(fill="x", padx=20, pady=(4, 0))
        ctk.CTkRadioButton(row, text="登录", variable=mode_var, value="login", command=apply_mode).pack(
            side="left", padx=(0, 16)
        )
        ctk.CTkRadioButton(row, text="注册", variable=mode_var, value="register", command=apply_mode).pack(side="left")
        apply_mode()

        su, sp = auth_client.load_credentials()
        if su:
            user_e.insert(0, su)
        if sp:
            pwd_e.insert(0, sp)

        def _release_grab() -> None:
            try:
                win.grab_release()
            except tk.TclError:
                pass

        def on_cancel_mandatory() -> None:
            _release_grab()
            win.destroy()

        if mandatory:

            def on_wm_close() -> None:
                on_cancel_mandatory()

            win.protocol("WM_DELETE_WINDOW", on_wm_close)
        else:

            def on_wm_close_optional() -> None:
                _release_grab()
                win.destroy()

            win.protocol("WM_DELETE_WINDOW", on_wm_close_optional)

        def do_action() -> None:
            u = user_e.get().strip()
            p = pwd_e.get()
            if not u or not p:
                messagebox.showwarning("登录", "请输入用户名和密码。", parent=win)
                return
            if mode_var.get() == "login":
                res = auth_client.login(u, p)
            else:
                res = auth_client.register(u, p)
            if res is None:
                messagebox.showerror("登录", "无法连接服务器或无响应。", parent=win)
                return
            if isinstance(res, dict) and res.get("user_id") is not None:
                auth_client.user_id = res.get("user_id")
                auth_client.username = res.get("username") or u
                auth_client.gold_beans = res.get("gold_beans")
                auth_client.load_gold_config()
                if remember_var.get():
                    auth_client.save_credentials(u, p)
                else:
                    auth_client.clear_credentials()
                refresh_auth_bar()
                if mandatory:
                    _release_grab()
                win.destroy()
                return
            em = _auth_api_error_message(res) if _auth_api_error_message else None
            messagebox.showerror("登录", em or str((res or {}).get("error") or "登录失败"), parent=win)

        if mandatory:
            tip = ctk.CTkLabel(
                win,
                text="须登录后才能使用本程序。点「取消」将退出。",
                text_color=("gray35", "gray60"),
                font=ctk.CTkFont(size=11),
                wraplength=360,
            )
            tip.pack(fill="x", padx=20, pady=(0, 4))
            btn_row = ctk.CTkFrame(win, fg_color="transparent")
            btn_row.pack(fill="x", padx=20, pady=(12, 14))
            ctk.CTkButton(btn_row, text="取消", height=36, fg_color=("gray70", "gray38"), command=on_cancel_mandatory).pack(
                side="left", expand=True, fill="x", padx=(0, 8)
            )
            ctk.CTkButton(btn_row, text="确定", height=36, command=do_action).pack(side="right", expand=True, fill="x")
        else:
            ctk.CTkButton(win, text="确定", height=36, command=do_action).pack(fill="x", padx=20, pady=(16, 12))

        _center_toplevel_on_root(win, root, dlg_w, dlg_h)
        root.lift()
        win.lift()
        win.focus_force()
        win.attributes("-topmost", True)
        win.after(150, lambda: win.attributes("-topmost", False))
        if mandatory:
            try:
                win.grab_set()
            except tk.TclError:
                pass
            root.wait_window(win)
            return bool(auth_client.user_id)
        return False

    def on_refresh_gold() -> None:
        from tkinter import messagebox

        if not auth_client or not auth_client.user_id:
            messagebox.showinfo("豆子", "请先登录。")
            return
        r = auth_client.ping_gold_beans()
        em = _auth_api_error_message(r) if _auth_api_error_message else None
        if em:
            messagebox.showerror("豆子", em)
        else:
            refresh_auth_bar()

    def on_login_toggle() -> None:
        if not auth_client:
            open_auth_dialog(mandatory=False)
            return
        if auth_client.user_id:
            auth_client.user_id = None
            auth_client.username = None
            auth_client.gold_beans = None
            refresh_auth_bar()
        else:
            open_auth_dialog(mandatory=False)

    auth_lbl = ctk.CTkLabel(top_bar, textvariable=auth_status_var, font=ctk.CTkFont(size=12), anchor="w")
    auth_lbl.pack(side="left", fill="x", expand=True, padx=(0, 8))
    ctk.CTkButton(top_bar, text="刷新豆子", width=88, height=28, command=on_refresh_gold).pack(side="right", padx=(4, 0))
    login_btn = ctk.CTkButton(top_bar, text="登录", width=88, height=28, command=on_login_toggle)
    login_btn.pack(side="right")

    def refresh_auth_bar() -> None:
        if not auth_client:
            auth_status_var.set("认证未加载（请安装 requests 并从仓库根目录运行）")
            try:
                login_btn.configure(text="登录")
            except tk.TclError:
                pass
            return
        if auth_client.user_id:
            u = auth_client.username or ""
            g = auth_client.gold_beans
            gtxt = str(g) if g is not None else "—"
            auth_status_var.set(f"已登录: {u}  |  豆子: {gtxt}")
            login_btn.configure(text="退出登录")
        else:
            auth_status_var.set("未登录（导出 MP4 需登录）")
            login_btn.configure(text="登录")

    draft_root = ctk.StringVar(value=initial_draft_root_for_ui())
    selected_name: Optional[str] = None

    main = ctk.CTkFrame(root, fg_color="transparent")
    main.pack(fill="both", expand=True, padx=10, pady=(2, 8))

    panel_paned, left, right, preview_col = _create_three_column_layout(main)
    panel_paned.pack(fill="both", expand=True)
    right.grid_columnconfigure(0, weight=1)
    # 草稿信息固定高度；时间轴占剩余空间；导出区固定高度
    right.grid_rowconfigure(0, weight=0, minsize=48)
    right.grid_rowconfigure(1, weight=1, minsize=160)
    right.grid_rowconfigure(2, weight=0, minsize=96)

    ctk.CTkLabel(left, text="草稿箱", font=ctk.CTkFont(size=16, weight="bold")).pack(anchor="w", padx=12, pady=(10, 4))

    path_entry = ctk.CTkEntry(left, placeholder_text="草稿根目录…", height=30)
    path_entry.pack(fill="x", padx=10, pady=(0, 6))

    list_frame = ctk.CTkScrollableFrame(left, label_text="草稿列表", corner_radius=10)
    list_frame.pack(fill="both", expand=True, padx=8, pady=(0, 8))

    detail = ctk.CTkTextbox(
        right, font=ctk.CTkFont(family="Consolas", size=12), wrap="word", height=52, activate_scrollbars=True
    )
    detail.grid(row=0, column=0, sticky="ew", padx=10, pady=(8, 4))

    timeline_block = ctk.CTkFrame(right, fg_color="transparent")
    timeline_block.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 2))
    timeline_block.grid_columnconfigure(0, weight=1)
    timeline_block.grid_rowconfigure(0, weight=0)
    timeline_block.grid_rowconfigure(1, weight=1)
    timeline_block.grid_rowconfigure(2, weight=0)

    DEFAULT_TIMELINE_PPS = 68.0
    timeline_content_cache: List[Optional[Dict[str, Any]]] = [None]
    timeline_zoom: Dict[str, float] = {"pps": DEFAULT_TIMELINE_PPS}
    timeline_zoom_label_var = ctk.StringVar(value="缩放 100%")
    timeline_duration_var = ctk.StringVar(value="")

    replace_state: Dict[str, Any] = {
        "refs": [],
        "style_refs": [],
        "encrypted": False,
        "content_ok": False,
        "timeline_draft_name": "",
        # 片段键 -> {"dir","order"} 与可选的 replace_file（单文件替换记录，仅界面展示）
        "segment_export_pool": {},
        # 顺序模式：按片段键延续下标（多轮导出）
        "export_pool_sequential_cursor": {},
    }

    timeline_header = ctk.CTkFrame(timeline_block, fg_color="transparent")
    timeline_header.grid(row=0, column=0, sticky="ew")
    timeline_header.grid_columnconfigure(0, weight=1)

    ctk.CTkLabel(
        timeline_header,
        text="时间轴预览（点击空白/标尺移动播放头；点击片段选中）",
        font=ctk.CTkFont(size=13, weight="bold"),
        anchor="w",
    ).grid(row=0, column=0, sticky="w")
    ctk.CTkLabel(
        timeline_header,
        textvariable=timeline_duration_var,
        font=ctk.CTkFont(size=11),
        text_color=("gray45", "gray60"),
        anchor="w",
    ).grid(row=1, column=0, sticky="w", pady=(0, 0))

    zoom_bar = ctk.CTkFrame(timeline_header, fg_color="transparent")
    zoom_bar.grid(row=0, column=1, sticky="e", padx=(8, 0))
    ctk.CTkLabel(zoom_bar, text="横向缩放", font=ctk.CTkFont(size=11), text_color=("gray45", "gray60")).pack(
        side="left", padx=(0, 6)
    )

    def _timeline_viewport_width() -> int:
        try:
            timeline_inner.update_idletasks()
            vw = int(timeline_inner.winfo_width())
        except (tk.TclError, ValueError, TypeError):
            vw = 0
        return vw if vw >= 120 else 780

    def timeline_zoom_fit_width() -> None:
        raw = timeline_content_cache[0]
        if not isinstance(raw, dict):
            return
        timeline_zoom["pps"] = _calc_timeline_fit_pps(raw, _timeline_viewport_width())
        refresh_timeline_panel_data(None, reset_selection=False)

    def refresh_timeline_panel_data(raw: Optional[Dict[str, Any]] = None, *, reset_selection: bool = True) -> None:
        if raw is not None:
            stop_play = replace_state.get("_stop_preview_playback")
            if callable(stop_play):
                try:
                    stop_play()
                except Exception:
                    pass
            timeline_content_cache[0] = raw
            timeline_zoom["pps"] = _calc_timeline_fit_pps(raw, _timeline_viewport_width())
            timeline_select["playhead_us"] = 0
            replace_state["playhead_us"] = 0
        elif reset_selection:
            timeline_content_cache[0] = None
        if reset_selection:
            timeline_select.clear()
            timeline_select.update({"kind": "none", "ti": None, "si": None, "summary": ""})
            timeline_select["playhead_us"] = 0
            replace_state["playhead_us"] = 0
            preview_state["gen"] = int(preview_state.get("gen", 0)) + 1
            preview_state["scrub_busy"] = False
            preview_state["ui_apply_pending"] = None
            preview_state["ui_apply_scheduled"] = False
            preview_state["frame_cache"].clear()
            preview_state["thumb_cache"].clear()
        if raw is not None:
            def _deferred_thumb_warm() -> None:
                cur = timeline_content_cache[0]
                if isinstance(cur, dict):
                    start_preview_foreground_warm_on_load(cur, preview_state["thumb_cache"])

            root.after(200, _deferred_thumb_warm)

        pct = int(round(100.0 * timeline_zoom["pps"] / DEFAULT_TIMELINE_PPS))
        timeline_zoom_label_var.set(f"缩放 {pct}%")
        raw_cur = timeline_content_cache[0]
        if isinstance(raw_cur, dict):
            total_us = _timeline_end_us(raw_cur)
            n_tracks = len(raw_cur.get("tracks") or [])
            n_segs = sum(len(tr.get("segments") or []) for tr in (raw_cur.get("tracks") or []))
            timeline_duration_var.set(
                f"总长 {_fmt_us_as_timecode(total_us)} · {n_tracks} 轨 · {n_segs} 片段（加载时自动适应宽度，可横向滚动或点「适应宽度」）"
            )
        else:
            timeline_duration_var.set("")

        def _wheel_zoom_step(direction: int) -> None:
            if timeline_content_cache[0] is None:
                return
            fac = 1.12 if direction > 0 else 1.0 / 1.12
            pps = float(timeline_zoom["pps"] * fac)
            pps = max(14.0, min(420.0, pps))
            if abs(pps - timeline_zoom["pps"]) < 0.01:
                return
            timeline_zoom["pps"] = pps
            refresh_timeline_panel_data(None, reset_selection=False)

        populate_timeline_panel(
            timeline_inner,
            timeline_content_cache[0],
            selection=timeline_select,
            status_label=timeline_sel_label,
            status_replace_highlight_label=timeline_replace_highlight_label,
            replace_state=replace_state,
            pixels_per_second=timeline_zoom["pps"],
            wheel_zoom_step=_wheel_zoom_step if timeline_content_cache[0] else None,
        )
        ui_sync = replace_state.get("_on_timeline_selection_ui")
        if callable(ui_sync):
            try:
                ui_sync()
            except Exception:
                pass
        if not reset_selection:
            try:
                refresh_timeline_segment_status_if_selected()
            except Exception:
                pass
        ph = int(timeline_select.get("playhead_us") or replace_state.get("playhead_us") or 0)
        prep = replace_state.get("_prepare_preview_for_draft_load")
        if raw is not None and callable(prep):
            try:
                prep(raw)
            except Exception:
                pass
        elif reset_selection and not isinstance(timeline_content_cache[0], dict) and callable(prep):
            try:
                prep(None)
            except Exception:
                pass
        else:
            cb_ph = replace_state.get("_on_playhead_change")
            if callable(cb_ph):
                try:
                    cb_ph(ph)
                except Exception:
                    pass

    def timeline_zoom_mult(factor: float) -> None:
        if timeline_content_cache[0] is None:
            return
        pps = max(14.0, min(420.0, float(timeline_zoom["pps"] * factor)))
        if abs(pps - timeline_zoom["pps"]) < 0.01:
            return
        timeline_zoom["pps"] = pps
        refresh_timeline_panel_data(None, reset_selection=False)

    def timeline_zoom_reset() -> None:
        if timeline_content_cache[0] is None:
            return
        timeline_zoom["pps"] = DEFAULT_TIMELINE_PPS
        refresh_timeline_panel_data(None, reset_selection=False)

    ctk.CTkButton(zoom_bar, text="−", width=30, command=lambda: timeline_zoom_mult(1 / 1.18)).pack(
        side="left", padx=2
    )
    ctk.CTkLabel(
        zoom_bar,
        textvariable=timeline_zoom_label_var,
        font=ctk.CTkFont(size=12),
        width=72,
    ).pack(side="left", padx=2)
    ctk.CTkButton(zoom_bar, text="+", width=30, command=lambda: timeline_zoom_mult(1.18)).pack(side="left", padx=2)
    ctk.CTkButton(zoom_bar, text="重置", width=52, fg_color=("gray70", "gray38"), command=timeline_zoom_reset).pack(
        side="left", padx=(6, 0)
    )
    ctk.CTkButton(
        zoom_bar, text="适应宽度", width=72, fg_color=("gray70", "gray38"), command=timeline_zoom_fit_width
    ).pack(side="left", padx=(6, 0))

    timeline_inner = ctk.CTkFrame(timeline_block, fg_color=("gray92", "gray20"), corner_radius=8)
    timeline_inner.grid(row=1, column=0, sticky="nsew", pady=(2, 0))

    timeline_select: Dict[str, Any] = {"kind": "none", "ti": None, "si": None, "summary": ""}

    ctk.CTkLabel(
        preview_col,
        text="播放器",
        font=ctk.CTkFont(size=14, weight="bold"),
        anchor="w",
    ).pack(anchor="w", padx=10, pady=(8, 2))
    preview_img_host = ctk.CTkFrame(preview_col, fg_color=("gray88", "gray18"), corner_radius=8)
    preview_img_host.pack(fill="both", expand=True, padx=8, pady=(0, 4))
    preview_video_host = tk.Frame(preview_img_host, bg="#1a1a1a", highlightthickness=0)
    preview_video_host.pack(fill="both", expand=True, padx=3, pady=3)
    preview_canvas = tk.Canvas(preview_img_host, bg="#1a1a1a", highlightthickness=0)
    preview_canvas.place(relx=0, rely=0, relwidth=1, relheight=1, x=0, y=0)
    preview_sub_overlay = tk.Canvas(
        preview_img_host,
        bg="#1a1a1a",
        highlightthickness=0,
        bd=0,
        height=PREVIEW_SUB_BAR_HEIGHT,
    )
    preview_ctrl = ctk.CTkFrame(preview_col, fg_color=("gray82", "gray22"), corner_radius=6, height=36)
    preview_ctrl.pack(fill="x", padx=8, pady=(0, 4))
    preview_ctrl.pack_propagate(False)
    preview_time_var = ctk.StringVar(value="00:00:00:00 / 00:00:00:00")
    ctk.CTkLabel(
        preview_ctrl,
        textvariable=preview_time_var,
        font=ctk.CTkFont(family="Consolas", size=11),
        text_color=("#1a9e9e", "#5ee9e9"),
        anchor="w",
    ).pack(side="left", fill="x", expand=True, padx=(8, 4), pady=4)
    preview_info_var = ctk.StringVar(value="")
    ctk.CTkLabel(
        preview_col,
        textvariable=preview_info_var,
        font=ctk.CTkFont(size=10),
        text_color=("gray45", "gray60"),
        anchor="w",
        wraplength=248,
        justify="left",
    ).pack(anchor="w", padx=10, pady=(0, 6))
    preview_state: Dict[str, Any] = {
        "photo": None,
        "frame_cache": _PreviewFrameCache(max_items=96),
        "thumb_cache": _ThumbnailStripCache(),
        "gen": 0,
        "pending_us": None,
        "scrub_busy": False,
        "last_worker_ms": 0,
        "warm_interrupted_for_scrub": False,
        "last_scrub_warm_ms": 0.0,
        "warm_idle_after_id": None,
        "ui_apply_scheduled": False,
        "ui_apply_pending": None,
        "merge_prefetch_gen": 0,
        "merge_session_paths": set(),
        "merge_delete_pending": set(),
        "merge_delete_after_id": None,
        "playing": False,
        "play_after_id": None,
        "play_wall_t0": None,
        "play_start_us": 0,
        "play_audio_proc": None,
        "play_audio_procs": None,
        "play_audio_key": None,
        "play_last_frame_idx": None,
        "play_last_video_key": None,
        "play_display_us": None,
        "play_last_ph_redraw_us": -1,
        "play_video_worker": None,
        "play_video_worker_started": False,
        "play_video_reader": _PlaybackVideoReader(),
        "preview_sub_layout": None,
        "last_preview_ppm": None,
        "last_preview_plan": None,
        "last_preview_subtitle_us": None,
        "last_preview_layout_size": (0, 0),
        "preview_resize_after_id": None,
        "play_subtitle_frame_idx": None,
        "play_clock_arm_after_id": None,
        "play_arm_us": None,
        "play_audio_alive_since": None,
        "play_audio_arm_started_at": None,
        "play_audio_output_ready": False,
        "play_audio_ready_gen": 0,
        "play_prime_ready": False,
        "play_prime_gen": 0,
        "play_mode": "live",
        "merge_path": None,
        "merge_t0_us": 0,
        "merge_window_us": PREVIEW_MERGE_CHUNK_US,
        "merge_chunk_t0_us": 0,
        "merge_chunk_end_us": 0,
        "merge_next_path": None,
        "merge_next_t0_us": None,
        "merge_next_end_us": None,
        "merge_prefetch_busy": False,
        "merge_prefetch_gen": 0,
        "merge_waiting_next": False,
        "merge_pause_timeline_us": None,
        "merge_ffplay_session": None,
        "merge_ffplay_token": 0,
        "merge_ffplay_embedded": False,
        "merge_ffplay_fallback": False,
        "audio_chunk_t0_us": None,
        "audio_chunk_end_us": None,
        "audio_chunk_path": None,
        "audio_next_path": None,
        "audio_next_t0_us": None,
        "audio_next_end_us": None,
        "audio_prefetch_busy": False,
        "audio_prefetch_gen": 0,
        "audio_waiting_next": False,
        "audio_pause_timeline_us": None,
    }

    def _playback_timeline_us() -> Optional[int]:
        """时间轴 T = play_start_us + 经过的 wall time（与字幕 target_timerange 同坐标）。"""
        wall_t0 = preview_state.get("play_wall_t0")
        if wall_t0 is None:
            return None
        start_us = int(preview_state.get("play_start_us") or 0)
        elapsed_us = int(max(0.0, time.time() - float(wall_t0)) * 1_000_000)
        return start_us + elapsed_us

    def _playback_subtitle_us(timeline_us: int) -> int:
        return int(timeline_us)

    def _preview_host_inner_size() -> Tuple[int, int]:
        try:
            preview_video_host.update_idletasks()
            cw = max(80, int(preview_video_host.winfo_width()))
            ch = max(80, int(preview_video_host.winfo_height()))
        except tk.TclError:
            cw, ch = PREVIEW_MAX_WIDTH, 360
        return cw, ch

    def _merge_ffplay_session() -> _MergedPreviewFfplaySession:
        sess = preview_state.get("merge_ffplay_session")
        if not isinstance(sess, _MergedPreviewFfplaySession):
            sess = _MergedPreviewFfplaySession()
            preview_state["merge_ffplay_session"] = sess
        return sess

    def _show_merge_ffplay_ui() -> None:
        preview_canvas.place_forget()
        try:
            cw = max(80, int(preview_video_host.winfo_width()))
        except tk.TclError:
            cw = PREVIEW_MAX_WIDTH
        preview_sub_overlay.configure(width=cw, height=PREVIEW_SUB_BAR_HEIGHT)
        preview_sub_overlay.place(relx=0, rely=1.0, relwidth=1, anchor="sw")
        preview_sub_overlay.lift()

    def _hide_merge_ffplay_ui() -> None:
        preview_sub_overlay.place_forget()
        preview_sub_overlay.delete("preview_sub")
        preview_canvas.place(relx=0, rely=0, relwidth=1, relheight=1, x=0, y=0)

    def _stop_merged_preview_ffplay() -> None:
        sess = preview_state.get("merge_ffplay_session")
        if isinstance(sess, _MergedPreviewFfplaySession):
            sess.close()
        preview_state["merge_ffplay_embedded"] = False
        preview_state["merge_ffplay_fallback"] = False
        _hide_merge_ffplay_ui()

    def _mark_merge_audio_spawned() -> None:
        now = time.time()
        preview_state["play_audio_alive_since"] = now
        preview_state["play_audio_arm_started_at"] = now
        preview_state["play_audio_output_ready"] = False

    def _attach_playback_audio_ready_watch(procs: List[Any]) -> None:
        if not procs:
            return
        ffplay_proc = procs[-1]
        ready_gen = int(preview_state.get("gen", 0))
        preview_state["play_audio_ready_gen"] = ready_gen
        preview_state["play_audio_output_ready"] = False

        def _on_ready() -> None:
            def _ui() -> None:
                if ready_gen != int(preview_state.get("play_audio_ready_gen", 0)):
                    return
                if not _preview_is_playing():
                    return
                preview_state["play_audio_output_ready"] = True

            try:
                root.after(0, _ui)
            except tk.TclError:
                pass

        watch_ffplay_audio_output_ready(
            ffplay_proc,
            _on_ready,
            timeout_sec=PREVIEW_PLAY_SYNC_TIMEOUT_MS / 1000.0,
        )

    def _start_merged_preview_ffplay(*, start_sec: float = 0.0) -> bool:
        """单路 ffplay 播放合成 MP4（Windows 嵌入预览区；失败则回退 OpenCV+仅音频）。"""
        merge_path = preview_state.get("merge_path")
        if not merge_path or not os.path.isfile(str(merge_path)):
            return False
        sess = preview_state.get("merge_ffplay_session")
        if isinstance(sess, _MergedPreviewFfplaySession) and sess.alive():
            if preview_state.get("merge_ffplay_fallback"):
                return bool(preview_state.get("play_audio_procs"))
            return True
        cw, ch = _preview_host_inner_size()
        token = int(preview_state.get("merge_ffplay_token") or 0) + 1
        preview_state["merge_ffplay_token"] = token
        title = _merge_preview_ffplay_title(str(token))
        player = _merge_ffplay_session()
        if sys.platform == "win32" and player.spawn(
            str(merge_path),
            window_title=title,
            width=cw,
            height=ch,
            start_sec=start_sec,
        ):
            preview_state["merge_ffplay_fallback"] = False
            preview_state["merge_ffplay_embedded"] = False
            preview_state["play_audio_procs"] = [player.proc]
            preview_state["play_audio_proc"] = player.proc
            _mark_merge_audio_spawned()
            return True
        preview_state["merge_ffplay_fallback"] = True
        _stop_merged_preview_ffplay()
        worker = preview_state.get("play_video_worker")
        content = timeline_content_cache[0]
        if isinstance(worker, _MergedPreviewVideoWorker) and isinstance(content, dict):
            merge_t0 = int(preview_state.get("merge_t0_us") or preview_state.get("play_start_us") or 0)
            file_us = int(max(0.0, float(start_sec) * 1_000_000))
            worker.switch_chunk(str(merge_path), merge_t0, file_us=file_us)
        procs = spawn_merged_preview_audio(str(merge_path), start_sec=start_sec)
        preview_state["play_audio_procs"] = procs
        preview_state["play_audio_proc"] = procs[-1] if procs else None
        if procs:
            _mark_merge_audio_spawned()
        return bool(procs)

    def _try_embed_merged_preview_ffplay() -> bool:
        if preview_state.get("merge_ffplay_fallback"):
            return True
        player = preview_state.get("merge_ffplay_session")
        if not isinstance(player, _MergedPreviewFfplaySession) or not player.alive():
            return False
        cw, ch = _preview_host_inner_size()
        try:
            parent_hwnd = int(preview_video_host.winfo_id())
        except tk.TclError:
            return False
        if not player.try_embed(parent_hwnd, cw, ch):
            return False
        preview_state["merge_ffplay_embedded"] = True
        _show_merge_ffplay_ui()
        return True

    def _cancel_playback_arm() -> None:
        aid = preview_state.get("play_clock_arm_after_id")
        if aid is not None:
            try:
                root.after_cancel(aid)
            except (tk.TclError, ValueError, TypeError):
                pass
            preview_state["play_clock_arm_after_id"] = None

    def _repoll_playback_arm() -> None:
        preview_state["play_clock_arm_after_id"] = root.after(40, _poll_playback_arm)

    def _arm_playback_clock(playhead_us: int) -> None:
        """音视频就绪后，以当前时刻起跑（不再用固定 hold 偏移）。"""
        _cancel_playback_arm()
        preview_state["play_audio_alive_since"] = None
        preview_state["play_audio_arm_started_at"] = None
        if not _preview_is_playing():
            return
        preview_state["play_start_us"] = int(playhead_us)
        preview_state["play_wall_t0"] = time.time()
        preview_state["play_subtitle_frame_idx"] = None
        preview_state["play_last_ph_redraw_us"] = -1
        _preview_play_tick()

    def _poll_playback_arm() -> None:
        preview_state["play_clock_arm_after_id"] = None
        if not _preview_is_playing():
            return
        if not preview_state.get("play_prime_ready"):
            started_at = float(preview_state.get("play_audio_arm_started_at") or time.time())
            if (time.time() - started_at) * 1000.0 >= PREVIEW_PLAY_SYNC_TIMEOUT_MS:
                preview_state["play_prime_ready"] = True
            else:
                _repoll_playback_arm()
                return
        us = int(preview_state.get("play_arm_us") or preview_state.get("play_start_us") or 0)
        content = timeline_content_cache[0]
        procs = preview_state.get("play_audio_procs") or []
        use_merge = preview_state.get("play_mode") == "merge"
        if use_merge:
            if not (preview_state.get("play_audio_procs") or []):
                if not _start_merged_preview_ffplay():
                    started_at = float(preview_state.get("play_audio_arm_started_at") or time.time())
                    if (time.time() - started_at) * 1000.0 >= PREVIEW_PLAY_SYNC_TIMEOUT_MS:
                        _arm_playback_clock(us)
                    else:
                        _repoll_playback_arm()
                    return
            procs = preview_state.get("play_audio_procs") or []
            if procs and any(p is None or p.poll() is not None for p in procs):
                started_at = float(preview_state.get("play_audio_arm_started_at") or time.time())
                if (time.time() - started_at) * 1000.0 >= PREVIEW_PLAY_SYNC_TIMEOUT_MS:
                    _arm_playback_clock(us)
                else:
                    _repoll_playback_arm()
                return
            if not preview_state.get("merge_ffplay_fallback") and not preview_state.get("merge_ffplay_embedded"):
                if not _try_embed_merged_preview_ffplay():
                    _repoll_playback_arm()
                    return
            alive_since = preview_state.get("play_audio_alive_since")
            if alive_since is None:
                preview_state["play_audio_alive_since"] = time.time()
                _repoll_playback_arm()
                return
            if (time.time() - float(alive_since)) * 1000.0 < PREVIEW_MERGE_SYNC_HOLD_MS:
                _repoll_playback_arm()
                return
            _arm_playback_clock(us)
            return

        if preview_state.get("play_mode") == "scrub":
            hits = _playback_audio_hits(content, us) if isinstance(content, dict) else ()
            procs = preview_state.get("play_audio_procs") or []
            if hits:
                if not procs:
                    _ensure_scrub_preview_audio(content, us, force=True)
                    procs = preview_state.get("play_audio_procs") or []
                if procs:
                    if any(p is None or p.poll() is not None for p in procs):
                        started_at = float(
                            preview_state.get("play_audio_arm_started_at") or time.time()
                        )
                        if (time.time() - started_at) * 1000.0 >= PREVIEW_PLAY_SYNC_TIMEOUT_MS:
                            _arm_playback_clock(us)
                        else:
                            _repoll_playback_arm()
                        return
                    alive_since = preview_state.get("play_audio_alive_since")
                    if not preview_state.get("play_audio_output_ready"):
                        started_at = float(alive_since or preview_state.get("play_audio_arm_started_at") or time.time())
                        if (time.time() - started_at) * 1000.0 >= PREVIEW_PLAY_SYNC_TIMEOUT_MS:
                            preview_state["play_audio_output_ready"] = True
                        else:
                            _repoll_playback_arm()
                            return
                    _arm_playback_clock(us)
                    return
            _arm_playback_clock(us)
            return

        hits: Tuple[Any, ...] = ()
        if isinstance(content, dict):
            hits = _playback_audio_hits(content, us)
            if hits and not procs:
                _start_playback_audio(content, us)
                procs = preview_state.get("play_audio_procs") or []

        if hits and procs:
            if any(p is None or p.poll() is not None for p in procs):
                started_at = float(preview_state.get("play_audio_arm_started_at") or time.time())
                if (time.time() - started_at) * 1000.0 >= PREVIEW_PLAY_SYNC_TIMEOUT_MS:
                    _arm_playback_clock(us)
                    return
                _repoll_playback_arm()
                return
            alive_since = preview_state.get("play_audio_alive_since")
            if alive_since is None:
                preview_state["play_audio_alive_since"] = time.time()
                _repoll_playback_arm()
                return
            if (time.time() - float(alive_since)) * 1000.0 < PREVIEW_PLAY_SYNC_HOLD_MS:
                _repoll_playback_arm()
                return

        _arm_playback_clock(us)

    def _schedule_playback_arm(playhead_us: int) -> None:
        _cancel_playback_arm()
        preview_state["play_arm_us"] = int(playhead_us)
        if not (preview_state.get("play_audio_procs") or []):
            preview_state["play_audio_alive_since"] = None
        preview_state["play_audio_arm_started_at"] = time.time()
        preview_state["play_clock_arm_after_id"] = root.after(40, _poll_playback_arm)

    def _playback_worker_state() -> Optional[Tuple[float, int, int]]:
        if not _preview_is_playing():
            return None
        wall_t0 = preview_state.get("play_wall_t0")
        if wall_t0 is None:
            return None
        return (
            float(wall_t0),
            int(preview_state.get("play_start_us") or 0),
            int(preview_state.get("gen", 0)),
        )

    def _preview_is_playing() -> bool:
        return bool(preview_state.get("playing"))

    def _preview_play_btn_set(text: str) -> None:
        btn = preview_state.get("play_btn")
        if btn is not None:
            try:
                btn.configure(text=text)
            except tk.TclError:
                pass

    def _stop_playback_audio() -> None:
        _stop_merged_preview_ffplay()
        kill_playback_audio_procs(preview_state.get("play_audio_procs"))
        preview_state["play_audio_procs"] = None
        preview_state["play_audio_proc"] = None
        preview_state["play_audio_key"] = None
        preview_state["play_audio_output_ready"] = False
        preview_state["play_audio_ready_gen"] = int(preview_state.get("play_audio_ready_gen", 0)) + 1

    def _start_playback_audio(content: Dict[str, Any], playhead_us: int) -> None:
        hits = _playback_audio_hits(content, playhead_us)
        if not hits:
            _stop_playback_audio()
            return
        key = _playback_audio_signature(hits)
        if key == preview_state.get("play_audio_key"):
            return
        old_key = preview_state.get("play_audio_key")
        need_resync = old_key is not None and old_key != key
        if need_resync:
            preview_state["play_wall_t0"] = None
        _stop_playback_audio()
        layers = tuple(layer for layer, _seg_key in hits)
        procs = spawn_playback_audio(layers)
        if not procs:
            if need_resync and _preview_is_playing():
                _arm_playback_clock(playhead_us)
            return
        preview_state["play_audio_procs"] = procs
        preview_state["play_audio_proc"] = procs[-1]
        preview_state["play_audio_key"] = key
        _mark_merge_audio_spawned()
        _attach_playback_audio_ready_watch(procs)
        if need_resync and _preview_is_playing():
            _schedule_playback_arm(playhead_us)

    def _sync_playback_audio_if_needed(content: Dict[str, Any], playhead_us: int) -> None:
        hits = _playback_audio_hits(content, playhead_us)
        if not hits:
            if preview_state.get("play_audio_key") is not None:
                _stop_playback_audio()
            return
        key = _playback_audio_signature(hits)
        if key != preview_state.get("play_audio_key"):
            _start_playback_audio(content, playhead_us)

    def _track_merge_preview_path(path: Optional[str]) -> None:
        if path and os.path.isfile(str(path)):
            preview_state.setdefault("merge_session_paths", set()).add(str(path))

    def _queue_merge_preview_file_deletion(
        paths: Optional[Iterable[str]] = None,
        *,
        delay_ms: int = 800,
    ) -> None:
        """延后删除合成预览 MP4，避免 ffplay/OpenCV 仍在读文件时 unlink 导致崩溃。"""
        pending = preview_state.setdefault("merge_delete_pending", set())
        if paths is not None:
            for p in paths:
                if p:
                    pending.add(str(p))
        if not pending:
            return
        aid = preview_state.get("merge_delete_after_id")
        if aid is not None:
            try:
                root.after_cancel(aid)
            except (tk.TclError, ValueError, TypeError):
                pass

        def _flush() -> None:
            preview_state["merge_delete_after_id"] = None
            items = list(preview_state.get("merge_delete_pending") or set())
            preview_state["merge_delete_pending"] = set()
            preview_state["merge_session_paths"] = set()
            for p in items:
                _delete_merge_preview_file(str(p))

        preview_state["merge_delete_after_id"] = root.after(max(200, int(delay_ms)), _flush)

    def _stop_preview_playback() -> None:
        preview_state["playing"] = False
        _cancel_playback_arm()
        aid = preview_state.get("play_after_id")
        if aid is not None:
            try:
                root.after_cancel(aid)
            except (tk.TclError, ValueError, TypeError):
                pass
            preview_state["play_after_id"] = None
        _stop_playback_audio()
        worker = preview_state.get("play_video_worker")
        if isinstance(worker, (_PlaybackVideoWorker, _MergedPreviewVideoWorker)):
            worker.close()
        preview_state["play_video_worker"] = None
        preview_state["play_video_worker_started"] = False
        preview_state["play_mode"] = "live"
        preview_state["merge_path"] = None
        preview_state["merge_next_path"] = None
        preview_state["merge_prefetch_busy"] = False
        preview_state["merge_waiting_next"] = False
        preview_state["merge_pause_timeline_us"] = None
        preview_state["merge_prefetch_gen"] = int(preview_state.get("merge_prefetch_gen") or 0) + 1
        _queue_merge_preview_file_deletion(preview_state.get("merge_session_paths"))
        reader = preview_state.get("play_video_reader")
        if isinstance(reader, _PlaybackVideoReader):
            reader.close()
        preview_state["play_display_us"] = None
        preview_state["play_last_ph_redraw_us"] = -1
        preview_state["play_wall_t0"] = None
        preview_state["preview_sub_layout"] = None
        preview_state["play_subtitle_frame_idx"] = None
        preview_state["play_prime_ready"] = False
        preview_state["play_audio_alive_since"] = None
        preview_state["play_audio_arm_started_at"] = None
        _hide_merge_ffplay_ui()
        preview_state["audio_chunk_path"] = None
        preview_state["audio_next_path"] = None
        preview_state["audio_prefetch_busy"] = False
        preview_state["audio_waiting_next"] = False
        preview_state["audio_pause_timeline_us"] = None
        preview_state["audio_prefetch_gen"] = int(preview_state.get("audio_prefetch_gen") or 0) + 1
        preview_state["audio_chunk_t0_us"] = None
        preview_state["audio_chunk_end_us"] = None
        _preview_play_btn_set("▶")

    def _refresh_playback_subtitles(timeline_us: int) -> None:
        """播放中刷新字幕（合成单路 ffplay 时画在透明 overlay 上）。"""
        content = timeline_content_cache[0]
        if not isinstance(content, dict):
            return
        plan = build_preview_plan(content, _playback_subtitle_us(timeline_us))
        if (
            preview_state.get("play_mode") == "merge"
            and preview_state.get("merge_ffplay_embedded")
            and not preview_state.get("merge_ffplay_fallback")
        ):
            cw, _ch = _preview_host_inner_size()
            bar_h = PREVIEW_SUB_BAR_HEIGHT
            preview_sub_overlay.configure(width=cw, height=bar_h)
            preview_sub_overlay.delete("preview_sub")
            _draw_preview_subtitle_overlays(preview_sub_overlay, plan.texts, cw, bar_h)
            preview_state["preview_sub_layout"] = (0, 0, cw, bar_h)
            return
        layout = preview_state.get("preview_sub_layout")
        if not layout or preview_state.get("photo") is None:
            return
        ox, oy, iw, ih = layout
        _draw_preview_subtitle_overlays(preview_canvas, plan.texts, iw, ih, offset_x=ox, offset_y=oy)

    def _start_merge_chunk_prefetch(content: Dict[str, Any], next_t0_us: int) -> None:
        if preview_state.get("merge_prefetch_busy") or preview_state.get("merge_next_path"):
            return
        total_us = _timeline_end_us(content)
        if int(next_t0_us) >= total_us:
            return
        gen = int(preview_state.get("merge_prefetch_gen") or 0) + 1
        preview_state["merge_prefetch_gen"] = gen
        preview_state["merge_prefetch_busy"] = True

        def _bg() -> None:
            path, _err = render_preview_merge_window(
                content, int(next_t0_us), window_us=PREVIEW_MERGE_CHUNK_US
            )

            def _done() -> None:
                preview_state["merge_prefetch_busy"] = False
                if gen != int(preview_state.get("merge_prefetch_gen") or 0):
                    return
                if not _preview_is_playing() or preview_state.get("play_mode") != "merge":
                    return
                if not path:
                    if preview_state.get("merge_waiting_next"):
                        preview_state["merge_waiting_next"] = False
                        preview_state["playing"] = False
                        _preview_play_btn_set("▶")
                        _preview_show_message("下一段合成失败，播放已停止")
                    return
                _track_merge_preview_path(path)
                preview_state["merge_next_path"] = path
                preview_state["merge_next_t0_us"] = int(next_t0_us)
                preview_state["merge_next_end_us"] = _preview_merge_chunk_end_us(
                    content, int(next_t0_us), PREVIEW_MERGE_CHUNK_US
                )
                if preview_state.get("merge_waiting_next"):
                    pause_us = preview_state.get("merge_pause_timeline_us")
                    if pause_us is not None:
                        _advance_merge_chunk(int(pause_us))

            root.after(0, _done)

        threading.Thread(target=_bg, daemon=True, name="preview-merge-prefetch").start()

    def _maybe_prefetch_next_merge_chunk(content: Dict[str, Any], timeline_us: int) -> None:
        if preview_state.get("play_mode") != "merge":
            return
        chunk_end = int(preview_state.get("merge_chunk_end_us") or 0)
        total_us = _timeline_end_us(content)
        if chunk_end >= total_us:
            return
        if int(timeline_us) < chunk_end - PREVIEW_MERGE_PREFETCH_LEAD_US:
            return
        _start_merge_chunk_prefetch(content, chunk_end)

    def _advance_merge_chunk(timeline_us: int) -> None:
        content = timeline_content_cache[0]
        if not isinstance(content, dict):
            _stop_preview_playback()
            return
        next_path = preview_state.get("merge_next_path")
        next_t0 = preview_state.get("merge_next_t0_us")
        next_end = preview_state.get("merge_next_end_us")
        if not next_path or next_t0 is None or next_end is None:
            return
        next_t0_i = int(next_t0)
        next_end_i = int(next_end)
        file_us = max(0, int(timeline_us) - next_t0_i)
        _stop_playback_audio()
        preview_state["merge_path"] = str(next_path)
        preview_state["merge_t0_us"] = next_t0_i
        preview_state["merge_chunk_t0_us"] = next_t0_i
        preview_state["merge_chunk_end_us"] = next_end_i
        preview_state["merge_next_path"] = None
        preview_state["merge_next_t0_us"] = None
        preview_state["merge_next_end_us"] = None
        preview_state["merge_waiting_next"] = False
        preview_state["merge_pause_timeline_us"] = None
        preview_state["merge_prefetch_gen"] = int(preview_state.get("merge_prefetch_gen") or 0) + 1
        file_sec = max(0.0, float(file_us) / 1_000_000.0)
        if not _start_merged_preview_ffplay(start_sec=file_sec):
            _stop_preview_playback()
            _preview_show_message("无法切换下一段预览")
            return
        if preview_state.get("merge_ffplay_fallback"):
            worker = preview_state.get("play_video_worker")
            if isinstance(worker, _MergedPreviewVideoWorker):
                if not worker.switch_chunk(str(next_path), next_t0_i, file_us=file_us):
                    _stop_preview_playback()
                    _preview_show_message("无法切换下一段预览")
                    return
        preview_state["merge_ffplay_embedded"] = False
        preview_state["play_wall_t0"] = None
        preview_state["play_subtitle_frame_idx"] = None
        try:
            preview_info_var.set(
                f"合成预览 · {_fmt_us_as_timecode(next_t0_i)}～{_fmt_us_as_timecode(next_end_i)}"
            )
        except Exception:
            pass
        _schedule_playback_arm(int(timeline_us))
        _maybe_prefetch_next_merge_chunk(content, int(timeline_us))

    def _try_continue_merge_playback(content: Dict[str, Any], timeline_us: int) -> bool:
        """当前合成段播完：切下一段或等待后台合成。返回 True 表示已处理（勿停止）。"""
        chunk_end = int(preview_state.get("merge_chunk_end_us") or 0)
        total_us = _timeline_end_us(content)
        if int(timeline_us) < chunk_end - 40_000:
            return False
        if chunk_end >= total_us:
            return False
        if preview_state.get("merge_next_path"):
            _advance_merge_chunk(max(int(timeline_us), chunk_end))
            return True
        preview_state["merge_waiting_next"] = True
        preview_state["merge_pause_timeline_us"] = max(int(timeline_us), chunk_end)
        preview_state["play_wall_t0"] = None
        _preview_show_message("正在合成下一段…")
        if not preview_state.get("merge_prefetch_busy"):
            _start_merge_chunk_prefetch(content, chunk_end)
        return True

    def _timeline_audio_chunk_end(content: Dict[str, Any], t0_us: int) -> int:
        return min(int(t0_us) + PREVIEW_AUDIO_CHUNK_US, _timeline_end_us(content))

    def _start_timeline_audio_prefetch(content: Dict[str, Any], next_t0_us: int) -> None:
        if preview_state.get("audio_prefetch_busy") or preview_state.get("audio_next_path"):
            return
        total_us = _timeline_end_us(content)
        if int(next_t0_us) >= total_us:
            return
        gen = int(preview_state.get("audio_prefetch_gen") or 0) + 1
        preview_state["audio_prefetch_gen"] = gen
        preview_state["audio_prefetch_busy"] = True

        def _bg() -> None:
            path, _err = render_preview_audio_window(
                content, int(next_t0_us), window_us=PREVIEW_AUDIO_CHUNK_US
            )

            def _done() -> None:
                preview_state["audio_prefetch_busy"] = False
                if gen != int(preview_state.get("audio_prefetch_gen") or 0):
                    return
                if not _preview_is_playing() or preview_state.get("play_mode") != "scrub":
                    return
                if not path:
                    return
                _track_merge_preview_path(path)
                preview_state["audio_next_path"] = path
                preview_state["audio_next_t0_us"] = int(next_t0_us)
                preview_state["audio_next_end_us"] = _timeline_audio_chunk_end(content, int(next_t0_us))
                if preview_state.get("audio_waiting_next"):
                    pause_us = preview_state.get("audio_pause_timeline_us")
                    if pause_us is not None:
                        _advance_timeline_audio_chunk(int(pause_us))

            root.after(0, _done)

        threading.Thread(target=_bg, daemon=True, name="preview-audio-prefetch").start()

    def _advance_timeline_audio_chunk(timeline_us: int) -> None:
        content = timeline_content_cache[0]
        if not isinstance(content, dict):
            _stop_preview_playback()
            return
        next_path = preview_state.get("audio_next_path")
        next_t0 = preview_state.get("audio_next_t0_us")
        next_end = preview_state.get("audio_next_end_us")
        if not next_path or next_t0 is None or next_end is None:
            return
        next_t0_i = int(next_t0)
        next_end_i = int(next_end)
        preview_state["audio_next_path"] = None
        preview_state["audio_next_t0_us"] = None
        preview_state["audio_next_end_us"] = None
        preview_state["audio_waiting_next"] = False
        preview_state["audio_pause_timeline_us"] = None
        preview_state["audio_prefetch_gen"] = int(preview_state.get("audio_prefetch_gen") or 0) + 1
        _spawn_scrub_preview_audio(
            content,
            next_t0_i,
            str(next_path),
            t0_us=next_t0_i,
            end_us=next_end_i,
        )
        preview_state["play_wall_t0"] = None
        preview_state["play_subtitle_frame_idx"] = None
        try:
            preview_info_var.set(
                f"时间轴音频 · {_fmt_us_as_timecode(next_t0_i)}～{_fmt_us_as_timecode(next_end_i)}"
            )
        except Exception:
            pass
        _schedule_playback_arm(int(timeline_us))
        if next_end_i < _timeline_end_us(content):
            _start_timeline_audio_prefetch(content, next_end_i)

    def _maybe_prefetch_timeline_audio_chunk(content: Dict[str, Any], timeline_us: int) -> None:
        chunk_end = int(preview_state.get("audio_chunk_end_us") or 0)
        total_us = _timeline_end_us(content)
        if chunk_end >= total_us:
            return
        if int(timeline_us) < chunk_end - PREVIEW_AUDIO_PREFETCH_LEAD_US:
            return
        _start_timeline_audio_prefetch(content, chunk_end)

    def _try_continue_timeline_audio(content: Dict[str, Any], timeline_us: int) -> bool:
        if preview_state.get("play_mode") != "scrub":
            return False
        if preview_state.get("audio_waiting_next"):
            if preview_state.get("audio_next_path") and preview_state.get("audio_pause_timeline_us") is not None:
                _advance_timeline_audio_chunk(int(preview_state["audio_pause_timeline_us"]))
            return True
        chunk_end = int(preview_state.get("audio_chunk_end_us") or 0)
        total_us = _timeline_end_us(content)
        if chunk_end <= 0 or int(timeline_us) < chunk_end:
            return False
        if chunk_end >= total_us:
            return False
        if not preview_state.get("audio_next_path"):
            preview_state["audio_waiting_next"] = True
            preview_state["audio_pause_timeline_us"] = chunk_end
            preview_state["play_wall_t0"] = None
            _preview_show_message("正在准备下一段时间轴音频…")
            if not preview_state.get("audio_prefetch_busy"):
                _start_timeline_audio_prefetch(content, chunk_end)
            return True
        _advance_timeline_audio_chunk(chunk_end)
        return True

    def _ensure_scrub_preview_audio(
        content: Dict[str, Any],
        timeline_us: int,
        *,
        force: bool = False,
    ) -> None:
        """播放中：按当前时间轴位置立即 ffplay 出声（不等待后台 chunk 渲染）。"""
        hits = _playback_audio_hits(content, int(timeline_us))
        if not hits:
            if preview_state.get("play_audio_procs"):
                _stop_playback_audio()
            return
        sig = _playback_audio_signature(hits)
        procs = preview_state.get("play_audio_procs") or []
        alive = any(p is not None and p.poll() is None for p in procs)
        if alive and not force and sig == preview_state.get("play_audio_key"):
            return
        old_key = preview_state.get("play_audio_key")
        need_resync = old_key is not None and old_key != sig
        if alive:
            _stop_playback_audio()
        layers = tuple(layer for layer, _key in hits)
        new_procs = spawn_playback_audio(layers)
        preview_state["play_audio_procs"] = new_procs or None
        preview_state["play_audio_proc"] = new_procs[-1] if new_procs else None
        preview_state["play_audio_key"] = sig if new_procs else None
        if new_procs:
            _mark_merge_audio_spawned()
            _attach_playback_audio_ready_watch(new_procs)
            try:
                preview_info_var.set(
                    f"预览音频 · {_fmt_us_as_timecode(int(timeline_us))}"
                )
            except Exception:
                pass
        elif not find_ffplay():
            try:
                preview_info_var.set("（未找到 ffplay，无法播放预览音频）")
            except Exception:
                pass
        if need_resync and _preview_is_playing():
            preview_state["play_wall_t0"] = None
            _schedule_playback_arm(int(timeline_us))

    def _mark_playback_prime_ready() -> None:
        if not _preview_is_playing():
            return
        preview_state["play_prime_ready"] = True

    def _start_playback_preview_prime(content: Dict[str, Any], playhead_us: int) -> None:
        """播放起跑前：拉取当前播放头画面（与 ffplay 启动并行）。"""
        us = int(playhead_us)
        plan = build_preview_plan(content, us)
        prime_gen = int(preview_state.get("gen", 0))
        preview_state["play_prime_gen"] = prime_gen
        preview_state["play_prime_ready"] = False

        if not plan.videos:
            _preview_sync_labels(us, plan)
            _mark_playback_prime_ready()
            return

        thumb_cache = preview_state["thumb_cache"]
        frame_cache = preview_state["frame_cache"]
        instant = fetch_instant_scrub_frame(plan, thumb_cache)
        if not instant:
            top = plan.videos[-1]
            instant = frame_cache.get(top.path, top.source_us)
        if instant:
            _queue_preview_apply(instant, plan, prime_gen, subtitle_us=us)
            _preview_sync_labels(us, plan)
            _mark_playback_prime_ready()
            return

        try:
            preview_info_var.set("准备预览画面…")
        except Exception:
            pass
        _preview_sync_timecode(us, content)

        def _worker() -> None:
            img = fetch_scrub_frame_fast(plan, frame_cache=frame_cache)

            def _ui() -> None:
                if not _preview_is_playing():
                    return
                if prime_gen != int(preview_state.get("gen", 0)):
                    return
                if img:
                    _queue_preview_apply(img, plan, prime_gen, subtitle_us=us)
                _preview_sync_labels(us, plan)
                _mark_playback_prime_ready()

            root.after(0, _ui)

        threading.Thread(target=_worker, daemon=True, name="preview-play-prime").start()

    def _spawn_scrub_preview_audio(
        content: Dict[str, Any],
        timeline_us: int,
        path: Optional[str],
        *,
        t0_us: int,
        end_us: int,
    ) -> List[Any]:
        """启动时间轴音频 ffplay；失败则回退到当前播放头的 live 混音。"""
        _stop_playback_audio()
        procs: List[Any] = []
        if path and os.path.isfile(str(path)):
            _track_merge_preview_path(path)
            procs = spawn_merged_preview_audio(str(path), start_sec=0.0)
        if not procs:
            layers = find_playback_audio_layers(content, int(timeline_us))
            if layers:
                procs = spawn_playback_audio(layers)
        preview_state["play_audio_procs"] = procs or None
        preview_state["play_audio_proc"] = procs[-1] if procs else None
        preview_state["audio_chunk_t0_us"] = int(t0_us)
        preview_state["audio_chunk_end_us"] = int(end_us)
        preview_state["audio_chunk_path"] = path
        if procs:
            _mark_merge_audio_spawned()
            _attach_playback_audio_ready_watch(procs)
            try:
                preview_info_var.set(
                    f"时间轴音频 · {_fmt_us_as_timecode(int(t0_us))}～"
                    f"{_fmt_us_as_timecode(int(end_us))}"
                )
            except Exception:
                pass
        elif find_playback_audio_layers(content, int(timeline_us)):
            try:
                preview_info_var.set("（时间轴音频渲染失败，live 回退也未启动 ffplay）")
            except Exception:
                pass
        elif not find_ffplay():
            try:
                preview_info_var.set("（未找到 ffplay，无法播放预览音频）")
            except Exception:
                pass
        return procs

    def _start_timeline_audio_chunk_play(content: Dict[str, Any], t0_us: int, *, gen: int) -> None:
        win_s = PREVIEW_AUDIO_CHUNK_US // 1_000_000
        try:
            preview_info_var.set(
                f"准备时间轴音频（{_fmt_us_as_timecode(t0_us)} 起 {win_s}s）…"
            )
        except Exception:
            pass

        def _bg() -> None:
            path: Optional[str] = None
            err: Optional[str] = None
            try:
                path, err = render_preview_audio_window(
                    content, int(t0_us), window_us=PREVIEW_AUDIO_CHUNK_US
                )
            except Exception as ex:
                err = str(ex)

            def _done() -> None:
                if not _preview_is_playing() or gen != int(preview_state.get("gen", 0)):
                    return
                end_us = _timeline_audio_chunk_end(content, int(t0_us))
                attach_us = int(t0_us)
                cur_us = _playback_timeline_us()
                if cur_us is not None:
                    attach_us = int(cur_us)
                window_sec = max(0.001, (end_us - int(t0_us)) / 1_000_000.0)
                start_sec = max(0.0, (attach_us - int(t0_us)) / 1_000_000.0)
                if path and start_sec < window_sec - 0.08:
                    _stop_playback_audio()
                    _track_merge_preview_path(path)
                    procs = spawn_merged_preview_audio(str(path), start_sec=start_sec)
                    if procs:
                        preview_state["play_audio_procs"] = procs
                        preview_state["play_audio_proc"] = procs[-1]
                        _mark_merge_audio_spawned()
                elif not (preview_state.get("play_audio_procs") or []):
                    _ensure_scrub_preview_audio(content, attach_us, force=True)
                if preview_state.get("play_wall_t0") is None:
                    preview_state["play_prime_ready"] = True
                    _schedule_playback_arm(int(t0_us))
                if end_us < _timeline_end_us(content):
                    _start_timeline_audio_prefetch(content, end_us)

            root.after(0, _done)

        threading.Thread(target=_bg, daemon=True, name="preview-audio-chunk").start()

    def _preview_play_tick() -> None:
        """播放 = 时间轴指针自动前进 + 与拖动相同的预览取帧。"""
        preview_state["play_after_id"] = None
        if not _preview_is_playing():
            return
        content = timeline_content_cache[0]
        if not isinstance(content, dict):
            _stop_preview_playback()
            return
        fps = _draft_preview_fps(content)
        tick_ms = max(16, int(1000.0 / fps))

        if preview_state.get("play_wall_t0") is None:
            if preview_state.get("play_clock_arm_after_id") is not None:
                if _preview_is_playing():
                    preview_state["play_after_id"] = root.after(tick_ms, _preview_play_tick)
                return
            preview_state["play_wall_t0"] = time.time()
            preview_state["play_start_us"] = int(
                preview_state.get("play_start_us") or replace_state.get("playhead_us") or 0
            )

        timeline_us = _playback_timeline_us()
        if timeline_us is None:
            return

        total_us = _timeline_end_us(content)
        if timeline_us >= total_us:
            set_ph = replace_state.get("_set_playhead")
            if callable(set_ph):
                try:
                    set_ph(total_us, notify=True, redraw=True)
                except Exception:
                    pass
            _stop_preview_playback()
            return

        if preview_state.get("play_mode") == "scrub":
            procs = preview_state.get("play_audio_procs") or []
            if not any(p is not None and p.poll() is None for p in procs):
                _ensure_scrub_preview_audio(content, timeline_us)

        set_ph = replace_state.get("_set_playhead")
        if callable(set_ph):
            try:
                set_ph(timeline_us, notify=True, redraw=True)
            except TypeError:
                try:
                    set_ph(timeline_us, notify=True)
                except Exception:
                    pass
            except Exception:
                pass
        else:
            replace_state["playhead_us"] = timeline_us
            preview_state["pending_us"] = timeline_us
            on_playhead_changed(timeline_us)

        preview_state["play_last_ph_redraw_us"] = timeline_us
        _maybe_warm_scrub_strip(build_preview_plan(content, timeline_us))

        if _preview_is_playing():
            preview_state["play_after_id"] = root.after(tick_ms, _preview_play_tick)

    def _toggle_preview_playback() -> None:
        if _preview_is_playing():
            _stop_preview_playback()
            return
        content = timeline_content_cache[0]
        if not isinstance(content, dict):
            return
        us = int(replace_state.get("playhead_us") or preview_state.get("pending_us") or 0)
        plan = build_preview_plan(content, us)
        audio_hits = _playback_audio_hits(content, us)
        if not plan.videos and not audio_hits:
            _preview_show_message("（当前时间无视频/音频）")
            return
        total_us = _timeline_end_us(content)
        if us >= total_us:
            return

        _hide_merge_ffplay_ui()
        old_worker = preview_state.get("play_video_worker")
        if isinstance(old_worker, (_PlaybackVideoWorker, _MergedPreviewVideoWorker)):
            old_worker.close()
        _stop_playback_audio()
        _queue_merge_preview_file_deletion(preview_state.get("merge_session_paths"))

        preview_state["playing"] = True
        preview_state["play_mode"] = "scrub"
        preview_state["play_wall_t0"] = None
        preview_state["play_start_us"] = us
        preview_state["play_last_ph_redraw_us"] = -1
        preview_state["play_video_worker"] = None
        preview_state["play_video_worker_started"] = False
        preview_state["play_prime_ready"] = False
        preview_state["merge_path"] = None
        preview_state["merge_next_path"] = None
        preview_state["audio_chunk_path"] = None
        preview_state["audio_next_path"] = None
        preview_state["audio_prefetch_busy"] = False
        preview_state["audio_waiting_next"] = False
        preview_state["audio_pause_timeline_us"] = None
        preview_state["audio_prefetch_gen"] = int(preview_state.get("audio_prefetch_gen") or 0) + 1
        preview_state["gen"] = int(preview_state.get("gen", 0)) + 1
        _preview_play_btn_set("⏸")
        _interrupt_warm_for_scrub()
        _cancel_warm_idle_timer()
        try:
            preview_info_var.set("准备预览…")
        except Exception:
            pass
        if audio_hits:
            _ensure_scrub_preview_audio(content, us, force=True)
        _start_playback_preview_prime(content, us)
        _schedule_playback_arm(us)

    preview_play_btn = ctk.CTkButton(
        preview_ctrl,
        text="▶",
        width=36,
        height=28,
        font=ctk.CTkFont(size=16),
        fg_color=("gray70", "gray32"),
        hover_color=("gray60", "gray40"),
        command=_toggle_preview_playback,
    )
    preview_play_btn.pack(side="right", padx=(4, 6), pady=4)
    preview_state["play_btn"] = preview_play_btn

    def _preview_focus_in_text_input() -> bool:
        try:
            fw = root.focus_get()
        except tk.TclError:
            return False
        if fw is None:
            return False
        if isinstance(fw, (ctk.CTkEntry, ctk.CTkTextbox)):
            return True
        return str(fw.winfo_class()) in ("Entry", "Text", "TEntry", "Spinbox")

    def _on_preview_space_key(_event: tk.Event) -> Optional[str]:
        if _preview_focus_in_text_input():
            return None
        _toggle_preview_playback()
        return "break"

    root.bind("<KeyPress-space>", _on_preview_space_key, add="+")
    replace_state["_stop_preview_playback"] = _stop_preview_playback

    def _schedule_preview_apply(
        img_bytes: bytes,
        plan: PreviewPlan,
        gen: int,
        *,
        subtitle_us: Optional[int] = None,
    ) -> None:
        preview_state["ui_apply_pending"] = (img_bytes, plan, gen, subtitle_us)
        if preview_state.get("ui_apply_scheduled"):
            return
        preview_state["ui_apply_scheduled"] = True

        def _flush_ui_apply() -> None:
            preview_state["ui_apply_scheduled"] = False
            pending = preview_state.get("ui_apply_pending")
            if not pending:
                return
            preview_state["ui_apply_pending"] = None
            img_b, plan_b, gen_b, sub_us = pending
            if gen_b != int(preview_state.get("gen", 0)):
                return
            try:
                _apply_preview_image(img_b, plan_b, gen_b, subtitle_us=sub_us)
            except Exception:
                pass

        root.after(0, _flush_ui_apply)

    def _preview_show_message(msg: str) -> None:
        preview_state["photo"] = None
        preview_canvas.delete("all")
        try:
            w = max(160, int(preview_canvas.winfo_width()))
            h = max(120, int(preview_canvas.winfo_height()))
        except tk.TclError:
            w, h = 280, 200
        preview_canvas.create_text(
            w // 2,
            h // 2,
            text=msg,
            fill="#888888",
            font=("Microsoft YaHei UI", 10),
            justify="center",
            width=max(120, w - 24),
        )

    def _preview_canvas_inner_size() -> Tuple[int, int]:
        try:
            cw = max(80, int(preview_canvas.winfo_width()))
            ch = max(80, int(preview_canvas.winfo_height()))
        except tk.TclError:
            cw, ch = PREVIEW_MAX_WIDTH, 360
        return cw, ch

    def _layout_preview_ppm(
        img_bytes: bytes,
        plan: PreviewPlan,
        gen: int,
        *,
        subtitle_us: Optional[int] = None,
        silent: bool = False,
    ) -> bool:
        if gen != int(preview_state.get("gen", 0)):
            return False
        cw, ch = _preview_canvas_inner_size()
        scaled = _scale_ppm_to_fit(img_bytes, cw, ch)
        try:
            photo = tk.PhotoImage(data=scaled)
        except tk.TclError:
            if not silent:
                _preview_show_message("（预览解码失败）")
            return False
        preview_state["photo"] = photo
        preview_canvas.delete("all")
        iw, ih = photo.width(), photo.height()
        ox = max(0, (cw - iw) // 2)
        oy = max(0, (ch - ih) // 2)
        preview_canvas.create_image(ox, oy, anchor="nw", image=photo, tags=("preview_img",))
        texts = plan.texts
        if subtitle_us is not None:
            content = timeline_content_cache[0]
            if isinstance(content, dict):
                texts = build_preview_plan(content, subtitle_us).texts
        preview_state["preview_sub_layout"] = (ox, oy, iw, ih)
        preview_state["last_preview_layout_size"] = (cw, ch)
        _draw_preview_subtitle_overlays(preview_canvas, texts, iw, ih, offset_x=ox, offset_y=oy)
        return True

    def _relayout_preview_from_cache() -> None:
        preview_state["preview_resize_after_id"] = None
        ppm = preview_state.get("last_preview_ppm")
        plan = preview_state.get("last_preview_plan")
        if not ppm or plan is None:
            return
        gen = int(preview_state.get("gen", 0))
        cw, ch = _preview_canvas_inner_size()
        if (cw, ch) == tuple(preview_state.get("last_preview_layout_size") or (0, 0)):
            return
        subtitle_us = preview_state.get("last_preview_subtitle_us")
        if _preview_is_playing():
            timeline_us = _playback_timeline_us()
            if timeline_us is not None:
                subtitle_us = _playback_subtitle_us(timeline_us)
        try:
            _layout_preview_ppm(ppm, plan, gen, subtitle_us=subtitle_us, silent=True)
        except Exception:
            pass

    def _schedule_preview_relayout(_event: Any = None) -> None:
        if (
            preview_state.get("play_mode") == "merge"
            and preview_state.get("merge_ffplay_embedded")
            and not preview_state.get("merge_ffplay_fallback")
        ):
            player = preview_state.get("merge_ffplay_session")
            if isinstance(player, _MergedPreviewFfplaySession) and player.hwnd:
                cw, ch = _preview_host_inner_size()
                _win_resize_embedded_window(player.hwnd, cw, ch)
                preview_sub_overlay.configure(width=cw, height=PREVIEW_SUB_BAR_HEIGHT)
                timeline_us = _playback_timeline_us()
                if timeline_us is not None:
                    _refresh_playback_subtitles(timeline_us)
        if preview_state.get("last_preview_ppm") is None:
            return
        cw, ch = _preview_canvas_inner_size()
        if cw < 80 or ch < 80:
            return
        if (cw, ch) == tuple(preview_state.get("last_preview_layout_size") or (0, 0)):
            return
        aid = preview_state.get("preview_resize_after_id")
        if aid is not None:
            try:
                root.after_cancel(aid)
            except (tk.TclError, ValueError, TypeError):
                pass
        preview_state["preview_resize_after_id"] = root.after(60, _relayout_preview_from_cache)

    preview_canvas.bind("<Configure>", _schedule_preview_relayout, add="+")
    preview_video_host.bind("<Configure>", _schedule_preview_relayout, add="+")

    def _apply_preview_image(
        img_bytes: bytes,
        plan: PreviewPlan,
        gen: int,
        *,
        silent: bool = False,
        subtitle_us: Optional[int] = None,
    ) -> bool:
        preview_state["last_preview_ppm"] = img_bytes
        preview_state["last_preview_plan"] = plan
        preview_state["last_preview_subtitle_us"] = subtitle_us
        return _layout_preview_ppm(img_bytes, plan, gen, subtitle_us=subtitle_us, silent=silent)

    def _queue_preview_apply(
        img_bytes: bytes,
        plan: PreviewPlan,
        gen: int,
        *,
        subtitle_us: Optional[int] = None,
    ) -> None:
        _schedule_preview_apply(img_bytes, plan, gen, subtitle_us=subtitle_us)

    def _preview_is_scrubbing() -> bool:
        flag = replace_state.get("_playhead_scrubbing")
        if isinstance(flag, list) and flag:
            return bool(flag[0])
        return False

    def _preview_sync_timecode(us: int, content: Optional[Dict[str, Any]] = None) -> None:
        if content is None:
            content = timeline_content_cache[0]
        if not isinstance(content, dict):
            preview_time_var.set("00:00:00:00 / 00:00:00:00")
            return
        fps = _draft_preview_fps(content)
        total_us = _timeline_end_us(content)
        preview_time_var.set(
            f"{_fmt_player_timecode(us, fps=fps)} / {_fmt_player_timecode(total_us, fps=fps)}"
        )

    def _preview_sync_labels(us: int, plan: Optional[PreviewPlan] = None) -> None:
        content = timeline_content_cache[0]
        if not isinstance(content, dict):
            preview_time_var.set("00:00:00:00 / 00:00:00:00")
            preview_info_var.set("")
            return
        _preview_sync_timecode(us, content)
        if plan is None:
            plan = build_preview_plan(content, us)
        preview_info_var.set(plan.info[:120] + ("…" if len(plan.info) > 120 else ""))

    def _cancel_warm_idle_timer() -> None:
        aid = preview_state.get("warm_idle_after_id")
        if aid is not None:
            try:
                root.after_cancel(aid)
            except (tk.TclError, ValueError, TypeError):
                pass
            preview_state["warm_idle_after_id"] = None

    def _interrupt_warm_for_scrub() -> None:
        if preview_state.get("warm_interrupted_for_scrub"):
            return
        preview_state["warm_interrupted_for_scrub"] = True
        _cancel_warm_idle_timer()
        # 不终止缩略图预热 ffmpeg：拖动时仍需要后台持续写入 thumb_cache

    def _schedule_warm_near_playhead(playhead_us: int) -> None:
        _cancel_warm_idle_timer()

        def _idle_warm() -> None:
            preview_state["warm_idle_after_id"] = None
            if _preview_is_scrubbing() or _preview_is_playing():
                return
            content = timeline_content_cache[0]
            if not isinstance(content, dict):
                return
            warm_preview_near_playhead(content, preview_state["thumb_cache"], int(playhead_us))

        preview_state["warm_idle_after_id"] = root.after(PREVIEW_WARM_IDLE_MS, _idle_warm)

    def _on_scrub_end(playhead_us: int) -> None:
        preview_state["warm_interrupted_for_scrub"] = False
        _schedule_warm_near_playhead(playhead_us)

    def _try_instant_scrub_preview(plan: PreviewPlan) -> bool:
        instant = fetch_instant_scrub_frame(plan, preview_state["thumb_cache"])
        if not instant:
            return False
        gen = int(preview_state.get("gen", 0)) + 1
        preview_state["gen"] = gen
        _queue_preview_apply(instant, plan, gen)
        return True

    def _maybe_warm_scrub_strip(plan: PreviewPlan) -> None:
        now_ms = time.time() * 1000.0
        last_ms = float(preview_state.get("last_scrub_warm_ms") or 0.0)
        if now_ms - last_ms < PREVIEW_WARM_SCRUB_THROTTLE_MS:
            return
        preview_state["last_scrub_warm_ms"] = now_ms
        warm_preview_strip_near_plan(plan, preview_state["thumb_cache"])

    def _run_fast_preview_fetch(plan: PreviewPlan, us: int) -> None:
        interactive = _preview_is_scrubbing() or _preview_is_playing()
        if preview_state.get("scrub_busy") and not interactive:
            return
        gen = int(preview_state.get("gen", 0)) + 1
        preview_state["gen"] = gen
        preview_state["scrub_busy"] = True
        preview_state["last_worker_ms"] = time.time() * 1000.0
        frame_cache = preview_state["frame_cache"]

        def worker() -> None:
            img = fetch_scrub_frame_fast(plan, frame_cache=frame_cache)

            def ui() -> None:
                if gen != int(preview_state.get("gen", 0)):
                    return
                preview_state["scrub_busy"] = False
                if img:
                    _queue_preview_apply(img, plan, gen)
                latest = preview_state.get("pending_us")
                if (
                    latest is not None
                    and int(latest) != us
                    and isinstance(timeline_content_cache[0], dict)
                ):
                    p2 = build_preview_plan(timeline_content_cache[0], int(latest))
                    if not _try_instant_scrub_preview(p2):
                        _run_fast_preview_fetch(p2, int(latest))

            root.after(0, ui)

        threading.Thread(target=worker, daemon=True).start()

    def _request_preview_update(plan: PreviewPlan, us: int) -> None:
        if _try_instant_scrub_preview(plan):
            return
        warm_preview_for_plan(plan, preview_state["thumb_cache"])
        if not preview_state.get("scrub_busy"):
            _run_fast_preview_fetch(plan, us)

    def _preview_sync_time_only(us: int) -> None:
        _preview_sync_timecode(us)

    def on_playhead_changed(playhead_us: int) -> None:
        preview_state["pending_us"] = int(playhead_us)

        us = int(playhead_us)
        content = timeline_content_cache[0]
        if not isinstance(content, dict):
            preview_time_var.set("00:00:00:00 / 00:00:00:00")
            preview_info_var.set("")
            return

        plan = build_preview_plan(content, us)
        if _preview_is_playing():
            _preview_sync_time_only(us)
        elif _preview_is_scrubbing():
            _preview_sync_time_only(us)
            _interrupt_warm_for_scrub()
        else:
            _preview_sync_labels(us, plan)
        if not plan.videos:
            if _preview_is_playing():
                return
            _preview_show_message("（当前时间无视频）")
            return

        if _preview_is_playing() or _preview_is_scrubbing():
            if _try_instant_scrub_preview(plan):
                if _preview_is_scrubbing() or _preview_is_playing():
                    _maybe_warm_scrub_strip(plan)
                return
            if _preview_is_scrubbing() or _preview_is_playing():
                _maybe_warm_scrub_strip(plan)
            if not preview_state.get("scrub_busy") or _preview_is_scrubbing() or _preview_is_playing():
                _run_fast_preview_fetch(plan, us)
            return

        _request_preview_update(plan, us)

    def _prepare_preview_for_draft_load(content: Optional[Dict[str, Any]]) -> None:
        """切换草稿：清空旧画面并拉取新稿 timeline 0 的首帧。"""
        preview_state["scrub_busy"] = False
        preview_state["ui_apply_pending"] = None
        preview_state["ui_apply_scheduled"] = False
        preview_state["last_preview_ppm"] = None
        preview_state["last_preview_plan"] = None
        preview_state["last_preview_subtitle_us"] = None
        preview_state["last_preview_layout_size"] = (0, 0)
        preview_state["photo"] = None
        preview_state["preview_sub_layout"] = None
        preview_state["pending_us"] = 0
        if not isinstance(content, dict):
            preview_time_var.set("00:00:00:00 / 00:00:00:00")
            preview_info_var.set("")
            _preview_show_message("（未选择草稿）")
            return
        _preview_show_message("（加载预览…）")
        on_playhead_changed(0)

    replace_state["_on_playhead_change"] = on_playhead_changed
    replace_state["_prepare_preview_for_draft_load"] = _prepare_preview_for_draft_load

    def _flush_preview_after_scrub(playhead_us: int) -> None:
        """松手：只补全文字信息，不重复取帧（拖动链式路径已显示画面）。"""
        preview_state["pending_us"] = int(playhead_us)
        us = int(playhead_us)
        content = timeline_content_cache[0]
        if isinstance(content, dict):
            plan = build_preview_plan(content, us)
            _preview_sync_labels(us, plan)
        _on_scrub_end(us)

    replace_state["_on_playhead_preview_flush"] = _flush_preview_after_scrub

    def _on_root_close_preview() -> None:
        _stop_preview_playback()

    root.protocol("WM_DELETE_WINDOW", lambda: (_on_root_close_preview(), root.destroy()))

    timeline_status_area = ctk.CTkFrame(timeline_block, fg_color="transparent")
    timeline_status_area.grid(row=2, column=0, sticky="ew", padx=4, pady=(2, 0))
    timeline_status_area.grid_columnconfigure(0, weight=1)
    timeline_status_area.grid_columnconfigure(1, weight=0)

    timeline_status_left = ctk.CTkFrame(timeline_status_area, fg_color="transparent")
    timeline_status_left.grid(row=0, column=0, rowspan=2, sticky="nsew")
    timeline_status_left.grid_columnconfigure(0, weight=1)

    # 右侧留给「导出槽素材预设」工具条（与片段说明同一行，节省导出区纵向空间）
    preset_toolbar_host = ctk.CTkFrame(timeline_status_area, fg_color="transparent")
    preset_toolbar_host.grid(row=0, column=1, rowspan=2, sticky="ne", padx=(6, 0), pady=(0, 2))

    timeline_sel_label = ctk.CTkTextbox(
        timeline_status_left,
        height=44,
        width=80,
        font=ctk.CTkFont(size=10),
        text_color=("gray40", "gray60"),
        fg_color="transparent",
        border_width=0,
        corner_radius=0,
        activate_scrollbars=True,
        wrap="word",
        takefocus=False,
    )
    timeline_sel_label.grid(row=0, column=0, sticky="ew")

    timeline_replace_highlight_label = ctk.CTkTextbox(
        timeline_status_left,
        height=28,
        width=80,
        font=ctk.CTkFont(size=10),
        text_color=("#2dd48f", "#5ee9ad"),
        fg_color="transparent",
        border_width=0,
        corner_radius=0,
        activate_scrollbars=False,
        wrap="word",
        takefocus=False,
    )
    timeline_replace_highlight_label.grid(row=1, column=0, sticky="ew", pady=(1, 0))

    _hint0 = (
        "提示：点击左侧轨道名选中轨道；点击彩色条选中片段；"
        "音视频可右键「替换素材…」；字幕/贴纸可点轨道名选中整轨后点「替换…」，或点片段右键配置花字/贴纸"
        "（Windows 下也可将单个文件或素材文件夹从资源管理器拖到片段条上，与弹窗保存一致）。"
        " 时间轴点一下后可用方向键：左右同轨片段，上下换轨（同序）且横滚对齐片段左缘；"
        "轨道多时可滚轮上下浏览或拖右侧竖条；Ctrl+滚轮或标题栏「+/−」横向缩放。"
    )
    _ctk_readonly_text_set(timeline_sel_label, _hint0)
    _ctk_readonly_text_set(timeline_replace_highlight_label, "")

    def refresh_timeline_segment_status_if_selected() -> None:
        """重绘时间轴后，若仍选中片段则按当前 segment_export_pool 等信息刷新下方说明。"""
        ts = timeline_select
        if ts.get("kind") != "seg" or ts.get("ti") is None or ts.get("orig_i") is None:
            _timeline_status_set_text(timeline_replace_highlight_label, "", ctk_mod=ctk)
            return
        raw = timeline_content_cache[0]
        if not raw or not isinstance(raw, dict):
            return
        try:
            ti = int(ts["ti"])
            oi = int(ts["orig_i"])
            vi = int(ts.get("vis_i", 0))
        except (TypeError, ValueError):
            return
        parts = timeline_segment_selection_status_parts(
            raw, ti=ti, vis_i=vi, orig_i=oi, replace_state=replace_state
        )
        if parts is None:
            return
        main, hl = parts
        ts["summary"] = main + (f"\n\n{hl}" if hl else "")
        _timeline_status_set_text(timeline_sel_label, main, ctk_mod=ctk)
        _timeline_status_set_text(timeline_replace_highlight_label, hl, ctk_mod=ctk)

    export_strip = ctk.CTkFrame(right, fg_color="transparent")
    export_strip.grid(row=2, column=0, sticky="ew", padx=10, pady=(2, 8))
    export_strip.grid_columnconfigure(0, weight=1)

    def _slot_index_1based(ref: MediaSegmentRef) -> int:
        refs = replace_state.get("refs") or []
        for i, r in enumerate(refs):
            if r.segment_index != ref.segment_index or r.track_type != ref.track_type:
                continue
            if (ref.track_id or "").strip() and (r.track_id or "").strip():
                if r.track_id == ref.track_id:
                    return i + 1
            elif r.track_name == ref.track_name and r.track_type_index == ref.track_type_index:
                return i + 1
        return 1

    def _filetypes_for_ref(r: MediaSegmentRef) -> List[Tuple[str, str]]:
        if r.track_type == "video":
            return [
                ("视频文件", "*.mp4 *.m4v *.mov *.mkv *.avi *.gif *.webm"),
                ("MP4 / M4V", "*.mp4 *.m4v"),
                ("所有文件", "*.*"),
            ]
        return [
            ("音频文件", "*.mp3 *.wav *.m4a *.aac *.flac"),
            ("视频（自动抽音轨为 MP3）", "*.mp4 *.m4v *.mov *.mkv *.avi *.webm"),
            ("MP3", "*.mp3"),
            ("所有文件", "*.*"),
        ]

    def _try_apply_ref(
        ref: MediaSegmentRef,
        npath: str,
        *,
        start_mode: str = VIDEO_REPLACE_SOURCE_HEAD,
        start_sec: float = 0.0,
    ) -> bool:
        from tkinter import messagebox

        name = selected_name
        base = draft_root.get().strip()
        slot_n = _slot_index_1based(ref)
        if not name:
            messagebox.showwarning("未选择草稿", "请先在左侧选择草稿。")
            return False
        if not npath or not os.path.isfile(npath):
            messagebox.showwarning("文件无效", f"槽 {slot_n}：请选择或填写一个存在的文件路径。")
            return False
        content_json = os.path.join(base, name, "draft_content.json")
        if not _file_exists_nonempty(content_json) or _looks_like_jianying_encrypted(content_json):
            messagebox.showerror(
                "无法替换",
                "draft_content.json 不存在或已被剪映加密，只能替换明文草稿。",
            )
            return False
        try:
            ck = segment_export_pool_key(name, ref)
            seg_map = replace_state.setdefault("segment_export_pool", {})
            sm = normalize_replace_source_start_mode(start_mode)
            sec_v = float(parse_replace_source_start_sec(start_sec)) if sm == VIDEO_REPLACE_SOURCE_CUSTOM else 0.0
            seg_map[ck] = {
                "replace_file": os.path.abspath(npath),
                "replace_source_start_mode": sm,
                "replace_source_start_sec": sec_v,
            }
            persist_working_export_pool_snapshot(base, name, replace_state)
            persist_active_named_export_pool_preset(base, name, pool_preset_var.get(), replace_state)
        except Exception as e:
            messagebox.showerror("保存失败", f"槽 {slot_n}: {e}")
            return False
        try:
            refresh_timeline_panel_data(None, reset_selection=False)
        except Exception:
            pass
        try:
            refresh_timeline_segment_status_if_selected()
        except Exception:
            pass
        return True

    def open_replace_material_dialog(ref: MediaSegmentRef) -> None:
        from tkinter import filedialog, messagebox

        win = ctk.CTkToplevel(root)
        win.title("替换素材")
        dlg_w, dlg_h = 600, 440
        win.geometry(f"{dlg_w}x{dlg_h}")
        win.minsize(520, 360)
        win.transient(root)

        main = ctk.CTkFrame(win, fg_color="transparent")
        main.pack(side="top", fill="both", expand=True, padx=16)

        slot_n = _slot_index_1based(ref)
        cur_show = os.path.basename(ref.current_path) if ref.current_path else "（无本地路径）"
        ctk.CTkLabel(
            main,
            text=f"槽 {slot_n} · {ref.combo_label}",
            font=ctk.CTkFont(size=14, weight="bold"),
            anchor="w",
        ).pack(fill="x", padx=0, pady=(16, 4))
        ctk.CTkLabel(
            main,
            text=f"当前文件: {cur_show}",
            font=ctk.CTkFont(size=12),
            text_color=("gray35", "gray55"),
            anchor="w",
        ).pack(fill="x", padx=0, pady=(0, 8))

        mode_var = ctk.StringVar(value="file")
        path_var = ctk.StringVar(value="")
        dir_var = ctk.StringVar(value="")
        _dn = (selected_name or "").strip()
        _seg_key = segment_export_pool_key(_dn, ref) if _dn else ""
        _cfg0: Dict[str, Any] = (
            (replace_state.get("segment_export_pool") or {}).get(_seg_key) or {}
            if _seg_key
            else {}
        )
        _ord0 = _cfg0.get("order", "random")
        seg_order_var = ctk.StringVar(value=_ord0 if _ord0 in ("random", "sequential") else "random")
        _rf0 = str(_cfg0.get("replace_file", "") or "").strip()
        _d0 = str(_cfg0.get("dir", "") or "").strip()
        if _rf0:
            path_var.set(_rf0)
            mode_var.set("file")
        elif _d0:
            dir_var.set(_d0)
            mode_var.set("dir")
        replace_src_mode_var = ctk.StringVar(
            value=normalize_replace_source_start_mode(_cfg0.get("replace_source_start_mode"))
        )
        _rsv0 = parse_replace_source_start_sec(_cfg0.get("replace_source_start_sec"))
        replace_src_sec_var = ctk.StringVar(value="" if _rsv0 == 0 else str(_rsv0))

        mode_row = ctk.CTkFrame(main, fg_color="transparent")
        mode_row.pack(fill="x", padx=0, pady=(0, 6))
        ctk.CTkLabel(mode_row, text="来源", font=ctk.CTkFont(size=12, weight="bold"), anchor="w").pack(
            side="left", padx=(0, 12)
        )

        def sync_mode() -> None:
            m = mode_var.get()
            if m == "file":
                if dir_block.winfo_manager():
                    dir_block.pack_forget()
                file_row.pack(fill="x", padx=0, pady=(4, 4))
            else:
                if file_row.winfo_manager():
                    file_row.pack_forget()
                dir_block.pack(fill="x", padx=0, pady=(4, 4))

        rb_file = ctk.CTkRadioButton(
            mode_row,
            text="单个文件",
            variable=mode_var,
            value="file",
            font=ctk.CTkFont(size=12),
            command=sync_mode,
        )
        rb_file.pack(side="left", padx=(0, 14))
        rb_dir = ctk.CTkRadioButton(
            mode_row,
            text="素材目录",
            variable=mode_var,
            value="dir",
            font=ctk.CTkFont(size=12),
            command=sync_mode,
        )
        rb_dir.pack(side="left")

        start_block = ctk.CTkFrame(main, fg_color="transparent")
        start_block.pack(fill="x", padx=0, pady=(4, 2))
        start_line = ctk.CTkFrame(start_block, fg_color="transparent")
        start_line.pack(fill="x")
        ctk.CTkLabel(start_line, text="起点", width=52, anchor="w", font=ctk.CTkFont(size=11)).pack(
            side="left", padx=(0, 8)
        )
        start_inner = ctk.CTkFrame(start_line, fg_color="transparent")
        start_inner.pack(side="left", fill="x", expand=True)

        sec_row = ctk.CTkFrame(start_block, fg_color="transparent")

        def _sync_replace_src_sec_row(*_args: Any) -> None:
            if replace_src_mode_var.get() == VIDEO_REPLACE_SOURCE_CUSTOM:
                sec_row.pack(fill="x", pady=(6, 0))
            else:
                sec_row.pack_forget()

        rb_src_head = ctk.CTkRadioButton(
            start_inner,
            text="片头",
            variable=replace_src_mode_var,
            value=VIDEO_REPLACE_SOURCE_HEAD,
            font=ctk.CTkFont(size=11),
            command=_sync_replace_src_sec_row,
        )
        rb_src_head.pack(side="left", padx=(0, 10))
        rb_src_rand = ctk.CTkRadioButton(
            start_inner,
            text="随机",
            variable=replace_src_mode_var,
            value=VIDEO_REPLACE_SOURCE_RANDOM,
            font=ctk.CTkFont(size=11),
            command=_sync_replace_src_sec_row,
        )
        rb_src_rand.pack(side="left", padx=(0, 10))
        rb_src_custom = ctk.CTkRadioButton(
            start_inner,
            text="自定义秒",
            variable=replace_src_mode_var,
            value=VIDEO_REPLACE_SOURCE_CUSTOM,
            font=ctk.CTkFont(size=11),
            command=_sync_replace_src_sec_row,
        )
        rb_src_custom.pack(side="left", padx=(0, 0))

        ctk.CTkLabel(sec_row, text="", width=52).pack(side="left", padx=(0, 8))
        ctk.CTkLabel(sec_row, text="从第几秒起", font=ctk.CTkFont(size=11), anchor="w").pack(side="left", padx=(0, 8))
        ctk.CTkEntry(
            sec_row,
            textvariable=replace_src_sec_var,
            width=100,
            height=30,
            placeholder_text="如 2 或 2.5",
        ).pack(side="left", padx=(0, 0))
        replace_src_mode_var.trace_add("write", _sync_replace_src_sec_row)

        def _persist_segment_export_pool() -> None:
            dn = (selected_name or "").strip()
            if not dn:
                return
            k = segment_export_pool_key(dn, ref)
            pool: Dict[str, Dict[str, Any]] = replace_state.setdefault("segment_export_pool", {})
            d = dir_var.get().strip()
            od = seg_order_var.get()
            if od not in ("random", "sequential"):
                od = "random"
            if mode_var.get() != "dir":
                return
            if d:
                sm = normalize_replace_source_start_mode(replace_src_mode_var.get())
                sec_v = parse_replace_source_start_sec(replace_src_sec_var.get()) if sm == VIDEO_REPLACE_SOURCE_CUSTOM else 0.0
                pool[k] = {
                    "dir": d,
                    "order": od,
                    "replace_source_start_mode": sm,
                    "replace_source_start_sec": float(sec_v) if sm == VIDEO_REPLACE_SOURCE_CUSTOM else 0.0,
                }
            else:
                pool.pop(k, None)
            base_s = draft_root.get().strip()
            if base_s:
                persist_working_export_pool_snapshot(base_s, dn, replace_state)
                persist_active_named_export_pool_preset(base_s, dn, pool_preset_var.get(), replace_state)

        def resolve_replacement_path() -> Optional[str]:
            # 目录模式仅配置导出套素材；立即替换文件请用「单个文件」。
            if mode_var.get() != "file":
                return None
            p = path_var.get().strip()
            return p if p else None

        def _confirm_replace_dialog() -> None:
            if mode_var.get() == "file":
                p = resolve_replacement_path()
                if not p:
                    messagebox.showwarning("文件无效", "请填写或浏览选择一个素材文件。")
                    return
                sm = normalize_replace_source_start_mode(replace_src_mode_var.get())
                sec_v = parse_replace_source_start_sec(replace_src_sec_var.get()) if sm == VIDEO_REPLACE_SOURCE_CUSTOM else 0.0
                if sm == VIDEO_REPLACE_SOURCE_CUSTOM and sec_v < 0:
                    messagebox.showwarning("秒数无效", "起点秒数不能为负数。")
                    return
                if _try_apply_ref(ref, p, start_mode=sm, start_sec=sec_v):
                    try:
                        win.destroy()
                    except Exception:
                        pass
            else:
                d = dir_var.get().strip()
                if d and not os.path.isdir(d):
                    messagebox.showwarning("目录无效", "请填写或选择一个有效的素材目录。")
                    return
                _persist_segment_export_pool()
                try:
                    refresh_timeline_panel_data(None, reset_selection=False)
                except Exception:
                    pass
                try:
                    win.destroy()
                except Exception:
                    pass

        file_row = ctk.CTkFrame(main, fg_color="transparent")
        ctk.CTkLabel(file_row, text="文件", width=52, anchor="w", font=ctk.CTkFont(size=11)).pack(
            side="left", padx=(0, 8)
        )
        ent = ctk.CTkEntry(
            file_row,
            textvariable=path_var,
            placeholder_text="新素材文件路径（可粘贴或浏览）",
            height=32,
        )
        ent.pack(side="left", fill="x", expand=True, padx=(0, 8))

        def browse_file() -> None:
            init_dir = ""
            cur = (ref.current_path or "").strip()
            if cur:
                if os.path.isfile(cur):
                    init_dir = os.path.dirname(os.path.abspath(cur)) or ""
                elif os.path.isdir(cur):
                    init_dir = os.path.abspath(cur)
                else:
                    parent = os.path.dirname(os.path.abspath(cur))
                    if parent and os.path.isdir(parent):
                        init_dir = parent
            kw: Dict[str, Any] = {
                "title": f"槽 {slot_n} — 选择新素材",
                "filetypes": _filetypes_for_ref(ref),
            }
            if init_dir:
                kw["initialdir"] = init_dir
            p = filedialog.askopenfilename(**kw)
            if p:
                path_var.set(p)

        btn_browse_file = ctk.CTkButton(file_row, text="浏览…", width=88, command=browse_file)
        btn_browse_file.pack(side="left")

        dir_block = ctk.CTkFrame(main, fg_color="transparent")

        dir_entry_row = ctk.CTkFrame(dir_block, fg_color="transparent")
        dir_entry_row.pack(fill="x")
        ctk.CTkLabel(dir_entry_row, text="目录", width=52, anchor="w", font=ctk.CTkFont(size=11)).pack(
            side="left", padx=(0, 8)
        )
        dir_ent = ctk.CTkEntry(
            dir_entry_row,
            textvariable=dir_var,
            placeholder_text="导出 MP4 前从此目录为本片段套素材；立即替换请选「单个文件」",
            height=32,
        )
        dir_ent.pack(side="left", fill="x", expand=True, padx=(0, 8))

        def browse_directory() -> None:
            init_dir = ""
            cur = (ref.current_path or "").strip()
            if cur:
                if os.path.isfile(cur):
                    init_dir = os.path.dirname(os.path.abspath(cur)) or ""
                elif os.path.isdir(cur):
                    init_dir = os.path.abspath(cur)
                else:
                    parent = os.path.dirname(os.path.abspath(cur))
                    if parent and os.path.isdir(parent):
                        init_dir = parent
            if not init_dir:
                dv = dir_var.get().strip()
                if dv and os.path.isdir(dv):
                    init_dir = os.path.abspath(dv)
            kw: Dict[str, str] = {"title": f"槽 {slot_n} — 选择素材目录（本片段导出前套用）"}
            if init_dir:
                kw["initialdir"] = init_dir
            p = filedialog.askdirectory(**kw)
            if p:
                dir_var.set(p)

        btn_browse_dir = ctk.CTkButton(dir_entry_row, text="选目录…", width=88, command=browse_directory)
        btn_browse_dir.pack(side="left")

        order_row = ctk.CTkFrame(dir_block, fg_color="transparent")
        order_row.pack(fill="x", pady=(8, 0))
        ctk.CTkLabel(order_row, text="", width=52).pack(side="left", padx=(0, 8))
        order_frame = ctk.CTkFrame(order_row, fg_color="transparent")
        order_frame.pack(side="left", fill="x")
        ctk.CTkLabel(
            order_frame,
            text="本片段导出时选取：",
            font=ctk.CTkFont(size=11),
            anchor="w",
        ).pack(side="left", padx=(0, 10))
        ctk.CTkRadioButton(
            order_frame,
            text="随机",
            variable=seg_order_var,
            value="random",
            font=ctk.CTkFont(size=11),
        ).pack(side="left", padx=(0, 12))
        ctk.CTkRadioButton(
            order_frame,
            text="顺序（按文件名）",
            variable=seg_order_var,
            value="sequential",
            font=ctk.CTkFont(size=11),
        ).pack(side="left")

        sync_mode()
        _sync_replace_src_sec_row()

        def _cancel_replace_dialog() -> None:
            win.destroy()

        def _clear_material_dialog() -> None:
            base_s = draft_root.get().strip()
            dn = (selected_name or "").strip()
            if not clear_material_export_pool_for_ref(
                replace_state, base_s, dn, ref, pool_preset_var.get()
            ):
                return
            try:
                refresh_timeline_panel_data(None, reset_selection=False)
            except Exception:
                pass
            try:
                refresh_timeline_segment_status_if_selected()
            except Exception:
                pass
            try:
                win.destroy()
            except Exception:
                pass

        win.protocol("WM_DELETE_WINDOW", _cancel_replace_dialog)

        footer_row = ctk.CTkFrame(win, fg_color="transparent")
        footer_row.pack(side="bottom", fill="x", padx=16, pady=(8, 14))
        ctk.CTkButton(
            footer_row,
            text="确定",
            width=88,
            fg_color=("#2FA572", "#1D7A4F"),
            hover_color=("#268A5F", "#176642"),
            command=_confirm_replace_dialog,
        ).pack(side="right")
        ctk.CTkButton(
            footer_row,
            text="清除配置",
            width=88,
            fg_color=("gray70", "gray35"),
            command=_clear_material_dialog,
        ).pack(side="right", padx=(0, 10))
        ctk.CTkButton(
            footer_row,
            text="关闭",
            width=88,
            fg_color=("gray70", "gray35"),
            command=_cancel_replace_dialog,
        ).pack(side="right", padx=(0, 10))

        _center_toplevel_on_root(win, root, dlg_w, dlg_h)
        win.after(80, win.lift)

    def open_replace_style_dialog(
        ref: StyleSegmentRef,
        *,
        batch_refs: Optional[List[StyleSegmentRef]] = None,
        track_summary: str = "",
    ) -> None:
        from tkinter import messagebox

        targets = list(batch_refs) if batch_refs else [ref]
        if not targets:
            return
        ref = targets[0]
        batch_mode = len(targets) > 1

        kind = STYLE_KIND_TEXT_EFFECT if ref.track_type == "text" else STYLE_KIND_STICKER
        title = "替换花字" if kind == STYLE_KIND_TEXT_EFFECT else "替换贴纸"
        if batch_mode:
            title = "替换轨道花字" if kind == STYLE_KIND_TEXT_EFFECT else "替换轨道贴纸"
        pool_name = "花字" if kind == STYLE_KIND_TEXT_EFFECT else "贴纸"

        win = ctk.CTkToplevel(root)
        win.title(title)
        dlg_w, dlg_h = 560, (400 if batch_mode else 360)
        win.geometry(f"{dlg_w}x{dlg_h}")
        win.minsize(480, 300)
        win.transient(root)

        main = ctk.CTkFrame(win, fg_color="transparent")
        main.pack(side="top", fill="both", expand=True, padx=16)

        if batch_mode:
            head = (track_summary or f"[{ref.track_type}] {ref.track_name}").strip()
            ctk.CTkLabel(
                main,
                text=head,
                font=ctk.CTkFont(size=14, weight="bold"),
                anchor="w",
            ).pack(fill="x", padx=0, pady=(16, 4))
            ctk.CTkLabel(
                main,
                text=f"将为本轨道 {len(targets)} 个片段统一配置{pool_name}（导出/生成子稿时分别套用）。",
                font=ctk.CTkFont(size=12),
                text_color=("gray35", "gray55"),
                anchor="w",
                wraplength=500,
            ).pack(fill="x", padx=0, pady=(0, 8))
        else:
            ctk.CTkLabel(
                main,
                text=ref.combo_label,
                font=ctk.CTkFont(size=14, weight="bold"),
                anchor="w",
            ).pack(fill="x", padx=0, pady=(16, 4))
            cur_id = (ref.current_resource_id or "").strip()
            ctk.CTkLabel(
                main,
                text=f"当前{pool_name} id: {cur_id or '（无）'}",
                font=ctk.CTkFont(size=12),
                text_color=("gray35", "gray55"),
                anchor="w",
            ).pack(fill="x", padx=0, pady=(0, 8))

        base = draft_root.get().strip()
        parent_json = (
            os.path.join(base, (selected_name or "").strip(), "draft_content.json")
            if base and (selected_name or "").strip()
            else ""
        )
        if kind == STYLE_KIND_TEXT_EFFECT:
            valid_ids, _ = build_text_effect_id_pool(parent_json or "")
            name_map = get_text_effect_display_names(base or None)
        else:
            valid_ids, _ = build_sticker_resource_id_pool(parent_json or "")
            name_map = get_sticker_display_names()
        ctk.CTkLabel(
            main,
            text=f"本机可用{pool_name}池：{len(valid_ids)} 个（导出/生成子稿时套用）",
            font=ctk.CTkFont(size=11),
            text_color=("gray40", "gray60"),
            anchor="w",
        ).pack(fill="x", padx=0, pady=(0, 10))

        _dn = (selected_name or "").strip()
        _pool_all: Dict[str, Dict[str, Any]] = replace_state.get("segment_export_pool") or {}

        def _cfg_for_ref(r: StyleSegmentRef) -> Optional[Dict[str, Any]]:
            if not _dn:
                return None
            k = segment_style_pool_key(_dn, r)
            return normalize_style_pool_config(_pool_all.get(k))

        _cfg0: Optional[Dict[str, Any]] = None
        if batch_mode:
            cfgs = [c for c in (_cfg_for_ref(r) for r in targets) if c]
            if cfgs and all(c == cfgs[0] for c in cfgs):
                _cfg0 = cfgs[0]
        else:
            _cfg0 = _cfg_for_ref(ref)

        mode_var = ctk.StringVar(
            value=_cfg0.get("style_mode", STYLE_MODE_RANDOM) if _cfg0 else STYLE_MODE_RANDOM
        )
        id_var = ctk.StringVar(value=str((_cfg0 or {}).get("style_resource_id") or ""))

        mode_row = ctk.CTkFrame(main, fg_color="transparent")
        mode_row.pack(fill="x", padx=0, pady=(0, 8))
        ctk.CTkLabel(mode_row, text="方式", font=ctk.CTkFont(size=12, weight="bold"), anchor="w").pack(
            side="left", padx=(0, 12)
        )

        id_row = ctk.CTkFrame(main, fg_color="transparent")
        if kind == STYLE_KIND_TEXT_EFFECT:
            pick_labels, pick_label_to_id = build_text_effect_picker_choices(valid_ids, name_map)
        else:
            pick_labels, pick_label_to_id = build_style_resource_picker_choices(valid_ids, name_map)
        pick_var = ctk.StringVar(value=pick_labels[0])

        def _sync_style_id_row(*_args: Any) -> None:
            if mode_var.get() == STYLE_MODE_FIXED:
                id_row.pack(fill="x", padx=0, pady=(4, 4))
            else:
                id_row.pack_forget()

        ctk.CTkRadioButton(
            mode_row,
            text=f"从{pool_name}池随机",
            variable=mode_var,
            value=STYLE_MODE_RANDOM,
            font=ctk.CTkFont(size=12),
            command=_sync_style_id_row,
        ).pack(side="left", padx=(0, 14))
        ctk.CTkRadioButton(
            mode_row,
            text=f"指定{pool_name}",
            variable=mode_var,
            value=STYLE_MODE_FIXED,
            font=ctk.CTkFont(size=12),
            command=_sync_style_id_row,
        ).pack(side="left")

        ctk.CTkLabel(id_row, text="选择", width=52, anchor="w", font=ctk.CTkFont(size=11)).pack(
            side="left", padx=(0, 8)
        )

        def _apply_style_pick_label(label: str) -> None:
            rid = pick_label_to_id.get(label, "")
            if rid:
                id_var.set(rid)
                mode_var.set(STYLE_MODE_FIXED)
                _sync_style_id_row()

        style_pick_menu = ctk.CTkOptionMenu(
            id_row,
            variable=pick_var,
            values=pick_labels if len(pick_labels) > 1 else pick_labels + [f"（无可用{pool_name}）"],
            width=360,
            height=32,
            font=ctk.CTkFont(size=12),
            command=_apply_style_pick_label,
        )
        style_pick_menu.pack(side="left", fill="x", expand=True)

        cur_rid = id_var.get().strip()
        if cur_rid:
            for lab, rid in pick_label_to_id.items():
                if rid == cur_rid:
                    pick_var.set(lab)
                    break
            else:
                if kind == STYLE_KIND_TEXT_EFFECT:
                    pick_var.set(text_effect_picker_label_for_id(cur_rid, name_map))
                else:
                    pick_var.set(style_resource_picker_label_for_id(cur_rid, name_map.get(cur_rid, "")))

        _sync_style_id_row()

        def _persist_style_pool(cfg: Optional[Dict[str, Any]], refs: Optional[List[StyleSegmentRef]] = None) -> None:
            dn = (selected_name or "").strip()
            if not dn:
                return
            apply_refs = refs if refs is not None else targets
            pool: Dict[str, Dict[str, Any]] = replace_state.setdefault("segment_export_pool", {})
            for r in apply_refs:
                k = segment_style_pool_key(dn, r)
                if cfg:
                    pool[k] = dict(cfg)
                else:
                    pool.pop(k, None)
            base_s = draft_root.get().strip()
            if base_s:
                persist_working_export_pool_snapshot(base_s, dn, replace_state)
                persist_active_named_export_pool_preset(base_s, dn, pool_preset_var.get(), replace_state)

        def _confirm_style_dialog() -> None:
            mode = mode_var.get()
            if mode == STYLE_MODE_RANDOM:
                cfg = {"style_kind": kind, "style_mode": STYLE_MODE_RANDOM}
            else:
                rid = id_var.get().strip()
                if not rid:
                    messagebox.showwarning("未选择", f"请从列表中选择要指定的{pool_name}。")
                    return
                if kind == STYLE_KIND_TEXT_EFFECT:
                    if not _subtitle_flower_effect_id_is_usable(rid):
                        messagebox.showwarning(
                            "花字无效",
                            f"id {rid} 不是可用的字幕花字，或未在本机缓存。\n"
                            "可在剪映花字面板预览后点「检测花字池」。",
                        )
                        return
                elif not _sticker_resource_id_is_usable(rid):
                    messagebox.showwarning(
                        "贴纸无效",
                        f"id {rid} 不是可用的贴纸，或未在本机缓存。\n"
                        "可在剪映贴纸面板预览后点「检测贴纸池」。",
                    )
                    return
                cfg = {"style_kind": kind, "style_mode": STYLE_MODE_FIXED, "style_resource_id": rid}
            _persist_style_pool(cfg)
            try:
                refresh_timeline_panel_data(None, reset_selection=False)
            except Exception:
                pass
            try:
                refresh_timeline_segment_status_if_selected()
            except Exception:
                pass
            try:
                win.destroy()
            except Exception:
                pass

        def _clear_style_dialog() -> None:
            base_s = draft_root.get().strip()
            dn = (selected_name or "").strip()
            if not clear_style_export_pool_for_refs(
                replace_state, base_s, dn, targets, pool_preset_var.get()
            ):
                return
            try:
                refresh_timeline_panel_data(None, reset_selection=False)
            except Exception:
                pass
            try:
                refresh_timeline_segment_status_if_selected()
            except Exception:
                pass
            try:
                win.destroy()
            except Exception:
                pass

        def _cancel_style_dialog() -> None:
            win.destroy()

        win.protocol("WM_DELETE_WINDOW", _cancel_style_dialog)

        footer_row = ctk.CTkFrame(win, fg_color="transparent")
        footer_row.pack(side="bottom", fill="x", padx=16, pady=(8, 14))
        ctk.CTkButton(
            footer_row,
            text="确定",
            width=88,
            fg_color=("#2FA572", "#1D7A4F"),
            hover_color=("#268A5F", "#176642"),
            command=_confirm_style_dialog,
        ).pack(side="right")
        ctk.CTkButton(
            footer_row,
            text="清除配置",
            width=88,
            fg_color=("gray70", "gray35"),
            command=_clear_style_dialog,
        ).pack(side="right", padx=(0, 10))
        ctk.CTkButton(
            footer_row,
            text="关闭",
            width=88,
            fg_color=("gray70", "gray35"),
            command=_cancel_style_dialog,
        ).pack(side="right", padx=(0, 10))

        _center_toplevel_on_root(win, root, dlg_w, dlg_h)
        win.after(80, win.lift)

    replace_state["_open_replace_dialog"] = open_replace_material_dialog
    replace_state["_open_style_dialog"] = open_replace_style_dialog

    def _clear_material_config_cb(ref: MediaSegmentRef) -> None:
        base_s = draft_root.get().strip()
        dn = (selected_name or "").strip()
        if not clear_material_export_pool_for_ref(
            replace_state, base_s, dn, ref, pool_preset_var.get()
        ):
            return
        try:
            refresh_timeline_panel_data(None, reset_selection=False)
        except Exception:
            pass
        try:
            refresh_timeline_segment_status_if_selected()
        except Exception:
            pass

    def _clear_style_config_cb(ref: StyleSegmentRef) -> None:
        base_s = draft_root.get().strip()
        dn = (selected_name or "").strip()
        if not clear_style_export_pool_for_refs(
            replace_state, base_s, dn, [ref], pool_preset_var.get()
        ):
            return
        try:
            refresh_timeline_panel_data(None, reset_selection=False)
        except Exception:
            pass
        try:
            refresh_timeline_segment_status_if_selected()
        except Exception:
            pass

    replace_state["_clear_material_config"] = _clear_material_config_cb
    replace_state["_clear_style_config"] = _clear_style_config_cb

    bottom_actions = ctk.CTkFrame(export_strip, fg_color="transparent")
    bottom_actions.pack(fill="both", expand=True)

    pool_preset_suppress: Dict[str, Any] = {"v": False}
    pool_preset_var = ctk.StringVar(value=POOL_EXPORT_PRESET_DEFAULT)

    def _persist_dir_for_ref(
        ref: MediaSegmentRef,
        d: str,
        order: str,
        start_mode: str,
        start_sec: float,
    ) -> bool:
        from tkinter import messagebox

        dn = (selected_name or "").strip()
        base_s = draft_root.get().strip()
        if not dn:
            messagebox.showwarning("拖放", "请先在左侧选择草稿。")
            return False
        if not base_s:
            messagebox.showwarning("拖放", "请先设置有效的草稿根目录。")
            return False
        d_abs = os.path.abspath(d)
        if not os.path.isdir(d_abs):
            messagebox.showwarning("目录无效", "拖入的路径不是有效的文件夹。")
            return False
        k = segment_export_pool_key(dn, ref)
        pool: Dict[str, Dict[str, Any]] = replace_state.setdefault("segment_export_pool", {})
        od = order if order in ("random", "sequential") else "random"
        sm = normalize_replace_source_start_mode(start_mode)
        sec_v = (
            float(parse_replace_source_start_sec(start_sec))
            if sm == VIDEO_REPLACE_SOURCE_CUSTOM
            else 0.0
        )
        pool[k] = {
            "dir": d_abs,
            "order": od,
            "replace_source_start_mode": sm,
            "replace_source_start_sec": sec_v,
        }
        try:
            persist_working_export_pool_snapshot(base_s, dn, replace_state)
            persist_active_named_export_pool_preset(base_s, dn, pool_preset_var.get(), replace_state)
        except Exception as e:
            messagebox.showerror("保存失败", str(e))
            return False
        try:
            refresh_timeline_panel_data(None, reset_selection=False)
        except Exception:
            pass
        try:
            refresh_timeline_segment_status_if_selected()
        except Exception:
            pass
        return True

    def _handle_timeline_shell_drop(ref: Optional[MediaSegmentRef], paths: List[str]) -> None:
        from tkinter import messagebox

        if not paths:
            return
        if len(paths) > 1:
            messagebox.showwarning("拖放", "一次请只拖入一个文件或一个文件夹。")
            return
        p = paths[0]
        if not ref:
            messagebox.showwarning(
                "拖放",
                "请将文件或文件夹拖到时间轴上的音视频片段（彩色条）上；"
                "不可替换的轨道片段上无法接收拖放。",
            )
            return
        if not replace_state.get("content_ok") or replace_state.get("encrypted"):
            messagebox.showerror(
                "无法替换",
                "draft_content.json 不可用（未加载或已加密），无法配置替换素材。",
            )
            return
        name = (selected_name or "").strip()
        if not name:
            messagebox.showwarning("拖放", "请先在左侧选择草稿。")
            return
        ck = segment_export_pool_key(name, ref)
        prev: Dict[str, Any] = {}
        raw_pool = replace_state.get("segment_export_pool")
        if isinstance(raw_pool, dict):
            pv = raw_pool.get(ck)
            if isinstance(pv, dict):
                prev = pv
        if os.path.isfile(p):
            sm = normalize_replace_source_start_mode(prev.get("replace_source_start_mode"))
            sec_v = (
                parse_replace_source_start_sec(prev.get("replace_source_start_sec"))
                if sm == VIDEO_REPLACE_SOURCE_CUSTOM
                else 0.0
            )
            _try_apply_ref(ref, p, start_mode=sm, start_sec=sec_v)
        elif os.path.isdir(p):
            od = prev.get("order", "random")
            if od not in ("random", "sequential"):
                od = "random"
            sm = normalize_replace_source_start_mode(prev.get("replace_source_start_mode"))
            sec_v = (
                parse_replace_source_start_sec(prev.get("replace_source_start_sec"))
                if sm == VIDEO_REPLACE_SOURCE_CUSTOM
                else 0.0
            )
            _persist_dir_for_ref(ref, p, od, sm, sec_v)
        else:
            messagebox.showwarning("拖放", "拖入的路径不是有效的文件或文件夹。")

    replace_state["_timeline_shell_drop_handler"] = _handle_timeline_shell_drop

    preset_toolbar = ctk.CTkFrame(preset_toolbar_host, fg_color="transparent")
    preset_toolbar.pack(anchor="ne")

    def _export_pool_preset_name_list(base_s: str, draft_folder_name: str) -> List[str]:
        return export_pool_preset_names_for_draft(base_s, draft_folder_name)

    def _apply_export_pool_preset_choice(choice: str, *, redraw_timeline: bool = True) -> None:
        base_s = draft_root.get().strip()
        dn = (selected_name or "").strip()
        if is_pool_export_default_menu_preset(choice):
            if base_s and dn:
                bkt = (load_export_pool_store(base_s).get("by_draft") or {}).get(dn) or {}
                wp = bkt.get("working_pool")
                if isinstance(wp, dict):
                    seg_wp = wp.get("segment_export_pool")
                    cur_wp = wp.get("export_pool_sequential_cursor")
                    replace_state["segment_export_pool"] = segment_export_pool_enforce_exclusive_sources(
                        dict(seg_wp) if isinstance(seg_wp, dict) else {}
                    )
                    replace_state["export_pool_sequential_cursor"] = _normalize_export_pool_cursor_dict(cur_wp)
                else:
                    replace_state["segment_export_pool"] = {}
                    replace_state["export_pool_sequential_cursor"] = {}
            else:
                replace_state["segment_export_pool"] = {}
                replace_state["export_pool_sequential_cursor"] = {}
        else:
            blob = get_export_pool_preset_blob_for_draft(base_s, dn, choice) if base_s and dn else None
            if not isinstance(blob, dict):
                replace_state["segment_export_pool"] = {}
                replace_state["export_pool_sequential_cursor"] = {}
            else:
                seg = blob.get("segment_export_pool")
                cur = blob.get("export_pool_sequential_cursor")
                replace_state["segment_export_pool"] = segment_export_pool_enforce_exclusive_sources(
                    dict(seg) if isinstance(seg, dict) else {}
                )
                replace_state["export_pool_sequential_cursor"] = {}
                if isinstance(cur, dict):
                    for ck, cv in cur.items():
                        try:
                            replace_state["export_pool_sequential_cursor"][str(ck)] = int(cv)
                        except (TypeError, ValueError):
                            replace_state["export_pool_sequential_cursor"][str(ck)] = 0
        ui_sync = replace_state.get("_on_timeline_selection_ui")
        if callable(ui_sync):
            try:
                ui_sync()
            except Exception:
                pass
        if redraw_timeline:
            try:
                refresh_timeline_panel_data(None, reset_selection=False)
            except Exception:
                pass

    def on_pool_preset_menu_change(choice: str) -> None:
        if pool_preset_suppress["v"]:
            return
        _apply_export_pool_preset_choice(choice)
        persist_export_pool_last_preset_choice(draft_root.get().strip(), (selected_name or "").strip(), choice)

    ctk.CTkLabel(
        preset_toolbar,
        text="槽位预设（按草稿）",
        font=ctk.CTkFont(size=11),
        anchor="w",
        text_color=("gray30", "gray70"),
    ).pack(side="left", padx=(0, 4))
    pool_preset_menu = ctk.CTkOptionMenu(
        preset_toolbar,
        values=[POOL_EXPORT_PRESET_DEFAULT],
        variable=pool_preset_var,
        width=140,
        height=26,
        font=ctk.CTkFont(size=11),
        command=on_pool_preset_menu_change,
    )
    pool_preset_menu.pack(side="left", padx=(0, 4))

    def refresh_export_pool_preset_bar(*, reset_memory: bool = False) -> None:
        base_s = draft_root.get().strip()
        dn = (selected_name or "").strip()
        names = _export_pool_preset_name_list(base_s, dn)
        vals = [POOL_EXPORT_PRESET_DEFAULT] + names
        pool_preset_suppress["v"] = True
        try:
            pool_preset_menu.configure(values=vals)
            if reset_memory or not base_s or not os.path.isdir(base_s):
                pool_preset_var.set(POOL_EXPORT_PRESET_DEFAULT)
        finally:
            pool_preset_suppress["v"] = False
        if reset_memory or not base_s or not os.path.isdir(base_s):
            _apply_export_pool_preset_choice(POOL_EXPORT_PRESET_DEFAULT)

    def sync_export_pool_preset_for_draft(draft_folder_name: str, *, skip_timeline_redraw: bool = False) -> None:
        """切换草稿后：按该稿记录恢复下拉项与上次选用的预设。"""
        base_s = draft_root.get().strip()
        if not base_s or not os.path.isdir(base_s):
            return
        dn = (draft_folder_name or "").strip()
        if not dn:
            return
        names = export_pool_preset_names_for_draft(base_s, dn)
        vals = [POOL_EXPORT_PRESET_DEFAULT] + names
        store = load_export_pool_store(base_s)
        b = (store.get("by_draft") or {}).get(dn) or {}
        last = b.get("last_preset") if isinstance(b, dict) else None
        last = normalize_pool_export_last_preset_value(last)
        if last not in vals:
            last = POOL_EXPORT_PRESET_DEFAULT
        pool_preset_suppress["v"] = True
        try:
            pool_preset_menu.configure(values=vals)
            pool_preset_var.set(last)
        finally:
            pool_preset_suppress["v"] = False
        _apply_export_pool_preset_choice(last, redraw_timeline=not skip_timeline_redraw)

    def on_save_export_pool_preset() -> None:
        from customtkinter import CTkInputDialog
        from tkinter import messagebox

        base_s = draft_root.get().strip()
        if not base_s or not os.path.isdir(base_s):
            messagebox.showwarning("无法保存", "请先设置有效的草稿根目录。")
            return
        dlg = CTkInputDialog(
            text="预设名称（保存当前各槽：素材目录/文件、花字/贴纸随机或指定 id）：",
            title="保存导出槽预设",
        )
        _center_ctk_input_dialog_on_parent(dlg, root)

        def _prefill_preset_name(attempts: int = 0) -> None:
            if attempts > 30:
                return
            try:
                ent = getattr(dlg, "_entry", None)
                if ent is None:
                    dlg.after(15, lambda: _prefill_preset_name(attempts + 1))
                    return
                default_name = (pool_preset_var.get() or "").strip()
                if default_name and not is_pool_export_default_menu_preset(default_name):
                    ent.delete(0, "end")
                    ent.insert(0, default_name)
                    try:
                        ent.select_range(0, "end")
                    except Exception:
                        pass
            except Exception:
                pass

        dlg.after(20, lambda: _prefill_preset_name(0))
        name = (dlg.get_input() or "").strip()
        if not name or is_pool_export_default_menu_preset(name):
            return
        if re.search(r'[<>:"/\\|?*]', name):
            messagebox.showwarning("名称无效", "预设名不能包含下列字符：< > : \" / \\ | ? *")
            return
        dn = (selected_name or "").strip()
        if not dn:
            messagebox.showwarning("无法保存", "请先在左侧列表中选择一个草稿。")
            return
        seg = replace_state.get("segment_export_pool") or {}
        if not isinstance(seg, dict) or not seg:
            messagebox.showinfo(
                "保存预设",
                "当前没有可保存的槽位配置。\n"
                "请为至少一个片段配置「替换素材…」或「替换花字/贴纸…」后再保存。",
            )
            return
        if not _segment_export_pool_has_saveable_config(seg):
            messagebox.showinfo(
                "保存预设",
                "当前没有可保存的槽位配置。\n"
                "请为至少一个片段配置「替换素材…」或「替换花字/贴纸…」后再保存。",
            )
            return
        seg = segment_export_pool_enforce_exclusive_sources(seg)
        replace_state["segment_export_pool"] = seg
        store = load_export_pool_store(base_s)
        bucket = _export_pool_by_draft_bucket_mut(store, dn)
        presets = bucket.setdefault("presets", {})
        if not isinstance(presets, dict):
            bucket["presets"] = {}
            presets = bucket["presets"]
        if name in presets:
            if not messagebox.askyesno("覆盖预设", f"当前草稿下已存在预设「{name}」，是否覆盖？"):
                return
        cur = replace_state.get("export_pool_sequential_cursor") or {}
        cur_out: Dict[str, int] = {}
        if isinstance(cur, dict):
            for ck, cv in cur.items():
                try:
                    cur_out[str(ck)] = int(cv)
                except (TypeError, ValueError):
                    cur_out[str(ck)] = 0
        presets[name] = {
            "segment_export_pool": _segment_export_pool_for_preset_disk(dict(seg)),
            "export_pool_sequential_cursor": cur_out,
        }
        bucket["last_preset"] = name
        save_export_pool_store(base_s, store)
        refresh_export_pool_preset_bar(reset_memory=False)
        pool_preset_suppress["v"] = True
        try:
            pool_preset_var.set(name)
        finally:
            pool_preset_suppress["v"] = False
        persist_working_export_pool_snapshot(base_s, dn, replace_state)

    def on_delete_export_pool_preset() -> None:
        from tkinter import messagebox

        base_s = draft_root.get().strip()
        cur = pool_preset_var.get()
        if not base_s or not os.path.isdir(base_s):
            messagebox.showwarning("无法删除", "请先设置有效的草稿根目录。")
            return
        if is_pool_export_default_menu_preset(cur):
            messagebox.showinfo("删除预设", "请先在列表中选择一个已保存的预设（「(默认)」不可删除）。")
            return
        dn = (selected_name or "").strip()
        if not dn:
            messagebox.showwarning("无法删除", "请先在左侧列表中选择一个草稿。")
            return
        if not messagebox.askyesno("删除预设", f"确定删除预设「{cur}」吗？\n（仅删除本地保存的配置，不影响草稿文件）"):
            return
        store = load_export_pool_store(base_s)
        removed = False
        b = (store.get("by_draft") or {}).get(dn) or {}
        pr = b.get("presets") if isinstance(b, dict) else None
        if isinstance(pr, dict) and cur in pr:
            pr.pop(cur, None)
            removed = True
        if not removed:
            leg = store.get("legacy_presets") or {}
            if isinstance(leg, dict) and cur in leg:
                if not messagebox.askyesno(
                    "删除旧版全局预设",
                    f"「{cur}」来自旧版全局列表（所有草稿共用）。删除后所有草稿的下拉菜单中都不再显示该项。\n\n确定删除？",
                ):
                    return
                leg.pop(cur, None)
                removed = True
        if removed:
            bkt = _export_pool_by_draft_bucket_mut(store, dn)
            bkt["last_preset"] = POOL_EXPORT_PRESET_DEFAULT
            save_export_pool_store(base_s, store)
        else:
            messagebox.showinfo("删除预设", "未找到可删除的预设（可能已被删除）。")
            return
        refresh_export_pool_preset_bar(reset_memory=False)
        pool_preset_suppress["v"] = True
        try:
            pool_preset_var.set(POOL_EXPORT_PRESET_DEFAULT)
        finally:
            pool_preset_suppress["v"] = False
        _apply_export_pool_preset_choice(POOL_EXPORT_PRESET_DEFAULT)

    ctk.CTkButton(
        preset_toolbar,
        text="保存…",
        width=62,
        height=26,
        font=ctk.CTkFont(size=11),
        fg_color=("gray70", "gray35"),
        hover_color=("gray60", "gray28"),
        command=on_save_export_pool_preset,
    ).pack(side="left", padx=(0, 3))
    ctk.CTkButton(
        preset_toolbar,
        text="删除",
        width=48,
        height=26,
        font=ctk.CTkFont(size=11),
        fg_color=("gray70", "gray35"),
        hover_color=("gray60", "gray28"),
        command=on_delete_export_pool_preset,
    ).pack(side="left", padx=(0, 0))
    ctk.CTkLabel(
        preset_toolbar_host,
        text=(
            "「(默认)」＝本稿工作台槽位（可改、会保存到本地）；"
            "命名预设下改动会写回该预设。"
        ),
        font=ctk.CTkFont(size=10),
        text_color=("gray45", "gray62"),
        anchor="e",
        justify="right",
        wraplength=360,
    ).pack(anchor="ne", pady=(3, 0))

    export_row = ctk.CTkFrame(bottom_actions, fg_color="transparent")
    export_row.pack(fill="x", pady=(0, 0))

    export_jianying_cell = ctk.CTkFrame(export_row, fg_color="transparent")
    export_jianying_cell.pack(side="left", anchor="n", padx=(0, 28))

    export_actions = ctk.CTkFrame(export_row, fg_color="transparent")
    export_actions.pack(side="right", anchor="n")

    _exp_ui = load_export_mp4_ui_preferences()
    backup_before_export = ctk.BooleanVar(
        value=_export_ui_pref_bool(_exp_ui, "backup_before_export", False)
    )
    export_generate_subtitles = ctk.BooleanVar(
        value=_export_ui_pref_bool(_exp_ui, "generate_subtitles", False)
    )
    export_mp4_create_child_draft = ctk.BooleanVar(
        value=_export_ui_pref_bool(_exp_ui, "create_child_draft", True)
    )
    export_repeat_var = ctk.StringVar(value=_export_ui_pref_repeat(_exp_ui))
    export_name_prefix_var = ctk.StringVar(value=_export_ui_pref_name_prefix(_exp_ui))

    def _persist_export_mp4_ui_prefs(*_args: Any) -> None:
        try:
            save_export_mp4_ui_preferences(
                {
                    "backup_before_export": bool(backup_before_export.get()),
                    "generate_subtitles": bool(export_generate_subtitles.get()),
                    "create_child_draft": bool(export_mp4_create_child_draft.get()),
                    "export_repeat": export_repeat_var.get().strip() or "1",
                    "name_prefix": export_name_prefix_var.get(),
                }
            )
        except OSError:
            pass

    for _ev in (
        backup_before_export,
        export_generate_subtitles,
        export_mp4_create_child_draft,
        export_repeat_var,
        export_name_prefix_var,
    ):
        _ev.trace_add("write", lambda *_: _persist_export_mp4_ui_prefs())
    _export_busy_widgets: List[Any] = []

    def on_export_mp4() -> None:
        from tkinter import filedialog, messagebox

        if sys.platform != "win32":
            messagebox.showerror("无法导出", "剪映自动化导出仅支持 Windows。")
            return
        name = selected_name
        if not name:
            messagebox.showwarning("未选择草稿", "请先在左侧列表中点击要导出的草稿。")
            return

        base = draft_root.get().strip()
        if not base or not os.path.isdir(base):
            messagebox.showerror("无法导出", "草稿根目录无效。")
            return

        content_json = os.path.join(base, name, "draft_content.json")
        if _file_exists_nonempty(content_json) and _looks_like_jianying_encrypted(content_json):
            if not messagebox.askyesno(
                "可能已是密文",
                "当前草稿的 draft_content.json 看起来已被剪映加密；此时备份也无法得到明文 JSON。\n\n是否仍要继续导出？",
            ):
                return

        raw_n = export_repeat_var.get().strip()
        if not raw_n:
            n_export = 1
        else:
            try:
                n_export = int(raw_n)
            except ValueError:
                messagebox.showwarning("条数无效", "导出条数请填写正整数（留空为 1）。")
                return
        if n_export < 1:
            messagebox.showwarning("条数无效", "导出条数至少为 1。")
            return
        if n_export > 200:
            messagebox.showwarning("条数过大", "单次最多导出 200 条，请改小后重试。")
            return

        preview_prefix = _safe_mp4_name_prefix(export_name_prefix_var.get())
        if n_export == 1:
            name_hint = f"{preview_prefix}1.mp4"
        else:
            name_hint = f"{preview_prefix}1.mp4 ～ {preview_prefix}{n_export}.mp4"
        folder = filedialog.askdirectory(
            title=(
                f"选择导出目录（共 {n_export} 个文件：{name_hint}；"
                f"同名已存在时自动用 {preview_prefix}1_1.mp4 等形式，不覆盖）"
            ),
        )
        if not folder:
            return
        try:
            out_paths = _batch_mp4_paths_with_suffix_on_collision(folder, preview_prefix, n_export)
        except RuntimeError as e:
            messagebox.showerror("无法分配文件名", str(e))
            return

        backup_path: Optional[str] = None
        if backup_before_export.get():
            try:
                backup_path = backup_plaintext_draft(base, name)
            except OSError as e:
                messagebox.showerror("备份失败", f"无法复制明文草稿（将中止导出，以免丢失可编辑副本）：\n{e}")
                return

        jianying_exe_pick = ensure_jianying_exe_for_ui(root)
        if not jianying_exe_pick:
            if not list_jianying_pro_installations():
                messagebox.showerror(
                    "未找到剪映",
                    "未在常见安装路径找到剪映专业版（JianyingPro.exe）。\n"
                    "请确认已安装剪映专业版。",
                )
            else:
                messagebox.showinfo("导出", "已取消选择剪映版本。")
            return

        if not auth_client or not getattr(auth_client, "user_id", None):
            messagebox.showwarning("请先登录", "导出 MP4 需要登录账号。\n请点击窗口顶部「登录」。")
            return
        unit = int(auth_client.get_gold_cost("导出为MP4", default_cost=1))
        total_cost = unit * n_export
        deduct_res = auth_client.record_operation(
            "导出为MP4",
            -total_cost,
            {
                "draft_name": name,
                "export_count": n_export,
                "name_prefix": preview_prefix,
                "create_child_draft": bool(export_mp4_create_child_draft.get()),
            },
        )
        err_deduct = _auth_api_error_message(deduct_res) if _auth_api_error_message else None
        if err_deduct:
            messagebox.showerror("扣减豆子失败", err_deduct)
            return
        refresh_auth_bar()

        gen_subtitles = export_generate_subtitles.get()
        create_child = bool(export_mp4_create_child_draft.get())

        for _bw in _export_busy_widgets:
            try:
                _bw.configure(state="disabled")
            except tk.TclError:
                pass

        def worker() -> None:
            err: Optional[Exception] = None
            used_fx_batch: set[str] = set()
            used_sticker_batch: set[str] = set()
            try:
                from pyJianYingDraft import DraftFolder, ExportFramerate, ExportResolution

                ctrl = wait_jianying_controller_or_launch_process(exe_path=jianying_exe_pick)
                sanitize_replace_state_export_pool_styles(replace_state, base, name, persist=False)
                df = DraftFolder(base) if create_child else None
                need_refresh = False
                last_child: Optional[str] = None
                did_inplace_pool_export = False
                for out_one in out_paths:
                    inplace_backup: Optional[Dict[str, Any]] = None
                    inplace_path: Optional[str] = None
                    if create_child:
                        assert df is not None
                        lineage_parent = _export_parent_for_new_child(name)
                        child_name = _next_generated_child_name(base, lineage_parent)
                        df.duplicate_as_template(name, child_name, allow_replace=False)
                        content_json_c = os.path.join(base, child_name, "draft_content.json")
                        _ensure_jianying_home_before_draft_json_write(ctrl)
                        seg_pool: Dict[str, Dict[str, Any]] = dict(
                            replace_state.get("segment_export_pool") or {}
                        )
                        remapped_pool = remap_draft_keyed_map(seg_pool, name, child_name)
                        raw_cur = remap_draft_keyed_map(
                            replace_state.get("export_pool_sequential_cursor") or {}, name, child_name
                        )
                        cursor_ints: Dict[str, int] = {}
                        for k, v in raw_cur.items():
                            try:
                                cursor_ints[k] = int(v)
                            except (TypeError, ValueError):
                                cursor_ints[k] = 0
                        ok_n, _sk, pool_errs, exp_n = apply_per_segment_export_pools_to_draft(
                            content_json_c,
                            child_name,
                            remapped_pool,
                            cursor_ints,
                        )
                        if exp_n > 0:
                            if ok_n == 0:
                                if pool_errs:
                                    raise RuntimeError("从目录套素材失败：\n" + "\n".join(pool_errs[:12]))
                                raise RuntimeError(
                                    "已有片段配置了导出素材目录，但未能替换任何槽。"
                                    "请确认明文草稿，且各片段对应目录内有与槽类型匹配后缀的素材。"
                                )
                            if pool_errs:
                                raise RuntimeError("从目录套素材失败：\n" + "\n".join(pool_errs[:12]))
                        elif pool_errs:
                            raise RuntimeError("套素材失败：\n" + "\n".join(pool_errs[:12]))
                        style_slot_n = apply_segment_style_pools_or_raise(
                            content_json_c,
                            child_name,
                            remapped_pool,
                            used_fx_batch=used_fx_batch,
                            used_sticker_batch=used_sticker_batch,
                        )
                        if style_slot_n > 0:
                            print(f"[槽位花字/贴纸] {child_name}: {style_slot_n} 个片段")
                        register_child_draft(base, lineage_parent, child_name)
                        merge_remapped_pool_and_cursor_into_replace_state(
                            replace_state, remapped_pool, cursor_ints
                        )
                        draft_to_export = child_name
                    else:
                        draft_to_export = name
                        has_export_pool = draft_has_any_segment_export_pool(
                            name, replace_state.get("segment_export_pool")
                        )
                        need_inplace = has_export_pool
                        if need_inplace:
                            inplace_path = os.path.join(base, name, "draft_content.json")
                            snap = _safe_read_json(inplace_path)
                            if not isinstance(snap, dict):
                                raise RuntimeError(
                                    "无法读取当前草稿的 draft_content.json，已中止导出（避免未还原的改写）。"
                                )
                            inplace_backup = copy.deepcopy(snap)
                            _ensure_jianying_home_before_draft_json_write(ctrl)
                            try:
                                if has_export_pool:
                                    seg_pool_b: Dict[str, Dict[str, Any]] = dict(
                                        replace_state.get("segment_export_pool") or {}
                                    )
                                    raw_cur_b = dict(replace_state.get("export_pool_sequential_cursor") or {})
                                    cursor_b: Dict[str, int] = {}
                                    for k, v in raw_cur_b.items():
                                        try:
                                            cursor_b[k] = int(v)
                                        except (TypeError, ValueError):
                                            cursor_b[k] = 0
                                    ok_nb, _skb, pool_errs_b, exp_nb = apply_per_segment_export_pools_to_draft(
                                        inplace_path,
                                        name,
                                        seg_pool_b,
                                        cursor_b,
                                    )
                                    if exp_nb > 0:
                                        if ok_nb == 0:
                                            if pool_errs_b:
                                                raise RuntimeError(
                                                    "从目录套素材失败：\n" + "\n".join(pool_errs_b[:12])
                                                )
                                            raise RuntimeError(
                                                "已有片段配置了导出素材目录，但未能替换任何槽。"
                                                "请确认明文草稿，且各片段对应目录内有与槽类型匹配后缀的素材。"
                                            )
                                        if pool_errs_b:
                                            raise RuntimeError(
                                                "从目录套素材失败：\n" + "\n".join(pool_errs_b[:12])
                                            )
                                    elif pool_errs_b:
                                        raise RuntimeError("套素材失败：\n" + "\n".join(pool_errs_b[:12]))
                                    merge_remapped_pool_and_cursor_into_replace_state(
                                        replace_state, seg_pool_b, cursor_b
                                    )
                                style_slot_n = apply_segment_style_pools_or_raise(
                                    inplace_path,
                                    name,
                                    seg_pool_b if has_export_pool else dict(
                                        replace_state.get("segment_export_pool") or {}
                                    ),
                                    used_fx_batch=used_fx_batch,
                                    used_sticker_batch=used_sticker_batch,
                                )
                                if style_slot_n > 0:
                                    print(f"[槽位花字/贴纸] {name}: {style_slot_n} 个片段")
                            except Exception:
                                try:
                                    if inplace_backup is not None and inplace_path:
                                        _write_draft_content_json(inplace_path, inplace_backup)
                                except OSError:
                                    pass
                                raise
                    try:
                        ctrl.export_draft(
                            draft_to_export,
                            out_one,
                            resolution=ExportResolution.RES_1080P,
                            framerate=ExportFramerate.FR_30,
                            subtitle_recognition=gen_subtitles,
                            clear_existing_subtitles=True,
                        )
                    finally:
                        if not create_child and inplace_backup is not None and inplace_path:
                            try:
                                _write_draft_content_json(inplace_path, inplace_backup)
                                did_inplace_pool_export = True
                            except OSError as oe:
                                raise RuntimeError(
                                    "导出后还原 draft_content.json 失败，请关闭占用该草稿的剪映窗口后重试：\n"
                                    f"{oe}"
                                ) from oe
                    if create_child:
                        last_child = draft_to_export
                        need_refresh = True
                if need_refresh and last_child:
                    root.after(0, refresh_list)
                    root.after(0, lambda c=last_child: show_draft(c))
                elif did_inplace_pool_export:
                    root.after(0, lambda n=name: show_draft(n))
            except Exception as e:
                err = e

            def finish() -> None:
                for _bw in _export_busy_widgets:
                    try:
                        _bw.configure(state="normal")
                    except tk.TclError:
                        pass
                if err is not None:
                    messagebox.showerror("导出失败", str(err))
                else:
                    if len(out_paths) == 1:
                        lines = [f"视频: {out_paths[0]}"]
                    else:
                        lines = [f"共导出 {len(out_paths)} 条："]
                        lines.extend(f"  · {p}" for p in out_paths)
                    if backup_path:
                        lines.append("")
                        lines.append("明文备份（剪映加密前已复制）:")
                        lines.append(backup_path)
                    msg = "\n".join(lines)

                    done = ctk.CTkToplevel(root)
                    done.title("导出完成")
                    done.transient(root)
                    done.resizable(True, True)
                    done_w, done_h = 520, 320
                    done.geometry(f"{done_w}x{done_h}")
                    done.minsize(400, 220)

                    ctk.CTkLabel(
                        done,
                        text=msg,
                        font=ctk.CTkFont(size=13),
                        anchor="w",
                        justify="left",
                        wraplength=460,
                    ).pack(fill="both", expand=True, padx=20, pady=(18, 12))

                    btn_row = ctk.CTkFrame(done, fg_color="transparent")
                    btn_row.pack(fill="x", padx=20, pady=(0, 16))

                    ctk.CTkButton(
                        btn_row,
                        text="打开导出文件夹",
                        width=148,
                        command=lambda: _open_containing_folder(out_paths[0]),
                    ).pack(side="left", padx=(0, 10))
                    if backup_path:
                        ctk.CTkButton(
                            btn_row,
                            text="打开备份文件夹",
                            width=148,
                            command=lambda bp=backup_path: _open_containing_folder(bp),
                        ).pack(side="left", padx=(0, 10))
                    ctk.CTkButton(btn_row, text="确定", width=90, command=done.destroy).pack(side="right")

                    done.protocol("WM_DELETE_WINDOW", done.destroy)
                    _center_toplevel_on_root(done, root, done_w, done_h)
                    done.after(60, done.lift)

            root.after(0, finish)

        threading.Thread(target=worker, daemon=True).start()

    def on_generate_child_drafts() -> None:
        """按「条数」仅复制底稿为子草稿并套用槽位目录，不选导出目录、不导出 MP4。"""
        from tkinter import messagebox

        name = selected_name
        if not name:
            messagebox.showwarning("未选择草稿", "请先在左侧列表中点击要作为模板的草稿。")
            return

        base = draft_root.get().strip()
        if not base or not os.path.isdir(base):
            messagebox.showerror("无法生成", "草稿根目录无效。")
            return

        content_json = os.path.join(base, name, "draft_content.json")
        if _file_exists_nonempty(content_json) and _looks_like_jianying_encrypted(content_json):
            if not messagebox.askyesno(
                "可能已是密文",
                "当前草稿的 draft_content.json 看起来已被剪映加密，复制后子稿可能无法在时间轴中编辑。\n\n是否仍要继续生成子草稿？",
            ):
                return

        raw_n = export_repeat_var.get().strip()
        if not raw_n:
            n_gen = 1
        else:
            try:
                n_gen = int(raw_n)
            except ValueError:
                messagebox.showwarning("条数无效", "生成条数请填写正整数（留空为 1）。")
                return
        if n_gen < 1:
            messagebox.showwarning("条数无效", "至少生成 1 条。")
            return
        if n_gen > 200:
            messagebox.showwarning("条数过大", "单次最多生成 200 个子草稿，请改小后重试。")
            return

        if not auth_client or not getattr(auth_client, "user_id", None):
            messagebox.showwarning("请先登录", "生成子草稿需要登录账号。")
            return
        unit = int(auth_client.get_gold_cost("生成草稿", default_cost=1))
        total_cost = unit * n_gen
        if not messagebox.askyesno("豆子确认", f"将扣除 {total_cost} 豆子。"):
            return
        deduct_res = auth_client.record_operation(
            "生成草稿",
            -total_cost,
            {"draft_name": name, "child_count": n_gen},
        )
        err_deduct = _auth_api_error_message(deduct_res) if _auth_api_error_message else None
        if err_deduct:
            messagebox.showerror("扣减豆子失败", err_deduct)
            return
        refresh_auth_bar()

        for _bw in _export_busy_widgets:
            try:
                _bw.configure(state="disabled")
            except tk.TclError:
                pass

        def worker_gen() -> None:
            err: Optional[Exception] = None
            created: List[str] = []
            used_fx_batch: set[str] = set()
            used_sticker_batch: set[str] = set()
            try:
                from pyJianYingDraft import DraftFolder

                sanitize_replace_state_export_pool_styles(replace_state, base, name, persist=False)
                df = DraftFolder(base)
                for _i in range(n_gen):
                    lineage_parent = _export_parent_for_new_child(name)
                    child_name = _next_generated_child_name(base, lineage_parent)
                    df.duplicate_as_template(name, child_name, allow_replace=False)
                    content_json_c = os.path.join(base, child_name, "draft_content.json")
                    seg_pool: Dict[str, Dict[str, Any]] = dict(replace_state.get("segment_export_pool") or {})
                    remapped_pool = remap_draft_keyed_map(seg_pool, name, child_name)
                    raw_cur = remap_draft_keyed_map(
                        replace_state.get("export_pool_sequential_cursor") or {}, name, child_name
                    )
                    cursor_ints: Dict[str, int] = {}
                    for k, v in raw_cur.items():
                        try:
                            cursor_ints[k] = int(v)
                        except (TypeError, ValueError):
                            cursor_ints[k] = 0
                    ok_n, _sk, pool_errs, exp_n = apply_per_segment_export_pools_to_draft(
                        content_json_c,
                        child_name,
                        remapped_pool,
                        cursor_ints,
                    )
                    if exp_n > 0:
                        if ok_n == 0:
                            if pool_errs:
                                raise RuntimeError("从目录套素材失败：\n" + "\n".join(pool_errs[:12]))
                            raise RuntimeError(
                                "已有片段配置了导出素材目录，但未能替换任何槽。"
                                "请确认明文草稿，且各片段对应目录内有与槽类型匹配后缀的素材。"
                            )
                        if pool_errs:
                            raise RuntimeError("从目录套素材失败：\n" + "\n".join(pool_errs[:12]))
                    elif pool_errs:
                        raise RuntimeError("套素材失败：\n" + "\n".join(pool_errs[:12]))
                    style_slot_n = apply_segment_style_pools_or_raise(
                        content_json_c,
                        child_name,
                        remapped_pool,
                        used_fx_batch=used_fx_batch,
                        used_sticker_batch=used_sticker_batch,
                    )
                    if style_slot_n > 0:
                        print(f"[槽位花字/贴纸] {child_name}: {style_slot_n} 个片段")
                    register_child_draft(base, lineage_parent, child_name)
                    merge_remapped_pool_and_cursor_into_replace_state(replace_state, remapped_pool, cursor_ints)
                    created.append(child_name)
                if created:
                    last_child = created[-1]
                    root.after(0, refresh_list)
                    root.after(0, lambda c=last_child: show_draft(c))
            except Exception as e:
                err = e

            def finish_gen() -> None:
                for _bw in _export_busy_widgets:
                    try:
                        _bw.configure(state="normal")
                    except tk.TclError:
                        pass
                if err is not None:
                    messagebox.showerror("生成失败", str(err))
                else:
                    preview_lines = "\n".join(f"  · {n}" for n in created[:24])
                    more = f"\n  … 共 {len(created)} 个" if len(created) > 24 else ""
                    messagebox.showinfo(
                        "生成完成",
                        f"已生成 {len(created)} 个子草稿：\n{preview_lines}{more}",
                    )

            root.after(0, finish_gen)

        threading.Thread(target=worker_gen, daemon=True).start()

    def on_replace_material_bar() -> None:
        from tkinter import messagebox

        if timeline_select.get("kind") == "track":
            track_refs = timeline_select.get("track_style_refs")
            if isinstance(track_refs, list) and track_refs:
                od = replace_state.get("_open_style_dialog")
                if callable(od):
                    od(
                        track_refs[0],
                        batch_refs=track_refs,
                        track_summary=str(timeline_select.get("track_summary") or ""),
                    )
                return

        ref = timeline_select.get("replace_ref")
        style_ref = timeline_select.get("style_ref")
        if style_ref is None and timeline_select.get("kind") == "seg":
            raw = timeline_content_cache[0]
            if isinstance(raw, dict):
                try:
                    ti = int(timeline_select["ti"])
                    oi = int(timeline_select["orig_i"])
                    tracks_sorted = sorted(list(raw.get("tracks") or []), key=_track_render_index, reverse=True)
                    if 0 <= ti < len(tracks_sorted):
                        style_ref = _style_segment_ref_from_timeline(raw, tracks_sorted[ti], oi)
                except (TypeError, KeyError, ValueError):
                    pass
        if ref:
            od = replace_state.get("_open_replace_dialog")
            if callable(od):
                od(ref)
            return
        if style_ref:
            od = replace_state.get("_open_style_dialog")
            if callable(od):
                od(style_ref)
            return
        messagebox.showinfo(
            "替换",
            "请先在时间轴上点击选中一个可替换的音视频片段，或选中字幕/贴纸轨道名称后配置花字/贴纸。",
        )

    def sync_replace_material_bar_btn() -> None:
        track_refs = (
            timeline_select.get("track_style_refs")
            if timeline_select.get("kind") == "track"
            else None
        )
        ref = timeline_select.get("replace_ref")
        style_ref = timeline_select.get("style_ref")
        if style_ref is None and timeline_select.get("kind") == "seg":
            raw = timeline_content_cache[0]
            if isinstance(raw, dict):
                try:
                    ti = int(timeline_select["ti"])
                    oi = int(timeline_select["orig_i"])
                    tracks_sorted = sorted(list(raw.get("tracks") or []), key=_track_render_index, reverse=True)
                    if 0 <= ti < len(tracks_sorted):
                        style_ref = _style_segment_ref_from_timeline(raw, tracks_sorted[ti], oi)
                        if style_ref is not None:
                            timeline_select["style_ref"] = style_ref
                except (TypeError, KeyError, ValueError):
                    pass
        ok = bool(
            (ref is not None or style_ref is not None or track_refs)
            and replace_state.get("content_ok")
            and not replace_state.get("encrypted")
            and (selected_name or "").strip()
        )
        try:
            replace_material_bar_btn.configure(state="normal" if ok else "disabled")
        except tk.TclError:
            pass

    def on_pick_jianying_version() -> None:
        from tkinter import messagebox

        if sys.platform != "win32":
            messagebox.showinfo("剪映版本", "当前仅在 Windows 下支持。")
            return
        if not list_jianying_pro_installations():
            messagebox.showerror(
                "未找到剪映",
                "未在常见安装路径找到剪映专业版（JianyingPro.exe）。",
            )
            return
        exe = ensure_jianying_exe_for_ui(root, force_dialog=True)
        if exe:
            messagebox.showinfo("剪映版本", f"已保存将使用的程序：\n{exe}")

    def on_launch_jianying() -> None:
        from tkinter import messagebox

        if sys.platform != "win32":
            messagebox.showinfo("打开剪映", "当前仅在 Windows 下支持从本程序启动剪映专业版。")
            return
        if not list_jianying_pro_installations():
            messagebox.showerror(
                "未找到剪映",
                "未在常见安装路径找到剪映专业版（JianyingPro.exe）。\n"
                "请确认已安装剪映专业版，或从系统开始菜单手动启动。",
            )
            return

        jy_exe = ensure_jianying_exe_for_ui(root)
        if not jy_exe:
            messagebox.showinfo("打开剪映", "已取消。")
            return

        draft_open = (selected_name or "").strip()

        def worker() -> None:
            err: Optional[str] = None
            try:
                _ensure_local_pyjianyingdraft_on_path()
                from pyJianYingDraft.exceptions import AutomationError, DraftNotFound

                if draft_open:
                    ctrl = wait_jianying_controller_or_launch_process(exe_path=jy_exe)
                    ctrl.open_draft_by_name(
                        draft_open,
                        after_click_sleep=8.0,
                        locate_timeout=3.0,
                    )
                else:
                    from pyJianYingDraft.jianying_controller import (
                        jianying_pids_for_executable,
                        wait_for_jianying_controller,
                    )

                    if not jianying_pids_for_executable(jy_exe):
                        if not start_jianying_pro_process(jy_exe):
                            raise OSError("无法启动剪映。")
                    else:
                        try:
                            wait_for_jianying_controller(timeout=8.0, poll=0.4, exe_path=jy_exe)
                        except AutomationError:
                            if not start_jianying_pro_process(jy_exe):
                                raise OSError("无法启动剪映。")
                            wait_for_jianying_controller(timeout=60.0, poll=0.5, exe_path=jy_exe)
            except DraftNotFound:
                err = (
                    f"剪映首页未找到草稿「{draft_open}」。\n"
                    "请确认左侧所选名称与剪映里显示的草稿名一致，并在剪映中刷新草稿列表后再试。"
                )
            except AutomationError as e:
                err = str(e)
            except OSError as e:
                err = str(e)
            except Exception as e:
                err = f"打开剪映失败：{e}"

            def finish() -> None:
                if err:
                    messagebox.showerror("打开剪映", err)

            root.after(0, finish)

        threading.Thread(target=worker, daemon=True).start()

    jy_btn_col = ctk.CTkFrame(export_jianying_cell, fg_color="transparent")
    jy_btn_col.pack(side="left", padx=(0, 0))
    ctk.CTkButton(
        jy_btn_col,
        text="打开剪映",
        height=30,
        width=112,
        fg_color=("#3B8ED0", "#1F538D"),
        hover_color=("#2E7CB8", "#163A6E"),
        command=on_launch_jianying,
    ).pack(anchor="w", pady=(0, 4))
    ctk.CTkButton(
        jy_btn_col,
        text="剪映版本",
        height=26,
        width=112,
        font=ctk.CTkFont(size=11),
        fg_color=("gray70", "gray35"),
        hover_color=("gray60", "gray28"),
        command=on_pick_jianying_version,
    ).pack(anchor="w")

    replace_material_bar_btn = ctk.CTkButton(
        export_actions,
        text="替换…",
        height=30,
        width=112,
        state="disabled",
        fg_color=("#3B8ED0", "#1F538D"),
        hover_color=("#2E7CB8", "#163A6E"),
        command=on_replace_material_bar,
    )
    replace_material_bar_btn.pack(side="left", anchor="n", padx=(0, 12))

    replace_state["_on_timeline_selection_ui"] = sync_replace_material_bar_btn

    export_count_row = ctk.CTkFrame(export_actions, fg_color="transparent")
    export_count_row.pack(side="left", anchor="n", padx=(0, 10))
    ctk.CTkLabel(export_count_row, text="条数", font=ctk.CTkFont(size=11)).pack(side="left", padx=(0, 4))
    ctk.CTkEntry(
        export_count_row,
        textvariable=export_repeat_var,
        width=52,
        height=28,
        placeholder_text="1",
    ).pack(side="left", padx=(0, 10))
    ctk.CTkLabel(export_count_row, text="前缀", font=ctk.CTkFont(size=11)).pack(side="left", padx=(0, 4))
    ctk.CTkEntry(
        export_count_row,
        textvariable=export_name_prefix_var,
        width=120,
        height=28,
        placeholder_text="video_",
    ).pack(side="left")

    _gen_btn_w = 96
    _mp4_btn_w = 188
    _export_btn_row_w = _gen_btn_w + 8 + _mp4_btn_w
    export_mp4_col = ctk.CTkFrame(export_actions, fg_color="transparent")
    export_mp4_col.pack(side="left", anchor="n", padx=(0, 0))
    export_btn_row = ctk.CTkFrame(export_mp4_col, fg_color="transparent")
    export_btn_row.pack(anchor="w", pady=(0, 2))
    generate_drafts_btn = ctk.CTkButton(
        export_btn_row,
        text="生成草稿",
        height=30,
        width=_gen_btn_w,
        fg_color=("#3B8ED0", "#1F538D"),
        hover_color=("#2E7CB8", "#163A6E"),
        command=on_generate_child_drafts,
    )
    generate_drafts_btn.pack(side="left", padx=(0, 8))
    export_btn = ctk.CTkButton(
        export_btn_row,
        text="导出为 MP4…",
        height=30,
        width=_mp4_btn_w,
        fg_color=("#C45C26", "#A34A1E"),
        hover_color=("#A34A1E", "#8B3E18"),
        command=on_export_mp4,
    )
    export_btn.pack(side="left", padx=(0, 0))
    _export_busy_widgets.extend([generate_drafts_btn, export_btn])
    chk_row = ctk.CTkFrame(export_mp4_col, fg_color="transparent")
    chk_row.pack(anchor="w", pady=(0, 0))
    backup_chk = ctk.CTkCheckBox(
        chk_row,
        text="导出前备份明文",
        variable=backup_before_export,
        font=ctk.CTkFont(size=11),
    )
    backup_chk.pack(side="left", padx=(0, 12))
    gen_sub_chk = ctk.CTkCheckBox(
        chk_row,
        text="生成字幕",
        variable=export_generate_subtitles,
        font=ctk.CTkFont(size=11),
    )
    gen_sub_chk.pack(side="left", padx=(0, 12))
    mp4_child_chk = ctk.CTkCheckBox(
        chk_row,
        text="导出生成子草稿",
        variable=export_mp4_create_child_draft,
        font=ctk.CTkFont(size=11),
    )
    mp4_child_chk.pack(side="left", padx=(0, 12))
    _export_busy_widgets.extend([backup_chk, gen_sub_chk, mp4_child_chk])

    draft_buttons: List[Any] = []
    collapsed_parents: set[str] = set()
    _mdl2_chevron = "Segoe MDL2 Assets" in tkfont.families()
    draft_tree_toggle_font = (
        ctk.CTkFont(family="Segoe MDL2 Assets", size=11)
        if _mdl2_chevron
        else ctk.CTkFont(size=12)
    )

    def draft_tree_toggle_symbol(expanded: bool) -> str:
        if _mdl2_chevron:
            return "\uE70D" if expanded else "\uE76C"
        return "\u2304" if expanded else "\u203A"

    def set_path(p: str) -> None:
        nonlocal draft_root
        p = (p or "").strip()
        draft_root.set(p)
        path_entry.delete(0, "end")
        path_entry.insert(0, p)
        if p:
            try:
                save_draft_root_preference(p)
            except OSError:
                pass
        refresh_list()
        refresh_export_pool_preset_bar(reset_memory=True)

    def choose_folder() -> None:
        from tkinter import filedialog

        p = filedialog.askdirectory(title="选择剪映草稿根目录")
        if p:
            set_path(p)

    btn_row = ctk.CTkFrame(left, fg_color="transparent")
    btn_row.pack(fill="x", padx=12, pady=(0, 8))
    ctk.CTkButton(btn_row, text="浏览…", width=100, command=choose_folder).pack(side="left", padx=(0, 8))
    ctk.CTkButton(
        btn_row,
        text="刷新",
        width=72,
        fg_color="transparent",
        border_width=1,
        command=lambda: refresh_list(),
    ).pack(side="left")

    btn_row2 = ctk.CTkFrame(left, fg_color="transparent")
    btn_row2.pack(fill="x", padx=12, pady=(0, 8))
    ctk.CTkButton(
        btn_row2,
        text="生成示例草稿…",
        height=36,
        fg_color=("#2FA572", "#1D7A4F"),
        hover_color=("#268A5F", "#176642"),
        command=lambda: on_generate_sample(),
    ).pack(fill="x")

    btn_row3 = ctk.CTkFrame(left, fg_color="transparent")
    delete_draft_btn = ctk.CTkButton(
        btn_row3,
        text="删除当前草稿…",
        height=32,
        fg_color=("gray55", "gray38"),
        hover_color=("gray45", "gray28"),
        command=lambda: on_delete_current_draft(),
    )
    # 暂不显示删除入口（逻辑保留，需要时恢复 pack 两行即可）
    # btn_row3.pack(fill="x", padx=12, pady=(0, 8))
    # delete_draft_btn.pack(fill="x")

    def on_generate_sample() -> None:
        from tkinter import messagebox

        base = draft_root.get().strip()
        if not base or not os.path.isdir(base):
            messagebox.showerror("无法生成", "请先通过「浏览…」选择有效的剪映草稿根目录（com.lveditor.draft）。")
            return

        missing = check_tutorial_assets()
        if missing:
            messagebox.showerror(
                "缺少例程素材",
                "需要以下文件位于:\n"
                f"{tutorial_assets_dir()}\n\n"
                "缺失: " + ", ".join(missing) + "\n\n请从仓库 readme_assets/tutorial 补齐（见项目说明）。",
            )
            return

        dialog = ctk.CTkInputDialog(text="草稿名称（将新建或覆盖同名文件夹）:", title="生成示例草稿")
        raw = dialog.get_input()
        if raw is None:
            return
        name = _sanitize_draft_name(raw) or _sanitize_draft_name("demo")
        if name is None:
            messagebox.showerror("名称无效", "请使用合法文件夹名，勿含 \\ / : * ? \" < > |")
            return

        draft_path = os.path.join(base, name)
        allow_replace = False
        if os.path.isdir(draft_path):
            if not messagebox.askyesno("覆盖确认", f"已存在「{name}」，是否覆盖？\n（将删除该文件夹下原有内容）"):
                return
            allow_replace = True

        try:
            generate_sample_draft(base, name, allow_replace=allow_replace)
        except FileExistsError:
            messagebox.showerror("生成失败", "同名草稿已存在且未允许覆盖。")
            return
        except Exception as e:
            messagebox.showerror("生成失败", str(e))
            return

        messagebox.showinfo("完成", f"已生成示例草稿「{name}」。\n在剪映中打开前，可先在右侧点击查看明文详情。")
        refresh_list()
        show_draft(name)

    def on_delete_current_draft() -> None:
        from tkinter import messagebox

        base = draft_root.get().strip()
        name = (selected_name or "").strip()
        if not base or not os.path.isdir(base):
            messagebox.showerror("无法删除", "草稿根目录无效。")
            return
        if not name:
            messagebox.showwarning("未选择", "请先在左侧选择要删除的草稿。")
            return
        path = os.path.join(base, name)
        if not os.path.isdir(path):
            messagebox.showerror("无法删除", f"找不到文件夹：\n{path}")
            return

        data = prune_draft_families(base, load_draft_families(base))
        by_parent: Dict[str, List[str]] = dict(data.get("by_parent") or {})
        children_of = list(by_parent.get(name, []))
        parent_of: Optional[str] = None
        for p, kids in by_parent.items():
            if name in kids:
                parent_of = p
                break

        paths_to_trash: List[str] = []
        unregister: str = "none"

        if parent_of is not None:
            if not messagebox.askyesno(
                "删除子草稿",
                f"确定将子草稿「{name}」移入回收站吗？\n\n可从系统回收站还原。",
            ):
                return
            paths_to_trash = [path]
            unregister = "child"
        elif children_of:
            kill_all = messagebox.askyesno(
                "删除父草稿",
                f"「{name}」下挂有 {len(children_of)} 个子草稿。\n\n"
                "选「是」：父与子全部移入回收站\n"
                "选「否」：仅将父草稿移入回收站，子草稿保留为顶层草稿",
            )
            if kill_all:
                for c in children_of:
                    cp = os.path.join(base, c)
                    if os.path.isdir(cp):
                        paths_to_trash.append(cp)
            else:
                if not messagebox.askyesno(
                    "确认",
                    f"将只把父草稿「{name}」移入回收站，子草稿文件夹保留。\n继续？",
                ):
                    return
            paths_to_trash.append(path)
            unregister = "parent"
        else:
            if not messagebox.askyesno(
                "删除草稿",
                f"确定将草稿「{name}」移入回收站吗？\n\n可从系统回收站还原。",
            ):
                return
            paths_to_trash = [path]

        def worker() -> None:
            err: Optional[str] = None
            try:
                _move_paths_to_trash(paths_to_trash)
                if unregister == "child":
                    unregister_child_draft(base, name)
                elif unregister == "parent":
                    unregister_parent_group(base, name)
            except Exception as e:
                err = str(e)

            def finish() -> None:
                try:
                    delete_draft_btn.configure(state="normal")
                except tk.TclError:
                    pass
                if err:
                    messagebox.showerror("删除失败", err)
                refresh_list(reset_list_scroll=True)

            root.after_idle(finish)

        try:
            delete_draft_btn.configure(state="disabled")
        except tk.TclError:
            pass
        threading.Thread(target=worker, daemon=True).start()

    def highlight_selection() -> None:
        for b in draft_buttons:
            kn = getattr(b, "_row_kind", "leaf")
            base_fg = getattr(b, "_base_fg", _DRAFT_LIST_COLORS.get(kn, _DRAFT_LIST_COLORS["leaf"])[0])
            if b._name == selected_name:  # type: ignore[attr-defined]
                b._selected = True  # type: ignore[attr-defined]
                b.configure(fg_color=_DRAFT_LIST_COLORS["selected"][0])
            else:
                b._selected = False  # type: ignore[attr-defined]
                b.configure(fg_color=base_fg)

    def show_draft(folder_name: str) -> None:
        nonlocal selected_name
        selected_name = folder_name
        highlight_selection()
        base = draft_root.get().strip()
        if not base or not os.path.isdir(base):
            detail.delete("1.0", "end")
            detail.insert("1.0", "请先设置有效的草稿根目录。")
            replace_state["refs"] = []
            replace_state["style_refs"] = []
            replace_state["encrypted"] = False
            replace_state["content_ok"] = False
            replace_state["timeline_draft_name"] = ""
            refresh_timeline_panel_data(None)
            return
        replace_state["timeline_draft_name"] = folder_name
        dpath = os.path.join(base, folder_name)
        summary = summarize_draft(dpath)
        detail.delete("1.0", "end")
        detail.insert("1.0", "\n".join(summary.lines))

        replace_state["refs"] = []
        replace_state["style_refs"] = []
        content_path = os.path.join(dpath, "draft_content.json")
        encrypted = _file_exists_nonempty(content_path) and _looks_like_jianying_encrypted(content_path)
        replace_state["encrypted"] = encrypted
        replace_state["content_ok"] = bool(summary.content_ok)
        raw_timeline: Optional[Dict[str, Any]] = None
        if summary.content_ok and not encrypted and isinstance(summary.content, dict):
            raw_timeline = summary.content

        def _finish_draft_load() -> None:
            if selected_name != folder_name:
                return
            sync_export_pool_preset_for_draft(folder_name, skip_timeline_redraw=True)
            refresh_timeline_panel_data(raw_timeline)
            if raw_timeline is not None:

                def _load_replace_refs_bg() -> None:
                    refs: List[Any] = []
                    err_msg: Optional[str] = None
                    try:
                        from pyJianYingDraft.script_file import ScriptFile

                        script = ScriptFile.load_from_parsed_json(raw_timeline, content_path)
                        refs = list_replaceable_media_segments_from_script(script)
                    except Exception as e:
                        err_msg = str(e)

                    def _on_refs_loaded() -> None:
                        if selected_name != folder_name:
                            return
                        if err_msg:
                            replace_state["refs"] = []
                            try:
                                detail.insert("end", f"\n\n【替换音视频槽解析失败】{err_msg}")
                            except tk.TclError:
                                pass
                            return
                        replace_state["refs"] = refs
                        ui_sync = replace_state.get("_on_timeline_selection_ui")
                        if callable(ui_sync):
                            try:
                                ui_sync()
                            except Exception:
                                pass

                    root.after(0, _on_refs_loaded)

                threading.Thread(
                    target=_load_replace_refs_bg,
                    daemon=True,
                    name="draft-refs-load",
                ).start()

        root.after(0, _finish_draft_load)

    def _redraw_list_scroll(*, reset_scroll: bool = False) -> None:
        """CTkScrollableFrame 在子控件批量 destroy/pack 后，内部 Canvas 的 scrollregion 可能不更新，导致列表看起来没刷新。"""
        try:
            list_frame.update_idletasks()
            pc = getattr(list_frame, "_parent_canvas", None)
            if pc is not None:
                pc.update_idletasks()
                bb = pc.bbox("all")
                if bb:
                    pc.configure(scrollregion=bb)
                if reset_scroll:
                    pc.yview_moveto(0)
        except tk.TclError:
            pass
        try:
            root.update_idletasks()
        except tk.TclError:
            pass

    def refresh_list(*, reset_list_scroll: bool = False) -> None:
        nonlocal draft_buttons, selected_name
        prev_selected = selected_name
        for w in list_frame.winfo_children():
            w.destroy()
        draft_buttons = []
        selected_name = None
        replace_state["refs"] = []
        replace_state["style_refs"] = []
        replace_state["encrypted"] = False
        replace_state["content_ok"] = False
        replace_state["timeline_draft_name"] = ""
        refresh_timeline_panel_data(None)

        base = draft_root.get().strip()
        if not base:
            ctk.CTkLabel(list_frame, text="请选择草稿目录").pack(pady=20)
            detail.delete("1.0", "end")
            detail.insert("1.0", "在上方「浏览」中选择剪映草稿文件夹。\n\n常见路径：\n%LOCALAPPDATA%\\JianyingPro\\User Data\\Projects\\com.lveditor.draft")
            _redraw_list_scroll(reset_scroll=reset_list_scroll)
            return
        if not os.path.isdir(base):
            ctk.CTkLabel(list_frame, text="目录无效", text_color="orange").pack(pady=20)
            _redraw_list_scroll(reset_scroll=reset_list_scroll)
            return

        items = list_draft_folders(base)
        if not items:
            ctk.CTkLabel(list_frame, text="（空）").pack(pady=20)
            detail.delete("1.0", "end")
            detail.insert("1.0", "当前根目录下没有草稿文件夹。")
            _redraw_list_scroll(reset_scroll=reset_list_scroll)
            return

        fam = prune_draft_families(base, load_draft_families(base))
        all_names = {n for n, _ in items}
        sync_by_parent_with_folder_name_inference(base, fam, all_names)
        by_parent: Dict[str, List[str]] = dict(fam.get("by_parent") or {})
        child_set: set[str] = set()
        for kids in by_parent.values():
            child_set.update(kids)
        top_level = [n for n in all_names if n not in child_set]
        top_level.sort(key=lambda n: _draft_list_sort_key(base, n), reverse=True)

        def add_leaf_button(container: Any, folder_name: str, *, indent: int) -> None:
            pad_l = 12 + max(0, indent)
            wrap = _draft_list_item_wraplength(indent=indent)
            b = _make_draft_list_click_box(
                container,
                folder_name,
                row_kind="leaf",
                on_click=lambda n=folder_name: show_draft(n),
                wraplength=wrap,
            )
            b.pack(fill="x", pady=2, padx=(pad_l, 4))
            draft_buttons.append(b)

        def render_draft_subtree(folder_name: str, *, indent: int) -> None:
            """递归展示父子草稿（支持 A → A_1 → A_1_1 等多级）。"""
            children = list(by_parent.get(folder_name) or [])
            if children:
                expanded = folder_name not in collapsed_parents
                row = ctk.CTkFrame(list_frame, fg_color="transparent")
                row.pack(fill="x", pady=2, padx=(4 + max(0, indent), 4))

                def _mk_toggle(pn: str = folder_name) -> Any:
                    def _inner() -> None:
                        if pn in collapsed_parents:
                            collapsed_parents.discard(pn)
                        else:
                            collapsed_parents.add(pn)
                        refresh_list()

                    return _inner

                sym = draft_tree_toggle_symbol(expanded)
                ctk.CTkButton(
                    row,
                    text=sym,
                    width=32,
                    height=32,
                    font=draft_tree_toggle_font,
                    command=_mk_toggle(),
                ).pack(side="left", padx=(0, 4))
                mid = ctk.CTkFrame(row, fg_color="transparent")
                mid.pack(side="left", fill="x", expand=True)
                n_sub = len(children)
                wrap = _draft_list_item_wraplength(indent=indent, reserved_right=36)
                pb = _make_draft_list_click_box(
                    mid,
                    folder_name,
                    row_kind="parent",
                    on_click=lambda n=folder_name: show_draft(n),
                    wraplength=wrap,
                    subtitle=f"· {n_sub} 个子稿",
                )
                pb.pack(fill="x")
                draft_buttons.append(pb)

                if expanded:
                    ch_sorted = sorted(children, key=lambda c: _draft_list_sort_key(base, c), reverse=True)
                    for ch in ch_sorted:
                        render_draft_subtree(ch, indent=indent + 8)
            else:
                add_leaf_button(list_frame, folder_name, indent=indent)

        for name in top_level:
            render_draft_subtree(name, indent=0)

        if prev_selected and os.path.isdir(os.path.join(base, prev_selected)):
            show_draft(prev_selected)
        else:
            detail.delete("1.0", "end")
            detail.insert(
                "1.0",
                "请从左侧选择草稿。\n\n"
                "「替换素材」与导出槽位会改当前草稿的素材引用；导出 MP4 仅在勾选「导出生成子草稿」时复制为子稿；"
                "未勾选时临时套用槽位导出后自动还原 draft_content.json。父子关系记在本地应用数据中。",
            )

        _redraw_list_scroll(reset_scroll=reset_list_scroll)

    def _commit_path_entry(_event: Any = None) -> None:
        """路径框手动修改后失焦或按回车时同步到 StringVar 并写入本地偏好。"""
        p = path_entry.get().strip()
        if p == (draft_root.get() or "").strip():
            return
        draft_root.set(p)
        if p:
            try:
                save_draft_root_preference(p)
            except OSError:
                pass
        refresh_list()
        refresh_export_pool_preset_bar(reset_memory=True)

    path_entry.bind("<Return>", lambda _e: _commit_path_entry())
    path_entry.bind("<FocusOut>", lambda _e: _commit_path_entry())

    # init path
    if draft_root.get():
        path_entry.insert(0, draft_root.get())
    refresh_list()
    refresh_export_pool_preset_bar(reset_memory=True)
    try:
        sync_harvested_text_effects_to_pool_file()
    except OSError:
        try:
            ensure_text_effect_pool_template_file()
        except OSError:
            pass
    try:
        _st_added, _st_pruned, _st_path = sync_harvested_stickers_to_pool_file()
        if _st_pruned > 0:
            print(f"[贴纸] 启动：已从配置文件清理 {_st_pruned} 个无效 id")
    except OSError:
        try:
            ensure_sticker_pool_template_file()
        except OSError:
            pass
    try:
        print_text_effect_pool_startup_summary()
        rep_st = build_sticker_pool_report(resync=False)
        print(
            f"[贴纸] 启动：可用 {rep_st.get('valid_count', 0)} 个"
            f"（配置 {rep_st.get('listed_count', 0)} 个 id）"
        )
        print(f"[贴纸] 配置：{rep_st.get('pool_path', '')}")
    except OSError:
        pass

    from tkinter import messagebox as _mb_startup

    root.update()
    root.update_idletasks()
    if not auth_client:
        _mb_startup.showerror(
            "无法启动",
            "认证模块不可用。\n请执行 pip install requests，并从仓库根目录运行本程序。",
            parent=root,
        )
        root.destroy()
        return
    if not open_auth_dialog(mandatory=True):
        root.destroy()
        return
    refresh_auth_bar()
    root.mainloop()


if __name__ == "__main__":
    run_app()
