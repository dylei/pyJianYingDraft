"""
爆款智剪 — 左侧草稿列表，右侧详情与时间轴预览（轨道与片段按时间排列）；
明文 draft_content.json 下可在时间轴音视频片段上右键「替换素材…」弹窗替换（按原片段时长截断或缩短）；
Windows 下可将单个素材文件或素材文件夹从资源管理器拖到时间轴片段彩色条上，效果与弹窗中保存「单个文件」或「素材目录」一致（需安装 windnd）；
每个导出槽位仅保留最后一次配置：「单个文件」与「素材目录」互斥，后保存的生效；可设新素材截取起点（片头 / 随机 / 自定义秒）。
下拉「(默认)」表示使用本稿槽位工作台（working_pool），与命名预设一样可编辑并持久化到本地；旧版曾显示为「(保持原样)」，程序会自动识别。命名预设下改动会写回该预设。「导出生成子草稿」默认勾选：导出 MP4 时复制为子草稿并在子稿上套用预设，底稿不动；取消勾选时仍会在**每次导出前**对当前草稿临时套用槽位再导出，随后**自动还原** draft_content.json，不增加子文件夹（与「生成草稿」按钮无关，该按钮仍会复制子稿）。
父子关系索引与导出 MP4 区选项（备份、字幕、子草稿、条数、文件名前缀等）记忆在 %LOCALAPPDATA%\\pyJianYingDraft_browser\\（export_mp4_ui_preference.json），草稿文件夹仍在剪映根目录下平铺。
音频槽选视频时自动用 ffmpeg 抽音轨为 MP3。
运行: pip install customtkinter Send2Trash requests windnd && python draft_browser_app.py
"""

from __future__ import annotations

import hashlib
import json
import copy
import os
import random
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
from typing import Any, Dict, List, Optional, Tuple

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


def segment_export_pool_key(draft_name: str, ref: MediaSegmentRef) -> str:
    """按草稿名 + 轨道 id + 片段下标定位（轨道名为空时也不冲突）。无 track_id 时回退旧格式。"""
    tid = (ref.track_id or "").strip()
    if tid:
        return f"{draft_name}\0{tid}\0{ref.segment_index}"
    return f"{draft_name}\0{ref.track_type}\0{ref.track_name}\0{ref.track_type_index}\0{ref.segment_index}"


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
    """根据本地 segment_export_pool 生成「替换目录/替换文件」说明行（用于时间轴下方信息区）。"""
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
    """该草稿在 segment_export_pool 中是否配置了替换目录或单个替换文件（导出 MP4 时可套用）。"""
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
    return False


def _segment_export_pool_for_preset_disk(seg_in: Dict[str, Any]) -> Dict[str, Dict[str, Any]]:
    """写入命名预设时保留「素材目录」与「单个替换文件」路径（供导出/生成子稿套用）。"""
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
        return DraftSummary(name, draft_dir, meta is not None, False, lines)

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

    return DraftSummary(name, draft_dir, meta is not None, True, lines)


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


def _compute_cover_uniform_zoom(canvas_w: int, canvas_h: int, mat_w: int, mat_h: int) -> float:
    """相对剪映默认「整段素材完整放进画布」的缩放，再放大到 **cover 铺满** 所需的等比倍数。

    即 ``max(cw/mw, ch/mh) / min(cw/mw, ch/mh)``，与 ``object-fit: cover`` / contain 的缩放比一致；
    宽高比已与画布一致时为 ``1.0``。不依赖「先按宽铺满」的假设，避免与部分草稿/版本语义不一致。
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
    mat_w: int,
    mat_h: int,
) -> None:
    """替换素材后重写片段 ``clip``：等比铺满画布（cover）；旋转归零；去掉与缩放/位置冲突的关键帧。

    缩放取相对「完整放入」的倍数，位移默认 ``0``（由剪映按 cover 裁切居中）；若仍错位可再调位移公式。
    """
    raw = getattr(seg, "raw_data", None)
    if not isinstance(raw, dict):
        return
    zoom = _compute_cover_uniform_zoom(canvas_w, canvas_h, mat_w, mat_h)
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

    **视频轨**：替换后会按画布与素材像素尺寸重写 ``clip``（**cover**：相对「完整放入」的等比放大倍数；兼容 ``transform.scale`` 嵌套结构；位移默认 0；旋转归零并清理冲突关键帧）。

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
            _patch_replaced_video_segment_clip_center_cover(
                seg_done,
                canvas_w=int(script.width),
                canvas_h=int(script.height),
                mat_w=mw,
                mat_h=mh,
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
    """先等待已运行的剪映窗口；若未找到（剪映未开）则拉起指定安装后再等到窗口可用。"""
    _ensure_local_pyjianyingdraft_on_path()
    from pyJianYingDraft.exceptions import AutomationError
    from pyJianYingDraft.jianying_controller import wait_for_jianying_controller

    try:
        return wait_for_jianying_controller(timeout=first_wait_s, poll=0.4)
    except AutomationError:
        if not start_jianying_pro_process(exe_path):
            raise AutomationError("无法启动剪映进程。")
        return wait_for_jianying_controller(timeout=after_launch_wait_s, poll=0.5)


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
        seg: Dict[str, Dict[str, Any]] = {}
        if isinstance(seg_in, dict):
            for sk, sv in seg_in.items():
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
                if piece:
                    seg[str(sk)] = piece
        cur: Dict[str, int] = {}
        if isinstance(cur_in, dict):
            for ck, cv in cur_in.items():
                try:
                    cur[str(ck)] = int(cv)
                except (TypeError, ValueError):
                    cur[str(ck)] = 0
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
    has_slot = False
    for _k, sv in seg.items():
        if not isinstance(sv, dict):
            continue
        if str(sv.get("dir", "") or "").strip() or str(sv.get("replace_file", "") or "").strip():
            has_slot = True
            break
    if not has_slot:
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


def _timeline_segment_label(seg: Dict[str, Any], materials: Dict[str, Any]) -> str:
    mid = (seg.get("material_id") or "").strip()
    mats = materials if isinstance(materials, dict) else {}
    for key in ("videos", "audios", "texts"):
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
    draft_nm = (replace_state.get("timeline_draft_name") or "").strip()
    pool_ui: Dict[str, Any] = replace_state.get("segment_export_pool") or {}
    if not isinstance(pool_ui, dict):
        pool_ui = {}
    rep_lines = segment_replace_status_lines(draft_nm, ref, pool_ui)
    src_path = ""
    if ref and (ref.current_path or "").strip():
        src_path = ref.current_path.strip()
    elif str(tr.get("type", "")) in ("video", "audio"):
        src_path = _local_media_path_for_segment(seg, materials)
    main_lines: List[str] = [
        f"已选片段：{tr.get('name')} [{tr.get('type')}] · 时间序第 {vis_i + 1} 段 · "
        f"{st/1e6:.2f}s—{(st+du)/1e6:.2f}s · {lab}",
    ]
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

    total_us = _timeline_end_us(content)
    total_sec = total_us / 1_000_000.0
    time_px = max(int(total_sec * pixels_per_second), 280)
    label_w = 118
    ruler_h = 28
    row_h = 34
    row_gap = 5
    pad = 6
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
        _set_status(f"已选轨道：{tr.get('name')} [{tr.get('type')}] · 共 {nseg} 个片段", replace_highlight="")
        apply_selection_visual()
        _notify_timeline_selection_ui()

    def on_select_seg(ti: int, vis_i: int, orig_i: int) -> None:
        tr = tracks_sorted[ti]
        sel["kind"] = "seg"
        sel["ti"] = ti
        sel["vis_i"] = vis_i
        sel["orig_i"] = orig_i
        refs_list = rs.get("refs") or []
        ref = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i, content)
        if ref is not None:
            sel["replace_ref"] = ref
        else:
            sel.pop("replace_ref", None)
        content_for_status: Dict[str, Any] = content if isinstance(content, dict) else {}
        parts = timeline_segment_selection_status_parts(
            content_for_status, ti=ti, vis_i=vis_i, orig_i=orig_i, replace_state=rs
        )
        if parts is not None:
            _set_status(parts[0], replace_highlight=parts[1])
        apply_selection_visual()
        _notify_timeline_selection_ui()

    def on_seg_context_menu(event: Any, ti: int, vis_i: int, orig_i: int) -> None:
        from tkinter import Menu

        tr = tracks_sorted[ti]
        refs_list = rs.get("refs") or []
        ref = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i, content)
        m = Menu(canvas, tearoff=0, bg="#2b2b2b", fg="#e0e0e0", activebackground="#3d3d3d")

        def _open_replace_win() -> None:
            if not ref:
                return
            on_select_seg(ti, vis_i, orig_i)
            od = rs.get("_open_replace_dialog")
            if callable(od):
                od(ref)

        if ref:
            m.add_command(label="替换素材…", command=_open_replace_win)
        else:
            m.add_command(label="（此片段无对应音视频替换槽）", state="disabled")
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
    step_us = 1_000_000
    t = 0
    while t <= total_us:
        x = _x_for_us(t)
        sec = t // 1_000_000
        is_major = sec % 5 == 0
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
            if x2 - x1 < 2:
                x2 = x1 + 2
            tag_s = f"sid{ti}_{orig_i}"
            seg_fill, seg_text = fill_c, text_c
            r_here = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i, content)
            if draft_nm and segment_has_replace_config(draft_nm, r_here, pool_ui):
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
            title = f"#{vis_i + 1} {lab}"
            if x2 - x1 > 52:
                canvas.create_text(
                    (x1 + x2) / 2,
                    y + row_h // 2,
                    text=title[:24] + ("…" if len(title) > 24 else ""),
                    fill=seg_text,
                    font=("Segoe UI", 8),
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
    if sel.get("kind") == "none":
        _set_status(
            "提示：点击左侧轨道名选中轨道；点击彩色条选中片段；音视频片段可右键「替换素材…」"
            "（Windows 下也可将单个文件或素材文件夹从资源管理器拖到片段条上，与弹窗保存一致）。"
            " 时间轴区域点一下后可用方向键：左右切换同轨片段，上下换轨（保持同序）且横滚对齐片段左缘；"
            "轨道多时可滚轮上下浏览或拖右侧竖条；Ctrl+滚轮或标题栏「+/−」横向缩放。",
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
    win_w, win_h = 1100, 800
    root.minsize(880, 560)
    root.geometry(f"{win_w}x{win_h}")
    root.update_idletasks()
    _center_window_on_screen(root, win_w, win_h)

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
    top_bar.pack(fill="x", padx=12, pady=(8, 0))
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
    main.pack(fill="both", expand=True, padx=12, pady=(4, 12))

    left = ctk.CTkFrame(main, width=280, corner_radius=12)
    left.pack(side="left", fill="y", padx=(0, 10))
    left.pack_propagate(False)

    right = ctk.CTkFrame(main, corner_radius=12)
    right.pack(side="left", fill="both", expand=True)
    right.grid_columnconfigure(0, weight=1)
    # 草稿信息 : 时间轴 : 导出区 = 2 : 9 : 2（时间轴占更多纵向空间）
    right.grid_rowconfigure(0, weight=2, uniform="right_stack", minsize=64)
    right.grid_rowconfigure(1, weight=9, uniform="right_stack", minsize=220)
    right.grid_rowconfigure(2, weight=2, uniform="right_stack", minsize=72)

    ctk.CTkLabel(left, text="草稿箱", font=ctk.CTkFont(size=18, weight="bold")).pack(anchor="w", padx=14, pady=(14, 6))

    path_entry = ctk.CTkEntry(left, placeholder_text="草稿根目录…", height=32)
    path_entry.pack(fill="x", padx=12, pady=(0, 8))

    list_frame = ctk.CTkScrollableFrame(left, label_text="草稿列表", corner_radius=10)
    list_frame.pack(fill="both", expand=True, padx=8, pady=(0, 12))

    detail = ctk.CTkTextbox(right, font=ctk.CTkFont(family="Consolas", size=13), wrap="word")
    detail.grid(row=0, column=0, sticky="nsew", padx=12, pady=(12, 6))

    timeline_block = ctk.CTkFrame(right, fg_color="transparent")
    timeline_block.grid(row=1, column=0, sticky="nsew", padx=12, pady=(0, 4))
    timeline_block.grid_columnconfigure(0, weight=1)
    timeline_block.grid_rowconfigure(0, weight=0)
    timeline_block.grid_rowconfigure(1, weight=1)
    timeline_block.grid_rowconfigure(2, weight=0)

    DEFAULT_TIMELINE_PPS = 68.0
    timeline_content_cache: List[Optional[Dict[str, Any]]] = [None]
    timeline_zoom: Dict[str, float] = {"pps": DEFAULT_TIMELINE_PPS}
    timeline_zoom_label_var = ctk.StringVar(value="缩放 100%")

    replace_state: Dict[str, Any] = {
        "refs": [],
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
        text="时间轴预览（可点击左侧轨道名或片段时间条进行选择）",
        font=ctk.CTkFont(size=14, weight="bold"),
        anchor="w",
    ).grid(row=0, column=0, sticky="w")

    zoom_bar = ctk.CTkFrame(timeline_header, fg_color="transparent")
    zoom_bar.grid(row=0, column=1, sticky="e", padx=(8, 0))
    ctk.CTkLabel(zoom_bar, text="横向缩放", font=ctk.CTkFont(size=11), text_color=("gray45", "gray60")).pack(
        side="left", padx=(0, 6)
    )

    def refresh_timeline_panel_data(raw: Optional[Dict[str, Any]] = None, *, reset_selection: bool = True) -> None:
        if raw is not None:
            timeline_content_cache[0] = raw
            timeline_zoom["pps"] = DEFAULT_TIMELINE_PPS
        elif reset_selection:
            timeline_content_cache[0] = None
        if reset_selection:
            timeline_select.clear()
            timeline_select.update({"kind": "none", "ti": None, "si": None, "summary": ""})

        pct = int(round(100.0 * timeline_zoom["pps"] / DEFAULT_TIMELINE_PPS))
        timeline_zoom_label_var.set(f"缩放 {pct}%")

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

    timeline_inner = ctk.CTkFrame(timeline_block, fg_color=("gray92", "gray20"), corner_radius=8)
    timeline_inner.grid(row=1, column=0, sticky="nsew", pady=(4, 0))

    timeline_select: Dict[str, Any] = {"kind": "none", "ti": None, "si": None, "summary": ""}
    timeline_status_area = ctk.CTkFrame(timeline_block, fg_color="transparent")
    timeline_status_area.grid(row=2, column=0, sticky="ew", padx=4, pady=(4, 0))
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
        height=80,
        width=80,
        font=ctk.CTkFont(size=11),
        text_color=("gray40", "gray60"),
        fg_color="transparent",
        border_width=0,
        corner_radius=0,
        activate_scrollbars=False,
        wrap="word",
        takefocus=False,
    )
    timeline_sel_label.grid(row=0, column=0, sticky="ew")

    timeline_replace_highlight_label = ctk.CTkTextbox(
        timeline_status_left,
        height=52,
        width=80,
        font=ctk.CTkFont(size=11),
        text_color=("#2dd48f", "#5ee9ad"),
        fg_color="transparent",
        border_width=0,
        corner_radius=0,
        activate_scrollbars=False,
        wrap="word",
        takefocus=False,
    )
    timeline_replace_highlight_label.grid(row=1, column=0, sticky="ew", pady=(2, 0))

    _hint0 = (
        "提示：点击左侧轨道名选中轨道；点击彩色条选中片段；音视频片段可右键「替换素材…」"
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
    export_strip.grid(row=2, column=0, sticky="nsew", padx=12, pady=(4, 12))
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
            text="关闭",
            width=88,
            fg_color=("gray70", "gray35"),
            command=_cancel_replace_dialog,
        ).pack(side="right", padx=(0, 10))

        _center_toplevel_on_root(win, root, dlg_w, dlg_h)
        win.after(80, win.lift)

    replace_state["_open_replace_dialog"] = open_replace_material_dialog

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

    def _apply_export_pool_preset_choice(choice: str) -> None:
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

    def sync_export_pool_preset_for_draft(draft_folder_name: str) -> None:
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
        _apply_export_pool_preset_choice(last)

    def on_save_export_pool_preset() -> None:
        from customtkinter import CTkInputDialog
        from tkinter import messagebox

        base_s = draft_root.get().strip()
        if not base_s or not os.path.isdir(base_s):
            messagebox.showwarning("无法保存", "请先设置有效的草稿根目录。")
            return
        dlg = CTkInputDialog(
            text="预设名称（保存当前各槽的目录/顺序与单个替换文件）：",
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
                "当前没有可保存的槽位配置。\n请在「替换素材…」中为至少一个片段指定「素材目录」或「单个文件」后再保存。",
            )
            return
        has_slot = False
        for _k, sv in seg.items():
            if not isinstance(sv, dict):
                continue
            if str(sv.get("dir", "") or "").strip() or str(sv.get("replace_file", "") or "").strip():
                has_slot = True
                break
        if not has_slot:
            messagebox.showinfo(
                "保存预设",
                "当前没有可保存的槽位配置。\n请在「替换素材…」中为至少一个片段指定「素材目录」或「单个文件」后再保存。",
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
        if not messagebox.askyesno("豆子确认", f"将扣除 {total_cost} 豆子。"):
            return
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

        for _bw in _export_busy_widgets:
            try:
                _bw.configure(state="disabled")
            except tk.TclError:
                pass

        gen_subtitles = export_generate_subtitles.get()
        create_child = bool(export_mp4_create_child_draft.get())

        def worker() -> None:
            err: Optional[Exception] = None
            try:
                from pyJianYingDraft import DraftFolder, ExportFramerate, ExportResolution

                ctrl = wait_jianying_controller_or_launch_process(exe_path=jianying_exe_pick)
                df = DraftFolder(base) if create_child else None
                need_refresh = False
                last_child: Optional[str] = None
                did_inplace_pool_export = False
                for out_one in out_paths:
                    inplace_backup: Optional[Dict[str, Any]] = None
                    inplace_path: Optional[str] = None
                    if create_child:
                        assert df is not None
                        lineage_parent = resolve_lineage_parent_for_nested_draft(base, name)
                        child_name = _next_generated_child_name(base, lineage_parent)
                        df.duplicate_as_template(name, child_name, allow_replace=False)
                        content_json_c = os.path.join(base, child_name, "draft_content.json")
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
                        register_child_draft(base, lineage_parent, child_name)
                        merge_remapped_pool_and_cursor_into_replace_state(
                            replace_state, remapped_pool, cursor_ints
                        )
                        draft_to_export = child_name
                    else:
                        draft_to_export = name
                        if draft_has_any_segment_export_pool(name, replace_state.get("segment_export_pool")):
                            inplace_path = os.path.join(base, name, "draft_content.json")
                            snap = _safe_read_json(inplace_path)
                            if not isinstance(snap, dict):
                                raise RuntimeError(
                                    "无法读取当前草稿的 draft_content.json，已中止导出（避免未还原的改写）。"
                                )
                            inplace_backup = copy.deepcopy(snap)
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
                            try:
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
            try:
                from pyJianYingDraft import DraftFolder

                df = DraftFolder(base)
                for _i in range(n_gen):
                    lineage_parent = resolve_lineage_parent_for_nested_draft(base, name)
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

        ref = timeline_select.get("replace_ref")
        if not ref:
            messagebox.showinfo("替换素材", "请先在时间轴上点击选中一个可替换的音视频片段。")
            return
        od = replace_state.get("_open_replace_dialog")
        if not callable(od):
            return
        od(ref)

    def sync_replace_material_bar_btn() -> None:
        ref = timeline_select.get("replace_ref")
        ok = bool(
            ref is not None
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
                    if not launch_jianying_pro(jy_exe):
                        raise OSError("无法启动剪映。")
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
        height=34,
        width=112,
        fg_color=("#3B8ED0", "#1F538D"),
        hover_color=("#2E7CB8", "#163A6E"),
        command=on_launch_jianying,
    ).pack(anchor="w", pady=(0, 6))
    ctk.CTkButton(
        jy_btn_col,
        text="剪映版本",
        height=28,
        width=112,
        font=ctk.CTkFont(size=11),
        fg_color=("gray70", "gray35"),
        hover_color=("gray60", "gray28"),
        command=on_pick_jianying_version,
    ).pack(anchor="w")

    replace_material_bar_btn = ctk.CTkButton(
        export_actions,
        text="替换素材…",
        height=34,
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
    ctk.CTkLabel(export_count_row, text="条数", font=ctk.CTkFont(size=12)).pack(side="left", padx=(0, 6))
    ctk.CTkEntry(
        export_count_row,
        textvariable=export_repeat_var,
        width=52,
        height=30,
        placeholder_text="1",
    ).pack(side="left", padx=(0, 12))
    ctk.CTkLabel(export_count_row, text="前缀", font=ctk.CTkFont(size=12)).pack(side="left", padx=(0, 6))
    ctk.CTkEntry(
        export_count_row,
        textvariable=export_name_prefix_var,
        width=120,
        height=30,
        placeholder_text="video_",
    ).pack(side="left")

    _gen_btn_w = 96
    _mp4_btn_w = 188
    _export_btn_row_w = _gen_btn_w + 8 + _mp4_btn_w
    export_mp4_col = ctk.CTkFrame(export_actions, fg_color="transparent")
    export_mp4_col.pack(side="left", anchor="n", padx=(0, 0))
    export_btn_row = ctk.CTkFrame(export_mp4_col, fg_color="transparent")
    export_btn_row.pack(anchor="w", pady=(0, 4))
    generate_drafts_btn = ctk.CTkButton(
        export_btn_row,
        text="生成草稿",
        height=34,
        width=_gen_btn_w,
        fg_color=("#3B8ED0", "#1F538D"),
        hover_color=("#2E7CB8", "#163A6E"),
        command=on_generate_child_drafts,
    )
    generate_drafts_btn.pack(side="left", padx=(0, 8))
    export_btn = ctk.CTkButton(
        export_btn_row,
        text="导出为 MP4…",
        height=34,
        width=_mp4_btn_w,
        fg_color=("#C45C26", "#A34A1E"),
        hover_color=("#A34A1E", "#8B3E18"),
        command=on_export_mp4,
    )
    export_btn.pack(side="left", padx=(0, 0))
    _export_busy_widgets.extend([generate_drafts_btn, export_btn])
    chk_row = ctk.CTkFrame(export_mp4_col, fg_color="transparent")
    chk_row.pack(anchor="w", pady=(0, 2))
    backup_chk = ctk.CTkCheckBox(
        chk_row,
        text="导出前备份明文",
        variable=backup_before_export,
        font=ctk.CTkFont(size=12),
    )
    backup_chk.pack(side="left", padx=(0, 18))
    gen_sub_chk = ctk.CTkCheckBox(
        chk_row,
        text="生成字幕",
        variable=export_generate_subtitles,
        font=ctk.CTkFont(size=12),
    )
    gen_sub_chk.pack(side="left", padx=(0, 18))
    mp4_child_chk = ctk.CTkCheckBox(
        chk_row,
        text="导出生成子草稿",
        variable=export_mp4_create_child_draft,
        font=ctk.CTkFont(size=12),
    )
    mp4_child_chk.pack(side="left")
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
            if b._name == selected_name:  # type: ignore[attr-defined]
                b.configure(fg_color=("#3B8ED0", "#1F538D"))
            elif kn == "parent":
                b.configure(fg_color=("gray78", "gray22"), hover_color=("gray68", "gray32"))
            else:
                b.configure(fg_color=("gray80", "gray20"), hover_color=("gray70", "gray30"))

    def show_draft(folder_name: str) -> None:
        nonlocal selected_name
        selected_name = folder_name
        highlight_selection()
        base = draft_root.get().strip()
        if not base or not os.path.isdir(base):
            detail.delete("1.0", "end")
            detail.insert("1.0", "请先设置有效的草稿根目录。")
            replace_state["refs"] = []
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
        content_path = os.path.join(dpath, "draft_content.json")
        encrypted = _file_exists_nonempty(content_path) and _looks_like_jianying_encrypted(content_path)
        replace_state["encrypted"] = encrypted
        replace_state["content_ok"] = bool(summary.content_ok)
        raw_timeline: Optional[Dict[str, Any]] = None
        if summary.content_ok and _file_exists_nonempty(content_path) and not encrypted:
            raw_timeline = _safe_read_json(content_path)
            if raw_timeline:
                try:
                    from pyJianYingDraft.script_file import ScriptFile

                    script = ScriptFile.load_from_parsed_json(raw_timeline, content_path)
                    replace_state["refs"] = list_replaceable_media_segments_from_script(script)
                except Exception as e:
                    replace_state["refs"] = []
                    detail.insert("end", f"\n\n【替换音视频槽解析失败】{e}")
        refresh_timeline_panel_data(raw_timeline)
        sync_export_pool_preset_for_draft(folder_name)

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
            b = ctk.CTkButton(
                container,
                text=folder_name,
                anchor="w",
                height=32,
                fg_color=("gray80", "gray20"),
                hover_color=("gray70", "gray30"),
                command=lambda n=folder_name: show_draft(n),
            )
            b.pack(fill="x", pady=2, padx=(pad_l, 4))
            b._name = folder_name  # type: ignore[attr-defined]
            b._row_kind = "leaf"  # type: ignore[attr-defined]
            draft_buttons.append(b)

        for name in top_level:
            children = list(by_parent.get(name) or [])
            if children:
                expanded = name not in collapsed_parents
                row = ctk.CTkFrame(list_frame, fg_color="transparent")
                row.pack(fill="x", pady=2, padx=4)

                def _mk_toggle(pn: str = name) -> Any:
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
                mid.grid_columnconfigure(0, weight=1)
                pb = ctk.CTkButton(
                    mid,
                    text=name,
                    anchor="w",
                    height=32,
                    fg_color=("gray78", "gray22"),
                    hover_color=("gray68", "gray32"),
                    command=lambda n=name: show_draft(n),
                )
                pb.grid(row=0, column=0, sticky="ew")
                n_sub = len(children)
                cnt_lbl = ctk.CTkLabel(
                    mid,
                    text=f"· {n_sub} 个子稿",
                    font=ctk.CTkFont(size=11),
                    text_color=("gray48", "gray58"),
                    anchor="e",
                )
                cnt_lbl.grid(row=0, column=1, sticky="e", padx=(6, 2))
                cnt_lbl.bind("<Button-1>", lambda _e, n=name: show_draft(n))
                cnt_lbl.bind("<Enter>", lambda _e: cnt_lbl.configure(cursor="hand2"))
                cnt_lbl.bind("<Leave>", lambda _e: cnt_lbl.configure(cursor=""))
                pb._name = name  # type: ignore[attr-defined]
                pb._row_kind = "parent"  # type: ignore[attr-defined]
                draft_buttons.append(pb)

                if expanded:
                    ch_sorted = sorted(children, key=lambda c: _draft_list_sort_key(base, c), reverse=True)
                    ch_frame = ctk.CTkFrame(list_frame, fg_color="transparent")
                    ch_frame.pack(fill="x", padx=(4, 4))
                    for ch in ch_sorted:
                        add_leaf_button(ch_frame, ch, indent=8)
            else:
                add_leaf_button(list_frame, name, indent=0)

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
