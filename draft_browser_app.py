"""
爆款智剪 — 左侧草稿列表，右侧详情与时间轴预览（轨道与片段按时间排列）；
明文 draft_content.json 下可在时间轴音视频片段上右键「替换素材…」弹窗替换（按原片段时长截断或缩短）；
片段可单独设置「导出用素材目录」；导出 MP4 前会先复制当前草稿为「父模板名_N」子草稿（挂在推断出的父模板下）、在子草稿上套素材再导出，不改动你选中的底稿文件夹。
单个文件替换同样写入新子草稿。父子关系索引在 %LOCALAPPDATA%\\pyJianYingDraft_browser\\，草稿文件夹仍在剪映根目录下平铺。
音频槽选视频时自动用 ffmpeg 抽音轨为 MP3。
运行: pip install customtkinter Send2Trash && python draft_browser_app.py
"""

from __future__ import annotations

import hashlib
import json
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


def segment_export_pool_key(draft_name: str, ref: MediaSegmentRef) -> str:
    """按草稿名 + 轨道 id + 片段下标定位（轨道名为空时也不冲突）。无 track_id 时回退旧格式。"""
    tid = (ref.track_id or "").strip()
    if tid:
        return f"{draft_name}\0{tid}\0{ref.segment_index}"
    return f"{draft_name}\0{ref.track_type}\0{ref.track_name}\0{ref.track_type_index}\0{ref.segment_index}"


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
    return out


def segment_has_replace_config(
    draft_name: str, ref: Optional[MediaSegmentRef], pool: Dict[str, Any]
) -> bool:
    return bool(segment_replace_status_lines(draft_name, ref, pool))


def _segment_export_pool_for_preset_disk(seg_in: Dict[str, Any]) -> Dict[str, Dict[str, Any]]:
    """写入预设文件时只保留「素材目录」配置，忽略 replace_file 等仅界面用的键。"""
    out: Dict[str, Dict[str, Any]] = {}
    for sk, sv in (seg_in or {}).items():
        if not isinstance(sv, dict):
            continue
        d = str(sv.get("dir", "") or "").strip()
        if not d:
            continue
        od = sv.get("order", "random")
        if od not in ("random", "sequential"):
            od = "random"
        out[str(sk)] = {"dir": d, "order": od}
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


def list_replaceable_media_segments(content_json_path: str) -> List[MediaSegmentRef]:
    """从明文 draft_content.json 解析可替换的音视频片段列表。"""
    _ensure_local_pyjianyingdraft_on_path()
    from pyJianYingDraft.script_file import ScriptFile
    from pyJianYingDraft.template_mode import ImportedMediaTrack

    script = ScriptFile.load_template(content_json_path)
    out: List[MediaSegmentRef] = []
    mats = script.imported_materials
    vi, ai = 0, 0

    for tr in script.imported_tracks:
        if not isinstance(tr, ImportedMediaTrack):
            continue
        kind = tr.track_type.name
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


def apply_single_material_replace(
    content_json_path: str,
    ref: MediaSegmentRef,
    new_file_path: str,
) -> Optional[str]:
    """将指定片段的素材替换为本地文件。

    时长处理（与 ``replace_material_by_seg`` / ``ShrinkMode.cut_tail``、``ExtendMode.cut_material_tail`` 一致）：
    新素材**更长**时，只使用素材前段，轨道上片段时长仍与原片段一致（截断素材尾部）；
    新素材**更短**时，轨道上该片段的**目标时长会缩短**为与素材长度一致（不是拉长时间轴上的空白）。

    若替换的是**音频轨**且所选文件带视频画面，则自动调用 ffmpeg 生成同目录下的 ``*_jy_audio.mp3`` 再引用。

    Returns:
        若有自动转码，返回提示文案；否则返回 None。
    """
    _ensure_local_pyjianyingdraft_on_path()
    from pyJianYingDraft import AudioMaterial, VideoMaterial
    from pyJianYingDraft.script_file import ScriptFile
    from pyJianYingDraft.template_mode import ExtendMode, ShrinkMode
    from pyJianYingDraft.track import TrackType

    script = ScriptFile.load_template(content_json_path)
    tt = TrackType.video if ref.track_type == "video" else TrackType.audio
    # 多条同类型且轨道名为空时，按 name 会歧义；仅用「同类导入轨道中的顺序 index」与 list_replaceable 枚举一致。
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

    script.replace_material_by_seg(
        track,
        ref.segment_index,
        material,
        source_timerange=None,
        handle_shrink=ShrinkMode.cut_tail,
        handle_extend=ExtendMode.cut_material_tail,
    )
    script.save()
    return extra_note


def apply_per_segment_export_pools_to_draft(
    content_json_path: str,
    draft_name: str,
    segment_pool: Dict[str, Dict[str, Any]],
    sequential_cursor: Dict[str, int],
) -> Tuple[int, int, List[str], int]:
    """仅对已在 segment_pool 中配置「dir」的片段，从各自目录选一文件套用。

    每个片段可配置 order: "random" | "sequential"；顺序模式用 sequential_cursor[片段键] 在多轮导出间延续。
    返回 (成功数, 因目录内无匹配文件跳过数, 错误信息列表, 已配置目录的片段数)。
    """
    errs: List[str] = []
    refs = list_replaceable_media_segments(content_json_path)
    ok = 0
    skip = 0
    configured = 0
    for ref in refs:
        key = segment_export_pool_key(draft_name, ref)
        cfg = segment_pool.get(key) or {}
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
            apply_single_material_replace(content_json_path, ref, pick)
            ok += 1
        except Exception as e:
            errs.append(f"{ref.combo_label}: {e}")
    return ok, skip, errs, configured


def backup_plaintext_draft(draft_root: str, draft_name: str) -> str:
    """将草稿整夹复制到草稿根目录的上一级下的 pyJianYingDraft_plain_backups，避免剪映导出保存后加密覆盖原稿。

    返回备份目录路径。
    """
    src = os.path.join(draft_root, draft_name)
    if not os.path.isdir(src):
        raise FileNotFoundError(f"找不到草稿目录:\n{src}")
    parent = os.path.dirname(os.path.normpath(draft_root))
    backup_root = os.path.join(parent, "pyJianYingDraft_plain_backups")
    os.makedirs(backup_root, exist_ok=True)
    dest = os.path.join(backup_root, draft_name)
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


def _find_jianying_pro_exe() -> Optional[str]:
    """查找剪映专业版主程序路径（Windows 常见安装布局）。"""
    if sys.platform != "win32":
        return None
    found: List[str] = []
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
                    if os.path.isfile(exe):
                        found.append(exe)
            except OSError:
                pass
        flat = os.path.join(local, "JianyingPro", "JianyingPro.exe")
        if os.path.isfile(flat):
            found.append(flat)
    for envkey in ("PROGRAMFILES", "PROGRAMFILES(X86)"):
        base = os.environ.get(envkey, "")
        if not base:
            continue
        exe = os.path.join(base, "JianyingPro", "JianyingPro.exe")
        if os.path.isfile(exe):
            found.append(exe)
    if not found:
        return None
    found.sort(key=lambda p: os.path.getmtime(p), reverse=True)
    return found[0]


def launch_jianying_pro() -> bool:
    """启动本机剪映专业版；成功返回 True。"""
    exe = _find_jianying_pro_exe()
    if not exe:
        return False
    try:
        os.startfile(exe)  # type: ignore[attr-defined]
        return True
    except OSError:
        return False


def start_jianying_pro_process() -> bool:
    """用子进程启动剪映（便于在启动后继续等待窗口并自动化）；成功返回 True。"""
    exe = _find_jianying_pro_exe()
    if not exe:
        return False
    try:
        cwd = os.path.dirname(exe)
        subprocess.Popen([exe], cwd=cwd if cwd else None, close_fds=True)
        return True
    except OSError:
        return False


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


POOL_EXPORT_PRESET_KEEP = "(保持原样)"


def _pool_export_presets_store_path(draft_root: str) -> Path:
    digest = hashlib.sha256(_normalized_draft_root_key(draft_root).encode("utf-8")).hexdigest()[:24]
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    root = Path(ada) / "pyJianYingDraft_browser"
    root.mkdir(parents=True, exist_ok=True)
    return root / f"export_pool_presets_{digest}.json"


def load_export_pool_presets(draft_root: str) -> Dict[str, Any]:
    """按草稿根目录读取导出槽「素材目录」预设（多组命名配置）。"""
    path = _pool_export_presets_store_path(draft_root)
    if not path.is_file():
        return {"version": 1, "draft_root": _normalized_draft_root_key(draft_root), "presets": {}}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return {"version": 1, "draft_root": _normalized_draft_root_key(draft_root), "presets": {}}
    if not isinstance(data, dict):
        return {"version": 1, "draft_root": _normalized_draft_root_key(draft_root), "presets": {}}
    raw = data.get("presets")
    if not isinstance(raw, dict):
        raw = {}
    clean: Dict[str, Any] = {}
    for pname, blob in raw.items():
        name = str(pname).strip()
        if not name or name == POOL_EXPORT_PRESET_KEEP:
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
                d = str(sv.get("dir", "") or "").strip()
                if not d:
                    continue
                od = sv.get("order", "random")
                if od not in ("random", "sequential"):
                    od = "random"
                seg[str(sk)] = {"dir": d, "order": od}
        cur: Dict[str, int] = {}
        if isinstance(cur_in, dict):
            for ck, cv in cur_in.items():
                try:
                    cur[str(ck)] = int(cv)
                except (TypeError, ValueError):
                    cur[str(ck)] = 0
        clean[name] = {"segment_export_pool": seg, "export_pool_sequential_cursor": cur}
    return {"version": 1, "draft_root": _normalized_draft_root_key(draft_root), "presets": clean}


def save_export_pool_presets(draft_root: str, data: Dict[str, Any]) -> None:
    path = _pool_export_presets_store_path(draft_root)
    presets = data.get("presets")
    if not isinstance(presets, dict):
        presets = {}
    payload = {
        "version": 1,
        "draft_root": _normalized_draft_root_key(draft_root),
        "presets": presets,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


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


def find_replace_ref_for_timeline_segment(
    refs: List[MediaSegmentRef], track: Dict[str, Any], segment_index_raw: int
) -> Optional[MediaSegmentRef]:
    """时间轴轨道片段（JSON 内 segment 下标）与下方「素材槽」列表项对应。"""
    tid = str(track.get("id", "") or "").strip()
    if tid:
        for r in refs:
            if (r.track_id or "").strip() == tid and r.segment_index == segment_index_raw:
                return r
    tname = str(track.get("name", ""))
    ttype = str(track.get("type", ""))
    for r in refs:
        if r.track_name == tname and r.track_type == ttype and r.segment_index == segment_index_raw:
            return r
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
    ref = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i)
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
        if status_label is not None:
            try:
                status_label.configure(text=text)
            except Exception:
                pass
        if status_replace_highlight_label is not None:
            try:
                status_replace_highlight_label.configure(text=replace_highlight)
            except Exception:
                pass

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
        ref = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i)
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
        ref = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i)
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
            r_here = find_replace_ref_for_timeline_segment(refs_list, tr, orig_i)
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

    apply_selection_visual()
    if sel.get("kind") == "none":
        _set_status(
            "提示：点击左侧轨道名选中轨道；点击彩色条选中片段；音视频片段可右键「替换素材…」。"
            " 轨道多时可滚轮上下浏览或拖右侧竖条；Ctrl+滚轮或标题栏「+/−」横向缩放。",
            replace_highlight="",
        )

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
    win_w, win_h = 1100, 720
    root.minsize(880, 560)
    root.geometry(f"{win_w}x{win_h}")
    root.update_idletasks()
    _center_window_on_screen(root, win_w, win_h)

    draft_root = ctk.StringVar(value=_default_draft_roots()[0] if _default_draft_roots() else "")
    selected_name: Optional[str] = None

    main = ctk.CTkFrame(root, fg_color="transparent")
    main.pack(fill="both", expand=True, padx=12, pady=12)

    left = ctk.CTkFrame(main, width=280, corner_radius=12)
    left.pack(side="left", fill="y", padx=(0, 10))
    left.pack_propagate(False)

    right = ctk.CTkFrame(main, corner_radius=12)
    right.pack(side="left", fill="both", expand=True)
    right.grid_columnconfigure(0, weight=1)
    # 草稿信息 : 时间轴 : 导出区 = 2 : 6 : 2
    right.grid_rowconfigure(0, weight=2, uniform="right_stack", minsize=72)
    right.grid_rowconfigure(1, weight=6, uniform="right_stack", minsize=160)
    right.grid_rowconfigure(2, weight=2, uniform="right_stack", minsize=88)

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

    timeline_sel_label = ctk.CTkLabel(
        timeline_status_left,
        text="提示：点击轨道名选中整条轨道；点击片段时间条选中片段；明文稿中音视频片段可右键「替换素材…」。轨道多时可滚轮上下浏览；Ctrl+滚轮横向缩放。",
        font=ctk.CTkFont(size=11),
        text_color=("gray40", "gray60"),
        anchor="nw",
        justify="left",
        wraplength=400,
    )
    timeline_sel_label.grid(row=0, column=0, sticky="ew")

    timeline_replace_highlight_label = ctk.CTkLabel(
        timeline_status_left,
        text="",
        font=ctk.CTkFont(size=11),
        text_color=("#2dd48f", "#5ee9ad"),
        anchor="nw",
        justify="left",
        wraplength=400,
    )
    timeline_replace_highlight_label.grid(row=1, column=0, sticky="ew", pady=(2, 0))

    _timeline_status_wrap_w: List[int] = [-1]

    def _sync_timeline_status_wrap(_event: Optional[tk.Event] = None) -> None:
        """按左侧信息区实际宽度设置 wraplength，避免窗体变窄时提示被裁切。"""
        try:
            timeline_status_left.update_idletasks()
            w = int(timeline_status_left.winfo_width())
        except (tk.TclError, ValueError, TypeError):
            return
        if w < 64:
            return
        if w == _timeline_status_wrap_w[0]:
            return
        _timeline_status_wrap_w[0] = w
        wl = max(120, w - 24)
        try:
            timeline_sel_label.configure(wraplength=wl)
            timeline_replace_highlight_label.configure(wraplength=wl)
        except Exception:
            pass

    timeline_status_left.bind("<Configure>", lambda e: _sync_timeline_status_wrap(e))
    root.after_idle(_sync_timeline_status_wrap)

    def refresh_timeline_segment_status_if_selected() -> None:
        """重绘时间轴后，若仍选中片段则按当前 segment_export_pool 等信息刷新下方说明。"""
        ts = timeline_select
        if ts.get("kind") != "seg" or ts.get("ti") is None or ts.get("orig_i") is None:
            try:
                timeline_replace_highlight_label.configure(text="")
            except Exception:
                pass
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
        try:
            timeline_sel_label.configure(text=main)
            timeline_replace_highlight_label.configure(text=hl)
        except Exception:
            pass

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

    def _try_apply_ref(ref: MediaSegmentRef, npath: str) -> bool:
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
            _ensure_local_pyjianyingdraft_on_path()
            from pyJianYingDraft import DraftFolder

            lineage_parent = resolve_lineage_parent_for_nested_draft(base, name)
            child_name = _next_generated_child_name(base, lineage_parent)
            DraftFolder(base).duplicate_as_template(name, child_name, allow_replace=False)
            content_child = os.path.join(base, child_name, "draft_content.json")
            extra = apply_single_material_replace(content_child, ref, npath)
            register_child_draft(base, lineage_parent, child_name)
            remapped_pool = remap_draft_keyed_map(replace_state.get("segment_export_pool") or {}, name, child_name)
            raw_cur = remap_draft_keyed_map(
                replace_state.get("export_pool_sequential_cursor") or {}, name, child_name
            )
            cursor_ints: Dict[str, int] = {}
            for k, v in raw_cur.items():
                try:
                    cursor_ints[k] = int(v)
                except (TypeError, ValueError):
                    cursor_ints[k] = 0
            merge_remapped_pool_and_cursor_into_replace_state(replace_state, remapped_pool, cursor_ints)
            ck = segment_export_pool_key(child_name, ref)
            seg_map = replace_state.setdefault("segment_export_pool", {})
            sub = dict(seg_map.get(ck) or {}) if isinstance(seg_map.get(ck), dict) else {}
            sub["replace_file"] = os.path.abspath(npath)
            seg_map[ck] = sub
        except Exception as e:
            messagebox.showerror("替换失败", f"槽 {slot_n}: {e}")
            return False
        tail = (
            f"已保存为新子草稿「{child_name}」（归在父模板「{lineage_parent}」下），"
            f"原草稿「{name}」未修改。\n若剪映已打开相关草稿，请关闭后重新打开以便加载。"
        )
        messagebox.showinfo("完成", f"{extra}\n\n{tail}" if extra else tail)
        refresh_list()
        show_draft(child_name)
        return True

    def open_replace_material_dialog(ref: MediaSegmentRef) -> None:
        from tkinter import filedialog, messagebox

        win = ctk.CTkToplevel(root)
        win.title("替换素材")
        dlg_w, dlg_h = 600, 360
        win.geometry(f"{dlg_w}x{dlg_h}")
        win.minsize(520, 320)
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
        if _cfg0.get("dir"):
            dir_var.set(str(_cfg0.get("dir", "")))
            mode_var.set("dir")

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
            # 「单个文件」下替换不改动已保存的导出目录；仅在「素材目录」模式下写入或清空。
            if mode_var.get() != "dir":
                return
            if d:
                prev = dict(pool.get(k) or {}) if isinstance(pool.get(k), dict) else {}
                prev["dir"] = d
                prev["order"] = od
                pool[k] = prev
            else:
                pool.pop(k, None)

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
                if _try_apply_ref(ref, p):
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
    pool_preset_var = ctk.StringVar(value=POOL_EXPORT_PRESET_KEEP)

    preset_toolbar = ctk.CTkFrame(preset_toolbar_host, fg_color="transparent")
    preset_toolbar.pack(anchor="ne")

    def _export_pool_preset_name_list(base_s: str) -> List[str]:
        if not base_s or not os.path.isdir(base_s):
            return []
        data = load_export_pool_presets(base_s)
        pr = data.get("presets") or {}
        if not isinstance(pr, dict):
            return []
        return sorted(k for k in pr if isinstance(k, str) and k.strip() and k != POOL_EXPORT_PRESET_KEEP)

    def _apply_export_pool_preset_choice(choice: str) -> None:
        base_s = draft_root.get().strip()
        if choice == POOL_EXPORT_PRESET_KEEP:
            replace_state["segment_export_pool"] = {}
            replace_state["export_pool_sequential_cursor"] = {}
        else:
            blob = ((load_export_pool_presets(base_s).get("presets") or {}) if base_s else {}).get(choice)
            if not isinstance(blob, dict):
                replace_state["segment_export_pool"] = {}
                replace_state["export_pool_sequential_cursor"] = {}
            else:
                seg = blob.get("segment_export_pool")
                cur = blob.get("export_pool_sequential_cursor")
                replace_state["segment_export_pool"] = dict(seg) if isinstance(seg, dict) else {}
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

    ctk.CTkLabel(
        preset_toolbar,
        text="槽位预设",
        font=ctk.CTkFont(size=11),
        anchor="w",
        text_color=("gray30", "gray70"),
    ).pack(side="left", padx=(0, 4))
    pool_preset_menu = ctk.CTkOptionMenu(
        preset_toolbar,
        values=[POOL_EXPORT_PRESET_KEEP],
        variable=pool_preset_var,
        width=140,
        height=26,
        font=ctk.CTkFont(size=11),
        command=on_pool_preset_menu_change,
    )
    pool_preset_menu.pack(side="left", padx=(0, 4))

    def refresh_export_pool_preset_bar(*, reset_memory: bool = False) -> None:
        base_s = draft_root.get().strip()
        names = _export_pool_preset_name_list(base_s)
        vals = [POOL_EXPORT_PRESET_KEEP] + names
        pool_preset_suppress["v"] = True
        try:
            pool_preset_menu.configure(values=vals)
            if reset_memory or not base_s or not os.path.isdir(base_s):
                pool_preset_var.set(POOL_EXPORT_PRESET_KEEP)
        finally:
            pool_preset_suppress["v"] = False
        if reset_memory or not base_s or not os.path.isdir(base_s):
            _apply_export_pool_preset_choice(POOL_EXPORT_PRESET_KEEP)

    def on_save_export_pool_preset() -> None:
        from customtkinter import CTkInputDialog
        from tkinter import messagebox

        base_s = draft_root.get().strip()
        if not base_s or not os.path.isdir(base_s):
            messagebox.showwarning("无法保存", "请先设置有效的草稿根目录。")
            return
        dlg = CTkInputDialog(
            text="预设名称（保存当前所有槽的目录与顺序模式）：",
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
                if default_name and default_name != POOL_EXPORT_PRESET_KEEP:
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
        if not name or name == POOL_EXPORT_PRESET_KEEP:
            return
        if re.search(r'[<>:"/\\|?*]', name):
            messagebox.showwarning("名称无效", "预设名不能包含下列字符：< > : \" / \\ | ? *")
            return
        seg = replace_state.get("segment_export_pool") or {}
        if not isinstance(seg, dict) or not seg:
            messagebox.showinfo(
                "保存预设",
                "当前没有可保存的「素材目录」槽位配置。\n请在「替换素材…」弹窗中选择「素材目录」并为至少一个片段指定目录后再保存。",
            )
            return
        data = load_export_pool_presets(base_s)
        presets = data.setdefault("presets", {})
        if not isinstance(presets, dict):
            presets = {}
            data["presets"] = presets
        if name in presets:
            if not messagebox.askyesno("覆盖预设", f"已存在预设「{name}」，是否覆盖？"):
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
        save_export_pool_presets(base_s, data)
        refresh_export_pool_preset_bar(reset_memory=False)
        pool_preset_suppress["v"] = True
        try:
            pool_preset_var.set(name)
        finally:
            pool_preset_suppress["v"] = False

    def on_delete_export_pool_preset() -> None:
        from tkinter import messagebox

        base_s = draft_root.get().strip()
        cur = pool_preset_var.get()
        if not base_s or not os.path.isdir(base_s):
            messagebox.showwarning("无法删除", "请先设置有效的草稿根目录。")
            return
        if cur == POOL_EXPORT_PRESET_KEEP:
            messagebox.showinfo("删除预设", "请先在列表中选择一个已保存的预设（非「保持原样」）。")
            return
        if not messagebox.askyesno("删除预设", f"确定删除预设「{cur}」吗？\n（仅删除本地保存的配置，不影响草稿文件）"):
            return
        data = load_export_pool_presets(base_s)
        pr = data.setdefault("presets", {})
        if isinstance(pr, dict):
            pr.pop(cur, None)
        save_export_pool_presets(base_s, data)
        refresh_export_pool_preset_bar(reset_memory=False)
        pool_preset_suppress["v"] = True
        try:
            pool_preset_var.set(POOL_EXPORT_PRESET_KEEP)
        finally:
            pool_preset_suppress["v"] = False
        _apply_export_pool_preset_choice(POOL_EXPORT_PRESET_KEEP)

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

    export_row = ctk.CTkFrame(bottom_actions, fg_color="transparent")
    export_row.pack(fill="x", pady=(0, 0))

    export_actions = ctk.CTkFrame(export_row, fg_color="transparent")
    export_actions.pack(side="right")

    jianying_row = ctk.CTkFrame(bottom_actions, fg_color="transparent")
    jianying_row.pack(fill="x", pady=(8, 0))

    backup_before_export = ctk.BooleanVar(value=False)
    export_repeat_var = ctk.StringVar(value="1")
    export_name_prefix_var = ctk.StringVar(value="video_")

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

        export_btn.configure(state="disabled")

        def worker() -> None:
            err: Optional[Exception] = None
            try:
                from pyJianYingDraft import DraftFolder, ExportFramerate, ExportResolution, JianyingController

                ctrl = JianyingController()
                df = DraftFolder(base)
                need_refresh = False
                last_child: Optional[str] = None
                for out_one in out_paths:
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
                    register_child_draft(base, lineage_parent, child_name)
                    merge_remapped_pool_and_cursor_into_replace_state(replace_state, remapped_pool, cursor_ints)
                    ctrl.export_draft(
                        child_name,
                        out_one,
                        resolution=ExportResolution.RES_1080P,
                        framerate=ExportFramerate.FR_30,
                    )
                    last_child = child_name
                    need_refresh = True
                if need_refresh and last_child:
                    root.after(0, refresh_list)
                    root.after(0, lambda c=last_child: show_draft(c))
            except Exception as e:
                err = e

            def finish() -> None:
                export_btn.configure(state="normal")
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
    replace_material_bar_btn.pack(side="left", padx=(0, 12))

    def on_launch_jianying() -> None:
        from tkinter import messagebox

        if sys.platform != "win32":
            messagebox.showinfo("打开剪映", "当前仅在 Windows 下支持从本程序启动剪映专业版。")
            return
        if not _find_jianying_pro_exe():
            messagebox.showerror(
                "未找到剪映",
                "未在常见安装路径找到剪映专业版（JianyingPro.exe）。\n"
                "请确认已安装剪映专业版，或从系统开始菜单手动启动。",
            )
            return

        draft_open = (selected_name or "").strip()

        def worker() -> None:
            err: Optional[str] = None
            try:
                _ensure_local_pyjianyingdraft_on_path()
                from pyJianYingDraft.exceptions import AutomationError, DraftNotFound
                from pyJianYingDraft.jianying_controller import wait_for_jianying_controller

                if draft_open:
                    try:
                        ctrl = wait_for_jianying_controller(timeout=5.0, poll=0.4)
                    except AutomationError:
                        if not start_jianying_pro_process():
                            raise AutomationError("无法启动剪映进程。")
                        ctrl = wait_for_jianying_controller(timeout=90.0, poll=0.5)
                    ctrl.open_draft_by_name(
                        draft_open,
                        after_click_sleep=8.0,
                        locate_timeout=3.0,
                    )
                else:
                    if not launch_jianying_pro():
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

    ctk.CTkButton(
        jianying_row,
        text="打开剪映",
        height=32,
        width=112,
        fg_color=("#3B8ED0", "#1F538D"),
        hover_color=("#2E7CB8", "#163A6E"),
        command=on_launch_jianying,
    ).pack(side="right")

    replace_state["_on_timeline_selection_ui"] = sync_replace_material_bar_btn

    export_count_row = ctk.CTkFrame(export_actions, fg_color="transparent")
    export_count_row.pack(side="left", padx=(0, 10))
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

    export_btn = ctk.CTkButton(
        export_actions,
        text="导出为 MP4…",
        height=38,
        width=200,
        fg_color=("#C45C26", "#A34A1E"),
        hover_color=("#A34A1E", "#8B3E18"),
        command=on_export_mp4,
    )
    export_btn.pack(side="left", padx=(0, 14))

    ctk.CTkCheckBox(
        export_actions,
        text="导出前备份明文",
        variable=backup_before_export,
        font=ctk.CTkFont(size=12),
    ).pack(side="left", padx=(0, 4))

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
        draft_root.set(p)
        path_entry.delete(0, "end")
        path_entry.insert(0, p)
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
        if summary.content_ok and _file_exists_nonempty(content_path) and not encrypted:
            try:
                replace_state["refs"] = list_replaceable_media_segments(content_path)
            except Exception:
                replace_state["refs"] = []
        raw_timeline: Optional[Dict[str, Any]] = None
        if summary.content_ok and _file_exists_nonempty(content_path) and not encrypted:
            raw_timeline = _safe_read_json(content_path)
        refresh_timeline_panel_data(raw_timeline)

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
                "单文件替换、导出 MP4 时都会新建「父模板名_N」子草稿并挂在推断的父模板下，"
                "不直接改写你选中的底稿；父子关系记在本地应用数据中。",
            )

        _redraw_list_scroll(reset_scroll=reset_list_scroll)

    # init path
    if draft_root.get():
        path_entry.insert(0, draft_root.get())
    refresh_list()
    refresh_export_pool_preset_bar(reset_memory=True)

    root.mainloop()


if __name__ == "__main__":
    run_app()
