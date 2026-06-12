# -*- coding: utf-8 -*-
"""
爆款模板 — 两层目录：folder（分类）→ template（可下载文件夹）。

列表: GET /api/hot_templates?user_id=...
下载: GET /api/hot_templates/download?user_id=...&template_id=...  → application/zip
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import tempfile
import zipfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple

# ratio: 0.0~1.0 为确定进度；None 表示总大小未知（仅更新文案）
ImportProgressCallback = Callable[[Optional[float], str], None]
from urllib.parse import unquote

try:
    import requests
except ImportError:
    requests = None  # type: ignore


@dataclass(frozen=True)
class HotTemplateNode:
    template_id: str
    name: str
    node_type: str  # folder | template
    updated_at: str = ""
    children: Tuple["HotTemplateNode", ...] = ()

    @property
    def is_folder(self) -> bool:
        return self.node_type == "folder"

    @property
    def is_template(self) -> bool:
        return self.node_type == "template"


def _as_str(value: Any) -> str:
    if value is None:
        return ""
    return str(value).strip()


def _parse_template_node(row: Any) -> Optional[HotTemplateNode]:
    """严格按 type + children 解析；template 节点不展开子项。"""
    if not isinstance(row, dict):
        return None
    tid = _as_str(row.get("id"))
    name = _as_str(row.get("name"))
    ntype = _as_str(row.get("type")).lower()
    if ntype not in ("folder", "template"):
        return None
    if not tid and not name:
        return None
    if not tid:
        tid = name
    children: Tuple[HotTemplateNode, ...] = ()
    if ntype == "folder":
        children_raw = row.get("children")
        if isinstance(children_raw, list):
            parsed = [_parse_template_node(ch) for ch in children_raw]
            children = tuple(n for n in parsed if n is not None)
    return HotTemplateNode(
        template_id=tid,
        name=name or tid,
        node_type=ntype,
        updated_at=_as_str(row.get("updated_at") or row.get("update_time")) if ntype == "template" else "",
        children=children,
    )


def parse_hot_template_tree(payload: Any) -> List[HotTemplateNode]:
    if not isinstance(payload, dict):
        return []
    raw_list = payload.get("templates")
    if not isinstance(raw_list, list):
        return []
    out: List[HotTemplateNode] = []
    for row in raw_list:
        node = _parse_template_node(row)
        if node is not None:
            out.append(node)
    return out


def count_hot_templates(nodes: Iterable[HotTemplateNode]) -> int:
    n = 0
    for node in nodes:
        if node.is_template:
            n += 1
        n += count_hot_templates(node.children)
    return n


def _response_error_message(data: Any, *, default: str) -> str:
    if isinstance(data, dict):
        return _as_str(data.get("message") or data.get("msg") or data.get("error")) or default
    return default


def _json_error_from_response(response: Any, *, default: str) -> Optional[str]:
    try:
        data = response.json()
    except ValueError:
        return None
    if isinstance(data, dict) and data.get("success") is False:
        return _response_error_message(data, default=default)
    return None


def _json_error_from_bytes(raw: bytes, *, default: str) -> Optional[str]:
    if not raw or raw[:1] != b"{":
        return None
    if len(raw) > 8192:
        peek = raw[:320].decode("utf-8", errors="ignore")
        if '"success"' not in peek or "false" not in peek.lower():
            return None
    try:
        data = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None
    if isinstance(data, dict) and data.get("success") is False:
        return _response_error_message(data, default=default)
    return None


def _filename_from_content_disposition(header: str) -> str:
    if not header:
        return ""
    m = re.search(r"filename\*=UTF-8''([^;]+)", header, re.I)
    if m:
        return unquote(m.group(1).strip().strip('"'))
    m = re.search(r'filename="?([^";]+)"?', header, re.I)
    if m:
        return unquote(m.group(1).strip())
    return ""


def _sanitize_draft_folder_name(name: str) -> Optional[str]:
    name = (name or "").strip()
    if not name or re.search(r'[<>:"/\\|?*]', name) or name in (".", ".."):
        return None
    return name


def _normalized_draft_root_key(draft_root: str) -> str:
    return os.path.normcase(os.path.normpath(os.path.abspath(draft_root)))


def _hot_template_local_map_path(draft_root: str) -> Path:
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    d = Path(ada) / "pyJianYingDraft_browser"
    d.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256(_normalized_draft_root_key(draft_root).encode("utf-8")).hexdigest()[:24]
    return d / f"hot_template_local_{digest}.json"


def _load_hot_template_local_map(draft_root: str) -> Dict[str, str]:
    path = _hot_template_local_map_path(draft_root)
    if not path.is_file():
        return {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        by_id = data.get("by_template_id") if isinstance(data, dict) else {}
        if not isinstance(by_id, dict):
            return {}
        return {str(k): str(v) for k, v in by_id.items() if k and v}
    except (OSError, json.JSONDecodeError, TypeError, ValueError):
        return {}


def record_hot_template_local_folder(draft_root: str, template_id: str, folder_name: str) -> None:
    tid = _as_str(template_id)
    fname = _as_str(folder_name)
    if not draft_root or not tid or not fname:
        return
    path = _hot_template_local_map_path(draft_root)
    by_id = _load_hot_template_local_map(draft_root)
    by_id[tid] = fname
    data = {
        "version": 1,
        "draft_root": _normalized_draft_root_key(draft_root),
        "by_template_id": by_id,
    }
    tmp = path.with_suffix(".json.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def _is_valid_draft_folder(draft_root: str, folder_name: str) -> bool:
    folder_path = os.path.join(draft_root, folder_name)
    return os.path.isdir(folder_path) and os.path.isfile(os.path.join(folder_path, "draft_content.json"))


def _folder_matches_template_base(folder_name: str, base_name: str) -> bool:
    if not base_name:
        return False
    if folder_name == base_name:
        return True
    prefix = base_name + "_"
    if folder_name.startswith(prefix):
        rest = folder_name[len(prefix) :]
        return rest.isdigit()
    return False


def find_local_hot_template_folder(
    draft_root: str,
    *,
    template_id: str = "",
    template_name: str = "",
) -> Optional[str]:
    """查找模板对应的本地草稿文件夹名；优先读导入记录，再按名称匹配。"""
    if not draft_root or not os.path.isdir(draft_root):
        return None
    tid = _as_str(template_id)
    local_map = _load_hot_template_local_map(draft_root)
    if tid and tid in local_map:
        mapped = local_map[tid]
        if _is_valid_draft_folder(draft_root, mapped):
            return mapped
    base_names: List[str] = []
    for candidate in (template_name, os.path.basename(tid.replace("\\", "/").replace("/", os.sep))):
        sanitized = _sanitize_draft_folder_name(candidate)
        if sanitized and sanitized not in base_names:
            base_names.append(sanitized)
    if not base_names:
        return None
    matches: List[Tuple[str, float]] = []
    try:
        for name in os.listdir(draft_root):
            if not _is_valid_draft_folder(draft_root, name):
                continue
            if any(_folder_matches_template_base(name, base) for base in base_names):
                try:
                    mtime = os.path.getmtime(os.path.join(draft_root, name))
                except OSError:
                    mtime = 0.0
                matches.append((name, mtime))
    except OSError:
        return None
    if not matches:
        return None
    matches.sort(key=lambda x: x[1], reverse=True)
    return matches[0][0]


def _unique_draft_folder_name(draft_root: str, base_name: str) -> str:
    root = os.path.abspath(draft_root)
    name = base_name
    idx = 1
    while os.path.exists(os.path.join(root, name)):
        name = f"{base_name}_{idx}"
        idx += 1
    return name


def _fmt_byte_count(n: int) -> str:
    n = max(0, int(n))
    if n < 1024:
        return f"{n} B"
    if n < 1024 * 1024:
        return f"{n / 1024:.1f} KB"
    if n < 1024 * 1024 * 1024:
        return f"{n / (1024 * 1024):.1f} MB"
    return f"{n / (1024 * 1024 * 1024):.2f} GB"


def _dir_byte_size(path: str) -> int:
    total = 0
    for dirpath, _, files in os.walk(path):
        for name in files:
            fp = os.path.join(dirpath, name)
            try:
                total += os.path.getsize(fp)
            except OSError:
                pass
    return max(1, total)


def _copytree_with_progress(
    src: str,
    dst: str,
    *,
    on_bytes: Callable[[int, int], None],
) -> None:
    total = _dir_byte_size(src)
    copied = 0
    for dirpath, _, files in os.walk(src):
        rel = os.path.relpath(dirpath, src)
        dest_dir = dst if rel in (".", "") else os.path.join(dst, rel)
        os.makedirs(dest_dir, exist_ok=True)
        for name in files:
            s = os.path.join(dirpath, name)
            d = os.path.join(dest_dir, name)
            shutil.copy2(s, d)
            try:
                copied += os.path.getsize(d)
            except OSError:
                copied += 1
            on_bytes(min(copied, total), total)


def _zip_entries_safe(zf: zipfile.ZipFile) -> Optional[str]:
    for name in zf.namelist():
        norm = os.path.normpath(name.replace("\\", "/"))
        if norm.startswith("..") or os.path.isabs(norm):
            return "ZIP 包路径不安全"
    return None


def import_template_zip_file(
    draft_root: str,
    zip_path: str,
    *,
    expected_folder_name: str = "",
    on_progress: Optional[ImportProgressCallback] = None,
) -> Tuple[Optional[str], Optional[str]]:
    """解压 zip 并将顶层模板文件夹放入剪映草稿根目录。返回 (文件夹名, error)。"""

    def report(ratio: Optional[float], message: str) -> None:
        if on_progress is not None:
            on_progress(ratio, message)

    if not draft_root or not os.path.isdir(draft_root):
        return None, "请先设置有效的剪映草稿根目录"
    if not zip_path or not os.path.isfile(zip_path):
        return None, "下载文件无效"
    root = os.path.abspath(draft_root)
    hint = _sanitize_draft_folder_name(expected_folder_name) or ""
    try:
        report(0.0, "正在校验 ZIP…")
        with zipfile.ZipFile(zip_path, "r") as zf:
            unsafe = _zip_entries_safe(zf)
            if unsafe:
                return None, unsafe
            members = [info for info in zf.infolist() if info.filename and not info.is_dir()]
            if not members:
                return None, "ZIP 包为空"
            total_uncompressed = sum(max(0, int(info.file_size)) for info in members)
            if total_uncompressed <= 0:
                total_uncompressed = len(members)
            with tempfile.TemporaryDirectory(prefix="jy_tpl_unzip_") as tmp:
                extracted = 0
                for info in members:
                    zf.extract(info, tmp)
                    extracted += max(0, int(info.file_size)) or 1
                    if total_uncompressed > 0:
                        pct = min(100, int(extracted * 100 / total_uncompressed))
                        report(
                            min(1.0, extracted / total_uncompressed),
                            f"正在解压… {pct}%",
                        )
                    else:
                        report(None, "正在解压…")
                top_entries = [e for e in os.listdir(tmp) if e not in (".", "..")]
                if len(top_entries) != 1:
                    return None, "ZIP 应只包含一个模板文件夹"
                src_path = os.path.join(tmp, top_entries[0])
                if not os.path.isdir(src_path):
                    return None, "ZIP 内未找到模板文件夹"
                src_folder_name = top_entries[0]
                base_name = _sanitize_draft_folder_name(src_folder_name) or hint
                if not base_name:
                    return None, "模板文件夹名无效"
                dest_name = _unique_draft_folder_name(root, base_name)
                dest_path = os.path.join(root, dest_name)
                report(0.0, "正在写入草稿目录…")

                def _on_copy_bytes(done: int, total: int) -> None:
                    pct = min(100, int(done * 100 / max(1, total)))
                    report(min(1.0, done / max(1, total)), f"正在写入草稿目录… {pct}%")

                _copytree_with_progress(src_path, dest_path, on_bytes=_on_copy_bytes)
                report(1.0, "导入完成")
                return dest_name, None
    except zipfile.BadZipFile:
        return None, "下载内容不是有效的 ZIP 文件"
    except OSError as exc:
        return None, f"导入模板失败：{exc}"


class HotTemplateClient:
    LIST_PATH = "/api/hot_templates"
    DOWNLOAD_PATH = "/api/hot_templates/download"

    def __init__(self, base_url: str = "http://localhost:5000") -> None:
        self.base_url = base_url.rstrip("/")

    def fetch_list(
        self,
        *,
        user_id: Optional[Any] = None,
        timeout: float = 12.0,
    ) -> Tuple[List[HotTemplateNode], Optional[str]]:
        if requests is None:
            return [], "需要安装 requests：pip install requests"
        url = f"{self.base_url}{self.LIST_PATH}"
        params: Dict[str, Any] = {}
        if user_id is not None:
            params["user_id"] = user_id
        try:
            response = requests.get(url, params=params or None, timeout=timeout)
        except requests.RequestException as exc:
            return [], f"无法连接模板服务器：{exc}"
        if response.status_code in (400, 401, 403):
            err = _json_error_from_response(response, default="拉取失败")
            if err:
                return [], err
        if response.status_code == 404:
            return [], "模板列表接口尚未上线，敬请期待。"
        if response.status_code != 200:
            err = _json_error_from_response(response, default="拉取失败")
            if err:
                return [], err
            snippet = (response.text or "")[:120].strip()
            if snippet:
                return [], f"服务器返回 {response.status_code}：{snippet}"
            return [], f"服务器返回 {response.status_code}"
        try:
            data = response.json()
        except ValueError:
            return [], "服务器响应不是有效的 JSON"
        if isinstance(data, dict) and data.get("success") is False:
            return [], _response_error_message(data, default="拉取失败")
        return parse_hot_template_tree(data), None

    def download_template_to_file(
        self,
        template_id: str,
        dest_path: str,
        *,
        user_id: Optional[Any] = None,
        timeout: float = 180.0,
        on_progress: Optional[ImportProgressCallback] = None,
    ) -> Tuple[Optional[str], Optional[str]]:
        """下载 zip 到 dest_path。返回 (folder_hint, error)。成功时 folder_hint 为建议文件夹名。"""

        def report(ratio: Optional[float], message: str) -> None:
            if on_progress is not None:
                on_progress(ratio, message)
        if requests is None:
            return None, "需要安装 requests：pip install requests"
        tid = _as_str(template_id)
        if not tid:
            return None, "缺少 template_id"
        url = f"{self.base_url}{self.DOWNLOAD_PATH}"
        params: Dict[str, Any] = {"template_id": tid}
        if user_id is not None:
            params["user_id"] = user_id
        folder_hint = os.path.basename(tid.replace("\\", "/").replace("/", os.sep))
        first_chunk = b""
        cd_header = ""
        try:
            with requests.get(url, params=params, stream=True, timeout=timeout) as response:
                if response.status_code == 404:
                    err = _json_error_from_response(response, default="模板不存在")
                    return None, err or "模板不存在"
                if response.status_code != 200:
                    err = _json_error_from_response(response, default=f"服务器返回 {response.status_code}")
                    if err:
                        return None, err
                    snippet = (response.text or "")[:120].strip() if response.text else ""
                    if snippet:
                        return None, f"服务器返回 {response.status_code}：{snippet}"
                    return None, f"服务器返回 {response.status_code}"
                cd_header = response.headers.get("Content-Disposition", "")
                total_bytes: Optional[int] = None
                cl = response.headers.get("Content-Length")
                if cl:
                    try:
                        total_bytes = max(0, int(cl))
                    except (TypeError, ValueError):
                        total_bytes = None
                first_chunk = b""
                downloaded = 0
                report(0.0, "正在下载…" if total_bytes else "正在下载…")
                with open(dest_path, "wb") as out:
                    for chunk in response.iter_content(chunk_size=65536):
                        if not chunk:
                            continue
                        if not first_chunk:
                            first_chunk = chunk[:4]
                        out.write(chunk)
                        downloaded += len(chunk)
                        if total_bytes and total_bytes > 0:
                            pct = min(100, int(downloaded * 100 / total_bytes))
                            report(
                                min(1.0, downloaded / total_bytes),
                                f"正在下载… {pct}%（{_fmt_byte_count(downloaded)} / {_fmt_byte_count(total_bytes)}）",
                            )
                        else:
                            report(None, f"正在下载… {_fmt_byte_count(downloaded)}")
                if total_bytes and total_bytes > 0:
                    report(1.0, f"下载完成（{_fmt_byte_count(downloaded)}）")
        except requests.RequestException as exc:
            return None, f"下载失败：{exc}"
        except OSError as exc:
            return None, f"保存下载文件失败：{exc}"
        if not first_chunk:
            return None, "下载内容为空"
        if first_chunk[:2] != b"PK":
            try:
                with open(dest_path, "rb") as err_f:
                    api_err = _json_error_from_bytes(err_f.read(8192), default="下载失败")
                if api_err:
                    return None, api_err
            except OSError:
                pass
            return None, "下载内容不是 ZIP 文件"
        hint_from_cd = _filename_from_content_disposition(cd_header)
        if hint_from_cd:
            folder_hint = hint_from_cd
        if folder_hint.lower().endswith(".zip"):
            folder_hint = os.path.splitext(folder_hint)[0]
        folder_hint = _sanitize_draft_folder_name(folder_hint) or os.path.basename(tid)
        return folder_hint, None
