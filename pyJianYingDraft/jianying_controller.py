"""剪映自动化控制，主要与自动导出有关"""

import time
import shutil
import os
import uiautomation as uia

from enum import Enum
from typing import Callable, Dict, List, Literal, Optional, Tuple

from . import exceptions
from .exceptions import AutomationError


_VIDEO_EXTS = (".mp4", ".mov", ".mkv", ".m4v")


def _ui_first_name_line(raw: Optional[str]) -> str:
    """控件 Name 的首个非空行（剪映部分控件 Name 带换行）。"""
    for line in (raw or "").splitlines():
        t = line.strip()
        if t:
            return t
    return ""


def _control_primary_label(ctrl: uia.Control) -> str:
    """用于匹配的可见文案：优先 UIA Name，否则 LegacyIAccessible.Name（部分 QML 控件）。"""
    first = _ui_first_name_line(ctrl.Name)
    if first:
        return first
    try:
        lap = ctrl.GetLegacyIAccessiblePattern()
        if lap is not None:
            return _ui_first_name_line(str(getattr(lap, "Name", "") or ""))
    except Exception:
        pass
    return ""


def _walk_click_by_exact_first_label(
    app: uia.Control,
    target_trim: str,
    *,
    max_depth: int = 48,
    max_nodes: int = 16000,
) -> bool:
    """遍历主窗口控件树，按首个非空 Name 行**精确**等于 target 查找并点击得分最高者。

    新版剪映左侧 Tab 常为 CustomControl / Group 等，固定类型搜索会失败；本兜底按 Name + 大致区域（偏左）择优。
    """
    try:
        win_rect = app.BoundingRectangle
        win_left = win_rect.left
        win_w = max(win_rect.width(), 1)
        win_top = win_rect.top
        win_h = max(win_rect.height(), 1)
    except Exception:
        win_rect = uia.Rect(0, 0, 1920, 1080)
        win_left, win_w, win_top, win_h = 0, 1920, 0, 1080

    type_score = {
        "TabItemControl": 120,
        "ListItemControl": 115,
        "TreeItemControl": 115,
        "ButtonControl": 100,
        "HyperlinkControl": 95,
        "MenuItemControl": 90,
        "CustomControl": 70,
        "GroupControl": 55,
        "PaneControl": 50,
        "TextControl": 25,
    }

    best_score = -10**9
    best_ctrl: Optional[uia.Control] = None
    n = 0
    for ctrl, _depth in uia.WalkControl(app, includeTop=False, maxDepth=max_depth):
        n += 1
        if n > max_nodes:
            break
        if _control_primary_label(ctrl) != target_trim:
            continue
        try:
            rect = ctrl.BoundingRectangle
            if rect.isempty() or rect.width() < 2 or rect.height() < 2:
                continue
        except Exception:
            continue
        cx = rect.xcenter()
        rel_x = (cx - win_left) / win_w
        in_left = 130 if rel_x < 0.48 else 0
        rel_y_mid = (rect.ycenter() - win_top) / win_h
        upper_band = 25 if rel_y_mid < 0.72 else 0
        ts = type_score.get(ctrl.ControlTypeName, 40)
        score = ts + in_left + upper_band
        if score > best_score:
            best_score = score
            best_ctrl = ctrl

    if best_ctrl is not None:
        best_ctrl.Click(simulateMove=False)
        return True
    return False


def _walk_best_rects_for_labels(
    app: uia.Control,
    labels: Tuple[str, ...],
    *,
    max_depth: int = 54,
    max_nodes: int = 20000,
) -> Dict[str, Tuple[uia.Control, uia.Rect]]:
    """在窗口内为多个标签各找一个「最像左侧素材栏」的控件及其矩形（用于几何推算）。"""
    want = frozenset(labels)
    best_score: Dict[str, int] = {lab: -10**9 for lab in labels}
    best_ctrl: Dict[str, Optional[uia.Control]] = {lab: None for lab in labels}
    best_rect: Dict[str, Optional[uia.Rect]] = {lab: None for lab in labels}
    try:
        win_rect = app.BoundingRectangle
        win_left = win_rect.left
        win_w = max(win_rect.width(), 1)
        win_top = win_rect.top
        win_h = max(win_rect.height(), 1)
    except Exception:
        win_rect = uia.Rect(0, 0, 1920, 1080)
        win_left, win_w, win_top, win_h = 0, 1920, 0, 1080

    type_score = {
        "TabItemControl": 120,
        "ListItemControl": 115,
        "TreeItemControl": 115,
        "ButtonControl": 100,
        "HyperlinkControl": 95,
        "MenuItemControl": 90,
        "CustomControl": 70,
        "GroupControl": 55,
        "PaneControl": 50,
        "TextControl": 25,
    }

    n = 0
    for ctrl, _depth in uia.WalkControl(app, includeTop=False, maxDepth=max_depth):
        n += 1
        if n > max_nodes:
            break
        lab = _control_primary_label(ctrl)
        if lab not in want:
            continue
        try:
            rect = ctrl.BoundingRectangle
            if rect.isempty() or rect.width() < 2 or rect.height() < 2:
                continue
        except Exception:
            continue
        cx = rect.xcenter()
        rel_x = (cx - win_left) / win_w
        in_left = 130 if rel_x < 0.48 else 0
        rel_y_mid = (rect.ycenter() - win_top) / win_h
        upper_band = 25 if rel_y_mid < 0.78 else 0
        ts = type_score.get(ctrl.ControlTypeName, 40)
        score = ts + in_left + upper_band
        if score > best_score[lab]:
            best_score[lab] = score
            best_ctrl[lab] = ctrl
            best_rect[lab] = rect

    out: Dict[str, Tuple[uia.Control, uia.Rect]] = {}
    for lab in labels:
        c, r = best_ctrl[lab], best_rect[lab]
        if c is not None and r is not None:
            out[lab] = (c, r)
    return out


def _control_text_blob(ctrl: uia.Control) -> str:
    """合并 Name 与 Legacy 名，用于子串检测（如「识别字幕」）。"""
    parts: List[str] = [ctrl.Name or ""]
    try:
        lap = ctrl.GetLegacyIAccessiblePattern()
        if lap is not None:
            parts.append(str(getattr(lap, "Name", "") or ""))
    except Exception:
        pass
    return "".join(parts)


def _geometry_subtitle_click_candidates(app: uia.Control) -> List[Tuple[int, int]]:
    """当无障碍树无「字幕」名时，根据「媒体 / 音频 / 文本」等锚点生成若干屏幕坐标候选。

    若连锚点名称都搜不到，则按窗口左缘比例生成竖栏点击（最后手段，依赖默认布局）。
    """
    try:
        win_rect = app.BoundingRectangle
    except Exception:
        win_rect = uia.Rect(0, 0, 1920, 1080)

    pts: List[Tuple[int, int]] = []

    def _add(x: int, y: int) -> None:
        if win_rect.contains(int(x), int(y)):
            pts.append((int(x), int(y)))

    anchors = ("媒体", "音频", "文本", "贴纸", "特效")
    rects = _walk_best_rects_for_labels(app, anchors, max_depth=56, max_nodes=22000)

    if rects:
        if "媒体" in rects and "音频" in rects:
            _, mr = rects["媒体"]
            _, ar = rects["音频"]
            step = int(max(42, abs(ar.ycenter() - mr.ycenter())))
            x0 = mr.xcenter()
            ym = mr.ycenter()
            for k in (3, 4, 2, 5):
                _add(x0, ym + k * step)
        elif "媒体" in rects:
            _, mr = rects["媒体"]
            step = int(max(52, mr.height() * 1.12))
            x0, ym = mr.xcenter(), mr.ycenter()
            for k in (3, 4, 2, 5):
                _add(x0, ym + k * step)
        if "文本" in rects and "音频" in rects:
            _, tr = rects["文本"]
            _, ar = rects["音频"]
            step2 = int(max(42, abs(tr.ycenter() - ar.ycenter())))
            x1, yt = tr.xcenter(), tr.ycenter()
            _add(x1, yt + step2)
            _add(x1, yt + 2 * step2)
        elif "文本" in rects:
            _, tr = rects["文本"]
            step2 = int(max(52, tr.height() * 1.12))
            x1, yt = tr.xcenter(), tr.ycenter()
            _add(x1, yt + step2)
            _add(x1, yt + 2 * step2)

    if not pts:
        try:
            wr = app.BoundingRectangle
            if not wr.isempty():
                x = wr.left + max(28, int(wr.width() * 0.026))
                base_y = wr.top + int(wr.height() * 0.36)
                for dy in (0, 58, 116, 174, 232, 290, 348):
                    _add(x, base_y + dy)
        except Exception:
            pass

    seen = set()
    uniq: List[Tuple[int, int]] = []
    for p in pts:
        if p not in seen:
            seen.add(p)
            uniq.append(p)
    return uniq[:10]


def _resolve_actual_export_path(ui_export_path: str, export_started: float) -> str:
    """界面「导出路径」与磁盘上实际位置可能不一致。

    常见情况：界面显示 ``D:\\下载\\项目名.mp4``，剪映实际落在 ``D:\\下载\\项目名\\`` 子文件夹内；
    或同级目录下另有刚导出的视频。在父目录、与无后缀同名的子文件夹内（及一层子目录）按修改时间筛选。
    """
    p = os.path.normpath(str(ui_export_path).replace("/", os.sep))
    if os.path.isfile(p):
        return p

    t_lo = export_started - 10.0
    t_hi = time.time() + 180.0
    base_name = os.path.basename(p)
    stem, _ext = os.path.splitext(base_name)
    scored: List[Tuple[int, float, str]] = []

    def _try_file(fp: str, name: str, folder_bonus: int) -> None:
        if not name.lower().endswith(_VIDEO_EXTS):
            return
        try:
            mtime = os.path.getmtime(fp)
        except OSError:
            return
        if mtime < t_lo or mtime > t_hi:
            return
        score = folder_bonus
        if name == base_name:
            score += 220
        elif name.lower().startswith(stem.lower()):
            score += 90
        scored.append((score, mtime, fp))

    def _scan_folder(folder: str, folder_bonus: int, scan_one_sublevel: bool) -> None:
        if not folder or not os.path.isdir(folder):
            return
        try:
            names = os.listdir(folder)
        except OSError:
            return
        for name in names:
            fp = os.path.join(folder, name)
            if os.path.isfile(fp):
                _try_file(fp, name, folder_bonus)
            elif scan_one_sublevel and os.path.isdir(fp):
                try:
                    for name2 in os.listdir(fp):
                        fp2 = os.path.join(fp, name2)
                        if os.path.isfile(fp2):
                            _try_file(fp2, name2, folder_bonus + 25)
                except OSError:
                    pass

    # 界面路径本身就是目录
    if os.path.isdir(p):
        _scan_folder(p, 180, scan_one_sublevel=True)
    else:
        parent = os.path.dirname(p)
        if not parent:
            return p
        # 与「xxx.mp4」同名的子文件夹：D:\下载\5月8日(2).mp4 → D:\下载\5月8日(2)\
        sub_same_stem = os.path.join(parent, stem)
        if os.path.isdir(sub_same_stem):
            _scan_folder(sub_same_stem, 260, scan_one_sublevel=True)
        # 父目录内直接放置的视频（旧逻辑）
        if os.path.isdir(parent):
            _scan_folder(parent, 0, scan_one_sublevel=False)

    if not scored:
        return p
    scored.sort(key=lambda x: (-x[0], -x[1]))
    return scored[0][2]

class ExportResolution(Enum):
    """导出分辨率"""
    RES_8K = "8K"
    RES_4K = "4K"
    RES_2K = "2K"
    RES_1080P = "1080P"
    RES_720P = "720P"
    RES_480P = "480P"

class ExportFramerate(Enum):
    """导出帧率"""
    FR_24 = "24fps"
    FR_25 = "25fps"
    FR_30 = "30fps"
    FR_50 = "50fps"
    FR_60 = "60fps"

class ControlFinder:
    """控件查找器，封装部分与控件查找相关的逻辑"""

    @staticmethod
    def desc_matcher(target_desc: str, depth: int = 2, exact: bool = False) -> Callable[[uia.Control, int], bool]:
        """根据full_description查找控件的匹配器"""
        target_desc = target_desc.lower()
        def matcher(control: uia.Control, _depth: int) -> bool:
            if _depth != depth:
                return False
            full_desc: str = control.GetPropertyValue(30159).lower()
            return (target_desc == full_desc) if exact else (target_desc in full_desc)
        return matcher

    @staticmethod
    def class_name_matcher(class_name: str, depth: int = 1, exact: bool = False) -> Callable[[uia.Control, int], bool]:
        """根据ClassName查找控件的匹配器"""
        class_name = class_name.lower()
        def matcher(control: uia.Control, _depth: int) -> bool:
            if _depth != depth:
                return False
            curr_class_name: str = control.ClassName.lower()
            return (class_name == curr_class_name) if exact else (class_name in curr_class_name)
        return matcher

    @staticmethod
    def desc_exact_any_depth(target_desc: str, max_depth: int = 20) -> Callable[[uia.Control, int], bool]:
        """full_description 与 target 全字匹配，且深度不超过 max_depth（用于与导出按钮同类定位）。"""
        target_desc = target_desc.lower()

        def matcher(control: uia.Control, d: int) -> bool:
            if d < 1 or d > max_depth:
                return False
            try:
                full_desc = str(control.GetPropertyValue(30159) or "").lower()
            except Exception:
                return False
            return full_desc == target_desc

        return matcher


class JianyingController:
    """剪映控制器"""

    app: uia.WindowControl
    """剪映窗口"""
    app_status: Literal["home", "edit", "pre_export"]

    def __init__(self):
        """初始化剪映控制器, 此时剪映应该处于目录页"""
        self.get_window()

    def _click_toolbar_item_by_name(self, target: str, *, timeout: float = 12.0, depth: int = 32) -> None:
        """在编辑页剪映主窗口内点击名称匹配的功能入口。

        旧版「字幕」等在顶栏；新版多在左侧 Tab（部分版本为 CustomControl/Group，无标准 TabItem）。
        先按常见控件类型在 ``self.app`` 内查找，再遍历控件树按 Name 精确匹配并择优点击。
        """
        target_trim = (target or "").strip()

        def _name_matches(control: uia.Control) -> bool:
            first = _control_primary_label(control)
            if not first:
                return False
            return first == target_trim or first.startswith(target_trim + " ")

        control_method_names = (
            "ButtonControl",
            "TabItemControl",
            "TreeItemControl",
            "ListItemControl",
            "MenuItemControl",
            "HyperlinkControl",
            "CustomControl",
            "GroupControl",
            "PaneControl",
            "TextControl",
        )

        deadline = time.time() + timeout
        while time.time() < deadline:
            self.get_window()
            if self.app_status != "edit":
                raise exceptions.AutomationError("当前不在剪映编辑页，无法点击顶栏功能")
            for meth in control_method_names:
                ctor = getattr(self.app, meth, None)
                if ctor is None:
                    continue
                try:
                    c = ctor(searchDepth=depth, Name=target_trim)
                    if c.Exists(0):
                        c.Click(simulateMove=False)
                        return
                except Exception:
                    pass
                try:

                    def _cmp(ctrl: uia.Control, d: int) -> bool:
                        return d <= depth and _name_matches(ctrl)

                    c2 = ctor(searchDepth=depth, Compare=_cmp)
                    if c2.Exists(0):
                        c2.Click(simulateMove=False)
                        return
                except Exception:
                    pass
            try:
                if _walk_click_by_exact_first_label(self.app, target_trim, max_depth=52):
                    return
            except Exception:
                pass
            time.sleep(0.35)
        raise exceptions.AutomationError(
            f"未找到控件「{target}」（已搜索常见控件类型并遍历窗口控件树）。"
            f"请确认剪映为中文界面、已进入编辑页；若剪映更新后无障碍树不再暴露名称，"
            f"请先在剪映内手动完成「识别字幕」并取消勾选导出时的自动生成字幕。"
        )

    def _find_checkbox_containing(self, label_substring: str, depth: int = 18) -> Optional[uia.Control]:
        def matcher(control: uia.Control, d: int) -> bool:
            return d <= depth and label_substring in (control.Name or "")

        cb = self.app.CheckBoxControl(searchDepth=depth, Compare=matcher)
        if cb.Exists(0.5):
            return cb
        return None

    def _ensure_checkbox_state(self, label_substring: str, want_on: bool, *, depth: int = 18) -> None:
        deadline = time.time() + 12.0
        while time.time() < deadline:
            self.get_window()
            cb = self._find_checkbox_containing(label_substring, depth=depth)
            if cb is not None:
                try:
                    tp = cb.GetTogglePattern()
                    cur = tp.ToggleState
                    want = uia.ToggleState.On if want_on else uia.ToggleState.Off
                    if cur != want:
                        cb.Click(simulateMove=False)
                        time.sleep(0.4)
                except Exception:
                    cb.Click(simulateMove=False)
                    time.sleep(0.4)
                return
            time.sleep(0.35)
        raise exceptions.AutomationError(f"未找到包含「{label_substring}」的复选框（请展开「识别字幕」面板后重试）")

    def _any_visible_text_contains(self, needles: Tuple[str, ...], depth: int = 14) -> bool:
        for sub in needles:
            c = self.app.TextControl(
                searchDepth=depth,
                Compare=lambda ctrl, d: sub in (ctrl.Name or ""),
            )
            if c.Exists(0):
                return True
        return False

    def _control_in_left_chrome_band(self, ctrl: uia.Control, *, rel_right: float = 0.46) -> bool:
        """控件中心是否落在主窗口左侧条带（避免点到标题栏/时间轴上的无关「字幕」描述）。"""
        try:
            wr = self.app.BoundingRectangle
            cr = ctrl.BoundingRectangle
            if cr.isempty() or wr.isempty():
                return True
            return (cr.xcenter() - wr.left) / max(wr.width(), 1) < rel_right
        except Exception:
            return True

    def _find_subtitle_nav_by_full_description(self) -> Optional[uia.Control]:
        """与「导出」同源：用 UIA full_description（30159）匹配剪映内部对象名。

        具体 key 未公开文档，下列候选来自与 ``MainWindowTitleBarExportBtn`` 同类命名习惯的推测；
        若均不匹配，再在左侧控件中找 description 含 ``subtitle`` 等子串的节点。
        """
        exact_keys_list = (
            "MainWindowLeftSubtitleBtn",
            "MainWindowLeftNavSubtitleBtn",
            "MainWindowLeftNavSubtitleItem",
            "MainWindowMaterialSubtitleBtn",
            "MainWindowSubtitleNavBtn",
            "MainWindowSubtitleBtn",
            "MaterialPanelSubtitleBtn",
            "MaterialNavSubtitleItem",
            "EditorLeftSubtitleItem",
            "EditorNavSubtitleBtn",
            "NavItemSubtitle",
            "NavSubtitleBtn",
            "LeftDockSubtitleBtn",
        )
        for key in exact_keys_list:
            cmp_e = ControlFinder.desc_exact_any_depth(key, 22)
            for tn in ("TextControl", "ButtonControl", "CustomControl"):
                ctor = getattr(self.app, tn, None)
                if ctor is None:
                    continue
                try:
                    c = ctor(searchDepth=26, Compare=cmp_e)
                    if c.Exists(0.25) and self._control_in_left_chrome_band(c, rel_right=0.52):
                        return c
                except Exception:
                    pass

        exact_keys = frozenset(exact_keys_list)
        substrings = (
            "leftsubtitle",
            "left_nav_subtitle",
            "materialsubtitle",
            "navsubtitle",
            "subtitlebtn",
            "subtitle_btn",
            "subtitleitem",
            "subtitle_item",
            "mainwindowsubtitle",
            "captionbtn",
            "caption_btn",
        )
        allowed_types = frozenset(
            {
                "TextControl",
                "ButtonControl",
                "CustomControl",
                "GroupControl",
                "PaneControl",
                "ListItemControl",
            }
        )
        try:
            win = self.app.BoundingRectangle
            win_w = max(win.width(), 1)
        except Exception:
            win_w = 1920

        best: Optional[uia.Control] = None
        best_score = -10**9
        n = 0
        for ctrl, d in uia.WalkControl(self.app, False, 22):
            n += 1
            if n > 20000:
                break
            if ctrl.ControlTypeName not in allowed_types:
                continue
            if not self._control_in_left_chrome_band(ctrl, rel_right=0.48):
                continue
            try:
                fd = str(ctrl.GetPropertyValue(30159) or "").lower()
            except Exception:
                continue
            if d > 22:
                continue
            try:
                rect = ctrl.BoundingRectangle
                if rect.isempty() or rect.width() < 2 or rect.height() < 2:
                    continue
                if rect.width() > win_w * 0.75:
                    continue
            except Exception:
                continue

            score = -10**9
            if fd in exact_keys:
                score = 10000 - d * 5
            else:
                for i, frag in enumerate(substrings):
                    if frag in fd:
                        score = max(score, 3000 - i * 12 - d * 6)

            if score < -10**8:
                continue
            if any(bad in fd for bad in ("exportpath", "exportokbtn", "homepage", "titlebarexport")):
                score -= 8000
            if score > best_score:
                best_score = score
                best = ctrl

        return best

    def _subtitle_panel_has_recognize_entry(self) -> bool:
        """左侧字幕区是否已出现「识别字幕」文案（Name 或 Legacy）。"""
        n = 0
        for ctrl, _d in uia.WalkControl(self.app, False, 22):
            n += 1
            if n > 12000:
                break
            if "识别字幕" in _control_text_blob(ctrl):
                return True
        return False

    def _open_subtitle_source_panel(self) -> None:
        """打开左侧「字幕」素材区，直到出现「识别字幕」入口。

        优先用与「导出」相同的 full_description（30159）匹配内部控件名；失败再按 Name / 几何兜底。
        """
        self.get_window()
        if self.app_status != "edit":
            raise exceptions.AutomationError("请先打开草稿进入编辑页后再执行字幕识别")
        if self._subtitle_panel_has_recognize_entry():
            return
        nav = self._find_subtitle_nav_by_full_description()
        if nav is not None:
            try:
                nav.Click(simulateMove=False)
                time.sleep(0.65)
            except Exception:
                pass
            self.get_window()
            if self._subtitle_panel_has_recognize_entry():
                return
        try:
            self._click_toolbar_item_by_name("字幕")
            time.sleep(0.65)
        except exceptions.AutomationError:
            pass
        if self._subtitle_panel_has_recognize_entry():
            return
        for x, y in _geometry_subtitle_click_candidates(self.app):
            uia.Click(int(x), int(y))
            time.sleep(0.55)
            self.get_window()
            if self._subtitle_panel_has_recognize_entry():
                return
        raise exceptions.AutomationError(
            "无法打开字幕区：full_description 未匹配到字幕入口、无障碍 Name 无「字幕」，"
            "且根据「媒体/音频/文本」推算的点击也未出现「识别字幕」。"
            "请用 Inspect 查看「字幕」控件的 full_description 反馈给开发者以加入精确 key；"
            "或手动打开「字幕」完成识别后，取消导出时的自动生成字幕。"
        )

    def _click_first_control_whose_blob_contains(
        self,
        sub: str,
        *,
        max_depth: int = 28,
        max_nodes: int = 16000,
    ) -> bool:
        """在窗口内点击「文本 blob 含 sub」且大致可点、偏左/浅层的控件中得分最高者。"""
        try:
            win = self.app.BoundingRectangle
            win_left, win_w = win.left, max(win.width(), 1)
        except Exception:
            win_left, win_w = 0, 1920
        type_bonus = {
            "ButtonControl": 80,
            "HyperlinkControl": 78,
            "TabItemControl": 76,
            "ListItemControl": 74,
            "TreeItemControl": 74,
            "TextControl": 35,
            "CustomControl": 50,
            "GroupControl": 40,
        }
        best: Optional[uia.Control] = None
        best_score = -10**9
        n = 0
        for ctrl, d in uia.WalkControl(self.app, False, max_depth):
            n += 1
            if n > max_nodes:
                break
            if sub not in _control_text_blob(ctrl):
                continue
            try:
                rect = ctrl.BoundingRectangle
                if rect.isempty() or rect.width() < 2 or rect.height() < 2:
                    continue
            except Exception:
                continue
            rel_x = (rect.xcenter() - win_left) / win_w
            in_left = 60 if rel_x < 0.55 else 0
            tb = type_bonus.get(ctrl.ControlTypeName, 30)
            score = tb + in_left - d * 2
            if score > best_score:
                best_score = score
                best = ctrl
        if best is not None:
            best.Click(simulateMove=False)
            return True
        return False

    def _wait_subtitle_recognition_finish(self, timeout: float) -> None:
        """识别开始后轮询界面文案，尽量判断结束；不同版本剪映文案可能略有差异。"""
        start = time.time()
        time.sleep(2.5)
        saw_busy = False
        idle_start: Optional[float] = None
        while time.time() - start < timeout:
            self.get_window()
            if self.app_status != "edit":
                raise exceptions.AutomationError("识别过程中窗口已离开编辑页")
            if self._any_visible_text_contains(("识别失败", "字幕识别失败")):
                raise exceptions.AutomationError("剪映报告字幕识别失败，请检查素材、语言或网络后重试")
            busy = self._any_visible_text_contains(("识别中", "正在识别", "识别字幕中"))
            if busy:
                saw_busy = True
                idle_start = None
            else:
                if saw_busy:
                    now = time.time()
                    if idle_start is None:
                        idle_start = now
                    elif now - idle_start >= 12.0:
                        time.sleep(1.0)
                        return
                else:
                    if time.time() - start >= 28.0:
                        return
            time.sleep(2.0)
        raise exceptions.AutomationError(
            f"等待字幕识别结束超时（{int(timeout)} 秒）。可在剪映中手动确认进度或增大超时。"
        )

    def run_subtitle_recognition(
        self,
        *,
        clear_existing: bool = True,
        timeout: float = 900.0,
    ) -> None:
        """打开字幕区并执行：「识别字幕」→ 可选「同时清空已有字幕」→「开始识别」，并等待结束。

        依赖剪映专业版中文界面；若 UIA 树缺少名称，会尝试锚点几何点击打开字幕区。
        """
        self._open_subtitle_source_panel()
        time.sleep(0.45)
        self.get_window()
        try:
            self._click_toolbar_item_by_name("识别字幕")
        except exceptions.AutomationError:
            if not self._click_first_control_whose_blob_contains("识别字幕"):
                raise exceptions.AutomationError(
                    "未找到「识别字幕」入口。请在剪映左侧进入「字幕」后再导出，或关闭自动生成字幕并在剪映内手动识别。"
                )
        time.sleep(0.7)
        self.get_window()

        if clear_existing:
            self._ensure_checkbox_state("同时清空已有字幕", True)
        else:
            self._ensure_checkbox_state("同时清空已有字幕", False)

        self.get_window()
        clicked = False
        for meth in ("ButtonControl", "TextControl"):
            ctor = getattr(self.app, meth, None)
            if ctor is None:
                continue
            try:
                btn = ctor(searchDepth=20, Name="开始识别")
                if btn.Exists(0.5):
                    btn.Click(simulateMove=False)
                    clicked = True
                    break
            except Exception:
                pass
        if not clicked:
            clicked = self._click_first_control_whose_blob_contains("开始识别")
        if not clicked:
            raise exceptions.AutomationError("未找到「开始识别」按钮")

        print("已点击开始识别，等待剪映处理…")
        self._wait_subtitle_recognition_finish(timeout)
        print("字幕识别流程已结束（按界面文案判断）")

    def _find_export_button_in_editor(self) -> Optional[uia.Control]:
        """在编辑页中寻找“导出”按钮。

        不同剪映版本/渠道可能会调整控件的full_description或层级，因此这里做多种兜底匹配。
        """
        # 1) 原始实现：按full_description匹配
        btn = self.app.TextControl(searchDepth=2, Compare=ControlFinder.desc_matcher("MainWindowTitleBarExportBtn"))
        if btn.Exists(0):
            return btn

        # 2) 放宽搜索深度
        btn = self.app.TextControl(searchDepth=4, Compare=ControlFinder.desc_matcher("MainWindowTitleBarExportBtn"))
        if btn.Exists(0):
            return btn

        # 3) 按可见文本（中文/英文）匹配
        for name in ("导出", "Export"):
            btn = self.app.TextControl(searchDepth=6, Name=name)
            if btn.Exists(0):
                return btn

        # 4) 按full_description包含"export"兜底（不要求精确key）
        btn = self.app.TextControl(searchDepth=6, Compare=ControlFinder.desc_matcher("export", exact=False))
        if btn.Exists(0):
            return btn

        return None

    def open_draft_by_name(
        self,
        draft_name: str,
        *,
        after_click_sleep: float = 10.0,
        locate_timeout: float = 0,
    ) -> None:
        """在草稿首页打开指定名称的草稿（与 export_draft 前半段一致）。

        Args:
            draft_name: 剪映首页卡片上的草稿名（与磁盘上草稿文件夹名一致）。
            after_click_sleep: 点击草稿后等待进入编辑页的时间（秒）。
            locate_timeout: 查找首页草稿卡片的超时（秒），0 表示与旧版导出逻辑一致（立即判定）。
        """
        self.get_window()
        self.switch_to_home()
        draft_name_text = self.app.TextControl(
            searchDepth=2,
            Compare=ControlFinder.desc_matcher(f"HomePageDraftTitle:{draft_name}", exact=True),
        )
        if not draft_name_text.Exists(locate_timeout):
            raise exceptions.DraftNotFound(f"未找到名为{draft_name}的剪映草稿")
        draft_btn = draft_name_text.GetParentControl()
        assert draft_btn is not None
        draft_btn.Click(simulateMove=False)
        time.sleep(after_click_sleep)
        self.get_window()

    def export_draft(self, draft_name: str, output_path: Optional[str] = None, *,
                     resolution: Optional[ExportResolution] = None,
                     framerate: Optional[ExportFramerate] = None,
                     subtitle_recognition: bool = False,
                     clear_existing_subtitles: bool = True,
                     subtitle_recognition_timeout: float = 900.0,
                     timeout: float = 1200) -> None:
        """导出指定的剪映草稿, **目前仅支持剪映6及以下版本**

        **注意: 需要确认有导出草稿的权限(不使用VIP功能或已开通VIP), 否则可能陷入死循环**

        Args:
            draft_name (`str`): 要导出的剪映草稿名称
            output_path (`str`, optional): 导出路径, 支持指向文件夹或直接指向文件, 不指定则使用剪映默认路径.
            resolution (`Export_resolution`, optional): 导出分辨率, 默认不改变剪映导出窗口中的设置.
            framerate (`Export_framerate`, optional): 导出帧率, 默认不改变剪映导出窗口中的设置.
            subtitle_recognition (`bool`, optional): 为 True 时，在点击导出前自动打开「字幕→识别字幕」并执行识别（见 `run_subtitle_recognition`）。
            clear_existing_subtitles (`bool`, optional): 与「同时清空已有字幕」一致，仅在 `subtitle_recognition` 为 True 时有效。
            subtitle_recognition_timeout (`float`, optional): 等待识别结束的最长时间（秒），默认 15 分钟。
            timeout (`float`, optional): 导出超时时间(秒), 默认为20分钟.

        Raises:
            `DraftNotFound`: 未找到指定名称的剪映草稿
            `AutomationError`: 剪映操作失败
        """
        print(f"开始导出 {draft_name} 至 {output_path}")
        self.open_draft_by_name(draft_name, after_click_sleep=10.0, locate_timeout=0)

        if subtitle_recognition:
            self.run_subtitle_recognition(
                clear_existing=clear_existing_subtitles,
                timeout=subtitle_recognition_timeout,
            )
            time.sleep(1.0)
            self.get_window()

        # 点击导出按钮
        export_btn = self._find_export_button_in_editor()
        if export_btn is None:
            raise AutomationError("未在编辑窗口中找到导出按钮")
        export_btn.Click(simulateMove=False)
        time.sleep(10)
        self.get_window()

        # 获取原始导出路径（带后缀名）
        export_path_sib = self.app.TextControl(searchDepth=2, Compare=ControlFinder.desc_matcher("ExportPath"))
        if not export_path_sib.Exists(0):
            raise AutomationError("未找到导出路径框")
        export_path_text = export_path_sib.GetSiblingControl(lambda ctrl: True)
        assert export_path_text is not None
        export_path = export_path_text.GetPropertyValue(30159)
        print(f"剪映默认导出路径: {export_path}")

        # 设置分辨率
        if resolution is not None:
            setting_group = self.app.GroupControl(searchDepth=1,
                                                  Compare=ControlFinder.class_name_matcher("PanelSettingsGroup_QMLTYPE"))
            if not setting_group.Exists(0):
                raise AutomationError("未找到导出设置组")
            resolution_btn = setting_group.TextControl(searchDepth=2, Compare=ControlFinder.desc_matcher("ExportSharpnessInput"))
            if not resolution_btn.Exists(0.5):
                raise AutomationError("未找到导出分辨率下拉框")
            resolution_btn.Click(simulateMove=False)
            time.sleep(0.5)
            resolution_item = self.app.TextControl(
                searchDepth=2, Compare=ControlFinder.desc_matcher(resolution.value)
            )
            if not resolution_item.Exists(0.5):
                raise AutomationError(f"未找到{resolution.value}分辨率选项")
            resolution_item.Click(simulateMove=False)
            time.sleep(0.5)

        # 设置帧率
        if framerate is not None:
            setting_group = self.app.GroupControl(searchDepth=1,
                                                  Compare=ControlFinder.class_name_matcher("PanelSettingsGroup_QMLTYPE"))
            if not setting_group.Exists(0):
                raise AutomationError("未找到导出设置组")
            framerate_btn = setting_group.TextControl(searchDepth=2, Compare=ControlFinder.desc_matcher("FrameRateInput"))
            if not framerate_btn.Exists(0.5):
                raise AutomationError("未找到导出帧率下拉框")
            framerate_btn.Click(simulateMove=False)
            time.sleep(0.5)
            framerate_item = self.app.TextControl(
                searchDepth=2, Compare=ControlFinder.desc_matcher(framerate.value)
            )
            if not framerate_item.Exists(0.5):
                raise AutomationError(f"未找到{framerate.value}帧率选项")
            framerate_item.Click(simulateMove=False)
            time.sleep(0.5)


        # 点击导出（用于之后按修改时间在目录内反查真实输出文件）
        export_btn = self.app.TextControl(searchDepth=2, Compare=ControlFinder.desc_matcher("ExportOkBtn", exact=True))
        if not export_btn.Exists(0):
            raise AutomationError("未在导出窗口中找到导出按钮")
        export_started = time.time()
        export_btn.Click(simulateMove=False)
        time.sleep(5)

        # 等待导出完成
        st = time.time()
        while True:
            self.get_window()
            if self.app_status != "pre_export": continue

            succeed_close_btn = self.app.TextControl(searchDepth=2, Compare=ControlFinder.desc_matcher("ExportSucceedCloseBtn"))
            if succeed_close_btn.Exists(0):
                succeed_close_btn.Click(simulateMove=False)
                break

            if time.time() - st > timeout:
                raise AutomationError("导出超时, 时限为%d秒" % timeout)

            time.sleep(1)
        time.sleep(2)

        # 回到目录页
        self.get_window()
        self.switch_to_home()
        time.sleep(2)

        # 复制导出的文件到指定目录
        if output_path is not None:
            export_path_norm = os.path.normpath(str(export_path).replace("/", os.sep))
            try:
                # 若output_path是文件夹，则输出到该文件夹并保持原文件名
                dst = output_path
                if os.path.isdir(dst) or dst.endswith(("\\", "/")):
                    os.makedirs(dst, exist_ok=True)
                    dst = os.path.join(dst, os.path.basename(export_path_norm))
                else:
                    os.makedirs(os.path.dirname(dst) or ".", exist_ok=True)

                src = _resolve_actual_export_path(export_path_norm, export_started)
                if not os.path.isfile(src):
                    time.sleep(2.5)
                    src = _resolve_actual_export_path(export_path_norm, export_started)
                if not os.path.isfile(src):
                    raise AutomationError(
                        f"导出已完成，但在目录中未找到输出文件。\n界面路径：{export_path_norm}\n"
                        f"请确认剪映实际导出目录与文件名是否与界面一致。"
                    )

                # Windows 下跨盘移动会退化为复制+删除；这里显式捕获异常给出更可读的错误
                shutil.move(src, dst)
                output_path = dst
            except AutomationError:
                raise
            except Exception as e:
                raise AutomationError(f"导出已完成，但移动文件失败：{e}；源文件={export_path_norm}；目标={output_path}")

        print(f"导出 {draft_name} 至 {output_path} 完成")

    def switch_to_home(self) -> None:
        """切换到剪映主页"""
        if self.app_status == "home":
            return
        if self.app_status != "edit":
            raise AutomationError("仅支持从编辑模式切换到主页")
        close_btn = self.app.GroupControl(searchDepth=1, ClassName="TitleBarButton", foundIndex=3)
        close_btn.Click(simulateMove=False)
        time.sleep(2)
        self.get_window()

    def get_window(self) -> None:
        """寻找剪映窗口并尝试激活到前台（不保持长期「总在最前」）。"""
        if hasattr(self, "app") and self.app.Exists(0):
            self.app.SetTopmost(False)

        self.app = uia.WindowControl(searchDepth=1, Compare=self.__jianying_window_cmp)
        if not self.app.Exists(0):
            raise AutomationError("剪映窗口未找到")

        # 寻找可能存在的导出窗口
        export_window = self.app.WindowControl(searchDepth=1, Name="导出")
        if export_window.Exists(0):
            self.app = export_window
            self.app_status = "pre_export"

        self.app.SetActive()
        # 旧实现：SetTopmost(True) 会长期保持「总在最前」，导致用户之后用任务栏或点击窗口
        # 无法正常把剪映切到前台。改为短暂置顶再取消，仅用于把窗口抢到前台一次。
        try:
            self.app.SetTopmost(True)
            self.app.SetTopmost(False)
        except Exception:
            try:
                self.app.SetTopmost(False)
            except Exception:
                pass

    def __jianying_window_cmp(self, control: uia.WindowControl, depth: int) -> bool:
        # 不同渠道/版本窗口标题可能略有差异，这里放宽匹配
        name = (control.Name or "").strip()
        if not (("剪映" in name) or ("Jianying" in name) or ("CapCut" in name)):
            return False
        if "HomePage".lower() in control.ClassName.lower():
            self.app_status = "home"
            return True
        if "MainWindow".lower() in control.ClassName.lower():
            self.app_status = "edit"
            return True
        return False


def wait_for_jianying_controller(timeout: float = 90.0, poll: float = 0.5) -> JianyingController:
    """轮询直至剪映主窗口可被 UI 自动化连接（不负责启动进程）。"""
    deadline = time.time() + timeout
    last_err: Optional[Exception] = None
    while time.time() < deadline:
        try:
            return JianyingController()
        except AutomationError as e:
            last_err = e
        except Exception as e:
            last_err = e
        time.sleep(poll)
    tail = f"{last_err!s}" if last_err else "未知错误"
    raise AutomationError(f"等待剪映窗口超时（{int(timeout)} 秒）：{tail}")
