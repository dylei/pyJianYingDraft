"""剪映自动化控制，主要与自动导出有关"""

import time
import shutil
import os
import uiautomation as uia

from enum import Enum
from typing import Callable, List, Literal, Optional, Tuple

from . import exceptions
from .exceptions import AutomationError


_VIDEO_EXTS = (".mp4", ".mov", ".mkv", ".m4v")


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

class JianyingController:
    """剪映控制器"""

    app: uia.WindowControl
    """剪映窗口"""
    app_status: Literal["home", "edit", "pre_export"]

    def __init__(self):
        """初始化剪映控制器, 此时剪映应该处于目录页"""
        self.get_window()

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
                     timeout: float = 1200) -> None:
        """导出指定的剪映草稿, **目前仅支持剪映6及以下版本**

        **注意: 需要确认有导出草稿的权限(不使用VIP功能或已开通VIP), 否则可能陷入死循环**

        Args:
            draft_name (`str`): 要导出的剪映草稿名称
            output_path (`str`, optional): 导出路径, 支持指向文件夹或直接指向文件, 不指定则使用剪映默认路径.
            resolution (`Export_resolution`, optional): 导出分辨率, 默认不改变剪映导出窗口中的设置.
            framerate (`Export_framerate`, optional): 导出帧率, 默认不改变剪映导出窗口中的设置.
            timeout (`float`, optional): 导出超时时间(秒), 默认为20分钟.

        Raises:
            `DraftNotFound`: 未找到指定名称的剪映草稿
            `AutomationError`: 剪映操作失败
        """
        print(f"开始导出 {draft_name} 至 {output_path}")
        self.open_draft_by_name(draft_name, after_click_sleep=10.0, locate_timeout=0)

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
