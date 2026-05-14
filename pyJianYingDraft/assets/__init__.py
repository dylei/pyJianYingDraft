"""

pyJianYingDraft 的资源管理模块，提供集中管理资源文件的方式，避免硬编码路径

"""



import sys

from pathlib import Path



ASSETS_DIR = Path(__file__).resolve().parent



ASSET_FILES = {

    "DRAFT_CONTENT_TEMPLATE": "draft_content_template.json",

    "DRAFT_META_TEMPLATE": "draft_meta_info.json",

}





def get_asset_path(asset_name: str) -> Path:

    """

    获取指定资源文件的完整路径。



    - 开发环境：当前包内 ``assets`` 目录（与 ``__init__.py`` 同级）。

    - 运行环境（PyInstaller ``sys.frozen``）：``_MEIPASS``（或 exe 旁 ``_internal``）下的 ``pyJianYingDraft/assets``。

    """

    if asset_name not in ASSET_FILES:

        raise KeyError(f"Asset '{asset_name}' not found. Available assets: {list(ASSET_FILES.keys())}")



    fname = ASSET_FILES[asset_name]



    if getattr(sys, "frozen", False):

        meipass = getattr(sys, "_MEIPASS", None)

        root = Path(meipass) if meipass else Path(sys.executable).resolve().parent / "_internal"

        file_path = root / "pyJianYingDraft" / "assets" / fname

    else:

        file_path = ASSETS_DIR / fname



    if not file_path.is_file():

        mode = "打包运行" if getattr(sys, "frozen", False) else "开发"

        raise FileNotFoundError(

            f"找不到资源文件「{fname}」（{mode}）。期望路径：\n{file_path}\n"

            "开发时请确认仓库内 pyJianYingDraft/assets 含该文件；"

            "打包请确认 spec 的 datas 已包含 pyJianYingDraft/assets。"

        )



    return file_path





__all__ = [

    "get_asset_path",

    "ASSET_FILES",

]
