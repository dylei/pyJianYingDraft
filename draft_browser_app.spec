# -*- mode: python ; coding: utf-8 -*-
"""PyInstaller onedir 配置：生成 dist/爆款智剪/ 目录分发。"""
import os

from PyInstaller.utils.hooks import collect_all, collect_submodules

block_cipher = None
_root = os.path.dirname(os.path.abspath(SPEC))

_datas, _binaries, _hi_ctk = collect_all("customtkinter")

_tutorial = os.path.join(_root, "readme_assets", "tutorial")
_extra_datas = []
if os.path.isdir(_tutorial):
    _extra_datas.append((_tutorial, os.path.join("readme_assets", "tutorial")))

hiddenimports = list(_hi_ctk)
hiddenimports.extend(collect_submodules("pyJianYingDraft"))
for h in (
    "send2trash",
    "pymediainfo",
    "imageio",
    "uiautomation",
    "comtypes",
    "comtypes.gen",
):
    if h not in hiddenimports:
        hiddenimports.append(h)

a = Analysis(
    [os.path.join(_root, "draft_browser_app.py")],
    pathex=[_root],
    binaries=list(_binaries),
    datas=list(_datas) + _extra_datas,
    hiddenimports=hiddenimports,
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure, a.zipped_data, cipher=block_cipher)

exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name="爆款智剪",
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=False,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
)

coll = COLLECT(
    exe,
    a.binaries,
    a.datas,
    strip=False,
    upx=False,
    upx_exclude=[],
    name="爆款智剪",
)
