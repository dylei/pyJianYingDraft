import os

from setuptools import setup, find_packages

_PKG_DIR = os.path.dirname(os.path.abspath(__file__))
_desc = "轻量、灵活、易上手的Python剪映草稿生成及导出工具，构建全自动化视频剪辑/混剪流水线"
for _fname in ("pypi_readme.md", "README.md"):
    _readme = os.path.join(_PKG_DIR, _fname)
    if os.path.isfile(_readme):
        with open(_readme, "r", encoding="utf-8") as _f:
            _long_description = _f.read()
        break
else:
    _long_description = _desc

setup(
    name="pyjianyingdraft",
    version="0.2.6",
    author="gary318",
    description=_desc,
    long_description=_long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/GuanYixuan/pyJianYingDraft",
    packages=find_packages(exclude=["tools", "tools.*", "ignored", "ignored.*"]),
    package_data={
        'pyJianYingDraft': ['assets/*.json']
    },
    classifiers=[
        "Programming Language :: Python :: 3",
        "Development Status :: 4 - Beta",
        "Topic :: Multimedia :: Video"
    ],
    python_requires='>=3.8',
    install_requires=[
        "pymediainfo",
        "imageio",
        "uiautomation>=2; sys_platform == 'win32'"
    ],
    extras_require={
        "gui": ["customtkinter>=5.2"],
    },
)
