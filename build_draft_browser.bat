@echo off
setlocal
cd /d "%~dp0"
python -m pip install -q pyinstaller
python -m PyInstaller --noconfirm draft_browser_app.spec
if errorlevel 1 exit /b 1
echo.
echo 输出目录: %~dp0dist\爆款智剪\
echo 运行: dist\爆款智剪\爆款智剪.exe
endlocal
