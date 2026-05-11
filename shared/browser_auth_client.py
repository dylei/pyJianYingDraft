# -*- coding: utf-8 -*-
"""
爆款智剪等 CustomTkinter 界面使用：与 shared/auth.py 相同的后端协议（登录 / record_operation 扣豆），
不依赖 PyQt5；凭据存 %LOCALAPPDATA%\\pyJianYingDraft_browser\\account_credentials.json。
"""
from __future__ import annotations

import base64
import json
import os
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

try:
    import requests
except ImportError:
    requests = None  # type: ignore


def get_app_version() -> str:
    try:
        base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        vf = os.path.join(base, "version.json")
        if os.path.isfile(vf):
            with open(vf, "r", encoding="utf-8") as f:
                return str(json.load(f).get("version", "1.0.0"))
    except (OSError, json.JSONDecodeError, KeyError, TypeError):
        pass
    return "1.0.0"


CURRENT_VERSION = get_app_version()


def _credentials_path() -> Path:
    ada = os.environ.get("LOCALAPPDATA") or str(Path.home())
    root = Path(ada) / "pyJianYingDraft_browser"
    root.mkdir(parents=True, exist_ok=True)
    return root / "account_credentials.json"


def auth_api_error_message(result: Any) -> Optional[str]:
    if not isinstance(result, dict):
        return None
    err = result.get("error")
    if err:
        return str(err)
    if result.get("success") is False:
        return str(result.get("message") or result.get("msg") or "操作失败")
    return None


class BrowserAuthClient:
    """对齐 auth.AuthClient 的 HTTP 行为，便于同一套 leiyuantech 后端。"""

    def __init__(self, base_url: str = "http://leiyuantech.com:5000") -> None:
        self.base_url = base_url.rstrip("/")
        self.user_id: Optional[Any] = None
        self.username: Optional[str] = None
        self.gold_beans: Optional[Any] = None
        self._gold_config_cache: Optional[Dict[str, Any]] = None
        self._gold_config_loaded = False

    def save_credentials(self, username: str, password: str) -> None:
        path = _credentials_path()
        payload = {
            "remember_me": True,
            "username": username,
            "password_b64": base64.b64encode(password.encode("utf-8")).decode("ascii"),
        }
        tmp = path.with_suffix(".json.tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)

    def load_credentials(self) -> Tuple[Optional[str], Optional[str]]:
        path = _credentials_path()
        if not path.is_file():
            return None, None
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, json.JSONDecodeError):
            return None, None
        if not isinstance(data, dict) or not data.get("remember_me"):
            return None, None
        u = str(data.get("username") or "").strip()
        b64 = str(data.get("password_b64") or "")
        if not u or not b64:
            return None, None
        try:
            pw = base64.b64decode(b64.encode("ascii")).decode("utf-8")
        except Exception:
            return None, None
        return u, pw

    def clear_credentials(self) -> None:
        path = _credentials_path()
        try:
            if path.is_file():
                path.unlink()
        except OSError:
            pass

    def load_gold_config(self) -> bool:
        if requests is None:
            return False
        try:
            response = requests.get(f"{self.base_url}/api/get_gold_config", timeout=5)
            if response.status_code == 200:
                result = response.json()
                if isinstance(result, dict) and result.get("success") and isinstance(result.get("config"), dict):
                    self._gold_config_cache = result["config"]
                    self._gold_config_loaded = True
                    return True
        except Exception:
            pass
        return False

    def get_gold_cost(self, operation_name: str, default_cost: Optional[int] = None, **kwargs: Any) -> int:
        # 每次取价前请求最新配置；请求失败时保留上次缓存，仍按缓存键取值
        self.load_gold_config()
        if self._gold_config_cache and operation_name in self._gold_config_cache:
            try:
                return int(self._gold_config_cache[operation_name])
            except (TypeError, ValueError):
                pass
        if default_cost is not None:
            return int(default_cost)
        defaults: Dict[str, int] = {
            "导出为MP4": 1,
            "导出MP4": 1,
            "生成草稿": 1,
            "剪辑视频": 2,
        }
        return int(defaults.get(operation_name, 1))

    def record_operation(
        self,
        action: str,
        gold_change: int = 0,
        operation_details: Any = None,
    ) -> Dict[str, Any]:
        if requests is None:
            return {"error": "未安装 requests，请执行: pip install requests"}
        if not self.user_id:
            return {"error": "用户未登录"}
        try:
            payload: Dict[str, Any] = {
                "user_id": self.user_id,
                "username": self.username,
                "action": action,
                "gold_change": gold_change,
                "version": CURRENT_VERSION,
            }
            if operation_details is not None:
                payload["operation_details"] = operation_details
            response = requests.post(
                f"{self.base_url}/api/record_operation",
                json=payload,
                timeout=15,
            )
            result: Any = response.json() if response.text else {}
            if isinstance(result, dict):
                gb = result.get("gold_beans")
                if gb is None and isinstance(result.get("data"), dict):
                    gb = result["data"].get("gold_beans")
                if gb is not None:
                    self.gold_beans = gb
                return result
            return {"error": "服务器响应格式错误"}
        except requests.exceptions.RequestException as e:
            return {"error": f"记录操作失败: {e}"}

    def login(self, username: str, password: str) -> Optional[Dict[str, Any]]:
        if requests is None:
            return {"error": "未安装 requests，请执行: pip install requests"}
        try:
            response = requests.post(
                f"{self.base_url}/api/login",
                json={"username": username, "password": password},
                timeout=15,
            )
            try:
                return response.json()
            except Exception:
                return {"error": "服务器响应格式错误"}
        except requests.exceptions.RequestException:
            return None

    def register(self, username: str, password: str) -> Dict[str, Any]:
        if requests is None:
            return {"error": "未安装 requests，请执行: pip install requests"}
        try:
            response = requests.post(
                f"{self.base_url}/api/register",
                json={"username": username, "password": password},
                timeout=15,
            )
            try:
                out: Any = response.json()
                return out if isinstance(out, dict) else {"error": "服务器响应格式错误"}
            except Exception:
                return {"error": "服务器响应格式错误"}
        except requests.exceptions.RequestException as e:
            return {"error": f"请求失败: {e}"}

    def ping_gold_beans(self) -> Dict[str, Any]:
        """gold_change=0，仅同步余额（与 main1 中查询接口一致，action 上报为「查询豆子」）。"""
        return self.record_operation("查询豆子", 0)
