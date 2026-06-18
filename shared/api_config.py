# -*- coding: utf-8 -*-
"""桌面端 API 根地址（登录、爆款模板等共用）。"""
from __future__ import annotations

import os


def api_base_url() -> str:
    """默认 localhost 便于联调；生产环境请设环境变量 JYDRAFT_API_BASE_URL。"""
    return os.environ.get("JYDRAFT_API_BASE_URL", "http://114.132.72.59:5000").rstrip("/")
