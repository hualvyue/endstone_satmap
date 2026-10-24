# -*- coding: utf-8 -*-
"""
SatMap — 基于 uNmINeD 的 Endstone 卫星地图插件（重构版）

相比旧版 bdslm 的改动：
  1. 网页资源随插件分发，渲染后自动覆盖 uNmINeD 生成的 html，并按维度注入过滤器；
  2. 自动探测 GreenMoon 面板（默认 plugins/greenmoon_panel/web），有则把地图输出到
     它的 /map 子目录，由面板的 web 服务托管；没有则自己起一个轻量 web 服务器；
  3. 有 GreenMoon 时通过 gm.panel 注册设置面板，没有 GreenMoon 就不提供任何设置面板
     （settings.html 已移除，配置走 config.json / 命令）；
  4. 实时玩家数据改为写静态 JSON（players.json / chat.json），
     这样无论谁托管静态文件都能看到实时坐标，不再依赖自建服务器的 /api；
  5. Linux 下自动给 unmined 的 lic 目录递归 777，避免权限报错。
"""

import html
import importlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from endstone.plugin import Plugin
from endstone.command import Command, CommandSender
from endstone.event import (
    PlayerChatEvent,
    PlayerJoinEvent,
    PlayerQuitEvent,
    event_handler,
)

# --------------------------------------------------------------------------- #
# 常量
# --------------------------------------------------------------------------- #

LOG_PREFIX = "§e[喵~卫星地图]§f "

DEFAULT_DIMENSION_IDS: Dict[str, str] = {
    "overworld": "0",
    "nether": "-1",
    "the_end": "2",
}

# 维度名 -> (中文名, 图标, css class)
DIMENSION_DISPLAY: Dict[str, Tuple[str, str, str]] = {
    "overworld": ("主世界", "🏞️", "overworld"),
    "nether": ("下界", "🔥", "nether"),
    "the_end": ("末地", "🌌", "the_end"),
}

# GreenMoon 插件目录名线索（小写匹配）
GM_DIR_HINTS = ("greenmoon", "green_moon", "green-moon")
# GreenMoon 内部可能的 web 静态目录名
GM_WEB_NAMES = ("web", "www", "webroot", "html", "public", "static")
# lic 目录可能的名字
LIC_NAMES = ("lic", "licenses", "license")

# GreenMoon 面板注册重试参数
# 插件加载顺序不保证：本插件可能先于 GreenMoon 启用，此时 ``gm`` 顶层别名
# 尚未注入 sys.modules，``import gm.panel`` 会抛 ModuleNotFoundError。
# 首次失败后按固定间隔重试，等 GreenMoon 启用完成即可注册成功。
GM_PANEL_RETRIES = 30
GM_PANEL_RETRY_INTERVAL = 2.0


class SatMapPlugin(Plugin):
    version = "2.0.4"
    api_version = "0.11"

    commands = {
        "satmap": {
            "description": "卫星地图（uNmINeD）",
            "usages": [
                "/satmap render [维度|all]",
                "/satmap status",
                "/satmap reload",
                "/satmap marker <list|add|remove>",
                "/satmap apply",
                "/satmap fixperm",
            ],
            "permissions": ["satmap.command"],
        }
    }

    permissions = {
        "satmap.command": {
            "description": "允许使用 /satmap 命令（默认 OP）",
            "default": "op",
        }
    }

    # ------------------------------------------------------------------ #
    # 生命周期
    # ------------------------------------------------------------------ #

    def __init__(self):
        super().__init__()
        self._config: Dict[str, Any] = {}
        self._markers: List[Dict[str, Any]] = []
        self._players: Dict[str, Dict[str, Any]] = {}
        self._chat_history: List[Dict[str, Any]] = []
        self._lock = threading.RLock()

        self._dimension_ids: Dict[str, str] = dict(DEFAULT_DIMENSION_IDS)
        self._rendering = False
        self._render_lock = threading.Lock()

        self._web_root: Optional[Path] = None
        self._gm_web_dir: Optional[Path] = None
        self._gm_panel_ok = False
        self._stopping = False

        self._server: Optional[ThreadingHTTPServer] = None
        self._server_thread: Optional[threading.Thread] = None

    def on_load(self) -> None:
        self.logger.info(LOG_PREFIX + "插件加载中喵…")
        self._migrate_legacy()
        self._load_config()
        self._load_markers()

    def _migrate_legacy(self) -> None:
        """从旧版 bdslm 插件目录迁移配置/标记，省得手动复制。"""
        legacy = self.plugins_dir / "bdslm"
        if not legacy.is_dir():
            return
        try:
            self.data_dir.mkdir(parents=True, exist_ok=True)
            if not self.config_path.exists() and (legacy / "config.json").is_file():
                shutil.copyfile(legacy / "config.json", self.config_path)
                self.logger.info(LOG_PREFIX + "§a已从旧版 bdslm 迁移 config.json 喵")
            if not self.markers_path.exists() and (legacy / "markers.json").is_file():
                shutil.copyfile(legacy / "markers.json", self.markers_path)
                self.logger.info(LOG_PREFIX + "§a已从旧版 bdslm 迁移 markers.json 喵")
        except Exception as e:
            self.logger.warning(LOG_PREFIX + f"§e迁移旧配置失败喵: {e}")

    def on_enable(self) -> None:
        self.logger.info(LOG_PREFIX + "正在启动喵…")

        # ★ 重载时 on_disable 会把 _stopping 置 True，这里必须复位，
        #   否则重新启用后不会重试注册面板、也不重启自带服务器。
        self._stopping = False

        # 1. 决定网页输出根目录（GreenMoon / 自建）
        self._resolve_web_root()
        self._web_root.mkdir(parents=True, exist_ok=True)

        # 2. 释放网页模板到数据目录（用户可自行修改）
        self._ensure_assets()
        self._deploy_nav_page()

        # 3. 探测 GreenMoon 面板并注册设置面板
        self._register_greenmoon_panel(GM_PANEL_RETRIES)

        # 4. Linux 权限修复
        self._fix_permissions(log=True)

        # 5. 没有 GreenMoon（或强制开启）才自己起服务器
        if self._should_start_own_server():
            self._start_web_server()

        # 6. 事件 + 定时任务
        self.register_events(self)
        self._start_schedulers()

        # 7. 后台首轮渲染
        threading.Thread(target=self._initial_render_all, daemon=True).start()

        # 8. 立刻写一份实时数据，避免刚开服/刚开面板时前端读到 404
        self._sample_players()
        self._write_live_data()

        self.logger.info(LOG_PREFIX + f"加载完毕喵 | 版本 §b{self.version}")
        self.logger.info(LOG_PREFIX + "地图地址喵: §b" + self._public_url_hint())

    def on_disable(self) -> None:
        self.logger.info(LOG_PREFIX + "正在关闭喵…")
        self._stopping = True
        self._stop_web_server()
        self._save_markers()
        self.logger.info(LOG_PREFIX + "插件已卸载喵")

    # ------------------------------------------------------------------ #
    # 命令
    # ------------------------------------------------------------------ #

    def on_command(self, sender: CommandSender, command: Command, args: list) -> bool:
        if command.name != "satmap":
            return False

        if not args:
            self._send_usage(sender)
            return True

        action = str(args[0]).lower()

        if action == "render":
            self._cmd_render(sender, args)
        elif action == "status":
            self._cmd_status(sender)
        elif action == "reload":
            self._load_config()
            self._load_markers()
            self._trim_chat_history()
            self._resolve_web_root()
            self._deploy_nav_page()
            self._restart_web_server_if_needed()
            sender.send_message("§a配置已重载喵!")
        elif action == "marker":
            self._cmd_marker(sender, args)
        elif action == "fixperm":
            ok = self._fix_permissions(log=True, force=True)
            sender.send_message("§a权限修复完成喵!" if ok else "§c没有找到 lic 目录喵，请在 config.json 的 paths.licFolder 指定喵")

        elif action in ("apply", "deploy"):
            # 手动重新铺一遍网页：导航页 + 覆盖各维度 html + 标记
            count = self._apply_all_html()
            self._apply_markers_all()
            self._deploy_nav_page()
            self._write_live_data()
            sender.send_message(f"§a已重新铺设网页喵（覆盖 {count} 个维度的地图页面）")
        else:
            self._send_usage(sender)

        return True

    def _send_usage(self, sender: CommandSender) -> None:
        sender.send_message("§e[喵~卫星地图] 用法喵:")
        sender.send_message("  §f/satmap render [维度|all] §7- 立即渲染（默认主世界）")
        sender.send_message("  §f/satmap status §7- 查看运行状态")
        sender.send_message("  §f/satmap reload §7- 重载配置与网页")
        sender.send_message("  §f/satmap marker list|add|remove §7- 地图标记")
        sender.send_message("  §f/satmap apply §7- 手动重铺网页（改了模板后用它）")
        sender.send_message("  §f/satmap fixperm §7- 手动修复 lic 目录权限")

    def _cmd_render(self, sender: CommandSender, args: list) -> None:
        target = args[1] if len(args) > 1 else "overworld"
        if target.lower() == "all":
            dims = self._enabled_dimensions()
            if not dims:
                sender.send_message("§c没有启用任何维度喵!")
                return
            sender.send_message(f"§a开始渲染全部维度喵: {', '.join(dims)}")
            threading.Thread(target=self._render_many, args=(dims,), daemon=True).start()
            return

        if target not in self._dimension_ids:
            sender.send_message(f"§c未知维度喵: {target}，可选喵: {', '.join(self._dimension_ids)}")
            return

        sender.send_message(f"§a开始渲染 {target} 维度喵…")
        if self._render(target, wait=False):
            sender.send_message("§a渲染已启动喵!")
        else:
            sender.send_message(
                "§c渲染正在进行中喵，请稍后再试喵!" if self._rendering
                else "§c渲染启动失败喵! 请检查 unmined-cli 是否已配置喵"
            )

    def _cmd_status(self, sender: CommandSender) -> None:
        ws = self._config.get("webserver", {})
        auto = self._config.get("autoRend", {})
        cli = self._get_unmined_cli_path()
        lic = self._find_lic_folder()

        sender.send_message("§e[喵~卫星地图] 状态喵:")
        sender.send_message("  §f托管方式: " + (
            "§aGreenMoon 面板喵" if self._gm_web_dir else "§b自带 Web 服务器喵"
        ))
        if self._gm_web_dir:
            sender.send_message(f"  §f面板 web 目录: §7{self._gm_web_dir}")
            sender.send_message("  §f设置面板: " + ("§a已注册喵" if self._gm_panel_ok else "§c未注册（gm 不可用/无权限）喵"))
        else:
            sender.send_message("  §fWeb 服务器: " + ("§a运行中喵" if self._server else "§c已停止喵"))
            sender.send_message(f"  §f监听: §7{ws.get('bindAddress', '0.0.0.0')}:{ws.get('port', 5110)}")
        sender.send_message(f"  §f地图目录: §7{self._web_root}")
        sender.send_message(f"  §f访问地址: §b{self._public_url_hint()}")
        sender.send_message(f"  §f自动渲染: {'§a开启喵' if auto.get('enable', True) else '§c关闭喵'}（周期 {auto.get('cycle', 30)} 分钟）")
        sender.send_message(f"  §f正在渲染: {'§a是喵' if self._rendering else '§c否喵'}")
        sender.send_message("  §funmined-cli: " + ("§a已配置喵" if cli else "§c未找到喵"))
        if cli:
            sender.send_message(f"    §7{cli}")
        sender.send_message("  §flic 目录: " + (f"§a{lic}喵" if lic else "§c未找到喵"))
        sender.send_message(f"  §f启用维度: §7{', '.join(self._enabled_dimensions()) or '无'}")
        dims = self._enabled_dimensions()
        if dims:
            sample = f"{self._get_url_prefix()}/{dims[0]}/"
            if self._get_link_style() == "file":
                sample += "index.html"
            sender.send_message(f"  §f维度链接示例: §b{sample}")

    def _cmd_marker(self, sender: CommandSender, args: list) -> None:
        if len(args) < 2:
            sender.send_message("§e用法喵: /satmap marker <list|add <文本> [x] [z]|remove <序号>>")
            return

        sub = str(args[1]).lower()

        if sub == "list":
            if not self._markers:
                sender.send_message("§e当前没有标记喵")
                return
            sender.send_message("§e[喵~卫星地图] 标记列表喵:")
            for i, m in enumerate(self._markers, 1):
                sender.send_message(f"  §f#{i} §7({m.get('x')}, {m.get('z')}) §f{m.get('text', '')}")
            return

        if sub == "add":
            rest = args[2:]
            # 支持：add <文本> [x] [z]
            x = z = None
            if len(rest) >= 3:
                try:
                    z = int(float(rest[-1]))
                    x = int(float(rest[-2]))
                    rest = rest[:-2]
                except ValueError:
                    pass
            text = " ".join(rest).strip()
            if not text:
                sender.send_message("§e用法喵: /satmap marker add <文本> [x] [z]")
                return
            if x is None:
                try:
                    loc = sender.location
                    x, z = int(loc.x), int(loc.z)
                except Exception:
                    sender.send_message("§c拿不到你的坐标喵，请手动输入: /satmap marker add <文本> <x> <z>")
                    return
            self._markers.append({"x": x, "z": z, "text": text})
            self._save_markers()
            self._apply_markers_all()
            sender.send_message(f"§a已添加标记喵 #{len(self._markers)} §7({x}, {z}) {text}")
            return

        if sub == "remove":
            if len(args) < 3:
                sender.send_message("§e用法喵: /satmap marker remove <序号>")
                return
            try:
                idx = int(args[2]) - 1
            except ValueError:
                sender.send_message("§c序号必须是数字喵")
                return
            if idx < 0 or idx >= len(self._markers):
                sender.send_message("§c序号超出范围喵")
                return
            removed = self._markers.pop(idx)
            self._save_markers()
            self._apply_markers_all()
            sender.send_message(f"§a已删除标记喵: {removed.get('text', '')}")
            return

        sender.send_message("§e用法喵: /satmap marker <list|add|remove>")

    # ------------------------------------------------------------------ #
    # 事件
    # ------------------------------------------------------------------ #

    @event_handler
    def _on_player_join(self, event: PlayerJoinEvent) -> None:
        self._sample_players()

    @event_handler
    def _on_player_quit(self, event: PlayerQuitEvent) -> None:
        self._sample_players()

    @event_handler
    def _on_player_chat(self, event: PlayerChatEvent) -> None:
        entry = {
            "player": event.player.name,
            "message": event.message,
            "timestamp": time.time(),
        }
        with self._lock:
            self._chat_history.append(entry)
            self._trim_chat_history()

    def _trim_chat_history(self) -> None:
        max_messages = int(self._config.get("webserver", {}).get("maxChatMessages", 10))
        while len(self._chat_history) > max_messages:
            self._chat_history.pop(0)

    # ------------------------------------------------------------------ #
    # 路径 / 配置
    # ------------------------------------------------------------------ #

    @property
    def data_dir(self) -> Path:
        return Path(self.data_folder)

    @property
    def config_path(self) -> Path:
        return self.data_dir / "config.json"

    @property
    def markers_path(self) -> Path:
        return self.data_dir / "markers.json"

    @property
    def assets_dir(self) -> Path:
        return Path(__file__).parent / "assets"

    @property
    def plugins_dir(self) -> Path:
        """Endstone 的 plugins 目录（插件数据目录的上一级）"""
        return self.data_dir.parent

    @property
    def server_root(self) -> Path:
        return self.plugins_dir.parent

    def _default_config(self) -> Dict[str, Any]:
        return {
            "webserver": {
                # 仅在「没有 GreenMoon」时生效
                "enable": True,
                "port": 5110,
                "bindAddress": "0.0.0.0",
                # 就算有 GreenMoon 也强制起自己的服务器（调试用）
                "alwaysStart": False,
                "mapTitle": "default",
                "maxChatMessages": 10,
            },
            "greenmoon": {
                # 是否启用 GreenMoon 集成（false = 完全忽略面板）
                "enable": True,
                # 留空 = 自动探测；也可手动写死，例如 plugins/greenmoon_panel/web
                "webDir": "",
                # 挂在面板 web 目录下的子目录名 -> xxx/map/
                "subdir": "map",
                # 网页里拼 URL 用的前缀。
                # 留空 = 自动：GreenMoon 托管时取 "/<subdir>"（即 /map），自带服务器时为根。
                # 面板做了奇怪的重定向导致链接不对时，可手写成 "/map" 或 ""。
                "urlPrefix": "",
                # 维度链接形式：
                #   "dir"  -> /map/overworld/            （默认，依赖服务器做目录索引）
                #   "file" -> /map/overworld/index.html  （服务器不认目录时用这个）
                "linkStyle": "dir",
                # 有面板时把设置项注册进面板
                "usePanel": True,
            },
            "mapRender": {
                "maxZoomLevel": -2,
                "minZoomLevel": 4,
                "imageFormat": "webp",
                "dimensions": {
                    "overworld": True,
                    "nether": True,
                    "the_end": True,
                },
                "nether": {
                    "mode": "slice",
                    "topY": 64,
                    "bottomY": 0,
                    "gndxray": True,
                },
            },
            "autoRend": {
                "enable": True,
                "cycle": 30,
            },
            "players": {
                "enable": True,
                # 采样间隔（tick，20 = 1 秒）
                "sampleIntervalTicks": 20,
                # 前端刷新 / 写文件间隔（秒）
                "refreshInterval": 5,
            },
            "paths": {
                "unminedCli": "",
                "worldPath": "",
                "licFolder": "",
            },
            "permissions": {
                "chmodLic": True,
                "chmodOnRender": True,
                "chmodUnminedCli": True,
            },
            "dimensionIds": dict(DEFAULT_DIMENSION_IDS),
        }

    def _load_config(self) -> None:
        cfg = self._default_config()
        if self.config_path.exists():
            try:
                with open(self.config_path, encoding="utf-8") as f:
                    user_config = json.load(f)
                if isinstance(user_config, dict):
                    self._merge_config(cfg, user_config)
                    # 维度开关是「整体替换」语义：没勾选的维度必须真的关掉，
                    # 否则 dict 深合并会把默认的 True 又带回来
                    dims = (user_config.get("mapRender") or {}).get("dimensions")
                    if isinstance(dims, dict):
                        cfg["mapRender"]["dimensions"] = {str(k): bool(v) for k, v in dims.items()}
            except Exception as e:
                self.logger.warning(LOG_PREFIX + f"配置加载失败喵，使用默认值: {e}")

        self._config = cfg
        dim_ids = cfg.get("dimensionIds") or {}
        self._dimension_ids = {str(k): str(v) for k, v in dim_ids.items()} or dict(DEFAULT_DIMENSION_IDS)
        for name in DEFAULT_DIMENSION_IDS:
            self._dimension_ids.setdefault(name, DEFAULT_DIMENSION_IDS[name])

        # 配置里启用过的维度也要有 ID
        for name in (cfg.get("mapRender", {}).get("dimensions") or {}):
            self._dimension_ids.setdefault(str(name), str(name))

        self._save_config()

    def _save_config(self) -> None:
        try:
            self.data_dir.mkdir(parents=True, exist_ok=True)
            with open(self.config_path, "w", encoding="utf-8") as f:
                json.dump(self._config, f, indent=4, ensure_ascii=False)
        except Exception as e:
            self.logger.warning(LOG_PREFIX + f"配置保存失败喵: {e}")

    @staticmethod
    def _js_string(value: str) -> str:
        """转成可安全嵌入 JS 单引号字符串的内容（保留中文，转义单引号/反斜杠）。"""
        return json.dumps(str(value), ensure_ascii=False)[1:-1].replace("'", "\\'")

    @staticmethod
    def _merge_config(base: dict, override: dict) -> None:
        for k, v in override.items():
            if k in base and isinstance(base[k], dict) and isinstance(v, dict):
                SatMapPlugin._merge_config(base[k], v)
            else:
                base[k] = v

    def _enabled_dimensions(self) -> List[str]:
        dims = self._config.get("mapRender", {}).get("dimensions") or {}
        return [str(k) for k, v in dims.items() if v]

    # ------------------------------------------------------------------ #
    # GreenMoon 探测
    # ------------------------------------------------------------------ #

    def _detect_greenmoon_web_dir(self) -> Optional[Path]:
        """返回 GreenMoon 的 web 静态目录，找不到返回 None。"""
        gm_cfg = self._config.get("greenmoon", {})

        # 1) 手动指定
        manual = str(gm_cfg.get("webDir", "") or "").strip()
        if manual:
            p = Path(manual)
            if not p.is_absolute():
                p = self.server_root / p
            if p.is_dir():
                return p
            self.logger.warning(LOG_PREFIX + f"§e配置的 GreenMoon web 目录不存在喵: {p}")

        # 2) 已加载的插件里找（最可靠）
        for folder in self._greenmoon_plugin_folders():
            web = self._find_web_subdir(folder)
            if web:
                return web

        # 3) 扫 plugins 目录
        if self.plugins_dir.is_dir():
            try:
                entries = sorted(self.plugins_dir.iterdir(), key=lambda p: p.name.lower())
            except Exception:
                entries = []
            for entry in entries:
                if not entry.is_dir():
                    continue
                if not any(hint in entry.name.lower() for hint in GM_DIR_HINTS):
                    continue
                web = self._find_web_subdir(entry)
                if web:
                    return web

        return None

    def _greenmoon_plugin_folders(self) -> List[Path]:
        folders: List[Path] = []
        try:
            pm = self.server.plugin_manager
        except Exception:
            return folders
        try:
            plugins = pm.plugins
        except Exception:
            plugins = None

        items = []
        if isinstance(plugins, dict):
            items = list(plugins.values())
        elif isinstance(plugins, (list, tuple)):
            items = list(plugins)

        for plugin in items:
            name = ""
            folder = None
            try:
                name = str(getattr(plugin, "name", "") or "")
            except Exception:
                pass
            try:
                folder = Path(getattr(plugin, "data_folder", "") or "")
            except Exception:
                folder = None
            if not name and folder is not None:
                name = folder.name
            if any(hint in name.lower() for hint in GM_DIR_HINTS) and folder:
                folders.append(folder)
        return folders

    @staticmethod
    def _find_web_subdir(base: Path) -> Optional[Path]:
        if not base or not base.is_dir():
            return None
        for name in GM_WEB_NAMES:
            cand = base / name
            if cand.is_dir():
                return cand
        # 再退一步：base 本身就是 web 目录（里面直接有 index.html 之类）
        try:
            if any(base.iterdir()):
                return base
        except Exception:
            pass
        return None

    def _resolve_web_root(self) -> Path:
        """决定地图网页的输出根目录。"""
        gm_cfg = self._config.get("greenmoon", {})
        self._gm_web_dir = None

        if gm_cfg.get("enable", True):
            web = self._detect_greenmoon_web_dir()
            if web:
                self._gm_web_dir = web
                subdir = str(gm_cfg.get("subdir", "map") or "map").strip("/")
                self._web_root = web / subdir if subdir else web
                self.logger.info(LOG_PREFIX + f"§a检测到 GreenMoon 面板喵，地图将挂载到: §f{self._web_root}")
                return self._web_root
            self.logger.info(LOG_PREFIX + "§e未检测到 GreenMoon 面板，使用自带 Web 服务器喵")

        self._web_root = self.data_dir / "web"
        return self._web_root

    def _should_start_own_server(self) -> bool:
        ws = self._config.get("webserver", {})
        if not ws.get("enable", True):
            return False
        if ws.get("alwaysStart", False):
            return True
        return self._gm_web_dir is None

    def _public_url_hint(self) -> str:
        ws = self._config.get("webserver", {})
        subdir = str(self._config.get("greenmoon", {}).get("subdir", "map") or "map").strip("/")
        if self._gm_web_dir:
            return f"http://<面板地址>/{subdir}/"
        bind = ws.get("bindAddress", "0.0.0.0")
        host = "127.0.0.1" if bind in ("0.0.0.0", "", "::") else bind
        return f"http://{host}:{ws.get('port', 5110)}/"

    # ------------------------------------------------------------------ #
    # GreenMoon 设置面板（gm.panel）
    # ------------------------------------------------------------------ #

    def _retry_gm_panel_later(self, retries_left: int, reason: str) -> bool:
        """面板注册失败（通常是 GreenMoon 还没启用）时，安排稍后重试。

        返回 True 表示已排入重试；False 表示不再重试（次数耗尽或正在关闭）。
        ``_stopping`` 由 on_disable 置位，避免插件卸载后仍残留定时器。
        """
        if retries_left <= 0 or getattr(self, "_stopping", False):
            return False
        self.logger.info(
            LOG_PREFIX
            + f"§e{reason}，{GM_PANEL_RETRY_INTERVAL:g}s 后重试注册（剩余 {retries_left} 次）喵"
        )
        try:
            timer = threading.Timer(
                GM_PANEL_RETRY_INTERVAL,
                self._register_greenmoon_panel,
                kwargs={"retries_left": retries_left - 1},
            )
            timer.daemon = True
            timer.start()
        except Exception as e:
            self.logger.warning(LOG_PREFIX + f"§e安排面板注册重试失败喵: {e}")
            return False
        return True

    def _register_greenmoon_panel(self, retries_left: int = 0) -> bool:
        gm_cfg = self._config.get("greenmoon", {})
        if not gm_cfg.get("enable", True) or not gm_cfg.get("usePanel", True):
            return False
        if not self._gm_web_dir:
            # 没有面板就不提供设置面板（按需求：去掉 settings.html）
            return False

        try:
            gm_panel = importlib.import_module("gm.panel")
        except Exception as e:
            # ★ 加载顺序不保证：GreenMoon 可能晚于本插件启用，此时 gm 别名
            #   还没注入。先排重试，而不是直接放弃（否则先加载的插件永远挂不上）。
            if not self._retry_gm_panel_later(
                retries_left, f"GreenMoon 面板模块尚未就绪（{e}）"
            ):
                self.logger.info(
                    LOG_PREFIX + f"§e未检测到 GreenMoon 面板模块（{e}），不注册设置面板喵"
                )
            return False

        fields = [
            {"key": "mapTitle", "type": "text", "label": "地图标题", "default": "default"},
            {"key": "autoRender", "type": "bool", "label": "启用自动渲染", "default": True},
            {"key": "autoRenderCycle", "type": "text", "label": "自动渲染周期（分钟）", "default": "30"},
            {"key": "renderDimensions", "type": "text", "label": "渲染维度（逗号分隔，可选 overworld/nether/the_end）", "default": "overworld,nether,the_end"},
            {"key": "imageFormat", "type": "text", "label": "瓦片格式（webp / png / jpg）", "default": "webp"},
            {"key": "maxZoomLevel", "type": "text", "label": "最大缩放（zoomin，越小越清晰）", "default": "-2"},
            {"key": "minZoomLevel", "type": "text", "label": "最小缩放（zoomout）", "default": "4"},
            {"key": "worldPath", "type": "text", "label": "存档路径（留空自动探测）", "default": ""},
            {"key": "unminedCli", "type": "text", "label": "unmined-cli 路径（留空自动探测）", "default": ""},
            {"key": "licFolder", "type": "text", "label": "lic 目录（留空自动探测，Linux 下自动 777）", "default": ""},
            {"key": "showPlayers", "type": "bool", "label": "显示实时玩家位置", "default": True},
        ]

        try:
            result = gm_panel.register(
                plugin_id="satmap",
                title="卫星地图",
                icon="🛰️",
                fields=fields,
                loader=self._panel_loader,
                saver=self._panel_saver,
            )
            # register() 正常返回 (ok, msg)；ok 为假也视为失败并重试。
            ok = True
            msg = ""
            if isinstance(result, tuple) and result:
                ok = bool(result[0])
                msg = str(result[1]) if len(result) > 1 else ""
            if not ok:
                raise RuntimeError(msg or "register() 返回失败")
            self._gm_panel_ok = True
            self.logger.info(LOG_PREFIX + "§a已把设置面板注册到 GreenMoon 面板喵")
            return True
        except Exception as e:
            # 可能是 GmNotReady（面板模块已导入但主插件尚未 attach）等，同样重试。
            if not self._retry_gm_panel_later(
                retries_left, f"注册 GreenMoon 设置面板失败（{e}）"
            ):
                self._gm_panel_ok = False
                self.logger.warning(
                    LOG_PREFIX
                    + f"§e注册 GreenMoon 设置面板失败喵（{e}），设置请改 config.json 或用命令喵"
                )
            return False

    def _panel_loader(self) -> Dict[str, Any]:
        """GreenMoon 面板打开设置时读取当前值。必须快速返回。"""
        try:
            mr = self._config.get("mapRender", {})
            auto = self._config.get("autoRend", {})
            paths = self._config.get("paths", {})
            return {
                "mapTitle": self._config.get("webserver", {}).get("mapTitle", "default"),
                "autoRender": bool(auto.get("enable", True)),
                "autoRenderCycle": str(auto.get("cycle", 30)),
                "renderDimensions": ",".join(self._enabled_dimensions()),
                "imageFormat": mr.get("imageFormat", "webp"),
                "maxZoomLevel": str(mr.get("maxZoomLevel", -2)),
                "minZoomLevel": str(mr.get("minZoomLevel", 4)),
                "worldPath": paths.get("worldPath", ""),
                "unminedCli": paths.get("unminedCli", ""),
                "licFolder": paths.get("licFolder", ""),
                "showPlayers": bool(self._config.get("players", {}).get("enable", True)),
            }
        except Exception:
            return {}

    def _panel_saver(self, values: Dict[str, Any]) -> Tuple[bool, str]:
        """GreenMoon 面板点保存时回调。必须快速返回，重活丢后台线程。"""
        try:
            v = values or {}
            ws = self._config.setdefault("webserver", {})
            auto = self._config.setdefault("autoRend", {})
            mr = self._config.setdefault("mapRender", {})
            paths = self._config.setdefault("paths", {})
            players = self._config.setdefault("players", {})

            title = str(v.get("mapTitle", ws.get("mapTitle", "default")))
            ws["mapTitle"] = title

            auto["enable"] = bool(v.get("autoRender", auto.get("enable", True)))
            try:
                auto["cycle"] = max(1, int(str(v.get("autoRenderCycle", auto.get("cycle", 30)))))
            except ValueError:
                pass

            dims = str(v.get("renderDimensions", ""))
            if dims.strip():
                picked = [d.strip() for d in dims.split(",") if d.strip()]
                mr["dimensions"] = {d: True for d in picked}
                for d in picked:
                    self._dimension_ids.setdefault(d, DEFAULT_DIMENSION_IDS.get(d, d))

            fmt = str(v.get("imageFormat", mr.get("imageFormat", "webp"))).strip().lower()
            if fmt:
                mr["imageFormat"] = fmt
            for key, cfg_key in (("maxZoomLevel", "maxZoomLevel"), ("minZoomLevel", "minZoomLevel")):
                try:
                    mr[cfg_key] = int(str(v.get(key, mr.get(cfg_key))))
                except ValueError:
                    pass

            paths["worldPath"] = str(v.get("worldPath", paths.get("worldPath", "")))
            paths["unminedCli"] = str(v.get("unminedCli", paths.get("unminedCli", "")))
            paths["licFolder"] = str(v.get("licFolder", paths.get("licFolder", "")))
            players["enable"] = bool(v.get("showPlayers", players.get("enable", True)))

            self._save_config()
            self._load_config()

            # 重活（重新部署网页 / 修权限 / 按需重启自带服务器）丢后台
            threading.Thread(target=self._after_panel_save, daemon=True).start()
            return True, "已保存喵，1 秒后生效～"
        except Exception as e:
            return False, f"保存失败: {e}"

    def _after_panel_save(self) -> None:
        try:
            self._resolve_web_root()
            self._deploy_nav_page()
            self._fix_permissions(log=False)
            self._restart_web_server_if_needed()
        except Exception as e:
            self.logger.warning(LOG_PREFIX + f"应用面板设置时出错喵: {e}")

    # ------------------------------------------------------------------ #
    # 网页资源
    # ------------------------------------------------------------------ #

    @staticmethod
    def _template_version(text: str) -> tuple:
        m = re.search(r"satmap-template-version:\s*([\d.]+)", text or "")
        if not m:
            return (0,)
        try:
            return tuple(int(p) for p in m.group(1).split("."))
        except ValueError:
            return (0,)

    def _ensure_assets(self) -> None:
        """把包内网页模板复制到数据目录，方便用户自己改。

        升级插件时，如果包内模板比数据目录里的新，就覆盖（旧的备份为 .bak）；
        数据目录里的版本更新或相同则保留，不破坏用户的自定义。
        """
        dst_dir = self.data_dir / "assets"
        try:
            dst_dir.mkdir(parents=True, exist_ok=True)
        except Exception:
            return
        if not self.assets_dir.is_dir():
            return

        for name in ("nav.html", "map.html"):
            src = self.assets_dir / name
            dst = dst_dir / name
            if not src.is_file():
                continue
            try:
                src_text = src.read_text(encoding="utf-8")
            except Exception as e:
                self.logger.warning(LOG_PREFIX + f"读取网页模板失败喵 ({name}): {e}")
                continue

            if dst.exists():
                try:
                    dst_text = dst.read_text(encoding="utf-8")
                except Exception:
                    dst_text = ""
                if self._template_version(dst_text) >= self._template_version(src_text):
                    continue  # 用户手上的是新版或同版，保留
                try:
                    shutil.copyfile(dst, dst.with_name(dst.name + ".bak"))
                except Exception:
                    pass
                self.logger.info(LOG_PREFIX + f"§a网页模板已升级喵: {name}（旧版备份为 {name}.bak）")

            try:
                shutil.copyfile(src, dst)
            except Exception as e:
                self.logger.warning(LOG_PREFIX + f"释放网页模板失败喵 ({name}): {e}")

    def _read_asset(self, name: str) -> Optional[str]:
        """优先读用户改过的（数据目录），再读包内的。"""
        for p in (self.data_dir / "assets" / name, self.assets_dir / name):
            try:
                if p.is_file():
                    return p.read_text(encoding="utf-8")
            except Exception:
                continue
        self.logger.warning(LOG_PREFIX + f"§c找不到网页模板喵: {name}")
        return None

    def _build_dimension_cards(self) -> str:
        """维度按钮。href 在服务端直接写成绝对地址，前端 JS 只做兜底。"""
        prefix = self._get_url_prefix()
        style = self._get_link_style()
        cards = []
        for dim in self._enabled_dimensions():
            label, icon, cls = DIMENSION_DISPLAY.get(dim, (dim, "🗺️", "custom"))
            href = f"{prefix}/{html.escape(dim, quote=True)}/"
            if style == "file":
                href += "index.html"
            cards.append(
                f'            <a href="{href}" data-dim="{html.escape(dim, quote=True)}"'
                f' data-link-style="{style}" class="dim-btn {cls}">\n'
                f'                <span class="icon">{icon}</span>\n'
                f'                <span class="label">{html.escape(label)}</span>\n'
                f'            </a>'
            )
        if not cards:
            cards.append('            <div class="empty-msg">没有启用任何维度喵，请检查 mapRender.dimensions 配置</div>')
        return "\n".join(cards)

    def _get_url_prefix(self) -> str:
        """网页里拼 URL 的前缀（'' 表示站点根，前端会再兜底推断一次）。"""
        raw = str(self._config.get("greenmoon", {}).get("urlPrefix", "") or "").strip()
        if raw:
            prefix = raw.rstrip("/")
            if not prefix.startswith("/"):
                prefix = "/" + prefix
            return "" if prefix == "/" else prefix

        # 自动：GreenMoon 托管在 web/<subdir> 下，对外就是 /<subdir>
        if self._gm_web_dir:
            subdir = str(self._config.get("greenmoon", {}).get("subdir", "map") or "").strip("/")
            return "/" + subdir if subdir else ""

        # 自带服务器托管在根
        return ""

    def _get_link_style(self) -> str:
        style = str(self._config.get("greenmoon", {}).get("linkStyle", "dir") or "dir").strip().lower()
        return "file" if style == "file" else "dir"

    def _deploy_nav_page(self) -> None:
        """生成导航首页（每次重载/启动都会刷新，维度列表随配置变化）。"""
        if not self._web_root:
            return
        tpl = self._read_asset("nav.html")
        if not tpl:
            return

        refresh_sec = max(1, int(self._config.get("players", {}).get("refreshInterval", 5)))
        title = str(self._config.get("webserver", {}).get("mapTitle", "default"))
        page_title = "🌍 卫星地图导航 | 喵~" if title in ("default", "", None) else f"🌍 {title} | 卫星地图"
        subtitle = "选择维度" + ("（由 GreenMoon 面板托管）" if self._gm_web_dir else "")

        html_text = (
            tpl.replace("__DIM_CARDS__", self._build_dimension_cards())
            .replace("__URL_PREFIX__", self._js_string(self._get_url_prefix()))
            .replace("__PLAYERS_JSON__", "players.json")
            .replace("__CHAT_JSON__", "chat.json")
            .replace("__REFRESH_MS__", str(refresh_sec * 1000))
            .replace("__REFRESH_SEC__", str(refresh_sec))
            .replace("__PAGE_TITLE__", html.escape(page_title))
            .replace("__SUBTITLE__", html.escape(subtitle))
        )
        try:
            self._web_root.mkdir(parents=True, exist_ok=True)
            (self._web_root / "index.html").write_text(html_text, encoding="utf-8")
        except Exception as e:
            self.logger.warning(LOG_PREFIX + f"写入导航页失败喵: {e}")

    # ------------------------------------------------------------------ #
    # 渲染
    # ------------------------------------------------------------------ #

    def _get_unmined_cli_path(self) -> Optional[str]:
        cfg_path = str(self._config.get("paths", {}).get("unminedCli", "") or "").strip()
        if cfg_path:
            p = Path(cfg_path)
            if p.exists():
                return str(p)
            self.logger.warning(LOG_PREFIX + f"§e配置的 unmined-cli 不存在喵: {cfg_path}")

        which_path = shutil.which("unmined-cli")
        if which_path:
            return which_path

        candidates = []
        for base in (self.data_dir / "unmined-cli",
                     self.server_root / "unmined-cli",
                     self.plugins_dir / "unmined-cli",
                     self.plugins_dir / "bdslm" / "unmined-cli"):  # 旧插件留下的也算
            candidates.extend([base / "unmined-cli", base / "unmined-cli.exe", base / "bin" / "unmined-cli"])
        for c in candidates:
            if c.exists():
                return str(c)
        return None

    def _get_world_path(self) -> str:
        cfg_world = str(self._config.get("paths", {}).get("worldPath", "") or "").strip()
        if cfg_world:
            return cfg_world
        default = self.server_root / "worlds" / "Bedrock level"
        return str(default)

    def _fix_permissions(self, log: bool = False, force: bool = False) -> bool:
        """Linux 下递归给 lic 目录（以及 unmined-cli 本体）777。"""
        perm_cfg = self._config.get("permissions", {})
        if not force and not perm_cfg.get("chmodLic", True):
            return False
        if not sys.platform.startswith("linux"):
            if log:
                self.logger.info(LOG_PREFIX + "非 Linux 系统，跳过权限修复喵")
            return False

        ok = False
        lic = self._find_lic_folder()
        if lic:
            count = self._chmod_recursive(lic, 0o777)
            if log:
                self.logger.info(LOG_PREFIX + f"§a已修复 lic 目录权限喵: {lic}（{count} 项，777）")
            ok = True
        elif log:
            self.logger.warning(LOG_PREFIX + "§e没找到 lic 目录喵，可在 config.json 的 paths.licFolder 指定")

        if perm_cfg.get("chmodUnminedCli", True):
            cli = self._get_unmined_cli_path()
            if cli:
                try:
                    os.chmod(cli, 0o777)
                    ok = True
                except Exception as e:
                    if log:
                        self.logger.warning(LOG_PREFIX + f"§e给 unmined-cli 加权限失败喵: {e}")
        return ok

    def _find_lic_folder(self) -> Optional[Path]:
        manual = str(self._config.get("paths", {}).get("licFolder", "") or "").strip()
        if manual:
            p = Path(manual)
            if not p.is_absolute():
                p = self.server_root / p
            if p.is_dir():
                return p

        cli = self._get_unmined_cli_path()
        bases: List[Path] = []
        if cli:
            cli_path = Path(cli)
            bases.extend([cli_path.parent, cli_path.parent.parent])
        bases.extend([self.data_dir,
                      self.server_root / "unmined-cli",
                      self.plugins_dir / "unmined-cli",
                      self.plugins_dir / "bdslm" / "unmined-cli"])

        for base in bases:
            if not base or not base.is_dir():
                continue
            for name in LIC_NAMES:
                for cand in (base / name, base / name.upper()):
                    if cand.is_dir():
                        return cand
            # 往下再找两层，例如 unmined-cli/lib/lic
            try:
                children = [c for c in base.iterdir() if c.is_dir()]
            except Exception:
                children = []
            for child in children:
                for name in LIC_NAMES:
                    cand = child / name
                    if cand.is_dir():
                        return cand
                try:
                    grand = [c for c in child.iterdir() if c.is_dir()]
                except Exception:
                    grand = []
                for g in grand:
                    if g.name.lower() in LIC_NAMES:
                        return g
        return None

    @staticmethod
    def _chmod_recursive(path: Path, mode: int) -> int:
        count = 0
        try:
            os.chmod(path, mode)
            count += 1
        except Exception:
            pass
        try:
            for root, dirs, files in os.walk(path):
                for d in dirs:
                    try:
                        os.chmod(os.path.join(root, d), mode)
                        count += 1
                    except Exception:
                        pass
                for f in files:
                    try:
                        os.chmod(os.path.join(root, f), mode)
                        count += 1
                    except Exception:
                        pass
        except Exception:
            pass
        return count

    def _render(self, dimension_name: str, wait: bool = False) -> bool:
        if self._rendering and not wait:
            return False

        dim_id = self._dimension_ids.get(dimension_name, dimension_name)
        cli = self._get_unmined_cli_path()
        if not cli:
            self.logger.error(LOG_PREFIX + "§cunmined-cli 没找到喵，跳过渲染")
            return False

        if self._config.get("permissions", {}).get("chmodOnRender", True):
            self._fix_permissions(log=False)

        mr = self._config.get("mapRender", {})
        world_path = self._get_world_path()
        output_dir = self._web_root / dimension_name
        try:
            output_dir.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            self.logger.error(LOG_PREFIX + f"§c创建输出目录失败喵: {e}")
            return False

        cmd = [
            cli,
            "web", "render",
            f"--world={world_path}",
            f"--output={str(output_dir)}",
            f"--imageformat={mr.get('imageFormat', 'webp')}",
            "-c",
            f"--zoomin={mr.get('maxZoomLevel', -2)}",
            f"--zoomout={mr.get('minZoomLevel', 4)}",
            f"--dimension={dim_id}",
            "--players",
        ]

        if dimension_name == "nether":
            nether_cfg = mr.get("nether", {}) or {}
            if nether_cfg.get("mode", "slice") == "slice":
                cmd.append(f"--topY={nether_cfg.get('topY', 64)}")
                cmd.append(f"--bottomY={nether_cfg.get('bottomY', 0)}")
                if nether_cfg.get("gndxray", True):
                    cmd.append("--gndxray")

        self.logger.info(LOG_PREFIX + f"渲染命令喵: {' '.join(cmd)}")

        if wait:
            return self._do_render(cmd, dimension_name, output_dir)

        if not self._render_lock.acquire(blocking=False):
            return False
        self._rendering = True

        def run():
            try:
                self._do_render(cmd, dimension_name, output_dir)
            finally:
                self._rendering = False
                self._render_lock.release()

        threading.Thread(target=run, daemon=True).start()
        return True

    def _do_render(self, cmd: List[str], dimension_name: str, output_dir: Path) -> bool:
        try:
            self.logger.info(LOG_PREFIX + f"正在渲染 {dimension_name} 喵…")
            result = subprocess.run(cmd, capture_output=True, timeout=1800)
            if result.returncode == 0:
                self._post_process(dimension_name, output_dir)
                self.logger.info(LOG_PREFIX + f"§a{dimension_name} 维度渲染完成喵")
                return True
            stderr = result.stderr.decode(errors="ignore")
            stdout = result.stdout.decode(errors="ignore")
            self.logger.error(LOG_PREFIX + f"§c{dimension_name} 渲染失败喵（返回码 {result.returncode}）")
            self.logger.error(LOG_PREFIX + f"§c--- STDERR ---\n{stderr}")
            self.logger.error(LOG_PREFIX + f"§c--- STDOUT ---\n{stdout}")
            # 即便失败也把网页铺好，避免用户看到 404
            self._post_process(dimension_name, output_dir)
            return False
        except subprocess.TimeoutExpired:
            self.logger.error(LOG_PREFIX + f"§c{dimension_name} 渲染超时喵（1800 秒）!")
            return False
        except Exception as e:
            self.logger.error(LOG_PREFIX + f"§c{dimension_name} 渲染异常喵: {e}")
            return False

    def _render_many(self, dimensions: List[str]) -> None:
        """串行渲染多个维度；同一时刻只允许一个批量渲染在跑。"""
        if not self._render_lock.acquire(blocking=False):
            self.logger.warning(LOG_PREFIX + "§e已有渲染任务在进行中喵，跳过本次")
            return
        try:
            self._rendering = True
            for name in dimensions:
                if self._stopping:
                    return
                self._render(name, wait=True)
                time.sleep(2)
        finally:
            self._rendering = False
            self._render_lock.release()

    def _initial_render_all(self) -> None:
        dims = self._enabled_dimensions()
        if not dims:
            return
        if not self._get_unmined_cli_path():
            self.logger.warning(LOG_PREFIX + "§e未找到 unmined-cli，跳过首轮渲染喵（可在 config.json 的 paths.unminedCli 指定）")
            return
        self.logger.info(LOG_PREFIX + f"开始首轮渲染喵: {', '.join(dims)}")
        self._render_many(dims)
        self.logger.info(LOG_PREFIX + "首轮渲染结束喵")

    def _auto_render(self) -> None:
        dims = self._enabled_dimensions()
        if not dims:
            return
        threading.Thread(target=self._render_many, args=(dims,), daemon=True).start()

    # ------------------------------------------------------------------ #
    # 渲染后处理：覆盖 html / 写标记
    # ------------------------------------------------------------------ #

    def _post_process(self, dimension_name: str, output_dir: Path) -> None:
        self._apply_custom_html(dimension_name, output_dir)
        self._apply_markers(dimension_name, output_dir)
        # 立刻写一份玩家数据，避免刚打开地图时空白
        self._write_live_data()

    def _apply_custom_html(self, dimension_name: str, output_dir: Path) -> None:
        """用自定义模板覆盖 uNmINeD 生成的 html，并注入维度过滤器。"""
        tpl = self._read_asset("map.html")
        if not tpl:
            return

        refresh_sec = max(1, int(self._config.get("players", {}).get("refreshInterval", 5)))
        title = str(self._config.get("webserver", {}).get("mapTitle", "default"))
        map_title = "" if title in ("default", "", None) else title

        html_text = (
            tpl.replace("__MAP_DIMENSION__", self._js_string(dimension_name))
            .replace("__PLAYERS_JSON__", "players.json")
            .replace("__REFRESH_MS__", str(refresh_sec * 1000))
            .replace("__MAP_TITLE__", self._js_string(map_title))
        )

        written = 0
        for name in ("index.html", "unmined.index.html"):
            target = output_dir / name
            if target.exists():
                try:
                    target.write_text(html_text, encoding="utf-8")
                    written += 1
                except Exception as e:
                    self.logger.warning(LOG_PREFIX + f"覆盖 {name} 失败喵: {e}")
        if written:
            self.logger.info(LOG_PREFIX + f"§a已覆盖 {dimension_name} 的地图网页（维度过滤器 = {dimension_name}）喵")
        else:
            self.logger.warning(LOG_PREFIX + f"§e{dimension_name} 目录下没找到 index.html，跳过覆盖喵")

    def _apply_markers(self, dimension_name: str, output_dir: Path) -> None:
        marker_list = []
        for m in self._markers:
            text = str(m.get("text", "") or "")
            if not text:
                continue
            marker_list.append({
                "x": m.get("x", 0),
                "z": m.get("z", 0),
                "text": text,
                "image": "custom.pin.png",
                "imageAnchor": ["0.5", 1],
                "imageScale": "0.3",
                "textColor": "red",
                "offsetX": 0,
                "offsetY": 20,
                "font": "bold 20px Calibri,sans serif",
            })
        data = {"isEnabled": True, "markers": marker_list}
        try:
            output_dir.mkdir(parents=True, exist_ok=True)
            (output_dir / "custom.markers.js").write_text(
                "UnminedCustomMarkers = " + json.dumps(data, indent=4, ensure_ascii=False),
                encoding="utf-8",
            )
        except Exception as e:
            self.logger.warning(LOG_PREFIX + f"写入标记失败喵 ({dimension_name}): {e}")

    def _apply_all_html(self) -> int:
        """对所有已存在的维度目录重新铺一次网页（用于手动触发 / 配置变更）。"""
        if not self._web_root:
            return 0
        count = 0
        for dim in self._enabled_dimensions():
            out_dir = self._web_root / dim
            if out_dir.is_dir() and (out_dir / "index.html").exists():
                self._apply_custom_html(dim, out_dir)
                count += 1
        return count

    def _apply_markers_all(self) -> None:
        if not self._web_root:
            return
        for dim in self._enabled_dimensions():
            out_dir = self._web_root / dim
            if out_dir.exists():
                self._apply_markers(dim, out_dir)

    # ------------------------------------------------------------------ #
    # 玩家 / 聊天数据
    # ------------------------------------------------------------------ #

    @staticmethod
    def _normalize_dim(value: Any) -> str:
        return str(value or "overworld").lower().replace("minecraft:", "")

    def _sample_players(self) -> None:
        if not self._config.get("players", {}).get("enable", True):
            return
        snapshot: Dict[str, Dict[str, Any]] = {}
        try:
            online = self.server.online_players
        except Exception:
            return
        try:
            for player in online:
                try:
                    loc = player.location
                    dim = self._normalize_dim(getattr(getattr(loc, "dimension", None), "name", "overworld"))
                    snapshot[player.name] = {
                        "x": round(float(loc.x), 1),
                        "y": round(float(loc.y), 1),
                        "z": round(float(loc.z), 1),
                        "dim": dim,
                    }
                except Exception:
                    continue
        except Exception:
            return
        with self._lock:
            self._players = snapshot

    def _write_live_data(self) -> None:
        """把玩家/聊天写成静态 JSON：GreenMoon 托管和自建服务器都能读到。"""
        if not self._web_root:
            return
        if not self._config.get("players", {}).get("enable", True):
            return
        try:
            with self._lock:
                players_payload = json.dumps(self._players, ensure_ascii=False)
                chat_payload = json.dumps(self._chat_history, ensure_ascii=False)

            root = self._web_root
            root.mkdir(parents=True, exist_ok=True)
            (root / "players.json").write_text(players_payload, encoding="utf-8")
            (root / "chat.json").write_text(chat_payload, encoding="utf-8")
            # 各维度目录也放一份，前端用相对路径 ./players.json 取
            for dim in self._enabled_dimensions():
                dim_dir = root / dim
                if dim_dir.is_dir():
                    (dim_dir / "players.json").write_text(players_payload, encoding="utf-8")
        except Exception:
            pass

    # ------------------------------------------------------------------ #
    # 定时任务
    # ------------------------------------------------------------------ #

    def _start_schedulers(self) -> None:
        players_cfg = self._config.get("players", {})
        sample_ticks = max(1, int(players_cfg.get("sampleIntervalTicks", 20)))
        refresh_sec = max(1, int(players_cfg.get("refreshInterval", 5)))
        refresh_ticks = max(1, refresh_sec * 20)

        try:
            self.server.scheduler.run_task(self, self._sample_players, delay=0, period=sample_ticks)
            self.server.scheduler.run_task(self, self._write_live_data, delay=20, period=refresh_ticks)
        except Exception as e:
            self.logger.warning(LOG_PREFIX + f"注册定时任务失败喵: {e}")

        auto = self._config.get("autoRend", {})
        if auto.get("enable", True):
            cycle = max(1, int(auto.get("cycle", 30)))
            cycle_ticks = cycle * 60 * 20
            try:
                self.server.scheduler.run_task(self, self._auto_render, delay=cycle_ticks, period=cycle_ticks)
            except Exception as e:
                self.logger.warning(LOG_PREFIX + f"注册自动渲染失败喵: {e}")

    # ------------------------------------------------------------------ #
    # 自带 Web 服务器（无 GreenMoon 时使用）
    # ------------------------------------------------------------------ #

    def _start_web_server(self) -> None:
        if self._server:
            return
        ws = self._config.get("webserver", {})
        bind = ws.get("bindAddress", "0.0.0.0")
        port = int(ws.get("port", 5110))

        try:
            self._web_root.mkdir(parents=True, exist_ok=True)
        except Exception:
            pass

        plugin = self

        class MapHandler(SimpleHTTPRequestHandler):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, directory=str(plugin._web_root), **kwargs)

            def translate_path(self, path: str) -> str:
                clean = path.split("?", 1)[0].split("#", 1)[0]
                clean = clean.rstrip("/") or "/"

                # 兼容 /map/ 前缀（和 GreenMoon 托管时保持一致）
                if clean == "/map" or clean.startswith("/map/"):
                    clean = clean[len("/map"):] or "/"

                if clean.startswith("/api/"):
                    return super().translate_path(clean)

                # 维度：/overworld/... -> <root>/overworld/...
                for name in plugin._dimension_ids:
                    prefix = "/" + name
                    if clean == prefix or clean.startswith(prefix + "/"):
                        rel = clean[len(prefix):] or "/"
                        if rel == "/":
                            rel = "/index.html"
                        return str(plugin._web_root / name / rel.lstrip("/"))

                if clean == "/" or clean == "/index.html":
                    return str(plugin._web_root / "index.html")

                return super().translate_path(clean)

            def do_GET(self):
                try:
                    path = self.path.split("?", 1)[0]
                    if path.startswith("/api/players"):
                        with plugin._lock:
                            self._send_json(plugin._players)
                        return
                    if path.startswith("/api/chat"):
                        with plugin._lock:
                            self._send_json(plugin._chat_history)
                        return
                    if path.startswith("/api/markers"):
                        self._send_json(plugin._markers)
                        return
                    super().do_GET()
                except (ConnectionResetError, BrokenPipeError, ConnectionAbortedError):
                    pass
                except Exception as e:
                    plugin.logger.warning(LOG_PREFIX + f"处理请求出错喵: {e}")

            def _send_json(self, data):
                try:
                    content = json.dumps(data, ensure_ascii=False).encode("utf-8")
                    self.send_response(200)
                    self.send_header("Content-Type", "application/json; charset=utf-8")
                    self.send_header("Cache-Control", "no-store")
                    self.send_header("Access-Control-Allow-Origin", "*")
                    self.send_header("Content-Length", str(len(content)))
                    self.end_headers()
                    self.wfile.write(content)
                except (ConnectionResetError, BrokenPipeError, ConnectionAbortedError):
                    pass

            def log_message(self, fmt, *args):
                pass

        try:
            self._server = ThreadingHTTPServer((bind, port), MapHandler)
            self._server.daemon_threads = True
            self._server_thread = threading.Thread(target=self._server.serve_forever, daemon=True)
            self._server_thread.start()
            self.logger.info(LOG_PREFIX + f"§a自带 Web 服务器已启动喵: {bind}:{port}")
        except Exception as e:
            self.logger.error(LOG_PREFIX + f"§cWeb 服务器启动失败喵: {e}")
            self._server = None

    def _stop_web_server(self) -> None:
        if not self._server:
            return
        try:
            self._server.shutdown()
        except Exception:
            pass
        try:
            self._server.server_close()
        except Exception:
            pass
        self._server = None
        self._server_thread = None

    def _restart_web_server_if_needed(self) -> None:
        """面板/命令改了配置后：该开的开，该关的关，端口变了就重启。"""
        should_run = self._should_start_own_server()
        if not should_run:
            if self._server:
                self.logger.info(LOG_PREFIX + "检测到 GreenMoon 面板，关闭自带 Web 服务器喵")
                self._stop_web_server()
            return

        if not self._server:
            self._start_web_server()
            return

        current_port = self._server.server_address[1]
        want_port = int(self._config.get("webserver", {}).get("port", 5110))
        if current_port != want_port:
            self._stop_web_server()
            time.sleep(0.5)
            self._start_web_server()

    # ------------------------------------------------------------------ #
    # 标记持久化
    # ------------------------------------------------------------------ #

    def _load_markers(self) -> None:
        if self.markers_path.exists():
            try:
                with open(self.markers_path, encoding="utf-8") as f:
                    data = json.load(f)
                self._markers = data if isinstance(data, list) else []
                return
            except Exception as e:
                self.logger.warning(LOG_PREFIX + f"标记加载失败喵: {e}")
        self._markers = []
        self._save_markers()

    def _save_markers(self) -> None:
        try:
            self.data_dir.mkdir(parents=True, exist_ok=True)
            with open(self.markers_path, "w", encoding="utf-8") as f:
                json.dump(self._markers, f, indent=4, ensure_ascii=False)
        except Exception as e:
            self.logger.warning(LOG_PREFIX + f"标记保存失败喵: {e}")
