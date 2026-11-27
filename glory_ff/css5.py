# -*- coding: utf-8 -*-
import asyncio
import base64
import hashlib
import hmac
import itertools
import json
import math
import os
import random
import shutil
import socket
import ssl
import string
import struct
import sys
import time
import traceback
import uuid
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple

import aiohttp
import aiohttp.web
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from google_play_scraper import app as play_scraper
import httpx
from protobuf_decoder.protobuf_decoder import Parser

from message_ids import MESSAGE_ID_TO_NAME
import thunderFF_pb2

try:
    import reqClan_pb2
    CLAN_PB_AVAILABLE = True
except Exception:
    reqClan_pb2 = None
    CLAN_PB_AVAILABLE = False

if sys.platform == "win32":
    try:
        if hasattr(sys.stdout, "reconfigure"):
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

# ==================== CẤU HÌNH HỆ THỐNG ====================
WEB_HOST = "0.0.0.0"
WEB_PORT = 8086
ACCOUNTS_FILE = "accounts.json"
TOKEN_CACHE_FILE = "token_cache.json"
DEVICES_FILE = "devices.json"
INDEX_HTML_PATH = "temp/index.html"

# JWT của game thường có vòng đời ~8 giờ -> làm mới trước 30 phút để tránh đứt kết nối giữa chừng
JWT_DEFAULT_TTL_SEC = 8 * 3600
JWT_REFRESH_MARGIN_SEC = 30 * 60
TOKEN_CACHE_TTL_SEC = 86400 * 7
TOKEN_CACHE_MEMO_TTL_SEC = 5.0

START_MATCH_INTERVAL = 3.0
MAX_MATCH_DURATION = 1200
MATCH_IDLE_TIMEOUT = 120.0
NEW_MATCH_DELAY = 2.0  # Delay tối thiểu trước khi tìm trận mới sau khi kết thúc

NO_MATCH_RESTART_ENABLED = True
NO_MATCH_RESTART_TIMEOUT = 90.0
NO_MATCH_RESTART_GRACE = 60.0

AUTO_ACCEPT_FRIEND_REQUEST = True
TEAM_MODE = True
TEAM_SIZE = 4
TEAM_READY_DELAY = 5.0
TEAM_INVITE_WAIT = 2.5
DEFAULT_GAME_MODE_ID = 15   # Clash Squad / Tử chiến
DEFAULT_GAME_SUB_MODE_ID = 1
DEFAULT_GAME_MAP_ID = 1
CLAN_ID_DEFAULT = "3105683920"
BOT_NAME_PREFIX = "Senzu_"
DEV_UID = ""

MOVEMENT_TICK_MS = 100
MOVEMENT_SPEED_MIN = 0.96
MOVEMENT_SPEED_MAX = 1.02
MOVEMENT_UPDATE_SPEED_EVERY = 4.0

PLAYER_STATE_MAP = {
    "idle": 0, "walk": 1, "run": 1, "sprint": 1,
    "jump": 2, "crouch": 3, "prone": 4,
}
MOVE_STATE_MAP = {
    "idle": 0, "walk": 1, "run": 2, "sprint": 3,
    "jump": 4, "crouch": 1, "prone": 1,
}

AES_KEY = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
AES_IV = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])
KEYSTREAM = bytes([
    0x30, 0x30, 0x30, 0x32, 0x30, 0x31, 0x37, 0x30,
    0x30, 0x30, 0x30, 0x30, 0x32, 0x30, 0x31, 0x37,
    0x30, 0x30, 0x30, 0x30, 0x30, 0x32, 0x30, 0x31,
    0x37, 0x30, 0x30, 0x30, 0x30, 0x30, 0x32, 0x30,
])
HEX_KEY = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"
API_KEY = HEX_KEY.encode()
REGION_LANG = {
    "ME": "ar", "IND": "hi", "ID": "id", "VN": "vi", "TH": "th",
    "BD": "bn", "PK": "ur", "TW": "zh", "RU": "ru", "SAC": "es",
    "BR": "pt", "NA": "pt", "SG": "pt", "US": "pt",
}

GGRE_RAW = bytes.fromhex(
    "47475245010101006d020000b260ee08e1f86b4c57f9c70f86bba26ed5d1436bcf52e142db3249d905eded757764991ca31a8373cdd26eab91b80f3f1f6f262f4f10b895d7b6937ddba30a27197453890e9da49373f736c679b8254e2f8e1623e91084a5fdd5374fe478ff99e010834553fddeb0bec4018d142e49df9bb236675b67e852f92a43586f7a7d4d0d7a197a1d4da32714dab4d069ad53214e2c33b3877420a12459738c4c619cbd815fa878bbd104776bb3e1ac7818d5397b04a666ac57f682763ff2df31bc2f846ddc7904f3dce1bda0c4b01f9698e9166f98c84f92640abe3f6317834a42e5c12573b46842c1a6ea8fe6ca9c006dca48a2087e1f983dfb5692771e4a0b15b337ad669b1d08b40862b176bace5331b49a767375b1a8469012aa70a67b55fe71b72478201d0b3ac7269c064c960361e92ee7ba8a42cc6b582bf9b965fb388fa9172ad44c4b073ac23c02080a6bcd106b691ffdf4c7cf71e42f2063fcf196e9bddc5e85be1fe5048eb1b31b460efbb46d76195eef9904c4cba326f2e17ff51fec17dd965aa06dadd4ab07d6966e4a7c38e8afd66dfde56c872bb87516a8f7313c797e4d80e5ad4a5f7afad95c1e0449254adae052e71a3fb98399f93ab30848e0d23252dd45e6fd41bc5fa7303dfb846a8fd713a0032a0b0ae96dfba1bbe41d20abd8099e2cb7fccc329d25bd153029139ef05d090a5093ea557693c0a8d491395b8a23ca844b3887dd5dfc29ac06f4b9be87883a793211b973465e2644c4f5de02b8ab01571401203fc2740423826858cc6da0194c195d27aac4ec4b9d23d506c1501d06440aca3fc180926d75d4a004d3dff21eb4ea1e8c86e6c9627248eff953e1d192d5c8efc006a7e512388ef2ebdb72ee3ad42d719f28e8f994e12ebf4c79f2ffe3abd7408ccd2236a7b89b2606247a732c10c4"
)

# ==================== MÀU SẮC & LOGGING ====================
class PX:
    RESET = "\033[0m"
    BOLD = "\033[1m"
    DIM = "\033[2m"
    GOLD = "\033[38;5;220m"
    AMBER = "\033[38;5;214m"
    ROSE = "\033[38;5;204m"
    MAGENTA = "\033[38;5;200m"
    VIOLET = "\033[38;5;135m"
    CYAN = "\033[38;5;51m"
    TEAL = "\033[38;5;44m"
    MINT = "\033[38;5;121m"
    LIME = "\033[38;5;118m"
    EMERALD = "\033[38;5;48m"
    SKY = "\033[38;5;117m"
    SLATE = "\033[38;5;245m"
    SILVER = "\033[38;5;250m"
    WHITE = "\033[38;5;255m"
    CRIMSON = "\033[38;5;197m"


ICONS = {
    "ok": "◈", "err": "◇", "warn": "◉", "info": "◎",
    "star": "✦", "spark": "✧", "dot": "•", "arrow": "▸",
    "check": "✔", "bolt": "⚡", "flame": "🔥", "gem": "💎",
    "crown": "👑", "rocket": "🚀", "target": "🎯",
}


def current_ts() -> str:
    return datetime.now().strftime("%H:%M:%S")


def format_log(msg: str, color: str, icon: str, tag: str) -> str:
    return (
        f"{PX.SLATE}{current_ts()}{PX.RESET} "
        f"{color}{PX.BOLD}╭─{icon}─╮ {tag:<5}{PX.RESET} "
        f"{PX.DIM}{PX.SLATE}▸{PX.RESET} {PX.SILVER}{msg}{PX.RESET}"
    )


def log_ok(msg: str) -> None:
    print(format_log(msg, PX.EMERALD, ICONS["ok"], "OK"), flush=True)
    try:
        bot_state.append_log(msg, "success")
    except Exception:
        pass


def log_err(msg: str) -> None:
    print(format_log(msg, PX.CRIMSON, ICONS["err"], "ERR"), flush=True)
    try:
        bot_state.append_log(msg, "error")
    except Exception:
        pass


def log_warn(msg: str) -> None:
    print(format_log(msg, PX.AMBER, ICONS["warn"], "WARN"), flush=True)
    try:
        bot_state.append_log(msg, "warning")
    except Exception:
        pass


def log_info(msg: str) -> None:
    print(format_log(msg, PX.CYAN, ICONS["info"], "INFO"), flush=True)
    try:
        bot_state.append_log(msg, "info")
    except Exception:
        pass


def log_event(msg: str, color: str = PX.GOLD, icon: str = ICONS["star"], tag: str = "EVENT") -> None:
    print(format_log(msg, color, icon, tag), flush=True)
    try:
        bot_state.append_log(msg, "info")
    except Exception:
        pass


def print_rule(title: str = "", width: int = 72, color: str = PX.VIOLET) -> None:
    if not title:
        print(f"{color}{'═' * width}{PX.RESET}")
        return
    pad = max(0, width - len(title) - 6)
    left = pad // 2
    right = pad - left
    print(f"{color}{'═' * left}❰ {PX.BOLD}{title}{PX.RESET}{color} ❱{'═' * right}{PX.RESET}")


def print_menu_banner() -> None:
    print(f"\n{PX.CYAN}{PX.BOLD}Glory Free Fire Bot{PX.RESET}\n")


# ==================== TRẠNG THÁI TOÀN CỤC ====================
class BotState:
    def __init__(self) -> None:
        self.accounts: Dict[str, dict] = {}
        self.account_credentials: Dict[str, dict] = {}
        self.account_workers: Dict[str, asyncio.Task] = {}
        self.auth_to_game_id: Dict[str, str] = {}
        self.game_to_auth_id: Dict[str, str] = {}
        self.paused: set = set()
        self.writers: Dict[str, list] = {}
        self.logs: List[dict] = []
        self.total_matches = 0
        self.matches_started = 0
        self.total_exp_gained = 0
        self.create_progress: List[str] = []
        self.creating = False
        self.expected_workers = 0
        self.start_time = time.time()

    def append_log(self, msg: str, level: str = "info") -> None:
        try:
            self.logs.append({
                "t": time.time(),
                "time": current_ts(),
                "message": str(msg),
                "level": level,
            })
            if len(self.logs) > 500:
                self.logs = self.logs[-500:]
        except Exception:
            pass

    def register_account(
        self, uid: Any, nickname: str, region: str = "VN", level: int = 1,
        exp: int = 0, likes: int = 0, token: Optional[str] = None, auth_uid: Optional[str] = None,
    ) -> None:
        uid_s = str(uid)
        existing = self.accounts.get(uid_s, {})
        self.accounts[uid_s] = {
            "uid": uid_s,
            "nickname": nickname,
            "region": region,
            "level": level,
            "exp": exp,
            "likes": likes,
            "token": token,
            "auth_uid": auth_uid,
            "status": "ONLINE",
            "current_exp": exp,
            "initial_exp": existing.get("initial_exp", exp),
            "gained_exp": existing.get("gained_exp", 0),
            "matches": existing.get("matches", 0),
            "active_matches": 0,
            "uptime_seconds": existing.get("uptime_seconds", 0),
            "last_match_time": existing.get("last_match_time", "Running..."),
            "is_paused": False,
        }

    def update_status(self, uid: Any, status: str, matches: int = 0) -> None:
        uid_s = str(uid)
        if uid_s in self.accounts:
            self.accounts[uid_s]["status"] = status
            self.accounts[uid_s]["active_matches"] = matches
            self.accounts[uid_s]["is_paused"] = (status == "PAUSED")

    def update_exp(self, uid: Any, exp: int, level: Optional[int] = None) -> None:
        uid_s = str(uid)
        if uid_s in self.accounts:
            acc = self.accounts[uid_s]
            old_exp = acc.get("current_exp", 0)
            if exp > old_exp:
                diff = exp - old_exp
                acc["gained_exp"] = acc.get("gained_exp", 0) + diff
                self.total_exp_gained += diff
            acc["current_exp"] = exp
            acc["exp"] = exp
            if level:
                acc["level"] = level

    def increment_match(self, uid: Any) -> None:
        self.total_matches += 1
        uid_s = str(uid)
        if uid_s in self.accounts:
            self.accounts[uid_s]["matches"] = self.accounts[uid_s].get("matches", 0) + 1
            self.accounts[uid_s]["last_match_time"] = current_ts()

    def increment_match_started(self) -> None:
        self.matches_started += 1

    def register_writer(self, uid: Any, writer: asyncio.StreamWriter) -> None:
        self.writers.setdefault(str(uid), []).append(writer)

    def unregister_writer(self, uid: Any, writer: asyncio.StreamWriter) -> None:
        try:
            self.writers.get(str(uid), []).remove(writer)
        except Exception:
            pass

    def close_writers_for_account(self, uid: Any) -> None:
        for w in list(self.writers.get(str(uid), [])):
            try:
                w.close()
            except Exception:
                pass
        self.writers[str(uid)] = []

    def is_paused(self, uid: Any) -> bool:
        return str(uid) in self.paused

    def toggle_pause(self, uid: Any, paused: bool) -> None:
        uid_s = str(uid)
        if paused:
            self.paused.add(uid_s)
            if uid_s in self.accounts:
                self.accounts[uid_s]["is_paused"] = True
                self.accounts[uid_s]["status"] = "PAUSED"
        else:
            self.paused.discard(uid_s)
            if uid_s in self.accounts:
                self.accounts[uid_s]["is_paused"] = False
                if self.accounts[uid_s].get("status") == "PAUSED":
                    self.accounts[uid_s]["status"] = "ONLINE"


bot_state = BotState()

_team_state: Dict[str, Any] = {
    "peers": {},
    "leader_uid": None,
    "team_code": None,
    "team_codes": {},
    "squads": [],
    "locked_squads": [],
    "uid_to_leader": {},
    "uid_to_squad_idx": {},
    "partition_sig": None,
    "in_queue": False,
    "lock": asyncio.Lock(),
}
_restricted_57_uids: set = {"18951141012", "18951142384"}
_restart_state: Dict[str, Any] = {
    "lock": asyncio.Lock(),
    "finished_bots": set(),
    "target": None,
    "restarting": False,
}
_no_match_state: Dict[str, Any] = {
    "lock": asyncio.Lock(),
    "global_last_match": None,
    "restart_triggered": False,
}
_team_stuck_state: Dict[str, Any] = {
    "lock": asyncio.Lock(),
    "in_team_since": {},
    "triggered": False,
}
_ALLOWED_RESTART_STATUSES = {"ONLINE", "SEARCHING"}


def _split_squad_sizes(n: int) -> List[int]:
    if n <= 0:
        return []
    if n <= 4:
        return [n]
    rem = n % 4
    if rem == 0:
        return [4] * (n // 4)
    if rem in (2, 3):
        return [4] * (n // 4) + [rem]
    return [4] * (n // 4 - 1) + [3, 2]


def _compute_smart_squads(peers_dict: dict) -> List[List[str]]:
    def _sort_key(u: str) -> int:
        return int(u) if u.isdigit() else 999999999999

    all_uids = sorted((str(k) for k in peers_dict.keys()), key=_sort_key)
    healthy = [u for u in all_uids if u not in _restricted_57_uids]
    restricted = [u for u in all_uids if u in _restricted_57_uids]

    ordered = (
        (healthy + restricted)
        if not (len(healthy) >= 2 and len(restricted) >= 2)
        else None
    )
    squads: List[List[str]] = []
    if ordered is not None:
        idx = 0
        for sz in _split_squad_sizes(len(ordered)):
            squads.append(ordered[idx:idx + sz])
            idx += sz
    else:
        for group in (healthy, restricted):
            idx = 0
            for sz in _split_squad_sizes(len(group)):
                squads.append(group[idx:idx + sz])
                idx += sz
    return [s for s in squads if s]


async def _mark_match_found(account_id: Any = None) -> None:
    async with _no_match_state["lock"]:
        _no_match_state["global_last_match"] = time.time()


async def _mark_team_joined(uid: Any) -> None:
    uid_s = str(uid)
    async with _team_stuck_state["lock"]:
        if uid_s not in _team_stuck_state["in_team_since"]:
            _team_stuck_state["in_team_since"][uid_s] = time.time()
            log_info(f"[TEAM-STUCK] {uid_s} JOINED")


async def _clear_team_joined(uid: Any) -> None:
    uid_s = str(uid)
    async with _team_stuck_state["lock"]:
        _team_stuck_state["in_team_since"].pop(uid_s, None)


def _all_bots_are_online_or_searching() -> bool:
    active = [
        str(acc.get("status", "")).upper().strip()
        for acc in bot_state.accounts.values()
        if str(acc.get("status", "")).upper().strip() not in ("", "OFFLINE")
    ]
    return bool(active) and all(st in _ALLOWED_RESTART_STATUSES for st in active)


def _any_bot_in_match() -> bool:
    return any(
        "IN_MATCH" in str(acc.get("status", "")).upper()
        for acc in bot_state.accounts.values()
    )


async def _schedule_restart() -> None:
    await asyncio.sleep(10.0)
    log_warn("[RESTART] Đang reset toàn bộ phiên để tìm trận mới...")
    async with _restart_state["lock"]:
        _restart_state["finished_bots"].clear()
        _restart_state["target"] = None
        _restart_state["restarting"] = False
    async with _team_state["lock"]:
        _team_state["peers"].clear()
        _team_state["leader_uid"] = None
        _team_state["team_code"] = None
        _team_state["team_codes"].clear()
        _team_state["squads"].clear()
        _team_state["uid_to_leader"].clear()
        _team_state["uid_to_squad_idx"].clear()
        _team_state["partition_sig"] = None
    async with _no_match_state["lock"]:
        _no_match_state["global_last_match"] = time.time()
        _no_match_state["restart_triggered"] = False
    async with _team_stuck_state["lock"]:
        _team_stuck_state["in_team_since"].clear()
        _team_stuck_state["triggered"] = False


async def _no_match_watchdog() -> None:
    if not NO_MATCH_RESTART_ENABLED:
        return
    await asyncio.sleep(NO_MATCH_RESTART_GRACE)
    async with _no_match_state["lock"]:
        if _no_match_state["global_last_match"] is None:
            _no_match_state["global_last_match"] = time.time()
    log_info(f"[NO-MATCH] Watchdog hoạt động timeout={NO_MATCH_RESTART_TIMEOUT:.0f}s")

    while True:
        await asyncio.sleep(10.0)
        try:
            if _restart_state["restarting"] or _no_match_state["restart_triggered"]:
                return
            if _any_bot_in_match():
                now = time.time()
                async with _no_match_state["lock"]:
                    _no_match_state["global_last_match"] = now
                async with _team_stuck_state["lock"]:
                    for u in list(_team_stuck_state["in_team_since"].keys()):
                        _team_stuck_state["in_team_since"][u] = now
                continue

            now = time.time()
            async with _team_state["lock"]:
                team_size = len(_team_state["peers"])
                peer_keys = set(_team_state["peers"].keys())

            stuck_uids = []
            async with _team_stuck_state["lock"]:
                for u, since in list(_team_stuck_state["in_team_since"].items()):
                    if u not in peer_keys:
                        del _team_stuck_state["in_team_since"][u]
                        continue
                    if now - since >= NO_MATCH_RESTART_TIMEOUT:
                        stuck_uids.append((u, now - since))

            if stuck_uids and team_size >= TEAM_SIZE:
                async with _team_stuck_state["lock"]:
                    if not _team_stuck_state["triggered"]:
                        _team_stuck_state["triggered"] = True
                        log_warn(f"[TEAM-STUCK] {len(stuck_uids)} bot kẹt phòng ≥{NO_MATCH_RESTART_TIMEOUT:.0f}s")
                        async with _restart_state["lock"]:
                            _restart_state["restarting"] = True
                        await _schedule_restart()
                        return

            if not _all_bots_are_online_or_searching():
                async with _no_match_state["lock"]:
                    _no_match_state["global_last_match"] = time.time()
                continue

            async with _no_match_state["lock"]:
                last = _no_match_state["global_last_match"] or now
            elapsed = now - last
            if elapsed >= NO_MATCH_RESTART_TIMEOUT and _all_bots_are_online_or_searching():
                async with _no_match_state["lock"]:
                    if not _no_match_state["restart_triggered"]:
                        _no_match_state["restart_triggered"] = True
                        log_warn(f"[NO-MATCH] Không có trận sau {elapsed:.0f}s → restart!")
                        async with _restart_state["lock"]:
                            _restart_state["restarting"] = True
                        await _schedule_restart()
                        return
        except Exception as exc:
            log_warn(f"[NO-MATCH] Lỗi: {exc}")


# ==================== THIẾT BỊ, MẠNG & PROTOBUF ====================
def _generate_new_device() -> dict:
    presets = [
        ("Samsung", "SM-G998B", "Adreno (TM) 660", "Android OS 12 / API-31"),
        ("Xiaomi", "2201122G", "Adreno (TM) 730", "Android OS 13 / API-33"),
        ("Realme", "RMX3700", "Mali-G710", "Android OS 14 / API-34"),
        ("OnePlus", "CPH2451", "Adreno (TM) 740", "Android OS 13 / API-33"),
        ("OPPO", "CPH2611", "Adreno (TM) 720", "Android OS 14 / API-34"),
    ]
    brand, model, gpu, os_ver = random.choice(presets)
    return {
        "unique_device_id": f"Google|{uuid.uuid4()}",
        "brand": brand,
        "model": model,
        "gpu_renderer": gpu,
        "system_software": os_ver,
        "screen_width": random.choice([720, 1080, 1440]),
        "screen_height": random.choice([1600, 2400, 3200]),
        "screen_dpi": str(random.randint(300, 420)),
        "memory": random.randint(2800, 6500),
    }


def atomic_write_json(path: str, data: Any, default_fn=None) -> None:
    tmp_path = f"{path}.tmp"
    try:
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, default=default_fn, ensure_ascii=False)
        os.replace(tmp_path, path)
    except Exception as exc:
        log_err(f"Ghi file {path} thất bại: {exc}")
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass


def get_device_for_account(acc_key: str) -> dict:
    devices: Dict[str, dict] = {}
    if os.path.exists(DEVICES_FILE):
        try:
            with open(DEVICES_FILE, "r", encoding="utf-8") as f:
                loaded = json.load(f)
                if isinstance(loaded, dict):
                    devices = loaded
        except Exception:
            devices = {}
    if acc_key in devices:
        return devices[acc_key]
    dev = _generate_new_device()
    devices[acc_key] = dev
    atomic_write_json(DEVICES_FILE, devices)
    return dev


_DNS_CACHE: Dict[str, Tuple[str, float]] = {}


async def resolve_host(hostname: str) -> str:
    if not hostname:
        return hostname
    parts = hostname.split(".")
    if len(parts) == 4 and all(p.isdigit() for p in parts):
        return hostname
    now = time.time()
    cached = _DNS_CACHE.get(hostname)
    if cached and now < cached[1]:
        return cached[0]
    try:
        loop = asyncio.get_running_loop()
        info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
        if info:
            ip = info[0][4][0]
            _DNS_CACHE[hostname] = (ip, now + 300.0)
            return ip
    except Exception:
        pass
    return hostname


def optimize_tcp_socket(sock: socket.socket) -> None:
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception:
        pass


def optimize_udp_socket(sock: socket.socket) -> None:
    try:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception:
        pass


async def safe_close_writer(writer: Optional[asyncio.StreamWriter]) -> None:
    if not writer:
        return
    try:
        if not writer.is_closing():
            writer.close()
        await asyncio.wait_for(writer.wait_closed(), timeout=1.5)
    except Exception:
        pass


http_client = httpx.AsyncClient(
    verify=False,
    timeout=15.0,
    limits=httpx.Limits(max_connections=300, max_keepalive_connections=150),
)
_LOGIN_SEMAPHORE = asyncio.Semaphore(4)


def get_team_packet_prefix(region: Optional[str] = "ID") -> str:
    reg = str(region or "ID").upper()
    if reg == "VN":
        return "0501"
    if reg == "BD":
        return "0519"
    if reg == "IND":
        return "0514"
    return "0515"


def _get_region_idc(region: str) -> str:
    reg = str(region or "ID").upper()
    return "IDC1" if reg == "VN" else "IDC3"


def get_tcp_packet_prefix(region: Optional[str], typ: str) -> str:
    reg = str(region or "ID").upper()
    base = "72" if typ == "OnLine" else "81"
    if reg == "BD":
        return f"{base}19"
    if reg == "IND":
        return f"{base}14"
    return f"{base}15"


def extract_field_value(container: Any, key: Any, default: Any = None) -> Any:
    if not isinstance(container, dict):
        return default
    if key in container:
        val = container[key]
    elif str(key) in container:
        val = container[str(key)]
    else:
        return default
    if isinstance(val, dict) and "data" in val:
        return val["data"]
    return val if val is not None else default


# ==================== MÃ HÓA & PROTOBUF ====================
CRC7_TABLE = bytes([
    0, 9, 18, 27, 36, 45, 54, 63, 72, 65, 90, 83, 108, 101, 126, 119,
    25, 16, 11, 2, 61, 52, 47, 38, 81, 88, 67, 74, 117, 124, 103, 110,
    50, 59, 32, 41, 22, 31, 4, 13, 122, 115, 104, 97, 94, 87, 76, 69,
    43, 34, 57, 48, 15, 6, 29, 20, 99, 106, 113, 120, 71, 78, 85, 92,
    100, 109, 118, 127, 64, 73, 82, 91, 44, 37, 62, 55, 8, 1, 26, 19,
    125, 116, 111, 102, 89, 80, 75, 66, 53, 60, 39, 46, 17, 24, 3, 10,
    86, 95, 68, 77, 114, 123, 96, 105, 30, 23, 12, 5, 58, 51, 40, 33,
    79, 70, 93, 84, 107, 98, 121, 112, 7, 14, 21, 28, 35, 42, 49, 56,
    65, 72, 83, 90, 101, 108, 119, 126, 9, 0, 27, 18, 45, 36, 63, 54,
    88, 81, 74, 67, 124, 117, 110, 103, 16, 25, 2, 11, 52, 61, 38, 47,
    115, 122, 97, 104, 87, 94, 69, 76, 59, 50, 41, 32, 31, 22, 13, 4,
    106, 99, 120, 113, 78, 71, 92, 85, 34, 43, 48, 57, 6, 15, 20, 29,
    37, 44, 55, 62, 1, 8, 19, 26, 109, 100, 127, 118, 73, 64, 91, 82,
    60, 53, 46, 39, 24, 17, 10, 3, 116, 125, 102, 111, 80, 89, 66, 75,
    23, 30, 5, 12, 51, 58, 33, 40, 95, 86, 77, 68, 123, 114, 105, 96,
    14, 7, 28, 21, 42, 35, 56, 49, 70, 79, 84, 93, 98, 107, 112, 121,
])
_DELTA = 0x9E3779B9
_ROUNDS = 16
_FIELD_SIZES = {0: 1, 1: 2, 2: 2, 3: 1, 4: 2}
_FIELD_NAMES = {0: "sendOption", 1: "cmd", 2: "orderId", 3: "flags", 4: "length"}


def crc7_sync(data: bytes) -> int:
    c = 0
    for b in data:
        c = CRC7_TABLE[((2 * (c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F


def encode_varint(n: int) -> bytes:
    out = bytearray()
    if n < 0:
        n &= 0xFFFFFFFFFFFFFFFF
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            break
    return bytes(out)


def _pb_varint(fn: int, val: int) -> bytes:
    return encode_varint((fn << 3) | 0) + encode_varint(val)


def _pb_length(fn: int, val: Any) -> bytes:
    enc = val.encode("utf-8") if isinstance(val, str) else bytes(val)
    return encode_varint((fn << 3) | 2) + encode_varint(len(enc)) + enc


def create_proto(fields: dict) -> bytes:
    packet = bytearray()
    for field, value in fields.items():
        fn = int(field) if isinstance(field, str) else field
        items = value if isinstance(value, list) else [value]
        for item in items:
            if isinstance(item, dict):
                packet.extend(_pb_length(fn, create_proto(item)))
            elif isinstance(item, bool):
                packet.extend(_pb_varint(fn, 1 if item else 0))
            elif isinstance(item, int):
                packet.extend(_pb_varint(fn, item))
            elif isinstance(item, (str, bytes, bytearray)):
                packet.extend(_pb_length(fn, item))
    return bytes(packet)


def encrypt_aes(hex_data: str) -> str:
    cipher = AES.new(AES_KEY, AES.MODE_CBC, AES_IV)
    return cipher.encrypt(pad(bytes.fromhex(hex_data), AES.block_size)).hex()


async def aes_encrypt(payload: bytes, key: bytes, iv: bytes) -> bytes:
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(payload, AES.block_size))


def decode_varint(data: bytes, offset: int) -> Tuple[Optional[int], int]:
    result = 0
    shift = 0
    while offset < len(data):
        byte = data[offset]
        result |= (byte & 0x7F) << shift
        offset += 1
        if not (byte & 0x80):
            return result, offset
        shift += 7
    return None, offset


def decode_protobuf_2(data: bytes) -> dict:
    result: dict = {}
    offset = 0
    data_len = len(data)
    while offset < data_len:
        header, offset = decode_varint(data, offset)
        if header is None:
            break
        fn, wt = header >> 3, header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None:
                result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None or offset + length > data_len:
                break
            value = data[offset:offset + length]
            offset += length
            try:
                s = value.decode("utf-8")
                result[fn] = s if s else value.hex()
            except UnicodeDecodeError:
                nested = decode_protobuf_2(value)
                result[fn] = nested if nested else value.hex()
        elif wt == 1:
            offset += 8
        elif wt == 3:
            offset += 4
        else:
            break
    return result


def extract_raw_fields(data: bytes) -> dict:
    result: dict = {}
    offset = 0
    data_len = len(data)
    while offset < data_len:
        header, offset = decode_varint(data, offset)
        if header is None:
            break
        fn, wt = header >> 3, header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None:
                result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None or offset + length > data_len:
                break
            result[fn] = bytes(data[offset:offset + length])
            offset += length
        elif wt == 1:
            offset += 8
        elif wt == 3:
            offset += 4
        else:
            break
    return result


def _parse_results_sync(results: Any) -> dict:
    out: dict = {}
    for r in results:
        fd: dict = {"wire_type": r.wire_type}
        if r.wire_type in ("varint", "string", "bytes"):
            fd["data"] = r.data
        elif r.wire_type == "length_delimited":
            if hasattr(r.data, "results"):
                fd["data"] = _parse_results_sync(r.data.results)
            elif isinstance(r.data, list):
                fd["data"] = _parse_results_sync(r.data)
            else:
                fd["data"] = str(r.data)
        out[str(r.field)] = fd
    return out


def decode_protobuf_dict(data: bytes) -> dict:
    try:
        hex_str = data.hex() if isinstance(data, (bytes, bytearray)) else data
        return _parse_results_sync(Parser().parse(hex_str))
    except Exception:
        return {}


async def decode_protobuf_async(data: Any) -> str:
    try:
        # Parser().parse() nhận HEX STRING, không phải bytes
        hex_str = data if isinstance(data, str) else data.hex()
        return json.dumps(_parse_results_sync(Parser().parse(hex_str)))
    except Exception:
        return "{}"


def uleb_encode_sync(n: int) -> bytes:
    try:
        n = int(n)
    except Exception:
        n = 0
    if n < 0:
        n &= 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            break
    return bytes(out)


async def uleb_encode(n: int) -> bytes:
    try:
        n = int(n)
    except Exception:
        n = 0
    if n < 0:
        n &= 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            break
    return bytes(out)


async def zigzag_encode_signed(n: int) -> bytes:
    try:
        n = int(n)
    except Exception:
        n = 0
    zz = (n << 1) ^ (n >> 63)
    if zz < 0:
        zz = -zz
    zz &= 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while True:
        b = zz & 0x7F
        zz >>= 7
        if zz:
            b |= 0x80
        out.append(b)
        if not zz:
            break
    return bytes(out)


def create_packet(pk_hex: str, prefix: str, key: Any, iv: Any) -> bytes:
    if isinstance(key, str):
        key = bytes.fromhex(key) if len(key) == 32 else key.encode()
    if isinstance(iv, str):
        iv = bytes.fromhex(iv) if len(iv) == 32 else iv.encode()
    enc_hex = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(bytes.fromhex(pk_hex), 16)).hex()
    length = len(enc_hex) // 2
    hex_len = hex(length)[2:]
    if len(hex_len) % 2 != 0:
        hex_len = "0" + hex_len
    pad_len = max(0, 12 - len(prefix) - len(hex_len))
    return bytes.fromhex(prefix + ("0" * pad_len) + hex_len + enc_hex)


def extract_key_iv(res_json: dict) -> Tuple[Optional[bytes], Optional[bytes]]:
    if "__RAW_HEX__" in res_json and "__OFFSET__" in res_json:
        try:
            raw = bytes.fromhex(res_json["__RAW_HEX__"])
            off = int(res_json["__OFFSET__"])
            rf = extract_raw_fields(raw[off:])
            for kf, vf in ((22, 23), (24, 25), (6, 7)):
                k, v = rf.get(kf), rf.get(vf)
                if isinstance(k, (bytes, bytearray)) and len(k) == 16 and isinstance(v, (bytes, bytearray)) and len(v) == 16:
                    return bytes(k), bytes(v)
        except Exception:
            pass

    found: Dict[int, bytes] = {}
    for k, v in res_json.items():
        if str(k).startswith("__") or not isinstance(v, dict):
            continue
        data = v.get("data")
        raw: Optional[bytes] = None
        if isinstance(data, (bytes, bytearray)) and len(data) == 16:
            raw = bytes(data)
        elif isinstance(data, str) and len(data) == 32:
            try:
                cand = bytes.fromhex(data)
                if len(cand) == 16:
                    raw = cand
            except Exception:
                pass
        if raw:
            try:
                found[int(k)] = raw
            except Exception:
                pass

    if len(found) < 2:
        return None, None
    for kf, vf in ((22, 23), (24, 25), (6, 7)):
        if kf in found and vf in found:
            return found[kf], found[vf]
    sk = sorted(found.keys())
    return found[sk[0]], found[sk[1]]


# ==================== QUẢN LÝ JWT TOKEN (CHU KỲ 8H) ====================
def parse_jwt_expiry(jwt_token: Optional[str]) -> Optional[float]:
    """Đọc trường exp (epoch giây) từ payload của JWT nếu hợp lệ."""
    if not jwt_token or not isinstance(jwt_token, str):
        return None
    parts = jwt_token.split(".")
    if len(parts) < 2:
        return None
    try:
        payload_b64 = parts[1] + ("=" * (-len(parts[1]) % 4))
        payload = json.loads(base64.urlsafe_b64decode(payload_b64))
        exp_val = payload.get("exp")
        if exp_val is not None:
            return float(exp_val)
    except Exception:
        pass
    return None


def compute_jwt_expires_at(jwt_token: Optional[str], issued_at: Optional[float] = None) -> float:
    """Ưu tiên exp trong JWT; nếu không có thì tính theo chu kỳ mặc định 8 giờ."""
    jwt_exp = parse_jwt_expiry(jwt_token)
    if jwt_exp and jwt_exp > time.time():
        return jwt_exp
    base_t = issued_at if issued_at else time.time()
    return float(base_t) + JWT_DEFAULT_TTL_SEC


def is_jwt_expiring_soon(account_data: Optional[dict], margin_sec: float = JWT_REFRESH_MARGIN_SEC) -> bool:
    """Kiểm tra JWT sắp hết hạn hoặc đã hết hạn."""
    if not isinstance(account_data, dict):
        return True
    token = account_data.get("token")
    if not token:
        return True
    exp_at = account_data.get("jwt_expires_at")
    if exp_at is None:
        issued_at = account_data.get("jwt_issued_at") or account_data.get("cached_at") or time.time()
        exp_at = compute_jwt_expires_at(token, issued_at)
    return time.time() >= (float(exp_at) - margin_sec)


class TokenManager:
    """Quản lý vòng đời JWT token cho toàn bộ bot (đặc biệt tối ưu khi chạy 4 bot)."""

    def __init__(self) -> None:
        self._memo: Dict[str, Any] = {}
        self._memo_time: float = 0.0
        self._refresh_locks: Dict[str, asyncio.Lock] = {}

    def _get_lock(self, key: str) -> asyncio.Lock:
        lock = self._refresh_locks.get(key)
        if lock is None:
            lock = asyncio.Lock()
            self._refresh_locks[key] = lock
        return lock

    @staticmethod
    def _serialize(obj: Any) -> Any:
        if isinstance(obj, (bytes, bytearray)):
            return {"__bytes_hex__": bytes(obj).hex()}
        raise TypeError(f"Không thể serialize kiểu {type(obj)}")

    @classmethod
    def _deserialize(cls, obj: Any) -> Any:
        if isinstance(obj, dict):
            if "__bytes_hex__" in obj and len(obj) == 1:
                try:
                    return bytes.fromhex(obj["__bytes_hex__"])
                except Exception:
                    return b""
            return {k: cls._deserialize(v) for k, v in obj.items()}
        if isinstance(obj, list):
            return [cls._deserialize(x) for x in obj]
        return obj

    def _load_cache(self) -> Dict[str, Any]:
        now = time.time()
        if self._memo and (now - self._memo_time) < TOKEN_CACHE_MEMO_TTL_SEC:
            return self._memo
        if not os.path.exists(TOKEN_CACHE_FILE):
            return {}
        try:
            with open(TOKEN_CACHE_FILE, "r", encoding="utf-8") as f:
                raw_text = f.read().strip()
            if not raw_text:
                return {}
            parsed = self._deserialize(json.loads(raw_text))
            if not isinstance(parsed, dict):
                return {}
            self._memo = parsed
            self._memo_time = now
            return parsed
        except Exception:
            try:
                os.remove(TOKEN_CACHE_FILE)
            except Exception:
                pass
            return {}

    def _save_cache(self, cache: Dict[str, Any]) -> None:
        atomic_write_json(TOKEN_CACHE_FILE, cache, default_fn=self._serialize)
        self._memo = cache
        self._memo_time = time.time()

    def get(self, key: Any, allow_expiring: bool = False) -> Optional[dict]:
        cache = self._load_cache()
        entry = cache.get(str(key))
        if not isinstance(entry, dict):
            return None
        if time.time() - entry.get("cached_at", 0) > TOKEN_CACHE_TTL_SEC:
            self.invalidate(key)
            return None
        if str(entry.get("account_id", "")).isdigit():
            entry["account_id"] = int(entry["account_id"])
        if not isinstance(entry.get("login_payload_data"), (bytes, bytearray)):
            self.invalidate(key)
            return None
        if not allow_expiring and is_jwt_expiring_soon(entry):
            return None
        return entry

    def set(self, key: Any, data: dict) -> dict:
        now = time.time()
        entry = dict(data)
        issued_at = entry.get("jwt_issued_at") or now
        entry["jwt_issued_at"] = issued_at
        entry["jwt_expires_at"] = compute_jwt_expires_at(entry.get("token"), issued_at)
        entry["cached_at"] = now
        cache = self._load_cache()
        cache[str(key)] = entry
        self._save_cache(cache)
        return entry

    def invalidate(self, key: Any) -> None:
        cache = self._load_cache()
        if str(key) in cache:
            del cache[str(key)]
            self._save_cache(cache)

    async def ensure_valid_account(
        self,
        account_data: Optional[dict],
        region_override: Optional[str] = None,
        force_refresh: bool = False,
    ) -> Optional[dict]:
        """Đảm bảo tài khoản luôn có JWT còn hạn (dùng lock chống đua khi chạy nhiều bot)."""
        if not isinstance(account_data, dict):
            return None
        auth_type = account_data.get("auth_type")
        cache_key = (
            str(account_data["auth_uid"])
            if auth_type == "guest" and account_data.get("auth_uid")
            else f"tok_{str(account_data.get('auth_token', ''))[:20]}"
        )
        lock = self._get_lock(cache_key)
        async with lock:
            if not force_refresh:
                cached = self.get(cache_key, allow_expiring=False)
                if cached:
                    return cached
            else:
                self.invalidate(cache_key)

            if auth_type == "guest" and account_data.get("auth_uid") and account_data.get("auth_password"):
                rem_sec = max(0.0, float(account_data.get("jwt_expires_at", 0)) - time.time())
                log_info(f"[TOKEN] Làm mới JWT cho UID {account_data['auth_uid']} (còn ~{rem_sec/60:.0f} phút)")
                return await login_guest_account(
                    str(account_data["auth_uid"]),
                    str(account_data["auth_password"]),
                    region_override=region_override or account_data.get("region"),
                    force_fresh=True,
                )

            if auth_type == "token" and account_data.get("auth_token"):
                log_info("[TOKEN] Làm mới phiên từ Garena access_token...")
                return await exchange_garena_token(str(account_data["auth_token"]), force_fresh=True)

            return None


token_manager = TokenManager()


# ==================== ĐĂNG NHẬP & API GAME ====================
def get_app_version() -> str:
    try:
        return play_scraper("com.dts.freefireth").get("version") or "1.132.9"
    except Exception:
        return "1.132.9"


async def fetch_version_config(region: str = "ID") -> Optional[Tuple[str, str, str, str, str]]:
    app_version = get_app_version()
    lang = REGION_LANG.get(region.upper(), "en")
    url = (
        f"https://vnversion.ggpinkpenguin.com/live/ver.php?version={app_version}"
        f"&lang={lang}&device=android&channel=android&appstore=googleplay_vietnam"
        f"&region={region.upper()}&release_version=OB55&whitelist_version=1.8.1&whitelist_sp_version=1.0.0"
        f"&device_name=INFINIX%20Infinix%20X6891&device_CPU=ARMv7%20VFPv3%20NEON"
        f"&device_GPU=Adreno%20%28TM%29%20650&device_mem=2020"
    )
    try:
        resp = await http_client.get(url)
        data = resp.json()
        server_url = data.get("server_url")
        if not server_url:
            return None
        remote_version = data.get("remote_version")
        latest_release = data.get("latest_release_version")
        gops = [u.strip() for u in data.get("gop_url", "").split(";") if u.strip()]
        gop_1 = gops[0] if gops else "https://ffmconnect.ppmainecoonghj.com"
        return latest_release, remote_version, server_url, gop_1, app_version
    except Exception as exc:
        log_err(f"[VERCONFIG] {exc}")
        return None


async def grant_guest_access_token(uid: str, password: str) -> Optional[Tuple[str, str, Any]]:
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    headers = {
        "Host": "100067.connect.garena.com",
        "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B)",
        "Content-Type": "application/x-www-form-urlencoded",
        "Accept-Encoding": "gzip, deflate, br",
        "Connection": "close",
    }
    payload = {
        "uid": str(uid),
        "password": password,
        "response_type": "token",
        "client_type": "2",
        "client_secret": HEX_KEY,
        "client_id": "100067",
    }
    for _ in range(4):
        try:
            resp = await http_client.post(url, headers=headers, data=payload)
            if resp.status_code == 200:
                j = resp.json()
                oid, at, pf = j.get("open_id"), j.get("access_token"), j.get("platform", 4)
                if oid and at:
                    return oid, at, pf
        except Exception:
            pass
        await asyncio.sleep(0.7)
    return None


def generate_api_signature(payload_str: str) -> str:
    return hmac.new(API_KEY, payload_str.encode(), hashlib.sha256).hexdigest()


async def register_guest_uid(password: str, gop_url: str, app_version: str) -> Optional[str]:
    payload = json.dumps({"app_id": 100067, "client_type": 2, "password": password, "source": 2}, separators=(",", ":"))
    headers = {
        "User-Agent": f"GarenaMSDK/4.0.44(Infinix X6891 ;Android 7.1.2;en;US;app {app_version} 2019121257;)",
        "Authorization": f"Signature {generate_api_signature(payload)}",
        "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8",
    }
    for attempt in range(3):
        try:
            connector = aiohttp.TCPConnector(resolver=aiohttp.ThreadedResolver())
            async with aiohttp.ClientSession(connector=connector) as session:
                async with session.post(
                    f"{gop_url}/api/v2/oauth/guest:register",
                    headers=headers,
                    data=payload,
                    timeout=aiohttp.ClientTimeout(total=15),
                ) as resp:
                    data = json.loads(await resp.text())
                    if data.get("code") == 0:
                        return data["data"]["uid"]
        except Exception as exc:
            if attempt == 2:
                log_err(f"[REGISTER] {exc}")
        await asyncio.sleep(1.0)
    return None


async def grant_gop_token(uid: str, password: str, gop_url: str, app_version: str) -> Optional[dict]:
    for attempt in range(3):
        try:
            connector = aiohttp.TCPConnector(resolver=aiohttp.ThreadedResolver())
            payload = json.dumps({
                "client_id": 100067,
                "client_secret": HEX_KEY,
                "client_type": 2,
                "device_id": f"02-{uuid.uuid4()}",
                "password": password,
                "response_type": "token",
                "uid": int(uid),
            }, separators=(",", ":"))
            headers = {
                "User-Agent": f"GarenaMSDK/4.0.44(Infinix X6891 ;Android 7.1.2;en;US;app {app_version} 2019121257;)",
                "Authorization": f"Signature {generate_api_signature(payload)}",
                "Accept": "application/json",
                "Content-Type": "application/json; charset=utf-8",
            }
            async with aiohttp.ClientSession(connector=connector) as session:
                async with session.post(
                    f"{gop_url}/api/v2/oauth/guest/token:grant",
                    headers=headers,
                    data=payload,
                    timeout=aiohttp.ClientTimeout(total=15),
                ) as resp:
                    data = json.loads(await resp.text())
                    if data.get("code") == 0:
                        return data["data"]
        except Exception as exc:
            if attempt == 2:
                log_err(f"[GRANT] {exc}")
        await asyncio.sleep(1.0)
    return None


async def build_login_payload(access_token: str, open_id: str, platform: Any, version: str, lang_code: str = "vn") -> bytes:
    major_login = {
        "3": str(time.strftime("%Y-%m-%d %H:%M:%S"))[:-3],
        "4": "free fire",
        "5": 4,
        "7": f"{version}",
        "8": "Android OS 16 / API-36 (BP2A.250605.031.A3/OS3.0.303.0.WOQMIXM)",
        "9": "Handheld",
        "10": "Viettel",
        "11": "CarrierDataNetwork",
        "12": 2400,
        "13": 1080,
        "14": "450",
        "15": "ARMv7 VFPv3 NEON | 2002 | 8",
        "16": 7485,
        "17": "PowerVR B-Series BXM-8-256",
        "18": "OpenGL ES 3.2 build 25.1@6715691",
        "19": f"Google|{uuid.uuid4()}",
        "20": "27.65.22.191",
        "21": lang_code,
        "22": f"{open_id}",
        "23": f"{platform}",
        "24": "Handheld",
        "25": "Xiaomi 24094RAD4G",
        "26": "VN",
        "29": f"{access_token}",
        "30": 1,
        "41": "Viettel",
        "42": "4G",
        "57": "7428b253defc164018c604a1ebbfebdf",
        "60": 233141,
        "61": 169421,
        "62": 902,
        "64": 169945,
        "65": 233141,
        "66": 169945,
        "67": 233141,
        "73": 3,
        "74": "/data/app/~~OOxSMPtiZSaEIgYJjPoHOg==/com.dts.freefireth-KkAAAdjU2FG5Ts4HwgDgCw==/lib/arm64",
        "76": 1,
        "77": "b8e0cd5e295eee42f5860d3c86e483dd|/data/app/~~OOxSMPtiZSaEIgYJjPoHOg==/com.dts.freefireth-KkAAAdjU2FG5Ts4HwgDgCw==/base.apk",
        "78": 3,
        "79": 2,
        "81": "64",
        "83": "2019121229",
        "85": 3,
        "86": "OpenGLES2",
        "87": 8191,
        "88": int(platform),
        "90": "Ho Chi Minh City",
        "91": "SG",
        "92": 9339,
        "93": "android",
        "94": "KqsHTw6ig4Gc39MBHQa+5VKNNU8oo4ak8w0NllWLvoUr+2pIZc1TeWooIvcbn49btS06j6slKvWIX9RN9g+0k5QhGwsfQ6S0ZCVXh8Tr9/PC43kX",
        "95": 111207,
        "96": '{"cur_rate":[60,90,120],"support_etc2":false}',
        "97": 1,
        "99": "4",
        "100": "4",
        "102": "",
        "103": 1,
        "104": 53896,
        "105": 1,
        "106": "https://dl.gmc.freefiremobile.com/live/ABHotUpdates/|https://core-gmc.freefiremobile.com/live/ABHotUpdates/|ac2c27398b1d5d95a4b6b6e04fa94066",
        "107": "1.eaed02dd9f66cfa5",
    }
    return bytes.fromhex(encrypt_aes(create_proto(major_login).hex()))


def _insecure_ssl_context() -> ssl.SSLContext:
    ctx = ssl.create_default_context()
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE
    return ctx


async def post_major_login(payload: bytes, login_url: str, release_version: str) -> Optional[dict]:
    url = f"{login_url.rstrip('/')}/MajorLogin"
    headers = {
        "Accept": "*/*",
        "Authorization": "Bearer ",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_version}",
        "User-Agent": "UnityPlayer/2018.4.12f1",
        "X-GA": "v1 1",
        "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1",
    }
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
            async with session.post(url, headers=headers, data=payload, ssl=_insecure_ssl_context()) as resp:
                content = await resp.read()
                log_info(f"MAJOR-LOGIN status={resp.status} len={len(content)}")
                if resp.status != 200 or len(content) < 200:
                    return None
                best = None
                best_score = -1
                best_off = 0
                for offset in [64, 0, 48, 32, 80, 16, 128, 8, 96, 60, 56, 40, 24, 20, 12, 4]:
                    if offset >= len(content):
                        continue
                    cb = content[offset:]
                    cand = decode_protobuf_dict(cb)
                    if not cand:
                        c2 = decode_protobuf_2(cb)
                        cand = {str(k): {"data": v} for k, v in c2.items()} if c2 else None
                    if not cand:
                        continue
                    has_jwt = ("8" in cand) or (8 in cand)
                    has_url = ("10" in cand) or (10 in cand)
                    score = len(cand) + (100 if has_jwt else 0) + (50 if has_url else 0)
                    if score > best_score:
                        best, best_score, best_off = cand, score, offset
                    if has_jwt and has_url:
                        break
                if not best or (("8" not in best) and (8 not in best)):
                    return None
                best["__RAW_HEX__"] = content.hex()
                best["__OFFSET__"] = best_off
                return best
    except Exception as exc:
        log_err(f"MAJOR-LOGIN {exc}")
        return None


async def fetch_login_data(payload: bytes, jwt_token: str, server_url: str, release_version: str) -> Optional[dict]:
    url = f"{server_url.rstrip('/')}/GetLoginData"
    headers = {
        "Accept": "*/*",
        "Authorization": f"Bearer {jwt_token}",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_version}",
        "User-Agent": "UnityPlayer/2018.4.12f1",
        "X-GA": "v1 1",
        "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1",
    }
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as session:
            async with session.post(url, headers=headers, data=payload, ssl=_insecure_ssl_context()) as resp:
                if resp.status != 200:
                    return None
                content = await resp.read()
                for off in [0, 64, 48, 32, 80, 16, 128, 8, 96]:
                    if off < len(content):
                        c = decode_protobuf_dict(content[off:])
                        if c and len(c) >= 3:
                            return c
                for off in [0, 64, 48, 32, 80]:
                    if off < len(content):
                        c2 = decode_protobuf_2(content[off:])
                        if c2 and len(c2) >= 3:
                            return {str(k): {"data": v} for k, v in c2.items()}
        return None
    except Exception:
        return None


async def fetch_player_profile(target_uid: int, jwt_token: str, server_url: str, release_version: str) -> Optional[dict]:
    url = f"{server_url.rstrip('/')}/GetPlayerPersonalShow"
    payload = bytes.fromhex(encrypt_aes(create_proto({"1": int(target_uid)}).hex()))
    headers = {
        "authorization": f"Bearer {jwt_token}",
        "host": server_url.replace("https://", "").split("/")[0],
        "x-ga": "v1 1",
        "content-type": "application/x-www-form-urlencoded",
        "releaseversion": f"{release_version}",
        "user-agent": "UnityPlayer/2022.3.47f1",
        "accept": "*/*",
        "x-unity-version": "2022.3.47f1",
    }
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=8)) as session:
            async with session.post(url, headers=headers, data=payload, ssl=_insecure_ssl_context()) as resp:
                if resp.status != 200:
                    return None
                return decode_protobuf_2(await resp.read())
    except Exception:
        return None


# ==================== QUÂN ĐOÀN & GÓI TIN TEAM / TCP ====================
def get_region_from_jwt(jwt_token: str) -> str:
    try:
        p = jwt_token.split(".")[1]
        p += "=" * (-len(p) % 4)
        d = json.loads(base64.urlsafe_b64decode(p))
        return (d.get("lock_region") or d.get("noti_region") or "BD").upper()
    except Exception:
        return "ID"


def get_region_api_url(region: str) -> str:
    reg = region.upper()
    if reg == "IND":
        return "https://client.ind.freefiremobile.com"
    if reg in ("BR", "US", "NA"):
        return "https://client.us.freefiremobile.com"
    return "https://clientbp.ppmainecoonghj.com"


async def request_join_clan(jwt_token: str, clan_id: Any) -> bool:
    if not CLAN_PB_AVAILABLE or reqClan_pb2 is None:
        return False
    try:
        msg = reqClan_pb2.MyMessage()
        msg.field_1 = int(clan_id)
        payload = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(msg.SerializeToString(), AES.block_size))
        base_url = get_region_api_url(get_region_from_jwt(jwt_token))
        headers = {
            "Authorization": f"Bearer {jwt_token}",
            "X-Unity-Version": "2018.4.11f1",
            "X-GA": "v1 1",
            "ReleaseVersion": "OB55",
            "Content-Type": "application/octet-stream",
            "Host": base_url.replace("https://", ""),
            "Connection": "Keep-Alive",
            "Accept-Encoding": "gzip",
        }
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
            async with session.post(f"{base_url.rstrip('/')}/RequestJoinClan", headers=headers, data=payload, ssl=_insecure_ssl_context()) as resp:
                if resp.status == 200:
                    log_ok(f"Đã gửi yêu cầu vào quân đoàn {clan_id}")
                    return True
                log_warn(f"Join clan trả về HTTP {resp.status}")
                return False
    except Exception as exc:
        log_err(f"CLAN lỗi: {exc}")
        return False


def build_create_team_packet(key: Any, iv: Any, region: str = "ID", game_version: str = "1.132.9", team_size: int = 4) -> bytes:
    reg = str(region or "ID").upper()
    idc = _get_region_idc(reg)
    # Chế độ tử chiến (Clash Squad) - mode_id = 15
    proto_team_size = 3 if team_size >= 3 else team_size
    fields = {
        1: 1,
        2: {
            2: bytes.fromhex("011d"), 3: 15, 4: proto_team_size, 5: "en",
            8: {1: idc, 2: 123, 3: reg},
            9: 1, 10: bytes.fromhex("011d"), 11: 1, 13: 1,
            14: {
                1: "08FBA33B4BABE2790205390333330000009700050092005F72697EB2134DCBB2467625142201040e38e848dc0e748c3f6aa04d81000000ff1113090dcacfa16d",
                2: 478, 3: "7e585d55", 4: "y[Z]", 6: 12, 7: "15686677735a7506101c",
                8: str(game_version), 9: 3, 10: 1, 11: "03626253513637754174",
            },
            19: 324, 21: bytes.fromhex("374f521955"), 24: {1: 21}, 27: "a_6534489873065906362",
        },
    }
    if proto_team_size > 1:
        fields[2][27] = "a_6534489873065906362"
    return create_packet(create_proto(fields).hex(), get_team_packet_prefix(reg), key, iv)


def build_leave_team_packet(account_id: Any, key: Any, iv: Any, region: str = "ID") -> bytes:
    reg = str(region or "ID").upper()
    return create_packet(
        create_proto({1: 7, 2: {1: int(account_id)}}).hex(),
        get_team_packet_prefix(reg),
        key,
        iv,
    )


def build_invite_team_packet(target_uid: Any, key: Any, iv: Any, region: str = "ID") -> bytes:
    reg = str(region or "ID").upper()
    return create_packet(
        create_proto({1: 2, 2: {1: int(target_uid), 2: reg, 4: 1}}).hex(),
        get_team_packet_prefix(reg),
        key,
        iv,
    )


def build_accept_invite_packet(target_uid: Any, group_id: str, key: Any, iv: Any, region: str = "ID", game_version: str = "1.132.9") -> bytes:
    reg = str(region or "ID").upper()
    idc = _get_region_idc(reg)
    fields = {
        1: 4,
        2: {
            1: int(target_uid), 3: int(target_uid),
            4: bytes.fromhex("0107090a0b120f19202729"), 8: 1,
            9: {
                1: "08FBA33B0522052002041B0222220007000C00010004000547E265AE1080779546762514110104076fa2e8770e748c3f6a68ed75000000ff08080500cacfa16d",
                2: 235, 3: {14: 80, 11: 86}, 4: "{Y\\R", 6: 13, 7: {2: 4},
                8: str(game_version), 9: 2, 10: 1, 11: "0362625351",
            },
            10: str(group_id),
            11: {1: idc, 2: 123, 3: reg},
            13: "en", 16: "374f5219", 20: {1: 21},
            23: "a_6534489873065906362",
            24: "https://dl-sg-production.freefiremobile.com/",
            27: {1: 2, 2: 4},
        },
    }
    return create_packet(create_proto(fields).hex(), get_team_packet_prefix(reg), key, iv)


def build_start_team_match_packet(account_id: Any, key: Any, iv: Any, region: str = "ID") -> bytes:
    reg = str(region or "ID").upper()
    idc = _get_region_idc(reg)
    fields = {1: 9, 2: {1: int(account_id), 7: {1: idc, 2: 410, 3: reg}}}
    return create_packet(create_proto(fields).hex(), get_team_packet_prefix(reg), key, iv)


def build_ready_packet(uid: Any, key: Any, iv: Any, region: str = "ID") -> bytes:
    reg = str(region or "ID").upper()
    return create_packet(
        create_proto({1: 15, 2: {1: int(uid), 2: 1}}).hex(),
        get_team_packet_prefix(reg),
        key,
        iv,
    )


async def build_tcp_startup_packet(account_id: Any, token: str, server_time: Any, key: bytes, iv: bytes, region: str = "ID", typ: str = "OnLine") -> str:
    uid_hex = f"{int(account_id):016x}"
    ts_hex = f"{int(server_time):08x}"
    enc_hex = (await aes_encrypt(token.encode(), key, iv)).hex()
    enc_len = f"{len(enc_hex) // 2:08x}"
    prefix = get_tcp_packet_prefix(region, typ)
    extra = "00000000" if typ == "OnLine" else ""
    return f"{prefix}{uid_hex}{ts_hex}{extra}{enc_len}{enc_hex}"


async def build_keepalive_packet(region: str = "ID") -> bytes:
    reg = str(region or "ID").upper()
    if reg == "ID":
        return bytes.fromhex("0219")
    if reg == "IND":
        return bytes.fromhex("0214")
    return bytes.fromhex("0215")


async def send_solo_match_packet(region: str, client_version: str, writer: asyncio.StreamWriter, key: bytes, iv: bytes) -> None:
    raw_pkt = bytes.fromhex("0314000001e0a8c1becfcdd1a311df1b23e218f8b6ae1df958f76dfeb6bfd0399d153d1f9687174c189de3900d11f3eb8fd92cd831c482b06adec14632935703a0423b76051274d67f1381e5794cc6256079d1514ad9f9fa864733257d8e5910e9ba2f048dbe5008ba23d7e4db609ceb46ab823a50a15d0692d44c73d1f6c8e9ee33462952f2685ef8b32faea409a9b61ea091f3a36a727773dbb8316c01dfa6512dbe5b3a3ce6c8310783386c9c70c8fe143f6bc39854fdd1fffd157e52ef006a9e1e944b252a0072154aa34a45b7a5f080d7043eaf0ec6dd884b62b906781cdecca9d49f50f521c4a57dcefc4e5c274f242dcad6489dae6795c2173803fb1d343f64d47699164508e95709a43f018efca4eab791ff4010aab17d1926f7d5e11983249879940d90d5f257ad66dc0e193716addb278510de0afa48825d24ec20724382d731a2f2258ace8a4e614bfb620dc90ee9c3a87e5deaed1d44efdb561e320bc9faab91aea632d060f4ffa268067ab588edd6342c086059accb30d036b3cf766858f54b434d446935912e0e9c21b7e22ace9f17852366bd2390988f82545239e54baafcfd7bcd75d8a69a327019f8b608d80a49cbb6a65b31eec3fcab74afee3da4a9d59e367edd3f32d8eb0b8b516bcfbc1e104bd8c8bda5b76f8e5190ec1898d004dc")
    try:
        proto = thunderFF_pb2.StartMatch()
        proto.ParseFromString(raw_pkt)
        if hasattr(proto.main, "region_list") and len(proto.main.region_list) > 0:
            proto.main.region_list[0].region = region
            if len(proto.main.region_list) > 1:
                proto.main.region_list[1].region = region
        if hasattr(proto.main, "client_version"):
            proto.main.client_version.remote_version = client_version
        pkt_bytes = proto.SerializeToString()
    except Exception:
        pkt_bytes = raw_pkt

    reg = str(region or "BD").upper()
    prefix = "0319" if reg == "BD" else ("0314" if reg == "IND" else "0315")
    enc_hex = (await aes_encrypt(pkt_bytes, key, iv)).hex()
    pkt_len = len(enc_hex) // 2
    writer.write(bytes.fromhex(f"{prefix}{pkt_len:08x}{enc_hex}"))
    await writer.drain()
    log_event(f"Gửi yêu cầu tìm trận ({pkt_len}B)", color=PX.AMBER, icon=ICONS["target"], tag="MATCH")


# ==================== UDP & ĐIỀU KHIỂN DI CHUYỂN ====================
async def tea_enc(v0: int, v1: int, k0: int, k1: int, k2: int, k3: int) -> Tuple[int, int]:
    s = 0
    for _ in range(_ROUNDS):
        s = (s + _DELTA) & 0xFFFFFFFF
        v0 = (v0 + (((((v1 << 4) & 0xFFFFFFFF) + k0) & 0xFFFFFFFF ^ ((v1 + s) & 0xFFFFFFFF) ^ (((v1 >> 5) + k1) & 0xFFFFFFFF)))) & 0xFFFFFFFF
        v1 = (v1 + (((((v0 << 4) & 0xFFFFFFFF) + k2) & 0xFFFFFFFF ^ ((v0 + s) & 0xFFFFFFFF) ^ (((v0 >> 5) + k3) & 0xFFFFFFFF)))) & 0xFFFFFFFF
    return v0, v1


async def tea_dec(v0: int, v1: int, k0: int, k1: int, k2: int, k3: int) -> Tuple[int, int]:
    s = (_DELTA * _ROUNDS) & 0xFFFFFFFF
    for _ in range(_ROUNDS):
        v1 = (v1 - (((((v0 << 4) & 0xFFFFFFFF) + k2) & 0xFFFFFFFF ^ ((v0 + s) & 0xFFFFFFFF) ^ (((v0 >> 5) + k3) & 0xFFFFFFFF)))) & 0xFFFFFFFF
        v0 = (v0 - (((((v1 << 4) & 0xFFFFFFFF) + k0) & 0xFFFFFFFF ^ ((v1 + s) & 0xFFFFFFFF) ^ (((v1 >> 5) + k1) & 0xFFFFFFFF)))) & 0xFFFFFFFF
        s = (s - _DELTA) & 0xFFFFFFFF
    return v0, v1


async def tea_cbc_encrypt(padded: bytes, key_bytes: bytes) -> bytes:
    k0, k1, k2, k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0, 4, 8, 12))
    out = bytearray(len(padded))
    pc = bytearray(8)
    pi = bytearray(8)
    for i in range(0, len(padded), 8):
        x = bytearray(padded[i + j] ^ pc[j] for j in range(8))
        e0, e1 = await tea_enc(struct.unpack_from("<I", x, 0)[0], struct.unpack_from("<I", x, 4)[0], k0, k1, k2, k3)
        enc = struct.pack("<II", e0, e1)
        for j in range(8):
            out[i + j] = enc[j] ^ pi[j]
        pc[:] = out[i:i + 8]
        pi[:] = x
    return bytes(out)


async def tea_cbc_decrypt(body: bytes, key_bytes: bytes) -> bytes:
    k0, k1, k2, k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0, 4, 8, 12))
    out = bytearray(len(body))
    pi = bytearray(8)
    pc = bytearray(8)
    for i in range(0, len(body), 8):
        x = bytes(body[i + j] ^ pi[j] for j in range(8))
        d0, d1 = await tea_dec(struct.unpack_from("<I", x, 0)[0], struct.unpack_from("<I", x, 4)[0], k0, k1, k2, k3)
        dec = struct.pack("<II", d0, d1)
        for j in range(8):
            out[i + j] = dec[j] ^ pc[j]
        pc[:] = body[i:i + 8]
        pi[:] = dec
    return bytes(out)


async def build_padded(content: bytes) -> bytes:
    pad_len = (8 - (len(content) + 10) % 8) % 8
    return bytes([pad_len, 0, 0]) + (b"\x00" * pad_len) + content + (b"\x00" * 7)


async def oicq_unpad(padded: bytes) -> Optional[bytes]:
    if not padded or len(padded) < 8:
        return None
    if not all(padded[-1 - i] == 0 for i in range(7)):
        return None
    pad_len = padded[0] & 0x07
    start, end = 3 + pad_len, len(padded) - 7
    return padded[start:end] if start < end else b""


async def encode_header(layout: List[int], so: int, cmd: int, oid: Optional[int], flags: int, length: int, k: int, v80: int) -> bytes:
    out = bytearray()
    vals = {0: so, 1: cmd, 2: oid or 0, 3: flags, 4: length}
    for code in layout:
        val = vals[code]
        if _FIELD_SIZES[code] == 1:
            out.append((val & 0xFF) ^ k)
        else:
            v = ((val & 0xFFFF) ^ v80) & 0xFFFF
            out.append(v & 0xFF)
            out.append((v >> 8) & 0xFF)
    return bytes(out)


async def build_packet(
    msg_key: int, layout: List[int], so: int, cmd: int, oid: Optional[int],
    flags: int, content: bytes, key: bytes, encrypted: bool = True,
) -> bytes:
    k = key[0]
    v80 = ((k << 8) | k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0]) + await encode_header(layout, so, cmd, oid, flags, len(body), k, v80)
    pkt = bytearray(hdr + body)
    pkt[1] = crc7_sync(bytes(pkt[2:])) & 0x7F
    return bytes(pkt)


async def layouts_from_mask(mask: Any) -> Tuple[List[int], List[int]]:
    if isinstance(mask, (bytes, bytearray)):
        mask = mask.decode("utf-8", errors="ignore")
    digits = "".join(ch for ch in str(mask).strip() if ch in "01234")
    ru = [int(c) for c in digits] if len(digits) == 5 else [0, 1, 4, 3, 2]
    nr = [c for c in ru if c != 2]
    return ru, nr


async def build_match_startup_packets(
    token: str, udp_key_hex: str, match_code: Any, account_id: Any, block_val: Any,
    server_ip: str = "", region: str = "ID", client_version: str = "1.132.9",
    client_version_code: str = "2019121229", access_token: str = "", mode_id: int = 1, map_id: int = 1,
) -> Tuple[str, str]:
    token = token.strip()
    udp_key = bytes.fromhex(udp_key_hex)
    layout = [int(ch) for ch in str(match_code).strip()]
    thunder_jwt = token[:660] if len(token) > 660 else token
    sharma_jwt = token[660:] if len(token) > 660 else ""
    eth = thunder_jwt.encode()
    esh = sharma_jwt.encode()
    garena420 = await uleb_encode((len(eth) << 1) & 0xFFFFFFFFFFFFFFFF) + eth
    reg = str(region or "ID").upper()
    csoversea_block = bytes.fromhex(
        "ca0163736f7665727365612e7374726f6e67686f6c642e66726565666972656d6f62696c652e636f6d"
        "3b302e302e302e303b33342e3132362e37362e34353b33342e38372e3137372e31343b33342e38372e"
        "3137302e3233303b33352e3138352e3138332e35370000000000000100000000000000000000000001"
        "00000800000100000000000100a8a2d7bebd8d8bdf110200"
    )
    mid = (
        bytes.fromhex("0000000001000102030101")
        + await uleb_encode((len(reg) << 1) & 0xFFFFFFFFFFFFFFFF)
        + reg.encode()
        + bytes.fromhex("0001030003000004")
        + await uleb_encode((len(client_version) << 1) & 0xFFFFFFFFFFFFFFFF)
        + client_version.encode()
        + await uleb_encode((len(client_version_code) << 1) & 0xFFFFFFFFFFFFFFFF)
        + client_version_code.encode()
        + csoversea_block
    )
    clean_ip = server_ip.split(":")[0] if server_ip else "0.0.0.0"
    mid += await uleb_encode((len(clean_ip) << 1) & 0xFFFFFFFFFFFFFFFF) + clean_ip.encode()
    if access_token and access_token.strip():
        at = access_token.strip().encode()
        mid += await uleb_encode((len(at) << 1) & 0xFFFFFFFFFFFFFFFF) + at
    mid += await uleb_encode((len(esh) << 1) & 0xFFFFFFFFFFFFFFFF) + esh

    tg = (
        await uleb_encode(int(account_id))
        + await uleb_encode(int(block_val))
        + await uleb_encode(1)
        + await uleb_encode(int(mode_id))
        + await uleb_encode(int(block_val))
        + await uleb_encode(int(map_id))
        + mid
    )
    process_pkt = await build_packet(0x5E, layout, 2, 447, 0, 1, garena420, udp_key)
    loading_pkt = await build_packet(0x5A, layout, 2, 448, 1, 1, tg, udp_key)
    return process_pkt.hex(), loading_pkt.hex()


async def build_hello_packet(text: str, key: bytes, layout: Any) -> str:
    data = text.encode("utf-8")
    if len(data) > 25:
        raise ValueError("Hello text quá dài")
    content = b"\x10\x00\x00\x00" + data + (b"\x00" * (29 - 4 - len(data)))
    k = key[0]
    v80 = ((k << 8) | k) & 0xFFFF
    lay = [int(c) for c in str(layout).strip()] if isinstance(layout, str) else list(layout)
    enc_body = await tea_cbc_encrypt(await build_padded(content), key)
    hdr = await encode_header(lay, 1, 1, 0, 1, len(enc_body), k, v80)
    pkt = bytearray(b"\x63\x00" + hdr + enc_body)
    pkt[1] = crc7_sync(bytes(pkt[2:])) & 0x7F
    return bytes(pkt).hex()


async def classify_frame(frame: dict) -> str:
    cmd = frame["cmd"]
    name = MESSAGE_ID_TO_NAME.get(cmd, f"UNKNOWN_{cmd}")
    if name == "UDP_HELLO":
        return "HELLO"
    if name == "UDP_ACK":
        return "ACK"
    if name == "UDP_PING":
        return "PING"
    if name == "RUDP_JOIN_MATCH":
        return "JOIN_MATCH"
    if name.startswith("RUDP_") or name.startswith("UDP_"):
        return name
    return "DATA"


async def build_reply_packet(frame: dict, key: bytes, mask: Any, ack_style: str = "short") -> Tuple[str, Optional[bytes]]:
    _, nr = await layouts_from_mask(mask)
    typ = await classify_frame(frame)
    if typ == "HELLO":
        if ack_style == "echo":
            content = frame["content"] or b"\x10\x00\x00\x00"
            return typ, await build_packet(0x5B, nr, 1, 1, None, 1, content, key)
        return typ, await build_packet(0x68, nr, 0, 2, None, 1, b"\x01\x00", key)
    if typ == "ACK":
        return typ, await build_packet(0x68, nr, 0, 2, None, 1, frame["content"] or b"\x01\x00", key)
    if typ == "PING":
        c = frame["content"]
        counter = c[:4] if len(c) >= 4 else c
        return typ, await build_packet(0x6D, nr, 0, 3, None, 0, counter + b"\x00\x00\x00", key, encrypted=False)
    if typ == "JOIN_MATCH":
        return typ, await build_packet(0x68, nr, 0, 2, None, 1, b"\x02\x00", key)
    return typ, None


async def keepalive_ping(sock: socket.socket, ip: str, port: int, key_bytes: bytes, mask: Any, stop_event: asyncio.Event) -> None:
    _, nr = await layouts_from_mask(mask)
    ping_keys = [0x66, 0x6D, 0x69, 0x6C, 0x6B, 0x6E, 0x6F, 0x70]
    loop = asyncio.get_running_loop()
    idx = 0
    while not stop_event.is_set():
        pk = ping_keys[idx % len(ping_keys)]
        counter = int(time.time() * 1000) & 0xFFFFFFFF
        pkt = await build_packet(pk, nr, 0, 3, None, 0, struct.pack("<I", counter) + b"\x00\x00\x00", key_bytes, encrypted=False)
        try:
            await loop.sock_sendto(sock, pkt, (ip, port))
        except Exception:
            pass
        idx += 1
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=3.0)
        except asyncio.TimeoutError:
            pass


async def try_header(buf: bytes, layout: List[int], k: int, v80: int) -> Optional[dict]:
    off = 2
    out: dict = {}
    for code in layout:
        size = _FIELD_SIZES[code]
        if off + size > len(buf):
            return None
        out[_FIELD_NAMES[code]] = (
            (buf[off] ^ k) if size == 1 else (((buf[off] | (buf[off + 1] << 8)) ^ v80) & 0xFFFF)
        )
        off += size
    out["headerLen"] = off
    return out


async def decode_packet(packet: Any, key: bytes, mask: Any = None) -> Optional[dict]:
    data = bytes(packet) if isinstance(packet, (bytes, bytearray)) else bytes.fromhex(packet)
    if len(data) < 8:
        return None
    k = key[0]
    v80 = ((k << 8) | k) & 0xFFFF
    crc_ok = (data[1] & 0x7F) == crc7_sync(data[2:])

    if mask:
        ru, nr = await layouts_from_mask(mask)
        layouts = [("RUDP", ru), ("nonRUDP", nr)]
        if nr != [0, 1, 4, 3]:
            layouts.append(("nonRUDP", [0, 1, 4, 3]))
        if ru != [0, 1, 4, 3, 2]:
            layouts.append(("RUDP", [0, 1, 4, 3, 2]))
    else:
        layouts = [("RUDP", list(p)) for p in itertools.permutations([0, 1, 2, 3, 4])]
        layouts += [("nonRUDP", list(p)) for p in itertools.permutations([0, 1, 3, 4])]

    candidates = []
    for idx_l, (kind, layout) in enumerate(layouts):
        hdr = await try_header(data, layout, k, v80)
        if not hdr or hdr["flags"] > 7 or hdr["sendOption"] > 7:
            continue
        exact_len = hdr["length"] == len(data) - hdr["headerLen"]
        ack_piggy = (
            bool(hdr["flags"] & 4)
            and 0 <= hdr["length"] <= len(data) - hdr["headerLen"] - 1
            and (len(data) - hdr["headerLen"] - hdr["length"]) <= 32
        )
        if not (exact_len or ack_piggy):
            continue
        body = data[len(data) - hdr["length"]:] if hdr["length"] > 0 else b""
        content: Optional[bytes]
        if hdr["flags"] & 1:
            if len(body) < 8 or len(body) % 8 != 0:
                continue
            content = await oicq_unpad(await tea_cbc_decrypt(body, key))
            if content is None:
                continue
        else:
            content = body
        score = (2 if crc_ok else 0) + (2 if idx_l < 2 else 0) + (1 if exact_len else 0) + 1
        candidates.append({
            "kind": kind,
            "layout": layout,
            "headerLen": hdr["headerLen"],
            "msgKey": data[0],
            "cmd": hdr["cmd"],
            "flags": hdr["flags"],
            "sendOption": hdr["sendOption"],
            "orderId": hdr.get("orderId"),
            "length": hdr["length"],
            "content": content,
            "crcOk": crc_ok,
            "score": score,
        })

    if not candidates:
        return None
    candidates.sort(key=lambda c: c["score"], reverse=True)
    return candidates[0]


def _f32_bits(val: float) -> int:
    return struct.unpack("<I", struct.pack("<f", float(val)))[0]


async def build_movement_packet_2001(
    key_bytes: bytes, msg_key: int, x: float, y: float, z: float,
    tick: int, counter: int, room_code: Any = None, angle: float = 0.0,
    speed: float = 0.0, vel_y: float = 0.0, s1: int = 0, s2: int = 2, player_match_id: int = 1,
) -> bytes:
    _, nr = await layouts_from_mask(room_code) if room_code else ([0, 1, 4, 3, 2], [0, 1, 4, 3])
    pid_val = int(player_match_id) & 0x7F if player_match_id else 1
    body = bytearray(await uleb_encode((1 << 24) | pid_val))
    body += await zigzag_encode_signed(int(round(x)))
    body += await zigzag_encode_signed(int(round(y)))
    body += await zigzag_encode_signed(int(round(z)))

    ca, sa = math.cos(angle), math.sin(angle)
    fx = max(-100, min(100, int(round(100.0 * ca))))
    fy = -24 if s1 == 2 else 0
    fz = max(-100, min(100, int(round(100.0 * sa))))
    body += await zigzag_encode_signed(fx)
    body += await zigzag_encode_signed(fy)
    body += await zigzag_encode_signed(fz)

    if s1 in (4, 2):
        mx, mz = 0, 100
    elif s1 == 1 and s2 == 11:
        mx, mz = 0, 0
    elif speed > 1.0:
        mx, mz = fx, fz
    else:
        mx, mz = 0, 0
    body += await zigzag_encode_signed(mx)
    body += await zigzag_encode_signed(mz)

    body += await zigzag_encode_signed(int(round((speed * ca) / 10.0)))
    body += await zigzag_encode_signed(int(round(vel_y / 10.0)))
    body += await zigzag_encode_signed(int(round((speed * sa) / 10.0)))

    body += await uleb_encode(int(s1))
    body += await uleb_encode(int(s2))

    pitch = -0.25
    cp, sp = math.cos(pitch), math.sin(pitch)
    for comp in (ca * cp, sp, sa * cp):
        body += await uleb_encode(_f32_bits(comp))

    body += b"\x00\x00"
    body += struct.pack("<I", int(tick))
    body += await uleb_encode(int(counter) & 0xFFFFFFFF)
    return await build_packet(msg_key, nr, 0, 2001, None, 0, bytes(body), key_bytes, encrypted=False)


class MovementController:
    def __init__(
        self, account_id, account_region, key, iv,
        udp_sock=None, udp_server=None,
        udp_key_bytes=None, match_code=None, slot_id=None,
        mode_id=DEFAULT_GAME_MODE_ID, map_id=DEFAULT_GAME_MAP_ID,
    ):
        self.account_id = int(account_id) if str(account_id).isdigit() else 0
        self.account_id_uleb = uleb_encode_sync(self.account_id)
        self.region = str(account_region).upper()
        self.key = key
        self.iv = iv
        self.udp_sock = udp_sock
        self.udp_server = udp_server
        self.udp_key = udp_key_bytes
        self.match_code = match_code
        self.mode_id = int(mode_id) if mode_id else DEFAULT_GAME_MODE_ID
        self.map_id = int(map_id) if map_id else DEFAULT_GAME_MAP_ID
        self.is_cs_mode = (self.mode_id in (2, 4, 15))
        self.slot_id = max(1, min(4, int(slot_id))) if slot_id is not None else 1

        self.player_match_id = None
        self.phase = "ground" if self.is_cs_mode else "island"
        self.air_s1 = 4
        self.air_s2 = 0
        if self.is_cs_mode:
            self.spawn_x = 561760 + ((self.slot_id - 1) * 800)
            self.spawn_y = 24707
            self.spawn_z = -550064 + ((self.slot_id - 1) * 800)
            self.ground_y = 24707
        else:
            self.spawn_x = 5751
            self.spawn_y = 1400160
            self.spawn_z = 1650
            self.ground_y = 1400160
        self.x = float(self.spawn_x)
        self.y = float(self.spawn_y)
        self.z = float(self.spawn_z)
        self.has_real_coords = False
        self.has_real_ground_coords = False
        self.plane_x = None
        self.plane_y = None
        self.plane_z = None

        self.tick = 18
        self.counter = 0
        self.angle = ((self.slot_id - 1) * (math.pi / 2.0)) + random.uniform(-0.3, 0.3)
        self.state = "sprint"
        self.cur_speed = 0.0
        self.vel_y = 0.0
        self.pkt_s1 = 0
        self.pkt_s2 = 2
        self.speed_mul = random.uniform(MOVEMENT_SPEED_MIN, MOVEMENT_SPEED_MAX)
        self._msg_keys = [0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C]
        self._key_idx = 0

        self._stop_evt = asyncio.Event()
        self._clock_stop = asyncio.Event()
        self._task = None
        self._clock_task = None
        self._last_decision = 0.0
        self._last_speed_change = 0.0
        self._last_jump_t = 0.0
        self._jump_start_t = 0.0
        self._last_server_ack_t = 0.0
        self._last_air_log_t = 0.0
        self._plane_logged = False
        self._plane_start_t = 0.0
        self._start_time = 0.0
        self._last_clock_echo_t = 0.0
        self.last_srv_pos = None
        self._stuck_ref_pos = None
        self._stuck_ref_t = 0.0
        self._ground_land_t = None
        self._ground_start_t = 0.0

    async def _echo_clock_sync(self, raw_tick_bytes: bytes) -> None:
        if not self.udp_sock or not self.udp_server or not self.udp_key:
            return
        try:
            loop = asyncio.get_running_loop()
            _, nr = await layouts_from_mask(self.match_code)
            mk = self._msg_keys[self._key_idx % len(self._msg_keys)]
            pkt = await build_packet(mk, nr, 0, 2000, None, 0, raw_tick_bytes, self.udp_key, encrypted=False)
            await loop.sock_sendto(self.udp_sock, pkt, self.udp_server)
            self._last_clock_echo_t = time.time()
        except Exception:
            pass

    def handle_server_frame(self, frame: dict) -> None:
        cmd = frame.get("cmd")
        content = frame.get("content")
        if not content:
            return
        try:
            def _dec_v(b, off):
                res = s = 0
                cur = off
                while cur < len(b):
                    bt = b[cur]
                    res |= (bt & 0x7F) << s
                    cur += 1
                    s += 7
                    if not (bt & 0x80):
                        break
                return res, cur

            def _dec_zz(n):
                return (n >> 1) ^ -(n & 1)

            if cmd == 2000 and len(content) >= 1:
                _, end_off = _dec_v(content, 0)
                if end_off >= 1:
                    asyncio.create_task(self._echo_clock_sync(bytes(content[:end_off])))
                return

            if cmd == 2001 and len(content) >= 15 and content[:2] == b"\x00\x02" and 1 <= content[2] <= 64:
                pid = content[2]
                if self.player_match_id is None:
                    self.player_match_id = pid
                elif pid != self.player_match_id:
                    return

                cur = 3
                vx, cur = _dec_v(content, cur)
                vy, cur = _dec_v(content, cur)
                vz, cur = _dec_v(content, cur)
                zx, zy, zz = _dec_zz(vx), _dec_zz(vy), _dec_zz(vz)

                s1 = s2 = 0
                try:
                    for _ in range(8):
                        _, cur = _dec_v(content, cur)
                    s1, cur = _dec_v(content, cur)
                    s2, cur = _dec_v(content, cur)
                except Exception:
                    pass

                now = time.time()

                # CS mode: bỏ qua phase island/plane/airborne
                if not self.is_cs_mode:
                    if zy >= 800000:
                        self.phase = "island"
                        self.ground_y = self.spawn_y = zy
                        self.spawn_x, self.spawn_z = zx, zz
                        self.x, self.y, self.z = float(zx), float(zy), float(zz)
                        if not self.has_real_coords:
                            self.has_real_coords = True
                            log_event(f"SYNC ĐẢO CHỜ | uid={self.account_id} slot={self.slot_id} pos=({zx},{zy},{zz})", color=PX.CYAN, icon=ICONS["target"], tag="AFK")
                        return

                    if s1 == 3:
                        self.phase = "plane"
                        self.has_real_coords = True
                        self.plane_x, self.plane_y, self.plane_z = zx, zy, zz
                        self.x, self.y, self.z = float(zx), float(zy), float(zz)
                        if self._plane_start_t == 0.0:
                            self._plane_start_t = now
                        if not self._plane_logged or (now - self._last_air_log_t) >= 5.0:
                            self._plane_logged = True
                            self._last_air_log_t = now
                            log_event(f"SYNC MÁY BAY | uid={self.account_id} slot={self.slot_id} pos=({zx},{zy},{zz})", color=PX.CYAN, icon=ICONS["rocket"], tag="AFK")
                        in_mainland = (100000 <= zx <= 700000 and -200000 <= zz <= 900000)
                        time_in_plane = now - self._plane_start_t
                        if in_mainland or time_in_plane >= 12.0:
                            if (now - getattr(self, "_last_eject_req_t", 0.0)) >= 0.8:
                                self._last_eject_req_t = now
                                log_event(f"NHẢY MÁY BAY | uid={self.account_id} slot={self.slot_id}", color=PX.GOLD, icon=ICONS["rocket"], tag="AFK")
                        return

                    if s1 in (4, 2) or (s1 == 1 and s2 == 10 and not self.has_real_ground_coords):
                        self.has_real_coords = True
                        target_x, target_z = 350000.0, (350000.0 if zz < 500000 else 750000.0)
                        if self.phase != "airborne":
                            self.phase = "airborne"
                            self.x, self.y, self.z = float(zx), float(zy), float(zz)
                            self.angle = math.atan2(target_z - self.z, target_x - self.x)
                        else:
                            self.y = float(zy)
                            if math.hypot(self.x - zx, self.z - zz) > 3000.0:
                                self.x, self.z = float(zx), float(zz)
                            self.angle = math.atan2(target_z - self.z, target_x - self.x)
                        self.air_s1 = s1 if s1 in (4, 2) else 2
                        self.air_s2 = s2
                        if now - self._last_air_log_t >= 2.5:
                            self._last_air_log_t = now
                            log_event(f"SYNC NHẢY DÙ | uid={self.account_id} slot={self.slot_id} pos=({zx},{zy},{zz})", color=PX.SKY, icon=ICONS["check"], tag="AFK")
                        return

                # Phase ground (CS hoặc BR)
                cs_ground = self.is_cs_mode and (s1 in (0, 1)) and (-600000 <= zz <= 600000)
                br_ground = (not self.is_cs_mode) and zy < 250000
                if cs_ground or br_ground:
                    if not self.has_real_ground_coords:
                        self.phase = "ground"
                        self.spawn_x, self.spawn_y, self.spawn_z = zx, zy, zz
                        self.ground_y = zy
                        self.x, self.y, self.z = float(zx), float(zy), float(zz)
                        self.has_real_coords = self.has_real_ground_coords = True
                        self._ground_land_t = now
                        self.last_srv_pos = (zx, zy, zz)
                        self._stuck_ref_pos = (zx, zy, zz)
                        self._stuck_ref_t = now
                        self.angle = ((self.slot_id - 1) * (math.pi / 2.0)) + random.uniform(-0.3, 0.3)
                        self.state = "sprint"
                        log_event(f"HẠ CÁNH {'CS' if self.is_cs_mode else 'BR'} | uid={self.account_id} slot={self.slot_id} pos=({zx},{zy},{zz})", color=PX.LIME, icon=ICONS["target"], tag="AFK")
                        return

                    self.phase = "ground"
                    prev_srv = self.last_srv_pos or (zx, zy, zz)
                    self.last_srv_pos = (zx, zy, zz)
                    is_jumping = (self.state == "jump" and (now - self._jump_start_t) < 0.85)
                    if s1 == 0 and not is_jumping:
                        self.ground_y = zy
                        self.y = float(zy)

                    err_xz = math.hypot(self.x - zx, self.z - zz)
                    if err_xz > 25000.0:
                        self.x, self.z = float(zx), float(zz)
                        if not is_jumping:
                            self.ground_y = zy
                            self.y = float(zy)
                        self.angle = (self.angle + random.uniform(1.8, 4.4)) % (2.0 * math.pi)

                    # Stuck detector
                    if self._stuck_ref_pos is None:
                        self._stuck_ref_pos = (zx, zy, zz)
                        self._stuck_ref_t = now
                    elif (now - self._stuck_ref_t) >= 2.5:
                        moved_xz = math.hypot(zx - self._stuck_ref_pos[0], zz - self._stuck_ref_pos[2])
                        self._stuck_ref_pos = (zx, zy, zz)
                        self._stuck_ref_t = now
                        if moved_xz < 400.0 and self.cur_speed > 1000.0:
                            self.x, self.z = float(zx), float(zz)
                            self.ground_y = zy
                            self.angle = (self.angle + random.uniform(2.0, 4.2)) % (2.0 * math.pi)
                            if not is_jumping:
                                self._jump_start_t = self._last_jump_t = now
                                self.state = "jump"

                    if (now - self._last_server_ack_t) >= 2.0:
                        self._last_server_ack_t = now
                        log_event(f"VỊ TRÍ OK | uid={self.account_id} slot={self.slot_id} pos=({int(zx)},{int(zy)},{int(zz)}) state={self.state}", color=PX.LIME, icon=ICONS["check"], tag="AFK")
        except Exception:
            pass

    def _pick_state(self) -> str:
        r = random.random()
        if r < 0.50:
            return "sprint"
        if r < 0.70:
            return "run"
        if r < 0.85:
            return "crouch"
        return "walk"

    def _step_position(self, dt: float) -> None:
        now = time.time()
        elapsed = (now - self._start_time) if self._start_time > 0 else 0.0

        if self.is_cs_mode:
            if elapsed > 4.0 and self.phase in ("init", "island", "plane", "airborne") and not self.has_real_ground_coords:
                slot_off = (self.slot_id - 1) * 800
                self.spawn_x = 561760.0 + slot_off
                self.spawn_z = -550064.0 + slot_off
                self.spawn_y = self.ground_y = 24707.0
                self.x, self.y, self.z = float(self.spawn_x), float(self.spawn_y), float(self.spawn_z)
                self.phase = "ground"
                self.has_real_coords = self.has_real_ground_coords = True
                self.state = "sprint"
                self.cur_speed = 5600.0
                log_event(f"CS FALLBACK POS | uid={self.account_id} slot={self.slot_id}", color=PX.GOLD, icon=ICONS["rocket"], tag="AFK")
            if self.phase in ("init", "island", "plane", "airborne"):
                self.phase = "ground"
        else:
            if elapsed > 65.0 and self.phase in ("init", "island", "plane") and not self.has_real_ground_coords:
                slot_off = (self.slot_id - 1) * 800
                px = self.plane_x if self.plane_x is not None else 350000
                pz = self.plane_z if self.plane_z is not None else 350000
                if not (0 <= px <= 750000 and 0 <= pz <= 750000):
                    px, pz = 350000, 350000
                self.spawn_x = px + slot_off
                self.spawn_z = pz + slot_off
                self.spawn_y = self.ground_y = 9229.0
                self.x, self.y, self.z = float(self.spawn_x), float(self.spawn_y), float(self.spawn_z)
                self.phase = "ground"
                self.has_real_coords = self.has_real_ground_coords = True
                self.state = "sprint"
                self.cur_speed = 5600.0
                log_event(f"BR FALLBACK POS | uid={self.account_id} slot={self.slot_id}", color=PX.GOLD, icon=ICONS["rocket"], tag="AFK")

            if self.phase in ("init", "island"):
                self.tick = 18
                self.ground_y = self.spawn_y
                if self.state == "jump":
                    j_prog = (now - self._jump_start_t) / 0.85
                    if 0.0 <= j_prog < 1.0:
                        jump_h = 698.0 * 4.0 * j_prog * (1.0 - j_prog)
                        self.y = float(self.ground_y) + jump_h
                        self.vel_y = 3285.0 * (1.0 - 2.0 * j_prog)
                        self.pkt_s1, self.pkt_s2 = 1, 11
                        speed = 5550.0
                    else:
                        self.y = float(self.ground_y)
                        self.vel_y = 0.0
                        self.pkt_s1, self.pkt_s2 = 1, 0
                        self.state = "sprint"
                        speed = 5600.0
                else:
                    self.y = float(self.ground_y)
                    self.vel_y = 0.0
                    speed = 5600.0 * self.speed_mul
                    self.pkt_s1, self.pkt_s2 = 1, 11
                self.cur_speed = speed
                if speed > 0.0:
                    self.x += math.cos(self.angle) * speed * dt
                    self.z += math.sin(self.angle) * speed * dt
                    if ((self.x - self.spawn_x) ** 2 + (self.z - self.spawn_z) ** 2) > 35000.0 ** 2:
                        self.angle = math.atan2(self.spawn_z - self.z, self.spawn_x - self.x) + random.uniform(-0.35, 0.35)
                return

            if self.phase == "airborne":
                if self.air_s1 == 1 and self.air_s2 == 10:
                    self.cur_speed, self.vel_y = 0.0, -12000.0
                    self.pkt_s1, self.pkt_s2, self.tick = 1, 10, 17
                    self.y += self.vel_y * dt
                else:
                    self.cur_speed, self.vel_y = 6200.0, -11800.0
                    self.pkt_s1, self.pkt_s2, self.tick = self.air_s1, 0, 17
                    self.angle = math.atan2(350000.0 - self.z, 350000.0 - self.x)
                    self.x += math.cos(self.angle) * self.cur_speed * dt
                    self.z += math.sin(self.angle) * self.cur_speed * dt
                    self.y += self.vel_y * dt
                return

        # Phase ground
        self.tick = 18
        if self.state == "jump":
            j_prog = (now - self._jump_start_t) / 0.85
            if 0.0 <= j_prog < 1.0:
                jump_h = 698.0 * 4.0 * j_prog * (1.0 - j_prog)
                self.y = float(self.ground_y) + jump_h
                self.vel_y = 3285.0 * (1.0 - 2.0 * j_prog)
                self.pkt_s1, self.pkt_s2 = 1, 11
                speed = 5550.0
            else:
                self.y = float(self.ground_y)
                self.vel_y = -3300.0
                self.pkt_s1, self.pkt_s2 = 1, 0
                self.state = "sprint"
                speed = 5600.0
        else:
            self.y = float(self.ground_y)
            self.vel_y = 0.0
            if self.state == "idle":
                speed = 0.0
                self.pkt_s1, self.pkt_s2 = 0, 0
            elif self.state == "walk":
                speed = 3400.0 * self.speed_mul
                self.pkt_s1, self.pkt_s2 = 0, 1
            elif self.state == "crouch":
                speed = 2600.0 * self.speed_mul
                self.pkt_s1, self.pkt_s2 = 0, 2
            else:
                self.state = "sprint"
                speed = 5600.0 * self.speed_mul
                self.pkt_s1, self.pkt_s2 = 1, 11

        self.cur_speed = speed
        if speed > 0.0:
            self.x += math.cos(self.angle) * speed * dt
            self.z += math.sin(self.angle) * speed * dt

            if self.has_real_ground_coords:
                if self.is_cs_mode:
                    arena_cx = float(self.spawn_x)
                    arena_cz = float(self.spawn_z)
                    cs_arena_radius = 18000.0
                    dist_to_arena = math.hypot(arena_cx - self.x, arena_cz - self.z)
                    if dist_to_arena > cs_arena_radius:
                        target_angle = math.atan2(arena_cz - self.z, arena_cx - self.x)
                        angle_diff = (target_angle - self.angle + math.pi) % (2.0 * math.pi) - math.pi
                        self.angle = (self.angle + angle_diff * (dt * 2.5) + random.uniform(-0.03, 0.03)) % (2.0 * math.pi)
                    else:
                        self.angle = (self.angle + 0.4 * dt + random.uniform(-0.08, 0.08)) % (2.0 * math.pi)
                else:
                    t_ground = (time.time() - self._ground_land_t) if self._ground_land_t else 0.0
                    if t_ground < 45.0:
                        center_x, center_z = 350000.0, 350000.0
                        dist_to_center = math.hypot(center_x - self.x, center_z - self.z)
                        if dist_to_center > 25000.0:
                            target_angle = math.atan2(center_z - self.z, center_x - self.x)
                            angle_diff = (target_angle - self.angle + math.pi) % (2.0 * math.pi) - math.pi
                            self.angle = (self.angle + angle_diff * (dt * 0.8) + random.uniform(-0.04, 0.04)) % (2.0 * math.pi)
                        else:
                            self.angle = (self.angle + 0.5 * dt + random.uniform(-0.03, 0.03)) % (2.0 * math.pi)
                    else:
                        edge_x, edge_z = 850000.0, -250000.0
                        target_angle = math.atan2(edge_z - self.z, edge_x - self.x)
                        angle_diff = (target_angle - self.angle + math.pi) % (2.0 * math.pi) - math.pi
                        self.angle = (self.angle + angle_diff * (dt * 0.8) + random.uniform(-0.04, 0.04)) % (2.0 * math.pi)

    async def _send_udpp(self) -> bool:
        if not self.udp_sock or not self.udp_server or not self.udp_key or self.phase == "plane":
            return self.phase == "plane"
        try:
            loop = asyncio.get_running_loop()
            time_ms = int((time.time() - self._start_time) * 1000) & 0xFFFFFFFF
            mk = self._msg_keys[self._key_idx % len(self._msg_keys)]
            self._key_idx += 1
            pkt = await build_movement_packet_2001(
                self.udp_key, mk, self.x, self.y, self.z,
                self.tick, time_ms, room_code=self.match_code,
                angle=self.angle, speed=self.cur_speed, vel_y=self.vel_y,
                s1=self.pkt_s1, s2=self.pkt_s2, player_match_id=self.player_match_id or 1,
            )
            await loop.sock_sendto(self.udp_sock, pkt, self.udp_server)
            return True
        except Exception:
            return False

    async def _send_udp(self) -> bool:
        if not self.udp_sock or not self.udp_server or not self.udp_key or self.phase == "plane":
            return self.phase == "plane"
        try:
            loop = asyncio.get_running_loop()
            time_ms = int((time.time() - self._start_time) * 1000) & 0xFFFFFFFF
            p_state = PLAYER_STATE_MAP.get(self.state, 1)
            m_state = MOVE_STATE_MAP.get(self.state, 2)
            mk = self._msg_keys[self._key_idx % len(self._msg_keys)]
            self._key_idx += 1
            pkt = await build_movement_packet_2001(
                self.udp_key, mk,
                self.x, self.y, self.z,
                self.tick, time_ms,
                room_code=self.match_code,
                angle=self.angle, speed=self.cur_speed, vel_y=self.vel_y,
                s1=self.pkt_s1, s2=self.pkt_s2,
                player_match_id=self.player_match_id or 1,
            )
            await loop.sock_sendto(self.udp_sock, pkt, self.udp_server)
            return True
        except Exception:
            return False
            


    async def _clock_sync_loop(self) -> None:
        if not self.udp_sock or not self.udp_server or not self.udp_key:
            return
        loop = asyncio.get_running_loop()
        _, nr = await layouts_from_mask(self.match_code)
        tick_val = 60
        try:
            await asyncio.sleep(2.5)
            while not self._clock_stop.is_set():
                try:
                    if (time.time() - self._last_clock_echo_t) > 4.5:
                        pkt = await build_packet(0x68, nr, 0, 2000, None, 0, await uleb_encode(tick_val), self.udp_key, encrypted=False)
                        await loop.sock_sendto(self.udp_sock, pkt, self.udp_server)
                        tick_val = (tick_val + 60) & 0xFFFFFFFF
                    await asyncio.wait_for(self._clock_stop.wait(), timeout=2.0)
                    break
                except asyncio.TimeoutError:
                    pass
        except asyncio.CancelledError:
            pass

    async def _loop(self) -> None:
        self._start_time = time.time()
        if self.udp_sock and self.udp_server and self.udp_key:
            try:
                loop = asyncio.get_running_loop()
                ru, _ = await layouts_from_mask(self.match_code)
                pkt = await build_packet(0x60, ru, 2, 899, 8, 1, b"", self.udp_key)
                await loop.sock_sendto(self.udp_sock, pkt, self.udp_server)
            except Exception:
                pass
        await asyncio.sleep(1.0)
        if self.is_cs_mode and not getattr(self, "_startup_actions_sent", False):
            self._startup_actions_sent = True
        log_event(f"Anti-AFK START | uid={self.account_id} slot={self.slot_id} cs={self.is_cs_mode}", color=PX.MINT, icon=ICONS["rocket"], tag="AFK")
        interval = MOVEMENT_TICK_MS / 1000.0
        last_t = time.time()
        self._last_jump_t = self._last_decision = self._last_speed_change = last_t
        sent = fail = 0
        _next_jump_iv = random.uniform(3.8, 6.2)
        _next_dec_iv = random.uniform(3.0, 5.5)

        while not self._stop_evt.is_set():
            now = time.time()
            dt = now - last_t
            last_t = now
            if dt <= 0.0 or dt > 0.25:
                dt = interval

            if self.phase == "ground":
                if self.state != "jump" and (now - self._last_jump_t) >= _next_jump_iv:
                    self._last_jump_t = self._jump_start_t = now
                    _next_jump_iv = random.uniform(3.8, 6.2)
                    self.state = "jump"
                if self.state != "jump" and (now - self._last_decision) >= _next_dec_iv:
                    self.state = self._pick_state()
                    self.angle = (self.angle + random.uniform(-0.9, 0.9)) % (2.0 * math.pi)
                    self._last_decision = now
                    _next_dec_iv = random.uniform(3.0, 5.5)
                if (now - self._last_speed_change) >= MOVEMENT_UPDATE_SPEED_EVERY:
                    self.speed_mul = random.uniform(MOVEMENT_SPEED_MIN, MOVEMENT_SPEED_MAX)
                    self._last_speed_change = now

            if self.phase != "plane":
                self._step_position(dt)
                if await self._send_udp():
                    sent += 1
                    fail = 0
                else:
                    fail += 1
                    if fail % 30 == 0:
                        log_warn(f"Gửi UDP thất bại x{fail} | uid={self.account_id}")

            sleep_t = max(0.05, interval + random.gauss(0.0, 0.008))
            try:
                await asyncio.wait_for(self._stop_evt.wait(), timeout=sleep_t)
            except asyncio.TimeoutError:
                pass

        log_info(f"Dừng Anti-AFK | uid={self.account_id} đã gửi={sent} gói")

    def start(self) -> None:
        if self._task and not self._task.done():
            return
        self._stop_evt.clear()
        self._clock_stop.clear()
        self._task = asyncio.create_task(self._loop())
        self._clock_task = asyncio.create_task(self._clock_sync_loop())

    async def stop(self) -> None:
        self._stop_evt.set()
        self._clock_stop.set()
        for t in (self._task, self._clock_task):
            if t:
                try:
                    await asyncio.wait_for(t, timeout=3.0)
                except (asyncio.TimeoutError, asyncio.CancelledError):
                    t.cancel()



# ==================== VÒNG ĐỜI TRẬN ĐẤU UDP ====================
_match_counters: Dict[str, int] = {}
_match_counter_lock = asyncio.Lock()
_squad_match_slots: Dict[str, Dict[str, int]] = {}
_squad_slot_lock = asyncio.Lock()
_bot_is_external_invite: Dict[str, bool] = {}


async def _inc_match(uid: str) -> int:
    async with _match_counter_lock:
        _match_counters[uid] = _match_counters.get(uid, 0) + 1
        return _match_counters[uid]


async def _dec_match(uid: str) -> int:
    async with _match_counter_lock:
        if _match_counters.get(uid, 0) > 0:
            _match_counters[uid] -= 1
        return _match_counters.get(uid, 0)


async def _assign_squad_slot(uid_str: str, match_key: str, is_external: bool = False) -> int:
    async with _squad_slot_lock:
        slots = _squad_match_slots.setdefault(match_key, {})
        if uid_str in slots:
            return slots[uid_str]
        taken = set(slots.values())
        if is_external:
            taken.add(1)
            candidates = (2, 3, 4)
        else:
            candidates = (1, 2, 3, 4)
        chosen = next((s for s in candidates if s not in taken), candidates[len(slots) % len(candidates)])
        slots[uid_str] = chosen
        return chosen


async def _release_squad_slot(uid_str: str, match_key: str) -> None:
    async with _squad_slot_lock:
        slots = _squad_match_slots.get(match_key)
        if slots:
            slots.pop(uid_str, None)
            if not slots:
                _squad_match_slots.pop(match_key, None)


async def play_game_session(
    server_ip_port: str, thunder: str, sharma: str, udp_key: str, match_code: str,
    account_id: Any, player_region: str, client_version: str, key: bytes, iv: bytes, match_index: int,
) -> str:
    match_start_time = time.time()
    uid_str = str(account_id)
    match_key = f"{server_ip_port}_{match_code}"
    sock: Optional[socket.socket] = None
    ping_task: Optional[asyncio.Task] = None
    ping_stop = asyncio.Event()
    movement_ctrl: Optional[MovementController] = None
    completed_cleanly = False

    try:
        ip, port_str = server_ip_port.split(":")
        resolved_ip = await resolve_host(ip)
        port = int(port_str)
        loop = asyncio.get_running_loop()

        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            sock.bind(("0.0.0.0", 0))
        except Exception:
            pass
        optimize_udp_socket(sock)
        sock.setblocking(False)

        udp_key_bytes = bytes.fromhex(udp_key)
        hello_hex = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
        await loop.sock_sendto(sock, bytes.fromhex(hello_hex), (resolved_ip, port))

        ack_state = "waiting_for_hello_reply"
        thunder_sent = False
        thunder_sent_time = 0.0
        last_thunder_retry = 0.0
        join_match_received = False
        local_closed = False
        last_activity = time.time()
        send_lock = asyncio.Lock()

        ping_task = asyncio.create_task(keepalive_ping(sock, resolved_ip, port, udp_key_bytes, match_code, ping_stop))
        slot = await _assign_squad_slot(uid_str, match_key, is_external=_bot_is_external_invite.get(uid_str, False))
        movement_ctrl = MovementController(
            account_id=account_id,
            account_region=player_region,
            key=key,
            iv=iv,
            udp_sock=sock,
            udp_server=(resolved_ip, port),
            udp_key_bytes=udp_key_bytes,
            match_code=match_code,
            slot_id=slot,
        )

        async def _send_startup_burst() -> None:
            ru, nr = await layouts_from_mask(match_code)
            await loop.sock_sendto(sock, bytes.fromhex(thunder), (resolved_ip, port))
            await asyncio.sleep(0.25)
            await loop.sock_sendto(sock, await build_packet(0x68, nr, 0, 2, None, 1, b"\x01\x00", udp_key_bytes), (resolved_ip, port))
            await asyncio.sleep(0.35)
            await loop.sock_sendto(sock, bytes.fromhex(sharma), (resolved_ip, port))
            await asyncio.sleep(0.25)
            await loop.sock_sendto(sock, await build_packet(0x60, ru, 2, 899, 2, 1, b"", udp_key_bytes), (resolved_ip, port))
            await loop.sock_sendto(sock, await build_packet(0x60, ru, 2, 899, 8, 1, b"", udp_key_bytes), (resolved_ip, port))

        async def _trigger_startup() -> None:
            nonlocal ack_state, thunder_sent, thunder_sent_time, last_thunder_retry
            if thunder_sent:
                return
            async with send_lock:
                if thunder_sent:
                    return
                try:
                    await _send_startup_burst()
                    thunder_sent = True
                    thunder_sent_time = last_thunder_retry = time.time()
                    ack_state = "thunder_sharma_sent"
                    log_event(f"Trận #{match_index} đang vào game | UID: {uid_str}", color=PX.LIME, icon=ICONS["flame"], tag="MATCH")
                    movement_ctrl.start()
                except Exception as exc:
                    log_warn(f"Trận #{match_index} startup burst lỗi: {exc}")

        while not local_closed:
            now_t = time.time()
            if now_t - match_start_time > MAX_MATCH_DURATION:
                completed_cleanly = True
                break
            if ack_state == "thunder_sharma_sent":
                if (now_t - last_activity) > MATCH_IDLE_TIMEOUT:
                    completed_cleanly = movement_ctrl.has_real_coords
                    break
                if not movement_ctrl.has_real_coords:
                    if (now_t - match_start_time) > 65.0:
                        log_warn(f"Trận #{match_index} không nhận sync server sau 65s | UID: {uid_str}")
                        completed_cleanly = False
                        break
                    if thunder_sent_time > 0 and (now_t - last_thunder_retry) >= 8.0:
                        last_thunder_retry = now_t
                        try:
                            ru, _ = await layouts_from_mask(match_code)
                            await loop.sock_sendto(sock, await build_packet(0x60, ru, 2, 899, 2, 1, b"", udp_key_bytes), (resolved_ip, port))
                            await loop.sock_sendto(sock, await build_packet(0x60, ru, 2, 899, 8, 1, b"", udp_key_bytes), (resolved_ip, port))
                        except Exception:
                            pass

            try:
                response, server_addr = await asyncio.wait_for(loop.sock_recvfrom(sock, 65535), timeout=2.0)
                if not response:
                    continue
                last_activity = time.time()
                frame = await decode_packet(response, udp_key_bytes, match_code)
                if not frame:
                    continue
                movement_ctrl.handle_server_frame(frame)
                ptype = await classify_frame(frame)

                if frame["cmd"] == 103:
                    log_event(f"Kết thúc trận #{match_index} | UID: {uid_str}", color=PX.MAGENTA, icon=ICONS["star"], tag="MATCH")
                    completed_cleanly = True
                    local_closed = True
                    continue
                if frame["cmd"] == 101:
                    _, nr = await layouts_from_mask(match_code)
                    await loop.sock_sendto(sock, await build_packet(0x68, nr, 0, 2, None, 1, b"\x01\x00", udp_key_bytes), server_addr)
                    continue

                if ptype == "HELLO" and ack_state == "waiting_for_hello_reply":
                    _, reply = await build_reply_packet(frame, udp_key_bytes, match_code, ack_style="short")
                    if reply:
                        await loop.sock_sendto(sock, reply, server_addr)
                    ack_state = "ack_sent_waiting"
                elif ptype == "ACK":
                    if ack_state == "waiting_for_hello_reply":
                        _, reply = await build_reply_packet(frame, udp_key_bytes, match_code)
                        if reply:
                            await loop.sock_sendto(sock, reply, server_addr)
                        ack_state = "ready_to_send_thunder"
                    elif ack_state == "ack_sent_waiting":
                        ack_state = "ready_to_send_thunder"
                    else:
                        _, reply = await build_reply_packet(frame, udp_key_bytes, match_code)
                        if reply:
                            await loop.sock_sendto(sock, reply, server_addr)
                elif ptype == "PING":
                    _, reply = await build_reply_packet(frame, udp_key_bytes, match_code)
                    if reply:
                        await loop.sock_sendto(sock, reply, server_addr)
                elif ptype == "JOIN_MATCH" and not join_match_received:
                    _, reply = await build_reply_packet(frame, udp_key_bytes, match_code)
                    if reply:
                        await loop.sock_sendto(sock, reply, server_addr)
                    join_match_received = True
            except asyncio.TimeoutError:
                if ack_state in ("ready_to_send_thunder", "ack_sent_waiting") and not thunder_sent:
                    await _trigger_startup()
                elif ack_state == "waiting_for_hello_reply":
                    if (time.time() - last_activity) > 5.0:
                        try:
                            pkt = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
                            await loop.sock_sendto(sock, bytes.fromhex(pkt), (resolved_ip, port))
                        except Exception:
                            pass
                        last_activity = time.time()
                    if (time.time() - match_start_time) > 25.0:
                        log_warn(f"Trận #{match_index} handshake timeout | UID: {uid_str}")
                        break
                elif ack_state == "thunder_sharma_sent" and (time.time() - last_activity) > MATCH_IDLE_TIMEOUT:
                    completed_cleanly = movement_ctrl.has_real_coords
                    break
            except (BlockingIOError, OSError):
                await asyncio.sleep(0.5)
            except Exception:
                await asyncio.sleep(0.5)

            if ack_state == "ready_to_send_thunder" and not thunder_sent:
                await _trigger_startup()

        return f"match #{match_index} finished"
    except Exception as exc:
        log_err(f"Trận #{match_index} lỗi: {exc}")
        return f"match #{match_index} error"
    finally:
        await _release_squad_slot(uid_str, match_key)
        _bot_is_external_invite.pop(uid_str, None)
        if movement_ctrl:
            await movement_ctrl.stop()
        if completed_cleanly:
            bot_state.increment_match(uid_str)
            log_event(f"Hoàn thành trận #{match_index} | UID: {uid_str}", color=PX.GOLD, icon=ICONS["crown"], tag="MATCH")

            async def _delayed_profile_sync(uid_target: str) -> None:
                for delay in (5.0, 8.0, 12.0):
                    await asyncio.sleep(delay)
                    await refresh_account_profile(uid_target)

            asyncio.create_task(_delayed_profile_sync(uid_str))
        ping_stop.set()
        if ping_task:
            ping_task.cancel()
            try:
                await ping_task
            except asyncio.CancelledError:
                pass
        if sock:
            try:
                sock.close()
            except Exception:
                pass
        remaining = await _dec_match(uid_str)
        bot_state.update_status(uid_str, "ONLINE" if remaining == 0 else "IN_MATCH", remaining)


# ==================== WORKER TCP CHÍNH & PHỤ ====================
async def functional_worker(
    addrs: str, starter_packet: str, account_region: str, client_version: str,
    key: bytes, iv: bytes, account_id: Any = "", account_data: Optional[dict] = None,
) -> None:
    ip, port_str = addrs.split(":")
    port = int(port_str)
    uid_str = str(account_id)
    play_matches: List[asyncio.Task] = []
    last_start_time = 0.0
    reconnects = 0
    no_response_count = 0

    current_token = starter_packet
    current_key = key
    current_iv = iv
    current_account_data = account_data
    writer_holder: Dict[str, Optional[asyncio.StreamWriter]] = {"w": None}
    team_active = {"flag": True}
    match_played = {"flag": False}

    async def _handle_social_packet(raw_bytes: bytes, tag: str = "MAIN") -> None:
        if not AUTO_ACCEPT_FRIEND_REQUEST or not current_account_data or not DEV_UID:
            return
        hex_data = raw_bytes.hex()
        candidates = []
        for off in [5, 6, 10, 8, 12, 14, 4, 16, 0]:
            if off >= len(hex_data):
                continue
            try:
                inner = bytes.fromhex(hex_data[off:])
                dec = decode_protobuf_dict(inner)
                if not dec:
                    d2 = decode_protobuf_2(inner)
                    dec = {str(k): {"data": v} for k, v in d2.items()} if d2 else {}
                if dec:
                    candidates.append(dec)
            except Exception:
                pass
        if not candidates:
            return
        best = max(candidates, key=lambda d: len(d) - (100 if ("0" in d or 0 in d) else 0) + (6 if "5" in d else 0))
        f5 = extract_field_value(best, 5)
        target_uid = None
        if isinstance(f5, dict):
            for fk in (1, 2, 3, 4, 6):
                cand = extract_field_value(f5, fk)
                if cand and str(cand).isdigit() and 6 <= len(str(cand)) <= 15:
                    target_uid = str(cand)
                    break
        own_id = str(current_account_data.get("account_id", ""))
        if not target_uid or target_uid == own_id:
            return
        jwt_l = current_account_data.get("token")
        srv_l = current_account_data.get("server_url")
        rel_l = current_account_data.get("release_version")
        if not (jwt_l and srv_l and rel_l and own_id):
            return
        try:
            payload = bytes.fromhex(encrypt_aes(create_proto({"1": int(DEV_UID), "2": int(own_id)}).hex()))
            headers = {
                "authorization": f"Bearer {jwt_l}",
                "host": srv_l.replace("https://", "").replace("http://", "").split("/")[0],
                "x-ga": "v1 1",
                "content-type": "application/x-www-form-urlencoded",
                "releaseversion": f"{rel_l}",
                "user-agent": "UnityPlayer/2022.3.47f1",
                "accept": "*/*",
                "x-unity-version": "2022.3.47f1",
            }
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=8)) as session:
                async with session.post(f"{srv_l.rstrip('/')}/ConfirmFriendRequest", headers=headers, data=payload, ssl=_insecure_ssl_context()) as resp:
                    if resp.status == 200 and len(await resp.read()) > 0:
                        log_ok(f"FRIEND-{tag} Đã chấp nhận lời mời {target_uid}")
        except Exception:
            pass

    async def _send_writer(pkt: bytes) -> bool:
        w = writer_holder["w"]
        if not w or w.is_closing():
            return False
        w.write(pkt)
        await w.drain()
        return True

    async def _team_coordinator() -> None:
        try:
            while team_active["flag"] and not match_played["flag"]:
                if bot_state.is_paused(uid_str):
                    return
                wait_t0 = time.time()
                while team_active["flag"] and not match_played["flag"]:
                    async with _team_state["lock"]:
                        n = len(_team_state["peers"])
                    in_match_cnt = sum(1 for a in bot_state.accounts.values() if "IN_MATCH" in str(a.get("status", "")).upper())
                    expected_n = max(2, max(bot_state.expected_workers, len(set(bot_state.account_workers.values()))) - in_match_cnt)
                    if n >= expected_n or (n >= 2 and (time.time() - wait_t0) >= TEAM_READY_DELAY + 3.0) or ((time.time() - wait_t0) >= 15.0 and n >= 2):
                        break
                    if bot_state.is_paused(uid_str):
                        return
                    await asyncio.sleep(0.4)

                await asyncio.sleep(1.2)
                async with _team_state["lock"]:
                    now_ts = time.time()
                    valid_locked = []
                    for lsq in _team_state.get("locked_squads", []):
                        m_list = [u for u in lsq.get("members", []) if u in _team_state["peers"]]
                        if len(m_list) >= 2 and m_list[0] == lsq["members"][0] and (now_ts - lsq.get("created_at", 0.0)) < 58.0:
                            valid_locked.append({"members": m_list, "created_at": lsq["created_at"]})
                    locked_uids = {u for lsq in valid_locked for u in lsq["members"]}
                    unassigned = {u: p for u, p in _team_state["peers"].items() if u not in locked_uids}
                    if len(unassigned) >= 2:
                        for sq in _compute_smart_squads(unassigned):
                            if len(sq) >= 2:
                                valid_locked.append({"members": list(sq), "created_at": now_ts})
                    _team_state["locked_squads"] = valid_locked
                    squads = [list(lsq["members"]) for lsq in valid_locked]
                    _team_state["squads"] = squads
                    _team_state["uid_to_leader"].clear()
                    _team_state["uid_to_squad_idx"].clear()

                    my_squad: Optional[List[str]] = None
                    my_squad_idx = 0
                    for s_idx, sq in enumerate(squads, start=1):
                        lead_u = sq[0]
                        for u in sq:
                            _team_state["uid_to_leader"][u] = lead_u
                            _team_state["uid_to_squad_idx"][u] = s_idx
                        if uid_str in sq:
                            my_squad = list(sq)
                            my_squad_idx = s_idx
                    if squads:
                        _team_state["leader_uid"] = squads[0][0]

                    sig = tuple(tuple(sq) for sq in squads)
                    if _team_state.get("partition_sig") != sig and squads:
                        _team_state["partition_sig"] = sig
                        detail = " | ".join(f"Squad #{i} ({len(sq)}P: {','.join(sq)})" for i, sq in enumerate(squads, start=1))
                        log_event(f"CHIA TEAM THÔNG MINH | {detail}", color=PX.GOLD, icon=ICONS["crown"], tag="TEAM")
                    peers_snapshot = dict(_team_state["peers"])

                if not my_squad or len(my_squad) < 2:
                    await asyncio.sleep(4.0)
                    continue

                my_leader = my_squad[0]
                own_id_num = int(current_account_data["account_id"]) if (current_account_data and str(current_account_data.get("account_id", "")).isdigit()) else (int(uid_str) if uid_str.isdigit() else 0)

                if my_leader != uid_str:
                    member_t0 = time.time()
                    while team_active["flag"] and not match_played["flag"] and (time.time() - member_t0) < 62.0:
                        await asyncio.sleep(1.0)
                        if bot_state.is_paused(uid_str):
                            return
                        async with _team_state["lock"]:
                            cur_lead = _team_state["uid_to_leader"].get(uid_str)
                            lead_online = my_leader in _team_state["peers"]
                        if not lead_online or (cur_lead and cur_lead != my_leader):
                            break
                    if team_active["flag"] and not match_played["flag"]:
                        try:
                            await _send_writer(build_leave_team_packet(own_id_num, current_key, current_iv, region=account_region))
                        except Exception:
                            pass
                        await asyncio.sleep(0.5)
                    continue

                await asyncio.sleep((my_squad_idx - 1) * 0.45)
                log_event(f"Squad #{my_squad_idx} ({len(my_squad)}P) Leader {uid_str} tạo phòng ({account_region})", color=PX.GOLD, icon=ICONS["crown"], tag="TEAM")
                try:
                    await _send_writer(build_leave_team_packet(own_id_num, current_key, current_iv, region=account_region))
                    await asyncio.sleep(0.35)
                    await _send_writer(build_create_team_packet(current_key, current_iv, region=account_region, game_version=client_version, team_size=len(my_squad)))
                except Exception as exc:
                    log_err(f"TEAM tạo phòng lỗi: {exc}")

                await asyncio.sleep(1.0)
                for idx_m, peer_uid in enumerate(my_squad[1:], start=2):
                    peer_acc_id = extract_field_value(peers_snapshot.get(peer_uid, {}).get("data"), "account_id") or peer_uid
                    try:
                        await _send_writer(build_invite_team_packet(int(peer_acc_id), current_key, current_iv, region=account_region))
                        log_info(f"TEAM [Squad #{my_squad_idx}] Mời bot{idx_m} → {peer_acc_id}")
                    except Exception as exc:
                        log_warn(f"TEAM mời lỗi: {exc}")
                    await asyncio.sleep(0.45)

                await asyncio.sleep(TEAM_INVITE_WAIT + 1.2)
                log_event(f"Squad #{my_squad_idx} sẵn sàng → bắt đầu tìm trận", color=PX.EMERALD, icon=ICONS["rocket"], tag="TEAM")
                bot_state.update_status(uid_str, "SEARCHING", 0)

                # Gửi ready trước khi start match
                try:
                    await _send_writer(build_ready_packet(own_id_num, current_key, current_iv, region=account_region))
                    await asyncio.sleep(0.3)
                except Exception as exc:
                    log_warn(f"TEAM ready lỗi: {exc}")

                # Reset in_queue cho lần tìm trận mới
                async with _team_state["lock"]:
                    _team_state["in_queue"] = False

                leader_t0 = time.time()
                last_sm_time = 0.0
                while team_active["flag"] and not match_played["flag"] and (time.time() - leader_t0) < 180.0:
                    if bot_state.is_paused(uid_str):
                        break
                    async with _team_state["lock"]:
                        if _team_state["uid_to_leader"].get(uid_str) != uid_str:
                            break
                    if not _team_state.get("in_queue") and (time.time() - last_sm_time) >= 7.0:
                        last_sm_time = time.time()
                        try:
                            await _send_writer(build_start_team_match_packet(own_id_num, current_key, current_iv, region=account_region))
                            log_event(f"TEAM [Squad #{my_squad_idx}] gửi start_match", color=PX.EMERALD, icon=ICONS["bolt"], tag="TEAM")
                        except Exception as exc:
                            log_warn(f"TEAM start match lỗi: {exc}")
                    await asyncio.sleep(1.5)

                if team_active["flag"] and not match_played["flag"]:
                    async with _team_state["lock"]:
                        _team_state["locked_squads"] = [
                            lsq for lsq in _team_state.get("locked_squads", [])
                            if lsq.get("members", [None])[0] != uid_str
                        ]
                    try:
                        await _send_writer(build_leave_team_packet(own_id_num, current_key, current_iv, region=account_region))
                    except Exception:
                        pass
                    await asyncio.sleep(0.5)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            log_err(f"TEAM coordinator lỗi: {exc}")

    async def _member_trigger() -> None:
        try:
            await asyncio.sleep(TEAM_READY_DELAY + 6.0)
            async with _team_state["lock"]:
                if _team_state["uid_to_leader"].get(uid_str) == uid_str:
                    return
            bot_state.update_status(uid_str, "SEARCHING", 0)
        except asyncio.CancelledError:
            raise
        except Exception:
            pass

    while True:
        while bot_state.is_paused(uid_str):
            bot_state.update_status(uid_str, "PAUSED", 0)
            await asyncio.sleep(1.0)

        writer: Optional[asyncio.StreamWriter] = None
        gateway_ka_task: Optional[asyncio.Task] = None
        team_coord_task: Optional[asyncio.Task] = None
        member_task: Optional[asyncio.Task] = None

        try:
            if current_account_data:
                fresh = await token_manager.ensure_valid_account(
                    current_account_data,
                    region_override=account_region,
                    force_refresh=False,
                )
                if not fresh:
                    raise RuntimeError("Không thể làm mới JWT token")
                current_account_data = fresh
                current_key = fresh["aes_ak"]
                current_iv = fresh["iv_i"]
                current_token = await build_tcp_startup_packet(
                    fresh["account_id"], fresh["token"], fresh["server_time"],
                    current_key, current_iv, region=fresh.get("region", account_region), typ="OnLine",
                )

            resolved_ip = await resolve_host(ip)
            reader, writer = await asyncio.open_connection(resolved_ip, port)
            bot_state.register_writer(uid_str, writer)
            writer_holder["w"] = writer
            raw_sock = writer.get_extra_info("socket")
            if raw_sock:
                optimize_tcp_socket(raw_sock)

            writer.write(bytes.fromhex(current_token))
            await writer.drain()
            try:
                init_ka = await build_keepalive_packet(account_region)
                if init_ka and not writer.is_closing():
                    writer.write(init_ka)
                    await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception:
                pass

            async def _tcp_keepalive() -> None:
                ka_bytes = await build_keepalive_packet(account_region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka_bytes)
                            await writer.drain()
                    except Exception:
                        break

            gateway_ka_task = asyncio.create_task(_tcp_keepalive())
            log_event(f"TCP Connected | UID: {uid_str} | region={account_region}", color=PX.MINT, icon=ICONS["check"], tag="TCP")

            try:
                own_id_init = extract_field_value(current_account_data, "account_id", uid_str)
                await _send_writer(build_leave_team_packet(int(own_id_init), current_key, current_iv, region=account_region))
            except Exception:
                pass

            reconnects = 0
            async with _team_state["lock"]:
                _team_state["peers"][uid_str] = {
                    "writer": writer,
                    "data": current_account_data,
                    "key": current_key,
                    "iv": current_iv,
                }
                if _team_state["leader_uid"] is None:
                    _team_state["leader_uid"] = uid_str

            await _mark_team_joined(uid_str)

            async def _solo_search() -> None:
                bot_state.update_status(uid_str, "SEARCHING", 0)
                await asyncio.sleep(random.uniform(0.2, 0.4))
                try:
                    own_id_s = extract_field_value(current_account_data, "account_id", uid_str)
                    await _send_writer(build_ready_packet(int(own_id_s), current_key, current_iv, region=account_region))
                except Exception:
                    pass
                await asyncio.sleep(1.0)
                await send_solo_match_packet(account_region, client_version, writer, current_key, current_iv)

            if not match_played["flag"]:
                if TEAM_MODE:
                    team_coord_task = asyncio.create_task(_team_coordinator())
                    member_task = asyncio.create_task(_member_trigger())
                else:
                    await _solo_search()

            accepted_groups: set = set()
            tcp_buf = bytearray()

            while True:
                play_matches[:] = [m for m in play_matches if not m.done()]
                if bot_state.is_paused(uid_str):
                    break

                # Kiểm tra định kỳ xem JWT có sắp chạm mốc hết hạn 8h không
                if current_account_data and is_jwt_expiring_soon(current_account_data):
                    log_warn(f"[TOKEN] JWT của {uid_str} sắp hết hạn → kết nối lại để làm mới token")
                    raise RuntimeError("JWT sắp hết hạn")

                if match_played["flag"]:
                    try:
                        chunk = await asyncio.wait_for(reader.read(8192), timeout=1.0)
                    except asyncio.TimeoutError:
                        continue
                    if not chunk:
                        raise ConnectionError("Mất kết nối TCP")
                    if len(chunk) > 20 and chunk.hex().startswith("0600"):
                        await _handle_social_packet(chunk, tag="IDLE")
                    continue

                now_loop = asyncio.get_running_loop().time()
                if not TEAM_MODE and not play_matches and (now_loop - last_start_time >= NEW_MATCH_DELAY):
                    await _solo_search()
                    last_start_time = now_loop

                frame_bytes: Optional[bytes] = None
                while len(tcp_buf) >= 5:
                    if tcp_buf[1] == 0x00:
                        plen = int.from_bytes(tcp_buf[2:5], "big")
                        if 0 <= plen <= 131072:
                            if len(tcp_buf) < 5 + plen:
                                break
                            frame_bytes = bytes(tcp_buf[:5 + plen])
                            del tcp_buf[:5 + plen]
                            break
                    frame_bytes = bytes(tcp_buf)
                    tcp_buf.clear()
                    break

                if frame_bytes is None:
                    try:
                        chunk = await asyncio.wait_for(reader.read(8192), timeout=0.5)
                    except asyncio.TimeoutError:
                        continue
                    if not chunk:
                        raise ConnectionError("Mất kết nối TCP")
                    tcp_buf.extend(chunk)
                    continue

                hex_data = frame_bytes.hex()
                pkt_len = len(frame_bytes)

                if hex_data.startswith("0600") and pkt_len > 20:
                    await _handle_social_packet(frame_bytes, tag="MAIN")
                    continue

                if hex_data.startswith("0500") and pkt_len > 10:
                    try:
                        inner = bytes.fromhex(hex_data[10:])
                        dec2 = decode_protobuf_2(inner) or {}
                        dec = decode_protobuf_dict(inner) or {str(k): {"data": v} for k, v in dec2.items()}
                        d2 = extract_field_value(dec, 2, dec2.get(2))
                        d3 = extract_field_value(dec, 3, dec2.get(3))
                        d4 = extract_field_value(dec, 4, dec2.get(4))
                        f5 = extract_field_value(dec, 5, dec)
                        f5_2 = dec2.get(5) if isinstance(dec2.get(5), dict) else {}

                        if d4 == 1 and isinstance(f5_2.get(6), dict):
                            honor_val = f5_2[6].get(64)
                            if isinstance(honor_val, int):
                                if honor_val < 60:
                                    _restricted_57_uids.add(uid_str)
                                else:
                                    _restricted_57_uids.discard(uid_str)

                        def _f5_get(k_id: int) -> Any:
                            if k_id in f5_2 and not isinstance(f5_2[k_id], dict):
                                return f5_2[k_id]
                            return extract_field_value(f5, k_id)

                        for fk in (11, 5, 1, 3):
                            cand_tc = _f5_get(fk)
                            if cand_tc and str(cand_tc).isdigit() and len(str(cand_tc)) == 7:
                                async with _team_state["lock"]:
                                    s_idx = _team_state["uid_to_squad_idx"].get(uid_str, 1)
                                    _team_state["team_codes"][s_idx] = str(cand_tc)
                                    _team_state["team_code"] = str(cand_tc)
                                break

                        group_id = _f5_get(8)
                        if not (isinstance(group_id, str) and 20 <= len(group_id) <= 40):
                            group_id = None

                        own_acc = str(extract_field_value(current_account_data, "account_id", ""))
                        inviter = None
                        for fk in (1, 2, 3, 4, 6, 7, 13, 15, 20):
                            cand_inv = _f5_get(fk)
                            if cand_inv and str(cand_inv).isdigit() and 8 <= len(str(cand_inv)) <= 15:
                                if str(cand_inv) not in (uid_str, own_acc):
                                    inviter = cand_inv
                                    break

                        if d4 == 3 and inviter and group_id:
                            inviter_s = str(inviter)
                            is_ext = (inviter_s not in bot_state.accounts) and (inviter_s not in bot_state.account_workers)
                            assigned_leader = _team_state["uid_to_leader"].get(uid_str)
                            if is_ext or (assigned_leader != uid_str and (assigned_leader is None or inviter_s == str(assigned_leader))):
                                grp_key = (inviter_s, str(group_id))
                                if grp_key not in accepted_groups:
                                    accepted_groups.add(grp_key)
                                    _bot_is_external_invite[uid_str] = is_ext
                                    await _send_writer(build_leave_team_packet(int(own_acc or uid_str), current_key, current_iv, region=account_region))
                                    await asyncio.sleep(0.25)
                                    await _send_writer(build_accept_invite_packet(int(inviter), group_id, current_key, current_iv, region=account_region, game_version=client_version))

                        if d2 == 5 and d4 == 10:
                            _team_state["in_queue"] = True
                            log_event(f"TEAM Bắt đầu ghép trận | UID: {uid_str}", color=PX.EMERALD, icon=ICONS["bolt"], tag="TEAM")
                        elif d2 == 5 and d3:
                            _team_state["in_queue"] = False
                            log_warn(f"TEAM 0500 status={d3} | UID: {uid_str}")
                    except Exception as exc:
                        log_warn(f"TEAM 0500 lỗi parse: {exc}")
                    continue

                if hex_data.startswith("0300") and 10 < pkt_len < 60:
                    log_event(f"Đang trong hàng chờ ghép trận | UID: {uid_str}", color=PX.EMERALD, icon=ICONS["bolt"], tag="MATCH")
                    continue

                if hex_data.startswith("0300") and pkt_len >= 300:
                    match_played["flag"] = True
                    log_event(f"Tìm thấy trận | UID: {uid_str} | region={account_region}", color=PX.AMBER, icon=ICONS["target"], tag="MATCH")
                    async with _team_state["lock"]:
                        _team_state["peers"].pop(uid_str, None)
                        _team_state["uid_to_leader"].pop(uid_str, None)
                        _team_state["uid_to_squad_idx"].pop(uid_str, None)
                        _team_state["locked_squads"] = [
                            lsq for lsq in _team_state.get("locked_squads", [])
                            if uid_str not in lsq.get("members", [])
                        ]
                        if _team_state["leader_uid"] == uid_str:
                            _team_state["leader_uid"] = None
                            _team_state["team_code"] = None

                    await _mark_match_found(uid_str)
                    await _clear_team_joined(uid_str)
                    for tk in (team_coord_task, member_task):
                        if tk and not tk.done():
                            tk.cancel()
                    team_coord_task = member_task = None
                    team_active["flag"] = False
                    accepted_groups.clear()

                    try:
                        res = json.loads(await decode_protobuf_async(hex_data[10:]))
                        rf5 = res.get("5", {}).get("data", {}) if isinstance(res.get("5"), dict) else {}
                        server_ip_port = rf5.get("2", {}).get("data")
                        udp_key = rf5.get("3", {}).get("data")
                        token_match = rf5.get("4", {}).get("data")
                        match_code_raw = rf5.get("42", {}).get("data") or res.get("42", {}).get("data")
                        match_acc_id = res.get("1", {}).get("data")
                        block_val = rf5.get("1", {}).get("data", 0)
                        effective_acc_id = match_acc_id or account_id or "BOT"

                        if token_match and udp_key and match_code_raw and server_ip_port:
                            m_code = (
                                match_code_raw.decode("utf-8", errors="ignore").strip()
                                if isinstance(match_code_raw, (bytes, bytearray))
                                else str(match_code_raw).strip()
                            )
                            acc_tok = current_account_data.get("access_token", "") if current_account_data else ""
                            m_id_raw = rf5.get("7")
                            m_id = (m_id_raw.get("data") if isinstance(m_id_raw, dict) else m_id_raw) or DEFAULT_GAME_MODE_ID
                            map_id_raw = rf5.get("6")
                            map_id = (map_id_raw.get("data") if isinstance(map_id_raw, dict) else map_id_raw) or DEFAULT_GAME_MAP_ID
                            thunder, sharma = await build_match_startup_packets(
                                token_match, udp_key, m_code, effective_acc_id, block_val,
                                server_ip=server_ip_port, region=account_region,
                                client_version=client_version, access_token=acc_tok,
                                mode_id=m_id, map_id=map_id,
                            )
                            match_idx = await _inc_match(uid_str)
                            bot_state.increment_match_started()
                            bot_state.update_status(uid_str, "IN_MATCH (TEAM)", 1)

                            new_match = asyncio.create_task(play_game_session(
                                server_ip_port, thunder, sharma, udp_key, m_code,
                                effective_acc_id, account_region or "VN", client_version,
                                current_key, current_iv, match_index=match_idx,
                            ))
                            play_matches.append(new_match)

                            async def _drain_tcp() -> None:
                                while not new_match.done():
                                    try:
                                        dg = await asyncio.wait_for(reader.read(4096), timeout=1.0)
                                        if not dg:
                                            break
                                        if len(dg) > 20 and dg.hex().startswith("0600"):
                                            await _handle_social_packet(dg, tag="DRAIN")
                                    except asyncio.TimeoutError:
                                        continue
                                    except Exception:
                                        break

                            drain_task = asyncio.create_task(_drain_tcp())
                            try:
                                await new_match
                            finally:
                                drain_task.cancel()
                                try:
                                    await drain_task
                                except asyncio.CancelledError:
                                    pass

                            play_matches[:] = [m for m in play_matches if not m.done()]
                            match_played["flag"] = False
                            team_active["flag"] = True
                            no_response_count = 0
                            accepted_groups.clear()
                            log_event(f"IDLE {uid_str} xong trận — sẵn sàng vòng mới", color=PX.SLATE, icon=ICONS["dot"], tag="MATCH")

                            # Re-register vào peers — TCP vẫn còn sống, không cần reconnect
                            async with _team_state["lock"]:
                                if uid_str not in _team_state["peers"] and writer and not writer.is_closing():
                                    _team_state["peers"][uid_str] = {
                                        "writer": writer,
                                        "data": current_account_data,
                                        "key": current_key,
                                        "iv": current_iv,
                                    }
                                if _team_state["leader_uid"] is None:
                                    _team_state["leader_uid"] = uid_str
                            await _mark_team_joined(uid_str)

                            # Spawn coordinator/solo search ngay — không delay thêm
                            if TEAM_MODE and (team_coord_task is None or team_coord_task.done()):
                                last_start_time = asyncio.get_running_loop().time()
                                team_coord_task = asyncio.create_task(_team_coordinator())
                                member_task = asyncio.create_task(_member_trigger())
                            elif not TEAM_MODE:
                                await _solo_search()
                                last_start_time = asyncio.get_running_loop().time()
                    except Exception as exc:
                        log_warn(f"MATCH lỗi xử lý gói: {exc}")
                        continue
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            msg_err = str(exc)
            if "JWT" in msg_err or "token" in msg_err.lower():
                if current_account_data:
                    refreshed = await token_manager.ensure_valid_account(
                        current_account_data,
                        region_override=account_region,
                        force_refresh=True,
                    )
                    if refreshed:
                        current_account_data = refreshed
                        current_key = refreshed["aes_ak"]
                        current_iv = refreshed["iv_i"]
                        current_token = await build_tcp_startup_packet(
                            refreshed["account_id"], refreshed["token"], refreshed["server_time"],
                            current_key, current_iv, region=refreshed.get("region", account_region), typ="OnLine",
                        )
                await asyncio.sleep(2.0)
                continue

            reconnects += 1
            if reconnects > 5 and current_account_data:
                refreshed = await token_manager.ensure_valid_account(
                    current_account_data,
                    region_override=account_region,
                    force_refresh=True,
                )
                if refreshed:
                    current_account_data = refreshed
                    current_key = refreshed["aes_ak"]
                    current_iv = refreshed["iv_i"]
                    current_token = await build_tcp_startup_packet(
                        refreshed["account_id"], refreshed["token"], refreshed["server_time"],
                        current_key, current_iv, region=refreshed.get("region", account_region), typ="OnLine",
                    )
                reconnects = 0
            log_warn(f"{uid_str} Reconnect #{reconnects}: {exc}")
            await asyncio.sleep(min(reconnects * 0.5, 2.0))
        finally:
            team_active["flag"] = False
            async with _team_state["lock"]:
                _team_state["peers"].pop(uid_str, None)
                _team_state["uid_to_leader"].pop(uid_str, None)
                _team_state["uid_to_squad_idx"].pop(uid_str, None)
                if _team_state["leader_uid"] == uid_str:
                    _team_state["leader_uid"] = None
                    _team_state["team_code"] = None
            await _clear_team_joined(uid_str)
            for tk in (team_coord_task, member_task):
                if tk and not tk.done():
                    tk.cancel()
                    try:
                        await tk
                    except asyncio.CancelledError:
                        pass
            if gateway_ka_task:
                gateway_ka_task.cancel()
            if writer:
                bot_state.unregister_writer(uid_str, writer)
                await safe_close_writer(writer)
            if not match_played["flag"]:
                team_active["flag"] = True


async def informational_worker(
    addrs: str, starter_packet: str, region: str = "ID",
    account_id: Any = "", account_data: Optional[dict] = None, max_reconnects: int = 3,
) -> None:
    uid_str = str(account_id)
    ip, port_str = addrs.split(":")
    port = int(port_str)
    reconnects = 0
    cur_pkt = starter_packet
    cur_data = account_data

    while True:
        while uid_str and bot_state.is_paused(uid_str):
            await asyncio.sleep(1.0)
        writer: Optional[asyncio.StreamWriter] = None
        ping_task: Optional[asyncio.Task] = None
        try:
            if cur_data:
                fresh = await token_manager.ensure_valid_account(cur_data, region_override=region, force_refresh=False)
                if fresh:
                    cur_data = fresh
                    cur_pkt = await build_tcp_startup_packet(
                        fresh["account_id"], fresh["token"], fresh["server_time"],
                        fresh["aes_ak"], fresh["iv_i"], region=fresh.get("region", region), typ="ChaT",
                    )

            resolved_ip = await resolve_host(ip)
            reader, writer = await asyncio.open_connection(resolved_ip, port)
            if uid_str:
                bot_state.register_writer(uid_str, writer)
            raw_sock = writer.get_extra_info("socket")
            if raw_sock:
                optimize_tcp_socket(raw_sock)

            writer.write(bytes.fromhex(cur_pkt))
            await writer.drain()
            reconnects = 0

            try:
                init_ka = await build_keepalive_packet(region)
                if init_ka and not writer.is_closing():
                    writer.write(init_ka)
                    await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception:
                pass

            async def _info_ka() -> None:
                ka = await build_keepalive_packet(region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka)
                            await writer.drain()
                    except Exception:
                        break

            ping_task = asyncio.create_task(_info_ka())
            log_event(f"INFO Connected | UID: {uid_str} | region={region}", color=PX.SKY, icon=ICONS["dot"], tag="CHAT")

            while True:
                if uid_str and bot_state.is_paused(uid_str):
                    if ping_task:
                        ping_task.cancel()
                    bot_state.unregister_writer(uid_str, writer)
                    await safe_close_writer(writer)
                    writer = None
                    while bot_state.is_paused(uid_str):
                        await asyncio.sleep(1.0)
                    break
                try:
                    data = await asyncio.wait_for(reader.read(8192), timeout=1.0)
                except asyncio.TimeoutError:
                    continue
                if not data:
                    raise ConnectionError("Chat socket closed")
        except asyncio.CancelledError:
            if ping_task:
                ping_task.cancel()
            if uid_str and writer:
                bot_state.unregister_writer(uid_str, writer)
            await safe_close_writer(writer)
            raise
        except Exception:
            if ping_task:
                ping_task.cancel()
            if uid_str and writer:
                bot_state.unregister_writer(uid_str, writer)
            await safe_close_writer(writer)
            reconnects += 1
            await asyncio.sleep(3 if reconnects > max_reconnects else 1)
            if reconnects > max_reconnects:
                reconnects = 0


# ==================== TÀI KHOẢN, ĐĂNG NHẬP & TẠO BOT ====================
def register_account_credentials(ad: dict) -> None:
    try:
        bot_state.account_credentials[str(ad["account_id"])] = ad
        if ad.get("auth_uid"):
            bot_state.account_credentials[str(ad["auth_uid"])] = ad
    except Exception:
        pass


async def refresh_account_profile(ad_or_uid: Any) -> None:
    try:
        if isinstance(ad_or_uid, str):
            ad = bot_state.account_credentials.get(ad_or_uid)
        elif isinstance(ad_or_uid, dict):
            ad = ad_or_uid
        else:
            return
        if not ad:
            return
        ad = await token_manager.ensure_valid_account(ad, force_refresh=False) or ad
        token, acc_id, srv, rel = ad.get("token"), ad.get("account_id"), ad.get("server_url"), ad.get("release_version")
        if not (token and acc_id and srv and rel):
            return
        profile = await fetch_player_profile(int(acc_id), token, srv, rel)
        if not profile:
            return
        pd = profile.get(1, {}) if isinstance(profile.get(1), dict) else {}
        exp_raw = pd.get(7)
        if exp_raw is None:
            return
        exp_val = int(exp_raw)
        lvl_val = int(pd.get(6) or 1)
        nick = pd.get(3)
        aid = str(acc_id)
        if aid not in bot_state.accounts:
            bot_state.register_account(aid, nick or f"Player_{aid}", region=ad.get("region", "VN"), level=lvl_val, exp=exp_val, auth_uid=ad.get("auth_uid"))
            return
        old_exp = bot_state.accounts[aid].get("current_exp", 0)
        bot_state.update_exp(aid, exp_val, lvl_val)
        if nick:
            bot_state.accounts[aid]["nickname"] = nick
        if exp_val > old_exp:
            log_event(f"+{exp_val - old_exp:,} EXP | {aid}", color=PX.GOLD, icon=ICONS["spark"], tag="EXP")
    except Exception:
        pass


async def login_guest_account(uid: str, password: str, region_override: Optional[str] = None, force_fresh: bool = False) -> Optional[dict]:
    if not force_fresh:
        cached = token_manager.get(uid, allow_expiring=False)
        if cached:
            aid = str(cached["account_id"])
            bot_state.register_account(
                aid, cached.get("nickname", f"Player_{aid}"),
                cached.get("region", "VN"), cached.get("level", 1),
                cached.get("exp", 0), cached.get("likes", 0), auth_uid=str(uid),
            )
            register_account_credentials(cached)
            return cached

    log_info(f"[AUTH] Đăng nhập UID: {uid}")
    try:
        async with _LOGIN_SEMAPHORE:
            vc = await fetch_version_config(region_override or "ID")
            if not vc:
                return None
            release_version, client_version, server_url, _, _ = vc
            tg = await grant_guest_access_token(uid, password)
            if not tg:
                return None
            open_id, access_token, platform = tg
            login_payload = await build_login_payload(access_token, open_id, platform, client_version)
            res_json = await post_major_login(login_payload, server_url, release_version)
            if not res_json:
                return None

            acc_id_raw = extract_field_value(res_json, 1)
            region_raw = extract_field_value(res_json, 2, "ID")
            jwt_token = extract_field_value(res_json, 8)
            server_url_raw = extract_field_value(res_json, 10)
            server_time = extract_field_value(res_json, 21)
            aes_ak, iv_i = extract_key_iv(res_json)
            if not jwt_token or not server_url_raw or not aes_ak:
                return None

            login_data = await fetch_login_data(login_payload, jwt_token, server_url_raw, release_version)
            if not login_data:
                return None

            now_ts = time.time()
            level = int(extract_field_value(login_data, 6, 1) or 1)
            exp = int(extract_field_value(login_data, 7, 0) or 0)
            likes = int(extract_field_value(login_data, 8, 0) or 0)
            nickname = extract_field_value(login_data, 4, f"Player_{acc_id_raw}") or f"Player_{acc_id_raw}"
            region = region_raw or extract_field_value(login_data, 3, "ID") or "ID"
            acc_id = str(acc_id_raw)

            bot_state.register_account(acc_id, nickname, region, level, exp, likes, auth_uid=str(uid))
            log_event(f"Đăng nhập thành công: {acc_id} | {nickname} | Lvl {level} | {region}", color=PX.GOLD, icon=ICONS["gem"], tag="AUTH")

            ad = {
                "account_id": acc_id_raw,
                "nickname": nickname,
                "region": region,
                "level": level,
                "exp": exp,
                "likes": likes,
                "open_id": open_id,
                "access_token": access_token,
                "platform": str(platform),
                "token": jwt_token,
                "jwt_issued_at": now_ts,
                "jwt_expires_at": compute_jwt_expires_at(jwt_token, now_ts),
                "server_time": server_time,
                "aes_ak": aes_ak,
                "iv_i": iv_i,
                "functional_addrs": extract_field_value(login_data, 14),
                "informational_addrs": extract_field_value(login_data, 32),
                "release_version": release_version,
                "client_version": client_version,
                "server_url": server_url_raw,
                "login_payload_data": login_payload,
                "auth_type": "guest",
                "auth_uid": uid,
                "auth_password": password,
            }
            register_account_credentials(ad)
            return token_manager.set(uid, ad)
    except Exception as exc:
        log_err(f"[AUTH] Lỗi đăng nhập {uid}: {exc}")
        return None


async def run_account_worker(ad: dict, label: str, region_override: Optional[str] = None, clan_override: Optional[str] = None) -> None:
    acc_id = str(ad["account_id"])
    info_task: Optional[asyncio.Task] = None
    exp_task: Optional[asyncio.Task] = None
    try:
        reg = region_override or ad.get("region", "BD")
        tcp_online = await build_tcp_startup_packet(
            ad["account_id"], ad["token"], ad["server_time"],
            ad["aes_ak"], ad["iv_i"], region=reg, typ="OnLine",
        )
        tcp_chat = await build_tcp_startup_packet(
            ad["account_id"], ad["token"], ad["server_time"],
            ad["aes_ak"], ad["iv_i"], region=reg, typ="ChaT",
        )
        if clan_override:
            try:
                await asyncio.sleep(1.0)
                await request_join_clan(ad["token"], clan_override)
            except Exception as exc:
                log_warn(f"CLAN {exc}")

        info_task = asyncio.create_task(informational_worker(
            ad["informational_addrs"], tcp_chat, region=reg, account_id=acc_id, account_data=ad,
        ))

        async def _exp_loop() -> None:
            while True:
                await asyncio.sleep(90 + random.uniform(-10, 10))
                fresh = bot_state.account_credentials.get(acc_id)
                if fresh:
                    await refresh_account_profile(fresh)

        exp_task = asyncio.create_task(_exp_loop())
        await functional_worker(
            ad["functional_addrs"], tcp_online, reg, ad["client_version"],
            ad["aes_ak"], ad["iv_i"], account_id=acc_id, account_data=ad,
        )
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        log_err(f"Worker {label} lỗi: {exc}")
    finally:
        for t in (info_task, exp_task):
            if t and not t.done():
                t.cancel()
                try:
                    await t
                except Exception:
                    pass


async def account_loop_guest(uid: str, password: str, region_override: Optional[str] = None, clan_override: Optional[str] = None) -> None:
    uid_str = str(uid)
    bot_state.account_workers[uid_str] = asyncio.current_task()
    acc_id: Optional[str] = None
    while True:
        try:
            bot_state.update_status(uid_str, "CONNECTING")
            ad = await login_guest_account(uid_str, password, region_override)
            if not ad:
                log_err(f"Đăng nhập thất bại {uid_str} — thử lại sau 15s")
                await asyncio.sleep(15)
                continue
            acc_id = str(ad["account_id"])
            bot_state.account_workers[acc_id] = asyncio.current_task()
            bot_state.auth_to_game_id[uid_str] = acc_id
            bot_state.game_to_auth_id[acc_id] = uid_str
            await run_account_worker(ad, uid_str, region_override, clan_override)
            await asyncio.sleep(3)
        except asyncio.CancelledError:
            bot_state.update_status(uid_str, "OFFLINE")
            if acc_id:
                bot_state.update_status(acc_id, "OFFLINE")
            await _clear_team_joined(uid_str)
            if acc_id:
                await _clear_team_joined(acc_id)
            break
        except Exception as exc:
            log_err(f"Lỗi vòng lặp {uid_str}: {exc}")
            await asyncio.sleep(10)


async def exchange_garena_token(token: str, force_fresh: bool = False) -> Optional[dict]:
    cache_key = f"tok_{token[:20]}"
    if not force_fresh:
        cached = token_manager.get(cache_key, allow_expiring=False)
        if cached:
            register_account_credentials(cached)
            return cached

    log_info(f"[TOKEN] Đang xác thực token {token[:20]}...")
    try:
        vc = await fetch_version_config("ID")
        if not vc:
            return None
        release_version, client_version, server_url, _, _ = vc
        url = f"https://100067.connect.garena.com/oauth/token/inspect?token={token}"
        resp = await http_client.get(url, headers={"User-Agent": "GarenaMSDK/4.0.19P4(G011A ;Android 9;en;US;)"})
        if resp.status_code != 200:
            return None
        info = resp.json()
        if "error" in info or not info.get("open_id"):
            return None

        open_id = info["open_id"]
        platform = info.get("platform", 4)
        login_payload = await build_login_payload(token, open_id, platform, client_version)
        res_json = await post_major_login(login_payload, server_url, release_version)
        if not res_json:
            return None

        acc_id_raw = extract_field_value(res_json, 1)
        jwt_token = extract_field_value(res_json, 8)
        server_url_raw = extract_field_value(res_json, 10)
        server_time = extract_field_value(res_json, 21)
        region_raw = extract_field_value(res_json, 2, "ID")
        aes_ak, iv_i = extract_key_iv(res_json)
        if not (jwt_token and server_url_raw and aes_ak):
            return None

        login_data = await fetch_login_data(login_payload, jwt_token, server_url_raw, release_version)
        now_ts = time.time()
        ad = {
            "account_id": acc_id_raw,
            "nickname": extract_field_value(login_data, 4, f"Player_{acc_id_raw}") or f"Player_{acc_id_raw}",
            "region": region_raw,
            "level": int(extract_field_value(login_data, 6, 1) or 1),
            "exp": int(extract_field_value(login_data, 7, 0) or 0),
            "likes": int(extract_field_value(login_data, 8, 0) or 0),
            "open_id": open_id,
            "access_token": token,
            "platform": str(platform),
            "token": jwt_token,
            "jwt_issued_at": now_ts,
            "jwt_expires_at": compute_jwt_expires_at(jwt_token, now_ts),
            "server_time": server_time,
            "aes_ak": aes_ak,
            "iv_i": iv_i,
            "functional_addrs": extract_field_value(login_data, 14),
            "informational_addrs": extract_field_value(login_data, 32),
            "release_version": release_version,
            "client_version": client_version,
            "server_url": server_url_raw,
            "login_payload_data": login_payload,
            "auth_type": "token",
            "auth_token": token,
        }
        register_account_credentials(ad)
        return token_manager.set(cache_key, ad)
    except Exception as exc:
        log_err(f"[TOKEN] Lỗi đổi token: {exc}")
        return None


async def account_loop_token(token: str) -> None:
    cur_tok = token
    while True:
        ad = await exchange_garena_token(cur_tok, force_fresh=False)
        if not ad:
            log_err("[TOKEN] Xác thực token thất bại — thử lại sau 15s")
            await asyncio.sleep(15)
            continue
        await run_account_worker(ad, str(ad["account_id"]))
        await asyncio.sleep(3)


async def choose_region(region: str, jwt_token: str, login_url: str, release_version: str) -> Optional[int]:
    payload = bytes.fromhex(encrypt_aes(create_proto({1: region.upper()}).hex()))
    headers = {
        "Accept-Encoding": "gzip",
        "Authorization": f"Bearer {jwt_token}",
        "Connection": "Keep-Alive",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_version}",
        "User-Agent": "UnityPlayer/2018.4.12f1",
        "X-GA": "v1 1",
        "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1",
    }
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
            async with session.post(f"{login_url.rstrip('/')}/ChooseRegion", data=payload, headers=headers, ssl=_insecure_ssl_context()) as resp:
                log_info(f"CHOOSE-REGION {region} → HTTP {resp.status}")
                return resp.status
    except Exception as exc:
        log_err(f"CHOOSE-REGION {exc}")
        return None


async def post_major_register(release_v: str, access_token: str, open_id: str, name: str, game_version: str, login_url: str, lang_code: str = "en") -> Optional[dict]:
    try:
        field14 = bytes(ord(c) ^ KEYSTREAM[i % 32] for i, c in enumerate(open_id))
        proto = create_proto({
            1: name, 2: access_token, 3: open_id, 5: 102000007,
            6: 4, 7: 1, 13: 1, 14: field14, 15: lang_code,
            16: 2, 20: "2.132.4", 21: 1, 22: GGRE_RAW,
        })
        payload = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(proto, 16))
        headers = {
            "Accept": "*/*",
            "Accept-Encoding": "deflate, gzip",
            "Authorization": "Bearer",
            "Content-Type": "application/x-www-form-urlencoded",
            "ReleaseVersion": f"{release_v}",
            "User-Agent": "UnityPlayer/2018.4.12f1",
            "X-GA": "v1 1",
            "X-GA-SV": str(int(time.time())),
            "X-Unity-Version": "2018.4.12f1",
        }
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=30)) as session:
            async with session.post(f"{login_url.rstrip('/')}/MajorRegister", headers=headers, data=payload, ssl=_insecure_ssl_context()) as resp:
                content = await resp.read()
                if resp.status != 200 or not content:
                    return None
                for off in [0, 64, 48, 32, 80, 16, 8, 96, 128]:
                    if off < len(content):
                        r = decode_protobuf_2(content[off:])
                        if r and 3 in r:
                            return {str(k): {"data": v} for k, v in r.items()}
                if len(content) % 16 == 0:
                    pt = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).decrypt(content)
                    pad_len = pt[-1]
                    if 1 <= pad_len <= 16 and all(b == pad_len for b in pt[-pad_len:]):
                        r = decode_protobuf_2(pt[:-pad_len])
                        if r and 3 in r:
                            return {str(k): {"data": v} for k, v in r.items()}
                return None
    except Exception as exc:
        log_err(f"MAJOR-REG {exc}")
        return None


async def create_accounts_batch(region: str, clan_id: str, count: int = 4, password: str = "vanducdev") -> List[dict]:
    bot_state.creating = True
    bot_state.create_progress = []

    def _prog(text: str) -> None:
        log_event(text, color=PX.VIOLET, icon=ICONS["bolt"], tag="CREATE")
        bot_state.create_progress.append(text)

    try:
        print_rule(f"AUTO-CREATE {count} BOTS · {region}", color=PX.MAGENTA)
        vc = await fetch_version_config(region)
        if not vc:
            _prog("Lấy version config thất bại")
            return []
        release_v, remote_v, login_url, gop_1, app_version = vc
        if not login_url.endswith("/"):
            login_url += "/"
        lang = REGION_LANG.get(region.upper(), "en")
        game_version = remote_v or app_version
        created: List[dict] = []

        for i in range(count):
            _prog(f"Đang tạo bot {i + 1}/{count}...")
            try:
                uid = await register_guest_uid(password, gop_1, app_version)
                if not uid:
                    _prog(f"Bot {i + 1}: đăng ký thất bại")
                    continue
                tok = await grant_gop_token(uid, password, gop_1, app_version)
                if not tok:
                    _prog(f"Bot {i + 1}: cấp token thất bại")
                    continue

                open_id, access_token, platform = tok["open_id"], tok["access_token"], tok.get("platform", 4)
                suffix = "".join(random.choices(string.ascii_uppercase + string.digits, k=3))
                nickname_final = f"{BOT_NAME_PREFIX}{suffix}"
                mr = await post_major_register(release_v, access_token, open_id, nickname_final, game_version, login_url, lang)
                if not mr and "*" in BOT_NAME_PREFIX:
                    nickname_final = f"{BOT_NAME_PREFIX.replace('*', '•')}{suffix}"
                    mr = await post_major_register(release_v, access_token, open_id, nickname_final, game_version, login_url, lang)
                if not mr:
                    _prog(f"Bot {i + 1}: MajorRegister thất bại")
                    continue

                await asyncio.sleep(3.0)
                res_json = None
                login_payload = b""
                for _ in range(3):
                    login_payload = await build_login_payload(access_token, open_id, platform, game_version, lang)
                    cand = await post_major_login(login_payload, login_url, release_v)
                    if cand and (("8" in cand) or (8 in cand)):
                        res_json = cand
                        break
                    await asyncio.sleep(2.0)

                if not res_json:
                    _prog(f"Bot {i + 1}: MajorLogin #1 thất bại")
                    continue

                jwt_token = extract_field_value(res_json, 8)
                server_url_raw = extract_field_value(res_json, 10)
                server_time = extract_field_value(res_json, 21)
                acc_id_raw = extract_field_value(res_json, 1)

                if not jwt_token:
                    _prog(f"Bot {i + 1}: thiếu JWT")
                    continue

                if not server_url_raw:
                    if await choose_region(region, jwt_token, login_url, release_v) != 200:
                        _prog(f"Bot {i + 1}: ChooseRegion thất bại")
                        continue
                    await asyncio.sleep(2.0)
                    res_json2 = None
                    for _ in range(3):
                        login_payload = await build_login_payload(access_token, open_id, platform, game_version, lang)
                        cand2 = await post_major_login(login_payload, login_url, release_v)
                        if cand2 and (("10" in cand2) or (10 in cand2)):
                            res_json2 = cand2
                            break
                        await asyncio.sleep(2.0)
                    if not res_json2:
                        _prog(f"Bot {i + 1}: MajorLogin #2 thất bại")
                        continue
                    res_json = res_json2
                    jwt_token = extract_field_value(res_json, 8)
                    server_url_raw = extract_field_value(res_json, 10)
                    server_time = extract_field_value(res_json, 21)
                    acc_id_raw = extract_field_value(res_json, 1)

                aes_ak, iv_i = extract_key_iv(res_json)
                if not aes_ak or not iv_i:
                    _prog(f"Bot {i + 1}: lỗi lấy AES key/IV")
                    continue

                ld = await fetch_login_data(login_payload, jwt_token, server_url_raw, release_v)
                now_ts = time.time()
                ad = {
                    "account_id": acc_id_raw,
                    "nickname": extract_field_value(ld, 4, nickname_final) or nickname_final,
                    "region": region,
                    "level": int(extract_field_value(ld, 6, 1) or 1),
                    "exp": int(extract_field_value(ld, 7, 0) or 0),
                    "likes": int(extract_field_value(ld, 8, 0) or 0),
                    "open_id": open_id,
                    "access_token": access_token,
                    "platform": str(platform),
                    "token": jwt_token,
                    "jwt_issued_at": now_ts,
                    "jwt_expires_at": compute_jwt_expires_at(jwt_token, now_ts),
                    "server_time": server_time,
                    "aes_ak": aes_ak,
                    "iv_i": iv_i,
                    "functional_addrs": extract_field_value(ld, 14),
                    "informational_addrs": extract_field_value(ld, 32),
                    "release_version": release_v,
                    "client_version": game_version,
                    "server_url": server_url_raw,
                    "login_payload_data": login_payload,
                    "auth_type": "guest",
                    "auth_uid": uid,
                    "auth_password": password,
                }
                register_account_credentials(ad)
                token_manager.set(uid, ad)
                created.append(ad)
                _prog(f"Bot {i + 1}: {ad['nickname']} | UID {acc_id_raw} | {region}")
                await asyncio.sleep(0.6)
            except Exception as exc:
                _prog(f"Bot {i + 1} lỗi: {exc}")
                traceback.print_exc()

        if created:
            existing: list = []
            if os.path.exists(ACCOUNTS_FILE):
                try:
                    with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                        loaded = json.load(f)
                        if isinstance(loaded, list):
                            existing = loaded
                except Exception:
                    existing = []
            known_uids = {str(a.get("uid")) for a in existing if isinstance(a, dict)}
            for a in created:
                u = str(a["auth_uid"])
                if u not in known_uids:
                    existing.append({"uid": u, "password": a["auth_password"], "region": region, "clan_id": clan_id})
            atomic_write_json(ACCOUNTS_FILE, existing)
            _prog(f"Đã lưu {len(created)} tài khoản vào {ACCOUNTS_FILE}")

            bot_state.expected_workers += len(created)
            for idx_w, a in enumerate(created, start=1):
                u = str(a["auth_uid"])
                task = asyncio.create_task(account_loop_guest(u, a["auth_password"], region_override=region, clan_override=clan_id))
                bot_state.account_workers[u] = task
                _prog(f"Khởi chạy worker {idx_w}/{len(created)} ({u})")
                await asyncio.sleep(0.35)

        return created
    except Exception as exc:
        _prog(f"Lỗi tạo tài khoản: {exc}")
        return []
    finally:
        bot_state.creating = False
        print_rule(color=PX.MAGENTA)


async def autoload_accounts() -> None:
    if not os.path.exists(ACCOUNTS_FILE):
        log_info("[BOOT] Không tìm thấy accounts.json")
        return
    try:
        with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
            accounts = json.load(f) or []
    except Exception as exc:
        log_err(f"[BOOT] Lỗi đọc accounts.json: {exc}")
        return

    if not isinstance(accounts, list) or not accounts:
        log_info("[BOOT] accounts.json trống")
        return

    valid = [
        a for a in accounts
        if isinstance(a, dict) and str(a.get("uid", "")).strip() and str(a.get("password", "")).strip()
    ]
    bot_state.expected_workers = len(valid)
    log_event(f"Tự động nạp {len(valid)} tài khoản", color=PX.GOLD, icon=ICONS["star"], tag="BOOT")

    for idx, acc in enumerate(valid, start=1):
        uid = str(acc["uid"]).strip()
        password = str(acc["password"]).strip()
        region = str(acc.get("region", "")).strip() or None
        clan_id = str(acc.get("clan_id", "")).strip() or CLAN_ID_DEFAULT
        bot_state.account_workers[uid] = asyncio.create_task(
            account_loop_guest(uid, password, region_override=region, clan_override=clan_id)
        )
        log_info(f"Worker {uid} ({idx}/{len(valid)}) region={region or 'AUTO'}")
        await asyncio.sleep(0.25)


# ==================== WEB API & SERVER ====================
@aiohttp.web.middleware
async def request_logger_middleware(request: aiohttp.web.Request, handler: Any) -> aiohttp.web.StreamResponse:
    try:
        resp = await handler(request)
        print(f"{PX.SLATE}[HTTP]{PX.RESET} {request.method} {request.path} → {PX.EMERALD}{resp.status}{PX.RESET}")
        return resp
    except aiohttp.web.HTTPException as exc:
        if request.path.startswith("/api/"):
            return aiohttp.web.json_response({"ok": False, "status": "error", "error": exc.reason or str(exc)}, status=exc.status)
        raise
    except Exception as exc:
        traceback.print_exc()
        if request.path.startswith("/api/"):
            return aiohttp.web.json_response({"ok": False, "status": "error", "error": str(exc)}, status=500)
        raise


async def serve_index(request: aiohttp.web.Request) -> aiohttp.web.Response:
    for path in (INDEX_HTML_PATH, "index.html"):
        if os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return aiohttp.web.Response(text=f.read(), content_type="text/html")
            except Exception:
                pass
    return aiohttp.web.Response(text="<h1>Glory - Free Fire</h1>", content_type="text/html")


async def api_ping(request: aiohttp.web.Request) -> aiohttp.web.Response:
    return aiohttp.web.json_response({"pong": True, "app": "GloryFF", "version": "3.2"})


async def api_stats(request: aiohttp.web.Request) -> aiohttp.web.Response:
    accs = list(bot_state.accounts.values())
    online = sum(1 for a in accs if str(a.get("status", "")).startswith(("ONLINE", "IN_MATCH", "SEARCHING")))
    active_matches = sum(a.get("active_matches", 0) for a in accs)
    uptime = max(1, int(time.time() - bot_state.start_time))
    uptime_h = max(0.016, uptime / 3600.0)
    logs_out = [
        {"time": str(l.get("time", "")), "message": str(l.get("message", "")), "level": str(l.get("level", "info"))}
        for l in bot_state.logs[-200:]
    ]
    payload = {
        "accounts": accs,
        "logs": logs_out,
        "total_accounts": len(accs),
        "total_online": online,
        "total_matches": bot_state.total_matches,
        "total_matches_started": bot_state.matches_started,
        "total_active_matches": active_matches,
        "total_gained_exp": bot_state.total_exp_gained,
        "uptime": uptime,
        "exp_per_hour": int(bot_state.total_exp_gained / uptime_h),
        "matches_per_hour": int(bot_state.matches_started / uptime_h),
        "creating": bool(bot_state.creating),
        "create_progress": [str(x) for x in bot_state.create_progress[-40:]],
        "team_code": _team_state.get("team_code"),
        "team_codes": _team_state.get("team_codes", {}),
        "squads": _team_state.get("squads", []),
        "leader_uid": _team_state.get("leader_uid"),
        "team_size": len(_team_state["peers"]),
        "restart_finished": len(_restart_state["finished_bots"]),
        "restart_target": _restart_state["target"],
        "restarting": _restart_state["restarting"],
    }
    return aiohttp.web.Response(text=json.dumps(payload, default=str, ensure_ascii=False), content_type="application/json", charset="utf-8")


async def api_state(request: aiohttp.web.Request) -> aiohttp.web.Response:
    payload = {
        "creating": bool(bot_state.creating),
        "create_progress": [str(x) for x in bot_state.create_progress[-40:]],
        "accounts": list(bot_state.accounts.values()),
        "team_size": len(_team_state["peers"]),
        "squads": _team_state.get("squads", []),
        "team_codes": _team_state.get("team_codes", {}),
    }
    return aiohttp.web.Response(text=json.dumps(payload, default=str, ensure_ascii=False), content_type="application/json", charset="utf-8")


async def api_progress(request: aiohttp.web.Request) -> aiohttp.web.Response:
    return aiohttp.web.json_response({
        "creating": bool(bot_state.creating),
        "create_progress": [str(x) for x in bot_state.create_progress[-60:]],
    })


async def api_create_team(request: aiohttp.web.Request) -> aiohttp.web.Response:
    body = await request.json()
    region = str(body.get("region", "VN")).upper()
    clan_id = str(body.get("clan_id", "")).strip()
    count = max(1, min(12, int(body.get("count", 4))))
    password = str(body.get("password", "senzuffx")).strip() or "senzuffx"
    if not clan_id:
        return aiohttp.web.json_response({"ok": False, "error": "clan_id required"})
    if bot_state.creating:
        return aiohttp.web.json_response({"ok": False, "error": "already creating"})
    asyncio.create_task(create_accounts_batch(region, clan_id, count, password))
    return aiohttp.web.json_response({"ok": True, "msg": f"creating {count} bots"})


async def api_account_add(request: aiohttp.web.Request) -> aiohttp.web.Response:
    body = await request.json()
    if body.get("token"):
        token = str(body["token"]).strip()
        if not token:
            return aiohttp.web.json_response({"status": "error", "error": "empty token"})
        asyncio.create_task(account_loop_token(token))
        return aiohttp.web.json_response({"status": "ok"})
    uid = str(body.get("uid", "")).strip()
    password = str(body.get("password", "")).strip()
    if not uid or not password:
        return aiohttp.web.json_response({"status": "error", "error": "uid/password required"})
    asyncio.create_task(account_loop_guest(uid, password))
    return aiohttp.web.json_response({"status": "ok"})


async def api_account_delete(request: aiohttp.web.Request) -> aiohttp.web.Response:
    body = await request.json()
    uid = str(body.get("uid", "")).strip()
    auth_uid = str(body.get("auth_uid", "")).strip()
    targets = {uid, auth_uid} - {""}
    for u in list(targets):
        if u in bot_state.auth_to_game_id:
            targets.add(str(bot_state.auth_to_game_id[u]))
        if u in bot_state.game_to_auth_id:
            targets.add(str(bot_state.game_to_auth_id[u]))
        acc_obj = bot_state.accounts.get(u)
        if isinstance(acc_obj, dict) and acc_obj.get("auth_uid"):
            targets.add(str(acc_obj["auth_uid"]))

    for u in targets:
        task = bot_state.account_workers.pop(u, None)
        if task:
            task.cancel()
        bot_state.accounts.pop(u, None)
        bot_state.account_credentials.pop(u, None)
        token_manager.invalidate(u)
        bot_state.toggle_pause(u, False)
        async with _team_state["lock"]:
            _team_state["peers"].pop(u, None)
            _team_state["uid_to_leader"].pop(u, None)
            _team_state["uid_to_squad_idx"].pop(u, None)

    if os.path.exists(ACCOUNTS_FILE):
        try:
            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                existing = json.load(f) or []
            if isinstance(existing, list):
                filtered = [a for a in existing if isinstance(a, dict) and str(a.get("uid", "")).strip() not in targets]
                atomic_write_json(ACCOUNTS_FILE, filtered)
                bot_state.expected_workers = len(filtered)
        except Exception:
            pass
    return aiohttp.web.json_response({"status": "ok"})


async def api_account_refresh(request: aiohttp.web.Request) -> aiohttp.web.Response:
    body = await request.json()
    uid = str(body.get("uid", "")).strip()
    asyncio.create_task(refresh_account_profile(uid))
    return aiohttp.web.json_response({"status": "ok"})


async def api_account_restart(request: aiohttp.web.Request) -> aiohttp.web.Response:
    body = await request.json()
    uid = str(body.get("uid", "")).strip()
    targets = {uid}
    if uid in bot_state.game_to_auth_id:
        targets.add(str(bot_state.game_to_auth_id[uid]))
    if uid in bot_state.auth_to_game_id:
        targets.add(str(bot_state.auth_to_game_id[uid]))

    for u in targets:
        task = bot_state.account_workers.pop(u, None)
        if task:
            task.cancel()

    if os.path.exists(ACCOUNTS_FILE):
        try:
            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                accs = json.load(f) or []
            for a in accs:
                if str(a.get("uid")) in targets and a.get("password"):
                    u_key = str(a["uid"])
                    bot_state.account_workers[u_key] = asyncio.create_task(
                        account_loop_guest(u_key, a["password"], region_override=a.get("region"), clan_override=a.get("clan_id"))
                    )
                    break
        except Exception:
            pass
    return aiohttp.web.json_response({"status": "ok"})


async def api_account_pause(request: aiohttp.web.Request) -> aiohttp.web.Response:
    body = await request.json()
    uid = str(body.get("uid", "")).strip()
    new_state = not bot_state.is_paused(uid)
    bot_state.toggle_pause(uid, new_state)
    if new_state:
        bot_state.close_writers_for_account(uid)
    return aiohttp.web.json_response({"status": "ok", "is_paused": new_state})


async def api_account_pause_all(request: aiohttp.web.Request) -> aiohttp.web.Response:
    accs = list(bot_state.accounts.keys())
    if not accs:
        return aiohttp.web.json_response({"status": "ok", "all_paused": False})
    new_state = not all(bot_state.is_paused(u) for u in accs)
    for u in accs:
        bot_state.toggle_pause(u, new_state)
        if new_state:
            bot_state.close_writers_for_account(u)
    return aiohttp.web.json_response({"status": "ok", "all_paused": new_state})


async def api_logs_clear(request: aiohttp.web.Request) -> aiohttp.web.Response:
    bot_state.logs = []
    return aiohttp.web.json_response({"status": "ok"})


async def start_web_server() -> aiohttp.web.AppRunner:
    app = aiohttp.web.Application(middlewares=[request_logger_middleware])
    app.router.add_get("/", serve_index)
    app.router.add_get("/index.html", serve_index)
    app.router.add_get("/api/ping", api_ping)
    app.router.add_get("/api/stats", api_stats)
    app.router.add_get("/api/state", api_state)
    app.router.add_get("/api/progress", api_progress)
    app.router.add_post("/api/create_team", api_create_team)
    app.router.add_post("/api/account/add", api_account_add)
    app.router.add_post("/api/account/delete", api_account_delete)
    app.router.add_post("/api/account/refresh", api_account_refresh)
    app.router.add_post("/api/account/restart", api_account_restart)
    app.router.add_post("/api/account/pause", api_account_pause)
    app.router.add_post("/api/account/pause_all", api_account_pause_all)
    app.router.add_post("/api/logs/clear", api_logs_clear)

    runner = aiohttp.web.AppRunner(app)
    await runner.setup()
    for attempt in range(5):
        try:
            await aiohttp.web.TCPSite(runner, WEB_HOST, WEB_PORT).start()
            break
        except OSError:
            if attempt == 4:
                raise
            await asyncio.sleep(1.0)

    log_event(f"Web Dashboard → http://localhost:{WEB_PORT}", color=PX.CYAN, icon=ICONS["rocket"], tag="WEB")
    return runner


# ==================== ĐIỂM KHỞI CHẠY CHÍNH ====================
async def main() -> None:
    print_menu_banner()
    try:
        await start_web_server()
    except Exception as exc:
        log_err(f"WEB khởi động lỗi: {exc}")
        return

    try:
        await autoload_accounts()
    except Exception as exc:
        log_err(f"BOOT nạp tài khoản lỗi: {exc}")

    asyncio.create_task(_no_match_watchdog())
    print_rule("Hệ Thống Đang Hoạt Động", color=PX.EMERALD)

    try:
        while True:
            await asyncio.sleep(1)
    except (KeyboardInterrupt, asyncio.CancelledError):
        log_warn("Đang dừng hệ thống...")
        for t in list(bot_state.account_workers.values()):
            t.cancel()
        await asyncio.gather(*bot_state.account_workers.values(), return_exceptions=True)
        try:
            await http_client.aclose()
        except Exception:
            pass


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        log_warn("Đã dừng")