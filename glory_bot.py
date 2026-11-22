# -*- coding: utf-8 -*-
"""
Glory FF Bot – Telegram Integration
Tích hợp PyTelegramBotAPI vào Glory FF
Hỗ trợ đa người dùng, mỗi người một luồng độc lập
Hệ thống KEY xác thực – Admin bypass
"""

import sys, os, json, time, uuid, asyncio, threading, logging
from typing import Dict, Optional

import telebot
from telebot import types

# ── Đường dẫn project ──────────────────────────────────────────────────────
BASE_DIR  = os.path.dirname(os.path.abspath(__file__))
GLORY_DIR = os.path.join(BASE_DIR, "glory_ff")
sys.path.insert(0, GLORY_DIR)
sys.path.insert(0, os.path.join(BASE_DIR, "clan_join"))

from glory_ff import main as glory_main
from clan_join.Req import join_sync

# ═══════════════════════════════════════════════════════════════════════════
#  CONFIG
# ═══════════════════════════════════════════════════════════════════════════
BOT_TOKEN           = "9169867428:AAEYnfFycjQs8ubT7P6rejOK68wU4uzd0Kg"       # 🔑 Thay token của bạn
ADMIN_ID            = 1804489430                   # Admin – không cần key
# ⚠️ SINGLE SOURCE OF TRUTH – chỉ dùng glory_ff/accounts.json
ACCOUNTS_FILE       = os.path.join(GLORY_DIR, "accounts.json")
KEYS_FILE           = os.path.join(BASE_DIR, "keys.json")      # lưu key trên disk
SESSIONS_FILE       = os.path.join(BASE_DIR, "sessions.json")  # lưu session trên disk
BOT_ACCOUNTS_PER_USER = 4
MSG_DELETE_SEC      = 10

# ── Logging → file, không tràn console ────────────────────────────────────
logging.basicConfig(
    level=logging.WARNING,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler("glory_bot.log", encoding="utf-8")]
)
log = logging.getLogger("glory_bot")


# ═══════════════════════════════════════════════════════════════════════════
#  KeyManager – tạo / xác thực key dùng 1 lần
# ═══════════════════════════════════════════════════════════════════════════
class KeyManager:
    """
    Key lưu trên disk (keys.json) để không mất khi restart bot.
    Mỗi key chỉ dùng được đúng 1 lần, sau đó xoá.
    user_id đã xác thực được lưu trong _authed set (in-memory).
    """

    def __init__(self, path: str):
        self._lock   = threading.Lock()
        self._path   = path
        self._keys: Dict[str, bool] = {}   # key → used (False = còn dùng được)
        self._authed: set = set()          # user_id đã xác thực trong session này
        self._load()

    # ── disk ────────────────────────────────────────────────────────────
    def _load(self):
        try:
            if os.path.exists(self._path):
                with open(self._path, "r", encoding="utf-8") as f:
                    self._keys = json.load(f)
        except Exception as e:
            log.error(f"KeyManager load: {e}")
            self._keys = {}

    def _save(self):
        try:
            with open(self._path, "w", encoding="utf-8") as f:
                json.dump(self._keys, f, indent=2)
        except Exception as e:
            log.error(f"KeyManager save: {e}")

    # ── API ─────────────────────────────────────────────────────────────
    def generate(self) -> str:
        """Tạo key mới dạng GLORY-XXXX-XXXX-XXXX."""
        raw   = uuid.uuid4().hex.upper()
        key   = f"GLORY-{raw[0:4]}-{raw[4:8]}-{raw[8:12]}"
        with self._lock:
            self._keys[key] = False   # False = chưa dùng
            self._save()
        return key

    def redeem(self, user_id: int, key: str) -> str:
        """
        Đổi key lấy quyền dùng bot.
        Return: 'ok' | 'used' | 'invalid' | 'already_authed'
        """
        with self._lock:
            if user_id in self._authed:
                return "already_authed"
            key = key.strip().upper()
            if key not in self._keys:
                return "invalid"
            if self._keys[key] is True:
                return "used"
            # Hợp lệ → đánh dấu dùng rồi, cấp quyền
            self._keys[key] = True
            self._save()
            self._authed.add(user_id)
            return "ok"

    def is_authed(self, user_id: int) -> bool:
        return user_id == ADMIN_ID or user_id in self._authed

    def list_keys(self) -> dict:
        with self._lock:
            available = [k for k, used in self._keys.items() if not used]
            used      = [k for k, v   in self._keys.items() if v]
            return {"available": available, "used": used}

    def revoke_all_unused(self) -> int:
        """Xoá toàn bộ key chưa dùng. Trả về số key đã xoá."""
        with self._lock:
            to_del = [k for k, v in self._keys.items() if not v]
            for k in to_del:
                del self._keys[k]
            self._save()
            return len(to_del)


# ═══════════════════════════════════════════════════════════════════════════
#  SessionManager – quản lý tài nguyên theo từng user
# ═══════════════════════════════════════════════════════════════════════════
class SessionManager:
    """
    Quản lý session theo từng user.
    Mỗi thay đổi (acquire / release / set_field) đều ghi ngay ra sessions.json
    để bot restart không mất dữ liệu.

    Cấu trúc sessions.json:
    {
      "<user_id>": {
        "clan_id"   : "3105683920",
        "indices"   : [0, 1, 2, 3],
        "accounts"  : [{"uid": "...", "password": "..."}, ...],
        "chat_id"   : 123456789,
        "started_at": 1700000000.0,
        "status"    : "DONE",
        "results"   : [...]
      },
      ...
    }
    Thread-runtime fields (thread) không lưu vì không serializable.
    """

    def __init__(self, accounts_file: str, sessions_file: str):
        self._lock          = threading.Lock()
        self._acc_file      = accounts_file
        self._sess_file     = sessions_file
        self._all_accounts  : list            = []
        self._free_indices  : list            = []
        self._sessions      : Dict[int, dict] = {}   # int key in-memory
        self._load_accounts()
        self._restore_sessions()

    # ── Accounts ────────────────────────────────────────────────────────
    def _load_accounts(self):
        try:
            with open(self._acc_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            self._all_accounts = data if isinstance(data, list) else data.get("accounts", [])
            self._free_indices = list(range(len(self._all_accounts)))
        except Exception as e:
            log.error(f"SessionManager load accounts: {e}")
            self._all_accounts = []
            self._free_indices = []

    # ── Persist sessions ─────────────────────────────────────────────────
    def _save(self):
        """Ghi toàn bộ session ra disk. Gọi bên trong lock."""
        try:
            # Chuyển key int → str để JSON hợp lệ, bỏ field 'thread'
            data = {}
            for uid, sess in self._sessions.items():
                data[str(uid)] = {k: v for k, v in sess.items() if k != "thread"}
            with open(self._sess_file, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            log.error(f"SessionManager save: {e}")

    def _restore_sessions(self):
        """
        Đọc sessions.json khi khởi động.
        Khôi phục lại _sessions và đánh dấu indices đã dùng vào _free_indices.
        """
        if not os.path.exists(self._sess_file):
            return
        try:
            with open(self._sess_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, dict):
                return

            restored = 0
            for uid_str, sess in data.items():
                user_id = int(uid_str)
                indices = sess.get("indices", [])

                # Kiểm tra indices còn hợp lệ với accounts.json hiện tại
                if not indices or max(indices) >= len(self._all_accounts):
                    log.warning(f"[restore] user={user_id} indices không hợp lệ, bỏ qua")
                    continue

                # Xoá các indices đó khỏi free pool
                for idx in indices:
                    if idx in self._free_indices:
                        self._free_indices.remove(idx)

                # Đảm bảo accounts trong session khớp với accounts.json hiện tại
                sess["accounts"] = [self._all_accounts[i] for i in indices]
                sess["thread"]   = None
                sess["status"]   = sess.get("status", "IDLE")

                # Nếu trước đó đang RUNNING → đánh dấu INTERRUPTED để user biết
                if sess["status"] == "RUNNING":
                    sess["status"] = "INTERRUPTED"

                self._sessions[user_id] = sess
                restored += 1

            if restored:
                log.warning(f"[restore] Khôi phục {restored} session từ disk")
                print(f"♻️  Khôi phục {restored} session từ sessions.json")
        except Exception as e:
            log.error(f"SessionManager restore: {e}")

    # ── API công khai ────────────────────────────────────────────────────
    def total(self) -> int:
        return len(self._all_accounts)

    def free(self) -> int:
        with self._lock:
            return len(self._free_indices)

    def acquire(self, user_id: int, clan_id: str) -> Optional[list]:
        """Lấy BOT_ACCOUNTS_PER_USER account chưa dùng, gắn cho user_id, lưu disk."""
        with self._lock:
            if user_id in self._sessions:
                return None
            if len(self._free_indices) < BOT_ACCOUNTS_PER_USER:
                return None
            picked   = self._free_indices[:BOT_ACCOUNTS_PER_USER]
            self._free_indices = self._free_indices[BOT_ACCOUNTS_PER_USER:]
            accounts = [self._all_accounts[i] for i in picked]
            self._sessions[user_id] = {
                "clan_id"   : clan_id,
                "indices"   : picked,
                "accounts"  : accounts,
                "chat_id"   : None,
                "started_at": time.time(),
                "thread"    : None,
                "status"    : "IDLE",
                "results"   : [],
            }
            self._save()
            return accounts

    def release(self, user_id: int):
        """Giải phóng session và account, xoá khỏi disk."""
        with self._lock:
            sess = self._sessions.pop(user_id, None)
            if sess:
                self._free_indices.extend(sess["indices"])
                self._free_indices.sort()
            self._save()

    def get_session(self, user_id: int) -> Optional[dict]:
        with self._lock:
            return self._sessions.get(user_id)

    def set_field(self, user_id: int, key: str, value):
        """Cập nhật một field trong session và lưu disk ngay."""
        with self._lock:
            if user_id in self._sessions:
                # Bỏ qua field thread – không serializable
                if key != "thread":
                    self._sessions[user_id][key] = value
                    self._save()
                else:
                    self._sessions[user_id][key] = value

    def has_session(self, user_id: int) -> bool:
        with self._lock:
            return user_id in self._sessions

    def is_free_enough(self) -> bool:
        with self._lock:
            return len(self._free_indices) >= BOT_ACCOUNTS_PER_USER

    def restored_sessions(self) -> list:
        """Trả về danh sách (user_id, sess) bị INTERRUPTED sau restart."""
        with self._lock:
            return [
                (uid, sess) for uid, sess in self._sessions.items()
                if sess.get("status") == "INTERRUPTED"
            ]

    def summary(self) -> str:
        with self._lock:
            return (
                f"Tổng account : <b>{self.total()}</b>\n"
                f"Đang rảnh    : <b>{len(self._free_indices)}</b>\n"
                f"Đang dùng    : <b>{len(self._sessions) * BOT_ACCOUNTS_PER_USER}</b>\n"
                f"Phiên đang chạy: <b>{len(self._sessions)}</b>"
            )


# ═══════════════════════════════════════════════════════════════════════════
#  Khởi tạo global objects
# ═══════════════════════════════════════════════════════════════════════════
key_mgr  = KeyManager(KEYS_FILE)
sessions = SessionManager(ACCOUNTS_FILE, SESSIONS_FILE)
bot      = telebot.TeleBot(BOT_TOKEN, parse_mode="HTML")


# ═══════════════════════════════════════════════════════════════════════════
#  Helpers
# ═══════════════════════════════════════════════════════════════════════════
def _auto_delete(chat_id: int, msg_id: int, delay: int = MSG_DELETE_SEC):
    def _do():
        time.sleep(delay)
        try:
            bot.delete_message(chat_id, msg_id)
        except Exception:
            pass
    threading.Thread(target=_do, daemon=True).start()


def _send(chat_id: int, text: str, auto_del: bool = True, **kwargs) -> types.Message:
    msg = bot.send_message(chat_id, text, parse_mode="HTML", **kwargs)
    if auto_del:
        _auto_delete(chat_id, msg.message_id)
    return msg


def _del_cmd(msg: types.Message, delay: int = 3):
    """Xoá lệnh người dùng gõ."""
    _auto_delete(msg.chat.id, msg.message_id, delay)


def _result_icon(ok: bool) -> str:
    return "✅" if ok else "❌"


def _require_auth(msg: types.Message) -> bool:
    """
    Kiểm tra user đã xác thực chưa.
    Trả về True nếu được phép, False + gửi thông báo nếu chưa.
    """
    if key_mgr.is_authed(msg.from_user.id):
        return True
    _del_cmd(msg, 3)
    _send(msg.chat.id,
          "🔐 <b>Yêu cầu xác thực!</b>\n"
          "━━━━━━━━━━━━━━━━━━━━━━━━\n"
          "Bạn cần nhập key để sử dụng bot.\n\n"
          "📌 Dùng lệnh:\n"
          "<code>/key YOUR_KEY_HERE</code>\n\n"
          "💡 Liên hệ admin để lấy key.")
    return False


# ═══════════════════════════════════════════════════════════════════════════
#  Worker – join_clan chạy trong luồng riêng
# ═══════════════════════════════════════════════════════════════════════════
def _join_worker(user_id: int, chat_id: int, clan_id: str, accounts: list):
    """Chạy 4 lần join_sync tuần tự, gửi kết quả, giải phóng session."""
    results = []
    sessions.set_field(user_id, "status", "RUNNING")

    for idx, acc in enumerate(accounts, 1):
        uid, pw = acc["uid"], acc["password"]
        log.info(f"[user={user_id}] join #{idx} uid={uid} clan={clan_id}")
        try:
            r     = join_sync(uid, pw, clan_id)
            ok    = r.get("ok", False)
            resp  = r.get("response", "")
            stage = r.get("stage", "")

            if ok:
                note = "Tham gia thành công"
            elif "ALREADY_IN_CLAN"         in resp: note = "Đã trong quân đoàn"
            elif "CLAN_NOT_EXIST"          in resp: note = "Quân đoàn không tồn tại"
            elif "CLAN_FULL"               in resp: note = "Quân đoàn đã đầy"
            elif "REQUEST_ALREADY_SENT"    in resp: note = "Yêu cầu đã gửi trước đó"
            elif "ACCOUNT_LEVEL_NOT_ENOUGH" in resp: note = "Cấp độ không đủ"
            elif stage:                              note = f"Lỗi tại bước: {stage}"
            else:                                    note = f"HTTP {r.get('status','?')}"

            results.append({"uid": uid, "ok": ok, "note": note})
        except Exception as e:
            log.exception(f"[user={user_id}] join exception uid={uid}")
            results.append({"uid": uid, "ok": False, "note": f"Ngoại lệ: {str(e)[:60]}"})

    sessions.set_field(user_id, "results", results)
    sessions.set_field(user_id, "status", "DONE")

    success = sum(1 for r in results if r["ok"])
    rows    = "\n".join(
        f"  {_result_icon(r['ok'])} <code>{r['uid']}</code> – {r['note']}"
        for r in results
    )
    try:
        _send(chat_id,
              f"🏰 <b>KẾT QUẢ THAM GIA QUÂN ĐOÀN</b>\n"
              f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
              f"🆔 Clan ID   : <code>{clan_id}</code>\n"
              f"📊 Thành công: <b>{success}/{len(results)}</b>\n"
              f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
              f"{rows}\n"
              f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
              f"<i>⏱ Tin nhắn tự xoá sau {MSG_DELETE_SEC}s</i>")
    except Exception as e:
        log.error(f"[user={user_id}] send result failed: {e}")

    sessions.release(user_id)
    log.info(f"[user={user_id}] session released")


# ═══════════════════════════════════════════════════════════════════════════
#  Glory FF runner – async loop trong thread riêng
# ═══════════════════════════════════════════════════════════════════════════
_glory_loop  : Optional[asyncio.AbstractEventLoop] = None
_glory_thread: Optional[threading.Thread]          = None
_glory_lock  = threading.Lock()


def _start_glory_runner() -> bool:
    global _glory_loop, _glory_thread
    with _glory_lock:
        if _glory_thread and _glory_thread.is_alive():
            return False
        def _run():
            global _glory_loop
            _glory_loop = asyncio.new_event_loop()
            asyncio.set_event_loop(_glory_loop)
            try:
                _glory_loop.run_until_complete(glory_main.main())
            except Exception as e:
                log.error(f"Glory runner crashed: {e}")
            finally:
                _glory_loop.close()
        _glory_thread = threading.Thread(target=_run, daemon=True, name="GloryRunner")
        _glory_thread.start()
        return True


def _glory_is_running() -> bool:
    return bool(_glory_thread and _glory_thread.is_alive())


# ═══════════════════════════════════════════════════════════════════════════
#  COMMANDS
# ═══════════════════════════════════════════════════════════════════════════

# ── /start ──────────────────────────────────────────────────────────────
@bot.message_handler(commands=["start"])
def cmd_start(msg: types.Message):
    _del_cmd(msg, 5)
    is_admin = msg.from_user.id == ADMIN_ID
    authed   = key_mgr.is_authed(msg.from_user.id)

    admin_cmds = (
        "\n\n👑 <b>Lệnh Admin:</b>\n"
        "🔑 <code>/genkey</code>  – Tạo key mới\n"
        "🗂 <code>/listkey</code> – Xem danh sách key\n"
        "🗑 <code>/clearkey</code>– Xoá key chưa dùng"
    ) if is_admin else ""

    auth_note = (
        "✅ <i>Bạn đã xác thực – sẵn sàng sử dụng</i>"
        if authed else
        "🔐 <i>Chưa xác thực – dùng /key để nhập key</i>"
    )

    text = (
        "🔥 <b>GLORY FF BOT</b> 🔥\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"{auth_note}\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        "📋 <b>Lệnh người dùng:</b>\n\n"
        "🔑 <code>/key &lt;KEY&gt;</code>          – Nhập key xác thực\n"
        "🏰 <code>/join_cl &lt;clan_id&gt;</code>  – Tham gia quân đoàn\n"
        "▶️ <code>/run</code>                – Khởi động farming\n"
        "🔄 <code>/restart</code>            – Restart bộ 4 bot của bạn\n"
        "📊 <code>/status</code>             – Xem trạng thái\n"
        "🛑 <code>/stop</code>               – Dừng phiên"
        f"{admin_cmds}\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"<i>⏱ Tin nhắn tự xoá sau 30s</i>"
    )
    m = _send(msg.chat.id, text, auto_del=False)
    _auto_delete(msg.chat.id, m.message_id, 30)


# ── /key <KEY> – người dùng nhập key ───────────────────────────────────
@bot.message_handler(commands=["key"])
def cmd_key(msg: types.Message):
    _del_cmd(msg, 2)   # xoá ngay để không lộ key
    user_id = msg.from_user.id
    chat_id = msg.chat.id

    if user_id == ADMIN_ID:
        _send(chat_id, "👑 <b>Admin không cần key!</b>\nBạn đã có toàn quyền truy cập.")
        return

    parts = msg.text.strip().split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        _send(chat_id,
              "⚠️ <b>Sai cú pháp!</b>\n"
              "Dùng: <code>/key YOUR_KEY_HERE</code>")
        return

    result = key_mgr.redeem(user_id, parts[1].strip())

    if result == "ok":
        _send(chat_id,
              "✅ <b>Xác thực thành công!</b>\n"
              "━━━━━━━━━━━━━━━━━━━━━━━━\n"
              "🎉 Key hợp lệ – bạn đã có quyền dùng bot.\n"
              "💡 Dùng <code>/start</code> để xem danh sách lệnh.")
    elif result == "already_authed":
        _send(chat_id,
              "ℹ️ <b>Bạn đã xác thực trước đó rồi!</b>\n"
              "✅ Tiếp tục sử dụng bot bình thường.")
    elif result == "used":
        _send(chat_id,
              "❌ <b>Key đã được sử dụng!</b>\n"
              "Mỗi key chỉ dùng được 1 lần.\n"
              "💡 Liên hệ admin để lấy key mới.")
    else:  # invalid
        _send(chat_id,
              "❌ <b>Key không hợp lệ!</b>\n"
              "Kiểm tra lại key hoặc liên hệ admin.")


# ── /genkey – admin tạo key ─────────────────────────────────────────────
@bot.message_handler(commands=["genkey"])
def cmd_genkey(msg: types.Message):
    _del_cmd(msg, 3)
    if msg.from_user.id != ADMIN_ID:
        _send(msg.chat.id, "⛔ <b>Lệnh này chỉ dành cho Admin!</b>")
        return

    key = key_mgr.generate()
    text = (
        "🔑 <b>KEY MỚI ĐÃ TẠO</b>\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"<code>{key}</code>\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        "⚠️ <i>Key chỉ dùng được 1 lần duy nhất</i>\n"
        f"<i>⏱ Tin nhắn tự xoá sau {MSG_DELETE_SEC}s</i>"
    )
    _send(msg.chat.id, text)
    log.info(f"[admin] genkey → {key}")


# ── /listkey – admin xem danh sách key ──────────────────────────────────
@bot.message_handler(commands=["listkey"])
def cmd_listkey(msg: types.Message):
    _del_cmd(msg, 3)
    if msg.from_user.id != ADMIN_ID:
        _send(msg.chat.id, "⛔ <b>Lệnh này chỉ dành cho Admin!</b>")
        return

    info = key_mgr.list_keys()
    avail_lines = "\n".join(f"  🟢 <code>{k}</code>" for k in info["available"]) or "  <i>Không có</i>"
    used_lines  = "\n".join(f"  🔴 <code>{k}</code>" for k in info["used"])      or "  <i>Không có</i>"

    _send(msg.chat.id,
          f"🗂 <b>DANH SÁCH KEY</b>\n"
          f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
          f"🟢 Còn dùng được ({len(info['available'])}):\n{avail_lines}\n\n"
          f"🔴 Đã dùng ({len(info['used'])}):\n{used_lines}\n"
          f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
          f"<i>⏱ Tin nhắn tự xoá sau {MSG_DELETE_SEC}s</i>")


# ── /clearkey – admin xoá key chưa dùng ─────────────────────────────────
@bot.message_handler(commands=["clearkey"])
def cmd_clearkey(msg: types.Message):
    _del_cmd(msg, 3)
    if msg.from_user.id != ADMIN_ID:
        _send(msg.chat.id, "⛔ <b>Lệnh này chỉ dành cho Admin!</b>")
        return

    n = key_mgr.revoke_all_unused()
    _send(msg.chat.id,
          f"🗑 <b>Đã xoá {n} key chưa sử dụng!</b>\n"
          f"<i>Key đã dùng vẫn được giữ lại trong log.</i>")


# ── /join_cl <clan_id> ───────────────────────────────────────────────────
@bot.message_handler(commands=["join_cl"])
def cmd_join_clan(msg: types.Message):
    if not _require_auth(msg):
        return
    _del_cmd(msg, 3)
    user_id = msg.from_user.id
    chat_id = msg.chat.id

    parts = msg.text.strip().split()
    if len(parts) < 2 or not parts[1].isdigit():
        _send(chat_id,
              "⚠️ <b>Sai cú pháp!</b>\n"
              "Dùng: <code>/join_cl &lt;clan_id&gt;</code>\n"
              "Ví dụ: <code>/join_cl 3105683920</code>")
        return

    clan_id = parts[1]

    if sessions.has_session(user_id):
        sess   = sessions.get_session(user_id)
        status = sess["status"] if sess else "?"
        _send(chat_id,
              f"⏳ <b>Bạn đang có phiên đang chạy!</b>\n"
              f"🔄 Trạng thái: <b>{status}</b>\n"
              f"💡 Dùng <code>/stop</code> để hủy hoặc <code>/restart</code> để khởi động lại.")
        return

    if not sessions.is_free_enough():
        _send(chat_id,
              f"❌ <b>Không đủ bot account!</b>\n"
              f"📦 Cần: <b>{BOT_ACCOUNTS_PER_USER}</b> | Còn trống: <b>{sessions.free()}</b>\n"
              f"⏳ Chờ người dùng khác hoàn thành hoặc liên hệ admin.")
        return

    accounts = sessions.acquire(user_id, clan_id)
    if not accounts:
        _send(chat_id, "❌ <b>Không thể khởi tạo phiên.</b> Thử lại sau.")
        return

    sessions.set_field(user_id, "chat_id", chat_id)

    uid_list = "\n".join(f"  🤖 <code>{a['uid']}</code>" for a in accounts)
    info_msg = _send(chat_id,
        f"🏰 <b>THAM GIA QUÂN ĐOÀN</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🆔 Clan ID: <code>{clan_id}</code>\n"
        f"🤖 Bot accounts:\n{uid_list}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"⏳ <i>Đang xử lý... vui lòng chờ</i>",
        auto_del=False
    )
    _auto_delete(chat_id, info_msg.message_id, 60)

    t = threading.Thread(
        target=_join_worker,
        args=(user_id, chat_id, clan_id, accounts),
        daemon=True,
        name=f"JoinWorker-{user_id}"
    )
    sessions.set_field(user_id, "thread", t)
    t.start()
    log.info(f"[user={user_id}] join_cl started clan={clan_id}")


# ── /restart – restart đúng bộ 4 bot của user đó ───────────────────────
@bot.message_handler(commands=["restart"])
def cmd_restart(msg: types.Message):
    if not _require_auth(msg):
        return
    _del_cmd(msg, 3)
    user_id = msg.from_user.id
    chat_id = msg.chat.id

    sess = sessions.get_session(user_id)
    if not sess:
        _send(chat_id,
              "ℹ️ <b>Bạn chưa có phiên nào đang chạy.</b>\n"
              "Dùng <code>/join_cl &lt;clan_id&gt;</code> để bắt đầu.")
        return

    # Lấy thông tin phiên hiện tại TRƯỚC khi release
    clan_id  = sess["clan_id"]
    accounts = sess["accounts"]   # giữ lại đúng bộ 4 account của user này
    indices  = sess["indices"]
    status   = sess.get("status", "?")

    # Nếu thread cũ còn chạy, để nó tự kết thúc (không force kill)
    old_thread = sess.get("thread")

    # Thông báo đang restart
    uid_list = "\n".join(f"  🤖 <code>{a['uid']}</code>" for a in accounts)
    _send(chat_id,
          f"🔄 <b>ĐANG RESTART PHIÊN</b>\n"
          f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
          f"🆔 Clan ID: <code>{clan_id}</code>\n"
          f"📌 Trạng thái cũ: <b>{status}</b>\n"
          f"🤖 Accounts giữ nguyên:\n{uid_list}\n"
          f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
          f"⏳ <i>Đang khởi động lại...</i>")

    # Giải phóng session cũ nhưng GIỮ NGUYÊN indices (không trả về pool)
    # → tái sử dụng đúng bộ account đó cho user này
    with sessions._lock:
        sessions._sessions.pop(user_id, None)
        # Tái đăng ký session với cùng bộ account
        sessions._sessions[user_id] = {
            "clan_id"   : clan_id,
            "indices"   : indices,
            "accounts"  : accounts,
            "chat_id"   : chat_id,
            "started_at": time.time(),
            "thread"    : None,
            "status"    : "RESTARTING",
            "results"   : [],
        }

    # Chạy lại worker với đúng bộ account đó
    t = threading.Thread(
        target=_join_worker,
        args=(user_id, chat_id, clan_id, accounts),
        daemon=True,
        name=f"JoinWorker-{user_id}-restart"
    )
    sessions.set_field(user_id, "thread", t)
    t.start()
    log.info(f"[user={user_id}] restart clan={clan_id} accounts={[a['uid'] for a in accounts]}")


# ── /run ─────────────────────────────────────────────────────────────────
@bot.message_handler(commands=["run"])
def cmd_run(msg: types.Message):
    if not _require_auth(msg):
        return
    _del_cmd(msg, 3)
    chat_id = msg.chat.id

    if _glory_is_running():
        _send(chat_id,
              "▶️ <b>Glory FF đang chạy!</b>\n"
              "✅ Hệ thống farming đã hoạt động.\n\n"
              f"📊 {sessions.summary()}")
        return

    total = sessions.total()
    if total == 0:
        _send(chat_id,
              "❌ <b>Không tìm thấy account nào!</b>\n"
              "📂 Kiểm tra file <code>accounts.json</code> trên VPS.")
        return

    notice = _send(chat_id,
                   f"⏳ <b>Đang khởi động Glory FF...</b>\n"
                   f"📦 Tải <b>{total}</b> account từ file\n"
                   f"<i>Vui lòng chờ vài giây...</i>",
                   auto_del=False)

    _start_glory_runner()

    for _ in range(10):
        time.sleep(0.5)
        if _glory_is_running():
            break

    try:
        bot.delete_message(chat_id, notice.message_id)
    except Exception:
        pass

    if _glory_is_running():
        _send(chat_id,
              f"✅ <b>GLORY FF ĐÃ KHỞI ĐỘNG!</b>\n"
              f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
              f"🤖 Accounts đã tải : <b>{total}</b>\n"
              f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
              f"<i>⏱ Tin nhắn tự xoá sau {MSG_DELETE_SEC}s</i>")
    else:
        _send(chat_id,
              "❌ <b>Khởi động thất bại!</b>\n"
              "📋 Kiểm tra <code>glory_bot.log</code> để xem lỗi.")


# ── /status ──────────────────────────────────────────────────────────────
@bot.message_handler(commands=["status"])
def cmd_status(msg: types.Message):
    if not _require_auth(msg):
        return
    _del_cmd(msg, 3)
    user_id = msg.from_user.id
    chat_id = msg.chat.id

    glory_st = "🟢 Đang chạy" if _glory_is_running() else "🔴 Chưa khởi động"
    sess     = sessions.get_session(user_id)

    if sess:
        elapsed  = int(time.time() - sess.get("started_at", time.time()))
        uid_list = " | ".join(f"<code>{a['uid']}</code>" for a in sess["accounts"])
        my_sess  = (
            f"\n👤 <b>Phiên của bạn:</b>\n"
            f"  🏰 Clan ID  : <code>{sess['clan_id']}</code>\n"
            f"  🔄 Trạng thái: <b>{sess['status']}</b>\n"
            f"  ⏱ Thời gian : <b>{elapsed}s</b>\n"
            f"  🤖 Accounts : {uid_list}"
        )
    else:
        my_sess = "\n👤 <b>Phiên của bạn:</b> Không có"

    _send(chat_id,
          f"📊 <b>TRẠNG THÁI HỆ THỐNG</b>\n"
          f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
          f"⚙️ Glory FF: {glory_st}\n\n"
          f"🗂 <b>Bot Accounts:</b>\n"
          f"  {sessions.summary().replace(chr(10), chr(10)+'  ')}"
          f"{my_sess}\n"
          f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
          f"<i>⏱ Tin nhắn tự xoá sau {MSG_DELETE_SEC}s</i>")


# ── /stop ─────────────────────────────────────────────────────────────────
@bot.message_handler(commands=["stop"])
def cmd_stop(msg: types.Message):
    if not _require_auth(msg):
        return
    _del_cmd(msg, 3)
    user_id = msg.from_user.id
    chat_id = msg.chat.id

    if not sessions.has_session(user_id):
        _send(chat_id,
              "ℹ️ <b>Không có phiên nào đang chạy.</b>\n"
              "Dùng <code>/join_cl &lt;clan_id&gt;</code> để bắt đầu.")
        return

    sessions.release(user_id)
    _send(chat_id,
          "🛑 <b>Phiên đã được hủy!</b>\n"
          "✅ Các bot account đã được giải phóng.\n"
          "💡 Dùng <code>/join_cl</code> để bắt đầu phiên mới.")
    log.info(f"[user={user_id}] session stopped manually")


# ── Fallback ─────────────────────────────────────────────────────────────
@bot.message_handler(func=lambda m: True)
def fallback(msg: types.Message):
    _del_cmd(msg, 5)
    _send(msg.chat.id,
          "❓ <b>Lệnh không hợp lệ!</b>\n"
          "Gõ <code>/start</code> để xem danh sách lệnh.")


# ═══════════════════════════════════════════════════════════════════════════
#  Entry point
# ═══════════════════════════════════════════════════════════════════════════
def _notify_restored():
    """
    Sau khi bot polling sẵn sàng, gửi thông báo cho các user
    có session bị gián đoạn (INTERRUPTED) vì bot offline/restart.
    Chạy trong thread riêng để không block polling.
    """
    interrupted = sessions.restored_sessions()
    if not interrupted:
        return

    time.sleep(3)   # chờ polling ổn định
    for user_id, sess in interrupted:
        chat_id = sess.get("chat_id")
        if not chat_id:
            continue
        clan_id  = sess.get("clan_id", "?")
        uid_list = "\n".join(
            f"  🤖 <code>{a['uid']}</code>" for a in sess.get("accounts", [])
        )
        try:
            _send(chat_id,
                  f"⚠️ <b>BOT ĐÃ ĐƯỢC KHỞI ĐỘNG LẠI</b>\n"
                  f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
                  f"♻️ Phiên của bạn đã được khôi phục:\n"
                  f"🏰 Clan ID: <code>{clan_id}</code>\n"
                  f"🤖 Accounts giữ nguyên:\n{uid_list}\n"
                  f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
                  f"💡 Dùng <code>/restart</code> để chạy lại\n"
                  f"💡 Dùng <code>/stop</code> để huỷ phiên",
                  auto_del=False)
        except Exception as e:
            log.error(f"[notify_restored] user={user_id}: {e}")


if __name__ == "__main__":
    total = sessions.total()
    print("🔥  Glory FF Bot khởi động")
    print(f"👑  Admin ID       : {ADMIN_ID}")
    print(f"📦  Bot accounts   : {total}")
    print(f"🔑  Keys file      : {KEYS_FILE}")
    print(f"💾  Sessions file  : {SESSIONS_FILE}")
    print(f"⏱   Auto-delete    : {MSG_DELETE_SEC}s")
    print(f"🤖  Account/phiên  : {BOT_ACCOUNTS_PER_USER}")
    print(f"🌐  Polling Telegram...")
    print("─" * 42)

    if total == 0:
        print("⚠️  accounts.json trống hoặc không tìm thấy!")
    if total < BOT_ACCOUNTS_PER_USER:
        print(f"⚠️  Chỉ có {total} account, cần tối thiểu {BOT_ACCOUNTS_PER_USER}!")

    # Thông báo session bị gián đoạn sau khi polling sẵn sàng
    threading.Thread(target=_notify_restored, daemon=True, name="NotifyRestored").start()

    try:
        bot.infinity_polling(timeout=30, long_polling_timeout=20)
    except KeyboardInterrupt:
        print("\n🛑  Bot đã dừng.")
