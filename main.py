import asyncio
import base64
import json
import os
import hashlib
import hmac
import secrets
import string
import time
import aiofiles
from contextlib import asynccontextmanager
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
from urllib.parse import quote
from collections import deque, defaultdict
from pathlib import Path

from fastapi import FastAPI, Request, HTTPException, WebSocket, WebSocketDisconnect, Depends
from fastapi.responses import Response, HTMLResponse, JSONResponse, RedirectResponse
from fastapi.middleware.cors import CORSMiddleware
import uvicorn
from concurrent.futures import ThreadPoolExecutor
import httpx
import logging
import re

# Fix __main__ vs main circular-import behavior
import sys as _sys
if __name__ == "__main__" and "main" not in _sys.modules:
    _sys.modules["main"] = _sys.modules["__main__"]

# Console log level. Per-connection chatter (client connected / target opened /
# socket closed) is logged at DEBUG, so by default the console only shows
# startup info plus real warnings and errors. Set LOG_LEVEL=DEBUG to see everything.
_LOG_LEVEL = os.environ.get("LOG_LEVEL", "INFO").strip().upper()
logging.basicConfig(
    level=getattr(logging, _LOG_LEVEL, logging.INFO),
    format="%(asctime)s [%(levelname)s] %(message)s",
)
logger = logging.getLogger("OMIDIRAN_PANEL")

_NORM_RE = [
    (re.compile(r"\[[^\]]{0,40}\]"), "[]"),                                  # [conn_id], [ip]
    (re.compile(r"\b[0-9a-fA-F]{8}-[0-9a-fA-F-]{27}\b"), "<uuid>"),           # full uuid
    (re.compile(r"\b\d{1,3}(?:\.\d{1,3}){3}\b"), "<ip>"),                    # ipv4
    (re.compile(r"\b[0-9a-fA-F]{6,}\b"), "<id>"),                             # hex ids
    (re.compile(r"\d+"), "#"),                                                # numbers / ports
]

def normalize_log_text(text: str) -> str:
    """Collapse ids / IPs / numbers so that repeated messages share one key."""
    t = str(text or "")
    for rx, rep in _NORM_RE:
        t = rx.sub(rep, t)
    return re.sub(r"\s+", " ", t).strip().lower()[:300]

class _RepeatFilter(logging.Filter):
    """Console: print a repeated WARNING/ERROR once, then summarise how many were hidden."""
    def __init__(self, window: float = 60.0):
        super().__init__()
        self.window = window
        self.seen: dict = {}

    def filter(self, record: logging.LogRecord) -> bool:
        if record.levelno < logging.WARNING:
            return True
        try:
            msg = record.getMessage()
            key = (record.name, record.levelno, normalize_log_text(msg))
            now = time.monotonic()
            ent = self.seen.get(key)
            if ent and now - ent[0] < self.window:
                ent[1] += 1
                return False
            if ent and ent[1]:
                record.msg = f"{msg}  (+{ent[1]} similar in the last {int(now - ent[0])}s)"
                record.args = ()
            self.seen[key] = [now, 0]
            if len(self.seen) > 500:
                cutoff = now - self.window
                self.seen = {k: v for k, v in self.seen.items() if v[0] >= cutoff}
        except Exception:
            pass
        return True

class _UvicornNoiseFilter(logging.Filter):
    """Hide uvicorn's per-request access lines and per-websocket open/close lines."""
    _DROP = ("connection open", "connection closed", "[accepted]", "WebSocket /")

    def filter(self, record: logging.LogRecord) -> bool:
        if record.levelno >= logging.WARNING:
            return True
        if _LOG_LEVEL == "DEBUG":
            return True
        if record.name == "uvicorn.access":
            try:  # args = (client, method, path, http_version, status_code)
                return int(record.args[4]) >= 500
            except Exception:
                return False
        msg = record.getMessage()
        return not any(tok in msg for tok in self._DROP)

def _quiet_third_party_loggers() -> None:
    # httpx logs one INFO line per outgoing request (Telegram bot polling, server-info
    # lookups, ...) and the URL can contain the bot token -> keep them off the console.
    if _LOG_LEVEL == "DEBUG":
        return
    for name in ("httpx", "httpcore", "websockets", "websockets.server", "asyncio"):
        logging.getLogger(name).setLevel(logging.WARNING)

def _install_console_filters() -> None:
    _quiet_third_party_loggers()
    for h in logging.getLogger().handlers:
        for f in [f for f in h.filters if isinstance(f, _RepeatFilter)]:
            h.removeFilter(f)
        h.addFilter(_RepeatFilter())
    for name in ("uvicorn", "uvicorn.error", "uvicorn.access"):
        lg = logging.getLogger(name)
        for f in [f for f in lg.filters if isinstance(f, _UvicornNoiseFilter)]:
            lg.removeFilter(f)
        lg.addFilter(_UvicornNoiseFilter())

_install_console_filters()

IRAN_TZ = ZoneInfo("Asia/Tehran")

# ══ Browser vs Client detection ══
import re as _re

_BROWSER_UA_RE = _re.compile(
    r"Mozilla|Chrome|Firefox|Safari|Edge|Opera|Brave|Vivaldi|MSIE|Trident|SamsungBrowser|MiuiBrowser|OPR/|YaBrowser|DuckDuckBot",
    _re.IGNORECASE
)
_CLIENT_UA_HINTS = (
    "v2ray", "nekobox", "neko", "clash", "sing-box", "singbox", "streisand",
    "shadowrocket", "hiddify", "foxray", "mihomo", "surge", "quantumult",
    "loon", "stash", "v2rayn", "shadowsocks", "trojan", "okhttp",
    "python-requests", "go-http-client", "curl", "wget", "postmanruntime",
    "telegrambot", "axios", "node-fetch", "deno", "bun",
)

def is_browser_request(request: Request) -> bool:
    """Detect whether a request came from a browser or a proxy client.
    Browser → True → HTML UI; client → False → base64."""
    ua = (request.headers.get("user-agent") or "").strip()
    if not ua:
        return False  # Empty UA is treated as a client
    
    ua_low = ua.lower()
    
    # Client hint detected → treat as client
    for hint in _CLIENT_UA_HINTS:
        if hint in ua_low:
            return False
    
    # Accept: text/html → treat as browser
    accept = (request.headers.get("accept") or "").lower()
    if "text/html" in accept:
        return True
    
    # Browser-like UA → treat as browser
    if _BROWSER_UA_RE.search(ua):
        return True
    
    # Otherwise treat as client
    return False

# ── Startup / Shutdown ────────────────────────────────────────────────────────
@asynccontextmanager
async def lifespan(app: FastAPI):
    """Application lifespan with verified persistent state and periodic autosave."""
    global http_client, autosave_task
    # ── Startup ──
    limits = httpx.Limits(max_connections=500, max_keepalive_connections=100)
    timeout = httpx.Timeout(30.0, connect=10.0)
    http_client = httpx.AsyncClient(
        limits=limits, timeout=timeout, follow_redirects=True,
    )

    # Persistence must be available before the panel starts serving traffic.
    await verify_persistence()
    await load_state()
    await _tg_start_bot()
    autosave_task = asyncio.create_task(_autosave_loop(), name="omid-state-autosave")
    log_activity("system", "Server started", "ok")
    logger.info(
        f"OMID-IRAN PANEL v3.0.0 started on port {CONFIG['port']} "
        f"| DATA_DIR={DATA_DIR} | STATE_FILE={DATA_FILE}"
    )

    yield  # Application runs while suspended here

    # ── Shutdown ──
    if autosave_task:
        autosave_task.cancel()
        try:
            await autosave_task
        except asyncio.CancelledError:
            pass
        autosave_task = None

    # Final synchronous save before the process exits.
    await save_state()
    await _tg_stop_bot()
    if http_client:
        await http_client.aclose()

app = FastAPI(
    title="OMID-IRAN PANEL",
    docs_url=None,
    redoc_url=None,
    lifespan=lifespan,  # FastAPI lifespan handler
)

# ── Persistence ───────────────────────────────────────────────────────────────
_configured_data_dir = (os.environ.get("DATA_DIR") or "/data").strip()
DATA_DIR = Path(_configured_data_dir).expanduser()
DATA_FILE = DATA_DIR / "gateway_state.json"
SECRET_FILE = DATA_DIR / "gateway_secret.key"
SAVE_LOCK = asyncio.Lock()
autosave_task: asyncio.Task | None = None
try:
    PERSISTENCE_INTERVAL = max(5, int(os.environ.get("PERSISTENCE_INTERVAL", "15")))
except (TypeError, ValueError):
    PERSISTENCE_INTERVAL = 15

def _load_or_create_secret() -> str:
    """Persist SECRET_KEY so passwords and sessions remain stable across restarts.
    If SECRET_KEY is not provided through the environment, a generated secret is
    stored on disk and reused on subsequent service restarts."""
    env_secret = os.environ.get("SECRET_KEY")
    if env_secret:
        return env_secret
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        if SECRET_FILE.exists():
            existing = SECRET_FILE.read_text(encoding="utf-8").strip()
            if existing:
                return existing
        new_secret = secrets.token_urlsafe(32)
        SECRET_FILE.write_text(new_secret, encoding="utf-8")
        return new_secret
    except Exception as e:
        logger.warning(f"Could not persist SECRET_KEY, sessions/password may reset on restart: {e}")
        return secrets.token_urlsafe(32)

CONFIG = {
    "port": int(os.environ.get("PORT", 8000)),
    "secret": _load_or_create_secret(),
    "host": os.environ.get("RAILWAY_PUBLIC_DOMAIN", "localhost"),
}

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

_DISK_EXECUTOR = ThreadPoolExecutor(max_workers=1, thread_name_prefix="omid-disk")

def _dump_and_write_state(path: Path, data: dict) -> int:
    payload = json.dumps(data, ensure_ascii=False, indent=2)
    _write_state_file_sync(path, payload)
    return len(payload)

def _write_state_file_sync(path: Path, payload: str) -> None:
    """Atomically write state to disk and force it through the filesystem cache."""
    tmp = path.with_name(path.name + f".{os.getpid()}.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(payload)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)

    # fsync the directory entry as well. This is supported on Linux/Railway.
    try:
        dir_fd = os.open(str(path.parent), os.O_DIRECTORY)
    except (AttributeError, OSError):
        dir_fd = None
    if dir_fd is not None:
        try:
            os.fsync(dir_fd)
        finally:
            os.close(dir_fd)

async def verify_persistence() -> None:
    """Verify storage. On Vercel, fall back to its writable temporary directory.

    IMPORTANT: /tmp on Vercel is ephemeral and instance-local. This fallback only
    prevents startup from crashing; it does NOT provide durable/shared state. Use
    Railway with a mounted /data volume (or an external database) for production.
    """
    global DATA_DIR, DATA_FILE, SECRET_FILE

    async def probe_dir(path: Path) -> None:
        await asyncio.to_thread(path.mkdir, parents=True, exist_ok=True)
        probe = path / f".omid_persistence_probe_{os.getpid()}"
        await asyncio.to_thread(probe.write_text, "ok", encoding="utf-8")
        await asyncio.to_thread(probe.unlink)

    try:
        await probe_dir(DATA_DIR)
        logger.info(f"Persistence ready: {DATA_DIR} (state: {DATA_FILE})")
        return
    except OSError as e:
        logger.warning(f"Configured DATA_DIR is not writable ({DATA_DIR}): {e}")
        if not (os.environ.get("VERCEL") or os.environ.get("NOW_REGION")):
            logger.error(f"Persistent storage is NOT writable: {DATA_DIR}: {e}")
            raise RuntimeError(f"Persistent storage is not writable: {DATA_DIR}") from e

    # Vercel Functions have a read-only deployment filesystem; /tmp is writable
    # but temporary and not shared across instances. Never use /temp/data here.
    fallback = Path("/tmp/omid-panel-data")
    try:
        await probe_dir(fallback)
    except OSError as e:
        logger.exception("Vercel temporary storage is not writable either")
        raise RuntimeError("Neither configured DATA_DIR nor Vercel /tmp is writable") from e

    DATA_DIR = fallback
    DATA_FILE = DATA_DIR / "gateway_state.json"
    SECRET_FILE = DATA_DIR / "gateway_secret.key"
    logger.warning(
        "Using ephemeral Vercel storage at %s. State may disappear between invocations; "
        "this is a startup workaround, not durable production storage.", DATA_DIR
    )

async def load_state():
    global LINKS, AUTH, SUBS
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        if not DATA_FILE.exists():
            logger.info(f"No saved state found at {DATA_FILE}; starting with fresh state")
            return

        async with aiofiles.open(DATA_FILE, "r", encoding="utf-8") as f:
            raw = await f.read()
        data = json.loads(raw)

        LINKS.update(data.get("links", {}))
        # Migrate protocol values from older panel builds.
        for _uid, _link in LINKS.items():
            _link["protocol"] = normalize_protocol(_link.get("protocol"))
            if _link.get("protocol", "").startswith("trojan-") and not _link.get("password"):
                _link["password"] = generate_trojan_password()
        SUBS.update(data.get("subs", {}))
        if "username" in data and str(data["username"]).strip():
            AUTH["username"] = str(data["username"]).strip()
        if "password_hash" in data:
            AUTH["password_hash"] = data["password_hash"]
        if "telegram" in data:
            tg = data["telegram"]
            if "bot_token" in tg:
                TELEGRAM["bot_token"] = str(tg.get("bot_token") or "").strip()
            if "admin_ids" in tg:
                TELEGRAM["admin_ids"] = str(tg.get("admin_ids") or "").strip()
            TELEGRAM["enabled"] = bool(TELEGRAM["bot_token"])
        logger.info(
            f"State loaded: {len(LINKS)} links, {len(SUBS)} subs "
            f"from {DATA_FILE}"
        )
    except Exception as e:
        logger.exception(f"Could not load state from {DATA_FILE}: {e}")
        # Do not silently pretend persistence is healthy. The server can still
        # start, but the exact path/error is now visible in Railway logs.

async def save_state():
    """Persist the complete panel state atomically and durably."""
    async with SAVE_LOCK:
        try:
            DATA_DIR.mkdir(parents=True, exist_ok=True)

            # Snapshot under the same locks used by the mutation paths so a
            # concurrent request cannot produce a partial/inconsistent JSON file.
            async with LINKS_LOCK:
                links_snapshot = {k: dict(v) for k, v in LINKS.items()}
            async with SUBS_LOCK:
                subs_snapshot = {k: dict(v) for k, v in SUBS.items()}

            data = {
                "links": links_snapshot,
                "subs": subs_snapshot,
                "username": AUTH["username"],
                "password_hash": AUTH["password_hash"],
                "telegram": dict(TELEGRAM),
                "saved_at": datetime.now().isoformat(),
            }
            # Serialize + fsync on a DEDICATED single thread. Using the default
            # executor here let slow fsyncs on the Railway volume starve the
            # threads that asyncio.open_connection() needs for DNS lookups,
            # which froze every relay (WS and XHTTP) at the same time.
            loop = asyncio.get_running_loop()
            size = await loop.run_in_executor(
                _DISK_EXECUTOR, _dump_and_write_state, DATA_FILE, data
            )
            logger.debug(f"State saved: {DATA_FILE} ({size} bytes)")
        except Exception as e:
            logger.exception(f"Could not save state to {DATA_FILE}: {e}")

# ── Coalesced, non-blocking save (used by relays on every connection close) ──
# Previously every closed tunnel spawned its own full save_state() (JSON dump +
# fsync of file and directory). Under normal browsing that is dozens of full
# rewrites per second, which starves the event loop/threads and made all
# tunnels stall together. request_save() merges any burst into ONE write.
SAVE_DEBOUNCE = 2.0
_save_task: asyncio.Task | None = None

async def _debounced_save() -> None:
    await asyncio.sleep(SAVE_DEBOUNCE)
    await save_state()

def request_save() -> None:
    """Schedule a state save without blocking; bursts collapse into one write.
    Must be called from the event loop. The periodic autosave remains the
    safety net for anything that changes while a save is already running."""
    global _save_task
    if _save_task is not None and not _save_task.done():
        return
    _save_task = asyncio.create_task(_debounced_save(), name="omid-state-save")

async def _autosave_loop() -> None:
    """Periodic safety net for abrupt deploy/restart cases where shutdown hooks
    are not given enough time to run."""
    while True:
        await asyncio.sleep(PERSISTENCE_INTERVAL)
        await save_state()

# ── In-memory state ───────────────────────────────────────────────────────────
connections: dict = {}
stats = {
    "total_bytes": 0,
    "total_requests": 0,
    "total_errors": 0,
    "start_time": time.time(),
}
class ErrorLog:
    """
    Grouped error store (drop-in for the old deque: .append(dict), iteration, len).
    Identical errors (after normalising ids / IPs / numbers) are merged into one
    entry with a counter, first_time and last time, instead of flooding the list.
    """
    def __init__(self, maxlen: int = 150):
        self._items: deque = deque(maxlen=maxlen)
        self._index: dict = {}
        self._seq = 0

    def append(self, item: dict) -> None:
        try:
            msg = str(item.get("error", ""))[:600]
            src = str(item.get("type") or item.get("source") or "app")
            level = str(item.get("level") or "error")
            now = datetime.now().isoformat()
            key = (src, normalize_log_text(msg))
            ent = self._index.get(key)
            if ent is not None and ent in self._items:
                ent["count"] += 1
                ent["time"] = now
                ent["error"] = msg          # keep the most recent raw text
                if level == "error":
                    ent["level"] = "error"
                self._items.remove(ent)
                self._items.append(ent)
                return
            self._seq += 1
            ent = {
                "id": self._seq, "error": msg, "type": src, "level": level,
                "url": item.get("url"), "count": 1, "first_time": now, "time": now,
            }
            self._items.append(ent)
            self._index[key] = ent
            if len(self._index) > 600:       # drop index rows whose entry was evicted
                self._index = {k: v for k, v in self._index.items() if v in self._items}
        except Exception:
            pass

    def clear(self) -> None:
        self._items.clear()
        self._index.clear()

    def __iter__(self):
        return iter(list(self._items))

    def __len__(self):
        return len(self._items)

error_logs = ErrorLog()
activity_logs: deque = deque(maxlen=500)
_activity_index: dict = {}
_activity_seq = 0
ACTIVITY_DEDUPE_WINDOW = 600            # seconds: identical events are merged
CONNECTION_LOG_COOLDOWN = 6 * 3600      # seconds: one "connected" entry per IP+config

class _PanelErrorHandler(logging.Handler):
    """Mirror real WARNING/ERROR records of the app into the panel's Errors tab."""
    def emit(self, record: logging.LogRecord) -> None:
        try:
            if record.levelno < logging.WARNING:
                return
            src = record.name.split(".")[-1].lower()
            src = "app" if src == "omidiran_panel" else src
            error_logs.append({
                "error": record.getMessage(),
                "type": src,
                "level": "error" if record.levelno >= logging.ERROR else "warn",
            })
        except Exception:
            pass

def _install_panel_error_handler() -> None:
    lg = logging.getLogger("OMIDIRAN_PANEL")
    for h in [h for h in lg.handlers if isinstance(h, _PanelErrorHandler)]:
        lg.removeHandler(h)
    lg.addHandler(_PanelErrorHandler(level=logging.WARNING))

_install_panel_error_handler()
hourly_traffic: dict = defaultdict(int)
http_client: httpx.AsyncClient | None = None
LINKS: dict = {}
LINKS_LOCK = asyncio.Lock()
SUBS: dict = {}
SUBS_LOCK = asyncio.Lock()

# ── Telegram bot config (managed from the panel) ──────────────────
TELEGRAM = {
    "bot_token": os.environ.get("TELEGRAM_BOT_TOKEN", "").strip(),
    "admin_ids": os.environ.get("TELEGRAM_ADMIN_IDS", "").strip(),
    "enabled": bool(os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()),
}

# Supported protocols for each config
PROTOCOLS = (
    "vless-ws", "vless-xhttp-packet-up", "vless-xhttp-stream-up",
    "vmess-ws", "vmess-xhttp-packet-up", "vmess-xhttp-stream-up",
    "trojan-ws", "trojan-xhttp-packet-up", "trojan-xhttp-stream-up",
)
DEFAULT_PROTOCOL = "vless-ws"

# Compatibility aliases for old saved links. Older builds used the transport
# name by itself for VLESS/XHTTP. We normalize those values to the explicit
# protocol+transport form during state load.
_PROTOCOL_ALIASES = {
    "xhttp-packet-up": "vless-xhttp-packet-up",
    "xhttp-stream-up": "vless-xhttp-stream-up",
    "xhttp-stream-one": "vless-xhttp-stream-up",
}

def normalize_protocol(value: str | None) -> str:
    p = str(value or DEFAULT_PROTOCOL).strip().lower()
    p = _PROTOCOL_ALIASES.get(p, p)
    return p if p in PROTOCOLS else DEFAULT_PROTOCOL

def split_protocol(protocol: str | None) -> tuple[str, str]:
    p = normalize_protocol(protocol)
    for family in ("vless", "vmess", "trojan"):
        if p == f"{family}-ws":
            return family, "ws"
        prefix = f"{family}-xhttp-"
        if p.startswith(prefix):
            return family, p[len(prefix):]
    return "vless", "ws"

def protocol_label(protocol: str | None) -> str:
    family, transport = split_protocol(protocol)
    fam = {"vless":"VLESS", "vmess":"VMess", "trojan":"Trojan"}.get(family, family.upper())
    tr = "WebSocket" if transport == "ws" else f"XHTTP · {transport}"
    return f"{fam} · {tr}"

# Selectable uTLS fingerprints for each config
FINGERPRINTS = ("chrome", "firefox", "safari", "ios", "android", "edge", "360", "qq", "random", "randomized")
DEFAULT_FINGERPRINT = "chrome"

# Default ALPN by transport when no manual value is supplied
DEFAULT_ALPN_BY_PROTOCOL = {
    "vless-ws": "http/1.1",
    "vless-xhttp-packet-up": "h2,http/1.1",
    "vless-xhttp-stream-up": "h2,http/1.1",
    "vmess-ws": "http/1.1",
    "vmess-xhttp-packet-up": "h2,http/1.1",
    "vmess-xhttp-stream-up": "h2,http/1.1",
    "trojan-ws": "http/1.1",
    "trojan-xhttp-packet-up": "h2,http/1.1",
    "trojan-xhttp-stream-up": "h2,http/1.1",
}
DEFAULT_PORT = 443
MIN_PORT, MAX_PORT = 1, 65535

SUPPORT_URL = os.environ.get("SUPPORT_URL", "https://t.me/omid_gamingORG").strip()


# Speed limit (0 = unlimited); internal storage uses bytes per second
DEFAULT_SPEED_LIMIT = 0

def log_activity(kind: str, message: str, level: str = "info", *,
                 key=None, window: float | None = None, meta: dict | None = None):
    """
    Record a panel activity event.
    Identical events (same key, default = kind+level+message) inside `window`
    seconds are merged: the existing entry gets count+1 and a fresh timestamp
    instead of adding another line.
    """
    global _activity_seq
    now = datetime.now()
    iso = now.isoformat()
    win = ACTIVITY_DEDUPE_WINDOW if window is None else window
    k = key if key is not None else (kind, level, message)

    hit = _activity_index.get(k)
    if hit is not None and win > 0:
        ent, ts = hit
        if (now.timestamp() - ts) <= win and ent in activity_logs:
            ent["count"] += 1
            ent["time"] = iso
            ent["message"] = message
            activity_logs.remove(ent)
            activity_logs.append(ent)
            _activity_index[k] = (ent, now.timestamp())
            return

    _activity_seq += 1
    ent = {
        "id": _activity_seq, "kind": kind, "level": level, "message": message,
        "time": iso, "first_time": iso, "count": 1,
    }
    if meta:
        ent["meta"] = meta
    activity_logs.append(ent)
    _activity_index[k] = (ent, now.timestamp())
    if len(_activity_index) > 1500:
        for kk in [kk for kk, (e, _t) in _activity_index.items() if e not in activity_logs][:800]:
            _activity_index.pop(kk, None)

def log_connection(uid: str, label: str, ip: str, *, rejected: bool = False):
    """
    Connection events are very repetitive (every reconnect of every client).
    One entry per IP+config is kept and its counter is incremented instead.
    """
    if rejected:
        log_activity(
            "connection",
            f"اتصال {ip} به کانفیگ «{label}» رد شد (محدودیت تعداد آی‌پی)", "warn",
            key=("conn-rej", uid, ip), window=600, meta={"ip": ip, "label": label},
        )
    else:
        log_activity(
            "connection",
            f"اتصال جدید از {ip} (کانفیگ {label})", "info",
            key=("conn", uid, ip), window=CONNECTION_LOG_COOLDOWN, meta={"ip": ip, "label": label},
        )

# ── Auth ──────────────────────────────────────────────────────────────────────
SESSION_COOKIE = "gateway_session"
SESSION_TTL = 60 * 60 * 24 * 365

def hash_password(pw: str) -> str:
    return hashlib.sha256(f"{pw}{CONFIG['secret']}".encode()).hexdigest()

ADMIN_USERNAME_DEFAULT = os.environ.get("ADMIN_USERNAME", "omid").strip() or "omid"
ADMIN_PASSWORD_DEFAULT = os.environ.get("ADMIN_PASSWORD", "omid")
AUTH = {
    "username": ADMIN_USERNAME_DEFAULT,
    "password_hash": hash_password(ADMIN_PASSWORD_DEFAULT),
}
def _session_b64encode(value: bytes) -> str:
    """URL-safe base64 without padding, suitable for a cookie token."""
    return base64.urlsafe_b64encode(value).rstrip(b"=").decode("ascii")


def _session_b64decode(value: str) -> bytes:
    return base64.urlsafe_b64decode(value + "=" * (-len(value) % 4))


def _session_auth_fingerprint() -> str:
    """Bind sessions to the current credentials so password changes invalidate old cookies."""
    material = f"{AUTH['username']}\0{AUTH['password_hash']}".encode("utf-8")
    return hashlib.sha256(material).hexdigest()


async def create_session() -> str:
    """Create a stateless, signed session cookie.

    Unlike an in-memory session dictionary, this token can be verified by any
    Vercel Function instance as long as SECRET_KEY and credentials are the same.
    """
    payload = {
        "v": 1,
        "exp": int(time.time()) + SESSION_TTL,
        "nonce": secrets.token_urlsafe(18),
        "auth": _session_auth_fingerprint(),
    }
    encoded = _session_b64encode(json.dumps(payload, separators=(",", ":")).encode("utf-8"))
    signature = hmac.new(CONFIG["secret"].encode("utf-8"), encoded.encode("ascii"), hashlib.sha256).digest()
    return f"{encoded}.{_session_b64encode(signature)}"


async def is_valid_session(token: str | None) -> bool:
    """Verify the session locally without relying on per-instance RAM or disk."""
    if not token or token.count(".") != 1:
        return False
    encoded, supplied_sig = token.split(".", 1)
    try:
        signature = hmac.new(CONFIG["secret"].encode("utf-8"), encoded.encode("ascii"), hashlib.sha256).digest()
        if not hmac.compare_digest(_session_b64encode(signature), supplied_sig):
            return False
        payload = json.loads(_session_b64decode(encoded).decode("utf-8"))
        if not isinstance(payload, dict) or payload.get("v") != 1:
            return False
        if int(payload.get("exp", 0)) < int(time.time()):
            return False
        if not hmac.compare_digest(str(payload.get("auth", "")), _session_auth_fingerprint()):
            return False
        return bool(payload.get("nonce"))
    except (ValueError, TypeError, UnicodeError, json.JSONDecodeError, base64.binascii.Error):
        return False


async def destroy_session(token: str | None):
    # Stateless cookies cannot be revoked in server-side memory. Logout clears the
    # browser cookie; credential changes invalidate every prior token via fingerprint.
    return None

async def require_auth(request: Request):
    token = request.cookies.get(SESSION_COOKIE)
    if not await is_valid_session(token):
        raise HTTPException(status_code=401, detail="unauthorized")
    return token

# ── Helpers ───────────────────────────────────────────────────────────────────
def get_host(request: Request | None = None) -> str:
    """Resolve the public host from the request headers first, with the Railway domain as fallback.
    The observed host is cached in CONFIG for callers that do not have a request object."""
    if request is not None:
        h = request.headers.get("x-forwarded-host") or request.headers.get("host")
        if h:
            h = h.split(":")[0]
            CONFIG["host"] = h  # Cache the last observed public host for request-less callers
            return h
    return os.environ.get("RAILWAY_PUBLIC_DOMAIN", CONFIG["host"])

def get_scheme(request: Request | None = None) -> str:
    """Resolve the real request scheme (http/https), including proxy headers."""
    if request is not None:
        proto = request.headers.get("x-forwarded-proto") or request.url.scheme
        if proto:
            return proto.split(",")[0].strip()
    return "https"  # Production fallback

def generate_uuid() -> str:
    h = secrets.token_hex(16)
    return f"{h[:8]}-{h[8:12]}-{h[12:16]}-{h[16:20]}-{h[20:32]}"
    
def now_ir() -> datetime:
    return datetime.now(IRAN_TZ)

def generate_vless_link(
    uuid: str,
    host: str,
    remark: str = "Gateway",
    protocol: str = DEFAULT_PROTOCOL,
    fingerprint: str | None = None,
    alpn: str | None = None,
    port: int | None = None,
) -> str:
    """Generate a VLESS share-link for WS or XHTTP packet/stream-up."""
    protocol = normalize_protocol(protocol)
    family, transport = split_protocol(protocol)
    if family != "vless":
        protocol = "vless-ws"
        family, transport = "vless", "ws"

    fp = (fingerprint or DEFAULT_FINGERPRINT).strip() or DEFAULT_FINGERPRINT
    if fp not in FINGERPRINTS:
        fp = DEFAULT_FINGERPRINT
    alpn_val = (alpn or "").strip() or DEFAULT_ALPN_BY_PROTOCOL.get(protocol, "http/1.1")
    port_val = port or DEFAULT_PORT
    if not (MIN_PORT <= port_val <= MAX_PORT):
        port_val = DEFAULT_PORT

    if transport == "ws":
        path = f"/ws/{uuid}"
        params = {
            "encryption": "none",
            "security": "tls",
            "type": "ws",
            "host": host,
            "path": path,
            "sni": host,
            "fp": fp,
            "alpn": alpn_val,
        }
    else:
        path = f"/xhttp-siz10/{transport}/{uuid}"
        params = {
            "encryption": "none",
            "security": "tls",
            "type": "xhttp",
            "mode": transport,
            "host": host,
            "path": path,
            "sni": host,
            "fp": fp,
            "alpn": alpn_val,
        }
    query = "&".join(f"{k}={quote(str(v))}" for k, v in params.items())
    return f"vless://{uuid}@{host}:{port_val}?{query}#{quote(remark)}"

def build_vless_remark(link: dict) -> str:
    inbound = "OMID"
    email = (link.get("label") or "Config").strip()

    used = int(link.get("used_bytes", 0) or 0)
    total = int(link.get("limit_bytes", 0) or 0)

    traffic_used = fmt_bytes(used)

    if total > 0:
        traffic_total = fmt_bytes(total)
        traffic_left = fmt_bytes(max(0, total - used))
    else:
        traffic_total = "UNLIMITED"
        traffic_left = "UNLIMITED"

    expires_at = link.get("expires_at")

    if expires_at:
        try:
            exp_dt = datetime.fromisoformat(expires_at)
            remaining_seconds = (exp_dt - datetime.now()).total_seconds()
            days_left = max(0, int((remaining_seconds + 86399) // 86400))
            expire_date = exp_dt.strftime("%Y-%m-%d")
        except Exception:
            days_left = "?"
            expire_date = "N/A"
    else:
        days_left = "∞"
        expire_date = "UNLIMITED"

    return (
        f"{inbound}-{email} | "
        f"📊{traffic_used}/{traffic_total} | "
        f"💾{traffic_left} | "
        f"⏳{days_left}D | "
        f"📅{expire_date}"
    )

def generate_trojan_password(length: int = 32) -> str:
    """Generate a URL-safe Trojan password for a newly-created config."""
    alphabet = string.ascii_letters + string.digits + "-_"
    return "".join(secrets.choice(alphabet) for _ in range(max(16, int(length))))


def generate_trojan_link(
    password: str,
    host: str,
    remark: str = "Gateway",
    uuid: str | None = None,
    port: int | None = None,
    fingerprint: str | None = None,
    alpn: str | None = None,
    protocol: str = "trojan-ws",
) -> str:
    """Generate Trojan share-link for WebSocket or XHTTP."""
    protocol = normalize_protocol(protocol)
    family, transport = split_protocol(protocol)
    if family != "trojan":
        protocol = "trojan-ws"
        transport = "ws"

    port_val = port or DEFAULT_PORT
    if not (MIN_PORT <= port_val <= MAX_PORT):
        port_val = DEFAULT_PORT
    fp = (fingerprint or DEFAULT_FINGERPRINT).strip() or DEFAULT_FINGERPRINT
    if fp not in FINGERPRINTS:
        fp = DEFAULT_FINGERPRINT
    alpn_val = (alpn or "").strip() or DEFAULT_ALPN_BY_PROTOCOL.get(protocol, "http/1.1")
    path = f"/trojan/{uuid}" if transport == "ws" and uuid else ("/trojan" if transport == "ws" else f"/xhttp-siz10/{transport}/{uuid}")

    params = {
        "security": "tls",
        "type": "ws" if transport == "ws" else "xhttp",
        "host": host,
        "path": path,
        "sni": host,
        "fp": fp,
        "alpn": alpn_val,
    }
    if transport != "ws":
        params["mode"] = transport
    query = "&".join(f"{k}={quote(str(v))}" for k, v in params.items())
    return f"trojan://{quote(password)}@{host}:{port_val}?{query}#{quote(remark)}"


def generate_vmess_link(
    uuid: str,
    host: str,
    remark: str = "Gateway",
    port: int | None = None,
    fingerprint: str | None = None,
    alpn: str | None = None,
    protocol: str = "vmess-ws",
) -> str:
    """Generate a VMess share-link for WS or XHTTP packet/stream-up."""
    protocol = normalize_protocol(protocol)
    family, transport = split_protocol(protocol)
    if family != "vmess":
        protocol = "vmess-ws"
        transport = "ws"

    port_val = port or DEFAULT_PORT
    if not (MIN_PORT <= port_val <= MAX_PORT):
        port_val = DEFAULT_PORT
    fp = (fingerprint or DEFAULT_FINGERPRINT).strip() or DEFAULT_FINGERPRINT
    if fp not in FINGERPRINTS:
        fp = DEFAULT_FINGERPRINT
    alpn_val = (alpn or "").strip() or DEFAULT_ALPN_BY_PROTOCOL.get(protocol, "http/1.1")
    is_xhttp = transport != "ws"

    # VMess XHTTP clients expect the mode value itself to be exactly
    # "packet-up" or "stream-up".  Be defensive here so an accidental
    # transport value like "xhttp-packet-up" can never produce a blank or
    # invalid mode in the exported VMess JSON.
    vmess_mode = transport
    if vmess_mode.startswith("xhttp-"):
        vmess_mode = vmess_mode[len("xhttp-"):]
    if vmess_mode not in ("packet-up", "stream-up"):
        vmess_mode = ""

    if is_xhttp:
        # v2rayNG's current VMess standard-URI parser maps:
        #   type=xhttp -> network=xhttp
        #   mode=packet-up|stream-up -> xhttpMode
        #   path/host -> the XHTTP transport settings
        # A Base64 VMess JSON only fills `headerType` from `type` and does
        # not populate xhttpMode, so XHTTP imports can lose the selected mode.
        # Generate the standard URI for XHTTP to preserve the mode on Android.
        params = {
            "type": "xhttp",
            "mode": vmess_mode,
            "host": host,
            "path": f"/xhttp-siz10/{vmess_mode}/{uuid}",
            "security": "tls",
            "sni": host,
            "fp": fp,
            "alpn": alpn_val,
            "insecure": "0",
        }
        query = "&".join(f"{k}={quote(str(v))}" for k, v in params.items())
        return f"vmess://{quote(uuid)}@{host}:{port_val}?{query}#{quote(remark)}"

    # Keep the existing Base64 JSON form for VMess WebSocket to avoid
    # changing the already-established WS export format.
    vmess_config = {
        "v": "2",
        "ps": remark,
        "add": host,
        "port": str(port_val),
        "id": uuid,
        "aid": "0",
        "scy": "auto",
        "net": "ws",
        "type": "none",
        "host": host,
        "path": f"/vmess/{uuid}",
        "tls": "tls",
        "sni": host,
        "alpn": alpn_val,
        "fp": fp,
        "insecure": "0",
        "vcn": "",
        "pcs": "",
    }
    json_bytes = json.dumps(
        vmess_config,
        ensure_ascii=False,
        indent=2,
        separators=(",", ": "),
    ).encode("utf-8")
    return f"vmess://{base64.b64encode(json_bytes).decode('utf-8')}"

def vless_link_for_link(link: dict, uid: str, host: str) -> str:
    """Return the correct share link for all 9 protocol/transport combinations."""
    proto = normalize_protocol(link.get("protocol", DEFAULT_PROTOCOL))
    family, _transport = split_protocol(proto)
    remark = build_vless_remark(link)

    if family == "vmess":
        return generate_vmess_link(
            uid, host, remark=remark,
            port=link.get("port"),
            fingerprint=link.get("fingerprint"),
            alpn=link.get("alpn"),
            protocol=proto,
        )

    if family == "trojan":
        password = (link.get("password") or uid).strip()
        return generate_trojan_link(
            password=password, host=host, remark=remark, uuid=uid,
            port=link.get("port"),
            fingerprint=link.get("fingerprint"),
            alpn=link.get("alpn"),
            protocol=proto,
        )

    return generate_vless_link(
        uid, host, remark=remark, protocol=proto,
        fingerprint=link.get("fingerprint"),
        alpn=link.get("alpn"),
        port=link.get("port"),
    )

def uptime() -> str:
    secs = int(time.time() - stats["start_time"])
    h, m, s = secs // 3600, (secs % 3600) // 60, secs % 60
    return f"{h:02d}:{m:02d}:{s:02d}"

def parse_size_to_bytes(value: float, unit: str) -> int:
    unit = unit.upper()
    if unit == "GB": return int(value * 1024 ** 3)
    if unit == "MB": return int(value * 1024 ** 2)
    if unit == "KB": return int(value * 1024)
    return int(value)

def parse_speed_to_bytes(value: float, unit: str) -> int:
    """Convert a speed limit to bytes per second."""
    if value <= 0:
        return 0
    unit = (unit or "MBIT").upper()
    if unit == "MBIT":
        return int(value * 1024 * 1024 / 8)
    if unit == "KB":
        return int(value * 1024)
    if unit == "MB":
        return int(value * 1024 * 1024)
    return int(value)

def is_link_expired(link: dict) -> bool:
    exp = link.get("expires_at")
    if not exp:
        return False
    try:
        return datetime.now() > datetime.fromisoformat(exp)
    except Exception:
        return False

def is_link_allowed(link: dict | None) -> bool:
    if link is None:
        return False
    if not link.get("active", True):
        return False
    if is_link_expired(link):
        return False
    lb = link.get("limit_bytes", 0)
    if lb > 0 and link.get("used_bytes", 0) >= lb:
        return False
    return True

def fmt_bytes(b: int) -> str:
    if b < 1024: return f"{b} B"
    if b < 1024**2: return f"{b/1024:.1f} KB"
    if b < 1024**3: return f"{b/1024**2:.2f} MB"
    return f"{b/1024**3:.2f} GB"

def unique_ips_for_uuid(uuid: str) -> set:
    """Return unique IPs currently connected to a specific UUID."""
    return {c.get("ip") for c in connections.values() if c.get("uuid") == uuid and c.get("ip")}

def is_ip_allowed(link: dict | None, uuid: str, ip: str) -> bool:
    """Check concurrent IP/user limits for a config. ip_limit=0 means unlimited.
    An IP that already has a session for this config remains allowed for additional sessions."""
    if link is None:
        return False
    limit = int(link.get("ip_limit", 0) or 0)
    if limit <= 0:
        return True
    ips = unique_ips_for_uuid(uuid)
    if ip in ips:
        return True
    return len(ips) < limit

def client_ip(request: Request) -> str:
    """Return the client IP, honoring Railway/Cloudflare proxy headers."""
    fwd = request.headers.get("x-forwarded-for")
    if fwd:
        return fwd.split(",")[0].strip()
    real_ip = request.headers.get("x-real-ip")
    if real_ip:
        return real_ip.strip()
    return request.client.host if request.client else "Unknown"

# ══════════════════════════════════════════════════════════════════════════════
# Sub-token — custom identifier for subscription URLs
# ══════════════════════════════════════════════════════════════════════════════
import re as _re

_SUB_TOKEN_RE = _re.compile(r"^[A-Za-z0-9_-]{3,32}$")


def find_link_by_key(key: str) -> tuple[str | None, dict | None]:
    """Find a link by UUID first, then by custom sub_token."""
    if not key:
        return None, None
    # 1) UUID — O(1)
    if key in LINKS:
        return key, LINKS[key]
    # 2) sub_token — O(n)
    for uid, l in LINKS.items():
        tok = (l.get("sub_token") or "").strip()
        if tok and tok == key:
            return uid, l
    return None, None


def normalize_sub_token(tok: str, ignore_uid: str | None = None) -> tuple[bool, str]:
    """Validate and normalize a sub_token.
    Returns: (ok, cleaned value or error message)."""
    tok = (tok or "").strip()
    if not tok:
        return True, ""  # Empty means keep it unset (optional)
    if not _SUB_TOKEN_RE.match(tok):
        return False, "Sub Token must be 3–32 characters and may contain letters, numbers, - and _"
    # Check uniqueness
    for uid, l in LINKS.items():
        if uid == ignore_uid:
            continue
        if (l.get("sub_token") or "").strip() == tok:
            return False, f"Sub Token \"{tok}\" is already in use"
    return True, tok

# ── Default link ──────────────────────────────────────────────────────────────
_default_link_created = False

async def ensure_default_link():
    global _default_link_created
    if _default_link_created:
        return

    created = False
    async with LINKS_LOCK:
        if not any(l.get("is_default") for l in LINKS.values()):
            uid = hashlib.sha256(f"default{CONFIG['secret']}".encode()).hexdigest()
            uid = f"{uid[:8]}-{uid[8:12]}-{uid[12:16]}-{uid[16:20]}-{uid[20:32]}"
            if uid not in LINKS:
                LINKS[uid] = {
                    "label": "VIP-config",
                    "limit_bytes": 0,
                    "used_bytes": 0,
                    "up_bytes": 0,
                    "down_bytes": 0,
                    "created_at": datetime.now().isoformat(),
                    "active": True,
                    "expires_at": None,
                    "note": "",
                    "is_default": True,
                    "sub_id": None,
                    "protocol": DEFAULT_PROTOCOL,
                    "fingerprint": DEFAULT_FINGERPRINT,
                    "alpn": "",
                    "port": DEFAULT_PORT,
                    "ip_limit": 0,
                    "speed_limit_bytes": DEFAULT_SPEED_LIMIT,
                    "sub_token": "OMIDIRAN",  # Default custom subscription token
                }
                created = True
        _default_link_created = True

    if created:
        await save_state()

# ── Basic endpoints ───────────────────────────────────────────────────────────
@app.get("/", response_class=HTMLResponse)
async def root(request: Request):
    token = request.cookies.get(SESSION_COOKIE)
    if await is_valid_session(token):
        return RedirectResponse(url="/dashboard")
    return HTMLResponse(content=LOGIN_HTML)

@app.get("/health")
async def health():
    return {"status": "ok", "connections": len(connections), "uptime": uptime()}

# ── Subscription (single link) ────────────────────────────────────────────────
@app.get("/sub/{uuid}")
async def subscription_single(uuid: str, request: Request):
    import base64
    async with LINKS_LOCK:
        real_uid, link = find_link_by_key(uuid)
    if not link or not is_link_allowed(link):
        raise HTTPException(status_code=404, detail="not found or inactive")

    # Browser → UI
    if is_browser_request(request):
        try:
            from public_page import get_single_config_page_html
            return HTMLResponse(content=get_single_config_page_html(real_uid))
        except ImportError:
            pass

    # Client → base64
    host = get_host(request)
    vless = vless_link_for_link(link, real_uid, host)
    content = base64.b64encode(vless.encode()).decode()
    return Response(content=content, media_type="text/plain",
                    headers={"profile-title": quote(link["label"]), "support-url": SUPPORT_URL})

@app.get("/sub-all")
async def subscription_all(request: Request):
    import base64
    is_auth = await is_valid_session(request.cookies.get(SESSION_COOKIE))
    browser = is_browser_request(request)

    # Browser request
    if browser:
        if not is_auth:
            return RedirectResponse(url="/")
        # Authenticated admin → Admin UI
        from public_page import get_admin_all_page_html
        return HTMLResponse(content=get_admin_all_page_html())

    # Client request → base64
    if not is_auth:
        raise HTTPException(status_code=401, detail="unauthorized")
    host = get_host(request)
    async with LINKS_LOCK:
        lines = [
            vless_link_for_link(d, uid, host)
            for uid, d in LINKS.items()
            if is_link_allowed(d)
        ]
    content = base64.b64encode("\n".join(lines).encode()).decode()
    return Response(content=content, media_type="text/plain")

# ══════════════════════════════════════════════════════════════════════════════
# SUB GROUP endpoints
# ══════════════════════════════════════════════════════════════════════════════

@app.post("/api/subs")
async def create_sub(request: Request, _=Depends(require_auth)):
    body = await request.json()
    name = (body.get("name") or "New Group").strip()[:60]
    desc = (body.get("desc") or "").strip()[:200]
    password = (body.get("password") or "").strip()
    sub_id = generate_uuid()
    uuid_key = secrets.token_urlsafe(16)
    async with SUBS_LOCK:
        SUBS[sub_id] = {
            "name": name,
            "desc": desc,
            "password_hash": hash_password(password) if password else None,
            "uuid_key": uuid_key,
            "created_at": datetime.now().isoformat(),
            "link_ids": [],
        }
    await save_state()
    log_activity("sub", f'Group "{name}" created', "ok")
    host = get_host(request)
    return {
        "sub_id": sub_id,
        **SUBS[sub_id],
        "public_url": f"https://{host}/p/{uuid_key}",
        "sub_url": f"https://{host}/sub-group/{uuid_key}",
    }

@app.get("/api/subs")
async def list_subs(request: Request, _=Depends(require_auth)):
    host = get_host(request)
    async with SUBS_LOCK:
        snap_subs = dict(SUBS)
    async with LINKS_LOCK:
        snap_links = dict(LINKS)
    result = []
    for sid, s in snap_subs.items():
        link_ids = s.get("link_ids", [])
        active_count = sum(1 for lid in link_ids if is_link_allowed(snap_links.get(lid)))
        total_used = sum(snap_links[lid].get("used_bytes", 0) for lid in link_ids if lid in snap_links)
        result.append({
            "sub_id": sid,
            **s,
            "password_hash": None,
            "has_password": s.get("password_hash") is not None,
            "links_count": len(link_ids),
            "active_count": active_count,
            "total_used_bytes": total_used,
            "total_used_fmt": fmt_bytes(total_used),
            "public_url": f"https://{host}/p/{s['uuid_key']}",
            "sub_url": f"https://{host}/sub-group/{s['uuid_key']}",
        })
    result.sort(key=lambda x: x["created_at"], reverse=True)
    return {"subs": result}

@app.patch("/api/subs/{sub_id}")
async def update_sub(sub_id: str, request: Request, _=Depends(require_auth)):
    body = await request.json()
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            raise HTTPException(status_code=404, detail="sub not found")
        s = SUBS[sub_id]
        if "name" in body:
            s["name"] = str(body["name"])[:60]
        if "desc" in body:
            s["desc"] = str(body["desc"])[:200]
        if "password" in body:
            pw = str(body["password"]).strip()
            s["password_hash"] = hash_password(pw) if pw else None
        if "link_ids" in body:
            s["link_ids"] = list(body["link_ids"])
    await save_state()
    return {"ok": True}

@app.delete("/api/subs/{sub_id}")
async def delete_sub(sub_id: str, _=Depends(require_auth)):
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            raise HTTPException(status_code=404, detail="sub not found")
        name = SUBS[sub_id].get("name", sub_id)
        del SUBS[sub_id]
    async with LINKS_LOCK:
        for link in LINKS.values():
            if link.get("sub_id") == sub_id:
                link["sub_id"] = None
    await save_state()
    log_activity("sub", f'Group "{name}" deleted', "warn")
    return {"ok": True, "deleted": sub_id}

@app.post("/api/subs/{sub_id}/links")
async def assign_link_to_sub(sub_id: str, request: Request, _=Depends(require_auth)):
    body = await request.json()
    link_id = str(body.get("link_id", ""))
    action = str(body.get("action", "add"))
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            raise HTTPException(status_code=404, detail="sub not found")
        s = SUBS[sub_id]
        ids = s.setdefault("link_ids", [])
        if action == "add":
            if link_id not in ids:
                ids.append(link_id)
        else:
            if link_id in ids:
                ids.remove(link_id)
    async with LINKS_LOCK:
        if link_id in LINKS:
            LINKS[link_id]["sub_id"] = sub_id if action == "add" else None
    await save_state()
    return {"ok": True}

# ── Public sub-group subscription file ───────────────────────────────────────
@app.get("/sub-group/{uuid_key}")
async def sub_group_subscription(uuid_key: str, request: Request):
    import base64
    async with SUBS_LOCK:
        sub = next((s for s in SUBS.values() if s.get("uuid_key") == uuid_key), None)
    if not sub:
        raise HTTPException(status_code=404, detail="not found")

    # Browser → subscription-group UI
    if is_browser_request(request):
        try:
            from public_page import get_public_page_html
            return HTMLResponse(content=get_public_page_html(uuid_key))
        except ImportError:
            pass  # Fall back to base64 if the UI module is unavailable

    if sub.get("password_hash"):
        pw = request.query_params.get("pw", "")
        if hash_password(pw) != sub["password_hash"]:
            raise HTTPException(status_code=403, detail="wrong password")

    host = get_host(request)
    link_ids = sub.get("link_ids", [])
    async with LINKS_LOCK:
        lines = []
        for lid in link_ids:
            link = LINKS.get(lid)
            if link and is_link_allowed(link):
                lines.append(vless_link_for_link(link, lid, host))

    content = base64.b64encode("\n".join(lines).encode()).decode()
    return Response(
        content=content,
        media_type="text/plain",
        headers={
            "profile-title": quote(sub["name"]),
            "support-url": SUPPORT_URL,
            "profile-update-interval": "12",
        }
    )

# ── Auth endpoints ────────────────────────────────────────────────────────────
@app.post("/api/login")
async def api_login(request: Request):
    body = await request.json()
    ip = client_ip(request)
    username = str(body.get("username", "")).strip()
    password = str(body.get("password", ""))
    if username != AUTH["username"] or hash_password(password) != AUTH["password_hash"]:
        log_activity("auth", f"Failed login attempt from {ip}", "err")
        raise HTTPException(status_code=401, detail="Invalid username or password")
    token = await create_session()
    log_activity("auth", f"Successful panel login from {ip}", "ok")
    resp = JSONResponse({"ok": True})
    resp.set_cookie(SESSION_COOKIE, token, max_age=SESSION_TTL, httponly=True, samesite="lax", path="/")
    return resp

@app.post("/api/logout")
async def api_logout(request: Request):
    await destroy_session(request.cookies.get(SESSION_COOKIE))
    resp = JSONResponse({"ok": True})
    resp.delete_cookie(SESSION_COOKIE, path="/")
    return resp

@app.get("/api/me")
async def api_me(request: Request):
    return {"authenticated": await is_valid_session(request.cookies.get(SESSION_COOKIE))}

@app.get("/api/account")
async def api_account(_=Depends(require_auth)):
    return {"username": AUTH["username"]}

@app.post("/api/change-credentials")
async def api_change_credentials(request: Request, token=Depends(require_auth)):
    body = await request.json()
    current_password = str(body.get("current_password", ""))
    if hash_password(current_password) != AUTH["password_hash"]:
        raise HTTPException(status_code=400, detail="Current password is incorrect")

    new_username = str(body.get("new_username", "")).strip()
    new_password = str(body.get("new_password", ""))

    if not new_username and not new_password:
        raise HTTPException(status_code=400, detail="Enter a new username or password")

    if new_username:
        if len(new_username) < 3 or len(new_username) > 32:
            raise HTTPException(status_code=400, detail="Username must be 3–32 characters long")
        if any(ch.isspace() for ch in new_username):
            raise HTTPException(status_code=400, detail="Username must not contain spaces")

    if new_password and len(new_password) < 4:
        raise HTTPException(status_code=400, detail="New password must be at least 4 characters")

    changed = []
    if new_username:
        if new_username != AUTH["username"]:
            AUTH["username"] = new_username
            changed.append("username")
    if new_password:
        AUTH["password_hash"] = hash_password(new_password)
        changed.append("password")

    if not changed:
        raise HTTPException(status_code=400, detail="No changes were made")

    # Invalidate all sessions and issue a fresh one for the current browser.
    fresh_token = await create_session()

    await save_state()
    log_activity("auth", f'Panel credentials changed: {", ".join(changed)}', "ok")

    resp = JSONResponse({"ok": True, "username": AUTH["username"]})
    resp.set_cookie(SESSION_COOKIE, fresh_token, max_age=SESSION_TTL, httponly=True, samesite="lax", path="/")
    return resp

# Backward-compatible endpoint for older UI builds.
@app.post("/api/change-password")
async def api_change_password_legacy(request: Request, token=Depends(require_auth)):
    body = await request.json()
    body["new_username"] = ""
    return await api_change_credentials_from_legacy(body, token)

async def api_change_credentials_from_legacy(body: dict, token: str):
    current_password = str(body.get("current_password", ""))
    if hash_password(current_password) != AUTH["password_hash"]:
        raise HTTPException(status_code=400, detail="Current password is incorrect")
    new = str(body.get("new_password", ""))
    if len(new) < 4:
        raise HTTPException(status_code=400, detail="New password must be at least 4 characters")
    AUTH["password_hash"] = hash_password(new)
    fresh_token = await create_session()
    await save_state()
    log_activity("auth", "Panel password changed", "ok")
    resp = JSONResponse({"ok": True, "username": AUTH["username"]})
    resp.set_cookie(SESSION_COOKIE, fresh_token, max_age=SESSION_TTL, httponly=True, samesite="lax", path="/")
    return resp

# ── Stats ─────────────────────────────────────────────────────────────────────
@app.get("/stats")
async def get_stats(_=Depends(require_auth)):
    async with LINKS_LOCK:
        snap = dict(LINKS)
    return {
        "active_connections": len(connections),
        "total_traffic_mb": round(stats["total_bytes"] / (1024 ** 2), 2),
        "total_requests": stats["total_requests"],
        "total_errors": stats["total_errors"],
        "uptime": uptime(),
        "timestamp": datetime.now().isoformat(),
        "hourly": dict(hourly_traffic),
        "recent_errors": list(error_logs)[-10:],
        "unique_errors": len(error_logs),
        "links_count": len(snap),
        "active_links": sum(1 for l in snap.values() if is_link_allowed(l)),
        "expired_links": sum(1 for l in snap.values() if is_link_expired(l)),
        "subs_count": len(SUBS),
    }

# ── Activity Logs ─────────────────────────────────────────────────────────────
# ── System resources (dashboard "Server Resources" card) ─────────────────────
# psutil-free: reads /proc (+ cgroup limits inside containers). On platforms
# without /proc every field degrades to null and the card shows "—".
_SYS_STATE: dict = {}

def _sys_cpu_times():
    with open("/proc/stat") as f:
        vals = [int(x) for x in f.readline().split()[1:]]
    idle = vals[3] + (vals[4] if len(vals) > 4 else 0)   # idle + iowait
    return idle, sum(vals[:8])                           # guest is already inside user/nice

def _sys_net_bytes():
    rx = tx = 0
    with open("/proc/net/dev") as f:
        for line in list(f)[2:]:
            name, data = line.split(":", 1)
            if name.strip() == "lo":
                continue
            cols = data.split()
            rx += int(cols[0])
            tx += int(cols[8])
    return rx, tx

def _sys_memory():
    info = {}
    with open("/proc/meminfo") as f:
        for line in f:
            k, v = line.split(":", 1)
            info[k] = int(v.split()[0]) * 1024
    total = info["MemTotal"]
    used = total - info.get("MemAvailable", info.get("MemFree", 0))
    # Inside a container prefer the cgroup limit (cgroup v2, then v1)
    for lim, cur, stat, key in (
        ("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory.current", "/sys/fs/cgroup/memory.stat", "inactive_file"),
        ("/sys/fs/cgroup/memory/memory.limit_in_bytes", "/sys/fs/cgroup/memory/memory.usage_in_bytes", "/sys/fs/cgroup/memory/memory.stat", "total_inactive_file"),
    ):
        try:
            lim_s = open(lim).read().strip()
            if lim_s == "max" or int(lim_s) >= total:
                continue
            c_total = int(lim_s)
            c_used = int(open(cur).read().strip())
            try:
                for line in open(stat):
                    if line.startswith(key + " "):
                        c_used -= int(line.split()[1])
                        break
            except Exception:
                pass
            return c_total, max(0, c_used)
        except Exception:
            continue
    return total, used

@app.get("/api/system")
async def get_system(_=Depends(require_auth)):
    import shutil
    now = time.monotonic()
    out = {
        "platform": _sys.platform, "cores": os.cpu_count(), "load": None,
        "cpu_percent": None, "mem_total": None, "mem_used": None, "mem_percent": None,
        "disk_total": None, "disk_used": None, "disk_percent": None,
        "net_rx_bps": None, "net_tx_bps": None, "net_rx_total": None, "net_tx_total": None,
    }
    try:
        out["load"] = [round(x, 2) for x in os.getloadavg()]
    except Exception:
        pass
    # CPU % and network rate are deltas between two samples (>= 1s apart)
    try:
        cpu, net = _sys_cpu_times(), _sys_net_bytes()
        st = _SYS_STATE
        if "t" not in st:
            await asyncio.sleep(0.25)
            st.update(t=now, cpu=cpu, net=net, rates=None)
            cpu, net, now = _sys_cpu_times(), _sys_net_bytes(), time.monotonic()
        if now - st["t"] >= 1.0 or st.get("rates") is None:
            dt = max(now - st["t"], 0.001)
            d_idle, d_total = cpu[0] - st["cpu"][0], cpu[1] - st["cpu"][1]
            pct = round(max(0.0, min(100.0, 100.0 * (1 - d_idle / d_total))), 1) if d_total > 0 else None
            st["rates"] = (pct, max(0, (net[0] - st["net"][0]) / dt), max(0, (net[1] - st["net"][1]) / dt))
            st.update(t=now, cpu=cpu, net=net)
        out["cpu_percent"], out["net_rx_bps"], out["net_tx_bps"] = st["rates"]
        out["net_rx_total"], out["net_tx_total"] = net
    except Exception:
        pass
    try:
        total, used = _sys_memory()
        out.update(mem_total=total, mem_used=used, mem_percent=round(100.0 * used / total, 1) if total else None)
    except Exception:
        pass
    try:
        du = shutil.disk_usage("/")
        out.update(disk_total=du.total, disk_used=du.used, disk_percent=round(100.0 * du.used / du.total, 1))
    except Exception:
        pass
    return out

@app.get("/api/activity")
async def get_activity(_=Depends(require_auth)):
    return {"logs": list(activity_logs)[-500:]}

@app.post("/api/activity/clear")
async def clear_activity(_=Depends(require_auth)):
    activity_logs.clear()
    _activity_index.clear()
    return {"ok": True}

@app.get("/api/errors")
async def get_errors(_=Depends(require_auth)):
    return {"errors": list(error_logs), "total_errors": stats["total_errors"]}

@app.post("/api/errors/clear")
async def clear_errors(_=Depends(require_auth)):
    error_logs.clear()
    stats["total_errors"] = 0
    return {"ok": True}

# ── Live connections (with IP) ────────────────────────────────────────────────
@app.get("/api/connections")
async def get_connections(_=Depends(require_auth)):
    """
    Return live connections grouped by IP.
    Each IP appears once with aggregated bytes and active session count.
    raw_count remains the number of raw open sessions.
    """
    async with LINKS_LOCK:
        snap = dict(LINKS)

    grouped: dict[str, dict] = {}
    for conn_id, c in connections.items():
        ip = c.get("ip", "Unknown")
        link = snap.get(c.get("uuid"))
        label = link.get("label") if link else "Unknown"
        g = grouped.get(ip)
        if g is None:
            g = {
                "ip": ip,
                "sessions": 0,
                "bytes": 0,
                "labels": set(),
                "transports": set(),
                "first_connected_at": c.get("connected_at"),
                "last_connected_at": c.get("connected_at"),
            }
            grouped[ip] = g
        g["sessions"] += 1
        g["bytes"] += c.get("bytes", 0)
        g["labels"].add(label)
        g["transports"].add(c.get("transport", "vless-ws"))
        ca = c.get("connected_at")
        if ca:
            if not g["first_connected_at"] or ca < g["first_connected_at"]:
                g["first_connected_at"] = ca
            if not g["last_connected_at"] or ca > g["last_connected_at"]:
                g["last_connected_at"] = ca

    result = []
    for ip, g in grouped.items():
        result.append({
            "ip": ip,
            "sessions": g["sessions"],
            "labels": sorted(g["labels"]),
            "label": " · ".join(sorted(g["labels"])) if g["labels"] else "Unknown",
            "transports": sorted(g["transports"]),
            "bytes": g["bytes"],
            "bytes_fmt": fmt_bytes(g["bytes"]),
            "connected_at": g["first_connected_at"],
            "last_connected_at": g["last_connected_at"],
        })
    result.sort(key=lambda x: x.get("last_connected_at") or "", reverse=True)

    return {
        "connections": result,
        "count": len(result),          # Unique IP count
        "raw_count": len(connections), # Total raw open-session count
    }

# ── Shared link create/delete helpers (used by API and Telegram bot) ───────
async def make_link(
    label: str = "New Link",
    limit_bytes: int = 0,
    expires_at: str | None = None,
    note: str = "",
    sub_id: str | None = None,
    protocol: str = DEFAULT_PROTOCOL,
    fingerprint: str = DEFAULT_FINGERPRINT,
    alpn: str = "",
    port: int = DEFAULT_PORT,
    ip_limit: int = 0,
    speed_limit_bytes: int = 0,
    sub_token: str = "",
) -> tuple[str, dict]:
    protocol = normalize_protocol(protocol)
    fingerprint = (fingerprint or DEFAULT_FINGERPRINT).strip().lower()
    if fingerprint not in FINGERPRINTS:
        fingerprint = DEFAULT_FINGERPRINT
    if not (MIN_PORT <= port <= MAX_PORT):
        port = DEFAULT_PORT
    uid = generate_uuid()
    trojan_password = generate_trojan_password() if split_protocol(protocol)[0] == "trojan" else ""
    async with LINKS_LOCK:
        LINKS[uid] = {
            "label": (label or "New Link").strip()[:60] or "New Link",
            "limit_bytes": max(0, limit_bytes),
            "used_bytes": 0,
                    "up_bytes": 0,
                    "down_bytes": 0,
            "created_at": datetime.now().isoformat(),
            "active": True,
            "expires_at": expires_at,
            "note": (note or "").strip()[:200],
            "is_default": False,
            "sub_id": sub_id,
            "protocol": protocol,
            "password": trojan_password,
            "fingerprint": fingerprint,
            "alpn": (alpn or "").strip()[:100],
            "port": port,
            "ip_limit": max(0, ip_limit),
            "speed_limit_bytes": max(0, speed_limit_bytes),
            "sub_token": (sub_token or "").strip(),
        }
    if sub_id:
        async with SUBS_LOCK:
            if sub_id in SUBS:
                ids = SUBS[sub_id].setdefault("link_ids", [])
                if uid not in ids:
                    ids.append(uid)
    await save_state()
    log_activity("link", f'Config "{LINKS[uid]["label"]}" created', "ok")
    return uid, LINKS[uid]

async def remove_link(uid: str) -> str | None:
    async with LINKS_LOCK:
        if uid not in LINKS:
            return None
        label = LINKS[uid].get("label", uid)
        sub_id = LINKS[uid].get("sub_id")
        del LINKS[uid]
    if sub_id:
        async with SUBS_LOCK:
            if sub_id in SUBS:
                ids = SUBS[sub_id].get("link_ids", [])
                if uid in ids:
                    ids.remove(uid)
    await save_state()
    log_activity("link", f'Config "{label}" deleted', "err")
    return label

async def set_link_active(uid: str, active: bool) -> dict | None:
    async with LINKS_LOCK:
        if uid not in LINKS:
            return None
        LINKS[uid]["active"] = bool(active)
        label = LINKS[uid]["label"]
    log_activity("link", f'Config "{label}" {"enabled" if active else "disabled"}', "ok" if active else "warn")
    await save_state()
    return LINKS[uid]

async def update_link_field(uid: str, field: str, value) -> dict | None:
    """Update one config field; shared by the Telegram bot."""
    async with LINKS_LOCK:
        if uid not in LINKS:
            return None
        LINKS[uid][field] = value
        link = dict(LINKS[uid])
    log_activity("link", f'Config "{link.get("label", "?")}" updated: {field}', "info")
    await save_state()
    return link

async def reset_link_usage(uid: str) -> dict | None:
    """Reset a config usage counter."""
    async with LINKS_LOCK:
        if uid not in LINKS:
            return None
        LINKS[uid]["used_bytes"] = 0
        LINKS[uid]["up_bytes"] = 0
        LINKS[uid]["down_bytes"] = 0
        link = dict(LINKS[uid])
    log_activity("link", f'Config "{link.get("label", "?")}" usage reset', "info")
    await save_state()
    return link

# ── Shared subscription-group helpers (web API and Telegram bot) ──
async def create_sub_group(name: str = "New Group", desc: str = "", password: str = "") -> tuple[str, dict]:
    name = (name or "New Group").strip()[:60]
    desc = (desc or "").strip()[:200]
    password = (password or "").strip()
    sub_id = generate_uuid()
    uuid_key = secrets.token_urlsafe(16)
    async with SUBS_LOCK:
        SUBS[sub_id] = {
            "name": name,
            "desc": desc,
            "password_hash": hash_password(password) if password else None,
            "uuid_key": uuid_key,
            "created_at": datetime.now().isoformat(),
            "link_ids": [],
        }
    await save_state()
    log_activity("sub", f'Group "{name}" created', "ok")
    return sub_id, SUBS[sub_id]

async def set_link_sub(uid: str, sub_id: str | None) -> bool:
    """Assign a config to a subscription group; sub_id=None removes the current assignment."""
    async with LINKS_LOCK:
        if uid not in LINKS:
            return False
        old_sub = LINKS[uid].get("sub_id")
        label = LINKS[uid].get("label", uid)
    if sub_id is not None:
        async with SUBS_LOCK:
            if sub_id not in SUBS:
                return False
    async with SUBS_LOCK:
        if old_sub and old_sub in SUBS:
            ids = SUBS[old_sub].get("link_ids", [])
            if uid in ids:
                ids.remove(uid)
        if sub_id and sub_id in SUBS:
            ids = SUBS[sub_id].setdefault("link_ids", [])
            if uid not in ids:
                ids.append(uid)
    async with LINKS_LOCK:
        if uid in LINKS:
            LINKS[uid]["sub_id"] = sub_id
    await save_state()
    log_activity("link", f'Config "{label}" {"added to group" if sub_id else "removed from group"}', "info")
    return True

async def remove_sub_group(sub_id: str) -> str | None:
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            return None
        name = SUBS[sub_id].get("name", sub_id)
        del SUBS[sub_id]
    async with LINKS_LOCK:
        for link in LINKS.values():
            if link.get("sub_id") == sub_id:
                link["sub_id"] = None
    await save_state()
    log_activity("sub", f'Group "{name}" deleted', "warn")
    return name

# ── Link Management ───────────────────────────────────────────────────────────
@app.post("/api/links")
async def create_link(request: Request, _=Depends(require_auth)):
    body = await request.json()
    lv = float(body.get("limit_value") or 0)
    lu = body.get("limit_unit") or "GB"
    limit_bytes = 0 if lv <= 0 else parse_size_to_bytes(lv, lu)
    exp_days = int(body.get("expires_days") or 0)
    expires_at = (datetime.now() + timedelta(days=exp_days)).isoformat() if exp_days > 0 else None
    try:
        port = int(body.get("port") or DEFAULT_PORT)
    except (TypeError, ValueError):
        port = DEFAULT_PORT
    try:
        ip_limit = int(body.get("ip_limit") or 0)
    except (TypeError, ValueError):
        ip_limit = 0

    sv = float(body.get("speed_limit_value") or 0)
    su = body.get("speed_limit_unit") or "MBIT"
    speed_limit_bytes = 0 if sv <= 0 else parse_speed_to_bytes(sv, su)

    # Validate sub_token
    sub_token_raw = str(body.get("sub_token") or "").strip()
    ok, result = normalize_sub_token(sub_token_raw)
    if not ok:
        raise HTTPException(status_code=400, detail=result)
    sub_token = result

    uid, link = await make_link(
        label=body.get("label") or "New Link",
        limit_bytes=limit_bytes,
        expires_at=expires_at,
        note=body.get("note") or "",
        sub_id=body.get("sub_id") or None,
        protocol=body.get("protocol") or DEFAULT_PROTOCOL,
        fingerprint=body.get("fingerprint") or DEFAULT_FINGERPRINT,
        alpn=body.get("alpn") or "",
        port=port,
        ip_limit=ip_limit,
        speed_limit_bytes=speed_limit_bytes,
        sub_token=sub_token,
    )

    host = get_host(request)
    scheme = get_scheme(request)
    sub_slug = sub_token if sub_token else uid
    return {
        "uuid": uid,
        **link,
        "expired": False,
        "vless_link": vless_link_for_link(link, uid, host),
        "sub_url": f"{scheme}://{host}/sub/{sub_slug}",
    }

@app.get("/api/links")
async def list_links(request: Request, _=Depends(require_auth)):
    host = get_host(request)
    scheme = get_scheme(request)
    async with LINKS_LOCK:
        snap = dict(LINKS)
    result = []
    for uid, d in snap.items():
        proto = d.get("protocol", DEFAULT_PROTOCOL)
        tok = (d.get("sub_token") or "").strip()
        sub_slug = tok if tok else uid
        result.append({
            "uuid": uid,
            **d,
            "protocol": proto,
            "expired": is_link_expired(d),
            "vless_link": vless_link_for_link(d, uid, host),
            "sub_url": f"{scheme}://{host}/sub/{sub_slug}",
            "connected_ips": len(unique_ips_for_uuid(uid)),
        })
    result.sort(key=lambda x: x["created_at"], reverse=True)
    return {"links": result}

@app.patch("/api/links/{uid}")
async def update_link(uid: str, request: Request, _=Depends(require_auth)):
    body = await request.json()
    async with LINKS_LOCK:
        if uid not in LINKS:
            raise HTTPException(status_code=404, detail="link not found")
        link = LINKS[uid]
        old_sub = link.get("sub_id")
        label = link.get("label")
        if "active" in body:
            link["active"] = bool(body["active"])
            log_activity("link", f'Config "{label}" {"enabled" if link["active"] else "disabled"}', "ok" if link["active"] else "warn")
        if "protocol" in body:
            new_proto = normalize_protocol(body.get("protocol"))
            link["protocol"] = new_proto
            if split_protocol(new_proto)[0] == "trojan" and not link.get("password"):
                link["password"] = generate_trojan_password()

        if "label" in body:
            link["label"] = str(body["label"])[:60]
        if "note" in body:
            link["note"] = str(body["note"])[:200]
        if "reset_usage" in body and body["reset_usage"]:
            link["used_bytes"] = 0
            link["up_bytes"] = 0
            link["down_bytes"] = 0
            log_activity("link", f'Config "{label}" usage reset', "info")
        if "limit_value" in body:
            lv = float(body.get("limit_value") or 0)
            lu = body.get("limit_unit") or "GB"
            link["limit_bytes"] = 0 if lv <= 0 else parse_size_to_bytes(lv, lu)
        if "expires_days" in body:
            ed = int(body["expires_days"] or 0)
            link["expires_at"] = (datetime.now() + timedelta(days=ed)).isoformat() if ed > 0 else None
        if "fingerprint" in body:
            fp = str(body.get("fingerprint") or DEFAULT_FINGERPRINT).strip().lower()
            link["fingerprint"] = fp if fp in FINGERPRINTS else DEFAULT_FINGERPRINT
        if "alpn" in body:
            link["alpn"] = str(body.get("alpn") or "").strip()[:100]
        if "port" in body:
            try:
                p = int(body.get("port") or DEFAULT_PORT)
            except (TypeError, ValueError):
                p = DEFAULT_PORT
            link["port"] = p if (MIN_PORT <= p <= MAX_PORT) else DEFAULT_PORT
        if "ip_limit" in body:
            try:
                il = int(body.get("ip_limit") or 0)
            except (TypeError, ValueError):
                il = 0
            link["ip_limit"] = max(0, il)
        if "sub_token" in body:
            ok, result = normalize_sub_token(str(body.get("sub_token") or ""), ignore_uid=uid)
            if not ok:
                raise HTTPException(status_code=400, detail=result)
            link["sub_token"] = result
            log_activity("link", f'Sub Token for config "{link["label"]}" set: {result or "cleared"}', "info")
        if any(k in body for k in ("protocol", "label", "note", "limit_value", "expires_days", "fingerprint", "alpn", "port", "ip_limit", "speed_limit_value", "sub_token")):
            log_activity("link", f'Config "{link["label"]}" updated', "info")
        new_sub = body.get("sub_id", "UNCHANGED")
        if new_sub != "UNCHANGED":
            link["sub_id"] = new_sub or None

    if new_sub != "UNCHANGED":
        async with SUBS_LOCK:
            if old_sub and old_sub in SUBS:
                ids = SUBS[old_sub].get("link_ids", [])
                if uid in ids:
                    ids.remove(uid)
            if new_sub and new_sub in SUBS:
                ids = SUBS[new_sub].setdefault("link_ids", [])
                if uid not in ids:
                    ids.append(uid)

    await save_state()
    return {"ok": True}

@app.delete("/api/links/{uid}")
async def delete_link(uid: str, _=Depends(require_auth)):
    label = await remove_link(uid)
    if label is None:
        raise HTTPException(status_code=404, detail="link not found")
    return {"ok": True, "deleted": uid}

# ══════════════════════════════════════════════════════════════════════════════
# VLESS / VMess / Trojan WebSocket Relay
# ══════════════════════════════════════════════════════════════════════════════

def _register_ws_route():
    from relay_vless import websocket_tunnel
    from relay_vmess import websocket_tunnel_vmess
    from relay_trojan import handle_trojan_ws

    # Existing VLESS/VMess routes remain unchanged.
    app.add_api_websocket_route("/ws/{uuid}", websocket_tunnel)
    app.add_api_websocket_route("/vmess/{uuid}", websocket_tunnel_vmess)

    # Trojan uses the callback-based handler instead of the wrapper that imports
    # main.py from inside relay_trojan.py. This avoids a circular-import edge
    # case where the WebSocket endpoint can return before websocket.accept(),
    # which FastAPI/Starlette reports as a 403 handshake rejection.
    async def trojan_websocket(websocket: WebSocket, uuid: str):
        await handle_trojan_ws(
            websocket,
            uuid,
            find_link_by_key,
            is_ip_allowed,
            LINKS_LOCK,
        )

    app.add_api_websocket_route("/trojan/{uuid}", trojan_websocket)

_register_ws_route()

# ══════════════════════════════════════════════════════════════════════════════
# XHTTP — Siz10a XHTTP transport
# ══════════════════════════════════════════════════════════════════════════════
from xhttp_siz10 import router as xhttp_router
app.include_router(xhttp_router)

# ══════════════════════════════════════════════════════════════════════════════
# Optional Telegram management bot (enabled when TELEGRAM_BOT_TOKEN is set)
# ══════════════════════════════════════════════════════════════════════════════
from telegram_bot import (
    start_bot as _tg_start_bot,
    stop_bot as _tg_stop_bot,
    is_running as _tg_is_running,
    validate_token as _tg_validate_token,
)

# ── Telegram bot management (from panel) ─────────────────────────
@app.get("/api/telegram")
async def get_telegram_config(_=Depends(require_auth)):
    """Return the current Telegram bot status and persisted settings."""
    token = TELEGRAM.get("bot_token", "")
    return {
        "bot_token": token,
        "admin_ids": TELEGRAM.get("admin_ids", ""),
        "enabled": bool(token),
        "running": _tg_is_running(),
        "has_token": bool(token),
    }

@app.post("/api/telegram")
async def save_telegram_config(request: Request, _=Depends(require_auth)):
    """Save the bot token and admin IDs, then restart the bot."""
    body = await request.json()
    new_token = str(body.get("bot_token") or "").strip()
    new_admins = str(body.get("admin_ids") or "").strip()

    if new_token:
        # Validate token before saving
        ok, username = await _tg_validate_token(new_token)
        if not ok:
            raise HTTPException(status_code=400, detail="Telegram bot token is invalid or could not connect to Telegram")
    else:
        username = None

    TELEGRAM["bot_token"] = new_token
    TELEGRAM["admin_ids"] = new_admins
    TELEGRAM["enabled"] = bool(new_token)

    await save_state()

    # Restart bot
    try:
        await _tg_stop_bot()
    except Exception:
        pass
    if TELEGRAM["enabled"]:
        await _tg_start_bot()

    log_activity(
        "system",
        f'Telegram bot {"enabled" if TELEGRAM["enabled"] else "disabled"}'
        + (f" (@{username})" if username else ""),
        "ok" if TELEGRAM["enabled"] else "warn",
    )

    return {
        "ok": True,
        "running": _tg_is_running(),
        "enabled": TELEGRAM["enabled"],
        "bot_username": username,
    }

@app.post("/api/telegram/stop")
async def stop_telegram_bot(_=Depends(require_auth)):
    """Stop the Telegram bot while keeping the saved token."""
    await _tg_stop_bot()
    log_activity("system", "Telegram bot stopped", "warn")
    return {"ok": True, "running": False}

@app.post("/api/telegram/test")
async def test_telegram_bot(request: Request, _=Depends(require_auth)):
    """Test the current Telegram bot token without saving changes."""
    body = await request.json()
    token = str(body.get("bot_token") or TELEGRAM.get("bot_token", "")).strip()
    if not token:
        raise HTTPException(status_code=400, detail="Enter the Telegram bot token")
    ok, username = await _tg_validate_token(token)
    if not ok:
        raise HTTPException(status_code=400, detail="Invalid token")
    return {"ok": True, "bot_username": username}

# ── HTTP Proxy ────────────────────────────────────────────────────────────────
_HOP = {"connection","keep-alive","proxy-authenticate","proxy-authorization",
        "te","trailers","transfer-encoding","upgrade","content-encoding","content-length"}

@app.api_route("/proxy/{target_url:path}", methods=["GET","POST","PUT","DELETE","PATCH","HEAD","OPTIONS"])
async def http_proxy(target_url: str, request: Request):
    if not target_url.startswith("http"):
        target_url = "https://" + target_url
    try:
        body = await request.body()
        headers = {k: v for k, v in request.headers.items() if k.lower() not in _HOP and k.lower() != "host"}
        resp = await http_client.request(method=request.method, url=target_url, headers=headers, content=body)
        stats["total_bytes"] += len(resp.content)
        stats["total_requests"] += 1
        hourly_traffic[now_ir().strftime("%H:00")] += len(resp.content)
        return Response(content=resp.content, status_code=resp.status_code,
                        headers={k: v for k, v in resp.headers.items() if k.lower() not in _HOP})
    except Exception as exc:
        stats["total_errors"] += 1
        error_logs.append({"error": str(exc), "url": target_url, "time": datetime.now().isoformat()})
        raise HTTPException(status_code=502, detail=f"Proxy error: {exc}")

# ── Public sub page ───────────────────────────────────────────────────────────
@app.get("/p/{uuid_key}", response_class=HTMLResponse)
async def public_sub_page(uuid_key: str, request: Request):
    import base64
    async with SUBS_LOCK:
        sub = next(({"sub_id": sid, **s} for sid, s in SUBS.items() if s.get("uuid_key") == uuid_key), None)
    if not sub:
        return HTMLResponse("<h2 style='font-family:sans-serif;padding:40px'>Group not found</h2>", status_code=404)

    # Client → base64 (all configs in the group)
    if not is_browser_request(request):
        # Password-protected groups require ?pw=XXXX
        if sub.get("password_hash"):
            pw = request.query_params.get("pw", "")
            if hash_password(pw) != sub["password_hash"]:
                raise HTTPException(status_code=403, detail="wrong password")

        host = get_host(request)
        link_ids = sub.get("link_ids", [])
        async with LINKS_LOCK:
            lines = []
            for lid in link_ids:
                link = LINKS.get(lid)
                if link and is_link_allowed(link):
                    lines.append(vless_link_for_link(link, lid, host))

        content = base64.b64encode("\n".join(lines).encode()).decode()
        return Response(
            content=content,
            media_type="text/plain",
            headers={
                "profile-title": quote(sub["name"]),
                "support-url": SUPPORT_URL,
                "profile-update-interval": "12",
            }
        )

    # 🌐 اگه از مرورگر اومد → UI
    from public_page import get_public_page_html
    return HTMLResponse(content=get_public_page_html(uuid_key))

@app.get("/api/public/sub/{uuid_key}")
async def public_sub_data(uuid_key: str, request: Request):
    async with SUBS_LOCK:
        sub_entry = next(((sid, s) for sid, s in SUBS.items() if s.get("uuid_key") == uuid_key), None)
    if not sub_entry:
        raise HTTPException(status_code=404, detail="not found")
    sub_id, sub = sub_entry

    has_pw = sub.get("password_hash") is not None
    if has_pw:
        pw = request.query_params.get("pw", "")
        if hash_password(pw) != sub["password_hash"]:
            return JSONResponse({"locked": True, "name": sub["name"]})

    host = get_host(request)
    link_ids = sub.get("link_ids", [])
    async with LINKS_LOCK:
        snap = dict(LINKS)

    links_out = []
    active_conns = 0
    for lid in link_ids:
        link = snap.get(lid)
        if not link:
            continue
        allowed = is_link_allowed(link)
        conn_count = sum(1 for c in connections.values() if c.get("uuid") == lid)
        active_conns += conn_count
        proto = link.get("protocol", DEFAULT_PROTOCOL)
        links_out.append({
            "uuid": lid,
            "label": link["label"],
            "active": allowed,
            "protocol": proto,
            "used_bytes": link.get("used_bytes", 0),
            "used_fmt": fmt_bytes(link.get("used_bytes", 0)),
            "limit_bytes": link.get("limit_bytes", 0),
            "limit_fmt": "∞" if link.get("limit_bytes", 0) == 0 else fmt_bytes(link["limit_bytes"]),
            "expires_at": link.get("expires_at"),
            "vless_link": vless_link_for_link(link, lid, host),
            "sub_url": f"https://{host}/sub/{lid}",
            "connections": conn_count,
            "ip_limit": link.get("ip_limit", 0),
            "speed_limit_bytes": link.get("speed_limit_bytes", 0),
        })

    total_used = sum(l["used_bytes"] for l in links_out)
    return {
        "locked": False,
        "name": sub["name"],
        "desc": sub.get("desc", ""),
        "sub_url": f"https://{host}/sub-group/{uuid_key}",
        "active_connections": active_conns,
        "total_used_fmt": fmt_bytes(total_used),
        "links": links_out,
    }

def _serialize_link_for_admin(link: dict, uid: str, host: str) -> dict:
    """Build one config payload for the admin page."""
    proto = link.get("protocol", DEFAULT_PROTOCOL)
    sub_slug = (link.get("sub_token") or "").strip() or uid
    return {
        "uuid": uid,
        "label": link.get("label", "Config"),
        "note": link.get("note", ""),
        "active": link.get("active", True),
        "expired": is_link_expired(link),
        "allowed": is_link_allowed(link),
        "protocol": proto,
        "trojan_password": link.get("password", "") if split_protocol(proto)[0] == "trojan" else "",
        "used_bytes": link.get("used_bytes", 0),
        "used_fmt": fmt_bytes(link.get("used_bytes", 0)),
        "limit_bytes": link.get("limit_bytes", 0),
        "limit_fmt": "∞" if link.get("limit_bytes", 0) == 0 else fmt_bytes(link["limit_bytes"]),
        "expires_at": link.get("expires_at"),
        "vless_link": vless_link_for_link(link, uid, host),
        "sub_url": f"https://{host}/sub/{sub_slug}",
        "sub_token": link.get("sub_token", ""),
        "connections": sum(1 for c in connections.values() if c.get("uuid") == uid),
        "ip_limit": link.get("ip_limit", 0),
        "speed_limit_bytes": link.get("speed_limit_bytes", 0),
        "port": link.get("port", DEFAULT_PORT),
        "fingerprint": link.get("fingerprint", DEFAULT_FINGERPRINT),
    }


@app.get("/api/admin/all")
async def admin_all_data(request: Request, _=Depends(require_auth)):
    """Build the complete configs and subscription groups payload for the admin page."""
    host = get_host(request)
    async with LINKS_LOCK:
        snap_links = dict(LINKS)
    async with SUBS_LOCK:
        snap_subs = dict(SUBS)

    # Grouping
    groups = []
    grouped_uids = set()
    for sid, s in snap_subs.items():
        link_ids = s.get("link_ids", [])
        group_links = []
        for lid in link_ids:
            link = snap_links.get(lid)
            if not link:
                continue
            group_links.append(_serialize_link_for_admin(link, lid, host))
            grouped_uids.add(lid)
        groups.append({
            "sub_id": sid,
            "name": s.get("name", ""),
            "desc": s.get("desc", ""),
            "has_password": s.get("password_hash") is not None,
            "public_url": f"https://{host}/p/{s.get('uuid_key','')}",
            "sub_url": f"https://{host}/sub-group/{s.get('uuid_key','')}",
            "links": group_links,
        })

    # Ungrouped configs
    ungrouped = []
    for uid, link in snap_links.items():
        if uid not in grouped_uids:
            ungrouped.append(_serialize_link_for_admin(link, uid, host))

    # Aggregate stats
    all_links = list(snap_links.values())
    total_used = sum(l.get("used_bytes", 0) for l in all_links)
    active_count = sum(1 for l in all_links if is_link_allowed(l))
    expired_count = sum(1 for l in all_links if is_link_expired(l))
    disabled_count = sum(1 for l in all_links if not l.get("active", True))

    return {
        "total": len(all_links),
        "active": active_count,
        "expired": expired_count,
        "disabled": disabled_count,
        "total_used_bytes": total_used,
        "total_used_fmt": fmt_bytes(total_used),
        "active_connections": len(connections),
        "groups_count": len(snap_subs),
        "groups": groups,
        "ungrouped": ungrouped,
        "sub_all_url": f"https://{host}/sub-all",
    }

@app.get("/api/public/one/{uuid}")
async def public_single_data(uuid: str, request: Request):
    async with LINKS_LOCK:
        link = LINKS.get(uuid)
    if not link:
        raise HTTPException(status_code=404, detail="not found")
    host = get_host(request)
    allowed = is_link_allowed(link)
    conn_count = sum(1 for c in connections.values() if c.get("uuid") == uuid)

    # Real, persisted per-direction counters (written by check_and_use in the relays).
    # up   = client -> server (what the user uploaded)
    # down = server -> client (what the user downloaded)
    last_online = None
    for c in connections.values():
        if c.get("uuid") == uuid:
            ca = c.get("connected_at")
            if ca and (last_online is None or ca > last_online):
                last_online = ca
    if last_online is None:
        last_online = link.get("last_online")

    used = int(link.get("used_bytes", 0) or 0)
    up_bytes = int(link.get("up_bytes", 0) or 0)
    down_bytes = int(link.get("down_bytes", 0) or 0)
    if up_bytes + down_bytes == 0 and used > 0:
        # Legacy link created before per-direction tracking existed:
        # no real split is available, so fall back to an estimate once.
        up_bytes = int(used * 0.3)
        down_bytes = used - up_bytes
    limit = int(link.get("limit_bytes", 0) or 0)
    remaining = max(0, limit - used) if limit > 0 else 0

    proto = link.get("protocol", DEFAULT_PROTOCOL)
    sub_slug = (link.get("sub_token") or "").strip() or uuid

    return {
        "uuid": uuid,
        "label": link.get("label", "Config"),
        "note": link.get("note", ""),
        "active": allowed,
        "expired": is_link_expired(link),
        "protocol": proto,
        "used_bytes": used,
        "used_fmt": fmt_bytes(used),
        "limit_bytes": limit,
        "limit_fmt": "∞" if limit == 0 else fmt_bytes(limit),
        "remaining_bytes": remaining,
        "remaining_fmt": "∞" if limit == 0 else fmt_bytes(remaining),
        "up_bytes": up_bytes,
        "up_fmt": fmt_bytes(up_bytes),
        "down_bytes": down_bytes,
        "down_fmt": fmt_bytes(down_bytes),
        "expires_at": link.get("expires_at"),
        "last_online": last_online,
        "vless_link": vless_link_for_link(link, uuid, host),
        "sub_url": f"https://{host}/sub/{sub_slug}",
        "connections": conn_count,
        "ip_limit": link.get("ip_limit", 0),
        "speed_limit_bytes": link.get("speed_limit_bytes", 0),
    }

# ═══════════════════════════════════════════════════════════════════════════
#  SERVER INFO — IP + Location (cached)
# ═══════════════════════════════════════════════════════════════════════════
_server_info_cache: dict | None = None
_server_info_lock = asyncio.Lock()

_COUNTRY_FA = {
    "IR": "ایران", "US": "آمریکا", "DE": "آلمان", "NL": "هلند", "FR": "فرانسه",
    "GB": "انگلستان", "TR": "ترکیه", "AE": "امارات", "CA": "کانادا",
    "IN": "هند", "SG": "سنگاپور", "JP": "ژاپن", "CN": "چین", "RU": "روسیه",
    "IT": "ایتالیا", "ES": "اسپانیا", "SE": "سوئد", "FI": "فینلاند",
    "NO": "نروژ", "DK": "دانمارک", "PL": "پلند", "AT": "اتریش",
    "CH": "سوئیس", "BE": "بلژیک", "IE": "ایرلند", "PT": "پرتغال",
    "RO": "رومانی", "BG": "بلغارستان", "HU": "مجارستان", "CZ": "چک",
    "GR": "یونان", "UA": "اوکراین", "KR": "کره جنوبی", "AU": "استرالیا",
    "BR": "برزیل", "MX": "مکزیک", "AR": "آرژانتین", "ZA": "آفریقای جنوبی",
    "EG": "مصر", "SA": "عربستان", "QA": "قطر", "KW": "کویت",
    "BH": "بحرین", "OM": "عمان", "JO": "اردن", "LB": "لبنان",
    "IQ": "عراق", "PK": "پاکستان", "AF": "افغانستان", "AZ": "آذربایجان",
    "AM": "ارمنستان", "GE": "گرجستان", "TM": "ترکمنستان", "UZ": "ازبکستان",
    "KZ": "قزاقستان", "KG": "قرقیزستان", "TJ": "تاجیکستان",
}

def _cc_to_flag(cc: str) -> str:
    """Convert a country code to its flag emoji."""
    cc = (cc or "").upper()
    if len(cc) != 2 or not cc.isalpha():
        return "🌐"
    try:
        return chr(0x1F1E6 + ord(cc[0]) - 65) + chr(0x1F1E6 + ord(cc[1]) - 65)
    except Exception:
        return "🌐"

def _cc_to_fa(cc: str) -> str:
    return _COUNTRY_FA.get((cc or "").upper(), "")

@app.get("/api/server-info")
async def api_server_info(_=Depends(require_auth)):
    """Fetch and cache server IP and geolocation information once."""
    global _server_info_cache
    if _server_info_cache is not None:
        return _server_info_cache
    async with _server_info_lock:
        if _server_info_cache is not None:
            return _server_info_cache
        try:
            r = await http_client.get(
                "http://ip-api.com/json/?fields=status,country,countryCode,regionName,city,isp,org,as,query,timezone",
                timeout=10,
            )
            data = r.json()
            if data.get("status") == "success":
                cc = data.get("countryCode", "")
                _server_info_cache = {
                    "ip": data.get("query", ""),
                    "country": data.get("country", ""),
                    "country_fa": _cc_to_fa(cc),
                    "country_code": (cc or "").lower(),
                    "flag": _cc_to_flag(cc),
                    "region": data.get("regionName", ""),
                    "city": data.get("city", ""),
                    "isp": data.get("isp", ""),
                    "org": data.get("org", ""),
                    "asn": data.get("as", ""),
                    "timezone": data.get("timezone", ""),
                }
                logger.info(f"Server info cached: {_server_info_cache['ip']} ({_server_info_cache['country']})")
            else:
                _server_info_cache = {"error": "unavailable"}
        except Exception as e:
            logger.warning(f"server-info fetch failed: {e}")
            _server_info_cache = {"error": "unavailable"}
    return _server_info_cache

# ── HTML pages (login + dashboard) ─────────────────────────────────────────
from pages import LOGIN_HTML, DASHBOARD_HTML

@app.get("/login", response_class=HTMLResponse)
async def login_page(request: Request):
    return RedirectResponse(url="/")

@app.get("/dashboard", response_class=HTMLResponse)
async def dashboard(request: Request):
    if not await is_valid_session(request.cookies.get(SESSION_COOKIE)):
        return RedirectResponse(url="/")
    await ensure_default_link()
    return HTMLResponse(content=DASHBOARD_HTML)

@app.get("/test-ws", response_class=HTMLResponse)
async def test_ws_redirect():
    return HTMLResponse(content="<script>location.href='/dashboard'</script>")

if __name__ == "__main__":
    uvicorn.run(
        "main:app", host="0.0.0.0", port=CONFIG["port"], log_level="info", workers=1,
        ws_ping_interval=20.0,    # server→client WS ping keeps idle tunnels alive through the edge proxy
        ws_ping_timeout=60.0,     # tolerate short event-loop stalls / slow mobile links (default 20s kills the tunnel)
        timeout_keep_alive=75,    # default 5s races with the proxy reusing idle upstream connections (XHTTP POSTs)
    )
