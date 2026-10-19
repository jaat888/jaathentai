"""HentaiJaat web app (Flask version, Termux friendly).

Needs only: flask, requests, beautifulsoup4  (all pure Python, no compiling).
Run:  python app.py
"""
import base64
import gzip
import hashlib
import math
import hmac
import ipaddress
import json
import os
import re
import socket
import itertools
import queue
import shutil
import tempfile
import threading
import time
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from io import BytesIO
from urllib.parse import quote, urlencode, urljoin, urlparse

import requests
from bs4 import BeautifulSoup
from flask import Flask, Response, abort, jsonify, redirect, render_template_string, request, session
from werkzeug.security import check_password_hash, generate_password_hash

try:
    from PIL import Image
except ImportError:
    Image = None

BASE = "https://hentai20.io"
TIMEOUT = 15
MAX_IMAGE_BYTES = 15 * 1024 * 1024
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Linux; Android 13; Mobile) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36"
    ),
    "Referer": BASE + "/",
    "Accept-Language": "en-US,en;q=0.9",
}

# 1x1 transparent gif, returned when an image cannot be fetched
EMPTY_GIF = base64.b64decode("R0lGODlhAQABAIAAAAAAAP///yH5BAEAAAAALAAAAAABAAEAAAIBRAA7")

app = Flask(__name__)
app.url_map.merge_slashes = False  # needed so /proxy/https://... keeps its //
app.json.sort_keys = False
app.secret_key = os.environ.get("SECRET_KEY") or hashlib.sha256(("h20" + os.environ.get("APP_PASSWORD", "") + os.environ.get("SQL_URL", "x")).encode()).hexdigest()
app.permanent_session_lifetime = 60 * 60 * 24 * 30
app.config.update(SESSION_COOKIE_SAMESITE="Lax", SESSION_COOKIE_HTTPONLY=True,
                  SESSION_COOKIE_SECURE=os.environ.get("COOKIE_SECURE", "1") != "0")

BRAND = "HentaiJaat"
TG_URL = os.environ.get("SUPPORT_TG", "https://t.me/mollad_jaat").strip()
MINPW = 6                                                   # minimum password length
SIGNUP_OPEN = os.environ.get("SIGNUP_OPEN", "1") != "0"    # anyone can create an account
MAX_USERS = int(os.environ.get("MAX_USERS", "1000"))
TRUSTED_PROXIES = int(os.environ.get("TRUSTED_PROXIES", "1"))  # proxies in front of the app (used for the client IP)
app.jinja_env.globals.update(BRAND=BRAND, TG=TG_URL)

http = requests.Session()
http.headers.update(HEADERS)
http.mount("https://", requests.adapters.HTTPAdapter(pool_connections=16, pool_maxsize=40))
http.mount("http://", requests.adapters.HTTPAdapter(pool_connections=16, pool_maxsize=40))


class UpstreamError(Exception):
    def __init__(self, status, detail=""):
        super().__init__(f"upstream status {status} {detail}")
        self.status = status
        self.detail = detail


API_KEY = os.environ.get("API_KEY", "").strip()
APP_PASSWORD = os.environ.get("APP_PASSWORD", "").strip()
ADMIN_NAME = os.environ.get("ADMIN_USER", "admin").strip() or "admin"
LOCAL_MODE = False  # becomes True only when started with `python app.py`


PUBLIC = ("/login", "/signup", "/admin/login", "/favicon.ico", "/manifest.json", "/sw.js", "/icon-192.png", "/icon-512.png")


@app.before_request
def gate():
    """Website: users log in at /login, admin at /admin/login. /hentai/* also accepts API_KEY."""
    p = request.path
    if request.method in ("POST", "PUT", "PATCH", "DELETE"):
        # CSRF: block cross-site requests; every /api/ call must come from our own JS (custom header)
        if request.headers.get("Sec-Fetch-Site", "") == "cross-site":
            abort(403)
        if p.startswith("/api/") and request.headers.get("X-Req") != "1":
            return jsonify({"ok": False, "msg": "Bad request."}), 403
    if p in PUBLIC:
        return None
    me = cur()
    if me and session_ok(me):
        if not p.startswith("/hentai"):
            warm()
        return None
    if me:
        session.clear()
    if API_KEY and p.startswith("/hentai"):
        given = request.headers.get("X-API-Key") or request.args.get("key", "")
        if given == API_KEY:
            return None
        return jsonify({"status_code": 401, "message": "invalid api key"}), 401
    if p.startswith("/api/"):
        return jsonify({"ok": False, "msg": "Please sign in."}), 401
    if p.startswith("/admin"):
        return redirect("/admin/login")
    return redirect("/login")


@app.after_request
def squeeze(resp):
    """gzip html/json (smaller = faster on mobile data)."""
    try:
        if (resp.status_code == 200 and not resp.is_streamed and not resp.direct_passthrough
                and resp.mimetype in ("text/html", "application/json", "application/javascript", "application/manifest+json")
                and "Content-Encoding" not in resp.headers and "gzip" in request.headers.get("Accept-Encoding", "")):
            data = resp.get_data()
            if len(data) > 900:
                resp.set_data(gzip.compress(data, 5))
                resp.headers["Content-Encoding"] = "gzip"
                resp.headers["Vary"] = "Accept-Encoding"
        if resp.mimetype == "text/html":
            resp.headers["Cache-Control"] = "no-cache"
        resp.headers.setdefault("X-Content-Type-Options", "nosniff")
        resp.headers.setdefault("X-Frame-Options", "DENY")
        resp.headers.setdefault("Referrer-Policy", "same-origin")
        resp.headers.setdefault("Permissions-Policy", "camera=(), microphone=(), geolocation=()")
        if request.headers.get("X-Forwarded-Proto", "") == "https":
            resp.headers.setdefault("Strict-Transport-Security", "max-age=15552000")
    except Exception:
        pass
    return resp


# ----------------------------------------------------------------- helpers
def reply(data=None, status=200, message=None):
    msg = message or {200: "successful", 404: "not found"}.get(status, "error")
    body = {"status_code": status, "message": msg}
    if data is not None:
        body["data"] = data
    return jsonify(body), status


def fetch_html(path, params=None, tries=4, timeout=TIMEOUT):
    """GET with retries; site often gives temporary 502/503/timeouts."""
    last = None
    for i in range(tries):
        try:
            r = http.get(BASE + path, params=params, timeout=timeout)
            if r.status_code == 200 and not re.search(r"Just a moment|cf-chl|challenge-platform", r.text[:4000]):
                return BeautifulSoup(r.text, "html.parser")
            last = f"HTTP {r.status_code}" if r.status_code != 200 else "Cloudflare challenge page (site bot-check)"
            if r.status_code in (404, 410):
                raise UpstreamError(404)
        except requests.RequestException as ex:
            last = f"{type(ex).__name__}: {str(ex)[:120]}"
        app.logger.warning("fetch %s try %d/%d failed: %s", path, i + 1, tries, last)
        time.sleep(0.8 * (i + 1))
    raise UpstreamError(502, last)


_OLDNAME = re.compile(r"hentai\s*20(?:\.\w+)?|\bh20\b", re.I)


def text_of(el, default=""):
    return _OLDNAME.sub(BRAND, el.get_text(strip=True)) if el else default


def img_src(img):
    if not img:
        return None
    for attr in ("src", "data-src", "data-lazy-src"):
        val = img.get(attr)
        if val and not val.startswith("data:"):
            return val
    return None


def chapter_id_from_href(href):
    return urlparse(href).path.strip("/")


@app.errorhandler(UpstreamError)
def handle_upstream(e):
    if e.status == 404:
        return reply(status=404, message="not found on source site")
    return reply(status=502, message=f"source site error: {e.detail or e.status}")


@app.errorhandler(Exception)
def handle_any(e):
    from werkzeug.exceptions import HTTPException
    if isinstance(e, HTTPException):
        return e
    # parsing broke (site layout changed) or something unexpected
    app.logger.exception("unhandled error")
    return reply(status=500, message="server error")


# ------------------------------------------------------------------ parsers
def parse_listing(soup):
    mangas = []
    for a in soup.select(".listupd .bsx > a"):
        href = a.get("href", "")
        parts = [p for p in href.split("/") if p]
        mangas.append(
            {
                "title": a.get("title") or text_of(a.select_one(".tt")),
                "image_url": img_src(a.select_one("img")),
                "colored": bool(a.select_one(".colored")),
                "slug": parts[-1] if parts else None,
                "latest_chapter": text_of(a.select_one(".epxs")),
                "score": text_of(a.select_one(".numscore")),
            }
        )
    return mangas


def parse_manga(manga_id, soup):
    cover = soup.select_one(".attachment-.size-.wp-post-image") or soup.select_one(
        ".wp-post-image"
    )
    desc_el = soup.select_one(".entry-content.entry-content-single > p") or soup.select_one(
        ".entry-content.entry-content-single"
    )

    info = {"score": text_of(soup.select_one(".num"))}
    for tick in soup.select(".imptdt"):
        raw = tick.get_text(" ", strip=True)
        key = (
            raw.replace("Posted On", "created_at")
            .replace("Updated On", "updated_at")
            .split(" ")[0]
            .lower()
            .strip()
        )
        if key == "type":
            info["type"] = text_of(tick.select_one("a"))
        elif key in ("created_at", "updated_at", "author"):
            info[key] = text_of(tick.select_one("i"))
        elif key == "status":
            info["status"] = text_of(tick.select_one("i")) or raw.replace("Status", "", 1).strip()

    genres = []
    for a in soup.select(".mgen a, .seriestugenre a"):
        parts = [p for p in a.get("href", "").split("/") if p]
        if parts and text_of(a):
            genres.append({"name": text_of(a), "slug": parts[-1]})

    chapter_links = soup.select("#chapterlist .eph-num > a")
    if not chapter_links:  # fallback to the old behaviour (skip first element)
        chapter_links = soup.select(".eph-num > a")[1:]

    chapters = []
    for a in chapter_links:
        chapters.append(
            {
                "name": text_of(a.select_one(".chapternum")),
                "chapter_id": chapter_id_from_href(a.get("href", "")),
                "date": text_of(a.select_one(".chapterdate")),
            }
        )

    return {
        "manga_id": manga_id,
        "image_url": img_src(cover),
        "title": (cover.get("alt") if cover else None) or text_of(soup.select_one(".entry-title")),
        **info,
        "description": text_of(desc_el),
        "genres": genres,
        "colored": bool(soup.select_one(".colored")) or any(g["name"].lower() == "colored" for g in genres),
        "related": [m for m in parse_listing(soup) if m["slug"] and m["slug"] != manga_id][:12],
        "chapters": chapters,
    }


def parse_panels(chapter_id, soup):
    # 1) current layout: plain <img> tags inside #readerarea
    imgs = soup.select("#readerarea img, .readerarea img")
    # 2) older layout fallback
    if not imgs:
        imgs = soup.select(".alignnone")

    panels, seen = [], set()
    for img in imgs:
        src = img_src(img)
        if src and src not in seen:
            seen.add(src)
            panels.append({"image_url": src})

    # 3) last resort: ts_reader JSON embedded in a <script>
    if not panels:
        for script in soup.find_all("script"):
            code = script.string or ""
            if "ts_reader" not in code:
                continue
            m = re.search(r'"images"\s*:\s*(\[.*?\])', code, re.S)
            if m:
                try:
                    for src in json.loads(m.group(1)):
                        if isinstance(src, str) and src not in seen:
                            seen.add(src)
                            panels.append({"image_url": src})
                except ValueError:
                    pass
            break

    return {
        "chapter_id": chapter_id,
        "chapter_title": text_of(soup.select_one(".entry-title")),
        "panels": panels,
    }


# ------------------------------------------------------------- image proxy
_HOSTOK = {}


def is_public_host(host):
    c = _HOSTOK.get(host)
    if c and time.time() - c[0] < 600:
        return c[1]
    r = _check_host(host)
    _HOSTOK[host] = (time.time(), r)
    return r


def _check_host(host):
    """Reject localhost / private / link-local targets (basic SSRF guard)."""
    try:
        infos = socket.getaddrinfo(host, None)
    except socket.gaierror:
        return False
    for info in infos:
        ip = ipaddress.ip_address(info[4][0])
        if (
            ip.is_private
            or ip.is_loopback
            or ip.is_link_local
            or ip.is_multicast
            or ip.is_reserved
            or ip.is_unspecified
        ):
            return False
    return True


def fetch_image(url, max_redirects=3):
    for _ in range(max_redirects + 1):
        parsed = urlparse(url)
        if parsed.scheme not in ("http", "https") or not parsed.hostname:
            return None
        if not is_public_host(parsed.hostname):
            return None
        try:
            r = http.get(url, timeout=TIMEOUT, stream=True, allow_redirects=False)
        except requests.RequestException:
            return None
        if r.status_code in (301, 302, 303, 307, 308):
            url = urljoin(url, r.headers.get("Location", ""))
            r.close()
            continue
        if r.status_code != 200:
            r.close()
            return None
        ctype = r.headers.get("Content-Type", "").split(";")[0].strip().lower()
        if not ctype.startswith("image/"):
            r.close()
            return None
        data = bytearray()
        for chunk in r.iter_content(65536):
            data.extend(chunk)
            if len(data) > MAX_IMAGE_BYTES:
                r.close()
                return None
        return bytes(data), ctype
    return None


# ------------------------------------------------------------------ routes
@app.get("/hentai/proxy/<path:image_url>")
def proxy(image_url):
    # path converter drops the query string and may squash "//"
    if image_url.startswith(("http:/", "https:/")) and "://" not in image_url:
        image_url = image_url.replace(":/", "://", 1)
    extra = {k: v for k, v in request.args.items() if k != "key"}
    if extra:
        image_url += "?" + urlencode(extra)

    result = fetch_image(image_url)
    if not result:
        return Response(EMPTY_GIF, mimetype="image/gif", status=404)
    data, ctype = result
    resp = Response(data, mimetype=ctype)
    resp.headers["Cache-Control"] = "public, max-age=604800, immutable"
    return resp


@app.get("/hentai/filter")
def filter_mangas():
    page = request.args.get("page", "1")
    if not page.isdigit():
        return reply(status=400, message="invalid page")

    params = {"page": page}
    if request.args.get("status"):
        params["status"] = request.args["status"]
    if request.args.get("type"):
        params["type"] = request.args["type"]
    if request.args.get("sort"):
        params["order"] = request.args["sort"]
    if request.args.get("genre"):
        params["genre[]"] = request.args["genre"]

    soup = fetch_html("/manga/", params=params)
    has_next = bool(soup.select_one("a.next.page-numbers, .hpage a.r"))
    return reply(
        {
            "mangas": parse_listing(soup),
            "pagination": {"page": page, "has_next": has_next},
        }
    )


@app.get("/hentai/search")
def search():
    q = request.args.get("q", "").strip()
    page = request.args.get("page", "1")
    if not q:
        return reply(status=400, message="missing q")
    if not page.isdigit() or int(page) < 1:
        return reply(status=400, message="invalid page")

    path = "/" if page == "1" else f"/page/{page}/"
    soup = fetch_html(path, params={"s": q})
    has_next = bool(soup.select_one("a.next.page-numbers, .hpage a.r"))
    return reply(
        {
            "query": q,
            "mangas": parse_listing(soup),
            "pagination": {"page": page, "has_next": has_next},
        }
    )


@app.get("/hentai/read/<path:chapter_id>")
def read(chapter_id):
    chapter_id = chapter_id.strip("/")
    soup = fetch_html(f"/{chapter_id}/")
    return reply(parse_panels(chapter_id, soup))


@app.get("/hentai/<manga_id>")
def manga(manga_id):
    soup = fetch_html(f"/manga/{manga_id}/")
    return reply({"manga": parse_manga(manga_id, soup)})



# ======================= DOWNLOADER + WEB UI (cloud: PDFs are stored in SQL storage) =======================
UI_ENABLED = True
SQL_BASE = os.environ.get("SQL_URL", "https://cloudservice.blitz.cloud/p/pZYFyB9nA5jW9Qc9fmez-taFy6vLYOLj").strip().rstrip("/")
SQL_URL = SQL_BASE if SQL_BASE.endswith("/sql") else SQL_BASE + "/sql"
CHUNK = max(32, int(os.environ.get("CHUNK_KB", "192"))) * 1024   # raw bytes per DB row
PER_INSERT = 3                                                     # rows per INSERT request
UP_PAR = max(1, min(int(os.environ.get("UP_PAR", "4")), 8))        # parallel INSERT requests
DL_PAR = 4                                                         # parallel chunk reads while downloading a PDF
IMG_PAR = max(1, min(int(os.environ.get("IMG_PAR", "12")), 24))    # parallel image downloads + conversions
NUM_WORKERS = max(1, min(int(os.environ.get("JOB_WORKERS", "2")), 4))  # jobs running at the same time
USER_MAX_CH = int(os.environ.get("USER_MAX_CH", "0"))              # chapters per request for normal users (0 = no limit)
AUTO_MIN = max(10, int(os.environ.get("AUTO_MIN", "360")))            # auto-update check every N minutes
USER_MAX_JOBS = 2                                                  # active jobs per normal user
TZ_MIN = int(os.environ.get("TZ_MIN", "330"))                      # minutes added to UTC for display (330 = IST)
LOCK = threading.Lock()
SCHEMA_LOCK = threading.Lock()
JOBS, JOBQ = [], queue.Queue()
_workers = []
_schema = {"ok": False}
_started = {"bg": False}
JOBS_LOCK = threading.Lock()
_job_ids = itertools.count(1)
# Work folder that survives a crash/restart of the app: downloaded images and finished PDFs stay here until uploaded,
# so a restart continues instead of downloading everything again.
SPOOL = os.environ.get("SPOOL_DIR") or os.path.join(tempfile.gettempdir(), "hjspool")
SPOOL_KEEP = int(os.environ.get("SPOOL_KEEP_MIN", "150")) * 60
os.makedirs(SPOOL, exist_ok=True)
EXT = {"image/jpeg": "jpg", "image/png": "png", "image/webp": "webp", "image/gif": "gif"}

sqlhttp = requests.Session()
sqlhttp.mount("https://", requests.adapters.HTTPAdapter(pool_connections=8, pool_maxsize=32))
sqlhttp.mount("http://", requests.adapters.HTTPAdapter(pool_connections=8, pool_maxsize=32))


# ----------------------------------------------------------------- SQL storage
def sql(stmt, params=(), retries=3):
    last = None
    for i in range(retries):
        try:
            r = sqlhttp.post(SQL_URL, json={"sql": stmt, "params": list(params)}, timeout=60)
            try:
                j = r.json()
            except ValueError:
                j = {}
            if r.status_code == 200 and not (isinstance(j, dict) and j.get("error")):
                return j
            last = f"HTTP {r.status_code} {r.text[:200]}"
        except requests.RequestException as ex:
            last = f"{type(ex).__name__}: {str(ex)[:120]}"
        app.logger.warning("sql try %d/%d failed: %s", i + 1, retries, last)
        if i < retries - 1:
            time.sleep(1 + i)
    raise RuntimeError(f"SQL storage error: {last}")


def q(stmt, params=()):
    j = sql(stmt, params)
    cols = j.get("columns", [])
    return [dict(zip(cols, row)) for row in j.get("rows", [])], j


def par(*fns):
    """Run several small functions at the same time and return their results in order."""
    with ThreadPoolExecutor(len(fns)) as ex:
        futs = [ex.submit(f) for f in fns]
        return [f.result() for f in futs]


def init_schema():
    if _schema["ok"]:
        return
    with SCHEMA_LOCK:
        if _schema["ok"]:
            return
        sql("create table if not exists kv(k text primary key, v text)")
        sql("create table if not exists files(id integer primary key autoincrement, slug text, name text, size integer, parts integer, created text, uid integer)")
        try:
            sql("select uid from files limit 1", retries=1)
        except RuntimeError:  # old table without owner column
            sql("alter table files add column uid integer")
        try:
            sql("select tg from files limit 1", retries=1)
        except RuntimeError:  # old table without the storage-file column
            sql("alter table files add column tg text")
        sql("create table if not exists chunks(file_id integer, n integer, data text, primary key(file_id, n))")
        sql("create table if not exists users(id integer primary key autoincrement, name text unique, pw text, created integer)")
        sql("create table if not exists hist(uid integer, slug text, title text, cover text, cid text, cname text, ts integer, primary key(uid, slug))")
        sql("create table if not exists bookmarks(uid integer, slug text, title text, cover text, ts integer, primary key(uid, slug))")
        try:
            sql("select status from bookmarks limit 1", retries=1)
        except RuntimeError:  # reading status column (reading / completed / plan)
            sql("alter table bookmarks add column status text")
        sql("create table if not exists reads(uid integer, slug text, cid text, ts integer, primary key(uid, cid))")
        _schema["ok"] = True


def warm():
    """Create / migrate tables once, before any page runs parallel queries."""
    if not _schema["ok"]:
        try:
            init_schema()
        except Exception:
            app.logger.warning("schema init failed", exc_info=True)
            return
    if _schema["ok"] and not _started["bg"]:
        _started["bg"] = True
        try:
            resume_jobs()
        except Exception:
            app.logger.warning("resume failed", exc_info=True)
        threading.Thread(target=auto_loop, daemon=True).start()
        threading.Thread(target=housekeep_loop, daemon=True).start()


def safe(name):
    return re.sub(r"[^\w\-. ]", "_", name).strip()[:60] or "manga"


def fmt_ts(ts):
    try:
        return time.strftime("%d %b, %H:%M", time.gmtime(int(ts) + TZ_MIN * 60))
    except Exception:
        return ""


# per-user state (which chapters are already downloaded). uid 0 = admin keeps the old 'state' key.
def skey(uid):
    return "state" if not uid else f"state_{uid}"


_STC = {}


def load_state(uid=0):
    c = _STC.get(uid)
    if c and time.time() - c[0] < 5:  # tiny cache: pages open without waiting for storage every time
        return json.loads(c[1])
    init_schema()
    rows, _ = q("select v from kv where k=?", [skey(uid)])
    raw = rows[0]["v"] if rows else "{}"
    _STC[uid] = (time.time(), raw)
    try:
        return json.loads(raw)
    except (ValueError, KeyError):
        return {}


def save_state(uid, st):
    init_schema()
    raw = json.dumps(st, ensure_ascii=False)
    sql("insert or replace into kv(k, v) values(?, ?)", [skey(uid), raw])
    _STC[uid] = (time.time(), raw)


STORE_BASE = SQL_BASE[:-4] if SQL_BASE.endswith("/sql") else SQL_BASE   # .../p/KEY


STORE_CHUNK = int(float(os.environ.get("STORE_CHUNK_MB", "18")) * 1048576)   # must be the same as CHUNK_MB of the storage
UP_PIECE_CHUNKS = max(1, min(int(os.environ.get("UP_PIECE_CHUNKS", "2")), 4))    # storage chunks sent per request (its own dashboard sends 2-4)


class _UploadBody:
    """File-like upload body with a known length. With it requests sends a plain Content-Length.
    (A generator body made requests send 'Transfer-Encoding: chunked' AS WELL as Content-Length; a proxy in front
    of the storage then reads the raw bytes as chunks and the upload breaks.)"""

    def __init__(self, path, offset, size, cb=None, end=None, stop=None):
        self.stop = stop
        self.f = open(path, "rb")
        self.f.seek(offset)
        self.start, self.size, self.cb = offset, size, cb
        self.total = (size if end is None else end) - offset
        self.sent, self._mark = offset, offset

    def __len__(self):
        return self.total

    def read(self, n=-1):
        if self.stop and self.stop():
            raise Cancelled()
        left = self.total - (self.sent - self.start)
        if left <= 0:
            return b""
        if n is None or n < 0 or n > (1 << 20):
            n = 1 << 20
        b = self.f.read(min(n, left))
        self.sent += len(b)
        if self.cb and self.sent - self._mark >= (1 << 20):
            self._mark = self.sent
            self.cb(min(0.99, self.sent / max(self.size, 1)))
        return b

    def close(self):
        try:
            self.f.close()
        except Exception:
            pass


class StorageRefused(Exception):
    pass


class Cancelled(StorageRefused):
    """The user pressed Cancel."""


def _short(r):
    """Response text for an error message; an html error page (proxy) is reduced to its title."""
    t = r.text or ""
    if "<html" in t[:300].lower():
        m = re.search(r"<title>(.*?)</title>", t, re.S | re.I)
        return (m.group(1).strip() if m else "html page")[:80]
    return t[:200]


def tg_up(tid, path, name, cb=None, stop=None):
    """Send a PDF to the storage /upload endpoint in pieces (a multiple of the storage chunk each; the proxy in front
    of the storage refuses one huge request with 413). Resumes from where it stopped if the link breaks."""
    size = os.path.getsize(path)
    fails = waits = 0
    pc = UP_PIECE_CHUNKS
    while True:
        if stop and stop():
            raise Cancelled()
        body = None
        try:
            r = sqlhttp.get(f"{STORE_BASE}/status/{tid}", timeout=30)
            st = r.json() if r.status_code == 200 else {}
            if st.get("done"):
                return tid
            if st.get("busy"):  # the storage is still saving the last piece
                waits += 1
                if waits > 300:
                    raise StorageRefused("storage stays busy")
                time.sleep(2)
                continue
            have = int(st.get("stored", 0)) if r.status_code == 200 else 0
            end = min(have + pc * STORE_CHUNK, size)
            body = _UploadBody(path, have, size, cb, end, stop) if end > have else b""
            u = f"{STORE_BASE}/upload?" + urlencode({"id": tid, "name": name, "offset": have, "size": size})
            r = requests.post(u, data=body, headers={"Content-Type": "application/octet-stream"}, timeout=(15, 900))
            if r.status_code == 200:
                fails = waits = 0
                if r.json().get("done"):
                    return tid
                continue  # piece stored, send the next one
            last = f"HTTP {r.status_code} {_short(r)}"
            if r.status_code == 413 and "<html" in (r.text or "")[:300].lower() and pc > 1:
                pc -= 1  # the proxy refuses requests this big: use smaller pieces
                app.logger.warning("proxy said 413, pieces are now %d chunk(s)", pc)
                continue
            if r.status_code == 409 and "already running" in (r.text or ""):
                # an earlier, cut connection is still being closed on the storage side: wait for it, don't give up
                waits += 1
                if waits > 300:
                    raise StorageRefused(last)
                time.sleep(5)
                continue
            if r.status_code in (400, 401, 403, 404, 413, 503):  # storage refuses (no bot enabled, too big...): not worth retrying
                raise StorageRefused(last)
            raise RuntimeError(last)
        except StorageRefused:
            raise
        except Exception as ex:
            if stop and stop():
                raise Cancelled()
            fails += 1
            app.logger.warning("upload try %d failed: %s", fails, str(ex)[:200])
            if fails >= 10:
                raise RuntimeError(f"upload failed after {fails} tries: {str(ex)[:200]}")
            time.sleep(min(2 * fails, 20))
        finally:
            if hasattr(body, "close"):
                body.close()


def tg_rm(tid):
    if not tid:
        return
    try:
        sqlhttp.delete(f"{STORE_BASE}/file/{tid}", timeout=60)
    except Exception:
        app.logger.warning("could not delete stored file %s", tid, exc_info=True)


def store_pdf(path, name, slug, uid, cb=None, stop=None, ids=None, on_ids=None):
    """Store a PDF in the storage file API (the storage cuts it into 18 MB pieces itself).
    There is NO SQL fallback any more: a PDF stored as SQL rows only fills the database and makes the storage send
    endless 1 MB blocks to Telegram. A failed upload is reported with its real error instead.
    ids = {"fid":..,"tid":..} of an earlier, interrupted try: the upload then continues where it stopped.
    On a failure the row and the pieces already stored are KEPT (the next try resumes); only Cancel removes them."""
    init_schema()
    size = os.path.getsize(path)
    ids = ids if ids is not None else {}
    fid, tid = ids.get("fid"), ids.get("tid")
    if fid:
        try:
            if not q("select 1 as x from files where id=?", [fid])[0]:
                fid = tid = None
        except Exception:
            pass
    if not fid:
        j = sql("insert into files(slug, name, size, parts, created, uid) values(?,?,?,0,datetime('now'),?)",
                [slug, name, size, uid])
        fid = j.get("last_id") or q("select max(id) as m from files")[0][0]["m"]
        tid = f"pdf{fid}x{int(time.time())}"
        ids.update(fid=fid, tid=tid)
        if on_ids:
            on_ids(fid, tid)
    try:
        tg_up(tid, path, name, cb, stop)
        sql("update files set tg=?, parts=1 where id=?", [tid, fid])  # parts>0 = finished; only then it shows in Library
        return fid
    except Cancelled:
        tg_rm(tid)
        try:
            sql("delete from files where id=?", [fid])
        except Exception:
            pass
        raise
    except Exception as ex:
        app.logger.warning("storage upload failed: %s", str(ex)[:300])
        raise RuntimeError(f"storage upload failed: {str(ex)[:250]}")


def delete_file(fid, owner):
    rows, _ = q("select tg from files where id=?", [fid])
    if rows and rows[0].get("tg"):
        tg_rm(rows[0]["tg"])
    sql("delete from chunks where file_id=?", [fid])
    sql("delete from files where id=?", [fid])
    with LOCK:
        st = load_state(owner)
        for rec in st.values():
            for ch in rec.get("chapters", {}).values():
                if ch.get("file_id") == fid:
                    ch.pop("file_id", None)
        save_state(owner, st)


# ----------------------------------------------------------------- users / session
def cur():
    """Logged-in user as {'uid','name','admin'} or None. uid 0 = admin (APP_PASSWORD)."""
    uid = session.get("uid")
    if uid is None:
        if LOCAL_MODE and not APP_PASSWORD and request.remote_addr in ("127.0.0.1", "::1"):
            return {"uid": 0, "name": ADMIN_NAME, "admin": True}
        return None
    return {"uid": uid, "name": session.get("name", ""), "admin": uid == 0}


_SV = {"t": 0.0, "ids": set(), "d": {}, "ok": False, "busy": False}


def refresh_sv():
    """Reload user list + 'logout everywhere' counters (runs in background, never blocks a click)."""
    if _SV["busy"]:
        return
    _SV["busy"] = True
    try:
        init_schema()
        rows, _ = q("select id from users")
        ids = {r["id"] for r in rows}
        rows, _ = q("select k, v from kv where k like 'sv\\_%' escape '\\'")
        d = {}
        for r in rows:
            try:
                d[int(r["k"][3:])] = int(r["v"])
            except ValueError:
                pass
        _SV.update(ids=ids, d=d, ok=True)
    except Exception:
        app.logger.warning("session refresh failed", exc_info=True)
    finally:
        _SV["t"] = time.time()
        _SV["busy"] = False


def session_ok(me):
    if _SV["t"] == 0.0:
        refresh_sv()
    elif time.time() - _SV["t"] > 30 and not _SV["busy"]:
        threading.Thread(target=refresh_sv, daemon=True).start()
    if not _SV["ok"]:
        return True  # storage unreachable right now: don't lock people out
    if me["uid"] != 0 and me["uid"] not in _SV["ids"]:
        return False  # user was deleted
    return session.get("sv", 0) == _SV["d"].get(me["uid"], 0)


def bump_sv(uid):
    """Log this account out on every device (old cookies stop working). Returns the new counter."""
    n = _SV["d"].get(uid, 0) + 1
    sql("insert or replace into kv(k, v) values(?, ?)", [f"sv_{uid}", str(n)])
    _SV["d"][uid] = n
    return n


def start_session(uid, name):
    session.clear()
    session.permanent = True
    session["uid"], session["name"], session["sv"] = uid, name, _SV["d"].get(uid, 0)


_FAIL = {}


def client_ip():
    """Real client IP. Takes the entry added by our own proxy (right side of X-Forwarded-For), because the
    left side can be faked by the client."""
    xff = [x.strip() for x in request.headers.get("X-Forwarded-For", "").split(",") if x.strip()]
    if TRUSTED_PROXIES > 0 and len(xff) >= TRUSTED_PROXIES:
        return xff[-TRUSTED_PROXIES]
    return request.remote_addr or "?"


def lock_left(key):
    e = _FAIL.get(key)
    return int(e[1] - time.time()) if e and e[1] > time.time() else 0


def note_fail(key, limit=5):
    now = time.time()
    if len(_FAIL) > 2000:  # drop old entries only; never wipe active blocks
        for k in [k for k, v in _FAIL.items() if now - v[2] > 3600]:
            _FAIL.pop(k, None)
        if len(_FAIL) > 4000:
            for k in sorted(_FAIL, key=lambda k: _FAIL[k][2])[:1000]:
                _FAIL.pop(k, None)
    e = _FAIL.setdefault(key, [0, 0.0, now])
    e[2] = now
    e[0] += 1
    if e[0] >= limit:  # too many wrong tries -> 10 min block
        e[0], e[1] = 0, now + 600


DUMMY_PW = generate_password_hash("not-a-real-password", method="pbkdf2:sha256")  # equal timing for unknown users


def need_admin():
    me = cur()
    if not me or not me["admin"]:
        abort(403)
    return me


def owns(me, owner):
    return me["admin"] or (owner or 0) == me["uid"]


# ----------------------------------------------------------------- low-memory PDF writer
def build_pdf(paths, out):
    """JPEGs are embedded as-is (not decoded); other formats are converted one at a time."""
    if Image is None:
        raise RuntimeError("Pillow missing (pip install pillow)")
    n = len(paths)
    offsets = {}
    with open(out, "wb") as f:
        f.write(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")

        def begin(num):
            offsets[num] = f.tell()
            f.write(f"{num} 0 obj\n".encode())

        begin(1)
        f.write(b"<< /Type /Catalog /Pages 2 0 R >>\nendobj\n")
        begin(2)
        kids = " ".join(f"{3 + 3 * i} 0 R" for i in range(n))
        f.write(f"<< /Type /Pages /Count {n} /Kids [{kids}] >>\nendobj\n".encode())
        for i, p in enumerate(paths):
            with Image.open(p) as im:
                w, h = im.size
                if im.format == "JPEG" and im.mode in ("RGB", "L"):
                    with open(p, "rb") as fh:
                        data = fh.read()
                    cs = "/DeviceRGB" if im.mode == "RGB" else "/DeviceGray"
                else:
                    buf = BytesIO()
                    im.convert("RGB").save(buf, "JPEG", quality=88)
                    data, cs = buf.getvalue(), "/DeviceRGB"
            try:
                os.remove(p)
            except OSError:
                pass
            sc = min(1.0, 14000.0 / max(w, h))
            pw, ph = w * sc, h * sc
            page, cont, img = 3 + 3 * i, 4 + 3 * i, 5 + 3 * i
            begin(page)
            f.write((f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {pw:.2f} {ph:.2f}] "
                     f"/Resources << /XObject << /Im0 {img} 0 R >> >> /Contents {cont} 0 R >>\nendobj\n").encode())
            c = f"q {pw:.2f} 0 0 {ph:.2f} 0 0 cm /Im0 Do Q".encode()
            begin(cont)
            f.write(f"<< /Length {len(c)} >>\nstream\n".encode() + c + b"\nendstream\nendobj\n")
            begin(img)
            f.write((f"<< /Type /XObject /Subtype /Image /Width {w} /Height {h} /ColorSpace {cs} "
                     f"/BitsPerComponent 8 /Filter /DCTDecode /Length {len(data)} >>\nstream\n").encode())
            f.write(data)
            f.write(b"\nendstream\nendobj\n")
        total = 2 + 3 * n
        xref = f.tell()
        f.write(f"xref\n0 {total + 1}\n".encode())
        f.write(b"0000000000 65535 f \n")
        for num in range(1, total + 1):
            f.write(f"{offsets[num]:010d} 00000 n \n".encode())
        f.write(f"trailer\n<< /Size {total + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n".encode())


# ----------------------------------------------------------------- chapters / queue
_CH = {}
CONV_LOCK = threading.Semaphore(int(os.environ.get("CONV_PAR", "3")))
# Free image service (wsrv.nl) fetches the picture itself and hands back a ready JPEG, so this server does no
# webp/png decoding at all. Set CONVERT_SERVICE= (empty) to turn it off. Any failure falls back to local convert.
CONVERT_SERVICE = os.environ.get("CONVERT_SERVICE", "https://wsrv.nl/,https://images.weserv.nl/").strip()
CONV_SERVICES = [u.strip() for u in CONVERT_SERVICE.split(",") if u.strip()]   # several mirrors = several requests spread out
_WS = {u: {"fail": 0, "off": 0.0} for u in CONV_SERVICES}
_WS_RR = itertools.count()


PDF_Q = int(os.environ.get("PDF_Q", "95"))   # JPEG quality when webp/png must be converted
PDF_WIDTH = int(os.environ.get("PDF_WIDTH", "0"))   # pictures wider than this are shrunk (0 = keep original size)


def prep_image(data, ctype):
    """Make one picture PDF-ready: shrink very wide pictures and turn webp/png into JPEG. Returns (bytes, ext).
    Small JPEGs are passed through untouched (no decoding, no RAM)."""
    ext = EXT.get(ctype, "jpg")
    if Image is None:
        return data, ext
    try:
        with Image.open(BytesIO(data)) as im:
            w, h = im.size
            big = PDF_WIDTH and w > PDF_WIDTH * 1.15
            if ctype == "image/jpeg" and im.mode in ("RGB", "L") and not big:
                return data, "jpg"
            with CONV_LOCK:  # one decoded picture in RAM at a time
                if big and im.format == "JPEG":
                    im.draft("RGB", (PDF_WIDTH, max(1, int(h * PDF_WIDTH / w))))  # JPEG decodes at 1/2, 1/4... size: fast, low RAM
                im = im.convert("RGB")
                if big:
                    im = im.resize((PDF_WIDTH, max(1, round(h * PDF_WIDTH / w))), Image.LANCZOS, reducing_gap=2.0)
                buf = BytesIO()
                im.save(buf, "JPEG", quality=PDF_Q)
                return buf.getvalue(), "jpg"
    except Exception:
        return data, ext  # keep the original, build_pdf can still handle it


def fetch_via_service(url):
    """Returns (jpeg_bytes, 'image/jpeg') from a free converter mirror, or None (caller then does it locally)."""
    if not CONV_SERVICES:
        return None
    if urlparse(url).path.lower().endswith((".jpg", ".jpeg")):  # already JPEG: no conversion needed, skip the extra hop
        return None
    now = time.time()
    live = [u for u in CONV_SERVICES if now >= _WS[u]["off"]]
    if not live:
        return None
    start = next(_WS_RR)
    for k in range(min(2, len(live))):          # try up to 2 different mirrors
        svc = live[(start + k) % len(live)]
        try:
            r = http.get(svc, params={"url": url, "output": "jpg", "q": str(PDF_Q), **({"w": PDF_WIDTH, "we": 1} if PDF_WIDTH else {})}, timeout=20)
            ok = r.status_code == 200 and r.headers.get("Content-Type", "").startswith("image/jpeg") and len(r.content) > 1500
        except requests.RequestException:
            ok = False
        if ok:
            _WS[svc]["fail"] = 0
            return r.content, "image/jpeg"
        _WS[svc]["fail"] += 1
        if _WS[svc]["fail"] >= 5:  # this mirror is blocked/down: skip it for 5 minutes
            _WS[svc]["fail"], _WS[svc]["off"] = 0, time.time() + 300
    return None


ERRLOG = deque(maxlen=40)


def cfetch(path, params=None, ttl=120, tries=2):
    """Cached site fetch (pages open instantly when seen recently; stale copy is used if the site is down)."""
    key = path + "|" + json.dumps(params or {}, sort_keys=True, default=str)
    c = _CH.get(key)
    if c and time.time() - c[0] < ttl:
        return c[1]
    try:
        soup = fetch_html(path, params, tries=tries, timeout=10)
    except UpstreamError:
        if c:
            return c[1]
        raise
    _CH[key] = (time.time(), soup)
    if len(_CH) > 30:
        _CH.pop(next(iter(_CH)))
    return soup


def manga_info(slug, fresh=False, ttl=180):
    """Everything about one manga (cover, rating, genres, related, sorted chapters)."""
    key = "info|" + slug
    c = _CH.get(key)
    if c and not fresh and time.time() - c[0] < ttl:
        return c[1]
    try:
        m = parse_manga(slug, fetch_html(f"/manga/{slug}/", tries=2, timeout=10))
    except UpstreamError:
        if c:
            return c[1]
        raise
    chs = []
    for ch in m["chapters"]:
        mm = re.search(r"\d+(?:\.\d+)?", ch["name"])
        num = float(mm.group()) if mm else None
        chs.append({**ch, "num": num, "spec": f"{num:g}" if num is not None else ""})
    chs.sort(key=lambda x: (x["num"] is None, x["num"] or 0))
    m["chs"] = chs
    m["cover"] = m.get("image_url")
    _CH[key] = (time.time(), m)
    if len(_CH) > 30:
        _CH.pop(next(iter(_CH)))
    return m


def chapters_for(slug, fresh=False):
    m = manga_info(slug, fresh=fresh)
    return m["title"], m.get("image_url"), m["chs"]


def select(spec, chs, done):
    spec = spec.strip().lower()
    if spec == "all":
        return chs
    if spec in ("", "new"):
        return [c for c in chs if c["chapter_id"] not in done]
    if spec.startswith("latest"):
        return chs[-max(1, int(re.sub(r"\D", "", spec) or 1)):]
    ranges = []
    for part in spec.split(","):
        part = part.strip()
        if "-" in part:
            a, b = part.split("-", 1)
            ranges.append((float(a), float(b)))
        elif part:
            ranges.append((float(part), float(part)))
    return [c for c in chs if c["num"] is not None and any(a <= c["num"] <= b for a, b in ranges)]


def chap_label(c):
    n = c["num"]
    if n is None:
        return safe(c["name"])
    return f"{int(n):03d}" + (f"{n % 1:.1f}"[1:] if n % 1 else "")



def job_pct(j):
    """Overall progress 0-100 (images 85%, upload 15%). 100 only when everything is stored."""
    if j["status"] in ("done", "done (errors)"):
        return 100
    tot = max(1, j["total"])
    cur = (j["cur_ok"] / j["cur_n"]) if j["cur_n"] else 0
    work = min(1.0, (j["done"] + cur) / tot)
    up = min(1.0, (j["uploaded"] + j["up_cur"] * j["up_n"]) / tot)
    return int(min(99, work * 85 + up * 15))


def make_job(me, slug, title, sel, per, note=""):
    job = {"id": next(_job_ids), "uid": me["uid"], "who": me["name"], "slug": slug, "title": title,
           "chapters": sel, "per": per, "status": "queued", "done": 0, "total": len(sel), "msg": "",
           "errors": [], "failed": [], "cancel": False, "par": IMG_PAR,
           "t": {"img": 0.0, "pdf": 0.0, "up": 0.0}, "note": note, "secs": 0.0,
           "cur_n": 0, "cur_ok": 0, "uploaded": 0, "up_cur": 0.0, "up_n": 0, "up_msg": ""}
    JOBS.append(job)
    fin = [j for j in JOBS if j["status"] not in ("queued", "running")]
    for j in fin[:-30]:
        JOBS.remove(j)
    JOBQ.put(job)
    ensure_workers()
    threading.Thread(target=save_jobs, daemon=True).start()  # don't make the click wait for storage
    return job


def enqueue(me, slug, spec, per):
    per = min(max(int(per or 1), 1), 30)
    title, cover, chs = chapters_for(slug, fresh=(spec.strip().lower() == "auto"))
    rec = load_state(me["uid"]).get(slug, {})
    done = {cid for cid, v in rec.get("chapters", {}).items() if v.get("file_id")}
    pending = {c["chapter_id"] for j in JOBS if j["uid"] == me["uid"] and j["status"] in ("queued", "running")
               for c in j["chapters"]}
    if spec.strip().lower() == "auto":  # only chapters newer than the newest one already downloaded
        nums = [v.get("num") for v in rec.get("chapters", {}).values() if v.get("file_id") and v.get("num") is not None]
        top = max(nums) if nums else None
        base = [c for c in chs if top is not None and c["num"] is not None and c["num"] > top and c["chapter_id"] not in done]
    else:
        base = select(spec, chs, done)
    sel = [c for c in base if c["chapter_id"] not in pending]
    note = ""
    if USER_MAX_CH and not me["admin"] and len(sel) > USER_MAX_CH:
        sel, note = sel[:USER_MAX_CH], f"Limit: only the first {USER_MAX_CH} chapters were queued"
    if not sel:
        return None
    return make_job(me, slug, title, sel, per, note)


def save_jobs():
    """Remember queued/running jobs in storage so they continue after a restart."""
    try:
        with JOBS_LOCK:
            act = [{"uid": j["uid"], "who": j["who"], "slug": j["slug"], "title": j["title"],
                    "chapters": j["chapters"], "per": j["per"]}
                   for j in JOBS if j["status"] in ("queued", "running") and not j["cancel"]]
            sql("insert or replace into kv(k, v) values('jobs', ?)", [json.dumps(act, ensure_ascii=False)])
    except Exception:
        app.logger.warning("could not save jobs", exc_info=True)


def resume_jobs():
    rows, _ = q("select v from kv where k='jobs'")
    if not rows:
        return
    for s in json.loads(rows[0]["v"] or "[]"):
        me = {"uid": s["uid"], "name": s["who"], "admin": s["uid"] == 0}
        rec = load_state(s["uid"]).get(s["slug"], {})
        done = {cid for cid, v in rec.get("chapters", {}).items() if v.get("file_id")}
        sel = [c for c in s["chapters"] if c["chapter_id"] not in done]
        if sel:
            make_job(me, s["slug"], s["title"], sel, s["per"], "Resumed after a restart")
    save_jobs()


def auto_loop():
    """Every AUTO_MIN minutes: queue newer chapters for users who switched Auto-update on."""
    while True:
        time.sleep(AUTO_MIN * 60)
        try:
            rows, _ = q("select k from kv where k like 'auto\\_%' escape '\\'")
            for r in rows:
                uid = int(r["k"][5:])
                if uid == 0:
                    name = ADMIN_NAME
                else:
                    u, _ = q("select name from users where id=?", [uid])
                    if not u:
                        continue
                    name = u[0]["name"]
                me = {"uid": uid, "name": name, "admin": uid == 0}
                for slug, rec in load_state(uid).items():
                    mine = [j for j in JOBS if j["uid"] == uid and j["status"] in ("queued", "running")]
                    if not me["admin"] and len(mine) >= USER_MAX_JOBS:
                        break
                    try:
                        enqueue(me, slug, "auto", rec.get("per", 1))
                    except Exception:
                        app.logger.warning("auto update failed for %s", slug, exc_info=True)
                    time.sleep(2)
        except Exception:
            app.logger.warning("auto loop error", exc_info=True)


RETENTION_DAYS = int(os.environ.get("KEEP_DAYS", "60"))


def expire_old():
    """Delete PDFs older than RETENTION_DAYS (for everyone) and half-uploaded leftovers. Returns how many were removed."""
    rows, _ = q("select id, coalesce(uid,0) as uid from files where parts>0 and created < datetime('now', ?)",
                [f"-{RETENTION_DAYS} days"])
    rows += q("select id, coalesce(uid,0) as uid from files where parts=0 and created < datetime('now', '-3 hours')")[0]
    for r in rows:
        try:
            delete_file(r["id"], r["uid"])
        except Exception:
            app.logger.warning("expire failed for %s", r["id"], exc_info=True)
    return len(rows)


def clean_spool():
    """Remove work folders nobody continued for SPOOL_KEEP_MIN minutes (the storage drops half-uploaded files after 3 h)."""
    now = time.time()
    for d in os.listdir(SPOOL):
        full = os.path.join(SPOOL, d)
        try:
            newest = max([os.path.getmtime(full)] + [os.path.getmtime(os.path.join(full, x)) for x in os.listdir(full)])
            if now - newest > SPOOL_KEEP:
                shutil.rmtree(full, ignore_errors=True)
        except OSError:
            pass


def housekeep_loop():
    time.sleep(90)
    rounds = 0
    while True:
        try:
            clean_spool()
            if rounds % 12 == 0:
                n = expire_old()
                if n:
                    app.logger.info("housekeeping removed %d old files", n)
        except Exception:
            app.logger.warning("housekeeping error", exc_info=True)
        rounds += 1
        time.sleep(1800)


def ensure_workers():
    _workers[:] = [t for t in _workers if t.is_alive()]
    while len(_workers) < NUM_WORKERS:
        t = threading.Thread(target=worker, daemon=True)
        t.start()
        _workers.append(t)


def worker():
    while True:
        job = JOBQ.get()
        if job["cancel"]:  # cancelled while waiting in the queue
            job["status"], job["msg"] = "cancelled", ""
            continue
        job["status"] = "running"
        t0 = time.time()
        try:
            if not job["cancel"]:
                run_job(job)
        except Exception as e:
            app.logger.exception("job failed")
            job["errors"].append(str(e)[:200])
        job["status"] = "cancelled" if job["cancel"] else ("done" if not job["errors"] else "done (errors)")
        job["msg"] = job["up_msg"] = ""
        for er in job["errors"][-5:]:
            ERRLOG.append({"ts": int(time.time()), "who": job["who"], "title": job["title"], "err": er})
        job["secs"] = time.time() - t0
        save_jobs()


def _meta_path(tmp):
    return os.path.join(tmp, "meta.json")


def _meta_read(tmp):
    try:
        with open(_meta_path(tmp), encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return None


def _meta_write(tmp, **kw):
    m = _meta_read(tmp) or {}
    m.update(kw)
    part = _meta_path(tmp) + ".part"
    with open(part, "w", encoding="utf-8") as fh:
        json.dump(m, fh, ensure_ascii=False)
    os.replace(part, _meta_path(tmp))


def group_dir(job, group):
    """Same chapters = same folder, so a restarted/retried job finds the images and the PDF it already made."""
    key = hashlib.sha1((f'{job["uid"]}|{job["slug"]}|' + ",".join(c["chapter_id"] for c in group)).encode()).hexdigest()[:20]
    d = os.path.join(SPOOL, key)
    os.makedirs(d, exist_ok=True)
    return d


def finish_group(job, tmp, pdf, name, okc):
    """Upload the PDF and update the library state. Runs in the background while the next group downloads.
    If the upload fails the PDF stays in its folder: a retry or a restart only uploads it again (resuming)."""
    t0 = time.time()
    job["up_n"], job["up_cur"] = len(okc), 0.0
    keep = False
    ids = dict((_meta_read(tmp) or {}).get("ids") or {})

    def on_ids(fid, tid):
        try:
            _meta_write(tmp, ids={"fid": fid, "tid": tid})
        except OSError:
            pass

    try:
        if job["cancel"]:
            raise Cancelled()
        job["up_msg"] = f"Uploading {name} 0%"

        def prog(f):
            job["up_cur"] = f
            job["up_msg"] = f"Uploading {name} {int(f * 100)}%"

        fid = store_pdf(pdf, name, job["slug"], job["uid"], cb=prog, stop=lambda: job["cancel"], ids=ids, on_ids=on_ids)
        with LOCK:
            st = load_state(job["uid"])
            rec = st.setdefault(job["slug"], {"chapters": {}})
            rec.update({"title": job["title"], "per": job["per"]})
            for c in okc:
                rec["chapters"].setdefault(c["chapter_id"], {}).update(
                    {"name": c["name"], "num": c["num"], "file_id": fid})
            save_state(job["uid"], st)
    except Cancelled:
        pass
    except Exception as e:
        job["errors"].append(f"upload {name}: {str(e)[:300]}")
        job["failed"] += okc
        keep = True
    finally:
        job["uploaded"] += len(okc)
        job["up_cur"], job["up_n"], job["up_msg"] = 0.0, 0, ""
        job["t"]["up"] += time.time() - t0
        if not keep:
            shutil.rmtree(tmp, ignore_errors=True)


def run_job(job):
    chs, per = job["chapters"], job["per"]
    up = ThreadPoolExecutor(1)
    pend = []
    try:
        for g in range(0, len(chs), per):
            if job["cancel"]:
                break
            group = chs[g:g + per]
            tmp = group_dir(job, group)
            handed = False
            files = []
            try:
                pdf = os.path.join(tmp, "out.pdf")
                meta = _meta_read(tmp)
                if meta and meta.get("name") and meta.get("okc") and os.path.isfile(pdf):
                    # an earlier run already built this PDF (crash / failed upload): only upload it, nothing is downloaded again
                    name, okc = meta["name"], meta["okc"]
                    have = {c["chapter_id"] for c in okc}
                    job["failed"] += [c for c in group if c["chapter_id"] not in have]
                    job["done"] += len(group)
                    job["msg"] = f"Continuing upload: {name}"
                else:
                    okc = []
                    for ci, c in enumerate(group):
                        try:
                            files += fetch_chapter_images(job, tmp, ci, c)
                            okc.append(c)
                        except Exception as e:  # skip this chapter, keep going
                            if not job["cancel"]:
                                job["errors"].append(f'{c["name"]}: {str(e)[:120]}')
                                job["failed"].append(c)
                        if job["cancel"]:
                            break
                        job["done"] += 1
                        job["cur_n"] = job["cur_ok"] = 0
                    if job["cancel"]:
                        break
                    if not files:
                        shutil.rmtree(tmp, ignore_errors=True)
                        handed = True  # nothing to keep
                        continue
                    first, last = chap_label(okc[0]), chap_label(okc[-1])
                    name = f'{safe(job["title"])} - Chapter {first}.pdf' if len(okc) == 1 else \
                           f'{safe(job["title"])} - Ch {first}-{last}.pdf'
                    job["msg"] = f"Building PDF: {name}"
                    t0 = time.time()
                    part = pdf + ".part"
                    build_pdf(files, part)
                    os.replace(part, pdf)
                    _meta_write(tmp, name=name, okc=okc, slug=job["slug"], uid=job["uid"])
                    job["t"]["pdf"] += time.time() - t0
                    for p in files:  # images are inside the PDF now, free the disk
                        try:
                            os.remove(p)
                        except OSError:
                            pass
                if job["cancel"]:
                    break
                pend.append(up.submit(finish_group, job, tmp, pdf, name, okc))
                handed = True
                while len(pend) > 1:  # at most one upload waiting, so disk/memory stay small
                    pend.pop(0).result()
            except Exception as e:
                job["errors"].append(f"PDF group {g // per + 1}: {str(e)[:150]}")
                job["failed"] += group
            finally:
                if not handed and job["cancel"]:
                    shutil.rmtree(tmp, ignore_errors=True)  # on an error the folder stays: a retry reuses the images
        for f in pend:
            f.result()
    finally:
        up.shutdown(wait=True)
        if job["cancel"]:  # a cancelled job leaves nothing behind
            for g in range(0, len(chs), per):
                shutil.rmtree(os.path.join(SPOOL, hashlib.sha1((f'{job["uid"]}|{job["slug"]}|' + ",".join(c["chapter_id"] for c in chs[g:g + per])).encode()).hexdigest()[:20]), ignore_errors=True)


def fetch_chapter_images(job, tmp, ci, c):
    mk = os.path.join(tmp, f"c{ci:03d}.json")
    try:  # this chapter was fully downloaded before a restart: use the files that are still on disk
        with open(mk, encoding="utf-8") as fh:
            names = json.load(fh)
        old = [os.path.join(tmp, x) for x in names]
        if old and all(os.path.isfile(x) for x in old):
            job["cur_n"] = job["cur_ok"] = len(old)
            job["msg"] = f'{c["name"]}  (already downloaded)'
            return old
    except Exception:
        pass
    panels = parse_panels(c["chapter_id"], fetch_html(f"/{c['chapter_id']}/"))["panels"]
    if not panels:
        raise RuntimeError("no images found")
    n = len(panels)
    job["cur_n"], job["cur_ok"] = n, 0
    cnt = {"ok": 0, "fail": 0}
    t0 = time.time()

    def one(idx, url):
        if job["cancel"]:
            raise RuntimeError("cancelled")
        res = None
        for k in range(3):
            res = (fetch_via_service(url) if k == 0 else None) or fetch_image(url)
            if res:
                break
            cnt["fail"] += 1
            time.sleep(0.5 * (k + 1))
        if not res:
            raise RuntimeError(f"image {idx} failed")
        data, ext = prep_image(*res)
        path = os.path.join(tmp, f"{ci:03d}_{idx:04d}.{ext}")
        with open(path, "wb") as fh:
            fh.write(data)
        cnt["ok"] += 1
        job["cur_ok"] = cnt["ok"]
        job["msg"] = f'{c["name"]}  image {cnt["ok"]}/{n}'
        return path

    with ThreadPoolExecutor(max_workers=job["par"]) as ex:
        futs = [ex.submit(one, i, p["image_url"]) for i, p in enumerate(panels, 1)]
        try:
            paths = [f.result() for f in futs]
        except Exception:
            for f in futs:
                f.cancel()
            raise
    if cnt["fail"] >= 3:  # site is pushing back, slow down for the rest of this job
        job["par"] = max(6, job["par"] - 2)
    job["t"]["img"] += time.time() - t0
    try:
        with open(mk + ".part", "w", encoding="utf-8") as fh:
            json.dump([os.path.basename(x) for x in paths], fh)
        os.replace(mk + ".part", mk)
    except OSError:
        pass
    return paths


# ============================================================================ UI  (HentaiJaat)
T = app.jinja_env.from_string  # templates are compiled once at start-up (faster pages)

CSS = r"""
:root{--bg:#0d0e12;--sf:#16181f;--sf2:#1f222b;--bd:#272b36;--fg:#eceef4;--mut:#8b90a0;--ac:#7c6cff;--ok:#35c28a;--er:#ff5d6c;--wa:#f5b942;--r:14px}
:root[data-theme=light]{--bg:#f3f4f8;--sf:#fff;--sf2:#eceef3;--bd:#dde0e8;--fg:#14161c;--mut:#667085}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
[hidden]{display:none!important}
html{color-scheme:dark;scroll-behavior:smooth}:root[data-theme=light]{color-scheme:light}
body{margin:0;background:var(--bg);color:var(--fg);font:15px/1.4 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;padding-bottom:calc(76px + env(safe-area-inset-bottom))}
a{color:inherit;text-decoration:none}b{font-weight:650}small,.mut{color:var(--mut)}small{font-size:12.5px}
h2{font-size:20px;margin:6px 0 12px}h3{font-size:16px;margin:18px 0 8px}
.wrap{max-width:860px;margin:0 auto;padding:10px 12px}
#nb{position:fixed;top:0;left:0;height:3px;width:0;background:var(--ac);z-index:99;opacity:0}
#toast{position:fixed;left:50%;bottom:calc(88px + env(safe-area-inset-bottom));transform:translate(-50%,20px);background:var(--fg);color:var(--bg);padding:10px 16px;border-radius:24px;font-weight:600;font-size:14px;opacity:0;pointer-events:none;transition:.2s;z-index:98;max-width:90%;text-align:center}
#toast.on{opacity:1;transform:translate(-50%,0)}
.top{position:sticky;top:0;z-index:20;display:flex;align-items:center;gap:10px;padding:calc(10px + env(safe-area-inset-top)) 14px 10px;background:color-mix(in srgb,var(--bg) 88%,transparent);backdrop-filter:blur(10px);border-bottom:1px solid var(--bd)}
.lg{font-weight:800;font-size:18px;letter-spacing:.2px;display:flex;align-items:center;gap:8px}.lg em{font-style:normal;color:var(--ac);font-weight:700;font-size:13px;border:1px solid var(--ac);border-radius:6px;padding:1px 6px}
.mk{width:22px;height:22px;border-radius:6px;background:url(data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA1MTIgNTEyIj48ZGVmcz48bGluZWFyR3JhZGllbnQgaWQ9ImJnIiB4MT0iMCIgeTE9IjAiIHgyPSIxIiB5Mj0iMSI+PHN0b3Agb2Zmc2V0PSIwIiBzdG9wLWNvbG9yPSIjYjA3YmZmIi8+PHN0b3Agb2Zmc2V0PSIxIiBzdG9wLWNvbG9yPSIjNGExZmM3Ii8+PC9saW5lYXJHcmFkaWVudD48cmFkaWFsR3JhZGllbnQgaWQ9Imdsb3ciIGN4PSIuNSIgY3k9Ii41IiByPSIuNSI+PHN0b3Agb2Zmc2V0PSIwIiBzdG9wLWNvbG9yPSIjZmZmIiBzdG9wLW9wYWNpdHk9Ii4zNSIvPjxzdG9wIG9mZnNldD0iMSIgc3RvcC1jb2xvcj0iI2ZmZiIgc3RvcC1vcGFjaXR5PSIwIi8+PC9yYWRpYWxHcmFkaWVudD48cmFkaWFsR3JhZGllbnQgaWQ9ImlyaXMiIGN4PSIuNSIgY3k9Ii40MiIgcj0iLjYiPjxzdG9wIG9mZnNldD0iMCIgc3RvcC1jb2xvcj0iI2ZmOGJlMCIvPjxzdG9wIG9mZnNldD0iLjQ1IiBzdG9wLWNvbG9yPSIjOWE0NWZmIi8+PHN0b3Agb2Zmc2V0PSIxIiBzdG9wLWNvbG9yPSIjMmEwYzc4Ii8+PC9yYWRpYWxHcmFkaWVudD48Y2xpcFBhdGggaWQ9ImV5ZSI+PHBhdGggZD0iTTYyIDI3NiBRMjU2IDEwOCA0NTAgMjc2IFEyNTYgNDA4IDYyIDI3NloiLz48L2NsaXBQYXRoPjwvZGVmcz48cmVjdCB3aWR0aD0iNTEyIiBoZWlnaHQ9IjUxMiIgcng9IjExMiIgZmlsbD0idXJsKCNiZykiLz48Y2lyY2xlIGN4PSIyNTYiIGN5PSIyNzAiIHI9IjIzMCIgZmlsbD0idXJsKCNnbG93KSIvPjxwYXRoIGQ9Ik02MiAyNzYgUTI1NiAxMDggNDUwIDI3NiBRMjU2IDQwOCA2MiAyNzZaIiBmaWxsPSIjZmZmIi8+PGcgY2xpcC1wYXRoPSJ1cmwoI2V5ZSkiPjxjaXJjbGUgY3g9IjI1NiIgY3k9IjI2OCIgcj0iMTAyIiBmaWxsPSJ1cmwoI2lyaXMpIi8+PGNpcmNsZSBjeD0iMjU2IiBjeT0iMjY4IiByPSIxMDIiIGZpbGw9Im5vbmUiIHN0cm9rZT0iIzFkMDc1NyIgc3Ryb2tlLXdpZHRoPSI4Ii8+PGVsbGlwc2UgY3g9IjI1NiIgY3k9IjI3MiIgcng9IjQwIiByeT0iNTIiIGZpbGw9IiMxMzA2M2EiLz48cGF0aCBkPSJNNjIgMjc2IFEyNTYgMTA4IDQ1MCAyNzYgTDQ1MCAxMDAgTDYyIDEwMFoiIGZpbGw9IiMwMDAiIG9wYWNpdHk9Ii4xOCIvPjwvZz48Y2lyY2xlIGN4PSIyMTgiIGN5PSIyMzYiIHI9IjI2IiBmaWxsPSIjZmZmIi8+PGNpcmNsZSBjeD0iMjk2IiBjeT0iMzA0IiByPSIxMiIgZmlsbD0iI2ZmZiIvPjxjaXJjbGUgY3g9IjMwMCIgY3k9IjI0NCIgcj0iNiIgZmlsbD0iI2ZmZiIgb3BhY2l0eT0iLjg1Ii8+PHBhdGggZD0iTTU0IDI4NCBRMjU2IDkyIDQ1OCAyODQiIGZpbGw9Im5vbmUiIHN0cm9rZT0iIzFhMDg0NiIgc3Ryb2tlLXdpZHRoPSIyNCIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIi8+PHBhdGggZD0iTTQ1MiAyNzYgTDQ4NiAyNDgiIGZpbGw9Im5vbmUiIHN0cm9rZT0iIzFhMDg0NiIgc3Ryb2tlLXdpZHRoPSIxNiIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIi8+PHBhdGggZD0iTTY2IDI4NCBMMzQgMjYyIiBmaWxsPSJub25lIiBzdHJva2U9IiMxYTA4NDYiIHN0cm9rZS13aWR0aD0iMTIiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIvPjxwYXRoIGQ9Ik05MiAzMDAgUTI1NiA0MDggNDIwIDMwMCIgZmlsbD0ibm9uZSIgc3Ryb2tlPSIjMWEwODQ2IiBzdHJva2Utd2lkdGg9IjYiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgb3BhY2l0eT0iLjciLz48cGF0aCBkPSJNNDAwIDk2IFE0MDQgMTI2IDQzNCAxMzAgUTQwNCAxMzQgNDAwIDE2NCBRMzk2IDEzNCAzNjYgMTMwIFEzOTYgMTI2IDQwMCA5NloiIGZpbGw9IiNmZmYiLz48cGF0aCBkPSJNMTE4IDEyMCBRMTIxIDEzOCAxMzkgMTQxIFExMjEgMTQ0IDExOCAxNjIgUTExNSAxNDQgOTcgMTQxIFExMTUgMTM4IDExOCAxMjBaIiBmaWxsPSIjZmZmIiBvcGFjaXR5PSIuOSIvPjxwYXRoIGQ9Ik0xNTAgNDA0IFExNTIgNDE2IDE2NCA0MTggUTE1MiA0MjAgMTUwIDQzMiBRMTQ4IDQyMCAxMzYgNDE4IFExNDggNDE2IDE1MCA0MDRaIiBmaWxsPSIjZmZmIiBvcGFjaXR5PSIuNyIvPjwvc3ZnPg==) center/cover no-repeat;display:inline-block}
.sp{flex:1}.top a{font-size:14px;color:var(--mut)}
.gh{background:none;border:1px solid var(--bd);color:var(--fg);border-radius:10px;padding:6px 10px;font-size:16px}
.adm{border-bottom:2px solid var(--ac)}
input,select,textarea{width:100%;background:var(--sf);color:var(--fg);border:1px solid var(--bd);border-radius:12px;padding:11px 13px;font:inherit;outline:none;margin:0}
input:focus,select:focus{border-color:var(--ac)}input[type=checkbox]{width:auto}
button,.btn{background:var(--ac);color:#fff;border:0;border-radius:12px;padding:10px 16px;font:inherit;font-weight:650;cursor:pointer;display:inline-flex;align-items:center;justify-content:center;gap:6px;transition:transform .08s,opacity .15s}
button:active,.btn:active,.c:active,.chip:active,.row:active{transform:scale(.97)}
button.sec,.btn.sec{background:var(--sf2);color:var(--fg);border:1px solid var(--bd)}
button.dn,.btn.dn{background:transparent;color:var(--er);border:1px solid var(--er)}
button.sm{padding:6px 11px;font-size:13px;border-radius:9px}
button:disabled,button.busy{opacity:.55;pointer-events:none}
.fl{background:var(--sf2);border:1px solid var(--bd);border-radius:12px;padding:10px 12px;margin-bottom:10px}
.card{background:var(--sf);border:1px solid var(--bd);border-radius:var(--r);padding:12px;margin:10px 0}
.sr{display:flex;gap:8px;margin:2px 0 10px}.sr button{padding:0 16px}
.chips{display:flex;gap:8px;overflow-x:auto;padding:2px 0 10px;scrollbar-width:none}.chips::-webkit-scrollbar{display:none}
.chip{white-space:nowrap;padding:7px 14px;border-radius:20px;background:var(--sf);border:1px solid var(--bd);font-size:14px;cursor:pointer;color:var(--fg)}
.chip.on{background:var(--ac);border-color:var(--ac);color:#fff;font-weight:650}
details.filt{margin:0 0 10px}details.filt>summary{cursor:pointer;color:var(--mut);padding:4px 0;list-style:none}details.filt>summary::before{content:"⚙ "}
.fg{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin:8px 0}.gn{display:flex;flex-wrap:wrap;gap:6px 14px;margin:6px 0}.gn label{font-size:14px;display:flex;gap:5px;align-items:center}
.g{display:grid;grid-template-columns:repeat(auto-fill,minmax(108px,1fr));gap:10px}
.c{display:block;transition:transform .08s}
.cv{position:relative;aspect-ratio:2/3;border-radius:12px;overflow:hidden;background:linear-gradient(110deg,var(--sf) 30%,var(--sf2) 50%,var(--sf) 70%);background-size:200% 100%;animation:sh 1.4s infinite}
@keyframes sh{to{background-position:-200% 0}}
.cv img{width:100%;height:100%;object-fit:cover;display:block}
.bd{position:absolute;font-style:normal;font-size:11px;font-weight:700;padding:2px 6px;border-radius:6px;background:rgba(0,0,0,.72);color:#fff}
.bd.s{left:5px;top:5px}.bd.k{right:5px;top:5px;background:#e0518f}.bd.n{left:5px;bottom:5px;background:var(--ok)}.bd.r{right:5px;bottom:5px;background:var(--ac)}
.c .t{display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;font-size:13px;font-weight:600;margin-top:6px;line-height:1.25}
.c small{display:block;font-size:12px;margin-top:2px}
.empty{color:var(--mut);text-align:center;padding:30px 0;grid-column:1/-1}
.pg{display:flex;justify-content:space-between;align-items:center;margin:18px 0}
.strip{display:flex;flex-wrap:nowrap;gap:10px;overflow-x:auto;padding:2px 0 12px;scrollbar-width:none;-webkit-overflow-scrolling:touch;scroll-snap-type:x proximity}.strip::-webkit-scrollbar{display:none}.strip .c{flex:0 0 96px;scroll-snap-align:start}
.row{display:flex;align-items:center;gap:10px;padding:10px 4px;border-bottom:1px solid var(--bd)}.row>.gr{flex:1;min-width:0}
.row .t1{font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.hs{display:flex;gap:12px;align-items:center;padding:10px 0;border-bottom:1px solid var(--bd)}.hs img{width:48px;aspect-ratio:2/3;object-fit:cover;border-radius:8px;background:var(--sf)}.hs .gr{flex:1;min-width:0}.hs b{display:block;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.hero{display:flex;gap:14px;margin:4px 0 12px}.hero .cv{flex:0 0 118px;animation:none}.hero .inf{flex:1;min-width:0}
.hero h2{margin:0 0 6px;font-size:19px;line-height:1.25}
.meta{display:flex;flex-wrap:wrap;gap:6px;margin:6px 0}.pill{font-size:12px;padding:3px 9px;border-radius:20px;background:var(--sf2);border:1px solid var(--bd);color:var(--mut)}.pill.ac{color:var(--ac);border-color:var(--ac)}.pill.ok{color:var(--ok);border-color:var(--ok)}.pill.er{color:var(--er);border-color:var(--er)}.pill.wa{color:var(--wa);border-color:var(--wa)}
.desc{color:var(--mut);font-size:14px;display:-webkit-box;-webkit-line-clamp:4;-webkit-box-orient:vertical;overflow:hidden}.desc.open{-webkit-line-clamp:unset;display:block}
.acts{display:flex;gap:8px;flex-wrap:wrap;margin:10px 0}.acts>*{flex:1 1 40%}
.ch{display:flex;align-items:center;gap:10px;padding:9px 2px;border-bottom:1px solid var(--bd)}.ch .gr{flex:1;min-width:0}.ch .nm{font-weight:600}
.ck{width:26px;height:26px;border-radius:50%;border:2px solid var(--bd);background:none;padding:0;color:#fff;font-size:14px;flex:none}.ck.on{background:var(--ok);border-color:var(--ok)}
.ch.isr .nm{color:var(--mut)}
.pb{height:8px;background:var(--sf2);border-radius:8px;overflow:hidden;margin:8px 0 4px}.pb i{display:block;height:100%;width:0;background:linear-gradient(90deg,var(--ac),#b39dff);border-radius:8px;transition:width .4s}
.pb.ok i{background:var(--ok)}.pb.er i{background:var(--er)}
.job .h{display:flex;justify-content:space-between;gap:8px;align-items:flex-start}.job .h b{overflow-wrap:anywhere}.job .pc{font-weight:800;font-size:20px;color:var(--ac)}
.st{font-size:12px;font-weight:700;text-transform:uppercase;letter-spacing:.4px}.st.running{color:var(--ac)}.st.queued{color:var(--wa)}.st.done{color:var(--ok)}.st.cancelled,.st.err{color:var(--er)}
.er{color:var(--er)}
.grp{margin:12px 0}.grp>.gh{display:flex;justify-content:space-between;align-items:center;gap:8px;padding:4px 2px}.grp .gh b{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.f{padding:10px 2px;border-bottom:1px solid var(--bd)}.f .l1{display:flex;gap:8px;align-items:center}.f .l1 .gr{flex:1;min-width:0}.f .nm{font-size:14px;font-weight:600;overflow-wrap:anywhere}
.bar{display:flex;gap:8px;margin:8px 0}.bar>input{flex:1}.bar>select{width:auto}
.tabs{position:fixed;left:0;right:0;bottom:0;z-index:30;display:flex;background:color-mix(in srgb,var(--sf) 94%,transparent);backdrop-filter:blur(12px);border-top:1px solid var(--bd);padding:6px 6px calc(6px + env(safe-area-inset-bottom))}
.tabs a{flex:1;display:flex;flex-direction:column;align-items:center;gap:2px;font-size:11px;font-weight:600;color:var(--mut);padding:6px 0;border-radius:12px;position:relative}
.tabs a.on{color:var(--ac)}.tabs svg{width:23px;height:23px;fill:none;stroke:currentColor;stroke-width:2;stroke-linecap:round;stroke-linejoin:round}
.bg{position:absolute;top:0;left:calc(50% + 6px);min-width:17px;height:17px;border-radius:9px;background:var(--er);color:#fff;font-size:11px;font-style:normal;display:flex;align-items:center;justify-content:center;padding:0 4px}
.stat{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px}.stat .card{margin:0}.stat b{font-size:22px;display:block}
table{width:100%;border-collapse:collapse;font-size:14px}td,th{padding:9px 6px;border-bottom:1px solid var(--bd);text-align:left}th{color:var(--mut);font-weight:600;font-size:12px;text-transform:uppercase}
.login{max-width:360px;margin:12vh auto 0;text-align:center}.login .card{text-align:left;padding:18px}.login input{margin:6px 0}.login button{width:100%;margin-top:8px}
.ld{opacity:.6}
.auth{max-width:390px;margin:8vh auto 0;padding:0 4px}
.brand{text-align:center;margin-bottom:20px}.brand .mk{display:block;margin:0 auto;width:64px;height:64px;border-radius:18px;box-shadow:0 8px 24px rgba(124,77,255,.35)}
.brand h1{font-size:27px;margin:12px 0 4px;letter-spacing:.2px}.brand p{margin:0;color:var(--mut);font-size:14px}
.auth .card{padding:20px}.auth label{display:block;font-size:13px;font-weight:600;color:var(--mut);margin:14px 0 5px}.auth label:first-child{margin-top:0}
.auth button[type=submit]{width:100%;margin-top:18px;padding:12px}
.auth .alt{text-align:right;margin-top:12px;font-size:13px}.auth a.ln,.sub a{color:var(--ac);font-weight:600}
.sub{text-align:center;color:var(--mut);font-size:14px;margin:14px 0 0}
.auth .chk{display:flex;gap:9px;align-items:flex-start;margin-top:16px;font-size:13px;font-weight:400;color:var(--mut)}.auth .chk input{margin-top:2px;flex:none}
.auth .er{margin:12px 0 0;font-size:14px}
.errc{text-align:center;padding:26px 18px}.errc h3{margin:0 0 6px;font-size:19px}.errc p{margin:0 0 6px}
@media(min-width:760px){.g{grid-template-columns:repeat(auto-fill,minmax(140px,1fr))}.hero .cv{flex-basis:170px}}
"""

JS = r"""
const $=(s,r=document)=>r.querySelector(s),$$=(s,r=document)=>[...r.querySelectorAll(s)];
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function toast(m,t){const e=$('#toast');e.textContent=m;e.className='on';clearTimeout(toast.t);toast.t=setTimeout(()=>e.className='',t||2200)}
async function api(u,d){
  const o={method:d===undefined?'GET':'POST',headers:{'X-Req':'1'}};
  if(d!==undefined){o.headers['Content-Type']='application/json';o.body=JSON.stringify(d)}
  const r=await fetch(u,o);if(r.status==401){const lp=location.pathname;if(lp.indexOf('login')<0&&lp.indexOf('signup')<0)location='/login';throw 0}
  let j={};try{j=await r.json()}catch(e){}
  if(!r.ok&&!j.msg)j.msg='Error '+r.status;return j}
function busy(b,v){if(b)b.classList[v?'add':'remove']('busy')}
const nb=$('#nb');
function nbStart(){nb.style.transition='none';nb.style.width='0';nb.style.opacity=1;requestAnimationFrame(()=>requestAnimationFrame(()=>{nb.style.transition='width 6s cubic-bezier(.1,.7,.2,1)';nb.style.width='88%'}))}
addEventListener('pageshow',()=>{nb.style.opacity=0;nb.style.width='0';$$('.ld').forEach(e=>e.classList.remove('ld'))});
document.addEventListener('click',e=>{const a=e.target.closest('a[href]');
  if(a&&!a.target&&!a.hasAttribute('download')&&!a.dataset.noload&&a.origin===location.origin&&!e.ctrlKey&&!e.metaKey&&a.getAttribute('href')[0]!='#'){nbStart();a.classList.add('ld')}});
document.addEventListener('submit',()=>nbStart());
const pf=new Set();
document.addEventListener('touchstart',e=>{const a=e.target.closest('a[href^="/m/"]');
  if(a&&!pf.has(a.href)){pf.add(a.href);fetch(a.href,{credentials:'same-origin',priority:'low'}).catch(()=>{})}},{passive:true});
const th=$('#thm');if(th)th.onclick=()=>{const d=document.documentElement,t=d.dataset.theme=='dark'?'light':'dark';d.dataset.theme=t;try{localStorage.setItem('t',t)}catch(e){}};
function setBadge(n){const b=$('#qb');if(b){b.textContent=n||'';b.hidden=!n}}
async function pollBadge(){if(document.hidden||window.NOBADGE)return;try{const j=await api('/api/jobs?brief=1');setBadge(j.active)}catch(e){}}
setInterval(pollBadge,6000);pollBadge();
function perPref(){let v=0;try{v=parseInt(localStorage.getItem('per'))||0}catch(e){}return v>=1&&v<=30?v:0}
function dlAdd(slug,spec,per,btn){busy(btn,1);
  return api('/api/dl',{slug:slug,spec:spec,per:per}).then(j=>{toast(j.msg||'Done');if(j.ok)pollBadge();return j}).catch(()=>toast('Network problem')).finally(()=>busy(btn,0))}
if('serviceWorker' in navigator)navigator.serviceWorker.register('/sw.js').catch(()=>{});
"""

ICONS = {
    "home": '<svg viewBox="0 0 24 24"><path d="M3 11l9-8 9 8v10a1 1 0 0 1-1 1h-5v-7H9v7H4a1 1 0 0 1-1-1z"/></svg>',
    "saved": '<svg viewBox="0 0 24 24"><path d="M6 3h12v18l-6-4-6 4z"/></svg>',
    "lib": '<svg viewBox="0 0 24 24"><path d="M12 3v12m0 0l-4-4m4 4l4-4M4 17v3h16v-3"/></svg>',
    "queue": '<svg viewBox="0 0 24 24"><path d="M4 6h16M4 12h16M4 18h10"/></svg>',
    "me": '<svg viewBox="0 0 24 24"><circle cx="12" cy="8" r="4"/><path d="M4 21c0-4 4-7 8-7s8 3 8 7"/></svg>',
}

TOP = T("""<!doctype html><html lang=en><meta charset=utf-8>
<style>*{-webkit-touch-callout:none}body{-webkit-user-select:none;user-select:none}input,textarea,select{-webkit-user-select:text;user-select:text}img{-webkit-user-drag:none;user-drag:none}</style><script>addEventListener("contextmenu",function(e){var t=e.target&&e.target.tagName;if(t!="INPUT"&&t!="TEXTAREA")e.preventDefault()});addEventListener("dragstart",function(e){e.preventDefault()})</script>
<meta name=viewport content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name=theme-color content="#0d0e12"><meta name=color-scheme content="dark light">
<link rel=manifest href=/manifest.json><link rel=icon href=/icon-192.png><link rel=apple-touch-icon href=/icon-192.png>
<meta name=apple-mobile-web-app-capable content=yes><meta name=mobile-web-app-capable content=yes>
<title>{{title}} · {{BRAND}}</title>
<script>try{document.documentElement.dataset.theme=localStorage.getItem('t')||'dark'}catch(e){}</script>
<style>{{css|safe}}</style><div id=nb></div><div id=toast></div>
{% if mode=='admin' %}<header class="top adm"><b class=lg>{{BRAND}} <em>Admin</em></b><span class=sp></span><a href=/>Open app</a>{% if me %}<form method=post action=/admin/logout style="margin:0"><button class=gh style="font-size:14px">Log out</button></form>{% endif %}</header>
{% elif mode=='app' %}<header class=top><a class=lg href=/><i class=mk></i>{{BRAND}}</a><span class=sp></span><button class=gh id=thm aria-label=theme>◐</button></header>{% endif %}
<script>window.NOBADGE={{ 'false' if mode=='app' else 'true' }};</script>
<script>{{js|safe}}</script>
<main class=wrap>{% if flash %}<div class=fl>{{flash}}</div>{% endif %}""")

BOT = T("""</main>{% if mode=='app' %}<nav class=tabs>
<a href=/ class="{{'on' if active=='home'}}">{{ic.home|safe}}<span>Home</span></a>
<a href=/saved class="{{'on' if active=='saved'}}">{{ic.saved|safe}}<span>Saved</span></a>
<a href=/library class="{{'on' if active=='lib'}}">{{ic.lib|safe}}<span>Library</span></a>
<a href=/queue class="{{'on' if active=='queue'}}">{{ic.queue|safe}}<span>Queue</span><i id=qb class=bg hidden></i></a>
<a href=/me class="{{'on' if active=='me'}}">{{ic.me|safe}}<span>Me</span></a></nav>{% endif %}""")

MACROS = """{% macro card(m, badge='') %}<a class=c href="/m/{{m.slug}}" data-slug="{{m.slug}}"><div class=cv>{% if m.image_url or m.cover %}<img loading=lazy decoding=async src="/hentai/proxy/{{m.image_url or m.cover}}" alt="">{% endif %}
{% if m.score %}<b class="bd s">★ {{m.score}}</b>{% endif %}{% if m.colored %}<b class="bd k">COLOR</b>{% endif %}<i class="bd n" hidden></i><i class="bd r" hidden></i></div>
<span class=t>{{m.title}}</span>{% if m.latest_chapter %}<small>{{m.latest_chapter}}</small>{% endif %}</a>{% endmacro %}
"""


def page(body, active="", title="Home", mode="app", **ctx):
    me = cur()
    flash = session.pop("flash", None)
    inner = body.render(me=me, **ctx)
    return (TOP.render(css=CSS, js=JS, me=me, flash=flash, title=title, mode=mode)
            + inner + BOT.render(me=me, active=active, mode=mode, ic=ICONS))


def jerr(msg, code=400):
    return jsonify({"ok": False, "msg": msg}), code


# ---------------------------------------------------------------- PWA (home-screen app)
def _bez(p0, p1, p2, n=40):
    return [((1 - t) ** 2 * p0[0] + 2 * (1 - t) * t * p1[0] + t * t * p2[0],
             (1 - t) ** 2 * p0[1] + 2 * (1 - t) * t * p1[1] + t * t * p2[1]) for t in (i / n for i in range(n + 1))]


def make_icon(size):
    """App icon: purple tile with an anime eye (drawn with Pillow, no image file needed)."""
    from PIL import ImageDraw
    k = 4
    S = size * k
    u = S / 512.0
    im = Image.new("RGB", (S, S), (13, 14, 18))
    tile = Image.new("RGB", (S, S))
    td = ImageDraw.Draw(tile)
    for y in range(S):
        t = y / S
        td.line([(0, y), (S, y)], fill=(int(176 - 102 * t), int(123 - 92 * t), int(255 - 56 * t)))
    mask = Image.new("L", (S, S), 0)
    ImageDraw.Draw(mask).rounded_rectangle([0, 0, S - 1, S - 1], radius=112 * u, fill=255)
    im.paste(tile, (0, 0), mask)
    d = ImageDraw.Draw(im)
    P = lambda pts: [(x * u, y * u) for x, y in pts]
    eye = _bez((62, 276), (256, 108), (450, 276)) + _bez((450, 276), (256, 408), (62, 276))
    d.polygon(P(eye), fill=(255, 255, 255))
    layer = Image.new("RGB", (S, S), (255, 255, 255))
    ld = ImageDraw.Draw(layer)
    cx, cy = 256 * u, 268 * u
    for n in range(102, 0, -2):
        f = n / 102.0
        c0, c1, c2 = (255, 139, 224), (154, 69, 255), (42, 12, 120)
        if f < .45:
            a, b_, t = c0, c1, f / .45
        else:
            a, b_, t = c1, c2, (f - .45) / .55
        r, g, b = (int(a[i] + (b_[i] - a[i]) * t) for i in range(3))
        ld.ellipse([cx - n * u, cy - n * u, cx + n * u, cy + n * u], fill=(r, g, b))
    ld.ellipse([cx - 102 * u, cy - 102 * u, cx + 102 * u, cy + 102 * u], outline=(29, 7, 87), width=int(8 * u))
    ld.ellipse([cx - 40 * u, 220 * u, cx + 40 * u, 324 * u], fill=(19, 6, 58))
    emask = Image.new("L", (S, S), 0)
    ImageDraw.Draw(emask).polygon(P(eye), fill=255)
    im.paste(layer, (0, 0), emask)
    d = ImageDraw.Draw(im)
    W = (255, 255, 255)
    for (x, y, r) in ((218, 236, 26), (296, 304, 12), (300, 244, 6)):
        d.ellipse([(x - r) * u, (y - r) * u, (x + r) * u, (y + r) * u], fill=W)
    dark, w = (26, 8, 70), int(24 * u)
    lid = P(_bez((54, 284), (256, 92), (458, 284)))
    d.line(lid, fill=dark, width=w)
    for (x, y) in ((54, 284), (458, 284)):
        d.ellipse([x * u - w / 2, y * u - w / 2, x * u + w / 2, y * u + w / 2], fill=dark)
    d.line(P([(452, 276), (486, 248)]), fill=dark, width=int(16 * u))
    d.line(P([(66, 284), (34, 262)]), fill=dark, width=int(12 * u))
    for (x, y, r) in ((400, 130, 34), (118, 141, 22), (150, 418, 14)):
        d.polygon(P([(x, y - r), (x + r * .28, y - r * .28), (x + r, y), (x + r * .28, y + r * .28),
                     (x, y + r), (x - r * .28, y + r * .28), (x - r, y), (x - r * .28, y - r * .28)]), fill=W)
    im = im.resize((size, size), Image.LANCZOS)
    buf = BytesIO()
    im.save(buf, "PNG")
    return buf.getvalue()


_ICONS = {}


@app.get("/icon-<int:size>.png")
def icon(size):
    if Image is None or size not in (192, 512):
        abort(404)
    if size not in _ICONS:
        _ICONS[size] = make_icon(size)
    return Response(_ICONS[size], mimetype="image/png", headers={"Cache-Control": "public, max-age=604800"})


@app.get("/manifest.json")
def manifest():
    return jsonify({"name": BRAND, "short_name": BRAND, "start_url": "/", "display": "standalone",
                    "background_color": "#0d0e12", "theme_color": "#0d0e12",
                    "icons": [{"src": "/icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any maskable"},
                              {"src": "/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"}]})


@app.get("/sw.js")
def sw():
    return Response("self.addEventListener('install',e=>self.skipWaiting());self.addEventListener('activate',e=>self.clients.claim());"
                    "self.addEventListener('fetch',()=>{});", mimetype="application/javascript",
                    headers={"Cache-Control": "no-cache"})


# ---------------------------------------------------------------- error pages
ERRT = T("""<div class="card errc"><h3>{{head}}</h3><p class=mut>{{msg}}</p>{% if ref %}<small>Reference: {{ref}}</small>{% endif %}
<div class=acts><a class=btn href="{{url}}">Try again</a><a class="btn sec" href=/>Go home</a><a class="btn sec" href="{{TG}}" target=_blank rel="noopener noreferrer" data-noload>Contact support</a></div></div>""")

_HTTP_MSG = {400: ("Bad request", "That request could not be understood."),
             403: ("Access denied", "You do not have access to this page."),
             404: ("Page not found", "The page you are looking for does not exist."),
             405: ("Not allowed", "That action is not allowed here."),
             413: ("Too large", "That upload is too large."),
             429: ("Slow down", "Too many requests. Please wait a moment.")}


def _ref():
    return hashlib.sha1(os.urandom(8)).hexdigest()[:8]


@app.errorhandler(UpstreamError)
def ui_upstream(e):
    if request.path.startswith("/hentai"):
        if e.status == 404:
            return reply(status=404, message="not found on source site")
        return reply(status=502, message="source site unavailable")
    if request.path.startswith("/api/"):
        return jerr("Could not reach the source site. Please try again shortly.", 502)
    if e.status == 404:
        head, msg = "Page not found", "That page could not be found on the source site."
    else:
        head, msg = "Source site unavailable", "The source site is slow or down right now. Please try again in a moment."
    return page(ERRT, title="Error", head=head, msg=msg, ref="", url=request.full_path.rstrip("?")), (404 if e.status == 404 else 502)


@app.errorhandler(Exception)
def ui_any(e):
    from werkzeug.exceptions import HTTPException
    if isinstance(e, HTTPException):
        code = e.code or 500
        head, msg = _HTTP_MSG.get(code, ("Something went wrong", "Please try again."))
        if request.path.startswith("/api/"):
            return jerr(msg, code)
        if request.path.startswith("/hentai"):
            return reply(status=code, message=msg)
        return page(ERRT, title=head, head=head, msg=msg, ref="", url=request.full_path.rstrip("?")), code
    ref = _ref()
    app.logger.exception("unhandled error [%s] %s %s", ref, request.method, request.path)
    if isinstance(e, RuntimeError) and "SQL storage" in str(e):
        head, msg = "Storage unavailable", "Storage is temporarily unavailable. Please try again in a moment."
    else:
        head, msg = "Something went wrong", "An unexpected error occurred on our side. Please try again."
    if request.path.startswith("/api/"):
        return jerr(f"{msg} (ref {ref})", 500)
    if request.path.startswith("/hentai"):
        return reply(status=500, message=f"server error (ref {ref})")
    return page(ERRT, title="Error", head=head, msg=msg, ref=ref, url=request.full_path.rstrip("?")), 500


# ---------------------------------------------------------------- login / logout
LOGIN = T("""<div class=auth><div class=brand><i class=mk></i><h1>{{BRAND}}</h1><p>Sign in to your account</p></div>
<form method=post class=card>
<label for=u>Username</label><input id=u name=u value="{{u}}" autocomplete=username autocapitalize=none autocorrect=off spellcheck=false required {% if not u %}autofocus{% endif %}>
<label for=p>Password</label><input id=p type=password name=p autocomplete=current-password required {% if u %}autofocus{% endif %}>
{% if err %}<p class=er role=alert>{{err}}</p>{% endif %}
<button type=submit>Sign in</button>
<div class=alt><a class=ln href="{{TG}}" target=_blank rel="noopener noreferrer" data-noload>Forgot password?</a></div></form>
{% if signup %}<p class=sub>New here? <a href=/signup>Create an account</a></p>{% endif %}
<p class=sub>Need help? <a href="{{TG}}" target=_blank rel="noopener noreferrer" data-noload>Contact support on Telegram</a></p></div>""")

SIGNUP = T("""<div class=auth><div class=brand><i class=mk></i><h1>{{BRAND}}</h1><p>Create your free account</p></div>
<form method=post class=card>
<label for=u>Username</label><input id=u name=u value="{{u}}" autocomplete=username autocapitalize=none autocorrect=off spellcheck=false required maxlength=20 placeholder="3-20 characters: a-z 0-9 _ . -">
<label for=p>Password</label><input id=p type=password name=p autocomplete=new-password required minlength=6 maxlength=128 placeholder="At least 6 characters">
<label for=p2>Confirm password</label><input id=p2 type=password name=p2 autocomplete=new-password required minlength=6 maxlength=128>
<label class=chk><input type=checkbox name=age value=1 required><span>I confirm that I am 18 years of age or older.</span></label>
{% if err %}<p class=er role=alert>{{err}}</p>{% endif %}
<button type=submit>Create account</button></form>
<p class=sub>Already have an account? <a href=/login>Sign in</a></p>
<p class=sub>Need help? <a href="{{TG}}" target=_blank rel="noopener noreferrer" data-noload>Contact support on Telegram</a></p></div>""")

ADMLOGIN = T("""<div class=auth><div class=brand><i class=mk></i><h1>{{BRAND}} <span class=pill style="color:var(--ac);border-color:var(--ac);vertical-align:middle">Admin</span></h1><p>Administrator sign in</p></div>
<form method=post class=card>
<label for=p>Admin password</label><input id=p type=password name=p autocomplete=current-password required autofocus>
{% if err %}<p class=er role=alert>{{err}}</p>{% endif %}
<button type=submit>Enter</button></form>
<p class=sub><a href=/login>Back to user sign in</a></p></div>""")


@app.route("/login", methods=["GET", "POST"])
def login():
    err, name = "", ""
    if request.method == "GET" and session.get("uid") is not None and session_ok(cur()):
        return redirect("/")
    if request.method == "POST":
        name, pw = request.form.get("u", "").strip().lower(), request.form.get("p", "")
        ip = client_ip()
        key, ikey = f"u:{ip}:{name[:40]}", f"i:{ip}"
        left = max(lock_left(key), lock_left(ikey))
        if left:
            err = f"Too many failed attempts. Please try again in {left // 60 + 1} minute(s)."
        elif not name or not pw:
            err = "Enter your username and password."
        else:
            try:
                init_schema()
                if _SV["t"] == 0.0:
                    (rows, _), _x = par(lambda: q("select id, pw from users where name=?", [name]), refresh_sv)
                else:
                    rows, _ = q("select id, pw from users where name=?", [name])
                if rows:
                    ok = check_password_hash(rows[0]["pw"], pw)
                else:
                    check_password_hash(DUMMY_PW, pw)
                    ok = False
                if ok:
                    _FAIL.pop(key, None)
                    start_session(rows[0]["id"], name)
                    return redirect("/")
            except RuntimeError:
                return page(LOGIN, mode="bare", title="Sign in", u=name, signup=SIGNUP_OPEN,
                            err="Could not reach storage. Please try again in a moment.")
            note_fail(key)
            note_fail(ikey, 20)
            err = "Incorrect username or password."
    return page(LOGIN, mode="bare", title="Sign in", err=err, u=name, signup=SIGNUP_OPEN)


_SIGNUPS = {}


@app.route("/signup", methods=["GET", "POST"])
def signup():
    if not SIGNUP_OPEN:
        return redirect("/login")
    err, name = "", ""
    if request.method == "GET" and session.get("uid") is not None and session_ok(cur()):
        return redirect("/")
    if request.method == "POST":
        name = request.form.get("u", "").strip().lower()
        pw, pw2 = request.form.get("p", ""), request.form.get("p2", "")
        ip, now = client_ip(), time.time()
        if len(_SIGNUPS) > 2000:
            _SIGNUPS.clear()
        recent = [t for t in _SIGNUPS.get(ip, []) if now - t < 3600]
        if len(recent) >= 5:
            err = "Too many accounts were created from this network. Please try again later."
        elif not re.fullmatch(r"[a-z0-9_.-]{3,20}", name) or name == ADMIN_NAME.lower():
            err = "Username must be 3-20 characters: letters, numbers, _ . -"
        elif len(pw) < MINPW or len(pw) > 128:
            err = f"Password must be {MINPW}-128 characters."
        elif pw != pw2:
            err = "The two passwords do not match."
        elif not request.form.get("age"):
            err = "You must confirm that you are 18 or older."
        else:
            try:
                init_schema()
                taken, total, pwh = par(
                    lambda: q("select id from users where name=?", [name])[0],
                    lambda: q("select count(*) as n from users")[0][0]["n"],
                    lambda: generate_password_hash(pw, method="pbkdf2:sha256"))
                if taken:
                    err = "That username is already taken."
                elif total >= MAX_USERS:
                    err = "Registrations are currently closed. Please contact support."
                else:
                    sql("insert into users(name, pw, created) values(?,?,?)", [name, pwh, int(time.time())])
                    rows, _ = q("select id from users where name=?", [name])
                    uid = rows[0]["id"]
                    _SV["ids"].add(uid)
                    _SIGNUPS[ip] = recent + [now]
                    start_session(uid, name)
                    return redirect("/")
            except RuntimeError:
                err = "Could not reach storage. Please try again in a moment."
    return page(SIGNUP, mode="bare", title="Create account", err=err, u=name)


@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    err = ""
    if request.method == "POST":
        key = "a:" + client_ip()
        left = lock_left(key)
        if not APP_PASSWORD:
            err = "Admin sign in is not configured (APP_PASSWORD is not set)."
        elif left:
            err = f"Too many failed attempts. Please try again in {left // 60 + 1} minute(s)."
        elif hmac.compare_digest(request.form.get("p", "").encode(), APP_PASSWORD.encode()):
            _FAIL.pop(key, None)
            try:
                refresh_sv() if _SV["t"] == 0.0 else None
            except Exception:
                pass
            start_session(0, ADMIN_NAME)
            return redirect("/admin")
        else:
            note_fail(key)
            err = "Incorrect password."
    return page(ADMLOGIN, mode="bare", title="Admin sign in", err=err)


@app.post("/logout")
def logout():
    session.clear()
    return redirect("/login")


@app.post("/admin/logout")
def admin_logout():
    session.clear()
    return redirect("/admin/login")


# ---------------------------------------------------------------- home
ORDERS = [("update", "Latest"), ("latest", "New"), ("popular", "Popular"), ("pw", "Top week"), ("pm", "Top month"),
          ("pa", "Top all"), ("title", "A-Z"), ("", "All")]
POP = {"pw": "weekly", "pm": "monthly", "pa": "alltime"}
_DEF_FILT = {"status": [("ongoing", "Ongoing"), ("completed", "Completed"), ("hiatus", "Hiatus")],
             "type": [("manga", "Manga"), ("manhwa", "Manhwa"), ("manhua", "Manhua"), ("comic", "Comic")], "genre": []}
_FILT = {"t": 0, "d": None, "busy": False}


def parse_popular(soup, key):
    """Weekly / monthly / all-time lists from the site's home-page widget."""
    box = soup.select_one(f".wpop-{key}")
    out = []
    for li in (box.select("li") if box else []):
        a = li.select_one(".leftseries h2 a, h2 a, a")
        parts = [p for p in (a.get("href", "") if a else "").split("/") if p]
        if not parts:
            continue
        out.append({"title": text_of(a) or a.get("title", ""), "image_url": img_src(li.select_one("img")),
                    "slug": parts[-1], "latest_chapter": "", "score": "", "colored": False})
    return out


def load_filters():
    """Read status / type / genre options from the site's filter form."""
    d = {"status": list(_DEF_FILT["status"]), "type": list(_DEF_FILT["type"]), "genre": []}
    soup = cfetch("/manga/", ttl=3600)
    for key in ("status", "type"):
        sel = soup.select_one(f'select[name="{key}"]')
        opts = [(o.get("value", ""), text_of(o)) for o in sel.select("option") if o.get("value")] if sel else []
        if opts:
            d[key] = opts
    for inp in soup.select('input[name="genre[]"]'):
        lab = soup.select_one(f'label[for="{inp.get("id")}"]') if inp.get("id") else None
        name = text_of(lab) or text_of(inp.parent)
        if inp.get("value") and name:
            d["genre"].append((inp["value"], name))
    return d


def get_filters(block=False):
    """Never makes a page wait: returns cached / default options and refreshes in the background."""
    if _FILT["d"] and time.time() - _FILT["t"] < 3600:
        return _FILT["d"]

    def work():
        try:
            _FILT["d"], _FILT["t"] = load_filters(), time.time()
        except Exception:
            app.logger.warning("could not read filter form", exc_info=True)
            _FILT["t"] = time.time() - 3300
        finally:
            _FILT["busy"] = False

    if block:
        _FILT["busy"] = True
        work()
    elif not _FILT["busy"]:
        _FILT["busy"] = True
        threading.Thread(target=work, daemon=True).start()
    return _FILT["d"] or _DEF_FILT


@app.get("/api/filters")
def api_filters():
    d = get_filters(block=True)
    return jsonify({"ok": True, "genre": d["genre"]})


HOME = T(MACROS + """<form class=sr action=/><input name=q value="{{q}}" placeholder="Search manga…" enterkeyhint=search><button aria-label=Search>Go</button></form>
{% if show_cont %}<div id=cont hidden></div>{% endif %}
<div class=chips>{% for v,l in orders %}<a class="chip {{'on' if (v==order and not q and not gs)}}" href="/?order={{v}}">{{l}}</a>{% endfor %}</div>
<details class=filt><summary>Filters{% if nf %} · {{nf}} on{% endif %}</summary><form>
<input type=hidden name=order value="{{order}}"><div class=fg>
<select name=status><option value="">Any status</option>{% for v,l in f.status %}<option value="{{v}}" {{'selected' if v==status}}>{{l}}</option>{% endfor %}</select>
<select name=type><option value="">Any type</option>{% for v,l in f.type %}<option value="{{v}}" {{'selected' if v==mtype}}>{{l}}</option>{% endfor %}</select></div>
<div class=gn id=gn>{% for v,l in f.genre %}<label><input type=checkbox name=genre value="{{v}}" {{'checked' if v in genres}}>{{l}}</label>{% endfor %}</div>
<button style="width:100%">Apply filters</button></form></details>
{% if gs %}<p class=mut>Genre: <b>{{gs|replace('-',' ')}}</b> · <a href=/ style="color:var(--ac)">clear</a></p>{% endif %}
{% if note %}<div class=fl>{{note}}</div>{% endif %}
<div class=g>{% for m in mangas %}{{ card(m) }}{% else %}<p class=empty>No results found</p>{% endfor %}</div>
<div class=pg><span>{% if pg>1 %}<a class="btn sec" href="{{link(pg-1)}}">‹ Prev</a>{% endif %}</span><small>Page {{pg}}</small><span>{% if has_next %}<a class="btn sec" href="{{link(pg+1)}}">Next ›</a>{% endif %}</span></div>
<script>
window.NOBADGE=false;
{% if show_cont %}api('/api/continue').then(j=>{const s=$('#cont');if(!j.items||!j.items.length)return;
s.innerHTML='<h3 style="margin-top:4px">Continue reading</h3><div class=strip>'+j.items.map(i=>'<a class=c href="/m/'+i.slug+'"><div class=cv>'+(i.cover?'<img src="/hentai/proxy/'+esc(i.cover)+'">':'')+'<b class="bd r">'+esc(i.cname)+'</b></div><span class=t>'+esc(i.title)+'</span></a>').join('')+'</div>';s.hidden=false}).catch(()=>{});{% endif %}
const fd=$('details.filt');if(fd&&!$('#gn').children.length)fd.addEventListener('toggle',()=>{if(fd.open&&!$('#gn').children.length)api('/api/filters').then(j=>{$('#gn').innerHTML=(j.genre||[]).map(g=>'<label><input type=checkbox name=genre value="'+esc(g[0])+'">'+esc(g[1])+'</label>').join('')})},{once:true});
</script>""")


@app.get("/")
def root():
    return ui_home()


def ui_home():
    q_ = request.args.get("q", "").strip()
    pg = request.args.get("page", "1")
    pg = int(pg) if pg.isdigit() and int(pg) > 0 else 1
    order = request.args.get("order", "update")
    status, mtype = request.args.get("status", ""), request.args.get("type", "")
    genres = [g for g in request.args.getlist("genre") if g]
    gs = request.args.get("gs", "").strip().strip("/")
    mangas, note, soup = None, "", None
    if q_:
        soup = cfetch("/" if pg == 1 else f"/page/{pg}/", {"s": q_}, ttl=120)
    elif gs:
        soup = cfetch(f"/genres/{quote(gs)}/" + ("" if pg == 1 else f"page/{pg}/"), ttl=180)
    elif order in POP:
        pg = 1
        mangas = parse_popular(cfetch("/", ttl=300), POP[order])
        if not mangas:  # widget not found on the home page: fall back to the normal popular list
            note = "The weekly/monthly list is unavailable right now, showing Popular instead."
            soup = cfetch("/manga/", {"page": 1, "order": "popular"}, ttl=180)
    else:
        params = {"page": pg}
        if order:
            params["order"] = order
        if status:
            params["status"] = status
        if mtype:
            params["type"] = mtype
        if genres:
            params["genre[]"] = genres
        soup = cfetch("/manga/", params, ttl=120)
    has_next = bool(soup and soup.select_one("a.next.page-numbers, .hpage a.r"))
    if mangas is None:
        mangas = parse_listing(soup)

    def link(p):
        a = {"q": q_, "order": order, "status": status, "type": mtype, "gs": gs, "page": p}
        return "/?" + urlencode([(k, v) for k, v in a.items() if v != ""] + [("genre", g) for g in genres])

    nf = sum(1 for x in (status, mtype) if x) + len(genres)
    return page(HOME, "home", "Home", q=q_, pg=pg, mangas=mangas, order=order, orders=ORDERS, status=status,
                mtype=mtype, genres=genres, f=get_filters(), has_next=has_next, link=link, gs=gs, nf=nf, note=note,
                show_cont=(pg == 1 and not q_ and not gs))


# ---------------------------------------------------------------- manga page
MANGA = T(MACROS + """<div id=mp data-slug="{{slug}}"></div>
<div class=hero><div class=cv>{% if m.cover %}<img src="/hentai/proxy/{{m.cover}}" alt="">{% endif %}{% if m.colored %}<b class="bd k">COLOR</b>{% endif %}</div>
<div class=inf><h2>{{m.title}}</h2>
<div class=meta>{% if m.score %}<span class="pill wa">★ {{m.score}}</span>{% endif %}{% if m.type %}<span class="pill ac">{{m.type}}</span>{% endif %}
{% if m.status %}<span class="pill {{'ok' if 'ongoing' in m.status|lower else ''}}">{{m.status}}</span>{% endif %}<span class=pill>{{chs|length}} ch</span></div>
{% if m.author %}<small>Author: {{m.author}}</small><br>{% endif %}
{% if m.created_at %}<small>Added: {{m.created_at}}</small><br>{% endif %}{% if m.updated_at %}<small>Updated: {{m.updated_at}}</small>{% endif %}</div></div>
{% if m.genres %}<div class=chips>{% for g in m.genres %}<a class=chip href="/?gs={{g.slug}}">{{g.name}}</a>{% endfor %}</div>{% endif %}
{% if m.description %}<p class=desc id=ds onclick="this.classList.toggle('open')">{{m.description}}</p>{% endif %}
<div class=acts>
{% if last %}<a class=btn href="/r/{{last.cid}}?m={{slug}}">▶ Continue · {{last.cname}}</a>{% endif %}
{% if first %}<a class="btn {{'sec' if last}}" href="/r/{{first.chapter_id}}?m={{slug}}">Read first</a>{% endif %}
{% if latest %}<a class="btn sec" href="/r/{{latest.chapter_id}}?m={{slug}}">Read latest</a>{% endif %}
<button class="{{'sec' if saved}}" id=sv onclick="toggleSave(this)">{{'★ Saved' if saved else '☆ Save'}}</button></div>
<div id=stw {{'hidden' if not saved}} class=bar><select id=st onchange="setSt(this.value)">
{% for v,l in [('reading','Reading'),('completed','Completed'),('plan','Plan to read')] %}<option value="{{v}}" {{'selected' if v==status_}}>{{l}}</option>{% endfor %}</select></div>
<details class=card><summary><b>⬇ Download as PDF</b></summary>
<div class=bar style="flex-wrap:wrap"><input id=sp value="new" placeholder="new · all · 1-50 · latest 10"><select id=per><option value=1>1 chapter = 1 PDF</option><option value=3>3 chapters = 1 PDF</option><option value=5>5 chapters = 1 PDF</option><option value=10>10 chapters = 1 PDF</option><option value=20>20 chapters = 1 PDF</option><option value=30>30 chapters = 1 PDF</option></select></div>
<small>Examples: new · all · 1-50 · 1,5,10-20 · latest 10</small><div style="margin-top:8px"><button onclick="dlAdd(slug,$('#sp').value,$('#per').value,this)">Add to queue</button></div></details>
<script>addEventListener('DOMContentLoaded',function(){const s=$('#per');if(!s)return;const v=perPref();if(v&&[...s.options].some(o=>+o.value===v))s.value=v;s.addEventListener('change',()=>{try{localStorage.setItem('per',s.value)}catch(e){}})})</script>
<div class=bar><button class="sec sm" onclick="markAll(1)">Mark all read</button><button class="sec sm" onclick="markAll(0)">Mark all unread</button><span class=sp></span><small>{{rd|length}} / {{chs|length}} read</small></div>
<div id=chl>{% for c in chs|reverse %}<div class="ch {{'isr' if c.chapter_id in rd}}" data-cid="{{c.chapter_id}}" data-spec="{{c.spec}}">
<button class="ck {{'on' if c.chapter_id in rd}}" onclick="rk(this)">{{'✓' if c.chapter_id in rd}}</button>
<a class=gr href="/r/{{c.chapter_id}}?m={{slug}}"><div class=nm>{{c.name}}{% if c.chapter_id in done and done[c.chapter_id].file_id %} <span class="pill ok">PDF</span>{% endif %}</div><small>{{c.date}}</small></a>
{% if c.spec %}<button class="sec sm" onclick="dlAdd(slug,'{{c.spec}}',1,this)" aria-label=download>⬇</button>{% endif %}</div>{% endfor %}</div>
{% if m.related %}<h3>Related</h3><div class=strip>{% for r in m.related %}{{ card(r) }}{% endfor %}</div>{% endif %}
<script>
const slug=$('#mp').dataset.slug;
async function toggleSave(b){busy(b,1);try{const j=await api('/api/save/'+slug,{});if(!j.ok)return toast(j.msg);
b.textContent=j.saved?'★ Saved':'☆ Save';b.classList.toggle('sec',j.saved);$('#stw').hidden=!j.saved;if(j.saved)$('#st').value=j.status||'reading';toast(j.saved?'Added to your Saved list':'Removed from Saved')}catch(e){toast('Network problem')}busy(b,0)}
function setSt(v){api('/api/status/'+slug,{status:v}).then(j=>toast(j.ok?'Status: '+v:j.msg))}
async function rk(b){const row=b.closest('.ch'),on=!b.classList.contains('on');b.classList.toggle('on',on);b.textContent=on?'✓':'';row.classList.toggle('isr',on);
try{const j=await api('/api/read',{slug:slug,cid:row.dataset.cid,v:on?1:0});if(!j.ok)throw 0}catch(e){b.classList.toggle('on',!on);b.textContent=!on?'✓':'';row.classList.toggle('isr',!on);toast('Could not update. Please try again.')}}
async function markAll(v){const j=await api('/api/readall',{slug:slug,v:v});if(!j.ok)return toast(j.msg);
$$('.ch').forEach(r=>{const b=$('.ck',r);b.classList.toggle('on',!!v);b.textContent=v?'✓':'';r.classList.toggle('isr',!!v)});toast(v?'All chapters marked as read':'All chapters marked as unread')}
</script>""")


@app.get("/m/<slug>")
def ui_manga(slug):
    uid = cur()["uid"]
    m = manga_info(slug)
    chs = m["chs"]
    done, rd, last, saved, status_ = {}, set(), None, False, "reading"
    try:
        st, r1, r2, r3 = par(lambda: load_state(uid),
                             lambda: q("select cid from reads where uid=? and slug=?", [uid, slug])[0],
                             lambda: q("select cid, cname from hist where uid=? and slug=?", [uid, slug])[0],
                             lambda: q("select status from bookmarks where uid=? and slug=?", [uid, slug])[0])
        saved = bool(r3)
        status_ = (r3[0]["status"] if r3 else None) or "reading"
        done = st.get(slug, {}).get("chapters", {})
        rd = {r["cid"] for r in r1}
        last = r2[0] if r2 else None
    except Exception:
        app.logger.warning("manga page: storage unavailable", exc_info=True)
    return page(MANGA, "home", m["title"], m=m, slug=slug, chs=chs, done=done, rd=rd, last=last, saved=saved,
                status_=status_, first=chs[0] if chs else None, latest=chs[-1] if chs else None)


# ---------------------------------------------------------------- reader
READER = T("""<!doctype html><html lang=en><meta charset=utf-8>
<style>*{-webkit-touch-callout:none}body{-webkit-user-select:none;user-select:none}input,textarea,select{-webkit-user-select:text;user-select:text}img{-webkit-user-drag:none;user-drag:none}</style><script>addEventListener("contextmenu",function(e){var t=e.target&&e.target.tagName;if(t!="INPUT"&&t!="TEXTAREA")e.preventDefault()});addEventListener("dragstart",function(e){e.preventDefault()})</script>
<meta name=viewport content="width=device-width,initial-scale=1,viewport-fit=cover"><meta name=theme-color content="#000">
<title>{{d.cname}} · {{BRAND}}</title>
<style>*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}body{margin:0;background:#000;color:#fff;font:15px system-ui,sans-serif}
a{color:#fff;text-decoration:none}#hb,#fb{position:fixed;left:0;right:0;z-index:5;display:flex;align-items:center;gap:10px;padding:8px 12px;background:rgba(12,12,16,.93);transition:transform .22s}
#hb{top:0;padding-top:calc(8px + env(safe-area-inset-top))}#fb{bottom:0;justify-content:space-between;padding-bottom:calc(8px + env(safe-area-inset-bottom))}
body.hide #hb{transform:translateY(-105%)}body.hide #fb{transform:translateY(105%)}
#bk{font-size:26px;line-height:1;padding:0 8px}#tt{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:14px}
#fb a{padding:9px 18px;border-radius:12px;background:#22252e;font-weight:650}#fb a.off{opacity:.3;pointer-events:none}#pgi{color:#9aa0b0;font-size:13px}
.pn{display:block;width:100%;min-height:260px;background:#0c0c0c}.dv{padding:30px 14px;text-align:center;font-weight:700;color:#aab;border-top:1px solid #222;background:#111}
#rd{padding-top:0}#end{text-align:center;color:#8b90a0;padding:46px 14px calc(90px + env(safe-area-inset-bottom))}#end a{color:#8f82ff}
#ov{position:fixed;inset:0;background:#000;z-index:9;display:flex;align-items:center;justify-content:center;color:#9aa0b0}#ov[hidden]{display:none}</style>
<div id=hb><a id=bk href="/m/{{d.slug}}">‹</a><span id=tt>{{d.mtitle}} · {{d.cname}}</span></div>
<div id=ov hidden>Resuming where you left off… <small style="margin-left:8px;opacity:.6">tap to skip</small></div><div id=rd></div><div id=end>Loading next chapter…</div>
<div id=fb><a id=pv href=#>‹ Prev</a><span id=pgi></span><a id=nx href=#>Next ›</a></div>
<script type=application/json id=init>{{d|tojson}}</script>
<script>
const $=s=>document.querySelector(s);
const D=JSON.parse($('#init').textContent),R=$('#rd'),secs=[];
let nextCid=D.next,loading=false,lastY=scrollY,curIdx=-1,tm;
const px=u=>'/hentai/proxy/'+u.replace(/ /g,'%20').replace(/#/g,'%23');
async function api(u,d){const o={method:d===undefined?'GET':'POST',headers:{'X-Req':'1'}};if(d!==undefined){o.headers['Content-Type']='application/json';o.body=JSON.stringify(d)}
const r=await fetch(u,o);if(r.status==401){const lp=location.pathname;if(lp.indexOf('login')<0&&lp.indexOf('signup')<0)location='/login';throw 0}try{return await r.json()}catch(e){return{ok:false}}}
function ld(im,t){t=t||0;if(im._p&&!t)return im._p;
im._p=new Promise(res=>{im.onload=()=>{im.style.minHeight='0';res()};im.onerror=()=>{if(t<2)setTimeout(()=>ld(im,t+1).then(res),1500*(t+1));else res()};im.src=px(im.dataset.src)});return im._p}
const io=new IntersectionObserver(es=>es.forEach(e=>{if(e.isIntersecting){io.unobserve(e.target);ld(e.target)}}),{rootMargin:'1600px 0px'});
function addSection(c,first){const s=document.createElement('section');
if(!first){const h=document.createElement('div');h.className='dv';h.textContent=c.cname;s.appendChild(h)}
const ims=c.panels.map(u=>{const im=document.createElement('img');im.dataset.src=u;im.className='pn';im.alt='';s.appendChild(im);io.observe(im);return im});
R.appendChild(s);const o={el:s,c:c,ims:ims,read:false,shown:first};secs.push(o);return o}
function curSec(){const mid=innerHeight*.35;let k=0;for(let i=0;i<secs.length;i++){if(secs[i].el.getBoundingClientRect().top<=mid)k=i}return k}
function setCur(sc){const c=sc.c;$('#tt').textContent=c.mtitle+' · '+c.cname;document.title=c.cname+' · {{BRAND}}';
const pv=$('#pv'),nx=$('#nx');pv.className=c.prev?'':'off';pv.href=c.prev?'/r/'+c.prev+'?m='+encodeURIComponent(D.slug):'#';
nx.className=c.next?'':'off';nx.href=c.next?'/r/'+c.next+'?m='+encodeURIComponent(D.slug):'#';
try{history.replaceState(null,'','/r/'+c.cid+'?m='+encodeURIComponent(D.slug))}catch(e){}}
function track(){const i=curSec(),sc=secs[i];
if(i!==curIdx){const first=curIdx<0;curIdx=i;setCur(sc);if(!first&&!sc.shown){sc.shown=true;api('/api/hist',{slug:D.slug,cid:sc.c.cid})}}
let k=0;for(let j=0;j<sc.ims.length;j++){const r=sc.ims[j].getBoundingClientRect();if(r.bottom>0){k=j;try{localStorage.setItem('rp:'+sc.c.cid,JSON.stringify({i:j,o:Math.max(0,-r.top)}))}catch(e){}break}}
$('#pgi').textContent=(k+1)+' / '+sc.ims.length;
if(!sc.read&&sc.el.getBoundingClientRect().bottom<innerHeight*1.6){sc.read=true;api('/api/read',{slug:D.slug,cid:sc.c.cid,v:1})}
if(secs[secs.length-1].el.getBoundingClientRect().bottom<innerHeight*3)loadNext()}
async function loadNext(){if(loading||!nextCid)return;loading=true;
try{const j=await api('/api/chapter/'+nextCid+'?m='+encodeURIComponent(D.slug));
if(j.ok){nextCid=j.c.next;const sc=addSection(j.c,false);sc.ims.slice(0,3).forEach(im=>ld(im));setTimeout(track,500)}}catch(e){}
loading=false;if(!nextCid)endMsg()}
function endMsg(){$('#end').innerHTML='Last chapter ✓<br><br><a href="/m/'+D.slug+'">Back to chapters</a>'}
addEventListener('scroll',()=>{const y=scrollY,dy=y-lastY;if(Math.abs(dy)>12){document.body.classList.toggle('hide',dy>0&&y>90);lastY=y}clearTimeout(tm);tm=setTimeout(track,200)},{passive:true});
R.addEventListener('click',()=>document.body.classList.toggle('hide'));
(async()=>{const sc=addSection(D,true);setCur(sc);if(!nextCid)endMsg();
let p=null;try{p=JSON.parse(localStorage.getItem('rp:'+D.cid))}catch(e){}
if(p&&p.i>0&&p.i<sc.ims.length){const ov=$('#ov');ov.hidden=false;let skip=false;
const go=()=>{skip=true;scrollTo(0,sc.ims[p.i].offsetTop+(p.o||0));ov.hidden=true};
ov.addEventListener('click',go);
const all=Promise.all(sc.ims.slice(0,p.i+1).map(im=>ld(im)));
await Promise.race([all,new Promise(r=>setTimeout(r,2500))]);
if(!skip)go();
all.then(()=>{if(scrollY<5||Math.abs(scrollY-(sc.ims[p.i].offsetTop+(p.o||0)))<4000&&!window._moved)scrollTo(0,sc.ims[p.i].offsetTop+(p.o||0))});
addEventListener('touchstart',()=>{window._moved=1},{once:true,passive:true})}
else sc.ims.slice(0,2).forEach(im=>ld(im));
setTimeout(track,300)})();
</script>""")


def chapter_payload(cid, slug):
    d = parse_panels(cid, cfetch(f"/{cid}/", ttl=600))
    prev = nxt = None
    cname, mtitle, cover = d["chapter_title"], slug, ""
    try:
        m = manga_info(slug)
        ids = [c["chapter_id"] for c in m["chs"]]
        mtitle, cover = m["title"], m.get("cover") or ""
        if cid in ids:
            i = ids.index(cid)
            cname = m["chs"][i]["name"]
            prev = ids[i - 1] if i > 0 else None
            nxt = ids[i + 1] if i + 1 < len(ids) else None
    except Exception:
        app.logger.warning("reader: chapter list unavailable", exc_info=True)
    return {"cid": cid, "slug": slug, "cname": cname or d["chapter_title"], "mtitle": mtitle, "cover": cover,
            "panels": [p["image_url"] for p in d["panels"]], "prev": prev, "next": nxt}


def hist_record(uid, slug, title, cover, cid, cname):
    """Save reading history in the background so the reader opens without waiting for storage."""
    def job():
        try:
            init_schema()
            now = int(time.time())
            sql("insert or replace into hist(uid, slug, title, cover, cid, cname, ts) values(?,?,?,?,?,?,?)",
                [uid, slug, title, cover or "", cid, cname, now])
            sql("insert or replace into reads(uid, slug, cid, ts) values(?,?,?,?)", [uid, slug, cid, now])
        except Exception:
            app.logger.warning("history save failed", exc_info=True)
    threading.Thread(target=job, daemon=True).start()


@app.get("/r/<path:cid>")
def ui_read(cid):
    cid = cid.strip("/")
    slug = request.args.get("m") or re.sub(r"-chapter-[^/]*$", "", cid)
    d = chapter_payload(cid, slug)
    hist_record(cur()["uid"], slug, d["mtitle"], d["cover"], cid, d["cname"])
    return READER.render(d=d)


@app.get("/api/chapter/<path:cid>")
def api_chapter(cid):
    cid = cid.strip("/")
    slug = request.args.get("m") or re.sub(r"-chapter-[^/]*$", "", cid)
    return jsonify({"ok": True, "c": chapter_payload(cid, slug)})


@app.post("/api/hist")
def api_hist():
    d = request.get_json(silent=True) or {}
    slug, cid = d.get("slug", ""), d.get("cid", "")
    if slug and cid:
        try:
            m = manga_info(slug)
            name = next((c["name"] for c in m["chs"] if c["chapter_id"] == cid), cid)
            hist_record(cur()["uid"], slug, m["title"], m.get("cover"), cid, name)
        except Exception:
            pass
    return jsonify({"ok": True})


@app.post("/api/read")
def api_read():
    d = request.get_json(silent=True) or {}
    uid, slug, cid = cur()["uid"], d.get("slug", ""), d.get("cid", "")
    if not slug or not cid:
        return jerr("bad request")
    if d.get("v"):
        sql("insert or replace into reads(uid, slug, cid, ts) values(?,?,?,?)", [uid, slug, cid, int(time.time())])
    else:
        sql("delete from reads where uid=? and cid=?", [uid, cid])
    return jsonify({"ok": True})


@app.post("/api/readall")
def api_readall():
    d = request.get_json(silent=True) or {}
    uid, slug = cur()["uid"], d.get("slug", "")
    if not slug:
        return jerr("bad request")
    if d.get("v"):
        now = int(time.time())
        chs = manga_info(slug)["chs"]
        for i in range(0, len(chs), 40):
            part = chs[i:i + 40]
            params = []
            for c in part:
                params += [uid, slug, c["chapter_id"], now]
            sql("insert or replace into reads(uid, slug, cid, ts) values " + ",".join(["(?,?,?,?)"] * len(part)), params)
    else:
        sql("delete from reads where uid=? and slug=?", [uid, slug])
    return jsonify({"ok": True})


@app.get("/api/continue")
def api_continue():
    rows, _ = q("select slug, title, cover, cid, cname from hist where uid=? order by ts desc limit 30", [cur()["uid"]])
    return jsonify({"ok": True, "items": rows})


# ---------------------------------------------------------------- saved
SAVED = T(MACROS + """<h2>Saved</h2>
<div class=chips>{% for v,l in [('','All'),('reading','Reading'),('completed','Completed'),('plan','Plan to read')] %}<span class="chip {{'on' if not v}}" data-f="{{v}}" onclick="flt(this)">{{l}}</span>{% endfor %}</div>
<div class=g id=sg>{% for m in rows %}{{ card(m) }}{% else %}<p class=empty>Nothing saved yet.<br>Tap ☆ Save on a manga page.</p>{% endfor %}</div>
<script>
window.NOBADGE=false;
const cards=$$('#sg .c');
const stt={{ sts|tojson }};cards.forEach(c=>c.dataset.st=stt[c.dataset.slug]||'reading');
function flt(ch){$$('.chips .chip').forEach(x=>x.classList.toggle('on',x===ch));const f=ch.dataset.f;cards.forEach(c=>c.style.display=(!f||c.dataset.st==f)?'':'none')}
(async()=>{const slugs=cards.map(c=>c.dataset.slug);
for(let i=0;i<slugs.length;i+=6){try{const j=await api('/api/saved/status?s='+encodeURIComponent(slugs.slice(i,i+6).join(',')));
for(const k in (j.d||{})){const v=j.d[k],c=$('#sg .c[data-slug="'+k+'"]');if(!c||!v)continue;
const n=$('.bd.n',c),r=$('.bd.r',c);if(v.new>0){n.textContent='NEW '+v.new;n.hidden=false}
if(v.read>0){r.textContent=v.read+'/'+v.total;r.hidden=false}
if(v.new>0){c.parentNode.insertBefore(c,c.parentNode.firstChild)}}}catch(e){}}})();
</script>""")


@app.get("/saved")
def ui_saved():
    rows, _ = q("select slug, title, cover as image_url, status from bookmarks where uid=? order by ts desc", [cur()["uid"]])
    return page(SAVED, "saved", "Saved", rows=rows, sts={r["slug"]: (r["status"] or "reading") for r in rows})


@app.get("/bookmarks")
def ui_bookmarks_old():
    return redirect("/saved")


@app.get("/api/saved/status")
def api_saved_status():
    uid = cur()["uid"]
    slugs = [s for s in request.args.get("s", "").split(",") if s][:8]
    reads, _ = q("select slug, cid from reads where uid=?", [uid])
    rs = {}
    for r in reads:
        rs.setdefault(r["slug"], set()).add(r["cid"])

    def one(slug):
        try:
            chs = manga_info(slug, ttl=600)["chs"]
        except Exception:
            return slug, None
        read = rs.get(slug, set())
        nums = [c["num"] for c in chs if c["chapter_id"] in read and c["num"] is not None]
        top = max(nums) if nums else None
        new = sum(1 for c in chs if top is not None and c["num"] is not None and c["num"] > top)
        return slug, {"total": len(chs), "read": sum(1 for c in chs if c["chapter_id"] in read), "new": new}

    with ThreadPoolExecutor(4) as ex:
        out = dict(ex.map(one, slugs))
    return jsonify({"ok": True, "d": out})


@app.post("/api/save/<slug>")
def api_save(slug):
    uid = cur()["uid"]
    rows, _ = q("select status from bookmarks where uid=? and slug=?", [uid, slug])
    if rows:
        sql("delete from bookmarks where uid=? and slug=?", [uid, slug])
        return jsonify({"ok": True, "saved": False})
    m = manga_info(slug)
    sql("insert or replace into bookmarks(uid, slug, title, cover, ts, status) values(?,?,?,?,?,?)",
        [uid, slug, m["title"], m.get("cover") or "", int(time.time()), "reading"])
    return jsonify({"ok": True, "saved": True, "status": "reading"})


@app.post("/api/status/<slug>")
def api_status(slug):
    v = (request.get_json(silent=True) or {}).get("status", "")
    if v not in ("reading", "completed", "plan"):
        return jerr("bad status")
    sql("update bookmarks set status=? where uid=? and slug=?", [v, cur()["uid"], slug])
    return jsonify({"ok": True})


# ---------------------------------------------------------------- history
HISTORY = T("""<h2>History <button class="sec sm" style="float:right" onclick="clr()">Clear</button></h2>
{% for r in rows %}<div class=hs>{% if r.cover %}<img loading=lazy src="/hentai/proxy/{{r.cover}}" alt="">{% else %}<span style="width:48px"></span>{% endif %}
<div class=gr><b><a href="/m/{{r.slug}}">{{r.title}}</a></b><small>{{r.cname}} · {{r.when}}</small></div>
<a class="btn sm" href="/r/{{r.cid}}?m={{r.slug}}">Continue</a></div>{% else %}<p class=empty>Nothing read yet</p>{% endfor %}
<script>async function clr(){if(!confirm('Clear your entire reading history?'))return;await api('/api/history/clear',{});location.reload()}</script>""")


@app.get("/history")
def ui_history():
    rows, _ = q("select slug, title, cover, cid, cname, ts from hist where uid=? order by ts desc limit 100", [cur()["uid"]])
    for r in rows:
        r["when"] = fmt_ts(r["ts"])
    return page(HISTORY, "me", "History", rows=rows)


@app.post("/api/history/clear")
def api_history_clear():
    uid = cur()["uid"]
    sql("delete from hist where uid=?", [uid])
    sql("delete from reads where uid=?", [uid])
    return jsonify({"ok": True})


# ---------------------------------------------------------------- downloads: queue / library
def job_view(j):
    return {"id": j["id"], "title": j["title"], "who": j["who"], "status": j["status"], "pct": job_pct(j),
            "done": j["done"], "total": j["total"], "msg": j["msg"], "up_msg": j["up_msg"], "note": j["note"],
            "errors": j["errors"][-4:], "nerr": len(j["errors"]), "failed": len(j["failed"]),
            "secs": round(j["secs"], 1)}


@app.get("/api/jobs")
def api_jobs():
    me = cur()
    own = request.args.get("mine") or request.args.get("brief") or not me["admin"]
    jobs = [j for j in JOBS if (j["uid"] == me["uid"] if own else True)]
    active = sum(1 for j in jobs if j["status"] in ("queued", "running"))
    if request.args.get("brief"):
        return jsonify({"ok": True, "active": active})
    jobs.sort(key=lambda j: (j["status"] not in ("queued", "running"), -j["id"]))
    return jsonify({"ok": True, "active": active, "jobs": [job_view(j) for j in jobs]})


def find_job(jid):
    me = cur()
    return next((j for j in JOBS if j["id"] == jid and owns(me, j["uid"])), None)


def active_of(uid):
    return [j for j in JOBS if j["uid"] == uid and j["status"] in ("queued", "running")]


@app.post("/api/dl")
def api_dl():
    me = cur()
    d = request.get_json(silent=True) or {}
    if not me["admin"] and len(active_of(me["uid"])) >= USER_MAX_JOBS:
        return jsonify({"ok": False, "msg": f"You already have {USER_MAX_JOBS} active jobs. Please wait for them to finish."})
    try:
        job = enqueue(me, d.get("slug", ""), str(d.get("spec", "new")), d.get("per", 1))
    except ValueError:
        return jsonify({"ok": False, "msg": "Invalid selection. Example: 1-50 or 1,5,10-20"})
    if job is None:
        return jsonify({"ok": False, "msg": "Nothing new to download (already downloaded or in the queue)."})
    note = f" · {job['note']}" if job["note"] else ""
    return jsonify({"ok": True, "msg": f"{len(job['chapters'])} chapters added · {job['per']} per PDF{note}", "job": job["id"]})


@app.post("/api/update")
def api_update():
    """Queue not-yet-downloaded chapters for one manga or the whole library (runs in background)."""
    me = cur()
    d = request.get_json(silent=True) or {}
    st = load_state(me["uid"])
    try:
        want_per = int(d.get("per") or 0)
    except (TypeError, ValueError):
        want_per = 0
    slugs = [d["slug"]] if d.get("slug") else list(st)
    if not slugs:
        return jsonify({"ok": False, "msg": "Your library is empty."})

    def work():
        for slug in slugs:
            if not me["admin"] and len(active_of(me["uid"])) >= USER_MAX_JOBS:
                break
            try:
                enqueue(me, slug, "new", want_per or st.get(slug, {}).get("per", 1))
            except Exception:
                app.logger.warning("update failed for %s", slug, exc_info=True)

    threading.Thread(target=work, daemon=True).start()
    return jsonify({"ok": True, "msg": "Checking for new chapters… Progress will appear in the Queue."})


@app.post("/api/cancel/<int:jid>")
def api_cancel(jid):
    j = find_job(jid)
    if j and j["status"] in ("queued", "running"):
        j["cancel"] = True          # the worker sees this in every loop (images, PDF, upload) and stops
        j["status"] = "cancelled"   # show it at once and free the user's job slot
        j["msg"] = j["up_msg"] = ""
        threading.Thread(target=save_jobs, daemon=True).start()   # a cancelled job must not come back after a restart
        return jsonify({"ok": True, "msg": "Cancelled"})
    return jsonify({"ok": True, "msg": "Already finished"})


@app.post("/api/retry/<int:jid>")
def api_retry(jid):
    j = find_job(jid)
    if not j or not j["failed"] or j["status"] in ("queued", "running"):
        return jerr("Nothing to retry.")
    me = {"uid": j["uid"], "name": j["who"], "admin": j["uid"] == 0}
    if not me["admin"] and len(active_of(j["uid"])) >= USER_MAX_JOBS:
        return jerr(f"You already have {USER_MAX_JOBS} active jobs. Please wait for them to finish.")
    seen, sel = set(), []
    for c in j["failed"]:
        if c["chapter_id"] not in seen:
            seen.add(c["chapter_id"])
            sel.append(c)
    j["failed"] = []
    make_job(me, j["slug"], j["title"], sel, j["per"], "retry")
    return jsonify({"ok": True, "msg": f"{len(sel)} chapters re-queued"})


@app.post("/api/jobs/clear")
def api_jobs_clear():
    me = cur()
    for j in [x for x in JOBS if owns(me, x["uid"]) and x["status"] not in ("queued", "running")]:
        JOBS.remove(j)
    return jsonify({"ok": True})


@app.post("/api/auto")
def api_auto():
    uid = cur()["uid"]
    k = f"auto_{uid}"
    rows, _ = q("select 1 as x from kv where k=?", [k])
    if rows:
        sql("delete from kv where k=?", [k])
    else:
        sql("insert or replace into kv(k, v) values(?, '1')", [k])
    return jsonify({"ok": True, "on": not rows})


QUEUE = T("""<h2>Queue <button class="sec sm" style="float:right" onclick="clearDone()">Clear finished</button></h2>
<div id=jl><p class=empty>Loading…</p></div>
<small>A PDF appears in the Library only after it has fully uploaded. Keep the app open while the queue runs (free hosting may sleep).</small>
<script>
window.NOBADGE=true;let tmr;const ME_ADMIN={{ 'true' if me.admin else 'false' }};
function row(j){const live=j.status=='queued'||j.status=='running',bad=j.status=='cancelled'||j.status=='done (errors)'||j.nerr>0;
const cls=j.status=='done'?'ok':(bad&&!live?'er':'');
return '<div class="card job" data-id="'+j.id+'"><div class=h><div><b>'+esc(j.title)+'</b>'+(ME_ADMIN&&j.who?' <small>('+esc(j.who)+')</small>':'')+'<br><span class="st '+(j.status=='done (errors)'?'cancelled':j.status)+'">'+esc(j.status)+'</span> <small>'+j.done+'/'+j.total+' chapters</small></div><span class=pc>'+j.pct+'%</span></div>'
+'<div class="pb '+cls+'"><i style="width:'+j.pct+'%"></i></div>'
+(live?'<small>'+esc(j.status=='queued'?'Waiting in queue…':(j.msg||'Working…'))+(j.up_msg?' · '+esc(j.up_msg):'')+'</small>':'')
+(j.note?'<br><small>'+esc(j.note)+'</small>':'')
+(j.errors.length?'<details style="margin-top:6px"><summary class=er>'+j.nerr+' error</summary>'+j.errors.map(e=>'<small class=er>'+esc(e)+'</small><br>').join('')+'</details>':'')
+'<div style="margin-top:8px;display:flex;gap:8px">'+(live?'<button class="dn sm" onclick="act('+j.id+',\\'cancel\\',this)">Cancel</button>':(j.failed?'<button class="sec sm" onclick="act('+j.id+',\\'retry\\',this)">Retry '+j.failed+'</button>':''))
+(j.status=='done'||j.status=='done (errors)'?'<a class="btn sec sm" href="/library">Open Library</a>':'')+'</div></div>'}
async function tick(){clearTimeout(tmr);let act=0;
try{if(!document.hidden){const j=await api('/api/jobs');act=j.active;$('#jl').innerHTML=j.jobs.length?j.jobs.map(row).join(''):'<p class=empty>No jobs yet.<br>Tap Download on a manga page.</p>';setBadge(j.active)}}catch(e){}
tmr=setTimeout(tick,act?1500:5000)}
async function act(id,w,b){busy(b,1);const j=await api('/api/'+w+'/'+id,{});toast(j.msg||'Done');tick()}
async function clearDone(){await api('/api/jobs/clear',{});tick()}
tick();document.addEventListener('visibilitychange',()=>{if(!document.hidden)tick()});
</script>""")


@app.get("/queue")
def ui_queue():
    return page(QUEUE, "queue", "Queue")


LIB = T("""{% for g in groups %}<section class=grp data-name="{{g.title|lower}}" data-size="{{g.size}}" data-date="{{g.last}}">
<div class=gh><b>{{g.title}} <small>({{g.files|length}})</small></b><button class="sec sm" onclick="upd('{{g.slug}}',this)">Get new</button></div>
{% for f in g.files %}<div class=f data-id="{{f.id}}" data-name="{{f.name|lower}}" data-size="{{f.size}}"><div class=l1><div class=gr><div class=nm>{{f.name}}</div>
<small>{{f.mb}} MB · {{f.left}} din baad auto-delete</small></div>
<button class=sm onclick="getPdf(this,{{f.id}},{{f.name|tojson|forceescape}},{{f.size}})">⬇ Download</button>
<button class="dn sm" onclick="del({{f.id}},this)" aria-label=delete>✕</button></div><div class=pb hidden><i></i></div></div>{% endfor %}</section>
{% else %}<p class=empty>No PDFs yet.<br>Tap Download on a manga page.</p>{% endfor %}""")

LIBPAGE = T("""<h2>Library</h2>
<div id=act></div>
<div class=bar><input id=sq placeholder="Search PDFs…" oninput="applyF()"><select id=so onchange="applyF()"><option value=date>Newest</option><option value=name>Name</option><option value=size>Size</option></select></div>
<div class=bar><button class="sec sm" id=au onclick="auto(this)">Auto-update: {{'ON' if auto else 'OFF'}}</button><button class="sec sm" onclick="upd('',this)">Update all</button><span class=sp></span><small>{{total}} PDF · {{mb}} MB</small></div>
<div id=lib>{{lib|safe}}</div>
<small>PDFs are kept for {{days}} days and then deleted automatically. Until a PDF finishes uploading, only its progress is shown here.</small>
<script>
window.NOBADGE=true;
function applyF(){const t=$('#sq').value.trim().toLowerCase(),s=$('#so').value,box=$('#lib');
$$('.grp',box).forEach(g=>{let any=false;$$('.f',g).forEach(f=>{const ok=!t||f.dataset.name.includes(t)||g.dataset.name.includes(t);f.style.display=ok?'':'none';if(ok)any=true});g.style.display=any?'':'none'});
const gs=$$('.grp',box);gs.sort((a,b)=>s=='name'?a.dataset.name.localeCompare(b.dataset.name):(+b.dataset[s])-(+a.dataset[s]));gs.forEach(g=>box.appendChild(g))}
async function refreshLib(){try{const r=await fetch('/library?frag=1');$('#lib').innerHTML=await r.text();applyF()}catch(e){}}
async function getPdf(btn,id,name,size){const row=btn.closest('.f'),pb=$('.pb',row),bar=$('i',pb);
if(size>130*1048576){location.href='/f/'+id;toast('Download started in your browser');return}
btn.disabled=true;pb.hidden=false;bar.style.width='0';btn.textContent='0%';
try{const r=await fetch('/f/'+id);if(!r.ok)throw 0;const total=+r.headers.get('Content-Length')||size,rd=r.body.getReader(),parts=[];let got=0;
for(;;){const x=await rd.read();if(x.done)break;parts.push(x.value);got+=x.value.length;const p=Math.min(99,Math.floor(got*100/total));bar.style.width=p+'%';btn.textContent=p+'%'}
const url=URL.createObjectURL(new Blob(parts,{type:'application/pdf'})),a=document.createElement('a');a.href=url;a.download=name;document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),60000);
bar.style.width='100%';pb.classList.add('ok');btn.textContent='✓ Saved';toast('Saved to your Downloads folder');
setTimeout(()=>{pb.hidden=true;pb.classList.remove('ok');btn.disabled=false;btn.textContent='⬇ Download'},3500)}
catch(e){toast('Download failed. Please try again.');pb.hidden=true;btn.disabled=false;btn.textContent='⬇ Download'}}
async function del(id,b){if(!confirm('Delete this PDF?'))return;busy(b,1);const j=await api('/api/del/'+id,{});if(j.ok){const f=b.closest('.f'),g=b.closest('.grp');f.remove();if(!$('.f',g))g.remove();toast('Deleted')}else{busy(b,0);toast(j.msg)}}
async function upd(slug,b){busy(b,1);const j=await api('/api/update',Object.assign(slug?{slug:slug}:{},{per:perPref()}));toast(j.msg);busy(b,0);tick()}
async function auto(b){busy(b,1);const j=await api('/api/auto',{});b.textContent='Auto-update: '+(j.on?'ON':'OFF');busy(b,0);toast(j.on?'Auto-update ON':'Auto-update OFF')}
let last=-1,tmr;
async function tick(){clearTimeout(tmr);let n=0;
try{if(!document.hidden){const j=await api('/api/jobs?mine=1');const a=j.jobs.filter(x=>x.status=='queued'||x.status=='running');n=a.length;
$('#act').innerHTML=a.map(x=>'<div class="card job"><div class=h><b>'+esc(x.title)+'</b><span class=pc>'+x.pct+'%</span></div><div class=pb><i style="width:'+x.pct+'%"></i></div><small>'+esc(x.status=='queued'?'Waiting in queue':(x.msg||'Working…'))+(x.up_msg?' · '+esc(x.up_msg):'')+' · will appear here when finished</small></div>').join('');
if(last>0&&n<last)refreshLib();last=n;setBadge(n)}}catch(e){}
tmr=setTimeout(tick,n?1500:5000)}
applyF();tick();document.addEventListener('visibilitychange',()=>{if(!document.hidden)tick()});
</script>""")


def lib_ctx(uid):
    import calendar
    st, rows = par(lambda: load_state(uid),
                   lambda: q("select id, slug, name, size, created from files where coalesce(uid,0)=? and parts>0 order by id desc", [uid])[0])
    now, groups = time.time(), {}
    for r in rows:
        try:
            ts = calendar.timegm(time.strptime(r["created"], "%Y-%m-%d %H:%M:%S"))
        except Exception:
            ts = now
        r["left"] = max(0, RETENTION_DAYS - int((now - ts) // 86400))
        r["mb"] = round(r["size"] / 1048576, 1)
        g = groups.setdefault(r["slug"], {"slug": r["slug"], "title": st.get(r["slug"], {}).get("title") or r["slug"],
                                          "files": [], "size": 0, "last": 0})
        g["files"].append(r)
        g["size"] += r["size"]
        g["last"] = max(g["last"], r["id"])
    return list(groups.values()), len(rows), round(sum(r["size"] for r in rows) / 1048576, 1)


@app.get("/library")
def ui_library():
    uid = cur()["uid"]
    groups, total, mb = lib_ctx(uid)
    html = LIB.render(groups=groups)
    if request.args.get("frag"):
        return Response(html, mimetype="text/html")
    auto = bool(q("select 1 as x from kv where k=?", [f"auto_{uid}"])[0])
    return page(LIBPAGE, "lib", "Library", lib=html, total=total, mb=mb, auto=auto, days=RETENTION_DAYS)


@app.get("/f/<int:fid>")
def ui_file(fid):
    me = cur()
    rows, _ = q("select name, size, parts, uid, tg from files where id=? and parts>0", [fid])
    if not rows or not owns(me, rows[0]["uid"]):
        return reply(status=404, message="File not found, or it has not finished uploading yet.")
    f = rows[0]
    if f.get("tg"):  # new way: stream straight from storage (keeps Range so a broken download can resume)
        hdr = {"Range": request.headers["Range"]} if request.headers.get("Range") else {}
        try:
            up = sqlhttp.get(f"{STORE_BASE}/file/{f['tg']}", headers=hdr, stream=True, timeout=(15, 120))
        except requests.RequestException:
            return reply(status=502, message="Storage is not reachable right now. Try again in a moment.")
        if up.status_code not in (200, 206):
            up.close()
            return reply(status=404 if up.status_code == 404 else 502, message="Storage could not give this file.")
        resp = Response(up.iter_content(256 * 1024), status=up.status_code, mimetype="application/pdf")
        resp.call_on_close(up.close)
        for h in ("Content-Length", "Content-Range"):
            if up.headers.get(h):
                resp.headers[h] = up.headers[h]
        resp.headers["Accept-Ranges"] = "bytes"
        resp.headers["Content-Disposition"] = "attachment; filename*=UTF-8''" + quote(f["name"])
        return resp

    def get_chunk(n):
        r, j = q("select data from chunks where file_id=? and n=?", [fid, n])
        if not r or j.get("truncated"):
            raise RuntimeError("chunk missing/truncated; lower CHUNK_KB")
        return base64.b64decode(r[0]["data"])

    def gen():
        with ThreadPoolExecutor(DL_PAR) as ex:
            n = 0
            while n < f["parts"]:
                futs = [ex.submit(get_chunk, k) for k in range(n, min(n + DL_PAR, f["parts"]))]
                for fu in futs:
                    yield fu.result()
                n += DL_PAR

    resp = Response(gen(), mimetype="application/pdf")
    resp.headers["Content-Disposition"] = "attachment; filename*=UTF-8''" + quote(f["name"])
    resp.headers["Content-Length"] = str(f["size"])
    return resp


@app.post("/api/del/<int:fid>")
def api_del(fid):
    me = cur()
    rows, _ = q("select uid from files where id=?", [fid])
    if rows and owns(me, rows[0]["uid"]):
        delete_file(fid, rows[0]["uid"] or 0)
        return jsonify({"ok": True})
    return jerr("File not found.", 404)


# ---------------------------------------------------------------- me / account
ME = T("""<h2>{{me.name}} {% if me.admin %}<span class="pill ac">admin</span>{% endif %}</h2>
<div class=card><b>Storage</b><br><small>{{n}} PDF · {{mb}} MB (kept for {{days}} days)</small></div>
<a class="card row" href=/history style="display:flex"><span class=gr><b>Reading history</b></span><span class=mut>›</span></a>
{% if me.admin %}<a class="card row" href=/admin style="display:flex"><span class=gr><b>Admin console</b></span><span class=mut>›</span></a>{% endif %}
{% if not me.admin %}<div class=card><b>Change password</b><input id=po type=password placeholder="Current password" style="margin-top:8px"><input id=pn type=password placeholder="New password (6+ characters)" style="margin-top:8px">
<button style="margin-top:8px;width:100%" onclick="chpw(this)">Save</button><small>Changing your password signs you out on all other devices.</small></div>{% endif %}
<div class=card><b>Security</b><br><small>If you are signed in on another phone or browser, you can sign out everywhere from here.</small>
<div style="margin-top:8px;display:flex;gap:8px"><button class="dn" onclick="allOut(this)">Sign out of all devices</button><form method=post action=/logout style="margin:0"><button class=sec>Log out</button></form></div></div>
<div class=card><b>Support</b><br><small>Need help, forgot your password, or found a problem? Message us on Telegram.</small>
<div style="margin-top:8px"><a class="btn sec" href="{{TG}}" target=_blank rel="noopener noreferrer" data-noload>Contact support</a></div></div>
<div class=card><b>Install as an app</b><br><small>Open your browser menu and choose “Add to Home screen” or “Install app” to use it full-screen.</small></div>
<script>
async function chpw(b){busy(b,1);const j=await api('/api/pw',{old:$('#po').value,new:$('#pn').value});busy(b,0);toast(j.msg||'Done');if(j.ok){$('#po').value='';$('#pn').value=''}}
async function allOut(b){if(!confirm('Sign out of all devices (including this one)?'))return;await api('/api/logoutall',{});location='/login'}
</script>""")


@app.get("/me")
def ui_me():
    me = cur()
    rows, _ = q("select count(*) as n, coalesce(sum(size),0) as s from files where coalesce(uid,0)=? and parts>0", [me["uid"]])
    return page(ME, "me", "Me", n=rows[0]["n"], mb=round(rows[0]["s"] / 1048576, 1), days=RETENTION_DAYS)


@app.get("/pw")
def ui_pw():
    return redirect("/me")


@app.post("/api/pw")
def api_pw():
    me = cur()
    d = request.get_json(silent=True) or {}
    old, new = d.get("old", ""), d.get("new", "")
    if me["admin"]:
        return jerr("The admin password is changed in the hosting dashboard (APP_PASSWORD).")
    rows, _ = q("select pw from users where id=?", [me["uid"]])
    if not rows or not check_password_hash(rows[0]["pw"], old):
        return jerr("Current password is incorrect.")
    if len(new) < MINPW or len(new) > 128:
        return jerr(f"New password must be {MINPW}-128 characters.")
    sql("update users set pw=? where id=?", [generate_password_hash(new, method="pbkdf2:sha256"), me["uid"]])
    session["sv"] = bump_sv(me["uid"])  # this device stays logged in, all others are logged out
    return jsonify({"ok": True, "msg": "Password updated. Other devices have been signed out."})


@app.post("/api/logoutall")
def api_logoutall():
    bump_sv(cur()["uid"])
    session.clear()
    return jsonify({"ok": True})


# ---------------------------------------------------------------- admin console
def usage_rows():
    rows, _ = q("select coalesce(uid,0) as uid, count(*) as n, coalesce(sum(size),0) as sz from files where parts>0 group by coalesce(uid,0)")
    return {r["uid"]: r for r in rows}


ADMIN = T("""<h2>Overview</h2>
<div class=stat><div class=card><small>Users</small><b>{{nusers}}</b></div><div class=card><small>PDFs</small><b>{{tot.n}}</b></div>
<div class=card><small>Storage</small><b>{{mb(tot.sz)}} MB</b></div><div class=card><small>Active jobs</small><b>{{nactive}}</b></div>
<div class=card><small>Failed jobs</small><b class="{{'er' if failed}}">{{failed}}</b></div></div>
<h3>Recent errors</h3>
<div class=card>{% for e in errs %}<div style="padding:6px 0;border-bottom:1px solid var(--bd)"><small>{{e.when}} · {{e.who}} · {{e.title}}</small><br><span class=er style="font-size:13px">{{e.err}}</span></div>{% else %}<small>No errors 🎉</small>{% endfor %}</div>
<h3>Users</h3>
<div class=card style="overflow-x:auto"><table><tr><th>User</th><th>PDFs</th><th>Storage</th><th></th></tr>
<tr><td><b>{{admin_name}}</b> <small>(admin)</small></td><td>{{adm.n}}</td><td>{{mb(adm.sz)}} MB</td><td><a href="/admin/u/0" class="btn sec sm">Open</a></td></tr>
{% for u in users %}<tr><td><b>{{u.name}}</b><br><small>{{u.when}}</small></td><td>{{u.n}}</td><td>{{mb(u.sz)}} MB</td><td><a href="/admin/u/{{u.id}}" class="btn sec sm">Open</a></td></tr>{% endfor %}</table></div>
<h3>New user</h3>
<form method=post action=/admin/new class=card><input name=u placeholder="username (3-20: a-z 0-9 _ . -)" autocapitalize=none style="margin-bottom:8px"><input name=p placeholder="password (6+ characters)" style="margin-bottom:8px"><button style="width:100%">Create user</button></form>
<h3>Maintenance</h3>
<form method=post action=/admin/cleanup class=card><small>Deletes PDFs older than {{days}} days (all users) and unfinished uploads. This also runs automatically every 6 hours.</small><div style="margin-top:8px"><button class=sec>Run cleanup now</button></div></form>""")

ADMUSER = T("""<p><a href=/admin class=mut>‹ Overview</a></p><h2>{{name}}</h2>
{% if uid %}<div class=card><b>Account</b><form method=post action="/admin/pw/{{uid}}" style="margin:8px 0"><input name=p placeholder="New password"><button style="margin-top:8px" class=sec>Reset password (signs out all devices)</button></form>
<div style="display:flex;gap:8px;flex-wrap:wrap"><form method=post action="/admin/out/{{uid}}"><button class=sec>Logout all devices</button></form>
<form method=post action="/admin/del/{{uid}}" onsubmit="return confirm('Delete {{name}} and all of their PDFs and history?')"><button class=dn>Delete user</button></form></div></div>{% endif %}
<h3>History</h3><div class=card>{% for r in hist %}<div class=row><span class=gr><a href="/m/{{r.slug}}"><b>{{r.title}}</b></a><br><small>{{r.cname}} · {{r.when}}</small></span></div>{% else %}<small>Nothing yet</small>{% endfor %}</div>
<h3>Saved</h3><div class=card>{% for b in bm %}<div class=row><a href="/m/{{b.slug}}" class=gr>{{b.title}}</a><small>{{b.status or 'reading'}}</small></div>{% else %}<small>Nothing yet</small>{% endfor %}</div>
<h3>PDF library</h3><div class=card>{% for f in files %}<div class=row><span class=gr><div class=t1>{{f.name}}</div><small>{{(f.size/1048576)|round(1)}} MB</small></span>
<a class="btn sec sm" href="/f/{{f.id}}">⬇</a></div>{% else %}<small>Nothing yet</small>{% endfor %}</div>""")


@app.get("/admin")
def ui_admin():
    need_admin()
    init_schema()
    users, use, tot = par(lambda: q("select id, name, created from users order by id")[0], usage_rows,
                          lambda: q("select count(*) as n, coalesce(sum(size),0) as sz from files where parts>0")[0][0])
    for u in users:
        u["when"] = fmt_ts(u["created"])
        x = use.get(u["id"], {})
        u["n"], u["sz"] = x.get("n", 0), x.get("sz", 0)
    errs = [{**e, "when": fmt_ts(e["ts"])} for e in reversed(ERRLOG)]
    failed = sum(1 for j in JOBS if j["failed"] or j["status"] in ("done (errors)", "cancelled") and j["errors"])
    return page(ADMIN, "", "Admin", mode="admin", users=users, nusers=len(users), tot=tot, adm=use.get(0, {"n": 0, "sz": 0}),
                nactive=sum(1 for j in JOBS if j["status"] in ("queued", "running")), failed=failed, errs=errs,
                mb=lambda b: round((b or 0) / 1048576, 1), admin_name=ADMIN_NAME, days=RETENTION_DAYS)


@app.get("/admin/u/<int:uid>")
def ui_admin_user(uid):
    need_admin()
    if uid:
        u, _ = q("select name from users where id=?", [uid])
        if not u:
            return reply(status=404)
        name = u[0]["name"]
    else:
        name = ADMIN_NAME
    hist, files, bm = par(lambda: q("select slug, title, cid, cname, ts from hist where uid=? order by ts desc limit 50", [uid])[0],
                          lambda: q("select id, name, size, created from files where coalesce(uid,0)=? and parts>0 order by id desc", [uid])[0],
                          lambda: q("select slug, title, status from bookmarks where uid=? order by ts desc", [uid])[0])
    for r in hist:
        r["when"] = fmt_ts(r["ts"])
    return page(ADMUSER, "", name, mode="admin", name=name, uid=uid, hist=hist, files=files, bm=bm)


@app.post("/admin/new")
def ui_admin_new():
    need_admin()
    init_schema()
    name, pw = request.form.get("u", "").strip().lower(), request.form.get("p", "")
    if not re.fullmatch(r"[a-z0-9_.-]{3,20}", name) or name == ADMIN_NAME.lower():
        session["flash"] = "Invalid username (3-20 characters: a-z 0-9 _ . -)."
    elif len(pw) < MINPW or len(pw) > 128:
        session["flash"] = f"Password must be {MINPW}-128 characters."
    elif q("select id from users where name=?", [name])[0]:
        session["flash"] = "That username is already taken."
    else:
        sql("insert into users(name, pw, created) values(?,?,?)",
            [name, generate_password_hash(pw, method="pbkdf2:sha256"), int(time.time())])
        refresh_sv()
        session["flash"] = f"User '{name}' created."
    return redirect("/admin")


@app.post("/admin/pw/<int:uid>")
def ui_admin_pw(uid):
    need_admin()
    pw = request.form.get("p", "")
    if len(pw) < MINPW or len(pw) > 128 or uid <= 0:
        session["flash"] = f"Password must be {MINPW}-128 characters."
    else:
        sql("update users set pw=? where id=?", [generate_password_hash(pw, method="pbkdf2:sha256"), uid])
        bump_sv(uid)
        session["flash"] = "Password reset. The user was signed out of all devices."
    return redirect(f"/admin/u/{uid}")


@app.post("/admin/out/<int:uid>")
def ui_admin_out(uid):
    need_admin()
    if uid > 0:
        bump_sv(uid)
        session["flash"] = "The user was signed out of all devices."
    return redirect(f"/admin/u/{uid}")


@app.post("/admin/del/<int:uid>")
def ui_admin_del(uid):
    need_admin()
    if uid > 0:
        for r in q("select tg from files where uid=? and tg is not null and tg != ''", [uid])[0]:
            tg_rm(r["tg"])
        sql("delete from chunks where file_id in (select id from files where uid=?)", [uid])
        sql("delete from files where uid=?", [uid])
        sql("delete from hist where uid=?", [uid])
        sql("delete from reads where uid=?", [uid])
        sql("delete from bookmarks where uid=?", [uid])
        sql("delete from kv where k in (?, ?, ?)", [skey(uid), f"auto_{uid}", f"sv_{uid}"])
        sql("delete from users where id=?", [uid])
        refresh_sv()
        session["flash"] = "User deleted."
    return redirect("/admin")


@app.post("/admin/cleanup")
def ui_admin_cleanup():
    need_admin()
    session["flash"] = f"Cleanup done: {expire_old()} old / incomplete files removed."
    return redirect("/admin")


if __name__ == "__main__":
    LOCAL_MODE = True
    app.config["SESSION_COOKIE_SECURE"] = False
    app.run(
        host=os.environ.get("HOST", "127.0.0.1"),
        port=int(os.environ.get("PORT", "8000")),
        debug=False,
    )
