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
IMG_PAR = max(1, min(int(os.environ.get("IMG_PAR", "6")), 10))     # parallel image downloads
NUM_WORKERS = max(1, min(int(os.environ.get("JOB_WORKERS", "2")), 4))  # jobs running at the same time
USER_MAX_CH = int(os.environ.get("USER_MAX_CH", "50"))             # chapters per request for normal users
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


def store_pdf(path, name, slug, uid, cb=None):
    """Upload a PDF to SQL storage in base64 chunks (several INSERTs in parallel). Returns the file id."""
    init_schema()
    size = os.path.getsize(path)
    j = sql("insert into files(slug, name, size, parts, created, uid) values(?,?,?,0,datetime('now'),?)",
            [slug, name, size, uid])
    fid = j.get("last_id") or 0
    if not fid:
        rows, _ = q("select max(id) as m from files")
        fid = rows[0]["m"]
    n = 0
    total_parts = max(1, -(-size // CHUNK))
    try:
        with open(path, "rb") as f, ThreadPoolExecutor(UP_PAR) as ex:
            while True:
                futs = []
                for _ in range(UP_PAR):
                    batch = []
                    for _ in range(PER_INSERT):
                        buf = f.read(CHUNK)
                        if not buf:
                            break
                        batch.append(base64.b64encode(buf).decode())
                    if not batch:
                        break
                    marks = ",".join("(?,?,?)" for _ in batch)
                    params = []
                    for k, b in enumerate(batch):
                        params += [fid, n + k, b]
                    futs.append(ex.submit(sql, f"insert into chunks(file_id, n, data) values {marks}", params))
                    n += len(batch)
                if not futs:
                    break
                for fu in futs:
                    fu.result()
                if cb:
                    cb(min(1.0, n / total_parts))
        sql("update files set parts=? where id=?", [n, fid])  # parts>0 = fully uploaded; only then it shows in Library
    except Exception:
        try:
            sql("delete from chunks where file_id=?", [fid])
            sql("delete from files where id=?", [fid])
        except Exception:
            pass
        raise
    return fid


def delete_file(fid, owner):
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
    if len(_CH) > 120:
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
    if len(_CH) > 120:
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
    if not me["admin"] and len(sel) > USER_MAX_CH:
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
                   for j in JOBS if j["status"] in ("queued", "running")]
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


def housekeep_loop():
    time.sleep(90)
    while True:
        try:
            n = expire_old()
            if n:
                app.logger.info("housekeeping removed %d old files", n)
        except Exception:
            app.logger.warning("housekeeping error", exc_info=True)
        time.sleep(6 * 3600)


def ensure_workers():
    _workers[:] = [t for t in _workers if t.is_alive()]
    while len(_workers) < NUM_WORKERS:
        t = threading.Thread(target=worker, daemon=True)
        t.start()
        _workers.append(t)


def worker():
    while True:
        job = JOBQ.get()
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


def finish_group(job, tmp, pdf, name, okc):
    """Upload the PDF and update the library state. Runs in the background while the next group downloads."""
    t0 = time.time()
    job["up_n"], job["up_cur"] = len(okc), 0.0
    try:
        job["up_msg"] = f"Uploading {name} 0%"

        def prog(f):
            job["up_cur"] = f
            job["up_msg"] = f"Uploading {name} {int(f * 100)}%"

        fid = store_pdf(pdf, name, job["slug"], job["uid"], cb=prog)
        with LOCK:
            st = load_state(job["uid"])
            rec = st.setdefault(job["slug"], {"chapters": {}})
            rec.update({"title": job["title"], "per": job["per"]})
            for c in okc:
                rec["chapters"].setdefault(c["chapter_id"], {}).update(
                    {"name": c["name"], "num": c["num"], "file_id": fid})
            save_state(job["uid"], st)
    except Exception as e:
        job["errors"].append(f"upload {name}: {str(e)[:150]}")
        job["failed"] += okc
    finally:
        job["uploaded"] += len(okc)
        job["up_cur"], job["up_n"], job["up_msg"] = 0.0, 0, ""
        job["t"]["up"] += time.time() - t0
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
            tmp = tempfile.mkdtemp(prefix="hj_")
            handed = False
            try:
                files, okc = [], []
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
                if not files:
                    continue
                first, last = chap_label(okc[0]), chap_label(okc[-1])
                name = f'{safe(job["title"])} - Chapter {first}.pdf' if len(okc) == 1 else \
                       f'{safe(job["title"])} - Ch {first}-{last}.pdf'
                pdf = os.path.join(tmp, "out.pdf")
                job["msg"] = f"Building PDF: {name}"
                t0 = time.time()
                build_pdf(files, pdf)
                job["t"]["pdf"] += time.time() - t0
                for p in files:  # images are inside the PDF now, free the disk
                    try:
                        os.remove(p)
                    except OSError:
                        pass
                pend.append(up.submit(finish_group, job, tmp, pdf, name, okc))
                handed = True
                while len(pend) > 1:  # at most one upload waiting, so disk/memory stay small
                    pend.pop(0).result()
            except Exception as e:
                job["errors"].append(f"PDF group {g // per + 1}: {str(e)[:150]}")
                job["failed"] += group
            finally:
                if not handed:
                    shutil.rmtree(tmp, ignore_errors=True)
        for f in pend:
            f.result()
    finally:
        up.shutdown(wait=True)


def fetch_chapter_images(job, tmp, ci, c):
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
            res = fetch_image(url)
            if res:
                break
            cnt["fail"] += 1
            time.sleep(1.0 * (k + 1))
        if not res:
            raise RuntimeError(f"image {idx} failed")
        path = os.path.join(tmp, f"{ci:03d}_{idx:04d}.{EXT.get(res[1], 'jpg')}")
        with open(path, "wb") as fh:
            fh.write(res[0])
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
        job["par"] = max(2, job["par"] - 2)
    job["t"]["img"] += time.time() - t0
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
_LOGO_PNG = (
    "iVBORw0KGgoAAAANSUhEUgAAAgAAAAIACAMAAADDpiTIAAAB4FBMVEX////o3/iifeqfde+mc/idc+2mcfmkcPijb/iibvedcfCf"
    "bvSdce+bcO+bbvCZcOuVcOagbfafbPaea/WdbPKdavWdafScbPKcavOcafSbbPGbafKbaPOZbO+ZavCZafCaaPKaZ/OXZ++Va+qT"
    "a+eTaOqQaeaOaeKpX/SYZfKXZfGWZPCVZe6UYvCSZOyRZemSYe2RYO6QXu2OZOeNYeiMY+WLZOKOX+uLX+eOXeyNW+yLXOmLWuqK"
    "WOqIYeGHXuKHXeOIWueIWOmFWuOIV+mHVumGVeiFVuaEVOeCWOGBVOKDUuZ/UuKBWt9+Vd58VdmaTfaBUeWAUOR/T+R/TuR+TuR9"
    "TeN9UOF7TuB7TOJ6UN16S+J5SuF5S+B5SeF3TN13Sd93SN92R991Rt90Rt13Ttt1S9pzSNpxSNaUQviIPOl8Ntt0Rd5zRN1yRNxz"
    "O9dwRNtwQtxvRNhvQdtvNdFsQdhsP9lrPtlpPtVpO9hnO9VoNtJpLMRjOstjN9NiNdNgM9NeM85dMdJcMNFcL9FbLtBaLdBXLcNY"
    "LM9XK85WKs5gKb9aJbJVKc1SJsxKI5c7JXI6GH4dB1cbC0UaFSoaCEcaCEYaB0cXDDYVBj0TBjoTBToQEBgODhQNDhISBTpZ6S9l"
    "AACNjklEQVR42u29i19UR7Yv3qDOueMI+jvXuSLIQ0QYFQVFHsYMD4khEB6JjgExBlQEotEfvtGPmJxk5mTO2JNuQJM5Ocb7r/6q"
    "Vr1Wvfau3b0bML+ssukNSWbU9X2star27szbkserfD6Xy65MTEz0ttT+7t/4+l//xheJ36P1//yeLx7/ztf//ne0SPyRLhL7+Tqw"
    "ny8SB8UicUSsI/AicZQtEsfYQnFcLBQnxTLilFgkztCF4j2xeLwvFo8/08XjHFkfiPXBB+M3F1dWstlcLp9ff1X67GRK+L/9C0l9"
    "dmL37/Qg2efBss8Q8L9+T7IvQ+VfogDlHuKPIkj2ZbD8H+C5Z4FzL4Ll/6iRfY4AK+zcSwTI0PN/BuVeIkALlX8WkHse5z84L2Ji"
    "JVdiGGRKRvts7x9+t50sM/scAU7+s9w7FMDBfsz//7Pf5n+Dxv+DKPdx/D+egP+C/Wnxn2afLRIf0kVilMDg1TsEAJL8ru0kzOz7"
    "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")


def make_icon(size):
    """App icon: the HentaiJaat anime-eye logo (pre-rendered 512px PNG, resized when needed)."""
    im = Image.open(BytesIO(base64.b64decode(_LOGO_PNG))).convert("RGB")
    if size != im.size[0]:
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
<div class=bar style="flex-wrap:wrap"><input id=sp value="new" placeholder="new · all · 1-50 · latest 10"><select id=per><option value=1>1 chapter = 1 PDF</option><option value=3>3 chapters = 1 PDF</option><option value=5>5 chapters = 1 PDF</option><option value=10>10 chapters = 1 PDF</option><option value=20>20 chapters = 1 PDF</option></select></div>
<small>Examples: new · all · 1-50 · 1,5,10-20 · latest 10</small><div style="margin-top:8px"><button onclick="dlAdd(slug,$('#sp').value,$('#per').value,this)">Add to queue</button></div></details>
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
#ov{position:fixed;inset:0;background:#000;z-index:9;display:flex;align-items:center;justify-content:center;color:#9aa0b0}</style>
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
    return jsonify({"ok": True, "msg": f"{len(job['chapters'])} chapters added to the queue{note}", "job": job["id"]})


@app.post("/api/update")
def api_update():
    """Queue not-yet-downloaded chapters for one manga or the whole library (runs in background)."""
    me = cur()
    d = request.get_json(silent=True) or {}
    st = load_state(me["uid"])
    slugs = [d["slug"]] if d.get("slug") else list(st)
    if not slugs:
        return jsonify({"ok": False, "msg": "Your library is empty."})

    def work():
        for slug in slugs:
            if not me["admin"] and len(active_of(me["uid"])) >= USER_MAX_JOBS:
                break
            try:
                enqueue(me, slug, "new", st.get(slug, {}).get("per", 1))
            except Exception:
                app.logger.warning("update failed for %s", slug, exc_info=True)

    threading.Thread(target=work, daemon=True).start()
    return jsonify({"ok": True, "msg": "Checking for new chapters… Progress will appear in the Queue."})


@app.post("/api/cancel/<int:jid>")
def api_cancel(jid):
    j = find_job(jid)
    if j and j["status"] in ("queued", "running"):
        j["cancel"] = True
        j["msg"] = "Cancelling…"
    return jsonify({"ok": True})


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
async function upd(slug,b){busy(b,1);const j=await api('/api/update',slug?{slug:slug}:{});toast(j.msg);busy(b,0);tick()}
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
    rows, _ = q("select name, size, parts, uid from files where id=? and parts>0", [fid])
    if not rows or not owns(me, rows[0]["uid"]):
        return reply(status=404, message="File not found, or it has not finished uploading yet.")
    f = rows[0]

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
