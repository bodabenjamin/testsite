#!/usr/bin/env python3
# lopas_seq_tabs_fast_parallel_crashproof_supabase_FASTSAVE_FONTSBLOCK_FLAGS_ASYNC_BATCH_SAFEEXEC_NAVTAG_SPEED.py

import time
from datetime import datetime
import os
import random
import warnings
import re
import json
import threading
from queue import Queue, Empty
from urllib.parse import urljoin, urlparse, parse_qs, unquote
import base64
import platform
import tempfile
import shutil
import uuid  # correlation_id-hoz

warnings.filterwarnings("ignore", category=ResourceWarning)

import requests
import undetected_chromedriver as uc
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.common.action_chains import ActionChains
from selenium.common.exceptions import (
    StaleElementReferenceException,
    NoSuchWindowException,
)

# --- DEBUG kapcsoló HTTP hívásokhoz ---
DEBUG_HTTP = os.getenv("DEBUG_HTTP", "0") == "1"

IS_MAC = (platform.system() == "Darwin")
KEY_MOD = Keys.COMMAND if IS_MAC else Keys.CONTROL

# ---------- CONFIG ----------
DEFAULT_BASE = "https://en.surebet.com"
LOGIN_URL = "https://surebet.com/users/sign_in"
CHECK_INTERVAL = 1.5
WAIT_FOR_REDIRECT = 15
SEEN_FILE = "seen_ids.txt"
FOUND_LINKS_FILE = "found_links.txt"
LINK_CACHE_FILE = "link_cache.json"

# Supabase Edge Functions
SUPABASE_URL = "https://sonudgyyvxncdcganppl.supabase.co"
SUPABASE_ANON_KEY = os.getenv("SUPABASE_ANON_KEY") or "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6InNvbnVkZ3l5eXZ4bmNkY2dhbnBwbCIsInJvbGUiOiJhbm9uIiwiaWF0IjoxNzYwMDMwOTQzLCJleHAiOjIwNzU2MDY5NDN9.QhtBEhUYoZU8dukJ2bNcy95bXW7unxln8NPe_13eBQ4"

SAVE_TIP_URL    = f"{SUPABASE_URL}/functions/v1/save-tip"
UPDATE_TIP_URL  = f"{SUPABASE_URL}/functions/v1/update-tip"
DELETE_TIP_URL  = f"{SUPABASE_URL}/functions/v1/delete-tip"
UPDATE_TIPS_BATCH_URL = f"{SUPABASE_URL}/functions/v1/update-tips-batch"
DELETE_TIPS_BATCH_URL = f"{SUPABASE_URL}/functions/v1/delete-tips-batch"

HTTP_HEADERS = {
    "Content-Type": "application/json",
    "apikey": SUPABASE_ANON_KEY,
    "Authorization": f"Bearer {SUPABASE_ANON_KEY}",
}

# Gyors beállítások
RESOLVE_TIMEOUT = 5.5
RESOLVE_STABLE_PERIOD = 0.35
RESOLVE_POLL_INTERVAL = 0.05
HANDLE_WAIT_TIMEOUT = 3.8
HEADLESS = False

# --- FAST FINAL (gyors elfogadás) beállítások ---
FAST_FINAL_STABLE_PERIOD = 0.07  # rövid stabilitási ablak gyors mintákra

OPEN_WITHIN_PAIR_MS = 80             # két link ugyanazon párban: A 0ms, B +80ms
OPEN_PAIR_STAGGER_MS_BASE = 200  

# NAV-specifikus feloldás
NAV_MIN_WAIT = 1.0         # en.surebet.com/nav-on minimum türelmi idő
RESOLVE_TIMEOUT_NAV = 3.30   # NAV-on hosszabb plafon
NAV_STABLE_AFTER_EXIT = 0.42 # ha kimentünk NAV-ról, ennyit várunk stabilan

# --- ACTIVE / GONE ---
ACTIVE_FILE = "active_ids.txt"
DISAPPEAR_GRACE_SEC = 4.5

# --- UPDATE CONFIG ---
UPDATE_MIN_INTERVAL = 2.0
UPDATE_DECIMALS = 2

# --- GROUP-LINK KEZELÉS ---
GROUP_EMPTY_CLOSE_TB_THRESHOLD = 1
GROUP_REOPEN_BACKOFF_SEC = 120
GROUP_ERR_BACKOFF_SEC = 90
GROUP_SELECTOR = "tbody.surebet_record"

# --- GROUP RÉSZLEGES REFRESH ---
GROUP_REFRESH_MIN = 35
GROUP_REFRESH_MAX = 55
GROUP_REFRESH_SKIP_ON_NEW_SEC = 10

# --- MAIN OLDAL PLAY/REFRESH ---
MAIN_REFRESH_MIN = 50
MAIN_REFRESH_MAX = 75

# --- MAIN PAGINATE WRAPPER REFRESH ---
MAIN_PAGINATE_REFRESH_MIN = 70
MAIN_PAGINATE_REFRESH_MAX = 90

# --- NEXT PAGE KEZELÉS ---
NEXT_REFRESH_MIN = 28
NEXT_REFRESH_MAX = 42
NEXT_SELECTOR = "tbody.surebet_record"
NEXT_EMPTY_CLOSE_TB_THRESHOLD = 0

# --- LOG kapcsoló ---
LOG_ENABLED = True
# Csendesítők a "már nyitva" spamre:
LOG_GROUP_ALREADY_OPEN_VERBOSE = False  # ha True, ír; ha False, elnémítva
LOG_NEXT_ALREADY_OPEN_VERBOSE  = False  # ha True, ír; ha False, elnémítva

# --- NAV backoff ---
NAV_RETRY_BASE = 20.0   # sec
NAV_RETRY_MAX  = 300.0  # sec

def log(msg):
    if LOG_ENABLED:
        print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}")

def warn(msg):
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}")

def load_seen():
    s = set()
    if os.path.exists(SEEN_FILE):
        with open(SEEN_FILE, "r", encoding="utf-8") as f:
            for line in f:
                parts = line.strip().split(" | ", 1)
                if len(parts) == 2:
                    _, tid = parts
                    s.add(tid)
    return s

def save_seen_line(tbody_id):
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with open(SEEN_FILE, "a", encoding="utf-8") as f:
        f.write(f"{ts} | {tbody_id}\n")

def remove_seen_line(tbody_id):
    if not os.path.exists(SEEN_FILE):
        return
    try:
        with open(SEEN_FILE, "r", encoding="utf-8") as f:
            lines = [ln for ln in f.readlines() if f" | {tbody_id}" not in ln]
        with open(SEEN_FILE, "w", encoding="utf-8") as f:
            f.writelines(lines)
    except Exception:
        pass

def load_active():
    s = set()
    if os.path.exists(ACTIVE_FILE):
        with open(ACTIVE_FILE, "r", encoding="utf-8") as f:
            for line in f:
                tid = line.strip()
                if tid:
                    s.add(tid)
    return s

def save_active_all(active_set: set):
    with open(ACTIVE_FILE, "w", encoding="utf-8") as f:
        for tid in sorted(active_set):
            f.write(tid + "\n")

def load_link_cache():
    if os.path.exists(LINK_CACHE_FILE):
        try:
            with open(LINK_CACHE_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}

def save_link_cache(cache: dict):
    try:
        with open(LINK_CACHE_FILE, "w", encoding="utf-8") as f:
            json.dump(cache, f, indent=2, ensure_ascii=False)
    except Exception:
        pass

# ---------- Chrome init ----------
PERSIST_PROFILE = os.getenv("SB_PERSIST_PROFILE", "0") == "1"
if PERSIST_PROFILE:
    PROFILE_DIR = os.path.abspath("./profile_surebet") if not os.getenv("SB_CHROME_PROFILE_DIR") else os.getenv("SB_CHROME_PROFILE_DIR")
else:
    PROFILE_DIR = tempfile.mkdtemp(prefix="sb_profile_")

chrome_options = Options()
if HEADLESS:
    chrome_options.add_argument("--headless=new")

chrome_options.add_argument(f"--user-data-dir={PROFILE_DIR}")

# Gyorsító/tiltó kapcsolók
chrome_options.add_argument("--disable-features=OptimizationHints,TranslateUI")
chrome_options.add_argument("--disable-site-isolation-trials")
chrome_options.add_argument("--disable-translate")
chrome_options.add_argument("--disable-infobars")
chrome_options.add_argument("--disable-sync")
chrome_options.add_argument("--disable-client-side-phishing-detection")
chrome_options.add_argument("--disable-gpu")
chrome_options.add_argument("--disable-dev-shm-usage")
chrome_options.add_argument("--disable-blink-features=AutomationControlled")
chrome_options.add_argument("--window-size=1920,1080")
chrome_options.add_argument("--disable-popup-blocking")
chrome_options.add_argument("--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/141.0.0.0 Safari/537.36")

# FONTOK tiltása + képek tiltása
chrome_options.add_argument("--blink-settings=imagesEnabled=false")
chrome_options.add_argument("--disable-extensions")
chrome_options.add_argument("--mute-audio")
chrome_options.add_argument("--disable-notifications")
chrome_options.add_argument("--no-default-browser-check")
chrome_options.add_argument("--no-first-run")

try:
    chrome_options.set_capability("pageLoadStrategy", "eager")
except Exception:
    pass

prefs = {
    "profile.default_content_setting_values.popups": 1,
    "profile.managed_default_content_settings.images": 2,
    "profile.managed_default_content_settings.geolocation": 2,
    "profile.managed_default_content_settings.notifications": 2,
    "profile.managed_default_content_settings.media_stream": 2,
}
chrome_options.add_experimental_option("prefs", prefs)

try:
    driver = uc.Chrome(options=chrome_options)
except Exception as e:
    print(f"❌ Nem sikerült elindítani a Chrome-ot: {e}")
    raise SystemExit(1)
uc.Chrome.__del__ = lambda self: None

# --- CDP gyorsítók / tiltások ---
try:
    driver.execute_cdp_cmd("Network.enable", {})
    driver.execute_cdp_cmd("Network.setBypassServiceWorker", {"bypass": True})
    driver.execute_cdp_cmd("Network.setBlockedURLs", {
        "urls": ["*.woff", "*.woff2", "*.ttf", "*.otf", "*.eot"]
    })
    try:
        driver.execute_cdp_cmd("Emulation.setEmulatedMedia", {
            "features": [{"name": "prefers-reduced-motion", "value": "reduce"}]
        })
    except Exception:
        pass

    log("🧱 Globális blokkolás aktív (fontok), SW bypass, reduced motion.")
except Exception as e:
    warn(f"⚠️ CDP init részben sikertelen: {e}")

try:
    driver.set_script_timeout(30)
except Exception:
    pass

# gyenge animációtiltás (CSS) – best-effort injektor
def _inject_disable_animations():
    try:
        driver.execute_script("""
        (function(){
          try{
            var st = document.getElementById('__noanim');
            if (st) return;
            st = document.createElement('style');
            st.id='__noanim';
            st.textContent='*{animation:none!important;transition:none!important;scroll-behavior:auto!important}';
            document.head && document.head.appendChild(st);
          }catch(e){}
        })();
        """)
    except Exception:
        pass

# ---------- SAFE SCRIPT HELPEREK ----------
def ensure_active_window():
    try:
        h = driver.current_window_handle
        if h in driver.window_handles:
            return True
    except Exception:
        pass
    try:
        handles = driver.window_handles
        if not handles:
            return False
        if 'MAIN_HANDLE' in globals() and MAIN_HANDLE and MAIN_HANDLE in handles:
            driver.switch_to.window(MAIN_HANDLE)
            return True
        driver.switch_to.window(handles[0])
        return True
    except Exception:
        return False

def _safe_execute_script(script, *args):
    for _ in range(2):
        try:
            if not ensure_active_window():
                raise NoSuchWindowException("No alive window to execute script")
            return driver.execute_script(script, *args)
        except NoSuchWindowException:
            time.sleep(0.05)
            continue
    if not ensure_active_window():
        raise NoSuchWindowException("No alive window after retries")
    return driver.execute_script(script, *args)

def _safe_execute_async_script(script, *args):
    for _ in range(2):
        try:
            if not ensure_active_window():
                raise NoSuchWindowException("No alive window to execute async script")
            return driver.execute_async_script(script, *args)
        except NoSuchWindowException:
            time.sleep(0.05)
            continue
    if not ensure_active_window():
        raise NoSuchWindowException("No alive window after retries (async)")
    return driver.execute_async_script(script, *args)

# ---------- URL utilok ----------
def is_http_url(u: str | None) -> bool:
    if not u: return False
    try:
        p = urlparse(u)
        return p.scheme in ("http", "https") and bool(p.netloc)
    except Exception:
        return False

def is_surebet_url(u: str | None) -> bool:
    if not u: return False
    try:
        host = urlparse(u).netloc.lower()
        return host.endswith("surebet.com")
    except Exception:
        return False

def is_nav_url(u: str | None) -> bool:
    if not u: return False
    try:
        p = urlparse(u)
        return p.netloc.lower().endswith("surebet.com") and p.path.startswith("/nav")
    except Exception:
        return False

def valid_external(u: str | None) -> bool:
    return is_http_url(u) and not is_surebet_url(u)

def _maybe_b64_decode(s: str) -> str | None:
    s2 = (s or "").strip()
    if not re.match(r'^[A-Za-z0-9+/=_-]{8,}$', s2):
        return None
    try:
        pad = '=' * (-len(s2) % 4)
        for variant in (s2, s2.replace('-', '+').replace('_', '/')):
            try:
                return base64.b64decode(variant + pad).decode('utf-8', errors='ignore')
            except Exception:
                continue
        return None
    except Exception:
        return None

def extract_target_from_nav(nav_url: str) -> str | None:
    try:
        p = urlparse(nav_url)
        q = parse_qs(p.query)
        keys = ["to","url","u","target","redirect","dest","link","r","q"]
        for k in keys:
            if k in q and q[k]:
                raw = q[k][0]
                cand = unquote(raw)
                if cand and cand.startswith(("http://","https://")):
                    return cand
                b = _maybe_b64_decode(raw)
                if b and b.startswith(("http://","https://")):
                    return b
                m = re.search(r'(https?://[^\s"\'<>]+)', cand)
                if m:
                    return m.group(1)
        return None
    except Exception:
        return None

# ---------- FAST FINAL szabályok (gyors elfogadás) ----------
def _sanitize_url(u: str | None) -> str | None:
    if not u:
        return None
    s = str(u).strip()
    s = re.sub(r'[,\.;\)\s]+$', '', s)
    return s

RX_BETWINNER = re.compile(r'^https?://(?:[\w-]+\.)?betwinner\.com(?:/[a-z]{2})?/line/[a-z]+(?:-[a-z]+)*/\d{2,9}-[a-z0-9-]+/\d{6,12}-[a-z0-9-]+/?(?:\?.*)?$', re.I)
RX_TIPPMIXPRO = re.compile(r'^https?://(?:www\.)?tippmixpro\.hu/hu/fogadas/i/esemenyek/\d+/[^/]+/[^/]+/[^/]+/\d{15,21}/(?:all|nepszeru)?/?$', re.I)
RX_BOABET = re.compile(r'^https?://sport\.ggiframe\.com/SportsBook/GameDetails\?gameId=\d+$', re.I)
RX_MOSTBET = re.compile(r'^https?://(?:[\w-]+\.)?mostbet\.com/line/\d+/?(?:\?lc=\d+)?$', re.I)
RX_CLOUDBET = re.compile(r'^https?://(?:www\.)?cloudbet\.com/[a-z]{2}/sports/[a-z-]+/[^/]+/\d+(?:\?.*)?$', re.I)
RX_WYLCAN = re.compile(r'^https?://(?:www\.)?wylcan-bet\.org/en/sports/[a-z-]+/match/[a-z0-9-]+\-\d{2}\-\d{2}(?:-\d{2})?$', re.I)
RX_GGBET = re.compile(r'^https?://(?:www\.)?gg\.bet/(?:sports|esports)/match/[a-z0-9-]+\-\d{2}\-\d{2}(?:-\d{2})?$', re.I)
RX_VALAMI_PREMATCH = re.compile(r'^https?://[^/]+/hu/prematch/football/\d{2,9}-[^/]+/\d{6,12}-[^/]+/?$', re.I)

# NEW: Parimatch events, BetInAsia Black, generic HU sports event
RX_PARIMATCH_EVENTS = re.compile(
    r'^https?://(?:[\w-]+\.)?parimatch\.[a-z.]+/.*/events/[a-z0-9-]+-\d{5,}(?:\?.*)?$', re.I)

RX_BIA_BLACK = re.compile(
    r'^https?://black\.betinasia\.com/sportsbook/[a-z]+/[A-Z]{2}/\d+/\d{4}-\d{2}-\d{2},\d+,\d+(?:\?.*)?$', re.I)

RX_GENERIC_HU_EVENT = re.compile(
    r'^https?://[^/]+/hu/sports/event/[a-z0-9-]+/\d+(?:\?.*)?$', re.I)

def _host(u: str) -> str:
    try:
        return urlparse(u).netloc.lower()
    except Exception:
        return ""

def _hash(u: str) -> str:
    try:
        return urlparse(u).fragment or ""
    except Exception:
        return ""

def _query_params(u: str) -> dict:
    try:
        return parse_qs(urlparse(u).query)
    except Exception:
        return {}

def _blaze_btpath_ok(u: str) -> bool:
    try:
        q = _query_params(u)
        p = q.get('bt-path', [])
        if not p:
            return False
        raw = p[0]
        dec = unquote(raw)
        if 'undefined' in dec.lower():
            return False
        if re.search(r'\d{10,}', dec):
            return True
        if re.search(r'-\d{10,}$', dec):
            return True
        return False
    except Exception:
        return False

def _vegas_ok(u: str) -> bool:
    if not _host(u).endswith("vegas.hu"):
        return False
    h = _hash(u)
    if "page=event" not in h:
        return False
    has_event = re.search(r'(?:^|[&#])eventId=\d+(?:[&#]|$)', h) is not None
    has_sport = re.search(r'(?:^|[&#])sportId=\d+(?:[&#]|$)', h) is not None
    return has_event and has_sport

def fast_final_match(u: str | None) -> str | None:
    s = _sanitize_url(u)
    if not s:
        return None
    if not valid_external(s):
        return None
    h = _host(s)

    if "betwinner.com" in h and RX_BETWINNER.match(s):
        return s
    if h.endswith("vegas.hu") and _vegas_ok(s):
        return s
    if "tippmixpro.hu" in h and RX_TIPPMIXPRO.match(s):
        return s
    if "blaze.com" in h and _blaze_btpath_ok(s):
        return s
    if "ggiframe.com" in h and RX_BOABET.match(s):
        return s
    if "mostbet.com" in h and RX_MOSTBET.match(s):
        return s
    if "cloudbet.com" in h and RX_CLOUDBET.match(s):
        return s
    if "wylcan-bet.org" in h and RX_WYLCAN.match(s):
        return s
    if "gg.bet" in h and RX_GGBET.match(s):
        return s
    if RX_VALAMI_PREMATCH.match(s):
        return s
    # NEW extras
    if "parimatch." in h and RX_PARIMATCH_EVENTS.match(s):
        return s
    if "betinasia.com" in h and RX_BIA_BLACK.match(s):
        return s
    if RX_GENERIC_HU_EVENT.match(s):
        return s

    return None

# ---------- kisegítő függvények ----------
def human_type(element, text: str):
    try:
        _safe_execute_script("arguments[0].focus();", element)
    except Exception:
        pass
    try:
        element.click()
    except Exception:
        pass
    try:
        element.send_keys(KEY_MOD, "a")
        element.send_keys(Keys.DELETE)
    except Exception:
        try:
            _safe_execute_script("arguments[0].value='';", element)
        except Exception:
            pass

    ok = False
    try:
        driver.execute_cdp_cmd("Input.insertText", {"text": text})
        ok = True
    except Exception:
        ok = False

    if not ok:
        try:
            element.send_keys(text)
            ok = True
        except Exception:
            ok = False

    try:
        cur = _safe_execute_script("return arguments[0].value;", element)
    except Exception:
        cur = None

    if cur != text:
        try:
            _safe_execute_script("""
                const el = arguments[0], val = arguments[1];
                const proto = Object.getPrototypeOf(el) || HTMLInputElement.prototype;
                const desc = Object.getOwnPropertyDescriptor(proto, 'value')
                           || Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value');
                if (desc && desc.set) desc.set.call(el, val);
                else el.value = val;
                el.dispatchEvent(new Event('input',  {bubbles:true}));
                el.dispatchEvent(new Event('change', {bubbles:true}));
            """, element, text)
        except Exception:
            pass

    time.sleep(0.05)

def get_bet_name(td):
    try:
        abbr = td.find_element(By.TAG_NAME, "abbr")
        val = abbr.get_attribute("data-bs-original-title") or abbr.get_attribute("title") or abbr.get_attribute("aria-label")
        if val:
            return val.strip()
    except:
        pass
    try:
        return td.text.strip() or "Ismeretlen szelvény"
    except:
        return "Ismeretlen szelvény"

def robust_event_text(tbody, attempts=3, sleep=0.06):
    for _ in range(attempts):
        try:
            els = tbody.find_elements(By.CSS_SELECTOR, "td[class^='event event-']")
            texts = []
            for e in els:
                try:
                    t = (e.text or "").strip()
                except StaleElementReferenceException:
                    t = ""
                except Exception:
                    t = ""
                if t:
                    texts.append(t)
            if texts:
                return max(texts, key=lambda t: len(t.strip())).strip()
            return ""
        except StaleElementReferenceException:
            time.sleep(sleep)
        except Exception:
            break
    return ""

def get_first_minor_text(tbody) -> str:
    try:
        minors = tbody.find_elements(By.CSS_SELECTOR, "span.minor")
        for el in minors:
            txt = (el.text or "").strip()
            if txt:
                return txt
    except Exception:
        pass
    return ""

def parse_float(text):
    if text is None:
        return None
    t = str(text).strip().replace(",", ".")
    m = re.search(r"-?\d+(?:\.\d+)?", t)
    try:
        return float(m.group(0)) if m else None
    except:
        return None

def to_float_or_none(val):
    v = parse_float(val)
    return v if v is not None else None

def canonical_bookmaker(name: str) -> str:
    if not name:
        return name
    # zárójeles kiegészítések levágása
    base = re.sub(r"\s*\([^)]*\)\s*", "", name).strip()
    base_norm = re.sub(r"\s+", " ", base).strip()

    alias = {
        "Vegas.hu": "Vegas",
        "Vegas": "Vegas",
        "BetInAsia (Black)": "BetInAsia",
        "BetInAsia Black": "BetInAsia",
        "BetInAsia": "BetInAsia",
        "Tippmix Pro": "Tippmixpro",
        "Tippmixpro": "Tippmixpro",
        "Boabet": "Boabet",
        "BetWinner": "Betwinner",
        "Betwinner": "Betwinner",
        "Rockyspin": "RockySpin",
        "RockySpin": "RockySpin",

        # KÉRT MÓDOSÍTÁS: Parimatch → Betmatch
        "Parimatch": "Betmatch",
        "PariMatch": "Betmatch",
        "Pari Match": "Betmatch",
        "PARIMATCH": "Betmatch",
    }
    return alias.get(base_norm, base_norm)

def normalize_match_start(s: str) -> str:
    if not s:
        return s
    s = s.replace(".", "/").strip()
    m = re.search(r"(\d{1,2})/(\d{1,2})\s+(\d{1,2}):(\d{2})", s)
    if m:
        d, mo, hh, mm = map(int, m.groups())
        year = datetime.now().year
        try:
            dt = datetime(year, mo, d, hh, mm)
            return dt.strftime("%Y-%m-%d %H:%M:%S")
        except ValueError:
            pass
    return s

def compute_profit_percent(odds1, odds2) -> str:
    try:
        o1 = float(odds1); o2 = float(odds2)
        s = 1.0/o1 + 1.0/o2
        val = max(0.0, (1.0 - s) * 100.0)
        return f"{val:.2f}%"
    except:
        return "0.00%"

def find_profit_percent(tbody):
    selectors = [
        "td.profit", "td[class*='profit']", "td.gain", "td.percent", "td.max_profit",
        ".profit", ".gain", ".percent"
    ]
    for sel in selectors:
        try:
            el = tbody.find_element(By.CSS_SELECTOR, sel)
            txt = el.text.strip()
            m = re.search(r"[-+]?\d+(?:[.,]\d+)?\s*%", txt)
            if m:
                return m.group(0).replace(",", ".")
        except:
            pass
    try:
        txt = tbody.text
        m = re.search(r"[-+]?\d+(?:[.,]\d+)?\s*%", txt)
        if m:
            return m.group(0).replace(",", ".")
    except:
        pass
    return None

def norm_odds(val):
    if val is None:
        return None
    try:
        return f"{float(val):.{UPDATE_DECIMALS}f}"
    except:
        v = parse_float(str(val))
        return f"{v:.{UPDATE_DECIMALS}f}" if v is not None else None

def norm_profit_str(s):
    if not s:
        return f"{0.0:.{UPDATE_DECIMALS}f}%"
    try:
        t = str(s).replace(",", ".")
        m = re.search(r"-?\d+(?:\.\d+)?", t)
        v = float(m.group(0)) if m else 0.0
        return f"{v:.{UPDATE_DECIMALS}f}%"
    except:
        return f"{0.0:.{UPDATE_DECIMALS}f}%"

def percent_to_float(s: str | None):
    if not s:
        return None
    try:
        m = re.search(r"-?\d+(?:\.\d+)?", s.replace(",", "."))
        return float(m.group(0)) if m else None
    except:
        return None

def iso_or_none(s: str | None):
    if not s:
        return None
    if re.match(r"^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}$", s):
        return s
    return None

def log_found_link(name, href, bet, odd):
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with open(FOUND_LINKS_FILE, "a", encoding="utf-8") as f:
        f.write(f"[{now}] {name} -> {href} | {bet} | {odd}\n")

# --- ÚJ: Cím-tisztító csak match/league mezőkre ---
def _clean_title(s: str | None) -> str | None:
    if s is None:
        return None
    t = str(s)
    t = re.sub(r"\[\d+\]", "", t)     # [123456] kidob
    t = t.replace(".", "")            # pontok törlése
    t = re.sub(r"\s+", " ", t).strip(" -—–\u2013\u2014").strip()
    return t or None

# --- HTTP helpers ---
def http_post(url: str, payload: dict, timeout=12) -> tuple[int, dict]:
    """
    Részletes JSON visszaadása + saját X-Correlation-Id header.
    A válaszban: {"message", "issues", "correlation_id", "__status__", ...}
    """
    try:
        corr_id = str(uuid.uuid4())
        headers = dict(HTTP_HEADERS)
        headers["X-Correlation-Id"] = corr_id

        r = requests.post(url, headers=headers, json=payload, timeout=timeout)

        try:
            data = r.json()
        except Exception:
            data = {"raw": r.text}

        data.setdefault("correlation_id",
                        r.headers.get("x-correlation-id") or data.get("correlation_id") or corr_id)
        data["__status__"] = r.status_code

        if DEBUG_HTTP:
            print(f"HTTP {r.status_code} {url} cid={data.get('correlation_id')}")
            try:
                print(json.dumps(data, ensure_ascii=False)[:1200])
            except Exception:
                print(str(data)[:1200])

        return r.status_code, data
    except Exception as e:
        return 0, {"error": "request_exception", "message": str(e)}

# ===================== ASZINKRON DISZPÉCSER + BATCH =====================
class AsyncHttpDispatcher:
    def __init__(self):
        self.q_save   = Queue(maxsize=10000)
        self.q_update = Queue(maxsize=10000)
        self.q_delete = Queue(maxsize=10000)
        self.result_q = Queue(maxsize=10000)

        self.UPDATE_BATCH_MAX = 50
        self.UPDATE_BATCH_FLUSH_SEC = 1.2

        self.DELETE_BATCH_MAX = 50
        self.DELETE_BATCH_FLUSH_SEC = 1.5

        self.HTTP_TIMEOUT = 12

        self._stop = threading.Event()
        self._thr = threading.Thread(target=self._run, daemon=True)
        self._thr.start()

    def stop(self):
        self._stop.set()
        self._thr.join(timeout=5)

    def get_results(self, max_items=200):
        items = []
        for _ in range(max_items):
            try:
                items.append(self.result_q.get_nowait())
            except Empty:
                break
        return items

    def enqueue_save(self, item: dict):
        try:
            self.q_save.put_nowait(item)
        except Exception:
            warn("⚠️ SAVE queue full, item dropped")

    def enqueue_update(self, payload: dict):
        try:
            self.q_update.put_nowait(payload)
        except Exception:
            warn("⚠️ UPDATE queue full, item dropped")

    def enqueue_delete(self, tip_id: str):
        try:
            self.q_delete.put_nowait(tip_id)
        except Exception:
            warn("⚠️ DELETE queue full, item dropped")

    def _run(self):
        upd_bucket = []
        upd_first_ts = None

        del_bucket = []
        del_first_ts = None

        while not self._stop.is_set():
            did_anything = False

            try:
                save_item = self.q_save.get_nowait()
                did_anything = True
                self._process_save_item(save_item)
            except Empty:
                pass

            now = time.time()
            try:
                while True:
                    upd_item = self.q_update.get_nowait()
                    upd_bucket.append(upd_item)
                    if upd_first_ts is None:
                        upd_first_ts = now
                    if len(upd_bucket) >= self.UPDATE_BATCH_MAX:
                        break
            except Empty:
                pass

            if upd_bucket:
                if (time.time() - (upd_first_ts or time.time())) >= self.UPDATE_BATCH_FLUSH_SEC or len(upd_bucket) >= self.UPDATE_BATCH_MAX:
                    self._flush_update_batch(upd_bucket)
                    upd_bucket = []
                    upd_first_ts = None
                    did_anything = True

            now = time.time()
            try:
                while True:
                    del_item = self.q_delete.get_nowait()
                    del_bucket.append(del_item)
                    if del_first_ts is None:
                        del_first_ts = now
                    if len(del_bucket) >= self.DELETE_BATCH_MAX:
                        break
            except Empty:
                pass

            if del_bucket:
                if (time.time() - (del_first_ts or time.time())) >= self.DELETE_BATCH_FLUSH_SEC or len(del_bucket) >= self.DELETE_BATCH_MAX:
                    self._flush_delete_batch(del_bucket)
                    del_bucket = []
                    del_first_ts = None
                    did_anything = True

            if not did_anything:
                time.sleep(0.02)

        if upd_bucket:
            self._flush_update_batch(upd_bucket)
        if del_bucket:
            self._flush_delete_batch(del_bucket)

        try:
            while True:
                save_item = self.q_save.get_nowait()
                self._process_save_item(save_item)
        except Empty:
            pass

    def _process_save_item(self, it: dict):
        tip_payload = it.get("tip_payload", {})
        status, data = http_post(SAVE_TIP_URL, tip_payload, timeout=self.HTTP_TIMEOUT)

        # siker csak akkor, ha 2xx ÉS ok:true
        ok = (200 <= status < 300) and isinstance(data, dict) and (data.get("ok") is True)

        if ok:
            self.result_q.put({
                "type": "save_ok",
                "id": tip_payload.get("id"),
                "state_info": it.get("state_info"),
                "finals": it.get("finals"),
                "resp": data,
            })
            return

        # duplikáció kezelése
        low = json.dumps(data, ensure_ascii=False).lower() if isinstance(data, dict) else str(data).lower()
        if status == 409 or any(k in low for k in ["duplicate", "unique", "already exists", "conflict"]):
            upd_payload = it.get("update_payload")
            if upd_payload:
                s2, d2 = http_post(UPDATE_TIP_URL, upd_payload, timeout=self.HTTP_TIMEOUT)
                if (200 <= s2 < 300) and isinstance(d2, dict) and d2.get("ok") is True:
                    self.result_q.put({
                        "type": "save_dup_updated",
                        "id": tip_payload.get("id"),
                        "state_info": it.get("state_info"),
                        "finals": it.get("finals"),
                        "update_payload": upd_payload,
                        "resp": d2,
                    })
                    return
                else:
                    self.result_q.put({
                        "type": "save_dup_update_fail",
                        "id": tip_payload.get("id"),
                        "status": s2,
                        "error": d2,
                    })
                    return
            else:
                self.result_q.put({
                    "type": "save_duplicate",
                    "id": tip_payload.get("id"),
                    "state_info": it.get("state_info"),
                    "finals": it.get("finals"),
                    "resp": data,
                })
                return

        # minden más hiba
        self.result_q.put({
            "type": "save_error",
            "id": tip_payload.get("id"),
            "status": status,
            "error": data
        })

    def _flush_update_batch(self, items: list[dict]):
        try:
            payload = {"items": items}
            status, data = http_post(UPDATE_TIPS_BATCH_URL, payload, timeout=self.HTTP_TIMEOUT)
            if (200 <= status < 300) and isinstance(data, dict) and data.get("ok") is True:
                for it in items:
                    self.result_q.put({"type": "update_ok", "id": it.get("id"), "payload": it, "resp": data})
                return
        except Exception:
            pass
        for it in items:
            s, d = http_post(UPDATE_TIP_URL, it, timeout=self.HTTP_TIMEOUT)
            if (200 <= s < 300) and isinstance(d, dict) and d.get("ok") is True:
                self.result_q.put({"type": "update_ok", "id": it.get("id"), "payload": it, "resp": d})
            else:
                self.result_q.put({"type": "update_error", "id": it.get("id"), "status": s, "error": d, "payload": it})

    def _flush_delete_batch(self, ids: list[str]):
        uniq_ids = list(dict.fromkeys(ids))
        try:
            payload = {"ids": uniq_ids}
            status, data = http_post(DELETE_TIPS_BATCH_URL, payload, timeout=self.HTTP_TIMEOUT)
            if (200 <= status < 300) and isinstance(data, dict) and data.get("ok") is True:
                for tid in uniq_ids:
                    self.result_q.put({"type": "delete_ok", "id": tid, "resp": data})
                return
        except Exception:
            pass
        for tid in uniq_ids:
            s, d = http_post(DELETE_TIP_URL, {"type": "gone", "id": tid}, timeout=self.HTTP_TIMEOUT)
            if (200 <= s < 300) and isinstance(d, dict) and d.get("ok") is True:
                self.result_q.put({"type": "delete_ok", "id": tid, "resp": d})
            else:
                self.result_q.put({"type": "delete_error", "id": tid, "status": s, "error": d})

dispatcher = AsyncHttpDispatcher()

# ---------- stale-biztos DOM snapshot ----------
def dom_snapshot_by_id(tbody_id: str, attempts=4, sleep=0.08):
    js = r"""
    const id = arguments[0];
    function snap(id){
      const sel1 = 'tbody.surebet_record[data-id="'+id+'"]';
      const sel2 = 'tbody.surebet_record[dataid="'+id+'"]';
      const row = document.querySelector(sel1) || document.querySelector(sel2);
      if (!row) return null;

      const getTxt = el => el ? (el.textContent || '').trim() : '';
      const q = (r, s) => r ? r.querySelector(s) : null;
      const qa = (r, s) => r ? Array.from(r.querySelectorAll(s)) : [];

      const values = qa(row, "td.value[class*='odd_record_']");
      const coeffs = qa(row, "td.coeff");

      const a1 = values[0] ? q(values[0], 'a') : null;
      const a2 = values[1] ? q(values[1], 'a') : null;

      const href1 = a1 ? a1.href : null;
      const href2 = a2 ? a2.href : null;

      const odds1_text = getTxt(values[0] || null);
      const odds2_text = getTxt(values[1] || null);

      const getBet = (cell) => {
        const ab = cell ? (cell.querySelector('abbr,[data-bs-original-title],[title],[aria-label]')) : null;
        const cands = [
          ab ? (ab.getAttribute('data-bs-original-title')||'') : '',
          ab ? (ab.getAttribute('title')||'') : '',
          ab ? (ab.getAttribute('aria-label')||'') : '',
          getTxt(cell || null)
        ].map(s => (s||'').trim()).filter(Boolean);
        return cands[0] || 'Ismeretlen szelvény';
      };

      const bet1 = getBet(coeffs[0] || null);
      const bet2 = getBet(coeffs[1] || null);

      // Bookmaker nevek (max 2)
      const bookers = qa(row, "td.booker a").map(a => getTxt(a)).filter(Boolean).slice(0,2);

      // EVENT cellák
      const evTds = qa(row, "td[class^='event event-']");
      const evAnchors = evTds
        .map(td => q(td, "a[target='_blank']"))
        .filter(Boolean)
        .map(a => getTxt(a))
        .filter(Boolean);

      // Két anchor is lehet – a rövidebbik kell
      let event_anchor_text = "";
      if (evAnchors.length === 1) {
        event_anchor_text = evAnchors[0];
      } else if (evAnchors.length >= 2) {
        event_anchor_text = evAnchors.sort((a,b) => a.length - b.length)[0];
      }

      // League a td.event... alatti span.minor-ból, ha kettő van -> rövidebbik kell
      const evMinors = evTds
        .map(td => getTxt(q(td, 'span.minor')))
        .filter(Boolean);

      let league_minor = "";
      if (evMinors.length === 1) {
        league_minor = evMinors[0];
      } else if (evMinors.length >= 2) {
        league_minor = evMinors.sort((a,b) => a.length - b.length)[0];
      }

      // sport_minor: meghagyjuk, ha kell később
      const minorsAll = qa(row, "span.minor").map(el => getTxt(el)).filter(Boolean);
      const sport_minor = minorsAll.length ? minorsAll[0] : "";

      // Profit szöveg
      const sels = ['td.profit','td[class*="profit"]','td.gain','td.percent','td.max_profit','.profit','.gain','.percent'];
      let profit = '';
      for (const s of sels) {
         const el = q(row, s);
         const t = getTxt(el);
         if (t) { profit = t; break; }
      }

      // Kezdési idő HTML (abbr)
      const timeabbr = q(row, "td.time abbr");
      const time_html = timeabbr ? (timeabbr.innerHTML || "") : "";

      return {
        href1, href2,
        odds1_text, odds2_text,
        bet1, bet2,
        bookers,
        league_minor,
        sport_minor,
        time_html,
        profit_text: profit,
        event_anchor_text
      };
    }
    return snap(arguments[0]);
    """
    for _ in range(attempts):
        try:
            data = driver.execute_script(js, tbody_id)
            if data:
                return data
        except StaleElementReferenceException:
            pass
        except Exception:
            pass
        time.sleep(sleep)
    return None

# ---------- stale-biztos SAVE előkészítés + batch ----------
def prepare_new_task_for_id(tbody_id):
    snap = dom_snapshot_by_id(tbody_id)
    if not snap:
        return None

    href1 = snap.get("href1")
    href2 = snap.get("href2")

    # match_name az anchor rövidebbik változata
    match_name_raw = (snap.get("event_anchor_text") or "").strip()
    match_name = _clean_title(match_name_raw) or "Ismeretlen meccs"

    # league_name a td.event alatti rövidebbik span.minor
    league_minor = (snap.get("league_minor") or "").strip()
    league_name = _clean_title(league_minor) or ""

    sport_name = (snap.get("sport_minor") or "").strip()

    names_raw = (snap.get("bookers") or [])[:2]
    if len(names_raw) < 2:
        return None
    names = [canonical_bookmaker(n) for n in names_raw]

    odds1_text = (snap.get("odds1_text") or "").strip()
    odds2_text = (snap.get("odds2_text") or "").strip()
    odds1 = to_float_or_none(odds1_text)
    odds2 = to_float_or_none(odds2_text)

    bet1 = (snap.get("bet1") or "").strip() or "Ismeretlen szelvény"
    bet2 = (snap.get("bet2") or "").strip() or "Ismeretlen szelvény"

    profit_dom = (snap.get("profit_text") or "").strip()
    if profit_dom:
        profit_percent = profit_dom
    else:
        if odds1 is not None and odds2 is not None:
            profit_percent = compute_profit_percent(odds1, odds2)
        else:
            profit_percent = "0.00%"

    time_html = snap.get("time_html") or ""
    parts = [p.strip() for p in time_html.replace("<br>", "\n").split("\n") if p.strip()]
    if len(parts) >= 2:
        match_start_raw = f"{parts[0]} {parts[1]}"
    else:
        match_start_raw = (time_html.strip() or "Ismeretlen időpont")
    match_start = normalize_match_start(match_start_raw)
    profit_text = norm_profit_str(profit_percent)

    task = {
        "id": tbody_id,
        "names": names,
        "bets": (bet1, bet2),
        "odds": (odds1 if odds1 is not None else to_float_or_none(odds1_text),
                 odds2 if odds2 is not None else to_float_or_none(odds2_text)),
        "profit_text": profit_text,
        "match_name": match_name,
        "league_name": league_name,
        "sport_name": sport_name,
        "match_start_iso": iso_or_none(match_start),
        "hrefs": (href1, href2),
        "finals": None,
    }

    if tbody_id in link_cache:
        l1 = link_cache[tbody_id].get("link1")
        l2 = link_cache[tbody_id].get("link2")
        if valid_external(l1) and valid_external(l2):
            task["finals"] = (l1, l2)

    return task

def _build_tip_payload_from_task(task):
    tbody_id = task["id"]
    names = task["names"]
    bet1, bet2 = task["bets"]
    odds1, odds2 = task["odds"]
    profit_text = task["profit_text"]

    # Tisztítás csak a cím mezőknél
    match_name = _clean_title(task["match_name"])
    league_name = _clean_title(task["league_name"])

    sport_name = task["sport_name"]
    match_start_iso = task["match_start_iso"]
    final_href1, final_href2 = task.get("finals") or (None, None)

    tip_payload = {
        "id": tbody_id,
        "bookmaker1": names[0],
        "bookmaker2": names[1],
        "profit_percent": profit_text,
        "profit_percent_num": percent_to_float(profit_text),
        "match_name": match_name,
        "league_name": league_name,
        "option1": bet1,
        "option2": bet2,
        "match_start": match_start_iso,
        "link1": final_href1,
        "link2": final_href2,
        "odds1": odds1,
        "odds2": odds2,
        "sport": sport_name,
    }
    return tip_payload

def _build_update_payload_from_task(task):
    tbody_id = task["id"]
    odds1, odds2 = task["odds"]
    profit_text = task["profit_text"]
    return {
        "type": "update",
        "id": tbody_id,
        "odds1": norm_odds(odds1),
        "odds2": norm_odds(odds2),
        "profit_percent": norm_profit_str(profit_text),
        "updated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    }

# ---------- NAV backoff ----------
nav_retry_attempts = {}   # id -> int
nav_retry_until    = {}   # id -> epoch

nav_backoff_consecutive = 0

def force_main_refresh(reason: str = ""):
    """MAIN tab kemény frissítés + autoupdate biztosítása."""
    global main_refresh_enabled, main_last_refresh, main_next_refresh
    try:
        if MAIN_HANDLE and MAIN_HANDLE in driver.window_handles:
            driver.switch_to.window(MAIN_HANDLE)
        driver.refresh()
        _inject_disable_animations()
        _wait_main_container(timeout=12)
        ensure_main_autoupdate()
        log(f"🔁 MAIN forced refresh {f'({reason})' if reason else ''}")
    except Exception as e:
        warn(f"⚠️ MAIN forced refresh failed: {e}")

def _schedule_nav_backoff(tid: str):
    global nav_backoff_consecutive
    att = nav_retry_attempts.get(tid, 0) + 1
    nav_retry_attempts[tid] = att
    delay = min(NAV_RETRY_BASE * (2 ** (att - 1)), NAV_RETRY_MAX)
    nav_retry_until[tid] = time.time() + delay

    nav_backoff_consecutive += 1
    warn(f"⏳ NAV backoff id={tid} {int(delay)}s (attempt={att})")

    if nav_backoff_consecutive >= 10:
        force_main_refresh("10 consecutive NAV backoffs")
        nav_backoff_consecutive = 0

def _clear_nav_backoff(tid: str):
    global nav_backoff_consecutive
    nav_retry_attempts.pop(tid, None)
    nav_retry_until.pop(tid, None)
    nav_backoff_consecutive = 0

# ---------- HANDLE → FINAL URL feloldás ----------
def _finalize_url_for_handle(handle, opened_at_ts) -> str | None:
    deadline = time.time() + RESOLVE_TIMEOUT
    stable_seen = None
    last_url = None

    while True:
        if handle not in driver.window_handles:
            return None
        driver.switch_to.window(handle)
        try:
            cur = driver.current_url
        except Exception:
            cur = "about:blank"

        _inject_disable_animations()

        now = time.time()
        if cur and cur != "about:blank" and not is_nav_url(cur):
            if valid_external(cur):
                fast_ok = fast_final_match(cur)
                if fast_ok:
                    if last_url != cur:
                        last_url = cur
                        stable_seen = now
                    else:
                        if stable_seen and (now - stable_seen) >= FAST_FINAL_STABLE_PERIOD:
                            return fast_ok
                else:
                    if last_url != cur:
                        last_url = cur
                        stable_seen = now
                    else:
                        if stable_seen and (now - stable_seen) >= RESOLVE_STABLE_PERIOD:
                            return cur
        elif is_nav_url(cur):
            total_timeout = RESOLVE_TIMEOUT_NAV
            if (now - opened_at_ts) < NAV_MIN_WAIT:
                time.sleep(RESOLVE_POLL_INTERVAL)
            else:
                tgt = extract_target_from_nav(cur)
                if valid_external(tgt):
                    fast_ok = fast_final_match(tgt)
                    wait_after = FAST_FINAL_STABLE_PERIOD if fast_ok else NAV_STABLE_AFTER_EXIT
                    stable_start = time.time()
                    while time.time() - stable_start < wait_after and handle in driver.window_handles:
                        time.sleep(RESOLVE_POLL_INTERVAL)
                    return tgt
            deadline = max(deadline, opened_at_ts + total_timeout)

        if now >= deadline:
            return None
        time.sleep(RESOLVE_POLL_INTERVAL)

def _open_window_tagged(url: str, tag: str, delay_ms: int):
    js = f"""
        (function(){{
            var go = function(u,t,delay){{
                var w = window.open('about:blank','_blank');
                if (!w) return;
                try {{ w.name = t; }} catch(e) {{}}
                setTimeout(function() {{
                    try {{ w.location.href = u; }} catch(e) {{}}
                }}, delay);
            }};
            go({json.dumps(url)}, {json.dumps(tag)}, {int(delay_ms)});
        }})();
    """
    _safe_execute_script(js)

def resolve_pairs_staggered(pairs, timeout=RESOLVE_TIMEOUT, stable_period=RESOLVE_STABLE_PERIOD, poll_interval=RESOLVE_POLL_INTERVAL):
    pre_finals = {}
    normalized_pairs = []
    for i, p in enumerate(pairs):
        if not p:
            normalized_pairs.append((None, None))
            continue
        a, b = p
        fa = fast_final_match(a)
        fb = fast_final_match(b)
        if fa and fb:
            pre_finals[i] = (fa, fb)
            normalized_pairs.append((None, None))
        else:
            normalized_pairs.append((a, b))

    results = []
    for p in normalized_pairs:
        if not p:
            results.append((None, None))
        else:
            a, b = p
            results.append((a, b))

    def _guid():
        return f"{int(time.time()*1000)}{random.randint(100,999)}"

    taginfo = []
    need_open = []
    for i, (h1, h2) in enumerate(results):
        ok = bool(h1 and h2)
        need_open.append(ok)
        if ok:
            tag1 = f"SB|{_guid()}|1|{i}"
            tag2 = f"SB|{_guid()}|2|{i}"
            taginfo.append({"pair_index": i, "tag1": tag1, "tag2": tag2})
        else:
            taginfo.append({"pair_index": i, "tag1": None, "tag2": None})

    try:
        ensure_active_window()
        prev = set(driver.window_handles)
        now_ts = time.time()

        if len(results) >= 1 and need_open[0]:
            _open_window_tagged(results[0][0], taginfo[0]["tag1"], 0)
            _open_window_tagged(results[0][1], taginfo[0]["tag2"], 80)
        if len(results) >= 2 and need_open[1]:
            _open_window_tagged(results[1][0], taginfo[1]["tag1"], 180)
            _open_window_tagged(results[1][1], taginfo[1]["tag2"], 260)

        target_count = (2 if need_open[0] else 0) + (2 if (len(results) >= 2 and need_open[1]) else 0)
        created = []
        deadline = time.time() + HANDLE_WAIT_TIMEOUT
        while time.time() < deadline and len(created) < target_count:
            try:
                now_handles = driver.window_handles
            except Exception:
                now_handles = []
            newh = list(set(now_handles) - prev)
            if len(newh) >= target_count:
                created = newh[:target_count]
                break
            time.sleep(0.05)

        handle_tag = {}
        for h in created:
            try:
                if h not in driver.window_handles:
                    continue
                driver.switch_to.window(h)
                name = _safe_execute_script("return window.name || ''") or ""
            except Exception:
                name = ""
            handle_tag[h] = name

        finals_by_pair = {i: [None, None] for i in range(len(results))}

        for k, v in pre_finals.items():
            finals_by_pair[k] = [v[0], v[1]]

        for h in created:
            tag = handle_tag.get(h, "")
            open_ts = now_ts
            final = _finalize_url_for_handle(h, open_ts)
            m = re.match(r'^SB\|.+\|(1|2)\|(\d+)$', tag)
            if m:
                pos = int(m.group(1))
                pidx = int(m.group(2))
                if 0 <= pidx < len(results):
                    finals_by_pair[pidx][pos-1] = final

        out = []
        for i in range(len(results)):
            out.append(tuple(finals_by_pair[i]))
        return out

    finally:
        try:
            cur = set(driver.window_handles)
            try:
                created_list = list(cur - prev) if 'prev' in locals() else []
            except Exception:
                created_list = []
            for h in created_list:
                try:
                    if h in driver.window_handles:
                        driver.switch_to.window(h)
                        driver.close()
                except Exception:
                    pass
            try:
                if MAIN_HANDLE and MAIN_HANDLE in driver.window_handles:
                    driver.switch_to.window(MAIN_HANDLE)
            except Exception:
                pass
        except Exception:
            pass

def resolve_two_final_urls(href1, href2,
                           timeout=RESOLVE_TIMEOUT,
                           stable_period=RESOLVE_STABLE_PERIOD,
                           poll_interval=RESOLVE_POLL_INTERVAL):
    if not (href1 and href2):
        return (None, None)

    f1 = fast_final_match(href1)
    f2 = fast_final_match(href2)
    if f1 and f2:
        return (f1, f2)

    try:
        original = driver.current_window_handle
    except Exception:
        original = None

    tag1 = f"SB|{int(time.time()*1000)}{random.randint(100,999)}|1|0"
    tag2 = f"SB|{int(time.time()*1000)}{random.randint(100,999)}|2|0"

    try:
        ensure_active_window()
        prev = set(driver.window_handles)
        now_ts = time.time()

        _open_window_tagged(href1, tag1, 0)
        _open_window_tagged(href2, tag2, 80)

        target_count = 2
        created = []
        deadline = time.time() + HANDLE_WAIT_TIMEOUT
        while time.time() < deadline and len(created) < target_count:
            try:
                now_handles = driver.window_handles
            except Exception:
                now_handles = []
            newh = list(set(now_handles) - prev)
            if len(newh) >= target_count:
                created = newh[:target_count]
                break
            time.sleep(0.05)

        final1 = None
        final2 = None
        for h in created:
            try:
                if h not in driver.window_handles:
                    continue
                driver.switch_to.window(h)
                name = _safe_execute_script("return window.name || ''") or ""
            except Exception:
                name = ""
            final = _finalize_url_for_handle(h, now_ts)
            if name.startswith("SB") and "|1|" in name:
                final1 = final
            elif name.startswith("SB") and "|2|" in name:
                final2 = final

        return (final1, final2)

    finally:
        try:
            cur = set(driver.window_handles)
            try:
                created_list = list(cur - prev) if 'prev' in locals() else []
            except Exception:
                created_list = []
            for h in created_list:
                try:
                    if h in driver.window_handles:
                        driver.switch_to.window(h)
                        driver.close()
                except Exception:
                    pass
        except Exception:
            pass
        try:
            if original and original in driver.window_handles:
                driver.switch_to.window(original)
        except Exception:
            pass

def batch_save_new_ids(new_ids: list, higher_ids: set | None = None):
    if not new_ids:
        return

    now = time.time()
    tasks = []
    for tid in new_ids:
        if tid in seen:
            continue
        if higher_ids and tid in higher_ids:
            continue
        until = nav_retry_until.get(tid, 0)
        if until and now < until:
            continue
        t = prepare_new_task_for_id(tid)
        if t:
            tasks.append(t)
    if not tasks:
        return

    for t in tasks:
        h1, h2 = t.get("hrefs") or (None, None)
        f1 = fast_final_match(h1)
        f2 = fast_final_match(h2)
        if f1 and f2:
            t["finals"] = (f1, f2)

    immediate = []
    queue = []
    for t in tasks:
        finals = t.get("finals")
        if finals and valid_external(finals[0]) and valid_external(finals[1]):
            immediate.append(t)
        else:
            queue.append(t)

    for t in immediate:
        tip_payload = _build_tip_payload_from_task(t)
        update_payload = _build_update_payload_from_task(t)
        dispatcher.enqueue_save({
            "id": t["id"],
            "tip_payload": tip_payload,
            "update_payload": update_payload,
            "state_info": {
                "odds1": tip_payload["odds1"],
                "odds2": tip_payload["odds2"],
                "profit_percent": tip_payload["profit_percent"],
            },
            "finals": t.get("finals"),
        })
        _clear_nav_backoff(t["id"])

    i = 0
    while i < len(queue):
        t1 = queue[i]
        pair1 = t1["hrefs"]

        t2 = queue[i+1] if (i+1) < len(queue) else None
        pair2 = t2["hrefs"] if t2 else None

        pairs = []
        if pair1 and pair1[0] and pair1[1]:
            pairs.append(pair1)
        else:
            pairs.append(None)
        if t2:
            if pair2 and pair2[0] and pair2[1]:
                pairs.append(pair2)
            else:
                pairs.append(None)

        finals = resolve_pairs_staggered(pairs) if any(pairs) else [(None, None)] * len(pairs)

        if pairs[0] is not None:
            t1["finals"] = finals[0]
        else:
            h1,h2 = pair1 if pair1 else (None,None)
            t1["finals"] = resolve_two_final_urls(h1,h2) if (h1 and h2) else (h1,h2)

        f1a, f1b = t1["finals"]
        ok1 = valid_external(f1a) and valid_external(f1b)
        if ok1:
            tip_payload1 = _build_tip_payload_from_task(t1)
            update_payload1 = _build_update_payload_from_task(t1)
            dispatcher.enqueue_save({
                "id": t1["id"],
                "tip_payload": tip_payload1,
                "update_payload": update_payload1,
                "state_info": {
                    "odds1": tip_payload1["odds1"],
                    "odds2": tip_payload1["odds2"],
                    "profit_percent": tip_payload1["profit_percent"],
                },
                "finals": t1.get("finals"),
            })
            link_cache[t1["id"]] = {"link1": f1a, "link2": f1b, "saved_at": datetime.now().isoformat()}
            _clear_nav_backoff(t1["id"])
        else:
            _schedule_nav_backoff(t1["id"])

        if t2:
            if len(finals) >= 2 and pairs[1] is not None:
                t2["finals"] = finals[1]
            else:
                h1,h2 = pair2 if pair2 else (None,None)
                t2["finals"] = resolve_two_final_urls(h1, h2) if (h1 and h2) else (h1, h2)

            f2a, f2b = t2["finals"]
            ok2 = valid_external(f2a) and valid_external(f2b)
            if ok2:
                tip_payload2 = _build_tip_payload_from_task(t2)
                update_payload2 = _build_update_payload_from_task(t2)
                dispatcher.enqueue_save({
                    "id": t2["id"],
                    "tip_payload": tip_payload2,
                    "update_payload": update_payload2,
                    "state_info": {
                        "odds1": tip_payload2["odds1"],
                        "odds2": tip_payload2["odds2"],
                        "profit_percent": tip_payload2["profit_percent"],
                    },
                    "finals": t2.get("finals"),
                })
                link_cache[t2["id"]] = {"link1": f2a, "link2": f2b, "saved_at": datetime.now().isoformat()}
                _clear_nav_backoff(t2["id"])
            else:
                _schedule_nav_backoff(t2["id"])

        save_link_cache(link_cache)
        i += 2

# ---------- UPDATE PATH ----------
def snapshot_update_values_by_id(tbody_id: str):
    js = r"""
    const id = arguments[0];
    const sel1 = 'tbody.surebet_record[data-id="'+id+'"]';
    const sel2 = 'tbody.surebet_record[dataid="'+id+'"]';
    const row = document.querySelector(sel1) || document.querySelector(sel2);
    if (!row) return null;
    const getTxt = (el) => el ? (el.textContent || '').trim() : '';
    const oddsCells = Array.from(row.querySelectorAll('td.value[class*="odd_record_"]'));
    const odds1 = getTxt(oddsCells[0]);
    const odds2 = getTxt(oddsCells[1]);
    const sels = ['td.profit','td[class*="profit"]','td.gain','td.percent','td.max_profit','.profit','.gain','.percent'];
    let profit = '';
    for (const s of sels) {
      const el = row.querySelector(s);
      const t = getTxt(el);
      if (t) { profit = t; break; }
    }
    return {odds1, odds2, profit};
    """
    try:
        return driver.execute_script(js, tbody_id)
    except Exception:
        return None

def handle_update_for_id(tbody_id):
    try:
        snap = snapshot_update_values_by_id(tbody_id)
        if not snap:
            return
        odds1_text = (snap.get("odds1") or "").strip()
        odds2_text = (snap.get("odds2") or "").strip()
        o1 = parse_float(odds1_text)
        o2 = parse_float(odds2_text)
        profit_dom = (snap.get("profit") or "").strip()
        if profit_dom:
            profit_now = norm_profit_str(profit_dom)
        else:
            if o1 is not None and o2 is not None:
                profit_now = norm_profit_str(compute_profit_percent(o1, o2))
            else:
                profit_now = norm_profit_str("0%")
        o1n = norm_odds(o1 if o1 is not None else odds1_text)
        o2n = norm_odds(o2 if o2 is not None else odds2_text)

        if tbody_id not in last_sent_state:
            last_sent_state[tbody_id] = {"odds1": o1n, "odds2": o2n, "profit_percent": profit_now}
            return

        prev = last_sent_state[tbody_id]
        changed = (o1n != prev.get("odds1")) or (o2n != prev.get("odds2")) or (profit_now != prev.get("profit_percent"))
        can_send = (time.time() - last_update_attempt_ts.get(tbody_id, 0)) >= UPDATE_MIN_INTERVAL

        if changed and can_send:
            payload = {
                "type": "update",
                "id": tbody_id,
                "odds1": o1n,
                "odds2": o2n,
                "profit_percent": profit_now,
                "updated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            }
            dispatcher.enqueue_update(payload)
            last_update_attempt_ts[tbody_id] = time.time()
    except Exception:
        return

# ---------- TAB REGISZTEREK ----------
group_tabs = {}
group_blocked_until = {}
next_tabs  = {}

id_source = {}
last_seen_ts = {}

# ---------- GROUP helpers ----------
def is_group_blocked(url, now_ts):
    return now_ts < group_blocked_until.get(url, 0)

def block_group_url(url, seconds, reason=""):
    group_blocked_until[url] = time.time() + seconds
    log(f"⛔ GROUP tiltólista {seconds}s: {url} ({reason})")

def close_group_tab(url):
    info = group_tabs.get(url)
    if not info:
        return
    try:
        handle = info["handle"]
        if handle in driver.window_handles:
            driver.switch_to.window(handle)
            driver.close()
    except Exception:
        pass
    finally:
        group_tabs.pop(url, None)
        try:
            if driver.window_handles:
                driver.switch_to.window(driver.window_handles[0])
        except Exception:
            pass

def find_group_link_in_tbody(tbody):
    try:
        a = tbody.find_element(By.CSS_SELECTOR, "a.group-link")
        href = a.get_attribute("href")
        if not href:
            return None
        cur = urlparse(driver.current_url)
        base = f"{cur.scheme}://{cur.netloc}"
        return urljoin(base, href)
    except Exception:
        return None

def _rand_group_refresh_interval():
    return random.uniform(GROUP_REFRESH_MIN, GROUP_REFRESH_MAX)

def open_group_tab_if_needed(group_url):
    now_ts = time.time()
    if group_url in group_tabs:
        if LOG_GROUP_ALREADY_OPEN_VERBOSE:
            log(f"ℹ️ Group már nyitva, nem nyitjuk újra: {group_url}")
        return
    if is_group_blocked(group_url, now_ts):
        log(f"⏳ Group URL tiltva még: {group_url}")
        return

    try:
        original = driver.current_window_handle
    except Exception:
        original = None

    try:
        driver.switch_to.new_window('tab')
        driver.get(group_url)
        _inject_disable_animations()
        handle = driver.current_window_handle

        WebDriverWait(driver, 8).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
        )
        tb_count = len(driver.find_elements(By.CSS_SELECTOR, GROUP_SELECTOR))
        if tb_count <= GROUP_EMPTY_CLOSE_TB_THRESHOLD:
            try:
                driver.close()
            except Exception:
                pass
            if original and original in driver.window_handles:
                driver.switch_to.window(original)
            block_group_url(group_url, GROUP_REOPEN_BACKOFF_SEC, "empty-at-open")
            return

        now = time.time()
        group_tabs[group_url] = {
            "handle": handle,
            "active_ids": set(),
            "created_at": now,
            "last_refresh": now,
            "next_refresh": now + _rand_group_refresh_interval(),
            "needs_scan": True,
        }
        if original and original in driver.window_handles:
            driver.switch_to.window(original)
        log(f"🆕 Group tab nyitva: {group_url}")
        return
    except Exception as e:
        warn(f"⚠️ Group nyitás hiba: {e}")
        block_group_url(group_url, GROUP_ERR_BACKOFF_SEC, "open-fail")
        try:
            if original and original in driver.window_handles:
                driver.switch_to.window(original)
        except Exception:
            pass

def maybe_refresh_group_tab(url: str, info: dict) -> bool:
    now = time.time()
    if now - info.get("created_at", now) < GROUP_REFRESH_SKIP_ON_NEW_SEC:
        info["next_refresh"] = now + _rand_group_refresh_interval()
        return False
    if now < info.get("next_refresh", 0):
        return False

    ok = False
    try:
        result = _safe_execute_async_script(r"""
            var callback = arguments[0];
            try {
                var sc = document.querySelector('div.table-container.product-table-container');
                if (!sc) { callback({ok:false, err:'container-not-found'}); return; }
                fetch(window.location.href, {cache:'no-store'})
                  .then(r => { if (!r.ok) throw new Error('http-'+r.status); return r.text(); })
                  .then(html => {
                      var parser = new DOMParser();
                      var doc = parser.parseFromString(html, 'text/html');
                      var newSc = doc.querySelector('div.table-container.product-table-container');
                      if (!newSc) { callback({ok:false, err:'new-container-not-found'}); return; }
                      var y = window.scrollY;
                      sc.innerHTML = newSc.innerHTML;
                      window.scrollTo(0, y);
                      callback({ok:true});
                  })
                  .catch(e => callback({ok:false, err:String(e)}));
            } catch(e) { callback({ok:false, err:String(e)}); }
        """)
        ok = bool(result and result.get("ok"))
    except Exception as e:
        warn(f"⚠️ Group részleges refresh hiba: {e}")
        ok = False

    if not ok:
        try:
            driver.refresh()
            _inject_disable_animations()
            WebDriverWait(driver, 8).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
            )
            ok = True
        except Exception as e:
            warn(f"⚠️ Group teljes reload hiba: {e}")
            ok = False

    info["last_refresh"] = now
    info["next_refresh"] = now + _rand_group_refresh_interval()
    if ok:
        info["needs_scan"] = True
    return ok

# ---------- NEXT helpers ----------
def _rand_next_refresh_interval():
    return random.uniform(NEXT_REFRESH_MIN, NEXT_REFRESH_MAX)

def find_next_page_link():
    try:
        a = driver.find_element(By.CSS_SELECTOR, "a.next_page")
        href = a.get_attribute("href")
        if not href:
            return None
        cur = urlparse(driver.current_url)
        base = f"{cur.scheme}://{cur.netloc}"
        return urljoin(base, href)
    except Exception:
        return None

def open_next_tab_if_needed(next_url):
    if next_url in next_tabs:
        if LOG_NEXT_ALREADY_OPEN_VERBOSE:
            log(f"ℹ️ NEXT már nyitva: {next_url}")
        return

    try:
        original = driver.current_window_handle
    except Exception:
        original = None

    try:
        driver.switch_to.new_window('tab')
        driver.get(next_url)
        _inject_disable_animations()
        handle = driver.current_window_handle

        WebDriverWait(driver, 8).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
        )
        tb_count = len(driver.find_elements(By.CSS_SELECTOR, NEXT_SELECTOR))
        if tb_count <= NEXT_EMPTY_CLOSE_TB_THRESHOLD:
            try:
                driver.close()
            except Exception:
                pass
            if original and original in driver.window_handles:
                driver.switch_to.window(original)
            log(f"🔒 NEXT zárva üres miatt: {next_url}")
            return

        now = time.time()
        next_tabs[next_url] = {
            "handle": handle,
            "active_ids": set(),
            "created_at": now,
            "last_refresh": now,
            "next_refresh": now + _rand_next_refresh_interval(),
            "needs_scan": True,
        }

        if original and original in driver.window_handles:
            driver.switch_to.window(original)
        log(f"🆕 NEXT tab nyitva: {next_url}")
        return
    except Exception as e:
        warn(f"⚠️ NEXT nyitás hiba: {e}")
        try:
            if original and original in driver.window_handles:
                driver.switch_to.window(original)
        except Exception:
            pass

def maybe_refresh_next_tab(url: str, info: dict) -> bool:
    now = time.time()
    if now < info.get("next_refresh", 0):
        return False

    ok = False
    try:
        result = _safe_execute_async_script(r"""
            var callback = arguments[0];
            try {
                var sc = document.querySelector('div.table-container.product-table-container');
                if (!sc) { callback({ok:false, err:'container-not-found'}); return; }
                fetch(window.location.href, {cache:'no-store'})
                  .then(r => { if (!r.ok) throw new Error('http-'+r.status); return r.text(); })
                  .then(html => {
                      var parser = new DOMParser();
                      var doc = parser.parseFromString(html, 'text/html');
                      var newSc = doc.querySelector('div.table-container.product-table-container');
                      if (!newSc) { callback({ok:false, err:'new-container-not-found'}); return; }
                      var y = window.scrollY;
                      sc.innerHTML = newSc.innerHTML;
                      window.scrollTo(0, y);
                      callback({ok:true});
                  })
                  .catch(e => callback({ok:false, err:String(e)}));
            } catch(e) { callback({ok:false, err:String(e)}); }
        """)
        ok = bool(result and result.get("ok"))
    except Exception as e:
        warn(f"⚠️ NEXT részleges refresh hiba: {e}")
        ok = False

    info["last_refresh"] = now
    info["next_refresh"] = now + _rand_next_refresh_interval()
    if ok:
        info["needs_scan"] = True
    return ok

# ---------- PLAY/PAUSE → SHIFT+P AUTUPDATE KEZELÉS ----------
def _dismiss_cookie_like_overlays():
    try:
        _safe_execute_script(r"""
        (function(){
          var cands = [
            '#onetrust-banner-sdk', '#CybotCookiebotDialog', '.cc-window',
            '.cookie', '.cookies', '[data-cookie]', '[aria-label*="cookie" i]'
          ];
          cands.forEach(function(sel){
            var el = document.querySelector(sel);
            if (!el) return;
            var st = window.getComputedStyle(el);
            if (st && st.position === 'fixed') {
              el.style.display='none';
              el.style.visibility='hidden';
              el.style.pointerEvents='none';
            }
          });
        })();
        """)
    except Exception:
        pass

def _get_autoupdate_state():
    try:
        txt = _safe_execute_script(r"""
        var w = document.querySelector('div.paginate-and.mb-3');
        return w ? (w.textContent || '').toLowerCase() : '';
        """) or ""
        if not txt:
            return None
        if "auto updates" in txt:
            if "pause them" in txt:
                return "running"
            if "start them" in txt:
                return "stopped"
        return None
    except Exception:
        return None

def _send_shift_p():
    try:
        _safe_execute_script("window.focus(); try{document.activeElement.blur();}catch(e){}")
    except Exception:
        pass
    try:
        driver.execute_cdp_cmd("Input.dispatchKeyEvent", {
            "type": "keyDown",
            "key": "P",
            "code": "KeyP",
            "windowsVirtualKeyCode": 80,
            "nativeVirtualKeyCode": 80,
            "modifiers": 8
        })
        driver.execute_cdp_cmd("Input.dispatchKeyEvent", {
            "type": "keyUp",
            "key": "P",
            "code": "KeyP",
            "windowsVirtualKeyCode": 80,
            "nativeVirtualKeyCode": 80,
            "modifiers": 8
        })
        return True
    except Exception:
        pass
    try:
        actions = ActionChains(driver)
        actions.key_down(Keys.SHIFT).send_keys('p').key_up(Keys.SHIFT).perform()
        return True
    except Exception:
        pass
    try:
        body = driver.find_element(By.TAG_NAME, "body")
        body.send_keys(Keys.SHIFT, 'p')
        return True
    except Exception:
        return False

MAIN_HANDLE = None
main_refresh_enabled = False
main_last_refresh = 0.0
main_next_refresh = 0.0

paginate_refresh_enabled = False
paginate_last_refresh = 0.0
paginate_next_refresh = 0.0
has_any_next_tab_opened_ever = False

def _rand_main_refresh_interval():
    return random.uniform(MAIN_REFRESH_MIN, MAIN_REFRESH_MAX)

def _rand_paginate_refresh_interval():
    return random.uniform(MAIN_PAGINATE_REFRESH_MIN, MAIN_PAGINATE_REFRESH_MAX)

def _wait_main_container(timeout=8):
    WebDriverWait(driver, timeout).until(
        EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
    )

def ensure_main_autoupdate():
    """
    Login utáni első 60 mp: Shift+P max 6×, amíg nem látszik a
    '(Auto updates — Shift+P to pause them)' szöveg.
    Később: ha eltűnik, Shift+P max 3×. Ha így sem látszik, timed-refresh fallback.
    """
    global main_refresh_enabled, main_last_refresh, main_next_refresh, _autoupdate_attempts, LOGIN_TS

    present = _autoupdate_banner_present()

    if present:
        main_refresh_enabled = False
        main_next_refresh = 0.0
        _autoupdate_attempts = 0
        return

    first_minute = (time.time() - (LOGIN_TS or 0)) <= 60
    max_tries = SHIFT_P_MAX_TRIES_FIRST_MIN if first_minute else 3

    tries = 0
    while present is False and _autoupdate_attempts < max_tries and tries < max_tries:
        if _send_shift_p():
            time.sleep(0.35)
        tries += 1
        _autoupdate_attempts += 1
        present = _autoupdate_banner_present()

    if present:
        main_refresh_enabled = False
        main_next_refresh = 0.0
        _autoupdate_attempts = 0
    else:
        main_refresh_enabled = True
        main_last_refresh = time.time()
        main_next_refresh = main_last_refresh + _rand_main_refresh_interval()

def maybe_refresh_main_page():
    global main_refresh_enabled, main_last_refresh, main_next_refresh
    if not main_refresh_enabled:
        return
    now = time.time()
    if now < main_next_refresh:
        return
    try:
        current = driver.current_window_handle
        if MAIN_HANDLE and MAIN_HANDLE in driver.window_handles:
            driver.switch_to.window(MAIN_HANDLE)

        driver.refresh()
        _inject_disable_animations()
        _wait_main_container(timeout=10)
        main_last_refresh = now
        main_next_refresh = now + _rand_main_refresh_interval()
        ensure_main_autoupdate()
    except Exception as e:
        warn(f"⚠️ Főoldal reload hiba: {e}")
        main_last_refresh = now
        main_next_refresh = now + _rand_main_refresh_interval()
    finally:
        try:
            if current and current in driver.window_handles:
                driver.switch_to.window(current)
        except Exception:
            pass

def maybe_refresh_main_paginate_and_try_open_next(len_tbodys_main: int):
    global paginate_refresh_enabled, paginate_last_refresh, paginate_next_refresh, has_any_next_tab_opened_ever

    try:
        if MAIN_HANDLE and MAIN_HANDLE in driver.window_handles:
            driver.switch_to.window(MAIN_HANDLE)
    except Exception:
        return

    next_link = find_next_page_link()
    if next_link:
        open_next_tab_if_needed(next_link)
        has_any_next_tab_opened_ever = True
        paginate_refresh_enabled = False
        return

    if len_tbodys_main == 49:
        if not has_any_next_tab_opened_ever:
            if not paginate_refresh_enabled:
                paginate_refresh_enabled = True
                paginate_last_refresh = time.time()
                paginate_next_refresh = paginate_last_refresh + _rand_paginate_refresh_interval()
        else:
            if not next_tabs:
                if not paginate_refresh_enabled:
                    paginate_refresh_enabled = True
                    paginate_last_refresh = time.time()
                    paginate_next_refresh = paginate_last_refresh + _rand_paginate_refresh_interval()
    else:
        paginate_refresh_enabled = False

    if paginate_refresh_enabled and time.time() >= paginate_next_refresh:
        try:
            _safe_execute_async_script(r"""
                var callback = arguments[0];
                try {
                    var wrap = document.querySelector('div.paginate-and.mb-3');
                    if (!wrap) { callback({ok:false,err:'paginate-wrapper-not-found'}); return; }
                    fetch(window.location.href, {cache:'no-store'})
                      .then(r => { if (!r.ok) throw new Error('http-'+r.status); return r.text(); })
                      .then(html => {
                          var parser = new DOMParser();
                          var doc = parser.parseFromString(html, 'text/html');
                          var newWrap = doc.querySelector('div.paginate-and.mb-3');
                          if (!newWrap) { callback({ok:false,err:'new-wrapper-not-found'}); return; }
                          wrap.innerHTML = newWrap.innerHTML;
                          callback({ok:true});
                      })
                      .catch(e => callback({ok:false,err:String(e)}));
                } catch(e) { callback({ok:false,err:String(e)}); }
            """)
        except Exception:
            pass
        paginate_last_refresh = time.time()
        paginate_next_refresh = paginate_last_refresh + _rand_paginate_refresh_interval()

        try:
            link2 = find_next_page_link()
            if link2:
                open_next_tab_if_needed(link2)
                has_any_next_tab_opened_ever = True
                paginate_refresh_enabled = False
        except Exception:
            pass

# ---------- LOGIN ----------
def _submit_login_form_robust(timeout_after=12):
    _dismiss_cookie_like_overlays()

    BTN_SEL = "#sign-in-form-submit-button, input[type='submit'][name='commit']"
    PW_SEL  = "input[autocomplete='password']"

    try:
        pw = WebDriverWait(driver, 6).until(EC.presence_of_element_located((By.CSS_SELECTOR, PW_SEL)))
        pw.send_keys(Keys.ENTER)
        WebDriverWait(driver, timeout_after).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
        )
        return True
    except Exception:
        pass

    try:
        btn = WebDriverWait(driver, 6).until(EC.presence_of_element_located((By.CSS_SELECTOR, BTN_SEL)))
        _safe_execute_script("arguments[0].scrollIntoView({block:'center', inline:'center'});", btn)
        _safe_execute_script("arguments[0].click();", btn)
        WebDriverWait(driver, timeout_after).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
        )
        return True
    except Exception:
        pass

    try:
        ok = _safe_execute_script(r"""
        (function(){
          var btn = document.querySelector(arguments[0]);
          if(!btn) return false;
          var f = btn.form || btn.closest('form');
          if(!f) return false;
          if (typeof f.requestSubmit === 'function') { f.requestSubmit(btn); }
          else { f.submit(); }
          return true;
        })();
        """, BTN_SEL)
        if ok:
            WebDriverWait(driver, timeout_after).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
            )
            return True
    except Exception:
        pass

    return False

def login():
    try:
        driver.get(LOGIN_URL)
        _inject_disable_animations()
        time.sleep(0.8)

        email_field = WebDriverWait(driver, 12).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "input[autocomplete='email']"))
        )
        password_field = WebDriverWait(driver, 12).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "input[autocomplete='password']"))
        )

        username = os.getenv("SB_USER") or "nosztalgiakonzol@gmail.com"
        password = os.getenv("SB_PASS") or "Pankix123!"

        human_type(email_field, username)
        human_type(password_field, password)

        if not _submit_login_form_robust(timeout_after=15):
            raise RuntimeError("Nem sikerült elküldeni a bejelentkezési űrlapot.")

        _inject_disable_animations()
        WebDriverWait(driver, 15).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
        )

        log("✅ Sikeres bejelentkezés.")
        global LOGIN_TS, _autoupdate_attempts
        LOGIN_TS = time.time()
        _autoupdate_attempts = 0
    except Exception as e:
        print(f"❌ Bejelentkezés sikertelen: {e}")
        try:
            driver.get(LOGIN_URL)
            _inject_disable_animations()
            try:
                pw = WebDriverWait(driver, 8).until(
                    EC.presence_of_element_located((By.CSS_SELECTOR, "input[autocomplete='password']"))
                )
                pw.send_keys(Keys.ENTER)
                WebDriverWait(driver, 12).until(
                    EC.presence_of_element_located((By.CSS_SELECTOR, 'div.table-container.product-table-container'))
                )
                log("✅ Sikeres bejelentkezés (fallback ENTER).")
            except Exception:
                raise
            return
        except Exception:
            try:
                driver.quit()
            except:
                pass
            raise SystemExit(1)

# ---------- SCAN függvények GROUP/NEXT ----------
def group_scan_tab(url: str, info: dict, higher_ids: set):
    pending_deletes = []
    curr_ids_tab = set()
    should_close = False
    new_ids_for_save = []

    try:
        WebDriverWait(driver, 6).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
        )
        tbodys = driver.find_elements(By.CSS_SELECTOR, GROUP_SELECTOR)

        if len(tbodys) <= GROUP_EMPTY_CLOSE_TB_THRESHOLD:
            should_close = True

        for tbody in tbodys:
            tid = None
            try:
                tid = tbody.get_attribute("data-id") or tbody.get_attribute("dataid")
            except Exception:
                pass
            if not tid:
                continue

            curr_ids_tab.add(tid)
            last_seen_ts[tid] = time.time()
            id_source[tid] = url

            if tid in higher_ids:
                continue

            if tid in seen:
                handle_update_for_id(tid)
            else:
                new_ids_for_save.append(tid)

        batch_save_new_ids(new_ids_for_save, higher_ids=higher_ids)

        gone_here = info.get("active_ids", set()) - curr_ids_tab
        for gid in gone_here:
            pending_deletes.append((url, gid))

        info["active_ids"] = curr_ids_tab
        info["needs_scan"] = False

    except Exception as e:
        warn(f"⚠️ Group szkennelés hiba: {e}")
        should_close = True

    return curr_ids_tab, pending_deletes, should_close

def next_scan_tab(url: str, info: dict, curr_ids_main: set):
    pending_deletes = []
    curr_ids_tab = set()
    should_close = False
    found_next_link = None
    new_ids_for_save = []

    try:
        WebDriverWait(driver, 6).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "div.table-container.product-table-container"))
        )
        tbodys = driver.find_elements(By.CSS_SELECTOR, NEXT_SELECTOR)

        if len(tbodys) <= NEXT_EMPTY_CLOSE_TB_THRESHOLD:
            should_close = True

        if len(tbodys) >= 50:
            found_next_link = find_next_page_link()

        for tbody in tbodys:
            tid = None
            try:
                tid = tbody.get_attribute("data-id") or tbody.get_attribute("dataid")
            except Exception:
                pass
            if not tid:
                continue

            curr_ids_tab.add(tid)
            last_seen_ts[tid] = time.time()
            id_source[tid] = url

            if tid in curr_ids_main:
                continue

            if tid in seen:
                handle_update_for_id(tid)
            else:
                new_ids_for_save.append(tid)

        batch_save_new_ids(new_ids_for_save, higher_ids=curr_ids_main)

        gone_here = info.get("active_ids", set()) - curr_ids_tab
        for gid in gone_here:
            pending_deletes.append((url, gid))

        info["active_ids"] = curr_ids_tab
        info["needs_scan"] = False

    except Exception as e:
        warn(f"⚠️ NEXT szkennelés hiba: {e}")
        should_close = True

    return curr_ids_tab, pending_deletes, should_close, found_next_link

# ---------- dispatcher eredmények feldolgozása ----------
pending_delete_ids = set()
def process_dispatcher_results(max_items=300):
    global active_ids, seen
    results = dispatcher.get_results(max_items=max_items)
    for res in results:
        rtype = res.get("type")
        tid = res.get("id")

        if rtype in ("save_ok", "save_dup_updated"):
            st = res.get("state_info", {})
            resp = res.get("resp", {})
            cid = resp.get("correlation_id")
            if tid not in seen:
                seen.add(tid)
                save_seen_line(tid)
            last_sent_state[tid] = {
                "odds1": norm_odds(st.get("odds1")),
                "odds2": norm_odds(st.get("odds2")),
                "profit_percent": norm_profit_str(st.get("profit_percent")),
            }
            last_update_ts[tid] = time.time()
            if tid not in active_ids:
                active_ids.add(tid); save_active_all(active_ids)
            log(f"💾 SAVE kész: {tid} ({'dup→update' if rtype=='save_dup_updated' else 'ok'}) cid={cid}")

        elif rtype == "save_duplicate":
            resp = res.get("resp", {})
            cid = resp.get("correlation_id")
            log(f"ℹ️ SAVE duplicate (külön UPDATE nem futott automatikusan): {tid} cid={cid}")

        elif rtype == "save_dup_update_fail":
            warn(f"⚠️ SAVE duplicate → UPDATE FAIL id={tid} status={res.get('status')} err={res.get('error')}")

        elif rtype == "save_error":
            err = res.get("error")
            cid = (err or {}).get("correlation_id") if isinstance(err, dict) else None
            warn(f"⚠️ SAVE hiba id={tid} status={res.get('status')} err={err} cid={cid}")

        elif rtype == "update_ok":
            p = res.get("payload", {})
            resp = res.get("resp", {})
            cid = resp.get("correlation_id")
            if tid:
                last_sent_state[tid] = {
                    "odds1": p.get("odds1"),
                    "odds2": p.get("odds2"),
                    "profit_percent": p.get("profit_percent"),
                }
                last_update_ts[tid] = time.time()
            log(f"🔄 UPDATE kész: {tid} cid={cid}")

        elif rtype == "update_error":
            status = res.get("status")
            err = res.get("error")
            cid = (err or {}).get("correlation_id") if isinstance(err, dict) else None
            if status == 404 and tid:
                t = prepare_new_task_for_id(tid)
                if t and t.get("finals") and valid_external(t["finals"][0]) and valid_external(t["finals"][1]):
                    tip_payload = _build_tip_payload_from_task(t)
                    update_payload = _build_update_payload_from_task(t)
                    dispatcher.enqueue_save({
                        "id": t["id"],
                        "tip_payload": tip_payload,
                        "update_payload": update_payload,
                        "state_info": {
                            "odds1": tip_payload["odds1"],
                            "odds2": tip_payload["odds2"],
                            "profit_percent": tip_payload["profit_percent"],
                        },
                        "finals": t.get("finals"),
                    })
                    log(f"↩️ UPDATE 404 → újra SAVE sorba téve: {tid}")
            else:
                warn(f"⚠️ UPDATE hiba id={tid} status={status} err={err} cid={cid}")

        elif rtype == "delete_ok":
            if tid in active_ids:
                active_ids.remove(tid); save_active_all(active_ids)
            last_sent_state.pop(tid, None)
            last_update_ts.pop(tid, None)
            last_update_attempt_ts.pop(tid, None)
            last_seen_ts.pop(tid, None)
            if tid in seen:
                seen.remove(tid); remove_seen_line(tid)
            pending_delete_ids.discard(tid)
            resp = res.get("resp", {})
            cid = resp.get("correlation_id")
            log(f"❌ DELETE kész: {tid} cid={cid}")

        elif rtype == "delete_error":
            err = res.get("error")
            cid = (err or {}).get("correlation_id") if isinstance(err, dict) else None
            warn(f"⚠️ DELETE hiba id={tid} status={res.get('status')} err={err} cid={cid}")
            pending_delete_ids.discard(tid)

# ---------- fő program ----------
seen = load_seen()
active_ids = load_active()
last_sent_state = {}
last_update_ts = {}
last_update_attempt_ts = {}
link_cache = load_link_cache()

# NOTE: A futtatáskor a login() hívás indít. Ha csak importálod, ne fusson automatikusan.
if __name__ == "__main__":
    login()
    try:
        MAIN_HANDLE = driver.current_window_handle
    except Exception:
        MAIN_HANDLE = None

    # Autoupdate indítása Shift+P-vel, ha kell
    ensure_main_autoupdate()
    prev_ids_main = set()

    def scan_next_tabs_evented(curr_ids_main: set):
        next_all_curr_ids = set()
        pending_deletes = []
        to_close = []
        open_requests = []

        items = list(next_tabs.items())
        for url, info in items:
            handle = info["handle"]
            try:
                if handle not in driver.window_handles:
                    next_tabs.pop(url, None)
                    continue
                driver.switch_to.window(handle)
            except Exception:
                to_close.append(url)
                continue

            try:
                if maybe_refresh_next_tab(url, info):
                    pass
            except Exception:
                pass

            if info.get("needs_scan", False):
                curr_ids_tab, pend_del, should_close, found_next = next_scan_tab(url, info, curr_ids_main)
                next_all_curr_ids.update(curr_ids_tab)
                pending_deletes.extend(pend_del)
                if found_next:
                    open_requests.append(found_next)
                if should_close:
                    to_close.append(url)

            try:
                if driver.window_handles:
                    driver.switch_to.window(MAIN_HANDLE or driver.window_handles[0])
            except Exception:
                pass

        return next_all_curr_ids, pending_deletes, to_close, open_requests

    def scan_group_tabs_evented(curr_ids_main: set, higher_ids: set):
        group_all_curr_ids = set()
        pending_deletes = []
        to_close = []

        items = list(group_tabs.items())
        for url, info in items:
            handle = info["handle"]
            try:
                if handle not in driver.window_handles:
                    group_tabs.pop(url, None)
                    continue
                driver.switch_to.window(handle)
            except Exception:
                to_close.append(url)
                continue

            try:
                if maybe_refresh_group_tab(url, info):
                    pass
            except Exception:
                pass

            if info.get("needs_scan", False):
                curr_ids_tab, pend_del, should_close = group_scan_tab(url, info, higher_ids)
                group_all_curr_ids.update(curr_ids_tab)
                pending_deletes.extend(pend_del)
                if should_close:
                    to_close.append(url)

            try:
                if driver.window_handles:
                    driver.switch_to.window(MAIN_HANDLE or driver.window_handles[0])
            except Exception:
                pass

        return group_all_curr_ids, pending_deletes, to_close

    try:
        while True:
            process_dispatcher_results(max_items=400)

            now_ts = time.time()
            maybe_refresh_main_page()

            try:
                if MAIN_HANDLE and MAIN_HANDLE in driver.window_handles:
                    driver.switch_to.window(MAIN_HANDLE)
                tbodys_main = driver.find_elements(By.CSS_SELECTOR, "tbody.surebet_record")
            except Exception:
                time.sleep(CHECK_INTERVAL)
                continue

            ensure_main_autoupdate()

            curr_ids_main = set()
            new_ids_main = []

            for tbody in tbodys_main:
                try:
                    tbody_id = tbody.get_attribute("data-id") or tbody.get_attribute("dataid")
                except Exception:
                    tbody_id = None
                if not tbody_id:
                    continue

                curr_ids_main.add(tbody_id)
                last_seen_ts[tbody_id] = now_ts
                id_source[tbody_id] = 'main'

                try:
                    group_url = find_group_link_in_tbody(tbody)
                    if group_url:
                        open_group_tab_if_needed(group_url)
                except Exception:
                    pass

                if tbody_id in seen:
                    handle_update_for_id(tbody_id)
                else:
                    new_ids_main.append(tbody_id)

            batch_save_new_ids(new_ids_main)

            try:
                maybe_refresh_main_paginate_and_try_open_next(len_tbodys_main=len(tbodys_main))
            except Exception:
                pass

            next_all_curr_ids, next_pending_deletes, next_to_close, next_open_requests = scan_next_tabs_evented(curr_ids_main)

            for nurl in next_open_requests:
                try:
                    open_next_tab_if_needed(nurl)
                except Exception:
                    pass

            higher_ids = curr_ids_main | next_all_curr_ids
            group_all_curr_ids, group_pending_deletes, group_to_close = scan_group_tabs_evented(curr_ids_main, higher_ids)

            curr_ids_all_now = curr_ids_main | next_all_curr_ids | group_all_curr_ids
            now2 = time.time()

            for url, gid in next_pending_deletes:
                if gid in curr_ids_all_now:
                    continue
                last_ts = last_seen_ts.get(gid, 0.0)
                if (now2 - last_ts) >= DISAPPEAR_GRACE_SEC and gid not in pending_delete_ids:
                    dispatcher.enqueue_delete(gid)
                    pending_delete_ids.add(gid)

            for url, gid in group_pending_deletes:
                if gid in curr_ids_all_now:
                    continue
                last_ts = last_seen_ts.get(gid, 0.0)
                if (now2 - last_ts) >= DISAPPEAR_GRACE_SEC and gid not in pending_delete_ids:
                    dispatcher.enqueue_delete(gid)
                    pending_delete_ids.add(gid)

            maybe_gone_main = [aid for aid in list(active_ids) if id_source.get(aid) == 'main' and aid not in curr_ids_main]
            now_ts2 = time.time()
            for gid in maybe_gone_main:
                last_ts = last_seen_ts.get(gid, 0.0)
                if (now_ts2 - last_ts) >= DISAPPEAR_GRACE_SEC and gid not in pending_delete_ids:
                    dispatcher.enqueue_delete(gid)
                    pending_delete_ids.add(gid)

            # TABOK BEZÁRÁSA
            for url in next_to_close:
                info = next_tabs.get(url)
                try:
                    if info and info["handle"] in driver.window_handles:
                        driver.switch_to.window(info["handle"])
                        driver.close()
                except Exception:
                    pass
                finally:
                    next_tabs.pop(url, None)
                    try:
                        if MAIN_HANDLE and MAIN_HANDLE in driver.window_handles:
                            driver.switch_to.window(MAIN_HANDLE)
                    except Exception:
                        pass

            for url in group_to_close:
                close_group_tab(url)
                block_group_url(url, GROUP_REOPEN_BACKOFF_SEC, "empty(<=1)-close")

            prev_ids_main = curr_ids_main
            time.sleep(CHECK_INTERVAL)

    except KeyboardInterrupt:
        warn("🛑 Leállítva.")
    finally:
        try:
            process_dispatcher_results(max_items=1000)
            dispatcher.stop()
        except:
            pass
        try:
            driver.quit()
        except:
            pass
        # Ephemerális profil törlése futás végén
        try:
            if not PERSIST_PROFILE and os.path.isdir(PROFILE_DIR):
                shutil.rmtree(PROFILE_DIR, ignore_errors=True)
        except Exception:
            pass
        driver = None
