import os
import time
import json
import math
import sqlite3
import threading
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from typing import Any, Dict, List, Optional, Tuple

import requests
from flask import Flask, jsonify, request

app = Flask(__name__)

# =========================================================
# Version
# =========================================================
SCRIPT_VERSION = "wallet-intel-v8-pattern-timing-clusters"
UTC = timezone.utc

# =========================================================
# Environment
# =========================================================
DATA_API_BASE = os.getenv("DATA_API_BASE", "https://data-api.polymarket.com")
DATA_API_V1_BASE = os.getenv("DATA_API_V1_BASE", f"{DATA_API_BASE}/v1")
GAMMA_BASE = os.getenv("GAMMA_BASE", "https://gamma-api.polymarket.com")
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")
REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "20"))
PORT = int(os.getenv("PORT", "10000"))

# Scan cadence
SCAN_EVERY_SECONDS = int(os.getenv("SCAN_EVERY_SECONDS", "1800"))
GROUP_WINDOW_SECONDS = int(os.getenv("GROUP_WINDOW_SECONDS", "10800"))
SEND_ZERO_GROUP_SUMMARY = os.getenv("SEND_ZERO_GROUP_SUMMARY", "true").lower() == "true"

# Discovery
LEADERBOARD_LIMIT = int(os.getenv("LEADERBOARD_LIMIT", "100"))
ACTIVE_MARKET_LIMIT = int(os.getenv("ACTIVE_MARKET_LIMIT", "40"))
HOLDERS_PER_MARKET = int(os.getenv("HOLDERS_PER_MARKET", "15"))
MAX_CANDIDATE_WALLETS = int(os.getenv("MAX_CANDIDATE_WALLETS", "120"))
EXCLUDE_SPORTS_WALLETS = os.getenv("EXCLUDE_SPORTS_WALLETS", "true").lower() == "true"
TOP_WALLETS_PER_SCAN = int(os.getenv("TOP_WALLETS_PER_SCAN", "8"))
TOP_WALLETS_PER_GROUP = int(os.getenv("TOP_WALLETS_PER_GROUP", "10"))

SPORTS_RATIO_CLOSED_MAX = float(os.getenv("SPORTS_RATIO_CLOSED_MAX", "0.40"))
SPORTS_RATIO_TRADES_MAX = float(os.getenv("SPORTS_RATIO_TRADES_MAX", "0.50"))
SPORTS_RATIO_CURRENT_MAX = float(os.getenv("SPORTS_RATIO_CURRENT_MAX", "0.50"))
SPORTS_RATIO_HOLDER_HINT_MAX = float(os.getenv("SPORTS_RATIO_HOLDER_HINT_MAX", "0.50"))
SIMILAR_WALLETS_LIMIT = int(os.getenv("SIMILAR_WALLETS_LIMIT", "3"))

# Manual quick scan limits
MANUAL_LEADERBOARD_LIMIT = int(os.getenv("MANUAL_LEADERBOARD_LIMIT", "25"))
MANUAL_ACTIVE_MARKET_LIMIT = int(os.getenv("MANUAL_ACTIVE_MARKET_LIMIT", "20"))
MANUAL_HOLDERS_PER_MARKET = int(os.getenv("MANUAL_HOLDERS_PER_MARKET", "10"))
MANUAL_MAX_CANDIDATE_WALLETS = int(os.getenv("MANUAL_MAX_CANDIDATE_WALLETS", "24"))
MANUAL_SCAN_DEADLINE_SECONDS = int(os.getenv("MANUAL_SCAN_DEADLINE_SECONDS", "45"))
MANUAL_SEND_CACHED_FIRST = os.getenv("MANUAL_SEND_CACHED_FIRST", "true").lower() == "true"

# Snapshot grading
LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "30"))
RECENT_DAYS = int(os.getenv("RECENT_DAYS", "7"))
MIN_CLOSED_POSITIONS_30D = int(os.getenv("MIN_CLOSED_POSITIONS_30D", "15"))
MIN_TRADES_30D = int(os.getenv("MIN_TRADES_30D", "10"))
MIN_WEIGHTED_RETURN_30D = float(os.getenv("MIN_WEIGHTED_RETURN_30D", "0.20"))
MIN_WIN_RATE_30D = float(os.getenv("MIN_WIN_RATE_30D", "0.55"))
MIN_CONSISTENCY_RATIO = float(os.getenv("MIN_CONSISTENCY_RATIO", "0.50"))
MIN_REALIZED_PNL_30D = float(os.getenv("MIN_REALIZED_PNL_30D", "0.0"))
MIN_RECENT_TRADES_7D = int(os.getenv("MIN_RECENT_TRADES_7D", "2"))
MIN_INTRADAY_SIGNALS = int(os.getenv("MIN_INTRADAY_SIGNALS", "1"))
WATCH_BUCKET_MIN_SCORE = float(os.getenv("WATCH_BUCKET_MIN_SCORE", "60"))
TEST_FIRST_MIN_SCORE = float(os.getenv("TEST_FIRST_MIN_SCORE", "75"))

# Observation settings
OBS_DB_PATH = os.getenv("OBS_DB_PATH", "/tmp/polymarket_wallet_intel.db")
OBSERVE_RECENT_HOURS = int(os.getenv("OBSERVE_RECENT_HOURS", "24"))
OBSERVE_MAX_TRADES_PER_WALLET = int(os.getenv("OBSERVE_MAX_TRADES_PER_WALLET", "30"))
OBS_MIN_ENTRY_PRICE = float(os.getenv("OBS_MIN_ENTRY_PRICE", "0.03"))
OBS_MAX_ENTRY_PRICE = float(os.getenv("OBS_MAX_ENTRY_PRICE", "0.97"))
OBS_SUCCESS_THRESHOLD = float(os.getenv("OBS_SUCCESS_THRESHOLD", "0.03"))
OBS_MIN_SAMPLE_24H = int(os.getenv("OBS_MIN_SAMPLE_24H", "3"))
OBS_PROMOTE_SUCCESS_RATE = float(os.getenv("OBS_PROMOTE_SUCCESS_RATE", "0.60"))
OBS_DEMOTE_SUCCESS_RATE = float(os.getenv("OBS_DEMOTE_SUCCESS_RATE", "0.40"))
OBS_TRACK_BUCKETS = os.getenv("OBS_TRACK_BUCKETS", "TEST FIRST,WATCH CLOSELY")
OBS_TRACK_BUCKET_SET = {x.strip().upper() for x in OBS_TRACK_BUCKETS.split(",") if x.strip()}

STATE_FILE = os.getenv("STATE_FILE", "/tmp/polymarket_wallet_intel_state.json")

# =========================================================
# Runtime state
# =========================================================
state_lock = threading.Lock()
manual_scan_in_progress = False
background_started = False
http_session = requests.Session()

runtime_state: Dict[str, Any] = {
    "last_group_sent_at": 0.0,
    "scan_history": [],
    "session_summary": {
        "scans": 0,
        "wallets_evaluated": 0,
        "wallets_passing": 0,
        "last_scan_top_count": 0,
        "last_group_top_count": 0,
        "observations_logged": 0,
        "observations_evaluated": 0,
        "last_observed_success_wallets": 0,
    },
    "last_health": {},
}

# =========================================================
# Helpers
# =========================================================
def now_utc() -> datetime:
    return datetime.now(tz=UTC)


def utc_ts() -> float:
    return time.time()


def safe_float(value: Any, default: float = 0.0) -> float:
    try:
        if value is None or value == "":
            return default
        return float(value)
    except Exception:
        return default


def safe_int(value: Any, default: int = 0) -> int:
    try:
        if value is None or value == "":
            return default
        return int(float(value))
    except Exception:
        return default


def clamp(value: float, low: float, high: float) -> float:
    return max(low, min(high, value))


def short_wallet(addr: str) -> str:
    addr = (addr or "").strip()
    if len(addr) <= 12:
        return addr
    return f"{addr[:6]}...{addr[-4:]}"


def clean_text(value: Any) -> str:
    return " ".join(str(value or "").split())


def parse_ts(value: Any) -> Optional[datetime]:
    if value is None or value == "":
        return None
    if isinstance(value, datetime):
        return value if value.tzinfo else value.replace(tzinfo=UTC)
    try:
        if isinstance(value, (int, float)):
            val = float(value)
            if val > 1e12:
                val /= 1000.0
            return datetime.fromtimestamp(val, tz=UTC)
        s = str(value).strip()
        if not s:
            return None
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        if s.isdigit():
            val = float(s)
            if val > 1e12:
                val /= 1000.0
            return datetime.fromtimestamp(val, tz=UTC)
        dt = datetime.fromisoformat(s)
        return dt if dt.tzinfo else dt.replace(tzinfo=UTC)
    except Exception:
        return None


def iso_utc(dt: Optional[datetime]) -> str:
    if not dt:
        return ""
    return dt.astimezone(UTC).isoformat()


def days_ago(days: int) -> datetime:
    return now_utc() - timedelta(days=days)


def hours_ago(hours: int) -> datetime:
    return now_utc() - timedelta(hours=hours)


def json_dump(path: str, payload: Dict[str, Any]) -> None:
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(payload, f)
    except Exception:
        pass


def json_load(path: str) -> Optional[Dict[str, Any]]:
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            return data
    except Exception:
        return None
    return None


def load_state() -> None:
    global runtime_state
    data = json_load(STATE_FILE)
    if not data:
        return
    runtime_state.update(data)
    runtime_state.setdefault("scan_history", [])
    runtime_state.setdefault("session_summary", {})
    runtime_state.setdefault("last_health", {})


def save_state() -> None:
    payload = {
        "last_group_sent_at": runtime_state.get("last_group_sent_at", 0.0),
        "scan_history": runtime_state.get("scan_history", [])[-36:],
        "session_summary": runtime_state.get("session_summary", {}),
        "last_health": runtime_state.get("last_health", {}),
    }
    json_dump(STATE_FILE, payload)


def fetch_json(url: str, params: Optional[Dict[str, Any]] = None) -> Any:
    resp = http_session.get(url, params=params, timeout=REQUEST_TIMEOUT)
    resp.raise_for_status()
    return resp.json()


def fetch_list(url: str, params: Optional[Dict[str, Any]] = None) -> List[Dict[str, Any]]:
    try:
        data = fetch_json(url, params=params)
        if isinstance(data, list):
            return [x for x in data if isinstance(x, dict)]
        if isinstance(data, dict):
            for key in ["data", "results", "markets", "events", "holders"]:
                val = data.get(key)
                if isinstance(val, list):
                    return [x for x in val if isinstance(x, dict)]
    except Exception:
        return []
    return []


def send_telegram(text: str) -> None:
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        return
    try:
        requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
            json={"chat_id": TELEGRAM_CHAT_ID, "text": text},
            timeout=REQUEST_TIMEOUT,
        )
    except Exception:
        pass


# =========================================================
# SQLite
# =========================================================
def get_db() -> sqlite3.Connection:
    conn = sqlite3.connect(OBS_DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn


def init_db() -> None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS observed_trades (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                unique_key TEXT UNIQUE,
                wallet TEXT NOT NULL,
                username TEXT,
                bucket TEXT,
                snapshot_score REAL DEFAULT 0,
                market_slug TEXT,
                market_question TEXT,
                condition_id TEXT,
                outcome TEXT,
                side TEXT,
                trade_time TEXT,
                entry_price REAL DEFAULT 0,
                size REAL DEFAULT 0,
                source TEXT,
                status TEXT DEFAULT 'open',
                price_1h REAL,
                price_6h REAL,
                price_24h REAL,
                move_1h REAL,
                move_6h REAL,
                move_24h REAL,
                success_1h INTEGER,
                success_6h INTEGER,
                success_24h INTEGER,
                created_at TEXT,
                updated_at TEXT
            )
            """
        )

        cur.execute("CREATE INDEX IF NOT EXISTS idx_observed_wallet_status ON observed_trades(wallet, status)")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_observed_trade_time ON observed_trades(trade_time)")
        conn.commit()
    finally:
        conn.close()


# =========================================================
# Public Polymarket fetchers
# =========================================================
def fetch_leaderboard_wallets(limit: int) -> List[Dict[str, Any]]:
    rows = fetch_list(
        f"{DATA_API_V1_BASE}/leaderboard",
        params={"limit": min(limit, 100), "timePeriod": "MONTH", "orderBy": "PNL", "category": "OVERALL"},
    )
    out: List[Dict[str, Any]] = []
    for row in rows:
        wallet = str(row.get("proxyWallet") or row.get("wallet") or row.get("user") or row.get("address") or "").strip()
        if not wallet:
            continue
        out.append(
            {
                "wallet": wallet,
                "username": clean_text(row.get("name") or row.get("username") or ""),
                "leaderboard_rank": safe_int(row.get("rank") or row.get("leaderboardRank"), 0),
                "leaderboard_pnl": safe_float(row.get("pnl") or row.get("profit") or row.get("realizedPnl"), 0.0),
                "leaderboard_vol": safe_float(row.get("volume") or row.get("vol") or row.get("tradedVolume"), 0.0),
            }
        )
    return out


def fetch_active_markets(limit: int) -> List[Dict[str, Any]]:
    rows = fetch_list(
        f"{GAMMA_BASE}/markets",
        params={"limit": min(limit, 200), "active": "true", "closed": "false", "archived": "false"},
    )
    out: List[Dict[str, Any]] = []
    for row in rows:
        out.append(
            {
                "slug": clean_text(row.get("slug") or row.get("marketSlug") or ""),
                "question": clean_text(row.get("question") or row.get("title") or ""),
                "condition_id": clean_text(row.get("conditionId") or row.get("condition_id") or ""),
                "market_id": clean_text(row.get("id") or row.get("marketId") or ""),
                "yes_price": safe_float(row.get("yesPrice") or row.get("yes_price"), 0.0),
                "no_price": safe_float(row.get("noPrice") or row.get("no_price"), 0.0),
            }
        )
    return [x for x in out if x.get("slug") or x.get("condition_id")]


def fetch_top_holders_for_market(market: Dict[str, Any], limit: int) -> List[Dict[str, Any]]:
    slug = market.get("slug")
    condition_id = market.get("condition_id")
    params: Dict[str, Any] = {"limit": min(limit, 50)}
    if slug:
        params["slug"] = slug
    elif condition_id:
        params["conditionId"] = condition_id
    else:
        return []

    rows = fetch_list(f"{DATA_API_BASE}/holders", params=params)
    out: List[Dict[str, Any]] = []
    for token_row in rows:
        holders = token_row.get("holders")
        if not isinstance(holders, list):
            continue
        for holder in holders:
            if not isinstance(holder, dict):
                continue
            wallet = str(holder.get("proxyWallet") or holder.get("wallet") or holder.get("address") or "").strip()
            if not wallet:
                continue
            out.append(
                {
                    "wallet": wallet,
                    "holder_size": safe_float(holder.get("balance") or holder.get("size") or holder.get("shares"), 0.0),
                    "market_slug": slug,
                    "market_question": market.get("question", ""),
                }
            )
    return out[:limit]


def fetch_closed_positions(wallet: str) -> List[Dict[str, Any]]:
    return fetch_list(f"{DATA_API_BASE}/closed-positions", params={"user": wallet})


def fetch_current_positions(wallet: str) -> List[Dict[str, Any]]:
    return fetch_list(f"{DATA_API_BASE}/positions", params={"user": wallet})


def fetch_user_activity(wallet: str) -> List[Dict[str, Any]]:
    return fetch_list(f"{DATA_API_BASE}/activity", params={"user": wallet})


def fetch_trades(wallet: str) -> List[Dict[str, Any]]:
    rows = fetch_list(f"{DATA_API_BASE}/trades", params={"user": wallet})
    if rows:
        return rows
    return fetch_user_activity(wallet)


def fetch_market_snapshot(slug: str = "", condition_id: str = "") -> Optional[Dict[str, Any]]:
    params: Dict[str, Any] = {"limit": 1}
    if slug:
        params["slug"] = slug
    elif condition_id:
        params["conditionId"] = condition_id
    else:
        return None
    rows = fetch_list(f"{GAMMA_BASE}/markets", params=params)
    if not rows:
        return None
    row = rows[0]
    return {
        "slug": clean_text(row.get("slug") or row.get("marketSlug") or slug),
        "question": clean_text(row.get("question") or row.get("title") or ""),
        "condition_id": clean_text(row.get("conditionId") or row.get("condition_id") or condition_id),
        "yes_price": safe_float(row.get("yesPrice") or row.get("yes_price"), 0.0),
        "no_price": safe_float(row.get("noPrice") or row.get("no_price"), 0.0),
    }


SPORTS_KEYWORDS = {
    "nba", "nfl", "nhl", "mlb", "soccer", "football", "basketball", "baseball", "hockey",
    "tennis", "golf", "mma", "ufc", "boxing", "f1", "formula 1", "premier league",
    "champions league", "world cup", "ncaa", "march madness", "olympics", "super bowl",
    "player", "team", "match", "game", "tournament", "season", "playoffs"
}

CATEGORY_KEYWORDS = {
    "politics": ["trump", "biden", "election", "senate", "house", "governor", "president", "white house", "democrat", "republican", "gop", "primary", "poll"],
    "macro": ["fed", "cpi", "inflation", "recession", "rate cut", "interest rate", "treasury", "jobs report", "gdp", "fomc", "economy", "tariff", "yield"],
    "crypto": ["bitcoin", "btc", "ethereum", "eth", "solana", "sol", "crypto", "token", "coin", "blockchain"],
    "geopolitics": ["ukraine", "russia", "china", "taiwan", "israel", "gaza", "iran", "ceasefire", "nato", "war"],
    "tech": ["openai", "anthropic", "google", "meta", "apple", "microsoft", "ai", "chatgpt", "claude", "tesla", "spacex"],
    "law": ["court", "scotus", "supreme court", "lawsuit", "sec", "doj", "trial", "judge", "legal", "regulation"],
    "weather": ["hurricane", "storm", "earthquake", "wildfire", "weather", "temperature"],
}

def row_market_text(row: Dict[str, Any]) -> str:
    parts = [
        clean_text(row.get("market_question") or ""),
        clean_text(row.get("question") or row.get("title") or ""),
        clean_text(row.get("market_slug") or row.get("slug") or row.get("marketSlug") or ""),
        clean_text(row.get("description") or ""),
        clean_text(row.get("ticker") or ""),
    ]
    return " ".join([p for p in parts if p]).strip().lower()

def is_sports_text(text: str) -> bool:
    s = clean_text(text).lower()
    if not s:
        return False
    return any(term in s for term in SPORTS_KEYWORDS)

def is_sports_row(row: Dict[str, Any]) -> bool:
    return is_sports_text(row_market_text(row))

def categorize_text(text: str) -> str:
    s = clean_text(text).lower()
    if not s:
        return "other"
    if is_sports_text(s):
        return "sports"
    best_cat = "other"
    best_hits = 0
    for cat, terms in CATEGORY_KEYWORDS.items():
        hits = sum(1 for term in terms if term in s)
        if hits > best_hits:
            best_cat = cat
            best_hits = hits
    return best_cat

def categorize_row(row: Dict[str, Any]) -> str:
    return categorize_text(row_market_text(row))

def dominant_category(counts: Dict[str, int]) -> str:
    if not counts:
        return "other"
    items = sorted(counts.items(), key=lambda kv: (kv[1], kv[0]), reverse=True)
    return items[0][0] if items and items[0][1] > 0 else "other"

def top_categories(counts: Dict[str, int], limit: int = 3) -> List[str]:
    if not counts:
        return []
    items = sorted(counts.items(), key=lambda kv: (kv[1], kv[0]), reverse=True)
    return [k for k, v in items[:limit] if v > 0]

def safe_ratio(num: float, den: float) -> float:
    if den <= 0:
        return 0.0
    return num / den



def category_trend_summary(metrics: Dict[str, Any]) -> str:
    cat = clean_text(metrics.get("top_category_30d") or "other")
    wr = safe_float(metrics.get("top_category_win_rate_30d"), 0.0)
    avg_ret = safe_float(metrics.get("top_category_avg_return_30d"), 0.0)
    sample = safe_int(metrics.get("top_category_closed_count_30d"), 0)
    return f"{cat} wr={wr:.1%} avg={avg_ret:.1%} n={sample}"


def hour_bucket_label(hour_val: Any) -> str:
    h = safe_int(hour_val, -1)
    if h < 0 or h > 23:
        return "unknown"
    return f"{h:02d}:00Z"


def cluster_label(metrics: Dict[str, Any]) -> str:
    cat = clean_text(metrics.get("top_category_30d") or "other")
    timing = clean_text(metrics.get("timing_style") or "unproven")
    return f"{cat}:{timing}"
def best_observation_window(metrics: Dict[str, Any]) -> str:
    options = {
        "1h": safe_float(metrics.get("obs_success_rate_1h"), 0.0),
        "6h": safe_float(metrics.get("obs_success_rate_6h"), 0.0),
        "24h": safe_float(metrics.get("obs_success_rate_24h"), 0.0),
    }
    best = max(options.items(), key=lambda kv: kv[1])
    return best[0] if best[1] > 0 else "none"

def timing_style(metrics: Dict[str, Any]) -> str:
    s1 = safe_float(metrics.get("obs_success_rate_1h"), 0.0)
    s6 = safe_float(metrics.get("obs_success_rate_6h"), 0.0)
    s24 = safe_float(metrics.get("obs_success_rate_24h"), 0.0)
    if s1 >= 0.60 and s1 >= s24:
        return "fast-entry"
    if s24 >= 0.60 and s24 > s1:
        return "patient-hold"
    if s6 > 0 or s24 > 0 or s1 > 0:
        return "mixed"
    return "unproven"

def similarity_distance(a: Dict[str, Any], b: Dict[str, Any]) -> float:
    vals = [
        abs(safe_float(a.get("weighted_return_30d"), 0.0) - safe_float(b.get("weighted_return_30d"), 0.0)) * 100.0,
        abs(safe_float(a.get("win_rate_30d"), 0.0) - safe_float(b.get("win_rate_30d"), 0.0)) * 50.0,
        abs(safe_float(a.get("consistency_ratio_30d"), 0.0) - safe_float(b.get("consistency_ratio_30d"), 0.0)) * 40.0,
        abs(safe_float(a.get("obs_success_rate_24h"), 0.0) - safe_float(b.get("obs_success_rate_24h"), 0.0)) * 50.0,
        abs(safe_float(a.get("recent_trades_7d"), 0.0) - safe_float(b.get("recent_trades_7d"), 0.0)) / 5.0,
        abs(safe_float(a.get("top_category_win_rate_30d"), 0.0) - safe_float(b.get("top_category_win_rate_30d"), 0.0)) * 35.0,
        abs(safe_int(a.get("dominant_entry_hour_utc"), -1) - safe_int(b.get("dominant_entry_hour_utc"), -1)) / 3.0,
    ]
    score = sum(vals)
    if clean_text(a.get("top_category_30d")) != clean_text(b.get("top_category_30d")):
        score += 8.0
    if clean_text(a.get("timing_style")) != clean_text(b.get("timing_style")):
        score += 4.0
    return score

def annotate_similar_wallets(rows: List[Dict[str, Any]]) -> None:
    eligible = [r for r in rows if r.get("passes_filters")]
    if len(eligible) < 2:
        return
    for row in eligible:
        peers = []
        for other in eligible:
            if other.get("wallet") == row.get("wallet"):
                continue
            peers.append((similarity_distance(row, other), other))
        peers.sort(key=lambda x: x[0])
        similar = []
        for dist, other in peers[:SIMILAR_WALLETS_LIMIT]:
            similar.append({
                "wallet": other.get("wallet"),
                "username": other.get("username", ""),
                "bucket": other.get("bucket", ""),
                "score": other.get("score", 0.0),
                "top_category_30d": other.get("top_category_30d", ""),
                "timing_style": other.get("timing_style", ""),
                "cluster_label": other.get("cluster_label", ""),
            })
        row["similar_wallets"] = similar

def pattern_summary_line(row: Dict[str, Any]) -> str:
    cat = clean_text(row.get("top_category_30d") or "other")
    timing = clean_text(row.get("timing_style") or "unproven")
    best_window = clean_text(row.get("best_observation_window") or "none")
    hour_txt = hour_bucket_label(row.get("dominant_entry_hour_utc"))
    cat_wr = safe_float(row.get("top_category_win_rate_30d"), 0.0)
    parts = [f"category={cat}", f"cat_wr={cat_wr:.1%}", f"entry_hour={hour_txt}", f"timing={timing}", f"best_window={best_window}"]
    obs24 = safe_int(row.get("obs_sample_24h"), 0)
    if obs24 > 0:
        parts.append(f"obs24={safe_float(row.get('obs_success_rate_24h'), 0.0):.1%}")
    obs1 = safe_int(row.get("obs_sample_1h"), 0)
    if obs1 > 0:
        parts.append(f"obs1={safe_float(row.get('obs_success_rate_1h'), 0.0):.1%}")
    parts.append(f"cluster={clean_text(row.get('cluster_label') or 'none')}")
    return "Pattern: " + " | ".join(parts)


# =========================================================
# Wallet discovery
# =========================================================
def discover_candidate_wallets(leaderboard_limit: Optional[int] = None, active_market_limit: Optional[int] = None, holders_per_market: Optional[int] = None, max_candidate_wallets: Optional[int] = None) -> Tuple[List[Dict[str, Any]], Dict[str, Any]]:
    candidates: Dict[str, Dict[str, Any]] = {}
    stats = {
        "leaderboard_wallets": 0,
        "active_markets": 0,
        "holder_wallets": 0,
        "unique_candidate_wallets": 0,
    }

    leaderboard_limit = leaderboard_limit or LEADERBOARD_LIMIT
    active_market_limit = active_market_limit or ACTIVE_MARKET_LIMIT
    holders_per_market = holders_per_market or HOLDERS_PER_MARKET
    max_candidate_wallets = max_candidate_wallets or MAX_CANDIDATE_WALLETS

    for row in fetch_leaderboard_wallets(leaderboard_limit):
        wallet = row["wallet"]
        base = candidates.setdefault(
            wallet,
            {
                "wallet": wallet,
                "sources": [],
                "leaderboard_rank": None,
                "leaderboard_pnl": 0.0,
                "leaderboard_vol": 0.0,
                "username": "",
                "holder_markets": [],
            },
        )
        base["sources"].append("leaderboard")
        base["leaderboard_rank"] = row.get("leaderboard_rank")
        base["leaderboard_pnl"] = row.get("leaderboard_pnl", 0.0)
        base["leaderboard_vol"] = row.get("leaderboard_vol", 0.0)
        if row.get("username"):
            base["username"] = row["username"]
    stats["leaderboard_wallets"] = len(candidates)

    active_markets = fetch_active_markets(active_market_limit)
    if EXCLUDE_SPORTS_WALLETS:
        active_markets = [m for m in active_markets if not is_sports_row(m)]
    stats["active_markets"] = len(active_markets)
    for market in active_markets:
        holders = fetch_top_holders_for_market(market, holders_per_market)
        stats["holder_wallets"] += len(holders)
        for row in holders:
            wallet = row["wallet"]
            base = candidates.setdefault(
                wallet,
                {
                    "wallet": wallet,
                    "sources": [],
                    "leaderboard_rank": None,
                    "leaderboard_pnl": 0.0,
                    "leaderboard_vol": 0.0,
                    "username": "",
                    "holder_markets": [],
                },
            )
            base["sources"].append("holders")
            base["holder_markets"].append(
                {
                    "slug": row.get("market_slug"),
                    "question": row.get("market_question"),
                    "size": row.get("holder_size", 0.0),
                }
            )
            if len(base["holder_markets"]) > 5:
                base["holder_markets"] = base["holder_markets"][:5]

    deduped = list(candidates.values())
    deduped.sort(
        key=lambda x: (
            0 if x.get("leaderboard_rank") in (None, 0) else -1,
            -(x.get("leaderboard_pnl") or 0.0),
            -(x.get("leaderboard_vol") or 0.0),
            -len(x.get("holder_markets") or []),
        )
    )
    stats["unique_candidate_wallets"] = len(deduped)
    return deduped[:max_candidate_wallets], stats


# =========================================================
# Observation helpers
# =========================================================
def normalize_outcome(value: Any) -> str:
    s = clean_text(value).lower()
    if s in {"yes", "y", "true", "1", "long"}:
        return "YES"
    if s in {"no", "n", "false", "0", "short"}:
        return "NO"
    return ""


def normalize_side(value: Any) -> str:
    s = clean_text(value).upper()
    if s in {"BUY", "B", "TAKE"}:
        return "BUY"
    if s in {"SELL", "S", "EXIT"}:
        return "SELL"
    return s


def infer_outcome_from_trade(row: Dict[str, Any]) -> str:
    for key in ["outcome", "outcomeName", "position", "tokenType", "token", "sideToken"]:
        val = normalize_outcome(row.get(key))
        if val:
            return val
    title = clean_text(row.get("title") or row.get("question") or "")
    lower = title.lower()
    if lower.endswith(" yes") or " outcome yes" in lower:
        return "YES"
    if lower.endswith(" no") or " outcome no" in lower:
        return "NO"
    return ""


def infer_entry_price(row: Dict[str, Any]) -> float:
    for key in ["price", "avgPrice", "executionPrice", "rate", "tradePrice"]:
        price = safe_float(row.get(key), 0.0)
        if price > 0:
            return price
    amount = safe_float(row.get("amount"), 0.0)
    shares = safe_float(row.get("size") or row.get("shares"), 0.0)
    if amount > 0 and shares > 0:
        return amount / shares
    return 0.0


def observation_side_price(snapshot: Dict[str, Any], outcome: str) -> float:
    if outcome == "YES":
        return safe_float(snapshot.get("yes_price"), 0.0)
    if outcome == "NO":
        return safe_float(snapshot.get("no_price"), 0.0)
    return 0.0


def make_observation_key(wallet: str, slug: str, condition_id: str, outcome: str, ts: str, price: float) -> str:
    return f"{wallet}|{slug}|{condition_id}|{outcome}|{ts}|{price:.6f}"


def log_candidate_observations(wallet_row: Dict[str, Any]) -> int:
    bucket = clean_text(wallet_row.get("bucket", "")).upper()
    if bucket not in OBS_TRACK_BUCKET_SET:
        return 0

    wallet = wallet_row["wallet"]
    username = wallet_row.get("username", "")
    score = safe_float(wallet_row.get("score"), 0.0)
    cutoff = hours_ago(OBSERVE_RECENT_HOURS)
    trades = fetch_trades(wallet)
    rows_to_insert: List[Tuple[Any, ...]] = []

    for row in trades[:OBSERVE_MAX_TRADES_PER_WALLET * 4]:
        side = normalize_side(row.get("side") or row.get("type") or row.get("action") or "")
        if side and side != "BUY":
            continue
        outcome = infer_outcome_from_trade(row)
        if outcome not in {"YES", "NO"}:
            continue
        ts = parse_ts(row.get("timestamp") or row.get("time") or row.get("createdAt") or row.get("updatedAt"))
        if ts is None or ts < cutoff:
            continue
        entry_price = infer_entry_price(row)
        if entry_price < OBS_MIN_ENTRY_PRICE or entry_price > OBS_MAX_ENTRY_PRICE:
            continue
        slug = clean_text(row.get("slug") or row.get("marketSlug") or row.get("market") or "")
        question = clean_text(row.get("title") or row.get("question") or "")
        condition_id = clean_text(row.get("conditionId") or row.get("marketId") or "")
        if not slug and not condition_id:
            continue
        size = safe_float(row.get("size") or row.get("shares") or row.get("amount"), 0.0)
        source = clean_text(row.get("source") or "trade")
        trade_time = iso_utc(ts)
        unique_key = make_observation_key(wallet, slug, condition_id, outcome, trade_time, entry_price)
        rows_to_insert.append(
            (
                unique_key,
                wallet,
                username,
                bucket,
                score,
                slug,
                question,
                condition_id,
                outcome,
                side or "BUY",
                trade_time,
                entry_price,
                size,
                source,
                iso_utc(now_utc()),
                iso_utc(now_utc()),
            )
        )
        if len(rows_to_insert) >= OBSERVE_MAX_TRADES_PER_WALLET:
            break

    if not rows_to_insert:
        return 0

    conn = get_db()
    inserted = 0
    try:
        cur = conn.cursor()
        cur.executemany(
            """
            INSERT OR IGNORE INTO observed_trades (
                unique_key, wallet, username, bucket, snapshot_score, market_slug, market_question,
                condition_id, outcome, side, trade_time, entry_price, size, source, created_at, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            rows_to_insert,
        )
        inserted = cur.rowcount if cur.rowcount is not None else 0
        conn.commit()
    finally:
        conn.close()
    return max(inserted, 0)


def evaluate_due_observations() -> Dict[str, int]:
    now = now_utc()
    conn = get_db()
    updated = {"one_hour": 0, "six_hour": 0, "twenty_four_hour": 0}
    try:
        cur = conn.cursor()
        rows = cur.execute(
            """
            SELECT * FROM observed_trades
            WHERE status = 'open'
            ORDER BY trade_time ASC
            LIMIT 300
            """
        ).fetchall()

        for row in rows:
            trade_time = parse_ts(row["trade_time"])
            if trade_time is None:
                continue
            age_hours = (now - trade_time).total_seconds() / 3600.0
            snapshot = fetch_market_snapshot(slug=row["market_slug"] or "", condition_id=row["condition_id"] or "")
            if not snapshot:
                continue
            current_price = observation_side_price(snapshot, row["outcome"])
            entry_price = safe_float(row["entry_price"], 0.0)
            if current_price <= 0 or entry_price <= 0:
                continue
            move = (current_price - entry_price) / entry_price
            now_iso = iso_utc(now)

            if age_hours >= 1 and row["price_1h"] is None:
                cur.execute(
                    """
                    UPDATE observed_trades
                    SET price_1h = ?, move_1h = ?, success_1h = ?, updated_at = ?
                    WHERE id = ?
                    """,
                    (current_price, move, 1 if move >= OBS_SUCCESS_THRESHOLD else 0, now_iso, row["id"]),
                )
                updated["one_hour"] += 1

            if age_hours >= 6 and row["price_6h"] is None:
                cur.execute(
                    """
                    UPDATE observed_trades
                    SET price_6h = ?, move_6h = ?, success_6h = ?, updated_at = ?
                    WHERE id = ?
                    """,
                    (current_price, move, 1 if move >= OBS_SUCCESS_THRESHOLD else 0, now_iso, row["id"]),
                )
                updated["six_hour"] += 1

            if age_hours >= 24 and row["price_24h"] is None:
                cur.execute(
                    """
                    UPDATE observed_trades
                    SET price_24h = ?, move_24h = ?, success_24h = ?, status = 'closed', updated_at = ?
                    WHERE id = ?
                    """,
                    (current_price, move, 1 if move >= OBS_SUCCESS_THRESHOLD else 0, now_iso, row["id"]),
                )
                updated["twenty_four_hour"] += 1
        conn.commit()
    finally:
        conn.close()
    return updated



def fetch_observation_stats(wallet: str) -> Dict[str, Any]:
    conn = get_db()
    try:
        cur = conn.cursor()
        row = cur.execute(
            """
            SELECT
                COUNT(*) AS observed_total,
                SUM(CASE WHEN success_1h IS NOT NULL THEN 1 ELSE 0 END) AS sample_1h,
                SUM(CASE WHEN success_6h IS NOT NULL THEN 1 ELSE 0 END) AS sample_6h,
                SUM(CASE WHEN success_24h IS NOT NULL THEN 1 ELSE 0 END) AS sample_24h,
                AVG(CASE WHEN move_1h IS NOT NULL THEN move_1h END) AS avg_move_1h,
                AVG(CASE WHEN move_6h IS NOT NULL THEN move_6h END) AS avg_move_6h,
                AVG(CASE WHEN move_24h IS NOT NULL THEN move_24h END) AS avg_move_24h,
                AVG(CASE WHEN success_1h IS NOT NULL THEN success_1h END) AS success_rate_1h,
                AVG(CASE WHEN success_6h IS NOT NULL THEN success_6h END) AS success_rate_6h,
                AVG(CASE WHEN success_24h IS NOT NULL THEN success_24h END) AS success_rate_24h
            FROM observed_trades
            WHERE wallet = ?
            """,
            (wallet,),
        ).fetchone()
        if not row:
            return {}
        out = {k: row[k] for k in row.keys()}
        cat_rows = cur.execute(
            """
            SELECT market_question, market_slug
            FROM observed_trades
            WHERE wallet = ?
            """,
            (wallet,),
        ).fetchall()
        counts = defaultdict(int)
        for r in cat_rows:
            counts[categorize_text(clean_text((r["market_question"] or "") + " " + (r["market_slug"] or "")))] += 1
        out["observed_categories"] = top_categories(dict(counts), limit=3)
        return out
    finally:
        conn.close()


def top_observed_wallets(limit: int = 10) -> List[Dict[str, Any]]:
    conn = get_db()
    try:
        cur = conn.cursor()
        rows = cur.execute(
            """
            SELECT
                wallet,
                MAX(username) AS username,
                COUNT(*) AS observed_total,
                SUM(CASE WHEN success_24h IS NOT NULL THEN 1 ELSE 0 END) AS sample_24h,
                AVG(CASE WHEN success_24h IS NOT NULL THEN success_24h END) AS success_rate_24h,
                AVG(CASE WHEN move_24h IS NOT NULL THEN move_24h END) AS avg_move_24h,
                MAX(snapshot_score) AS max_snapshot_score
            FROM observed_trades
            GROUP BY wallet
            HAVING sample_24h > 0
            ORDER BY success_rate_24h DESC, sample_24h DESC, avg_move_24h DESC
            LIMIT ?
            """,
            (limit,),
        ).fetchall()
        return [{k: row[k] for k in row.keys()} for row in rows]
    finally:
        conn.close()


# =========================================================
# Wallet grading
# =========================================================
def realized_return_from_closed_position(row: Dict[str, Any]) -> float:
    realized_pnl = safe_float(row.get("realizedPnl") or row.get("pnl"), 0.0)
    total_bought = safe_float(row.get("totalBought") or row.get("size") or row.get("amount"), 0.0)
    avg_price = safe_float(row.get("avgPrice") or row.get("avg_price"), 0.0)
    denom = total_bought
    if denom <= 0 and avg_price > 0:
        denom = avg_price
    if denom <= 0:
        return 0.0
    return realized_pnl / denom


def bucket_score(wallet_metrics: Dict[str, Any]) -> float:
    weighted_return = wallet_metrics.get("weighted_return_30d", 0.0)
    win_rate = wallet_metrics.get("win_rate_30d", 0.0)
    consistency = wallet_metrics.get("consistency_ratio_30d", 0.0)
    recent_trades = wallet_metrics.get("recent_trades_7d", 0)
    intraday = wallet_metrics.get("intraday_roundtrips_30d", 0)
    sample = wallet_metrics.get("closed_positions_30d", 0)
    obs_sample_24h = safe_int(wallet_metrics.get("obs_sample_24h"), 0)
    obs_success_24h = safe_float(wallet_metrics.get("obs_success_rate_24h"), 0.0)

    ret_score = clamp(weighted_return / 0.40, 0.0, 1.0) * 30.0
    win_score = clamp((win_rate - 0.50) / 0.30, 0.0, 1.0) * 15.0
    consistency_score = clamp((consistency - 0.40) / 0.40, 0.0, 1.0) * 15.0
    activity_score = clamp(recent_trades / 12.0, 0.0, 1.0) * 10.0
    intraday_score = clamp(intraday / 5.0, 0.0, 1.0) * 10.0
    sample_score = clamp(sample / 20.0, 0.0, 1.0) * 10.0
    obs_score = 0.0
    if obs_sample_24h > 0:
        obs_score = clamp(obs_success_24h / 0.75, 0.0, 1.0) * 10.0

    score = ret_score + win_score + consistency_score + activity_score + intraday_score + sample_score + obs_score

    # realism penalties
    if sample < 15 and win_rate >= 1.0:
        score -= 8.0
    if sample < 15 and consistency >= 1.0:
        score -= 6.0
    if safe_int(wallet_metrics.get("trades_30d"), 0) >= 100:
        score -= 4.0
        wallet_metrics["trade_count_capped"] = True
    if sample > 0 and wallet_metrics.get("losing_positions_30d", 0) == 0:
        score -= 6.0
        wallet_metrics["no_losers_seen"] = True
    if obs_sample_24h >= OBS_MIN_SAMPLE_24H:
        if obs_success_24h >= OBS_PROMOTE_SUCCESS_RATE:
            score += 6.0
        elif obs_success_24h <= OBS_DEMOTE_SUCCESS_RATE:
            score -= 8.0
    return round(clamp(score, 0.0, 100.0), 2)


def classify_bucket(wallet_metrics: Dict[str, Any]) -> str:
    score = wallet_metrics.get("score", 0.0)
    obs_sample_24h = safe_int(wallet_metrics.get("obs_sample_24h"), 0)
    obs_success_24h = safe_float(wallet_metrics.get("obs_success_rate_24h"), 0.0)

    if obs_sample_24h >= OBS_MIN_SAMPLE_24H and obs_success_24h <= OBS_DEMOTE_SUCCESS_RATE:
        return "WATCH CLOSELY" if score >= WATCH_BUCKET_MIN_SCORE else "REJECT"
    if score >= TEST_FIRST_MIN_SCORE:
        return "TEST FIRST"
    if score >= WATCH_BUCKET_MIN_SCORE:
        return "WATCH CLOSELY"
    return "REJECT"


def reason_strings(metrics: Dict[str, Any]) -> Tuple[List[str], List[str]]:
    good: List[str] = []
    weak: List[str] = []

    if metrics.get("weighted_return_30d", 0.0) >= MIN_WEIGHTED_RETURN_30D:
        good.append(f"30d weighted return {metrics['weighted_return_30d']:.1%}")
    else:
        weak.append(f"30d weighted return only {metrics.get('weighted_return_30d', 0.0):.1%}")

    if metrics.get("win_rate_30d", 0.0) >= MIN_WIN_RATE_30D:
        good.append(f"win rate {metrics['win_rate_30d']:.1%}")
    else:
        weak.append(f"win rate {metrics.get('win_rate_30d', 0.0):.1%}")

    if metrics.get("consistency_ratio_30d", 0.0) >= MIN_CONSISTENCY_RATIO:
        good.append(f"consistency {metrics['consistency_ratio_30d']:.1%} of closes above 20%")
    else:
        weak.append(f"consistency only {metrics.get('consistency_ratio_30d', 0.0):.1%} above 20%")

    if metrics.get("recent_trades_7d", 0) >= MIN_RECENT_TRADES_7D:
        good.append(f"recent activity {metrics['recent_trades_7d']} trades in 7d")
    else:
        weak.append(f"recent activity low at {metrics.get('recent_trades_7d', 0)} trades in 7d")

    if metrics.get("intraday_roundtrips_30d", 0) >= MIN_INTRADAY_SIGNALS:
        good.append(f"intraday signals {metrics['intraday_roundtrips_30d']}")
    else:
        weak.append("no strong intraday signal yet")

    obs_sample_24h = safe_int(metrics.get("obs_sample_24h"), 0)
    if obs_sample_24h > 0:
        good.append(f"24h observed success {safe_float(metrics.get('obs_success_rate_24h'), 0.0):.1%} on {obs_sample_24h} samples")
    else:
        weak.append("no 24h observation sample yet")

    top_cat = clean_text(metrics.get("top_category_30d") or "")
    if top_cat and top_cat != "other":
        good.append(f"best category {top_cat}")

    timing = clean_text(metrics.get("timing_style") or "")
    if timing and timing != "unproven":
        good.append(f"timing style {timing}")

    if metrics.get("trade_count_capped"):
        weak.append("trade count hit cap, so activity may be understated")
    sports_total = safe_int(metrics.get("sports_closed_positions_30d"), 0) + safe_int(metrics.get("sports_trades_30d"), 0) + safe_int(metrics.get("sports_current_positions"), 0)
    if sports_total > 0:
        weak.append(f"sports exposure ratios c={safe_float(metrics.get('sports_ratio_closed'), 0.0):.0%} t={safe_float(metrics.get('sports_ratio_trades'), 0.0):.0%}")
    if metrics.get("no_losers_seen"):
        weak.append("no losers seen in sample, so perfection may be overstated")

    return good[:4], weak[:4]


def evaluate_wallet(candidate: Dict[str, Any]) -> Dict[str, Any]:
    wallet = candidate["wallet"]
    cutoff_30d = days_ago(LOOKBACK_DAYS)
    cutoff_7d = days_ago(RECENT_DAYS)

    closed_positions = fetch_closed_positions(wallet)
    trades = fetch_trades(wallet)
    current_positions = fetch_current_positions(wallet)

    sports_rows_30d = 0
    sports_trade_rows_30d = 0
    sports_current_positions = 0
    closed_category_counts: Dict[str, int] = defaultdict(int)
    trade_category_counts: Dict[str, int] = defaultdict(int)
    current_category_counts: Dict[str, int] = defaultdict(int)
    holder_category_counts: Dict[str, int] = defaultdict(int)

    closed_30d: List[Dict[str, Any]] = []
    trade_30d: List[Dict[str, Any]] = []
    recent_trades_7d = 0

    for row in closed_positions:
        ts = parse_ts(row.get("timestamp") or row.get("time") or row.get("updatedAt") or row.get("closedAt"))
        if ts is None or ts < cutoff_30d:
            continue
        closed_30d.append(row)
        closed_category_counts[categorize_row(row)] += 1
        if EXCLUDE_SPORTS_WALLETS and is_sports_row(row):
            sports_rows_30d += 1

    for row in trades:
        ts = parse_ts(row.get("timestamp") or row.get("time") or row.get("createdAt") or row.get("updatedAt"))
        if ts is None:
            continue
        if ts >= cutoff_30d:
            trade_30d.append(row)
            trade_category_counts[categorize_row(row)] += 1
            if EXCLUDE_SPORTS_WALLETS and is_sports_row(row):
                sports_trade_rows_30d += 1
        if ts >= cutoff_7d:
            recent_trades_7d += 1

    if EXCLUDE_SPORTS_WALLETS:
        for row in current_positions:
            current_category_counts[categorize_row(row)] += 1
            if is_sports_row(row):
                sports_current_positions += 1

    weighted_pnl = 0.0
    weighted_cost = 0.0
    positive_positions = 0
    consistency_hits = 0
    losing_positions = 0
    returns: List[float] = []

    for row in closed_30d:
        realized_pnl = safe_float(row.get("realizedPnl") or row.get("pnl"), 0.0)
        total_bought = safe_float(row.get("totalBought") or row.get("size") or row.get("amount"), 0.0)
        r = realized_return_from_closed_position(row)
        returns.append(r)
        weighted_pnl += realized_pnl
        weighted_cost += max(total_bought, 0.0)
        if realized_pnl > 0:
            positive_positions += 1
        elif realized_pnl < 0:
            losing_positions += 1
        if r >= 0.20:
            consistency_hits += 1

    weighted_return = (weighted_pnl / weighted_cost) if weighted_cost > 0 else 0.0
    win_rate = (positive_positions / len(closed_30d)) if closed_30d else 0.0
    consistency_ratio = (consistency_hits / len(closed_30d)) if closed_30d else 0.0
    avg_return = (sum(returns) / len(returns)) if returns else 0.0
    median_return = sorted(returns)[len(returns) // 2] if returns else 0.0

    by_slug_day: Dict[Tuple[str, str], Dict[str, int]] = defaultdict(lambda: {"BUY": 0, "SELL": 0})
    for row in trade_30d:
        ts = parse_ts(row.get("timestamp") or row.get("time") or row.get("createdAt") or row.get("updatedAt"))
        if ts is None:
            continue
        slug = clean_text(row.get("slug") or row.get("marketSlug") or row.get("title") or row.get("conditionId"))
        key = (slug, ts.strftime("%Y-%m-%d"))
        side = normalize_side(row.get("side") or row.get("type") or row.get("action") or "")
        if side not in ("BUY", "SELL"):
            continue
        by_slug_day[key][side] += 1
    intraday_roundtrips = sum(1 for v in by_slug_day.values() if v["BUY"] > 0 and v["SELL"] > 0)

    for m in (candidate.get("holder_markets") or []):
        holder_category_counts[categorize_text(clean_text(m.get("slug") or m.get("question") or ""))] += 1

    top_category = dominant_category(dict(closed_category_counts or trade_category_counts or current_category_counts or holder_category_counts))
    sports_ratio_closed = safe_ratio(sports_rows_30d, len(closed_30d))
    sports_ratio_trades = safe_ratio(sports_trade_rows_30d, len(trade_30d))
    sports_ratio_current = safe_ratio(sports_current_positions, len(current_positions))
    holder_sports = holder_category_counts.get("sports", 0)
    sports_ratio_holder = safe_ratio(holder_sports, sum(holder_category_counts.values()))

    obs = fetch_observation_stats(wallet)
    metrics: Dict[str, Any] = {
        "wallet": wallet,
        "username": candidate.get("username", ""),
        "sources": sorted(set(candidate.get("sources") or [])),
        "leaderboard_rank": candidate.get("leaderboard_rank"),
        "leaderboard_pnl": candidate.get("leaderboard_pnl", 0.0),
        "leaderboard_vol": candidate.get("leaderboard_vol", 0.0),
        "holder_markets": candidate.get("holder_markets") or [],
        "closed_positions_30d": len(closed_30d),
        "trades_30d": len(trade_30d),
        "recent_trades_7d": recent_trades_7d,
        "current_positions": len(current_positions),
        "weighted_return_30d": weighted_return,
        "avg_return_30d": avg_return,
        "median_return_30d": median_return,
        "realized_pnl_30d": weighted_pnl,
        "gross_cost_30d": weighted_cost,
        "win_rate_30d": win_rate,
        "consistency_ratio_30d": consistency_ratio,
        "intraday_roundtrips_30d": intraday_roundtrips,
        "losing_positions_30d": losing_positions,
        "sports_closed_positions_30d": sports_rows_30d,
        "sports_trades_30d": sports_trade_rows_30d,
        "sports_current_positions": sports_current_positions,
        "sports_ratio_closed": sports_ratio_closed,
        "sports_ratio_trades": sports_ratio_trades,
        "sports_ratio_current": sports_ratio_current,
        "sports_ratio_holder": sports_ratio_holder,
        "top_category_30d": top_category,
        "top_categories_30d": top_categories(dict(closed_category_counts or trade_category_counts or current_category_counts or holder_category_counts)),
        "top_category_closed_count_30d": top_cat_count,
        "top_category_win_rate_30d": top_category_win_rate,
        "top_category_avg_return_30d": top_category_avg_return,
        "dominant_entry_hour_utc": dominant_entry_hour,
        "active_entry_hours_utc": active_entry_hours,
        "obs_sample_1h": safe_int(obs.get("sample_1h"), 0),
        "obs_sample_6h": safe_int(obs.get("sample_6h"), 0),
        "obs_sample_24h": safe_int(obs.get("sample_24h"), 0),
        "obs_success_rate_1h": safe_float(obs.get("success_rate_1h"), 0.0),
        "obs_success_rate_6h": safe_float(obs.get("success_rate_6h"), 0.0),
        "obs_success_rate_24h": safe_float(obs.get("success_rate_24h"), 0.0),
        "obs_avg_move_24h": safe_float(obs.get("avg_move_24h"), 0.0),
        "observed_total": safe_int(obs.get("observed_total"), 0),
        "observed_categories": obs.get("observed_categories") or [],
    }
    metrics["best_observation_window"] = best_observation_window(metrics)
    metrics["timing_style"] = timing_style(metrics)
    metrics["cluster_label"] = cluster_label(metrics)
    metrics["score"] = bucket_score(metrics)
    metrics["bucket"] = classify_bucket(metrics)
    metrics["good_reasons"], metrics["weak_reasons"] = reason_strings(metrics)

    sports_ok = (
        not EXCLUDE_SPORTS_WALLETS
        or (
            sports_ratio_closed <= SPORTS_RATIO_CLOSED_MAX
            and sports_ratio_trades <= SPORTS_RATIO_TRADES_MAX
            and sports_ratio_current <= SPORTS_RATIO_CURRENT_MAX
            and sports_ratio_holder <= SPORTS_RATIO_HOLDER_HINT_MAX
        )
    )

    passes = (
        metrics["closed_positions_30d"] >= MIN_CLOSED_POSITIONS_30D
        and metrics["trades_30d"] >= MIN_TRADES_30D
        and metrics["weighted_return_30d"] >= MIN_WEIGHTED_RETURN_30D
        and metrics["win_rate_30d"] >= MIN_WIN_RATE_30D
        and metrics["consistency_ratio_30d"] >= MIN_CONSISTENCY_RATIO
        and metrics["realized_pnl_30d"] >= MIN_REALIZED_PNL_30D
        and metrics["recent_trades_7d"] >= MIN_RECENT_TRADES_7D
        and sports_ok
    )
    metrics["passes_filters"] = passes
    return metrics


# =========================================================
# Formatting
# =========================================================
def display_name(row: Dict[str, Any]) -> str:
    username = clean_text(row.get("username") or "")
    if username:
        return username
    return row.get("wallet", "") or short_wallet(row.get("wallet", ""))


def row_discovery_text(row: Dict[str, Any]) -> str:
    sources = row.get("sources") or []
    holder_hint = "none"
    holder_markets = row.get("holder_markets") or []
    if holder_markets:
        holder_hint = clean_text(holder_markets[0].get("slug") or holder_markets[0].get("question") or "none") or "none"
    return f"Discovery: {','.join(sources) if sources else 'unknown'} | holder_hint={holder_hint}"


def format_wallet_row(row: Dict[str, Any]) -> List[str]:
    wallet = clean_text(row.get("wallet") or "")
    profile_url = f"https://polymarket.com/profile/{wallet}" if wallet else ""
    username = clean_text(row.get("username") or "")
    lines = [
        f"Wallet: {display_name(row)}",
        f"Username: {username or 'none'}",
        f"Address: {wallet or 'unknown'}",
        f"Profile: {profile_url or 'none'}",
        f"Bucket: {row.get('bucket', 'UNKNOWN')} | Score: {safe_float(row.get('score'), 0.0):.1f}",
        f"30d: pnl={safe_float(row.get('realized_pnl_30d'), 0.0):.2f} | weighted_ret={safe_float(row.get('weighted_return_30d'), 0.0):.1%} | avg_ret={safe_float(row.get('avg_return_30d'), 0.0):.1%}",
        f"30d sample: closed={safe_int(row.get('closed_positions_30d'), 0)} | trades={safe_int(row.get('trades_30d'), 0)} | wins={safe_float(row.get('win_rate_30d'), 0.0):.1%} | 20%+ closes={safe_float(row.get('consistency_ratio_30d'), 0.0):.1%}",
        f"Recent: trades_7d={safe_int(row.get('recent_trades_7d'), 0)} | intraday_signals={safe_int(row.get('intraday_roundtrips_30d'), 0)} | current_positions={safe_int(row.get('current_positions'), 0)}",
        f"Closed-trade trend: {category_trend_summary(row)} | dominant_entry_hour={hour_bucket_label(row.get('dominant_entry_hour_utc'))}",
    ]
    obs_sample_24h = safe_int(row.get("obs_sample_24h"), 0)
    if obs_sample_24h > 0:
        lines.append(
            f"Observed: 24h success={safe_float(row.get('obs_success_rate_24h'), 0.0):.1%} on {obs_sample_24h} samples | avg_24h_move={safe_float(row.get('obs_avg_move_24h'), 0.0):.1%}"
        )
    lines.append(pattern_summary_line(row))
    similar = row.get("similar_wallets") or []
    if similar:
        lines.append("Similar: " + " | ".join([f"{clean_text(x.get('username') or x.get('wallet') or '')} ({clean_text(x.get('cluster_label') or ((x.get('top_category_30d') or 'other') + ':' + (x.get('timing_style') or 'unproven')) )})" for x in similar]))
    lines.append(f"Why: {'; '.join(row.get('good_reasons') or ['none'])}")
    lines.append(f"Weakness: {'; '.join(row.get('weak_reasons') or ['none'])}")
    lines.append(row_discovery_text(row))
    return lines


def latest_cached_scan_text() -> str:
    with state_lock:
        history = runtime_state.get("scan_history", [])
    if not history:
        return "Latest cached candidates\nNone yet"
    last = history[-1]
    rows = last.get("top_wallets") or []
    lines = [
        "Latest cached candidates while fresh scan runs",
        f"script_version={SCRIPT_VERSION}",
        f"cached_timestamp={clean_text(last.get('timestamp') or '')}",
    ]
    if rows:
        for row in rows[:TOP_WALLETS_PER_SCAN]:
            wallet = clean_text(row.get("wallet") or "")
            username = clean_text(row.get("username") or "none")
            score = safe_float(row.get("score"), 0.0)
            bucket = clean_text(row.get("bucket") or "UNKNOWN")
            lines.append(f"{display_name(row)} | username={username} | {wallet} | bucket={bucket} | score={score:.1f} | category={clean_text(row.get('top_category_30d') or 'other')} | profile=https://polymarket.com/profile/{wallet}")
    else:
        lines.append("None")
    return "\n".join(lines).strip()


def format_scan_text(result: Dict[str, Any], manual: bool = False) -> str:
    header = "Manual wallet scan" if manual else "Auto wallet scan"
    lines = [
        header,
        f"script_version={SCRIPT_VERSION}",
        f"evaluated_wallets={result.get('evaluated_wallets', 0)} | passing_wallets={result.get('passing_wallets', 0)} | evaluation_errors={result.get('evaluation_errors', 0)}",
        f"leaderboard_wallets={result.get('leaderboard_wallets', 0)} | active_markets={result.get('active_markets', 0)} | holder_wallets={result.get('holder_wallets', 0)} | unique_candidates={result.get('unique_candidate_wallets', 0)}",
        f"observations_logged={result.get('observations_logged', 0)} | obs_eval_1h={result.get('obs_eval_1h', 0)} | obs_eval_6h={result.get('obs_eval_6h', 0)} | obs_eval_24h={result.get('obs_eval_24h', 0)}",
        f"scan_runtime_seconds={safe_float(result.get('scan_runtime_seconds'), 0.0):.2f} | time_budget_hit={str(bool(result.get('time_budget_hit', False))).lower()}",
        "",
        "Wallets to test first",
    ]
    test_first = result.get("test_first") or []
    watch = result.get("watch_closely") or []

    fallback = []
    if not test_first and not watch and safe_int(result.get("passing_wallets"), 0) > 0:
        evaluated = result.get("evaluated") or []
        fallback = [x for x in evaluated if x.get("passes_filters")][:TOP_WALLETS_PER_SCAN]
        test_first = fallback

    if test_first:
        for row in test_first:
            lines.extend(format_wallet_row(row))
            lines.append("")
    else:
        lines.append("None")

    lines.append("Wallets to watch closely")
    if watch and not fallback:
        for row in watch:
            lines.extend(format_wallet_row(row))
            lines.append("")
    else:
        lines.append("None")
    return "\n".join(lines).strip()


def format_group_text(group_payload: Dict[str, Any]) -> str:
    lines = [
        "3 hour wallet summary",
        f"script_version={SCRIPT_VERSION}",
        f"scans_in_window={group_payload.get('scan_count', 0)} | top_candidates_seen={group_payload.get('unique_wallets_seen', 0)}",
        "",
        "Highest recurring candidates",
    ]
    top = group_payload.get("top_group_wallets") or []
    if top:
        for row in top:
            lines.append(
                f"{display_name(row)} | username={clean_text(row.get('username') or 'none')} | {clean_text(row.get('wallet') or '')} | seen={safe_int(row.get('seen_count'), 0)} | best_score={safe_float(row.get('best_score'), 0.0):.1f} | best_bucket={row.get('best_bucket', 'UNKNOWN')} | category={clean_text(row.get('top_category_30d') or 'other')} | timing={clean_text(row.get('timing_style') or 'unproven')} | profile=https://polymarket.com/profile/{clean_text(row.get('wallet') or '')}"
            )
    else:
        lines.append("None")

    lines.extend(["", "Observed 24h leaders"])
    observed = group_payload.get("top_observed_wallets") or []
    if observed:
        for row in observed:
            lines.append(
                f"{display_name(row)} | username={clean_text(row.get('username') or 'none')} | {clean_text(row.get('wallet') or '')} | 24h_success={safe_float(row.get('success_rate_24h'), 0.0):.1%} | sample={safe_int(row.get('sample_24h'), 0)} | avg_24h_move={safe_float(row.get('avg_move_24h'), 0.0):.1%} | profile=https://polymarket.com/profile/{clean_text(row.get('wallet') or '')}"
            )
    else:
        lines.append("None")
    return "\n".join(lines).strip()


def health_text() -> str:
    session = runtime_state.get("session_summary", {})
    observed = top_observed_wallets(limit=5)
    lines = [
        "Wallet intel health",
        f"script_version={SCRIPT_VERSION}",
        f"scan_every_seconds={SCAN_EVERY_SECONDS}",
        f"group_window_seconds={GROUP_WINDOW_SECONDS}",
        f"scans={safe_int(session.get('scans'), 0)} | wallets_evaluated={safe_int(session.get('wallets_evaluated'), 0)} | wallets_passing={safe_int(session.get('wallets_passing'), 0)}",
        f"observations_logged={safe_int(session.get('observations_logged'), 0)} | observations_evaluated={safe_int(session.get('observations_evaluated'), 0)}",
        f"last_group_top_count={safe_int(session.get('last_group_top_count'), 0)} | observed_wallets={len(observed)}",
    ]
    if observed:
        lines.append("Observed 24h leaders")
        for row in observed:
            lines.append(
                f"{display_name(row)} | username={clean_text(row.get('username') or 'none')} | {clean_text(row.get('wallet') or '')} | success_24h={safe_float(row.get('success_rate_24h'), 0.0):.1%} | sample={safe_int(row.get('sample_24h'), 0)} | profile=https://polymarket.com/profile/{clean_text(row.get('wallet') or '')}"
            )
    return "\n".join(lines)


# =========================================================
# Scan engine
# =========================================================
def scan_once(manual_quick: bool = False) -> Dict[str, Any]:
    started = utc_ts()
    deadline_ts = started + MANUAL_SCAN_DEADLINE_SECONDS if manual_quick else None

    if manual_quick:
        discovery_rows, discovery_stats = discover_candidate_wallets(
            leaderboard_limit=MANUAL_LEADERBOARD_LIMIT,
            active_market_limit=MANUAL_ACTIVE_MARKET_LIMIT,
            holders_per_market=MANUAL_HOLDERS_PER_MARKET,
            max_candidate_wallets=MANUAL_MAX_CANDIDATE_WALLETS,
        )
    else:
        discovery_rows, discovery_stats = discover_candidate_wallets()

    evaluated: List[Dict[str, Any]] = []
    errors = 0
    time_budget_hit = False

    for idx, candidate in enumerate(discovery_rows):
        if deadline_ts and utc_ts() >= deadline_ts:
            time_budget_hit = True
            break
        try:
            evaluated.append(evaluate_wallet(candidate))
        except Exception:
            errors += 1

        if manual_quick:
            passes = [x for x in evaluated if x.get("passes_filters")]
            if len(evaluated) >= 12 and len(passes) >= min(6, TOP_WALLETS_PER_SCAN):
                break
            if len(evaluated) >= MANUAL_MAX_CANDIDATE_WALLETS:
                break

    evaluated.sort(
        key=lambda x: (
            x.get("passes_filters", False),
            x.get("score", 0.0),
            x.get("obs_success_rate_24h", 0.0),
            x.get("weighted_return_30d", 0.0),
            x.get("recent_trades_7d", 0),
        ),
        reverse=True,
    )

    annotate_similar_wallets(evaluated)

    test_first = [x for x in evaluated if x.get("bucket") == "TEST FIRST" and x.get("passes_filters")][:TOP_WALLETS_PER_SCAN]
    watch_closely = [x for x in evaluated if x.get("bucket") == "WATCH CLOSELY" and x.get("passes_filters")][:TOP_WALLETS_PER_SCAN]
    rejects = [x for x in evaluated if not x.get("passes_filters")][:TOP_WALLETS_PER_SCAN]

    observations_logged = 0
    for row in test_first + watch_closely:
        try:
            observations_logged += log_candidate_observations(row)
        except Exception:
            continue

    obs_updates = evaluate_due_observations()

    stats = {
        **discovery_stats,
        "evaluated_wallets": len(evaluated),
        "passing_wallets": len([x for x in evaluated if x.get("passes_filters")]),
        "test_first_count": len(test_first),
        "watch_count": len(watch_closely),
        "reject_count": len(rejects),
        "evaluation_errors": errors,
        "observations_logged": observations_logged,
        "obs_eval_1h": obs_updates.get("one_hour", 0),
        "obs_eval_6h": obs_updates.get("six_hour", 0),
        "obs_eval_24h": obs_updates.get("twenty_four_hour", 0),
        "evaluated": evaluated,
        "test_first": test_first,
        "watch_closely": watch_closely,
        "rejects": rejects,
        "time_budget_hit": time_budget_hit,
        "scan_runtime_seconds": round(utc_ts() - started, 2),
        "timestamp": iso_utc(now_utc()),
    }
    return stats


def update_runtime_after_scan(result: Dict[str, Any]) -> None:
    with state_lock:
        runtime_state["scan_history"].append(
            {
                "timestamp": result.get("timestamp"),
                "top_wallets": [
                    {
                        "wallet": row.get("wallet"),
                        "username": row.get("username"),
                        "score": row.get("score"),
                        "bucket": row.get("bucket"),
                        "top_category_30d": row.get("top_category_30d"),
                        "timing_style": row.get("timing_style"),
                    }
                    for row in (
                        (result.get("test_first") or [])
                        + (result.get("watch_closely") or [])
                        + ([x for x in (result.get("evaluated") or []) if x.get("passes_filters")][:TOP_WALLETS_PER_SCAN] if not ((result.get("test_first") or []) or (result.get("watch_closely") or [])) else [])
                    )
                ],
            }
        )
        runtime_state["scan_history"] = runtime_state["scan_history"][-36:]
        session = runtime_state.setdefault("session_summary", {})
        session["scans"] = safe_int(session.get("scans"), 0) + 1
        session["wallets_evaluated"] = safe_int(session.get("wallets_evaluated"), 0) + safe_int(result.get("evaluated_wallets"), 0)
        session["wallets_passing"] = safe_int(session.get("wallets_passing"), 0) + safe_int(result.get("passing_wallets"), 0)
        session["last_scan_top_count"] = len((result.get("test_first") or []) + (result.get("watch_closely") or []))
        session["observations_logged"] = safe_int(session.get("observations_logged"), 0) + safe_int(result.get("observations_logged"), 0)
        session["observations_evaluated"] = safe_int(session.get("observations_evaluated"), 0) + safe_int(result.get("obs_eval_1h"), 0) + safe_int(result.get("obs_eval_6h"), 0) + safe_int(result.get("obs_eval_24h"), 0)
        session["last_observed_success_wallets"] = len(top_observed_wallets(limit=10))
        runtime_state["last_health"] = {
            "last_scan_at": result.get("timestamp"),
            "last_scan_evaluated": result.get("evaluated_wallets", 0),
            "last_scan_passing": result.get("passing_wallets", 0),
        }
        save_state()


def build_group_payload() -> Dict[str, Any]:
    with state_lock:
        history = runtime_state.get("scan_history", [])
    cutoff = now_utc() - timedelta(seconds=GROUP_WINDOW_SECONDS)
    recent = []
    for item in history:
        ts = parse_ts(item.get("timestamp"))
        if ts and ts >= cutoff:
            recent.append(item)

    wallet_map: Dict[str, Dict[str, Any]] = {}
    for item in recent:
        for row in item.get("top_wallets", []):
            wallet = row.get("wallet")
            if not wallet:
                continue
            base = wallet_map.setdefault(
                wallet,
                {
                    "wallet": wallet,
                    "username": row.get("username", ""),
                    "seen_count": 0,
                    "best_score": 0.0,
                    "best_bucket": "",
                    "top_category_30d": row.get("top_category_30d", ""),
                    "timing_style": row.get("timing_style", ""),
                },
            )
            base["seen_count"] += 1
            if safe_float(row.get("score"), 0.0) > safe_float(base.get("best_score"), 0.0):
                base["best_score"] = safe_float(row.get("score"), 0.0)
                base["best_bucket"] = row.get("bucket", "")
            if row.get("username"):
                base["username"] = row.get("username")
            if row.get("top_category_30d"):
                base["top_category_30d"] = row.get("top_category_30d")
            if row.get("timing_style"):
                base["timing_style"] = row.get("timing_style")

    top_group_wallets = sorted(
        wallet_map.values(),
        key=lambda x: (safe_int(x.get("seen_count"), 0), safe_float(x.get("best_score"), 0.0)),
        reverse=True,
    )[:TOP_WALLETS_PER_GROUP]

    observed = top_observed_wallets(limit=TOP_WALLETS_PER_GROUP)
    payload = {
        "scan_count": len(recent),
        "unique_wallets_seen": len(wallet_map),
        "top_group_wallets": top_group_wallets,
        "top_observed_wallets": observed,
        "timestamp": iso_utc(now_utc()),
    }
    return payload


def maybe_send_group_summary(force: bool = False) -> Optional[str]:
    now_ts = utc_ts()
    with state_lock:
        last_group_sent = safe_float(runtime_state.get("last_group_sent_at"), 0.0)
    if not force and (now_ts - last_group_sent) < GROUP_WINDOW_SECONDS:
        return None

    payload = build_group_payload()
    if not SEND_ZERO_GROUP_SUMMARY and payload.get("scan_count", 0) == 0 and not payload.get("top_observed_wallets"):
        return None

    text = format_group_text(payload)
    send_telegram(text)

    with state_lock:
        runtime_state["last_group_sent_at"] = now_ts
        runtime_state.setdefault("session_summary", {})["last_group_top_count"] = len(payload.get("top_group_wallets") or [])
        save_state()
    return text


def run_scan_and_update(send_auto_telegram: bool = False, manual_quick: bool = False) -> Dict[str, Any]:
    result = scan_once(manual_quick=manual_quick)
    update_runtime_after_scan(result)
    if send_auto_telegram:
        send_telegram(format_scan_text(result, manual=False))
    maybe_send_group_summary(force=False)
    return result


# =========================================================
# Background
# =========================================================
def background_loop() -> None:
    while True:
        try:
            run_scan_and_update(send_auto_telegram=False)
        except Exception as exc:
            send_telegram(f"Wallet intel background scan error\nscript_version={SCRIPT_VERSION}\nerror={clean_text(exc)}")
        time.sleep(max(SCAN_EVERY_SECONDS, 60))


def ensure_background_started() -> None:
    global background_started
    if background_started:
        return
    background_started = True
    load_state()
    init_db()
    t = threading.Thread(target=background_loop, daemon=True)
    t.start()


# =========================================================
# Routes
# =========================================================
@app.route("/health", methods=["GET"])
def health_route():
    ensure_background_started()
    return health_text(), 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.route("/scan", methods=["GET"])
def scan_route():
    ensure_background_started()
    result = run_scan_and_update(send_auto_telegram=False, manual_quick=True)
    return format_scan_text(result, manual=True), 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.route("/group", methods=["GET"])
def group_route():
    ensure_background_started()
    payload = build_group_payload()
    return format_group_text(payload), 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.route("/webhook", methods=["POST"])
def webhook_route():
    ensure_background_started()
    global manual_scan_in_progress
    payload = request.get_json(silent=True) or {}
    message = payload.get("message") or payload.get("edited_message") or {}
    text = clean_text(message.get("text") or "")

    if text == "/health":
        send_telegram(health_text())
    elif text == "/group":
        text_out = build_group_payload()
        send_telegram(format_group_text(text_out))
    elif text == "/scan":
        with state_lock:
            if manual_scan_in_progress:
                send_telegram("Manual scan already running")
                return jsonify({"ok": True})
            manual_scan_in_progress = True

        def _manual_scan_worker() -> None:
            global manual_scan_in_progress
            try:
                send_telegram("Running wallet scan...")
                if MANUAL_SEND_CACHED_FIRST:
                    try:
                        cached = latest_cached_scan_text()
                        send_telegram(cached)
                    except Exception:
                        pass
                result = run_scan_and_update(send_auto_telegram=False, manual_quick=True)
                send_telegram(format_scan_text(result, manual=True))
            except Exception as exc:
                send_telegram(f"Manual wallet scan error\nscript_version={SCRIPT_VERSION}\nerror={clean_text(exc)}")
            finally:
                with state_lock:
                    manual_scan_in_progress = False

        threading.Thread(target=_manual_scan_worker, daemon=True).start()
    else:
        send_telegram("Commands\n/health\n/scan\n/group")
    return jsonify({"ok": True})


if __name__ == "__main__":
    ensure_background_started()
    app.run(host="0.0.0.0", port=PORT)
