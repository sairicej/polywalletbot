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
SCRIPT_VERSION = "wallet-intel-v2-observation"
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

# Scan cadence
SCAN_EVERY_SECONDS = int(os.getenv("SCAN_EVERY_SECONDS", "1800"))            # 30 min
GROUP_WINDOW_SECONDS = int(os.getenv("GROUP_WINDOW_SECONDS", "10800"))      # 3 hr
SEND_ZERO_GROUP_SUMMARY = os.getenv("SEND_ZERO_GROUP_SUMMARY", "true").lower() == "true"

# Discovery
LEADERBOARD_LIMIT = int(os.getenv("LEADERBOARD_LIMIT", "100"))
ACTIVE_MARKET_LIMIT = int(os.getenv("ACTIVE_MARKET_LIMIT", "40"))
HOLDERS_PER_MARKET = int(os.getenv("HOLDERS_PER_MARKET", "15"))
MAX_CANDIDATE_WALLETS = int(os.getenv("MAX_CANDIDATE_WALLETS", "120"))

# Wallet grading
LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "30"))
RECENT_DAYS = int(os.getenv("RECENT_DAYS", "7"))
MIN_CLOSED_POSITIONS_30D = int(os.getenv("MIN_CLOSED_POSITIONS_30D", "5"))
MIN_TRADES_30D = int(os.getenv("MIN_TRADES_30D", "10"))
MIN_WEIGHTED_RETURN_30D = float(os.getenv("MIN_WEIGHTED_RETURN_30D", "0.20"))
MIN_WIN_RATE_30D = float(os.getenv("MIN_WIN_RATE_30D", "0.55"))
MIN_CONSISTENCY_RATIO = float(os.getenv("MIN_CONSISTENCY_RATIO", "0.50"))
MIN_REALIZED_PNL_30D = float(os.getenv("MIN_REALIZED_PNL_30D", "0.0"))
MIN_RECENT_TRADES_7D = int(os.getenv("MIN_RECENT_TRADES_7D", "2"))
MIN_INTRADAY_SIGNALS = int(os.getenv("MIN_INTRADAY_SIGNALS", "1"))

# Observation grading
OBS_LOOKAHEAD_HOURS = int(os.getenv("OBS_LOOKAHEAD_HOURS", "24"))
OBS_MIN_MOVE_PCT = float(os.getenv("OBS_MIN_MOVE_PCT", "0.03"))
OBS_MAX_NEW_TRADES_PER_WALLET = int(os.getenv("OBS_MAX_NEW_TRADES_PER_WALLET", "20"))
OBS_MIN_SAMPLES_FOR_CONFIDENCE = int(os.getenv("OBS_MIN_SAMPLES_FOR_CONFIDENCE", "5"))
OBS_ENABLED = os.getenv("OBS_ENABLED", "true").lower() == "true"

# Output
TOP_WALLETS_PER_SCAN = int(os.getenv("TOP_WALLETS_PER_SCAN", "8"))
TOP_WALLETS_PER_GROUP = int(os.getenv("TOP_WALLETS_PER_GROUP", "10"))
WATCH_BUCKET_MIN_SCORE = float(os.getenv("WATCH_BUCKET_MIN_SCORE", "60"))
TEST_FIRST_MIN_SCORE = float(os.getenv("TEST_FIRST_MIN_SCORE", "75"))

STATE_FILE = os.getenv("STATE_FILE", "/tmp/polymarket_wallet_intel_state.json")
DB_FILE = os.getenv("DB_FILE", "/tmp/polymarket_wallet_intel.db")

# =========================================================
# Runtime state
# =========================================================
state_lock = threading.Lock()
manual_scan_in_progress = False
background_started = False
http_session = requests.Session()
price_cache: Dict[str, Tuple[float, Dict[str, Any]]] = {}

runtime_state: Dict[str, Any] = {
    "last_group_sent_at": 0.0,
    "scan_history": [],
    "session_summary": {
        "scans": 0,
        "wallets_evaluated": 0,
        "wallets_passing": 0,
        "last_scan_top_count": 0,
        "last_group_top_count": 0,
        "obs_logged_total": 0,
        "obs_resolved_total": 0,
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
        return int(value)
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
        dt = value
        return dt if dt.tzinfo else dt.replace(tzinfo=UTC)
    try:
        if isinstance(value, (int, float)):
            val = float(value)
        else:
            s = str(value).strip()
            if not s:
                return None
            if s.endswith("Z"):
                s = s[:-1] + "+00:00"
            if s.isdigit():
                val = float(s)
            else:
                dt = datetime.fromisoformat(s)
                return dt if dt.tzinfo else dt.replace(tzinfo=UTC)
        if val > 1e12:
            val /= 1000.0
        return datetime.fromtimestamp(val, tz=UTC)
    except Exception:
        return None


def days_ago(days: int) -> datetime:
    return now_utc() - timedelta(days=days)


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
            for key in ["data", "results", "markets", "events", "leaderboard", "items"]:
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


def parse_jsonish_list(value: Any) -> List[Any]:
    if isinstance(value, list):
        return value
    if value is None:
        return []
    if isinstance(value, str):
        s = value.strip()
        if not s:
            return []
        try:
            data = json.loads(s)
            return data if isinstance(data, list) else []
        except Exception:
            return []
    return []


def parse_outcomes_prices(row: Dict[str, Any]) -> Tuple[List[str], List[float]]:
    outcomes = parse_jsonish_list(row.get("outcomes") or row.get("outcomeNames") or row.get("tokens"))
    prices = parse_jsonish_list(row.get("outcomePrices") or row.get("prices") or row.get("outcome_prices"))

    out_names: List[str] = []
    out_prices: List[float] = []

    for item in outcomes:
        if isinstance(item, str):
            out_names.append(item)
        elif isinstance(item, dict):
            out_names.append(clean_text(item.get("name") or item.get("title") or item.get("outcome")))

    for item in prices:
        if isinstance(item, (int, float, str)):
            out_prices.append(safe_float(item))
        elif isinstance(item, dict):
            out_prices.append(safe_float(item.get("price") or item.get("value")))

    return out_names, out_prices


def normalize_outcome_name(value: Any) -> str:
    s = clean_text(value).strip().lower()
    if s in ("yes", "y"):
        return "yes"
    if s in ("no", "n"):
        return "no"
    return s


def resolve_side_from_trade(row: Dict[str, Any]) -> str:
    for key in ["outcome", "outcomeName", "tokenOutcome", "position", "side"]:
        val = row.get(key)
        name = normalize_outcome_name(val)
        if name:
            return name
    return ""


def make_market_key(slug: str, condition_id: str, token_id: str) -> str:
    if token_id:
        return f"token:{token_id}"
    if condition_id:
        return f"condition:{condition_id}"
    return f"slug:{slug}"


# =========================================================
# SQLite observation store
# =========================================================
def db_connect() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_FILE, timeout=30)
    conn.row_factory = sqlite3.Row
    return conn


def init_db() -> None:
    conn = db_connect()
    try:
        conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS trade_observations (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                observation_key TEXT NOT NULL UNIQUE,
                wallet TEXT NOT NULL,
                username TEXT,
                market_slug TEXT,
                market_question TEXT,
                market_condition_id TEXT,
                token_id TEXT,
                side TEXT,
                entry_price REAL,
                entry_ts TEXT,
                source TEXT,
                wallet_bucket TEXT,
                wallet_score REAL,
                initial_wallet_weighted_return REAL,
                initial_wallet_win_rate REAL,
                initial_wallet_consistency REAL,
                status TEXT NOT NULL DEFAULT 'open',
                price_after_1h REAL,
                price_after_6h REAL,
                price_after_24h REAL,
                checked_at_1h TEXT,
                checked_at_6h TEXT,
                checked_at_24h TEXT,
                max_favorable_move REAL,
                max_adverse_move REAL,
                success_24h INTEGER,
                resolution_notes TEXT,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            );

            CREATE INDEX IF NOT EXISTS idx_trade_obs_wallet ON trade_observations(wallet);
            CREATE INDEX IF NOT EXISTS idx_trade_obs_status ON trade_observations(status);
            CREATE INDEX IF NOT EXISTS idx_trade_obs_entry_ts ON trade_observations(entry_ts);
            """
        )
        conn.commit()
    finally:
        conn.close()


def db_scalar(query: str, params: Tuple[Any, ...] = ()) -> Any:
    conn = db_connect()
    try:
        cur = conn.execute(query, params)
        row = cur.fetchone()
        if row is None:
            return None
        if isinstance(row, sqlite3.Row):
            return row[0]
        return row[0]
    finally:
        conn.close()


def get_wallet_observation_summary(wallet: str) -> Dict[str, Any]:
    conn = db_connect()
    try:
        row = conn.execute(
            """
            SELECT
                COUNT(*) AS observed_total,
                SUM(CASE WHEN status='resolved' THEN 1 ELSE 0 END) AS resolved_total,
                SUM(CASE WHEN success_24h=1 THEN 1 ELSE 0 END) AS success_total,
                AVG(CASE WHEN success_24h IN (0,1) THEN success_24h END) AS success_rate_24h,
                AVG(CASE WHEN price_after_24h IS NOT NULL AND entry_price > 0 THEN
                    CASE
                        WHEN lower(side)='yes' THEN (price_after_24h - entry_price) / entry_price
                        WHEN lower(side)='no' THEN ((1.0 - price_after_24h) - (1.0 - entry_price)) / NULLIF((1.0 - entry_price), 0)
                        ELSE NULL
                    END
                END) AS avg_move_24h,
                AVG(CASE WHEN price_after_1h IS NOT NULL AND entry_price > 0 THEN
                    CASE
                        WHEN lower(side)='yes' THEN CASE WHEN (price_after_1h - entry_price) / entry_price < 0 THEN 1 ELSE 0 END
                        WHEN lower(side)='no' THEN CASE WHEN ((1.0 - price_after_1h) - (1.0 - entry_price)) / NULLIF((1.0 - entry_price), 0) < 0 THEN 1 ELSE 0 END
                        ELSE NULL
                    END
                END) AS early_failure_rate,
                MAX(entry_ts) AS latest_entry_ts
            FROM trade_observations
            WHERE wallet=?
            """,
            (wallet,),
        ).fetchone()
        if not row:
            return {
                "observed_total": 0,
                "resolved_total": 0,
                "success_total": 0,
                "success_rate_24h": None,
                "avg_move_24h": None,
                "early_failure_rate": None,
                "latest_entry_ts": None,
            }
        return {
            "observed_total": safe_int(row["observed_total"], 0),
            "resolved_total": safe_int(row["resolved_total"], 0),
            "success_total": safe_int(row["success_total"], 0),
            "success_rate_24h": row["success_rate_24h"] if row["success_rate_24h"] is not None else None,
            "avg_move_24h": row["avg_move_24h"] if row["avg_move_24h"] is not None else None,
            "early_failure_rate": row["early_failure_rate"] if row["early_failure_rate"] is not None else None,
            "latest_entry_ts": row["latest_entry_ts"],
        }
    finally:
        conn.close()


def get_observation_stats() -> Dict[str, int]:
    conn = db_connect()
    try:
        row = conn.execute(
            """
            SELECT
                COUNT(*) AS total,
                SUM(CASE WHEN status='open' THEN 1 ELSE 0 END) AS open_count,
                SUM(CASE WHEN status='resolved' THEN 1 ELSE 0 END) AS resolved_count
            FROM trade_observations
            """
        ).fetchone()
        return {
            "obs_total": safe_int(row["total"], 0) if row else 0,
            "obs_open": safe_int(row["open_count"], 0) if row else 0,
            "obs_resolved": safe_int(row["resolved_count"], 0) if row else 0,
        }
    finally:
        conn.close()


def top_observed_wallets(limit: int = 10) -> List[Dict[str, Any]]:
    conn = db_connect()
    try:
        rows = conn.execute(
            """
            SELECT
                wallet,
                MAX(COALESCE(username,'')) AS username,
                COUNT(*) AS observed_total,
                SUM(CASE WHEN status='resolved' THEN 1 ELSE 0 END) AS resolved_total,
                SUM(CASE WHEN success_24h=1 THEN 1 ELSE 0 END) AS success_total,
                AVG(CASE WHEN success_24h IN (0,1) THEN success_24h END) AS success_rate_24h,
                AVG(CASE WHEN price_after_24h IS NOT NULL AND entry_price > 0 THEN
                    CASE
                        WHEN lower(side)='yes' THEN (price_after_24h - entry_price) / entry_price
                        WHEN lower(side)='no' THEN ((1.0 - price_after_24h) - (1.0 - entry_price)) / NULLIF((1.0 - entry_price), 0)
                        ELSE NULL
                    END
                END) AS avg_move_24h,
                AVG(CASE WHEN price_after_1h IS NOT NULL AND entry_price > 0 THEN
                    CASE
                        WHEN lower(side)='yes' THEN CASE WHEN (price_after_1h - entry_price) / entry_price < 0 THEN 1 ELSE 0 END
                        WHEN lower(side)='no' THEN CASE WHEN ((1.0 - price_after_1h) - (1.0 - entry_price)) / NULLIF((1.0 - entry_price), 0) < 0 THEN 1 ELSE 0 END
                        ELSE NULL
                    END
                END) AS early_failure_rate,
                MAX(wallet_score) AS latest_score
            FROM trade_observations
            GROUP BY wallet
            HAVING resolved_total >= 1
            ORDER BY success_rate_24h DESC, resolved_total DESC, avg_move_24h DESC
            LIMIT ?
            """,
            (limit,),
        ).fetchall()
        out = []
        for row in rows:
            out.append({
                "wallet": row["wallet"],
                "username": clean_text(row["username"]),
                "observed_total": safe_int(row["observed_total"], 0),
                "resolved_total": safe_int(row["resolved_total"], 0),
                "success_total": safe_int(row["success_total"], 0),
                "success_rate_24h": row["success_rate_24h"],
                "avg_move_24h": row["avg_move_24h"],
                "early_failure_rate": row["early_failure_rate"],
                "latest_score": safe_float(row["latest_score"], 0.0),
            })
        return out
    finally:
        conn.close()


# =========================================================
# Public Polymarket fetchers
# =========================================================
def fetch_leaderboard_wallets(limit: int) -> List[Dict[str, Any]]:
    rows = fetch_list(
        f"{DATA_API_V1_BASE}/leaderboard",
        params={"limit": min(limit, 50), "timePeriod": "MONTH", "orderBy": "PNL", "category": "OVERALL"},
    )
    out: List[Dict[str, Any]] = []
    for row in rows:
        wallet = str(row.get("proxyWallet") or row.get("wallet") or row.get("user") or "").strip()
        if not wallet:
            continue
        out.append({
            "wallet": wallet,
            "source": "leaderboard",
            "leaderboard_rank": safe_int(row.get("rank"), 0),
            "leaderboard_pnl": safe_float(row.get("pnl"), 0.0),
            "leaderboard_vol": safe_float(row.get("vol"), 0.0),
            "username": clean_text(row.get("userName") or row.get("username") or row.get("name") or ""),
        })
    return out


def fetch_active_markets(limit: int) -> List[Dict[str, Any]]:
    params = {"closed": "false", "archived": "false", "limit": limit}
    rows = fetch_list(f"{GAMMA_BASE}/markets", params=params)
    out: List[Dict[str, Any]] = []
    for row in rows:
        slug = clean_text(row.get("slug"))
        condition_id = clean_text(row.get("conditionId") or row.get("condition_id"))
        if not slug and not condition_id:
            continue
        out.append({
            "slug": slug,
            "question": clean_text(row.get("question") or row.get("title") or slug),
            "conditionId": condition_id,
            "volume": safe_float(row.get("volume") or row.get("volumeNum"), 0.0),
            "liquidity": safe_float(row.get("liquidity") or row.get("liquidityNum"), 0.0),
            "endDate": row.get("endDate") or row.get("end_date") or row.get("end_date_iso"),
            "raw": row,
        })
    out.sort(key=lambda x: (x["liquidity"], x["volume"]), reverse=True)
    return out[:limit]


def fetch_market_by_slug(slug: str) -> Optional[Dict[str, Any]]:
    if not slug:
        return None
    rows = fetch_list(f"{GAMMA_BASE}/markets", params={"slug": slug})
    if rows:
        row = rows[0]
        return {
            "slug": clean_text(row.get("slug")),
            "question": clean_text(row.get("question") or row.get("title") or slug),
            "conditionId": clean_text(row.get("conditionId") or row.get("condition_id")),
            "raw": row,
        }
    return None


def fetch_top_holders_for_market(market: Dict[str, Any], limit: int) -> List[Dict[str, Any]]:
    params_candidates = [
        {"market": market.get("slug"), "limit": limit},
        {"slug": market.get("slug"), "limit": limit},
        {"conditionId": market.get("conditionId"), "limit": limit},
    ]
    for params in params_candidates:
        params = {k: v for k, v in params.items() if v not in (None, "")}
        if not params:
            continue
        rows = fetch_list(f"{DATA_API_BASE}/holders", params=params)
        if rows:
            out: List[Dict[str, Any]] = []
            for row in rows:
                nested_holders = row.get("holders")
                if isinstance(nested_holders, list):
                    for holder in nested_holders:
                        if not isinstance(holder, dict):
                            continue
                        wallet = str(holder.get("proxyWallet") or holder.get("wallet") or holder.get("user") or "").strip()
                        if not wallet:
                            continue
                        out.append({
                            "wallet": wallet,
                            "source": "holders",
                            "holder_size": safe_float(holder.get("amount") or holder.get("size") or holder.get("balance") or holder.get("shares"), 0.0),
                            "market_slug": clean_text(market.get("slug")),
                            "market_question": clean_text(market.get("question")),
                        })
                    continue
                wallet = str(row.get("proxyWallet") or row.get("wallet") or row.get("user") or "").strip()
                if not wallet:
                    continue
                out.append({
                    "wallet": wallet,
                    "source": "holders",
                    "holder_size": safe_float(row.get("amount") or row.get("size") or row.get("balance") or row.get("shares"), 0.0),
                    "market_slug": clean_text(market.get("slug")),
                    "market_question": clean_text(market.get("question")),
                })
            if out:
                return out
    return []


def fetch_closed_positions(wallet: str) -> List[Dict[str, Any]]:
    return fetch_list(f"{DATA_API_BASE}/closed-positions", params={"user": wallet})


def fetch_trades(wallet: str) -> List[Dict[str, Any]]:
    # limit is intentionally left out here because the endpoint often caps itself.
    return fetch_list(f"{DATA_API_BASE}/trades", params={"user": wallet})


def fetch_current_positions(wallet: str) -> List[Dict[str, Any]]:
    return fetch_list(f"{DATA_API_BASE}/positions", params={"user": wallet})


def fetch_user_activity(wallet: str) -> List[Dict[str, Any]]:
    return fetch_list(f"{DATA_API_BASE}/activity", params={"user": wallet})


# =========================================================
# Market price resolution for observations
# =========================================================
def infer_market_price(raw_market: Dict[str, Any], side: str) -> Optional[float]:
    names, prices = parse_outcomes_prices(raw_market)
    if names and prices and len(names) == len(prices):
        norm_side = normalize_outcome_name(side)
        for idx, name in enumerate(names):
            if normalize_outcome_name(name) == norm_side:
                price = safe_float(prices[idx], -1.0)
                return price if 0.0 <= price <= 1.0 else None

    # fallback for binary yes/no
    if normalize_outcome_name(side) == "yes":
        for key in ["lastTradePrice", "last_price", "price", "yesPrice"]:
            price = safe_float(raw_market.get(key), -1.0)
            if 0.0 <= price <= 1.0:
                return price
    if normalize_outcome_name(side) == "no":
        for key in ["lastTradePrice", "last_price", "price", "yesPrice"]:
            price = safe_float(raw_market.get(key), -1.0)
            if 0.0 <= price <= 1.0:
                return 1.0 - price
        price = safe_float(raw_market.get("noPrice"), -1.0)
        if 0.0 <= price <= 1.0:
            return price
    return None


def get_market_price_snapshot(slug: str, condition_id: str, token_id: str, side: str) -> Optional[Dict[str, Any]]:
    cache_key = f"{slug}|{condition_id}|{token_id}|{side}"
    cached = price_cache.get(cache_key)
    if cached and utc_ts() - cached[0] < 120:
        return cached[1]

    market = fetch_market_by_slug(slug) if slug else None
    if market and market.get("raw"):
        price = infer_market_price(market["raw"], side)
        if price is not None:
            snap = {
                "price": price,
                "question": market.get("question") or slug,
                "slug": market.get("slug") or slug,
                "conditionId": market.get("conditionId") or condition_id,
            }
            price_cache[cache_key] = (utc_ts(), snap)
            return snap
    return None


def move_in_favor(entry_price: float, later_price: float, side: str) -> Optional[float]:
    if entry_price <= 0 or later_price < 0:
        return None
    norm_side = normalize_outcome_name(side)
    if norm_side == "yes":
        return (later_price - entry_price) / entry_price if entry_price > 0 else None
    if norm_side == "no":
        entry_no = 1.0 - entry_price
        later_no = 1.0 - later_price
        if entry_no <= 0:
            return None
        return (later_no - entry_no) / entry_no
    return None


# =========================================================
# Wallet discovery
# =========================================================
def discover_candidate_wallets() -> Tuple[List[Dict[str, Any]], Dict[str, Any]]:
    candidates: Dict[str, Dict[str, Any]] = {}
    stats = {
        "leaderboard_wallets": 0,
        "active_markets": 0,
        "holder_wallets": 0,
        "unique_candidate_wallets": 0,
    }

    for row in fetch_leaderboard_wallets(LEADERBOARD_LIMIT):
        wallet = row["wallet"]
        base = candidates.setdefault(wallet, {"wallet": wallet, "sources": [], "leaderboard_rank": None, "leaderboard_pnl": 0.0, "leaderboard_vol": 0.0, "username": "", "holder_markets": []})
        if "leaderboard" not in base["sources"]:
            base["sources"].append("leaderboard")
        base["leaderboard_rank"] = row.get("leaderboard_rank")
        base["leaderboard_pnl"] = row.get("leaderboard_pnl", 0.0)
        base["leaderboard_vol"] = row.get("leaderboard_vol", 0.0)
        if row.get("username"):
            base["username"] = row["username"]
    stats["leaderboard_wallets"] = len(candidates)

    active_markets = fetch_active_markets(ACTIVE_MARKET_LIMIT)
    stats["active_markets"] = len(active_markets)
    for market in active_markets:
        holders = fetch_top_holders_for_market(market, HOLDERS_PER_MARKET)
        stats["holder_wallets"] += len(holders)
        for row in holders:
            wallet = row["wallet"]
            base = candidates.setdefault(wallet, {"wallet": wallet, "sources": [], "leaderboard_rank": None, "leaderboard_pnl": 0.0, "leaderboard_vol": 0.0, "username": "", "holder_markets": []})
            if "holders" not in base["sources"]:
                base["sources"].append("holders")
            base["holder_markets"].append({
                "slug": row.get("market_slug"),
                "question": row.get("market_question"),
                "size": row.get("holder_size", 0.0),
            })
            if len(base["holder_markets"]) > 5:
                base["holder_markets"] = base["holder_markets"][:5]

    deduped = list(candidates.values())
    deduped.sort(key=lambda x: (
        0 if x.get("leaderboard_rank") in (None, 0) else -1,
        -(x.get("leaderboard_pnl") or 0.0),
        -(x.get("leaderboard_vol") or 0.0),
        -len(x.get("holder_markets") or []),
    ))
    stats["unique_candidate_wallets"] = len(deduped)
    return deduped[:MAX_CANDIDATE_WALLETS], stats


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
    obs_rate = wallet_metrics.get("obs_success_rate_24h")
    obs_count = wallet_metrics.get("obs_resolved_total", 0)
    capped_trade_penalty = 8.0 if wallet_metrics.get("trades_capped_30d") else 0.0
    perfection_penalty = 0.0

    if wallet_metrics.get("win_rate_30d", 0.0) >= 0.999 and wallet_metrics.get("closed_positions_30d", 0) < 15:
        perfection_penalty += 10.0
    if wallet_metrics.get("win_rate_30d", 0.0) >= 0.95 and wallet_metrics.get("consistency_ratio_30d", 0.0) >= 0.90:
        perfection_penalty += 6.0

    ret_score = clamp(weighted_return / 0.40, 0.0, 1.0) * 28.0
    win_score = clamp((win_rate - 0.50) / 0.30, 0.0, 1.0) * 14.0
    consistency_score = clamp((consistency - 0.40) / 0.40, 0.0, 1.0) * 14.0
    activity_score = clamp(recent_trades / 8.0, 0.0, 1.0) * 10.0
    intraday_score = clamp(intraday / 5.0, 0.0, 1.0) * 8.0
    sample_score = clamp(sample / 15.0, 0.0, 1.0) * 6.0
    obs_score = 0.0
    if obs_rate is not None and obs_count > 0:
        obs_score = clamp((safe_float(obs_rate) - 0.50) / 0.30, 0.0, 1.0) * 20.0
        obs_score *= clamp(obs_count / max(OBS_MIN_SAMPLES_FOR_CONFIDENCE, 1), 0.25, 1.0)

    total = ret_score + win_score + consistency_score + activity_score + intraday_score + sample_score + obs_score
    total -= capped_trade_penalty
    total -= perfection_penalty
    return round(max(total, 0.0), 2)


def classify_bucket(wallet_metrics: Dict[str, Any]) -> str:
    score = wallet_metrics.get("score", 0.0)
    obs_rate = wallet_metrics.get("obs_success_rate_24h")
    obs_count = wallet_metrics.get("obs_resolved_total", 0)

    if obs_rate is not None and obs_count >= OBS_MIN_SAMPLES_FOR_CONFIDENCE and obs_rate < 0.50:
        return "REJECT"
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
        weak.append(f"win rate only {metrics.get('win_rate_30d', 0.0):.1%}")

    if metrics.get("consistency_ratio_30d", 0.0) >= MIN_CONSISTENCY_RATIO:
        good.append(f"consistency {metrics['consistency_ratio_30d']:.1%} of closes above 20%")
    else:
        weak.append(f"only {metrics.get('consistency_ratio_30d', 0.0):.1%} of closes above 20%")

    if metrics.get("recent_trades_7d", 0) >= MIN_RECENT_TRADES_7D:
        good.append(f"recent activity {metrics['recent_trades_7d']} trades in 7d")
    else:
        weak.append("not enough recent activity")

    if metrics.get("intraday_roundtrips_30d", 0) >= MIN_INTRADAY_SIGNALS:
        good.append(f"intraday signals {metrics['intraday_roundtrips_30d']}")
    else:
        weak.append("no strong intraday signal yet")

    if metrics.get("trades_capped_30d"):
        weak.append("trade count appears capped at API limit")

    obs_rate = metrics.get("obs_success_rate_24h")
    obs_count = metrics.get("obs_resolved_total", 0)
    if obs_rate is not None and obs_count > 0:
        good.append(f"observed 24h success {obs_rate:.1%} over {obs_count} logged trades")
        if obs_count < OBS_MIN_SAMPLES_FOR_CONFIDENCE:
            weak.append("24h observation sample still thin")
    else:
        weak.append("no resolved 24h observations yet")

    if metrics.get("win_rate_30d", 0.0) >= 0.999 and metrics.get("closed_positions_30d", 0) < 15:
        weak.append("snapshot looks too perfect for a small sample")

    return good, weak


def extract_wallet_trade_features(trades: List[Dict[str, Any]], start_30d: datetime, start_7d: datetime) -> Dict[str, Any]:
    trades_30d: List[Dict[str, Any]] = []
    recent_trades_7d = 0
    by_slug_day: Dict[Tuple[str, str], Dict[str, int]] = defaultdict(lambda: {"BUY": 0, "SELL": 0})

    for t in trades:
        ts = parse_ts(t.get("timestamp") or t.get("createdAt") or t.get("created_at") or t.get("time"))
        if not ts:
            continue
        if ts >= start_30d:
            trades_30d.append(t)
            slug = clean_text(t.get("marketSlug") or t.get("slug") or t.get("market"))
            side = clean_text(t.get("action") or t.get("tradeSide") or t.get("type") or t.get("side")).upper()
            key = (slug, ts.strftime("%Y-%m-%d"))
            if side in ("BUY", "SELL"):
                by_slug_day[key][side] += 1
        if ts >= start_7d:
            recent_trades_7d += 1

    intraday_roundtrips = sum(1 for v in by_slug_day.values() if v["BUY"] > 0 and v["SELL"] > 0)
    trades_capped = len(trades_30d) >= 100
    return {
        "trades_30d": len(trades_30d),
        "recent_trades_7d": recent_trades_7d,
        "intraday_roundtrips_30d": intraday_roundtrips,
        "trades_capped_30d": trades_capped,
    }


def evaluate_wallet(candidate: Dict[str, Any]) -> Dict[str, Any]:
    wallet = candidate["wallet"]
    start_30d = days_ago(LOOKBACK_DAYS)
    start_7d = days_ago(RECENT_DAYS)

    closed_positions = fetch_closed_positions(wallet)
    trades = fetch_trades(wallet)
    current_positions = fetch_current_positions(wallet)

    closed_30d: List[Dict[str, Any]] = []
    returns_30d: List[float] = []
    wins = 0
    strong_closes = 0
    realized_pnl_30d = 0.0
    weighted_num = 0.0
    weighted_den = 0.0

    for row in closed_positions:
        ts = parse_ts(row.get("closedAt") or row.get("endDate") or row.get("createdAt") or row.get("updatedAt"))
        if ts and ts < start_30d:
            continue
        closed_30d.append(row)
        realized = safe_float(row.get("realizedPnl") or row.get("pnl"), 0.0)
        realized_pnl_30d += realized
        r = realized_return_from_closed_position(row)
        returns_30d.append(r)
        if realized > 0:
            wins += 1
        if r >= 0.20:
            strong_closes += 1
        denom = safe_float(row.get("totalBought") or row.get("size") or row.get("amount"), 0.0)
        if denom <= 0:
            denom = 1.0
        weighted_num += realized
        weighted_den += denom

    trade_features = extract_wallet_trade_features(trades, start_30d, start_7d)
    obs_summary = get_wallet_observation_summary(wallet)

    avg_return = sum(returns_30d) / len(returns_30d) if returns_30d else 0.0
    weighted_return = weighted_num / weighted_den if weighted_den > 0 else 0.0
    win_rate = wins / len(closed_30d) if closed_30d else 0.0
    consistency_ratio = strong_closes / len(closed_30d) if closed_30d else 0.0

    metrics = {
        "wallet": wallet,
        "username": candidate.get("username") or "",
        "sources": candidate.get("sources") or [],
        "holder_markets": candidate.get("holder_markets") or [],
        "closed_positions_30d": len(closed_30d),
        "trades_30d": trade_features["trades_30d"],
        "recent_trades_7d": trade_features["recent_trades_7d"],
        "intraday_roundtrips_30d": trade_features["intraday_roundtrips_30d"],
        "trades_capped_30d": trade_features["trades_capped_30d"],
        "current_positions": len(current_positions),
        "realized_pnl_30d": realized_pnl_30d,
        "weighted_return_30d": weighted_return,
        "avg_return_30d": avg_return,
        "win_rate_30d": win_rate,
        "consistency_ratio_30d": consistency_ratio,
        "obs_observed_total": obs_summary["observed_total"],
        "obs_resolved_total": obs_summary["resolved_total"],
        "obs_success_total": obs_summary["success_total"],
        "obs_success_rate_24h": obs_summary["success_rate_24h"],
        "obs_avg_move_24h": obs_summary["avg_move_24h"],
        "obs_early_failure_rate": obs_summary["early_failure_rate"],
    }

    good_reasons, weak_reasons = reason_strings(metrics)
    metrics["good_reasons"] = good_reasons
    metrics["weak_reasons"] = weak_reasons
    metrics["score"] = bucket_score(metrics)
    metrics["bucket"] = classify_bucket(metrics)
    metrics["passes_thresholds"] = all([
        metrics["closed_positions_30d"] >= MIN_CLOSED_POSITIONS_30D,
        metrics["trades_30d"] >= MIN_TRADES_30D,
        metrics["weighted_return_30d"] >= MIN_WEIGHTED_RETURN_30D,
        metrics["win_rate_30d"] >= MIN_WIN_RATE_30D,
        metrics["consistency_ratio_30d"] >= MIN_CONSISTENCY_RATIO,
        metrics["realized_pnl_30d"] >= MIN_REALIZED_PNL_30D,
        metrics["recent_trades_7d"] >= MIN_RECENT_TRADES_7D,
        metrics["intraday_roundtrips_30d"] >= MIN_INTRADAY_SIGNALS,
    ])
    return metrics


# =========================================================
# Observation logging and resolution
# =========================================================
def normalize_trade_record(t: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    ts = parse_ts(t.get("timestamp") or t.get("createdAt") or t.get("created_at") or t.get("time"))
    if not ts:
        return None
    slug = clean_text(t.get("marketSlug") or t.get("slug") or t.get("market") or t.get("market_slug"))
    condition_id = clean_text(t.get("conditionId") or t.get("condition_id"))
    token_id = clean_text(t.get("tokenId") or t.get("token_id"))
    question = clean_text(t.get("question") or t.get("title") or slug)
    side = resolve_side_from_trade(t)
    entry_price = safe_float(t.get("price") or t.get("avgPrice") or t.get("matchedPrice"), -1.0)
    if entry_price < 0 or entry_price > 1:
        return None
    if not side:
        return None
    trade_action = clean_text(t.get("action") or t.get("tradeSide") or t.get("type") or "").upper()
    if trade_action and trade_action not in ("BUY", "BUYING", "TRADE", "FILLED"):
        # observation is focused on entries, not sells.
        return None
    return {
        "entry_ts": ts,
        "market_slug": slug,
        "market_question": question,
        "market_condition_id": condition_id,
        "token_id": token_id,
        "side": side,
        "entry_price": entry_price,
    }


def log_observations_for_wallet(metrics: Dict[str, Any], trades: List[Dict[str, Any]]) -> int:
    if not OBS_ENABLED:
        return 0
    wallet = metrics["wallet"]
    recent_floor = now_utc() - timedelta(hours=24)
    normalized: List[Dict[str, Any]] = []
    for t in trades:
        row = normalize_trade_record(t)
        if not row:
            continue
        if row["entry_ts"] < recent_floor:
            continue
        normalized.append(row)

    normalized.sort(key=lambda x: x["entry_ts"], reverse=True)
    normalized = normalized[:OBS_MAX_NEW_TRADES_PER_WALLET]
    if not normalized:
        return 0

    conn = db_connect()
    inserted = 0
    try:
        for row in normalized:
            obs_key = "|".join([
                wallet.lower(),
                make_market_key(row["market_slug"], row["market_condition_id"], row["token_id"]),
                normalize_outcome_name(row["side"]),
                row["entry_ts"].isoformat(),
                f"{row['entry_price']:.6f}",
            ])
            try:
                conn.execute(
                    """
                    INSERT INTO trade_observations (
                        observation_key, wallet, username, market_slug, market_question, market_condition_id,
                        token_id, side, entry_price, entry_ts, source, wallet_bucket, wallet_score,
                        initial_wallet_weighted_return, initial_wallet_win_rate, initial_wallet_consistency,
                        created_at, updated_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        obs_key,
                        wallet,
                        metrics.get("username") or "",
                        row["market_slug"],
                        row["market_question"],
                        row["market_condition_id"],
                        row["token_id"],
                        normalize_outcome_name(row["side"]),
                        row["entry_price"],
                        row["entry_ts"].isoformat(),
                        ",".join(metrics.get("sources") or []),
                        metrics.get("bucket"),
                        metrics.get("score", 0.0),
                        metrics.get("weighted_return_30d", 0.0),
                        metrics.get("win_rate_30d", 0.0),
                        metrics.get("consistency_ratio_30d", 0.0),
                        now_utc().isoformat(),
                        now_utc().isoformat(),
                    ),
                )
                inserted += 1
            except sqlite3.IntegrityError:
                continue
        conn.commit()
    finally:
        conn.close()
    return inserted


def resolve_due_observations() -> Dict[str, int]:
    if not OBS_ENABLED:
        return {"resolved_now": 0, "checked_1h": 0, "checked_6h": 0, "checked_24h": 0}

    conn = db_connect()
    resolved_now = 0
    checked_1h = 0
    checked_6h = 0
    checked_24h = 0
    try:
        rows = conn.execute(
            """
            SELECT * FROM trade_observations
            WHERE status='open'
            ORDER BY entry_ts ASC
            LIMIT 500
            """
        ).fetchall()

        for row in rows:
            entry_dt = parse_ts(row["entry_ts"])
            if not entry_dt:
                continue
            age_hours = (now_utc() - entry_dt).total_seconds() / 3600.0
            snap = get_market_price_snapshot(row["market_slug"], row["market_condition_id"], row["token_id"], row["side"])
            if not snap:
                continue
            price = safe_float(snap.get("price"), -1.0)
            if price < 0 or price > 1:
                continue

            updates: Dict[str, Any] = {}
            notes: List[str] = []
            entry_price = safe_float(row["entry_price"], 0.0)
            move = move_in_favor(entry_price, price, row["side"])
            if move is not None:
                prev_fav = row["max_favorable_move"] if row["max_favorable_move"] is not None else None
                prev_adv = row["max_adverse_move"] if row["max_adverse_move"] is not None else None
                if prev_fav is None or move > safe_float(prev_fav, -999):
                    updates["max_favorable_move"] = move
                if prev_adv is None or move < safe_float(prev_adv, 999):
                    updates["max_adverse_move"] = move

            if age_hours >= 1 and row["checked_at_1h"] is None:
                updates["price_after_1h"] = price
                updates["checked_at_1h"] = now_utc().isoformat()
                checked_1h += 1
                notes.append(f"1h={price:.3f}")
            if age_hours >= 6 and row["checked_at_6h"] is None:
                updates["price_after_6h"] = price
                updates["checked_at_6h"] = now_utc().isoformat()
                checked_6h += 1
                notes.append(f"6h={price:.3f}")
            if age_hours >= OBS_LOOKAHEAD_HOURS and row["checked_at_24h"] is None:
                updates["price_after_24h"] = price
                updates["checked_at_24h"] = now_utc().isoformat()
                final_move = move_in_favor(entry_price, price, row["side"])
                success = 1 if final_move is not None and final_move >= OBS_MIN_MOVE_PCT else 0
                updates["success_24h"] = success
                updates["status"] = "resolved"
                checked_24h += 1
                resolved_now += 1
                notes.append(f"24h={price:.3f}")
                notes.append(f"move={final_move:.2%}" if final_move is not None else "move=na")
                notes.append("success=yes" if success == 1 else "success=no")

            if updates:
                note_value = clean_text(" | ".join(notes))
                if note_value:
                    updates["resolution_notes"] = note_value
                updates["updated_at"] = now_utc().isoformat()
                set_clause = ", ".join([f"{k}=?" for k in updates.keys()])
                params = list(updates.values()) + [row["id"]]
                conn.execute(f"UPDATE trade_observations SET {set_clause} WHERE id=?", params)

        conn.commit()
        return {
            "resolved_now": resolved_now,
            "checked_1h": checked_1h,
            "checked_6h": checked_6h,
            "checked_24h": checked_24h,
        }
    finally:
        conn.close()


# =========================================================
# Scan and grouping
# =========================================================
def scan_once() -> Dict[str, Any]:
    candidates, discovery_stats = discover_candidate_wallets()

    evaluated: List[Dict[str, Any]] = []
    evaluation_errors = 0
    obs_logged = 0
    resolved_update = resolve_due_observations()

    for candidate in candidates:
        try:
            metrics = evaluate_wallet(candidate)
            evaluated.append(metrics)
            if metrics["bucket"] in ("TEST FIRST", "WATCH CLOSELY"):
                # fetch trades once more here for observation logging to avoid bloating evaluate_wallet return.
                wallet_trades = fetch_trades(candidate["wallet"])
                obs_logged += log_observations_for_wallet(metrics, wallet_trades)
        except Exception:
            evaluation_errors += 1

    test_first = [x for x in evaluated if x.get("bucket") == "TEST FIRST"]
    watch_closely = [x for x in evaluated if x.get("bucket") == "WATCH CLOSELY"]
    rejects = [x for x in evaluated if x.get("bucket") == "REJECT"]

    test_first.sort(key=lambda x: x.get("score", 0.0), reverse=True)
    watch_closely.sort(key=lambda x: x.get("score", 0.0), reverse=True)
    rejects.sort(key=lambda x: x.get("score", 0.0), reverse=True)

    scan = {
        "timestamp": now_utc().isoformat(),
        "stats": {
            **discovery_stats,
            "evaluated_wallets": len(evaluated),
            "passing_wallets": len(test_first) + len(watch_closely),
            "evaluation_errors": evaluation_errors,
            "obs_logged": obs_logged,
            "obs_resolved_now": resolved_update.get("resolved_now", 0),
            "obs_checked_1h": resolved_update.get("checked_1h", 0),
            "obs_checked_6h": resolved_update.get("checked_6h", 0),
            "obs_checked_24h": resolved_update.get("checked_24h", 0),
            **get_observation_stats(),
        },
        "test_first": test_first[:TOP_WALLETS_PER_SCAN],
        "watch_closely": watch_closely[:TOP_WALLETS_PER_SCAN],
        "rejects": rejects[:TOP_WALLETS_PER_SCAN],
    }

    runtime_state["last_health"] = scan["stats"]
    runtime_state["session_summary"]["scans"] = runtime_state["session_summary"].get("scans", 0) + 1
    runtime_state["session_summary"]["wallets_evaluated"] = runtime_state["session_summary"].get("wallets_evaluated", 0) + len(evaluated)
    runtime_state["session_summary"]["wallets_passing"] = runtime_state["session_summary"].get("wallets_passing", 0) + len(test_first) + len(watch_closely)
    runtime_state["session_summary"]["last_scan_top_count"] = len(test_first) + len(watch_closely)
    runtime_state["session_summary"]["obs_logged_total"] = runtime_state["session_summary"].get("obs_logged_total", 0) + obs_logged
    runtime_state["session_summary"]["obs_resolved_total"] = runtime_state["session_summary"].get("obs_resolved_total", 0) + resolved_update.get("resolved_now", 0)

    return scan


def append_scan_to_group(scan: Dict[str, Any]) -> None:
    history = runtime_state.setdefault("scan_history", [])
    history.append(scan)
    cutoff = now_utc() - timedelta(seconds=GROUP_WINDOW_SECONDS)
    runtime_state["scan_history"] = [
        x for x in history
        if parse_ts(x.get("timestamp")) and parse_ts(x.get("timestamp")) >= cutoff
    ][-72:]


def build_grouped_summary() -> Dict[str, Any]:
    scans = runtime_state.get("scan_history", [])
    cutoff = now_utc() - timedelta(seconds=GROUP_WINDOW_SECONDS)
    recent_scans = [x for x in scans if parse_ts(x.get("timestamp")) and parse_ts(x.get("timestamp")) >= cutoff]

    wallet_map: Dict[str, Dict[str, Any]] = {}
    for scan in recent_scans:
        for row in (scan.get("test_first") or []) + (scan.get("watch_closely") or []):
            wallet = row["wallet"]
            base = wallet_map.setdefault(wallet, {
                **row,
                "appearances": 0,
                "best_score": row.get("score", 0.0),
            })
            base["appearances"] += 1
            if row.get("score", 0.0) > base.get("best_score", 0.0):
                for key in row:
                    base[key] = row[key]
                base["best_score"] = row.get("score", 0.0)

    top_wallets = list(wallet_map.values())
    top_wallets.sort(key=lambda x: (x.get("appearances", 0), x.get("score", 0.0), safe_float(x.get("obs_success_rate_24h"), -1.0)), reverse=True)
    top_wallets = top_wallets[:TOP_WALLETS_PER_GROUP]

    return {
        "window_minutes": int(GROUP_WINDOW_SECONDS / 60),
        "scan_count": len(recent_scans),
        "wallet_count": len(wallet_map),
        "top_wallets": top_wallets,
        "observation_leaders": top_observed_wallets(limit=5),
    }


# =========================================================
# Formatting
# =========================================================
def format_wallet_block(row: Dict[str, Any]) -> str:
    name = clean_text(row.get("username") or "")
    label = f"{name} ({short_wallet(row['wallet'])})" if name else short_wallet(row["wallet"])
    source_text = ",".join(row.get("sources", [])) or "unknown"
    holder_markets = row.get("holder_markets") or []
    holder_hint = holder_markets[0].get("question") if holder_markets else "none"
    good = "; ".join(row.get("good_reasons") or []) or "none"
    weak = "; ".join(row.get("weak_reasons") or []) or "none"
    obs_rate = row.get("obs_success_rate_24h")
    obs_avg_move = row.get("obs_avg_move_24h")
    obs_early_fail = row.get("obs_early_failure_rate")
    obs_line = "Obs24h: none yet"
    if obs_rate is not None:
        avg_part = f" | avg_move={obs_avg_move:.1%}" if obs_avg_move is not None else ""
        fail_part = f" | early_fail={obs_early_fail:.1%}" if obs_early_fail is not None else ""
        obs_line = f"Obs24h: observed={row.get('obs_observed_total', 0)} | resolved={row.get('obs_resolved_total', 0)} | success={obs_rate:.1%}{avg_part}{fail_part}"
    return "\n".join([
        f"Wallet: {label}",
        f"Bucket: {row.get('bucket')} | Score: {row.get('score', 0.0):.1f}",
        f"30d: pnl={row.get('realized_pnl_30d', 0.0):.2f} | weighted_ret={row.get('weighted_return_30d', 0.0):.1%} | avg_ret={row.get('avg_return_30d', 0.0):.1%}",
        f"30d sample: closed={row.get('closed_positions_30d', 0)} | trades={row.get('trades_30d', 0)} | wins={row.get('win_rate_30d', 0.0):.1%} | 20%+ closes={row.get('consistency_ratio_30d', 0.0):.1%}",
        f"Recent: trades_7d={row.get('recent_trades_7d', 0)} | intraday_signals={row.get('intraday_roundtrips_30d', 0)} | current_positions={row.get('current_positions', 0)}",
        obs_line,
        f"Why: {good}",
        f"Weakness: {weak}",
        f"Discovery: {source_text} | holder_hint={holder_hint}",
    ])


def format_scan_text(scan: Dict[str, Any], manual: bool = False) -> str:
    stats = scan.get("stats", {})
    header = "Manual wallet scan" if manual else "Auto wallet scan"
    lines = [
        header,
        f"script_version={SCRIPT_VERSION}",
        f"evaluated_wallets={stats.get('evaluated_wallets', 0)} | passing_wallets={stats.get('passing_wallets', 0)} | evaluation_errors={stats.get('evaluation_errors', 0)}",
        f"leaderboard_wallets={stats.get('leaderboard_wallets', 0)} | active_markets={stats.get('active_markets', 0)} | holder_wallets={stats.get('holder_wallets', 0)} | unique_candidates={stats.get('unique_candidate_wallets', 0)}",
        f"observation: logged_now={stats.get('obs_logged', 0)} | resolved_now={stats.get('obs_resolved_now', 0)} | open_total={stats.get('obs_open', 0)} | resolved_total={stats.get('obs_resolved', 0)}",
        "",
        "Wallets to test first",
    ]

    rows = scan.get("test_first") or []
    if not rows:
        lines.append("None")
    else:
        for row in rows:
            lines.extend([format_wallet_block(row), ""])

    lines.append("Wallets to watch closely")
    rows = scan.get("watch_closely") or []
    if not rows:
        lines.append("None")
    else:
        for row in rows:
            lines.extend([format_wallet_block(row), ""])

    if not scan.get("test_first") and not scan.get("watch_closely"):
        lines.append("Top rejects")
        rows = scan.get("rejects") or []
        if not rows:
            lines.append("None")
        else:
            for row in rows[:3]:
                lines.extend([format_wallet_block(row), ""])

    return "\n".join(lines).strip()


def format_grouped_summary(grouped: Dict[str, Any]) -> str:
    lines = [
        f"Grouped auto summary for last {grouped.get('window_minutes', 0)} minutes",
        f"script_version={SCRIPT_VERSION}",
        f"scans_in_window={grouped.get('scan_count', 0)} | unique_wallets={grouped.get('wallet_count', 0)}",
        "",
        "Top wallet candidates",
    ]
    rows = grouped.get("top_wallets") or []
    if not rows:
        lines.append("None")
    else:
        for row in rows:
            obs_part = ""
            if row.get("obs_success_rate_24h") is not None:
                obs_part = f" | obs24h={row.get('obs_success_rate_24h', 0.0):.1%}"
            lines.append(
                f"{short_wallet(row['wallet'])} | appearances={row.get('appearances', 0)} | bucket={row.get('bucket')} | score={row.get('score', 0.0):.1f} | 30d_ret={row.get('weighted_return_30d', 0.0):.1%} | wins={row.get('win_rate_30d', 0.0):.1%} | 20%+={row.get('consistency_ratio_30d', 0.0):.1%} | recent7d={row.get('recent_trades_7d', 0)}{obs_part}"
            )

    lines.extend(["", "Observed 24h leaders"])
    obs_rows = grouped.get("observation_leaders") or []
    if not obs_rows:
        lines.append("None")
    else:
        for row in obs_rows:
            name = clean_text(row.get("username") or "")
            label = f"{name} ({short_wallet(row['wallet'])})" if name else short_wallet(row["wallet"])
            avg_part = f" | avg_move={row.get('avg_move_24h', 0.0):.1%}" if row.get("avg_move_24h") is not None else ""
            fail_part = f" | early_fail={row.get('early_failure_rate', 0.0):.1%}" if row.get("early_failure_rate") is not None else ""
            lines.append(
                f"{label} | resolved={row.get('resolved_total', 0)} | success={row.get('success_rate_24h', 0.0):.1%}{avg_part}{fail_part} | score={row.get('latest_score', 0.0):.1f}"
            )
    return "\n".join(lines)


def format_observation_text() -> str:
    stats = get_observation_stats()
    lines = [
        "Observation journal",
        f"script_version={SCRIPT_VERSION}",
        f"obs_total={stats.get('obs_total', 0)} | open={stats.get('obs_open', 0)} | resolved={stats.get('obs_resolved', 0)}",
        "",
        "Top observed wallets",
    ]
    rows = top_observed_wallets(limit=10)
    if not rows:
        lines.append("None")
        return "\n".join(lines)
    for row in rows:
        name = clean_text(row.get("username") or "")
        label = f"{name} ({short_wallet(row['wallet'])})" if name else short_wallet(row["wallet"])
        avg_part = f" | avg_move={row.get('avg_move_24h', 0.0):.1%}" if row.get("avg_move_24h") is not None else ""
        fail_part = f" | early_fail={row.get('early_failure_rate', 0.0):.1%}" if row.get("early_failure_rate") is not None else ""
        lines.append(
            f"{label} | observed={row.get('observed_total', 0)} | resolved={row.get('resolved_total', 0)} | success={row.get('success_rate_24h', 0.0):.1%}{avg_part}{fail_part}"
        )
    return "\n".join(lines)


def format_health_text() -> str:
    last = runtime_state.get("last_health", {})
    sess = runtime_state.get("session_summary", {})
    obs = get_observation_stats()
    return "\n".join([
        "Health check",
        f"script_version={SCRIPT_VERSION}",
        f"scan_every_seconds={SCAN_EVERY_SECONDS}",
        f"group_window_seconds={GROUP_WINDOW_SECONDS}",
        f"lookback_days={LOOKBACK_DAYS}",
        f"leaderboard_limit={LEADERBOARD_LIMIT}",
        f"active_market_limit={ACTIVE_MARKET_LIMIT}",
        f"holders_per_market={HOLDERS_PER_MARKET}",
        f"min_closed_positions_30d={MIN_CLOSED_POSITIONS_30D}",
        f"min_trades_30d={MIN_TRADES_30D}",
        f"min_weighted_return_30d={MIN_WEIGHTED_RETURN_30D}",
        f"min_win_rate_30d={MIN_WIN_RATE_30D}",
        f"min_consistency_ratio={MIN_CONSISTENCY_RATIO}",
        f"min_recent_trades_7d={MIN_RECENT_TRADES_7D}",
        f"obs_enabled={OBS_ENABLED} | obs_lookahead_hours={OBS_LOOKAHEAD_HOURS} | obs_min_move_pct={OBS_MIN_MOVE_PCT}",
        f"manual_scan_in_progress={manual_scan_in_progress}",
        f"session_scans={sess.get('scans', 0)} | wallets_evaluated_total={sess.get('wallets_evaluated', 0)} | wallets_passing_total={sess.get('wallets_passing', 0)}",
        f"obs_logged_total={sess.get('obs_logged_total', 0)} | obs_resolved_total={sess.get('obs_resolved_total', 0)} | db_open={obs.get('obs_open', 0)} | db_resolved={obs.get('obs_resolved', 0)}",
        f"last_evaluated_wallets={last.get('evaluated_wallets', 0)} | last_passing_wallets={last.get('passing_wallets', 0)} | last_errors={last.get('evaluation_errors', 0)}",
        f"last_group_top_count={sess.get('last_group_top_count', 0)} | last_scan_top_count={sess.get('last_scan_top_count', 0)}",
    ])


# =========================================================
# Commands and background
# =========================================================
def run_scan_and_update() -> Dict[str, Any]:
    scan = scan_once()
    append_scan_to_group(scan)
    save_state()
    return scan


def handle_command(text: str) -> str:
    cmd = (text or "").strip().lower()
    if cmd.startswith("/health"):
        return format_health_text()
    if cmd.startswith("/scan"):
        return "__RUN_SCAN_ASYNC__"
    if cmd.startswith("/group"):
        return format_grouped_summary(build_grouped_summary())
    if cmd.startswith("/observe") or cmd.startswith("/journal"):
        return format_observation_text()
    return "Commands: /health, /scan, /group, /observe"


def run_manual_scan_async(chat_id: str) -> None:
    global manual_scan_in_progress
    try:
        scan = run_scan_and_update()
        reply = format_scan_text(scan, manual=True)
        if TELEGRAM_BOT_TOKEN and chat_id:
            requests.post(
                f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
                json={"chat_id": chat_id, "text": reply},
                timeout=REQUEST_TIMEOUT,
            )
    except Exception as exc:
        if TELEGRAM_BOT_TOKEN and chat_id:
            try:
                requests.post(
                    f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
                    json={"chat_id": chat_id, "text": f"Scan error: {exc}"},
                    timeout=REQUEST_TIMEOUT,
                )
            except Exception:
                pass
    finally:
        with state_lock:
            manual_scan_in_progress = False


def background_loop() -> None:
    while True:
        time.sleep(max(30, SCAN_EVERY_SECONDS))
        try:
            run_scan_and_update()
            now_s = utc_ts()
            last_sent = runtime_state.get("last_group_sent_at", 0.0)
            if now_s - last_sent >= GROUP_WINDOW_SECONDS:
                grouped = build_grouped_summary()
                if grouped.get("top_wallets") or grouped.get("observation_leaders"):
                    send_telegram(format_grouped_summary(grouped))
                    runtime_state["last_group_sent_at"] = now_s
                    runtime_state["session_summary"]["last_group_top_count"] = len(grouped.get("top_wallets") or [])
                    save_state()
                elif SEND_ZERO_GROUP_SUMMARY:
                    send_telegram(format_grouped_summary(grouped))
                    runtime_state["last_group_sent_at"] = now_s
                    runtime_state["session_summary"]["last_group_top_count"] = 0
                    save_state()
        except Exception as exc:
            send_telegram(f"Background scan error: {exc}")


def ensure_background_started() -> None:
    global background_started
    if background_started:
        return
    background_started = True
    threading.Thread(target=background_loop, daemon=True).start()


# =========================================================
# Flask routes
# =========================================================
@app.route("/health", methods=["GET"])
def health_route():
    return format_health_text(), 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.route("/scan", methods=["GET"])
def scan_route():
    scan = run_scan_and_update()
    return format_scan_text(scan, manual=True), 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.route("/group", methods=["GET"])
def group_route():
    return format_grouped_summary(build_grouped_summary()), 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.route("/observe", methods=["GET"])
def observe_route():
    return format_observation_text(), 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.route("/webhook", methods=["POST"])
def webhook_route():
    global manual_scan_in_progress
    payload = request.get_json(silent=True) or {}
    msg = payload.get("message") or payload.get("edited_message") or {}
    chat_id = str(msg.get("chat", {}).get("id") or "").strip()
    text = msg.get("text", "")
    reply = handle_command(text)

    if reply == "__RUN_SCAN_ASYNC__":
        with state_lock:
            if manual_scan_in_progress:
                if TELEGRAM_BOT_TOKEN and chat_id:
                    try:
                        requests.post(
                            f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
                            json={"chat_id": chat_id, "text": "Scan already running. Wait for result."},
                            timeout=REQUEST_TIMEOUT,
                        )
                    except Exception:
                        pass
                return jsonify({"ok": True})
            manual_scan_in_progress = True

        if TELEGRAM_BOT_TOKEN and chat_id:
            try:
                requests.post(
                    f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
                    json={"chat_id": chat_id, "text": "Running wallet scan..."},
                    timeout=REQUEST_TIMEOUT,
                )
            except Exception:
                pass
        threading.Thread(target=run_manual_scan_async, args=(chat_id,), daemon=True).start()
        return jsonify({"ok": True})

    if TELEGRAM_BOT_TOKEN and chat_id and reply:
        try:
            requests.post(
                f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
                json={"chat_id": chat_id, "text": reply},
                timeout=REQUEST_TIMEOUT,
            )
        except Exception:
            pass
    return jsonify({"ok": True})


# =========================================================
# Main
# =========================================================
init_db()
load_state()
ensure_background_started()

if __name__ == "__main__":
    port = int(os.getenv("PORT", "10000"))
    app.run(host="0.0.0.0", port=port)
