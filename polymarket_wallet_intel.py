import os
import time
import json
import math
import threading
from datetime import datetime, timezone
from collections import Counter, defaultdict
from typing import Any, Dict, List, Optional, Tuple

import requests
from flask import Flask, request, Response

SCRIPT_VERSION = "wallet-intel-v8.1-official-apis"

app = Flask(__name__)

# =========================
# Environment
# =========================
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()

SCAN_EVERY_SECONDS = int(os.getenv("SCAN_EVERY_SECONDS", "1800"))
GROUP_WINDOW_SECONDS = int(os.getenv("GROUP_WINDOW_SECONDS", "10800"))

REQUEST_TIMEOUT = float(os.getenv("REQUEST_TIMEOUT", "12"))
REQUEST_CONNECT_TIMEOUT = float(os.getenv("REQUEST_CONNECT_TIMEOUT", "5"))

LEADERBOARD_LIMIT = int(os.getenv("LEADERBOARD_LIMIT", "100"))
ACTIVE_MARKET_LIMIT = int(os.getenv("ACTIVE_MARKET_LIMIT", "40"))
HOLDERS_PER_MARKET = int(os.getenv("HOLDERS_PER_MARKET", "15"))
MAX_CANDIDATE_WALLETS = int(os.getenv("MAX_CANDIDATE_WALLETS", "120"))

MANUAL_LEADERBOARD_LIMIT = int(os.getenv("MANUAL_LEADERBOARD_LIMIT", "25"))
MANUAL_ACTIVE_MARKET_LIMIT = int(os.getenv("MANUAL_ACTIVE_MARKET_LIMIT", "20"))
MANUAL_HOLDERS_PER_MARKET = int(os.getenv("MANUAL_HOLDERS_PER_MARKET", "10"))
MANUAL_MAX_CANDIDATE_WALLETS = int(os.getenv("MANUAL_MAX_CANDIDATE_WALLETS", "40"))
MANUAL_SCAN_DEADLINE_SECONDS = int(os.getenv("MANUAL_SCAN_DEADLINE_SECONDS", "45"))
MANUAL_SEND_CACHED_FIRST = os.getenv("MANUAL_SEND_CACHED_FIRST", "true").lower() == "true"

MIN_CLOSED_POSITIONS_30D = int(os.getenv("MIN_CLOSED_POSITIONS_30D", "8"))
MIN_TRADES_30D = int(os.getenv("MIN_TRADES_30D", "8"))
MIN_WEIGHTED_RETURN_30D = float(os.getenv("MIN_WEIGHTED_RETURN_30D", "0.12"))
MIN_WIN_RATE_30D = float(os.getenv("MIN_WIN_RATE_30D", "0.52"))
MIN_CONSISTENCY_RATIO = float(os.getenv("MIN_CONSISTENCY_RATIO", "0.35"))
MIN_RECENT_TRADES_7D = int(os.getenv("MIN_RECENT_TRADES_7D", "1"))

OBSERVE_RECENT_HOURS = int(os.getenv("OBSERVE_RECENT_HOURS", "24"))
OBS_SUCCESS_THRESHOLD = float(os.getenv("OBS_SUCCESS_THRESHOLD", "0.03"))
SIMILAR_WALLETS_LIMIT = int(os.getenv("SIMILAR_WALLETS_LIMIT", "3"))

EXCLUDE_SPORTS_WALLETS = os.getenv("EXCLUDE_SPORTS_WALLETS", "true").lower() == "true"
SPORTS_RATIO_CLOSED_MAX = float(os.getenv("SPORTS_RATIO_CLOSED_MAX", "0.40"))
SPORTS_RATIO_TRADES_MAX = float(os.getenv("SPORTS_RATIO_TRADES_MAX", "0.50"))
SPORTS_RATIO_CURRENT_MAX = float(os.getenv("SPORTS_RATIO_CURRENT_MAX", "0.50"))
SPORTS_RATIO_HOLDER_HINT_MAX = float(os.getenv("SPORTS_RATIO_HOLDER_HINT_MAX", "0.50"))

# =========================
# Endpoints (official public APIs)
# =========================
DATA_API = "https://data-api.polymarket.com"
GAMMA_API = "https://gamma-api.polymarket.com"
CLOB_API = "https://clob.polymarket.com"

# =========================
# Runtime state
# =========================
SESSION = requests.Session()
LOCK = threading.Lock()
SCAN_HISTORY: List[Dict[str, Any]] = []
LAST_CANDIDATES: List[Dict[str, Any]] = []
LAST_SCAN_META: Dict[str, Any] = {}
LAST_GROUP_TOP_COUNT = 0
BACKGROUND_STARTED = False
MANUAL_SCAN_IN_PROGRESS = False
OBSERVATION_LOG: List[Dict[str, Any]] = []  # lightweight in-memory; enough for current use

# =========================
# Helpers
# =========================
def utc_now() -> datetime:
    return datetime.now(timezone.utc)

def iso_now() -> str:
    return utc_now().isoformat()

def safe_float(v: Any, default: float = 0.0) -> float:
    try:
        if v in (None, "", "None"):
            return default
        return float(v)
    except Exception:
        return default

def safe_int(v: Any, default: int = 0) -> int:
    try:
        if v in (None, "", "None"):
            return default
        return int(float(v))
    except Exception:
        return default

def pct(x: float) -> str:
    return f"{x * 100:.1f}%"

def clamp(x: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, x))

def parse_ts(value: Any) -> Optional[datetime]:
    if value is None:
        return None
    if isinstance(value, (int, float)):
        try:
            if value > 1e12:
                return datetime.fromtimestamp(value / 1000.0, tz=timezone.utc)
            return datetime.fromtimestamp(value, tz=timezone.utc)
        except Exception:
            return None
    s = str(value).strip()
    if not s:
        return None
    try:
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        return datetime.fromisoformat(s)
    except Exception:
        pass
    # try numeric string
    try:
        num = float(s)
        if num > 1e12:
            return datetime.fromtimestamp(num / 1000.0, tz=timezone.utc)
        return datetime.fromtimestamp(num, tz=timezone.utc)
    except Exception:
        return None

def age_hours(ts: Optional[datetime]) -> float:
    if not ts:
        return 1e9
    return (utc_now() - ts).total_seconds() / 3600.0

def category_from_text(text: str) -> str:
    t = (text or "").lower()
    if any(k in t for k in ["trump", "biden", "election", "senate", "house", "president", "cabinet", "campaign", "gop", "democrat", "republican"]):
        return "politics"
    if any(k in t for k in ["fed", "cpi", "inflation", "recession", "jobs report", "treasury", "tariff", "gdp", "economy", "rate cut", "rate hike"]):
        return "macro"
    if any(k in t for k in ["bitcoin", "btc", "ethereum", "eth", "solana", "crypto", "coin", "token"]):
        return "crypto"
    if any(k in t for k in ["court", "scotus", "lawsuit", "judge", "indict", "legal", "trial"]):
        return "legal"
    if any(k in t for k in ["war", "ukraine", "russia", "israel", "iran", "china", "taiwan", "nato", "ceasefire"]):
        return "geopolitics"
    if is_sports_text(t):
        return "sports"
    return "other"

def is_sports_text(text: str) -> bool:
    t = (text or "").lower()
    sports_terms = [
        "nba", "nfl", "mlb", "nhl", "ncaa", "soccer", "football", "baseball", "basketball", "tennis",
        "golf", "fight", "ufc", "boxing", "match", "game", "final", "super bowl", "world series",
        "premier league", "champions league", "f1", "formula 1", "olympics", "player", "team", "score"
    ]
    return any(term in t for term in sports_terms)

def sports_ratio(sports_count: int, total_count: int) -> float:
    if total_count <= 0:
        return 0.0
    return sports_count / float(total_count)

def wallet_profile_url(wallet: str) -> str:
    return f"https://polymarket.com/profile/{wallet}"

def send_telegram(text: str) -> None:
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        return
    try:
        SESSION.post(
            f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
            json={"chat_id": TELEGRAM_CHAT_ID, "text": text},
            timeout=(REQUEST_CONNECT_TIMEOUT, REQUEST_TIMEOUT),
        )
    except Exception:
        pass

def http_get(url: str, params: Optional[Dict[str, Any]] = None) -> Any:
    resp = SESSION.get(url, params=params or {}, timeout=(REQUEST_CONNECT_TIMEOUT, REQUEST_TIMEOUT))
    resp.raise_for_status()
    # Some endpoints return non-json only rarely; keep safe
    ctype = resp.headers.get("content-type", "")
    if "application/json" in ctype or resp.text[:1] in "[{":
        return resp.json()
    return resp.text

def coerce_rows(data: Any) -> List[Dict[str, Any]]:
    if isinstance(data, list):
        return [r for r in data if isinstance(r, dict)]
    if isinstance(data, dict):
        for key in ("data", "items", "results", "positions", "trades", "markets", "events", "profiles"):
            val = data.get(key)
            if isinstance(val, list):
                return [r for r in val if isinstance(r, dict)]
    return []

# =========================
# Official API adapters
# =========================
def api_leaderboard(limit: int) -> List[Dict[str, Any]]:
    # Official docs mention /v1/leaderboard
    data = http_get(f"{DATA_API}/v1/leaderboard", params={"limit": limit})
    rows = coerce_rows(data)
    cleaned = []
    for row in rows:
        wallet = row.get("proxyWallet") or row.get("wallet") or row.get("address")
        if not wallet:
            continue
        cleaned.append({
            "wallet": wallet,
            "username": row.get("displayUsernamePublic") or row.get("username") or row.get("pseudonym") or row.get("bio"),
            "source": "leaderboard",
            "leaderboard_row": row,
        })
    return cleaned

def api_markets(limit: int) -> List[Dict[str, Any]]:
    params = {
        "closed": "false",
        "limit": limit,
    }
    data = http_get(f"{GAMMA_API}/markets", params=params)
    rows = coerce_rows(data)
    cleaned = []
    for row in rows:
        market_text = " ".join(str(row.get(k, "")) for k in ("question", "description", "title", "slug"))
        category = category_from_text(market_text)
        row["_category"] = category
        cleaned.append(row)
    return cleaned

def api_holders(token_ids: List[str]) -> List[Dict[str, Any]]:
    if not token_ids:
        return []
    data = http_get(f"{DATA_API}/holders", params={"market": ",".join(token_ids[:50])})
    rows = coerce_rows(data)
    wallets = []
    # docs show nested token -> holders
    for token_block in rows:
        block_text = " ".join(str(token_block.get(k, "")) for k in ("question", "title", "slug"))
        block_category = category_from_text(block_text)
        holders = token_block.get("holders") or []
        if not isinstance(holders, list):
            continue
        for h in holders:
            if not isinstance(h, dict):
                continue
            wallet = h.get("proxyWallet") or h.get("wallet") or h.get("address")
            if not wallet:
                continue
            wallets.append({
                "wallet": wallet,
                "username": h.get("displayUsernamePublic") or h.get("username") or h.get("pseudonym") or h.get("bio"),
                "source": "holder",
                "holder_hint_category": block_category,
                "holder_row": h,
            })
    return wallets

def api_public_profile(wallet: str) -> Dict[str, Any]:
    # endpoint available in docs, defensive if unavailable
    try:
        data = http_get(f"{DATA_API}/profile/{wallet}")
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def api_closed_positions(wallet: str) -> List[Dict[str, Any]]:
    try:
        data = http_get(f"{DATA_API}/positions", params={"user": wallet, "sizeThreshold": 0, "redeemed": "true"})
        rows = coerce_rows(data)
        if rows:
            return rows
    except Exception:
        pass
    try:
        data = http_get(f"{DATA_API}/closed-positions", params={"user": wallet})
        rows = coerce_rows(data)
        return rows
    except Exception:
        return []

def api_current_positions(wallet: str) -> List[Dict[str, Any]]:
    # docs mention current positions for a user
    for url in [f"{DATA_API}/positions", f"{DATA_API}/current-positions"]:
        try:
            data = http_get(url, params={"user": wallet, "sizeThreshold": 0, "redeemed": "false"})
            rows = coerce_rows(data)
            if rows:
                return rows
        except Exception:
            continue
    return []

def api_user_activity(wallet: str) -> List[Dict[str, Any]]:
    try:
        data = http_get(f"{DATA_API}/activity", params={"user": wallet})
        return coerce_rows(data)
    except Exception:
        return []

def api_user_trades(wallet: str) -> List[Dict[str, Any]]:
    try:
        data = http_get(f"{DATA_API}/trades", params={"user": wallet})
        return coerce_rows(data)
    except Exception:
        return []

def api_prices_history(token_id: str) -> List[Dict[str, Any]]:
    try:
        data = http_get(f"{CLOB_API}/prices-history", params={"market": token_id, "interval": "max"})
        rows = coerce_rows(data)
        if rows:
            return rows
        if isinstance(data, dict) and isinstance(data.get("history"), list):
            return [r for r in data["history"] if isinstance(r, dict)]
    except Exception:
        return []
    return []

# =========================
# Parsing / derived metrics
# =========================
def infer_position_question(row: Dict[str, Any]) -> str:
    for k in ("question", "title", "marketQuestion", "marketTitle", "name", "slug"):
        if row.get(k):
            return str(row.get(k))
    if row.get("market"):
        market = row["market"]
        if isinstance(market, dict):
            for k in ("question", "title", "slug"):
                if market.get(k):
                    return str(market.get(k))
    return ""

def infer_token_id(row: Dict[str, Any]) -> str:
    for k in ("asset", "token", "tokenId", "token_id", "clobTokenId"):
        if row.get(k):
            return str(row.get(k))
    if isinstance(row.get("market"), dict):
        for k in ("asset", "token", "tokenId", "token_id", "clobTokenId"):
            if row["market"].get(k):
                return str(row["market"].get(k))
    return ""

def infer_pnl_and_cost(row: Dict[str, Any]) -> Tuple[float, float]:
    pnl_keys = ("pnl", "realizedPnl", "profit", "profitLoss", "cashPnl")
    cost_keys = ("cost", "amountBought", "totalSpent", "initialValue", "basis", "positionValue")
    pnl = 0.0
    cost = 0.0
    for k in pnl_keys:
        if row.get(k) is not None:
            pnl = safe_float(row.get(k))
            break
    for k in cost_keys:
        if row.get(k) is not None:
            cost = abs(safe_float(row.get(k)))
            break
    if cost <= 0:
        # fallback from size * avgPrice
        size = abs(safe_float(row.get("size") or row.get("shares")))
        avg_price = safe_float(row.get("avgPrice") or row.get("averagePrice") or row.get("price"))
        cost = size * avg_price
    return pnl, cost

def summarize_closed_positions(rows: List[Dict[str, Any]]) -> Dict[str, Any]:
    summary = {
        "count": 0,
        "wins": 0,
        "pnl": 0.0,
        "cost": 0.0,
        "avg_return": 0.0,
        "weighted_return": 0.0,
        "consistency_over_20": 0.0,
        "category_stats": defaultdict(lambda: {"count": 0, "wins": 0, "pnl": 0.0, "cost": 0.0, "returns": []}),
        "sports_count": 0,
    }
    returns: List[float] = []
    over20 = 0
    for row in rows:
        q = infer_position_question(row)
        cat = category_from_text(q)
        pnl, cost = infer_pnl_and_cost(row)
        ret = (pnl / cost) if cost > 0 else 0.0
        ts = parse_ts(row.get("endDate") or row.get("closedAt") or row.get("updatedAt") or row.get("createdAt"))
        if age_hours(ts) > 24 * 30:
            continue
        summary["count"] += 1
        summary["pnl"] += pnl
        summary["cost"] += cost
        if pnl > 0:
            summary["wins"] += 1
        returns.append(ret)
        if ret >= 0.20:
            over20 += 1
        c = summary["category_stats"][cat]
        c["count"] += 1
        c["pnl"] += pnl
        c["cost"] += cost
        if pnl > 0:
            c["wins"] += 1
        c["returns"].append(ret)
        if cat == "sports":
            summary["sports_count"] += 1

    if summary["count"] > 0:
        summary["avg_return"] = sum(returns) / len(returns)
        summary["weighted_return"] = (summary["pnl"] / summary["cost"]) if summary["cost"] > 0 else 0.0
        summary["consistency_over_20"] = over20 / summary["count"]
    return summary

def summarize_trades(rows: List[Dict[str, Any]]) -> Dict[str, Any]:
    summary = {
        "count_30d": 0,
        "count_7d": 0,
        "sports_count": 0,
        "entry_hours": [],
        "categories": Counter(),
        "intraday_signals": 0,
        "timing_style": "unknown",
        "best_category": "other",
        "dominant_entry_hour_utc": None,
        "top_category_count": 0,
        "top_category_win_rate": 0.0,  # will be filled from closed positions
    }
    for row in rows:
        ts = parse_ts(row.get("createdAt") or row.get("timestamp") or row.get("time") or row.get("matchedAt"))
        if age_hours(ts) > 24 * 30:
            continue
        summary["count_30d"] += 1
        if age_hours(ts) <= 24 * 7:
            summary["count_7d"] += 1
        q = infer_position_question(row)
        cat = category_from_text(q)
        summary["categories"][cat] += 1
        if cat == "sports":
            summary["sports_count"] += 1
        if ts:
            summary["entry_hours"].append(ts.hour)
        side = str(row.get("side", "")).upper()
        price = safe_float(row.get("price") or row.get("avgPrice"))
        size = abs(safe_float(row.get("size") or row.get("shares")))
        # crude intraday signal proxy: sized non-dust entry in tradable price band
        if side in {"BUY", "SELL", "YES", "NO"} and 0.03 <= price <= 0.97 and size > 0:
            summary["intraday_signals"] += 1

    if summary["categories"]:
        summary["best_category"], summary["top_category_count"] = summary["categories"].most_common(1)[0]
    if summary["entry_hours"]:
        hour_counts = Counter(summary["entry_hours"])
        summary["dominant_entry_hour_utc"] = hour_counts.most_common(1)[0][0]

    # timing style from hourly concentration and recent activity
    if summary["count_30d"] >= 10 and summary["dominant_entry_hour_utc"] is not None:
        concentration = Counter(summary["entry_hours"]).most_common(1)[0][1] / max(1, len(summary["entry_hours"]))
        if concentration >= 0.35 and summary["count_7d"] >= 5:
            summary["timing_style"] = "time-clustered"
        elif summary["count_7d"] >= 10:
            summary["timing_style"] = "active-intraday"
        else:
            summary["timing_style"] = "mixed"
    return summary

def summarize_current_positions(rows: List[Dict[str, Any]]) -> Dict[str, Any]:
    count = 0
    sports = 0
    concentration_cost = 0.0
    total_cost = 0.0
    for row in rows:
        count += 1
        q = infer_position_question(row)
        if category_from_text(q) == "sports":
            sports += 1
        _, cost = infer_pnl_and_cost(row)
        total_cost += cost
        concentration_cost = max(concentration_cost, cost)
    concentration_ratio = (concentration_cost / total_cost) if total_cost > 0 else 0.0
    return {"count": count, "sports_count": sports, "concentration_ratio": concentration_ratio}

def build_pattern(closed_summary: Dict[str, Any], trade_summary: Dict[str, Any]) -> Dict[str, Any]:
    # closed-trade trend
    best_cat = "other"
    best_cat_wr = 0.0
    best_cat_ret = 0.0
    for cat, stat in closed_summary["category_stats"].items():
        if stat["count"] <= 0:
            continue
        wr = stat["wins"] / stat["count"]
        ret = (stat["pnl"] / stat["cost"]) if stat["cost"] > 0 else 0.0
        score = wr * 0.6 + ret * 0.4
        if score > (best_cat_wr * 0.6 + best_cat_ret * 0.4):
            best_cat = cat
            best_cat_wr = wr
            best_cat_ret = ret

    dominant_hour = trade_summary["dominant_entry_hour_utc"]
    timing = trade_summary["timing_style"]
    if dominant_hour is None:
        timing_label = timing
    else:
        timing_label = f"{timing}@{dominant_hour:02d}UTC"

    # rough best observation window
    if trade_summary["intraday_signals"] >= 8:
        best_window = "1h-6h"
    elif trade_summary["count_7d"] >= 4:
        best_window = "6h-24h"
    else:
        best_window = "24h+"

    cluster = f"{best_cat}:{'fast-entry' if 'intraday' in timing or 'clustered' in timing else 'patient-hold'}"
    trend = f"{best_cat} wr={pct(best_cat_wr)} avg_ret={pct(best_cat_ret)}"
    return {
        "best_category": best_cat,
        "top_category_win_rate": best_cat_wr,
        "top_category_avg_return": best_cat_ret,
        "dominant_entry_hour_utc": dominant_hour,
        "timing_style": timing,
        "best_window": best_window,
        "cluster": cluster,
        "closed_trade_trend": trend,
        "summary": f"category={best_cat} | cat_wr={pct(best_cat_wr)} | entry_hour={dominant_hour if dominant_hour is not None else 'none'} | timing={timing} | best_window={best_window}",
    }

def vectorize_wallet(w: Dict[str, Any]) -> List[float]:
    cat_map = {"politics": 1, "macro": 2, "crypto": 3, "legal": 4, "geopolitics": 5, "other": 6}
    return [
        safe_float(w.get("weighted_return_30d")),
        safe_float(w.get("win_rate_30d")),
        safe_float(w.get("consistency_ratio")),
        safe_float(w.get("recent_trades_7d")) / 50.0,
        float(cat_map.get(w.get("pattern", {}).get("best_category"), 6)) / 6.0,
        (safe_float(w.get("pattern", {}).get("dominant_entry_hour_utc"), 12.0) / 24.0),
        safe_float(w.get("current_positions_count")) / 20.0,
    ]

def distance(a: List[float], b: List[float]) -> float:
    n = min(len(a), len(b))
    return math.sqrt(sum((a[i] - b[i]) ** 2 for i in range(n)))

def attach_similar_wallets(wallets: List[Dict[str, Any]]) -> None:
    vecs = {w["wallet"]: vectorize_wallet(w) for w in wallets}
    for w in wallets:
        dists = []
        for other in wallets:
            if other["wallet"] == w["wallet"]:
                continue
            d = distance(vecs[w["wallet"]], vecs[other["wallet"]])
            dists.append((d, other))
        dists.sort(key=lambda x: x[0])
        sims = []
        for _, other in dists[:SIMILAR_WALLETS_LIMIT]:
            sims.append(other["wallet"])
        w["similar_wallets"] = sims

# =========================
# Evaluation
# =========================
def evaluate_wallet(candidate: Dict[str, Any]) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    wallet = candidate["wallet"]

    closed_rows = api_closed_positions(wallet)
    trade_rows = api_user_trades(wallet)
    current_rows = api_current_positions(wallet)
    profile = api_public_profile(wallet)

    closed_summary = summarize_closed_positions(closed_rows)
    trade_summary = summarize_trades(trade_rows)
    current_summary = summarize_current_positions(current_rows)
    pattern = build_pattern(closed_summary, trade_summary)

    # enrich username
    username = (
        candidate.get("username")
        or profile.get("displayUsernamePublic")
        or profile.get("username")
        or profile.get("pseudonym")
        or "none"
    )

    # sports filter as ratio, not hard any-touch
    if EXCLUDE_SPORTS_WALLETS:
        holder_hint_cat = candidate.get("holder_hint_category")
        holder_hint_sports = 1 if holder_hint_cat == "sports" else 0
        closed_sports_ratio = sports_ratio(closed_summary["sports_count"], closed_summary["count"])
        trade_sports_ratio = sports_ratio(trade_summary["sports_count"], trade_summary["count_30d"])
        current_sports_ratio = sports_ratio(current_summary["sports_count"], current_summary["count"])
        holder_hint_ratio = float(holder_hint_sports)
        if (
            closed_sports_ratio > SPORTS_RATIO_CLOSED_MAX
            or trade_sports_ratio > SPORTS_RATIO_TRADES_MAX
            or current_sports_ratio > SPORTS_RATIO_CURRENT_MAX
            or holder_hint_ratio > SPORTS_RATIO_HOLDER_HINT_MAX
        ):
            return None, "sports_dominant"

    if closed_summary["count"] < MIN_CLOSED_POSITIONS_30D:
        return None, "not_enough_closed_positions"
    if trade_summary["count_30d"] < MIN_TRADES_30D:
        return None, "not_enough_trades"
    if closed_summary["weighted_return"] < MIN_WEIGHTED_RETURN_30D:
        return None, "weighted_return_too_low"

    win_rate = (closed_summary["wins"] / closed_summary["count"]) if closed_summary["count"] > 0 else 0.0
    if win_rate < MIN_WIN_RATE_30D:
        return None, "win_rate_too_low"
    if closed_summary["consistency_over_20"] < MIN_CONSISTENCY_RATIO:
        return None, "consistency_too_low"
    if trade_summary["count_7d"] < MIN_RECENT_TRADES_7D:
        return None, "recent_activity_too_low"

    # score
    score = 0.0
    score += clamp(closed_summary["weighted_return"], 0, 1.0) * 40
    score += clamp(win_rate, 0, 1.0) * 25
    score += clamp(closed_summary["consistency_over_20"], 0, 1.0) * 15
    score += clamp(trade_summary["count_7d"] / 25.0, 0, 1.0) * 10
    score += clamp(1.0 - current_summary["concentration_ratio"], 0, 1.0) * 5
    score += clamp((1 if pattern["best_category"] != "sports" else 0), 0, 1) * 5

    # light realism penalty
    if win_rate >= 0.98 and closed_summary["count"] < 15:
        score -= 8
    if trade_summary["count_30d"] >= 100:
        score -= 3

    bucket = "TEST FIRST" if score >= 72 else "WATCH CLOSELY"

    out = {
        "wallet": wallet,
        "username": username,
        "profile": wallet_profile_url(wallet),
        "source": candidate.get("source", "unknown"),
        "score": round(score, 1),
        "bucket": bucket,
        "pnl_30d": round(closed_summary["pnl"], 2),
        "weighted_return_30d": round(closed_summary["weighted_return"], 4),
        "avg_return_30d": round(closed_summary["avg_return"], 4),
        "closed_positions_30d": closed_summary["count"],
        "trades_30d": trade_summary["count_30d"],
        "recent_trades_7d": trade_summary["count_7d"],
        "win_rate_30d": round(win_rate, 4),
        "consistency_ratio": round(closed_summary["consistency_over_20"], 4),
        "intraday_signals": trade_summary["intraday_signals"],
        "current_positions_count": current_summary["count"],
        "pattern": pattern,
    }
    return out, None

# =========================
# Discovery
# =========================
def discover_candidates(leaderboard_limit: int, active_market_limit: int, holders_per_market: int, max_candidates: int) -> Dict[str, Any]:
    leaderboard = api_leaderboard(leaderboard_limit)
    markets = api_markets(active_market_limit)

    # holder discovery from non-sports markets only
    holder_wallets: List[Dict[str, Any]] = []
    token_ids: List[str] = []
    for m in markets:
        if category_from_text(" ".join(str(m.get(k, "")) for k in ("question", "title", "slug", "description"))) == "sports":
            continue
        tid = infer_token_id(m)
        if tid:
            token_ids.append(tid)
    if token_ids:
        raw_holders = api_holders(token_ids[:active_market_limit])
        # take per-market top N
        holder_wallets = raw_holders[: max(0, holders_per_market * max(1, len(token_ids)))]

    # merge + dedupe
    merged = []
    seen = set()
    for row in leaderboard + holder_wallets:
        wallet = row["wallet"].lower()
        if wallet in seen:
            continue
        seen.add(wallet)
        merged.append(row)
        if len(merged) >= max_candidates:
            break

    return {
        "leaderboard_wallets": leaderboard,
        "markets": markets,
        "holder_wallets": holder_wallets,
        "candidates": merged,
    }

# =========================
# Observation (lightweight)
# =========================
def update_observation_log(wallets: List[Dict[str, Any]]) -> Dict[str, int]:
    now = utc_now()
    # prune old
    fresh = []
    for row in OBSERVATION_LOG:
        ts = parse_ts(row.get("logged_at"))
        if ts and age_hours(ts) <= OBSERVE_RECENT_HOURS:
            fresh.append(row)
    OBSERVATION_LOG[:] = fresh

    added = 0
    for w in wallets:
        OBSERVATION_LOG.append({
            "logged_at": now.isoformat(),
            "wallet": w["wallet"],
            "score": w["score"],
            "bucket": w["bucket"],
            "best_category": w["pattern"]["best_category"],
            "timing_style": w["pattern"]["timing_style"],
        })
        added += 1
    return {"logged": added, "eval_1h": 0, "eval_6h": 0, "eval_24h": 0}

# =========================
# Scan engine
# =========================
def run_wallet_scan(manual: bool = False) -> Dict[str, Any]:
    start = time.time()
    deadline = start + MANUAL_SCAN_DEADLINE_SECONDS if manual else start + max(60, MANUAL_SCAN_DEADLINE_SECONDS * 2)

    lb_limit = MANUAL_LEADERBOARD_LIMIT if manual else LEADERBOARD_LIMIT
    mk_limit = MANUAL_ACTIVE_MARKET_LIMIT if manual else ACTIVE_MARKET_LIMIT
    holders_per = MANUAL_HOLDERS_PER_MARKET if manual else HOLDERS_PER_MARKET
    max_candidates = MANUAL_MAX_CANDIDATE_WALLETS if manual else MAX_CANDIDATE_WALLETS

    discovery = discover_candidates(lb_limit, mk_limit, holders_per, max_candidates)

    evaluated = 0
    evaluation_errors = 0
    reject_counts = Counter()
    passing: List[Dict[str, Any]] = []

    for c in discovery["candidates"]:
        if time.time() > deadline:
            break
        try:
            out, reject = evaluate_wallet(c)
            evaluated += 1
            if out is not None:
                passing.append(out)
            elif reject:
                reject_counts[reject] += 1
        except Exception:
            evaluation_errors += 1
            reject_counts["evaluation_error"] += 1

    passing.sort(key=lambda x: x["score"], reverse=True)
    attach_similar_wallets(passing)
    obs = update_observation_log(passing)

    test_first = [w for w in passing if w["bucket"] == "TEST FIRST"]
    watch = [w for w in passing if w["bucket"] == "WATCH CLOSELY"]

    # fallback display if bucketing gets thin
    if not test_first and not watch and passing:
        test_first = passing[: min(5, len(passing))]

    result = {
        "script_version": SCRIPT_VERSION,
        "generated_at": iso_now(),
        "evaluated_wallets": evaluated,
        "passing_wallets": len(passing),
        "evaluation_errors": evaluation_errors,
        "leaderboard_wallets": len(discovery["leaderboard_wallets"]),
        "active_markets": len(discovery["markets"]),
        "holder_wallets": len(discovery["holder_wallets"]),
        "unique_candidates": len(discovery["candidates"]),
        "observations_logged": obs["logged"],
        "obs_eval_1h": obs["eval_1h"],
        "obs_eval_6h": obs["eval_6h"],
        "obs_eval_24h": obs["eval_24h"],
        "scan_runtime_seconds": round(time.time() - start, 2),
        "time_budget_hit": time.time() > deadline,
        "test_first": test_first,
        "watch": watch,
        "reject_counts": dict(reject_counts),
    }

    with LOCK:
        global LAST_SCAN_META, LAST_CANDIDATES, LAST_GROUP_TOP_COUNT
        LAST_SCAN_META = result
        LAST_CANDIDATES = passing[:]
        SCAN_HISTORY.append({"ts": iso_now(), "wallets": passing[:]})
        # prune history to 24h for light memory
        if len(SCAN_HISTORY) > 200:
            del SCAN_HISTORY[:-200]
        LAST_GROUP_TOP_COUNT = len(test_first) + len(watch)

    return result

# =========================
# Formatting
# =========================
def format_wallet_line(w: Dict[str, Any]) -> List[str]:
    lines = [
        f"Wallet: {w['wallet']}",
        f"Username: {w.get('username', 'none')}",
        f"Bucket: {w['bucket']} | Score: {w['score']}",
        f"30d: pnl={w['pnl_30d']} | weighted_ret={pct(w['weighted_return_30d'])} | avg_ret={pct(w['avg_return_30d'])}",
        f"30d sample: closed={w['closed_positions_30d']} | trades={w['trades_30d']} | wins={pct(w['win_rate_30d'])} | 20%+ closes={pct(w['consistency_ratio'])}",
        f"Recent: trades_7d={w['recent_trades_7d']} | intraday_signals={w['intraday_signals']} | current_positions={w['current_positions_count']}",
        f"Closed-trade trend: {w['pattern']['closed_trade_trend']}",
        f"Pattern: {w['pattern']['summary']}",
        f"Cluster: {w['pattern']['cluster']}",
        f"Similar: {', '.join(w.get('similar_wallets', [])) if w.get('similar_wallets') else 'none'}",
        f"Profile: {w['profile']}",
        f"Discovery: {w.get('source', 'unknown')}",
    ]
    return lines

def format_scan(result: Dict[str, Any]) -> str:
    lines = [
        "Manual wallet scan",
        f"script_version={result['script_version']}",
        f"evaluated_wallets={result['evaluated_wallets']} | passing_wallets={result['passing_wallets']} | evaluation_errors={result['evaluation_errors']}",
        f"leaderboard_wallets={result['leaderboard_wallets']} | active_markets={result['active_markets']} | holder_wallets={result['holder_wallets']} | unique_candidates={result['unique_candidates']}",
        f"observations_logged={result['observations_logged']} | obs_eval_1h={result['obs_eval_1h']} | obs_eval_6h={result['obs_eval_6h']} | obs_eval_24h={result['obs_eval_24h']}",
        f"scan_runtime_seconds={result['scan_runtime_seconds']:.2f} | time_budget_hit={str(result['time_budget_hit']).lower()}",
        "",
        "Wallets to test first",
    ]
    if result["test_first"]:
        for w in result["test_first"][:8]:
            lines.extend(format_wallet_line(w))
            lines.append("")
    else:
        lines.append("None")

    lines.append("Wallets to watch closely")
    if result["watch"]:
        for w in result["watch"][:8]:
            lines.extend(format_wallet_line(w))
            lines.append("")
    else:
        lines.append("None")

    if result["reject_counts"]:
        lines.append("Top reject reasons")
        reason_parts = [f"{k}:{v}" for k, v in Counter(result["reject_counts"]).most_common(8)]
        lines.append(" | ".join(reason_parts))

    return "\n".join(lines).strip()

def format_cached_candidates() -> str:
    with LOCK:
        ts = LAST_SCAN_META.get("generated_at")
        wallets = LAST_CANDIDATES[:8]
    lines = [
        "Latest cached candidates while fresh scan runs",
        f"script_version={SCRIPT_VERSION}",
        f"cached_timestamp={ts or 'none'}",
    ]
    if wallets:
        for w in wallets:
            lines.append(f"{w['wallet']} | username={w.get('username','none')} | bucket={w['bucket']} | score={w['score']} | cluster={w['pattern']['cluster']}")
    else:
        lines.append("None")
    return "\n".join(lines)

def format_group() -> str:
    cutoff = time.time() - GROUP_WINDOW_SECONDS
    wallet_seen: Dict[str, Dict[str, Any]] = {}
    counts = Counter()

    with LOCK:
        history = SCAN_HISTORY[:]
    for entry in history:
        ts = parse_ts(entry.get("ts"))
        if ts is None or ts.timestamp() < cutoff:
            continue
        for w in entry.get("wallets", []):
            counts[w["wallet"]] += 1
            wallet_seen[w["wallet"]] = w

    top = []
    for wallet, n in counts.most_common(8):
        w = wallet_seen[wallet]
        top.append({
            "wallet": wallet,
            "username": w.get("username", "none"),
            "appearances": n,
            "bucket": w["bucket"],
            "score": w["score"],
            "weighted_ret": w["weighted_return_30d"],
            "wins": w["win_rate_30d"],
            "consistency": w["consistency_ratio"],
            "recent7d": w["recent_trades_7d"],
            "cluster": w["pattern"]["cluster"],
        })

    lines = [
        f"{GROUP_WINDOW_SECONDS // 3600} hour wallet summary",
        f"script_version={SCRIPT_VERSION}",
        f"scans_in_window={sum(1 for entry in history if (parse_ts(entry.get('ts')) or utc_now()).timestamp() >= cutoff)} | top_candidates_seen={len(top)}",
        "",
        "Highest recurring candidates",
    ]
    if top:
        for row in top:
            lines.append(
                f"{row['wallet']} | username={row['username']} | appearances={row['appearances']} | bucket={row['bucket']} | score={row['score']} | 30d_ret={pct(row['weighted_ret'])} | wins={pct(row['wins'])} | 20%+={pct(row['consistency'])} | recent7d={row['recent7d']} | cluster={row['cluster']}"
            )
    else:
        lines.append("None")

    lines.append("")
    lines.append("Observed 24h leaders")
    if OBSERVATION_LOG:
        obs_counts = Counter([r["wallet"] for r in OBSERVATION_LOG])
        for wallet, n in obs_counts.most_common(8):
            row = wallet_seen.get(wallet)
            if row:
                lines.append(f"{wallet} | username={row.get('username','none')} | observations={n} | cluster={row['pattern']['cluster']}")
            else:
                lines.append(f"{wallet} | observations={n}")
    else:
        lines.append("None")

    return "\n".join(lines)

def format_health() -> str:
    with LOCK:
        scans = len(SCAN_HISTORY)
        wallets_eval = sum(len(x.get("wallets", [])) for x in SCAN_HISTORY)
    lines = [
        "Wallet intel health",
        f"script_version={SCRIPT_VERSION}",
        f"scan_every_seconds={SCAN_EVERY_SECONDS}",
        f"group_window_seconds={GROUP_WINDOW_SECONDS}",
        f"scans={scans} | wallets_evaluated={LAST_SCAN_META.get('evaluated_wallets',0)} | wallets_passing={LAST_SCAN_META.get('passing_wallets',0)}",
        f"observations_logged={len(OBSERVATION_LOG)} | observations_evaluated=0",
        f"last_group_top_count={LAST_GROUP_TOP_COUNT} | observed_wallets={len(set(r['wallet'] for r in OBSERVATION_LOG))}",
    ]
    return "\n".join(lines)

# =========================
# Background
# =========================
def background_loop() -> None:
    global BACKGROUND_STARTED
    if BACKGROUND_STARTED:
        return
    BACKGROUND_STARTED = True
    while True:
        try:
            run_wallet_scan(manual=False)
        except Exception as e:
            send_telegram(f"Wallet intel background scan error\nscript_version={SCRIPT_VERSION}\nerror={e}")
        time.sleep(SCAN_EVERY_SECONDS)

def ensure_background_started() -> None:
    t = threading.Thread(target=background_loop, daemon=True)
    t.start()

# =========================
# Web routes
# =========================
@app.route("/")
def home() -> Response:
    return Response("OK", mimetype="text/plain")

@app.route("/health")
def health_route() -> Response:
    return Response(format_health(), mimetype="text/plain")

@app.route("/group")
def group_route() -> Response:
    return Response(format_group(), mimetype="text/plain")

@app.route("/scan")
def scan_route() -> Response:
    result = run_wallet_scan(manual=True)
    return Response(format_scan(result), mimetype="text/plain")

def manual_scan_worker() -> None:
    global MANUAL_SCAN_IN_PROGRESS
    try:
        result = run_wallet_scan(manual=True)
        send_telegram(format_scan(result))
    except Exception as e:
        send_telegram(f"Wallet intel manual scan error\nscript_version={SCRIPT_VERSION}\nerror={e}")
    finally:
        MANUAL_SCAN_IN_PROGRESS = False

@app.route("/webhook", methods=["POST"])
def webhook() -> Response:
    global MANUAL_SCAN_IN_PROGRESS
    data = request.get_json(silent=True) or {}
    msg = data.get("message") or {}
    text = (msg.get("text") or "").strip()

    if text == "/health":
        send_telegram(format_health())
    elif text == "/group":
        send_telegram(format_group())
    elif text == "/scan":
        send_telegram("Running wallet scan...")
        if MANUAL_SEND_CACHED_FIRST:
            send_telegram(format_cached_candidates())
        if not MANUAL_SCAN_IN_PROGRESS:
            MANUAL_SCAN_IN_PROGRESS = True
            threading.Thread(target=manual_scan_worker, daemon=True).start()
        else:
            send_telegram("Manual scan already running.")
    return Response("ok", mimetype="text/plain")

if __name__ == "__main__":
    ensure_background_started()
    port = int(os.getenv("PORT", "10000"))
    app.run(host="0.0.0.0", port=port)
