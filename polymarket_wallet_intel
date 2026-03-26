import os
import time
import json
import math
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
SCRIPT_VERSION = "wallet-intel-v1"
UTC = timezone.utc

# =========================================================
# Environment
# =========================================================
DATA_API_BASE = os.getenv("DATA_API_BASE", "https://data-api.polymarket.com")
DATA_API_V1_BASE = os.getenv("DATA_API_V1_BASE", f"{DATA_API_BASE}/v1")
GAMMA_BASE = os.getenv("GAMMA_BASE", "https://gamma-api.polymarket.com")
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")
REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "15"))

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

# Output
TOP_WALLETS_PER_SCAN = int(os.getenv("TOP_WALLETS_PER_SCAN", "8"))
TOP_WALLETS_PER_GROUP = int(os.getenv("TOP_WALLETS_PER_GROUP", "10"))
WATCH_BUCKET_MIN_SCORE = float(os.getenv("WATCH_BUCKET_MIN_SCORE", "60"))
TEST_FIRST_MIN_SCORE = float(os.getenv("TEST_FIRST_MIN_SCORE", "75"))

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
            for key in ["data", "results", "markets", "events"]:
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
# Public Polymarket fetchers
# =========================================================
def fetch_leaderboard_wallets(limit: int) -> List[Dict[str, Any]]:
    rows = fetch_list(f"{DATA_API_V1_BASE}/leaderboard", params={"limit": min(limit, 50), "timePeriod": "MONTH", "orderBy": "PNL", "category": "OVERALL"})
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
        })
    out.sort(key=lambda x: (x["liquidity"], x["volume"]), reverse=True)
    return out[:limit]


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
    return fetch_list(f"{DATA_API_BASE}/trades", params={"user": wallet})


def fetch_current_positions(wallet: str) -> List[Dict[str, Any]]:
    return fetch_list(f"{DATA_API_BASE}/positions", params={"user": wallet})


def fetch_user_activity(wallet: str) -> List[Dict[str, Any]]:
    return fetch_list(f"{DATA_API_BASE}/activity", params={"user": wallet})


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

    # Best effort denominator. Use totalBought first because docs expose it.
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

    ret_score = clamp(weighted_return / 0.40, 0.0, 1.0) * 35.0
    win_score = clamp((win_rate - 0.50) / 0.30, 0.0, 1.0) * 20.0
    consistency_score = clamp((consistency - 0.40) / 0.40, 0.0, 1.0) * 20.0
    activity_score = clamp(recent_trades / 8.0, 0.0, 1.0) * 10.0
    intraday_score = clamp(intraday / 5.0, 0.0, 1.0) * 10.0
    sample_score = clamp(sample / 12.0, 0.0, 1.0) * 5.0
    return round(ret_score + win_score + consistency_score + activity_score + intraday_score + sample_score, 2)


def classify_bucket(wallet_metrics: Dict[str, Any]) -> str:
    score = wallet_metrics.get("score", 0.0)
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

    return good[:4], weak[:3]


def evaluate_wallet(candidate: Dict[str, Any]) -> Dict[str, Any]:
    wallet = candidate["wallet"]
    cutoff_30d = days_ago(LOOKBACK_DAYS)
    cutoff_7d = days_ago(RECENT_DAYS)

    closed_positions = fetch_closed_positions(wallet)
    trades = fetch_trades(wallet)
    current_positions = fetch_current_positions(wallet)

    closed_30d: List[Dict[str, Any]] = []
    trade_30d: List[Dict[str, Any]] = []
    recent_trades_7d = 0

    for row in closed_positions:
        ts = parse_ts(row.get("timestamp") or row.get("time") or row.get("updatedAt") or row.get("closedAt"))
        if ts is None or ts < cutoff_30d:
            continue
        closed_30d.append(row)

    for row in trades:
        ts = parse_ts(row.get("timestamp") or row.get("time") or row.get("createdAt"))
        if ts is None:
            continue
        if ts >= cutoff_30d:
            trade_30d.append(row)
        if ts >= cutoff_7d:
            recent_trades_7d += 1

    weighted_pnl = 0.0
    weighted_cost = 0.0
    positive_positions = 0
    consistency_hits = 0
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
        if r >= 0.20:
            consistency_hits += 1

    weighted_return = (weighted_pnl / weighted_cost) if weighted_cost > 0 else 0.0
    win_rate = (positive_positions / len(closed_30d)) if closed_30d else 0.0
    consistency_ratio = (consistency_hits / len(closed_30d)) if closed_30d else 0.0
    avg_return = (sum(returns) / len(returns)) if returns else 0.0
    median_return = sorted(returns)[len(returns)//2] if returns else 0.0

    # Intraday proxy from public trades only.
    by_slug_day: Dict[Tuple[str, str], Dict[str, int]] = defaultdict(lambda: {"BUY": 0, "SELL": 0})
    for row in trade_30d:
        ts = parse_ts(row.get("timestamp") or row.get("time") or row.get("createdAt"))
        if ts is None:
            continue
        slug = clean_text(row.get("slug") or row.get("marketSlug") or row.get("title") or row.get("conditionId"))
        key = (slug, ts.strftime("%Y-%m-%d"))
        side = clean_text(row.get("side") or row.get("type") or "").upper()
        if side not in ("BUY", "SELL"):
            continue
        by_slug_day[key][side] += 1
    intraday_roundtrips = sum(1 for v in by_slug_day.values() if v["BUY"] > 0 and v["SELL"] > 0)

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
    }
    metrics["score"] = bucket_score(metrics)
    metrics["bucket"] = classify_bucket(metrics)
    metrics["good_reasons"], metrics["weak_reasons"] = reason_strings(metrics)

    passes = (
        metrics["closed_positions_30d"] >= MIN_CLOSED_POSITIONS_30D and
        metrics["trades_30d"] >= MIN_TRADES_30D and
        metrics["weighted_return_30d"] >= MIN_WEIGHTED_RETURN_30D and
        metrics["win_rate_30d"] >= MIN_WIN_RATE_30D and
        metrics["consistency_ratio_30d"] >= MIN_CONSISTENCY_RATIO and
        metrics["realized_pnl_30d"] >= MIN_REALIZED_PNL_30D and
        metrics["recent_trades_7d"] >= MIN_RECENT_TRADES_7D
    )
    metrics["passes_filters"] = passes
    return metrics


# =========================================================
# Scan engine
# =========================================================
def scan_once() -> Dict[str, Any]:
    discovery_rows, discovery_stats = discover_candidate_wallets()
    evaluated: List[Dict[str, Any]] = []
    errors = 0

    for candidate in discovery_rows:
        try:
            evaluated.append(evaluate_wallet(candidate))
        except Exception:
            errors += 1

    evaluated.sort(key=lambda x: (x.get("passes_filters", False), x.get("score", 0.0), x.get("weighted_return_30d", 0.0), x.get("recent_trades_7d", 0)), reverse=True)

    test_first = [x for x in evaluated if x.get("bucket") == "TEST FIRST" and x.get("passes_filters")][:TOP_WALLETS_PER_SCAN]
    watch_closely = [x for x in evaluated if x.get("bucket") == "WATCH CLOSELY" and x.get("passes_filters")][:TOP_WALLETS_PER_SCAN]
    rejects = [x for x in evaluated if not x.get("passes_filters")][:TOP_WALLETS_PER_SCAN]

    stats = {
        **discovery_stats,
        "evaluated_wallets": len(evaluated),
        "passing_wallets": len([x for x in evaluated if x.get("passes_filters")]),
        "test_first_count": len(test_first),
        "watch_count": len(watch_closely),
        "reject_count": len(rejects),
        "evaluation_errors": errors,
    }

    scan = {
        "timestamp": now_utc().isoformat(),
        "stats": stats,
        "test_first": test_first,
        "watch_closely": watch_closely,
        "rejects": rejects,
        "top_wallets": (test_first + watch_closely + rejects)[:TOP_WALLETS_PER_SCAN],
    }

    runtime_state["session_summary"]["scans"] = runtime_state["session_summary"].get("scans", 0) + 1
    runtime_state["session_summary"]["wallets_evaluated"] = runtime_state["session_summary"].get("wallets_evaluated", 0) + len(evaluated)
    runtime_state["session_summary"]["wallets_passing"] = runtime_state["session_summary"].get("wallets_passing", 0) + stats["passing_wallets"]
    runtime_state["session_summary"]["last_scan_top_count"] = len(scan["top_wallets"])
    runtime_state["last_health"] = stats
    return scan


def append_scan_to_group(scan: Dict[str, Any]) -> None:
    history = runtime_state.setdefault("scan_history", [])
    now_s = utc_ts()
    history.append({
        "ts": now_s,
        "timestamp": scan.get("timestamp"),
        "top_wallets": scan.get("top_wallets", []),
        "stats": scan.get("stats", {}),
    })
    cutoff = now_s - max(GROUP_WINDOW_SECONDS * 2, 21600)
    runtime_state["scan_history"] = [x for x in history if x.get("ts", 0) >= cutoff]


def build_grouped_summary() -> Dict[str, Any]:
    now_s = utc_ts()
    cutoff = now_s - GROUP_WINDOW_SECONDS
    scans = [x for x in runtime_state.get("scan_history", []) if x.get("ts", 0) >= cutoff]

    wallet_map: Dict[str, Dict[str, Any]] = {}
    for scan in scans:
        for row in scan.get("top_wallets", []):
            wallet = row.get("wallet")
            if not wallet:
                continue
            current = wallet_map.get(wallet)
            if current is None:
                wallet_map[wallet] = dict(row)
                wallet_map[wallet]["appearances"] = 1
            else:
                current["appearances"] += 1
                if row.get("score", 0.0) > current.get("score", 0.0):
                    for k, v in row.items():
                        current[k] = v

    rows = list(wallet_map.values())
    rows.sort(key=lambda x: (x.get("appearances", 0), x.get("passes_filters", False), x.get("score", 0.0), x.get("weighted_return_30d", 0.0)), reverse=True)
    top_group = rows[:TOP_WALLETS_PER_GROUP]
    runtime_state["session_summary"]["last_group_top_count"] = len(top_group)

    return {
        "window_minutes": int(GROUP_WINDOW_SECONDS / 60),
        "scan_count": len(scans),
        "wallet_count": len(rows),
        "top_wallets": top_group,
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
    return "\n".join([
        f"Wallet: {label}",
        f"Bucket: {row.get('bucket')} | Score: {row.get('score', 0.0):.1f}",
        f"30d: pnl={row.get('realized_pnl_30d', 0.0):.2f} | weighted_ret={row.get('weighted_return_30d', 0.0):.1%} | avg_ret={row.get('avg_return_30d', 0.0):.1%}",
        f"30d sample: closed={row.get('closed_positions_30d', 0)} | trades={row.get('trades_30d', 0)} | wins={row.get('win_rate_30d', 0.0):.1%} | 20%+ closes={row.get('consistency_ratio_30d', 0.0):.1%}",
        f"Recent: trades_7d={row.get('recent_trades_7d', 0)} | intraday_signals={row.get('intraday_roundtrips_30d', 0)} | current_positions={row.get('current_positions', 0)}",
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
        return "\n".join(lines)

    for row in rows:
        lines.append(
            f"{short_wallet(row['wallet'])} | appearances={row.get('appearances', 0)} | bucket={row.get('bucket')} | score={row.get('score', 0.0):.1f} | 30d_ret={row.get('weighted_return_30d', 0.0):.1%} | wins={row.get('win_rate_30d', 0.0):.1%} | 20%+={row.get('consistency_ratio_30d', 0.0):.1%} | recent7d={row.get('recent_trades_7d', 0)}"
        )
    return "\n".join(lines)


def format_health_text() -> str:
    last = runtime_state.get("last_health", {})
    sess = runtime_state.get("session_summary", {})
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
        f"manual_scan_in_progress={manual_scan_in_progress}",
        f"session_scans={sess.get('scans', 0)} | wallets_evaluated_total={sess.get('wallets_evaluated', 0)} | wallets_passing_total={sess.get('wallets_passing', 0)}",
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
    return "Commands: /health, /scan, /group"


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
                if grouped.get("top_wallets"):
                    send_telegram(format_grouped_summary(grouped))
                    runtime_state["last_group_sent_at"] = now_s
                    save_state()
                elif SEND_ZERO_GROUP_SUMMARY:
                    send_telegram(format_grouped_summary(grouped))
                    runtime_state["last_group_sent_at"] = now_s
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
# Entrypoint
# =========================================================
load_state()
ensure_background_started()

if __name__ == "__main__":
    port = int(os.getenv("PORT", "10000"))
    app.run(host="0.0.0.0", port=port)
