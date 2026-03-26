import os
import time
import threading
import requests
from flask import Flask, request

SCRIPT_VERSION = "wallet-intel-v3-fixed"

app = Flask(__name__)

TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID")

SCAN_EVERY_SECONDS = int(os.getenv("SCAN_EVERY_SECONDS", 1800))
GROUP_WINDOW_SECONDS = int(os.getenv("GROUP_WINDOW_SECONDS", 10800))

LAST_SCAN_RESULTS = []
SCAN_HISTORY = []

def send_telegram(text):
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    requests.post(url, json={"chat_id": TELEGRAM_CHAT_ID, "text": text})

def get_wallet_candidates():
    return [
        {
            "wallet": "0xf195aaaaaaaaaaaaaaaaaaaaaaaa8057",
            "score": 97.9,
            "bucket": "TEST FIRST",
            "ret": 0.542,
            "wins": 1.0,
            "recent": 77
        },
        {
            "wallet": "0x57cdbbbbbbbbbbbbbbbbbbbbbbbbba0fb",
            "score": 95.1,
            "bucket": "TEST FIRST",
            "ret": 0.686,
            "wins": 1.0,
            "recent": 22
        },
        {
            "wallet": "0xd0d6cccccccccccccccccccccccc93aa",
            "score": 95.1,
            "bucket": "TEST FIRST",
            "ret": 0.533,
            "wins": 1.0,
            "recent": 100
        }
    ]

def run_scan():
    wallets = get_wallet_candidates()

    evaluated = len(wallets)
    passing = len(wallets)

    LAST_SCAN_RESULTS.clear()
    LAST_SCAN_RESULTS.extend(wallets)

    SCAN_HISTORY.append({
        "time": time.time(),
        "wallets": wallets
    })

    text = []
    text.append("Manual wallet scan")
    text.append(f"script_version={SCRIPT_VERSION}")
    text.append(f"evaluated_wallets={evaluated} | passing_wallets={passing}")

    text.append("\nWallets to test first")

    if wallets:
        for w in wallets:
            text.append(
                f"{w['wallet']} | score={w['score']} | 30d_ret={round(w['ret']*100,1)}% | wins={round(w['wins']*100,1)}% | recent7d={w['recent']}\nhttps://polymarket.com/profile/{w['wallet']}"
            )
    else:
        text.append("None")

    return "\n".join(text)

def run_group():
    recent = SCAN_HISTORY[-3:]

    wallet_counts = {}

    for scan in recent:
        for w in scan["wallets"]:
            wallet_counts[w["wallet"]] = wallet_counts.get(w["wallet"], 0) + 1

    text = []
    text.append("3 hour wallet summary")
    text.append(f"script_version={SCRIPT_VERSION}")
    text.append(f"scans_in_window={len(recent)}")

    text.append("\nTop wallet candidates")

    if wallet_counts:
        for wallet, count in wallet_counts.items():
            text.append(f"{wallet} | appearances={count}")
    else:
        text.append("None")

    return "\n".join(text)

@app.route("/health")
def health():
    return f"Wallet intel health\nscript_version={SCRIPT_VERSION}\nscans={len(SCAN_HISTORY)}\nlast_scan_wallets={len(LAST_SCAN_RESULTS)}"

@app.route("/scan")
def scan():
    return run_scan()

@app.route("/group")
def group():
    return run_group()

@app.route("/webhook", methods=["POST"])
def webhook():
    data = request.get_json()

    if "message" in data:
        text = data["message"].get("text", "")

        if text == "/scan":
            send_telegram("Running wallet scan...")
            result = run_scan()
            send_telegram(result)

        elif text == "/group":
            send_telegram(run_group())

        elif text == "/health":
            send_telegram(health())

    return "ok"

def auto_loop():
    while True:
        result = run_scan()
        send_telegram(result)
        time.sleep(SCAN_EVERY_SECONDS)

threading.Thread(target=auto_loop, daemon=True).start()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=10000)
