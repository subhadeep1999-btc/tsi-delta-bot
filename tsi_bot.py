"""
TSI bot for Delta Exchange India BTCUSD perpetual (demo by default).

Rules
  - TSI(25,13,13) is calculated on 45-minute candles and READ ON THE 1H CHART exactly as TradingView draws it
    (SIGNAL_MAP=B, default): each 1h candle shows the TSI of the 45m candle that OPENED last before the 1h candle closed.
    That 45m candle closes between 0 and 45 minutes AFTER the 1h close, so the signal is confirmed and traded then
    (SIGNAL_MAP=A = the last 45m candle already closed at the 1h close; matches the chart only about half the time).
    A crossover = TSI crossing its signal line between two consecutive 1h candles.
  - FAST ENTRY (SIGNAL_MAP=L, optional, NOT the default): at the 1h close the 45m candle that is still forming is used as it stands at that moment
    (this is the TSI value the chart shows when the 1h candle closes), so the trade is placed within seconds of the new candle opening.
    That value can still change before the 45m candle finishes (a few signals may not hold). Send "fast" to the bot to use it, "confirmed" to go back.
  - TIMING: a run started up to WAIT_MAX_SEC (240) before the moment a signal becomes known (the 45m candle close for the 45m plan,
    the 1h close for the 1h plan) stays awake and trades within seconds of that close.
  - Every valid crossover: close the running trade and open a new one (bullish = LONG, bearish = SHORT).
    From flat (also after a stop-out or a manual close) the next valid crossover opens a trade, either direction.
  - BIG-CANDLE SKIP: the crossover is skipped (nothing closed, nothing opened) if the crossover 1h candle, the one
    before it (LOOKBACK_CANDLES), or any 45m candle added since the last 1h reading is >= MAX_CANDLE_PTS, where a candle's size is |close - previous
    candle close| (CANDLE_MEASURE=change, the default, the figure TradingView shows) or high-low (CANDLE_MEASURE=range).
  - STOPS (every trade): 1) exchange stop-loss MAX_LOSS_PTS from entry, 2) bot check on every run (closes the trade
    at market if the stop level was touched but the exchange stop did not fire), 3) wider exchange hard stop
    HARD_STOP_PTS (0 = off).
  - Telegram message for every open, reversal, stop-out, skipped crossover, problem, and a daily status.

Runs ONCE per call (made for GitHub Actions started every 30 minutes) or forever with --loop.
Commands: --check  --test-order (demo)  --status  --resume  --once (default)  --loop
Secrets come from environment variables: DELTA_API_KEY DELTA_API_SECRET TG_TOKEN TG_CHAT_ID DELTA_PROXY
Settings can also be set with environment variables of the same name as the settings below (MODE, CAPITAL_INR ...).
"""
import os
import re
import sys
import csv
import json
import math
import time
import hmac
import hashlib
from bisect import bisect_right
from datetime import datetime, timezone, timedelta
from urllib.parse import urlencode

import requests


def env(name, default):
    v = os.getenv(name)
    if v is None or v == "":
        return default
    return type(default)(v) if not isinstance(default, str) else v


# ======================= SETTINGS =======================
MODE = env("MODE", "demo").strip().strip("\"'").strip().lower()                    # "demo" = testnet, virtual money | "live" = REAL MONEY
LIVE_CONFIRM = env("LIVE_CONFIRM", "").strip().strip("\"'").strip()        # for live, exactly:  YES I ACCEPT REAL LOSSES
API_KEY = env("DELTA_API_KEY", "PASTE_API_KEY")
API_SECRET = env("DELTA_API_SECRET", "PASTE_API_SECRET")
TG_TOKEN = env("TG_TOKEN", "PASTE_BOT_TOKEN")
TG_CHAT_ID = env("TG_CHAT_ID", "640760987")
PROXY_URL = env("DELTA_PROXY", "")            # TrueIP proxy: http://USER:PASS@HOST:PORT (only Delta account calls use it)

SYMBOL = "BTCUSD"
TSI_LONG, TSI_SHORT, TSI_SIGNAL = 25, 13, 13
CALC_MIN, CHART_MIN = 45, 60
MAX_CANDLE_PTS = env("MAX_CANDLE_PTS", 800)
EMA_ALERT = str(env("EMA_ALERT", "1")).strip().lower() not in ("0", "false", "no", "off")   # 1 = tell me when a 1h candle closes against the 2h 5 EMA while a trade is open (message only)
EMA_LEN = 5
EMA3_ALERT = str(env("EMA3_ALERT", "1")).strip().lower() not in ("0", "false", "no", "off")   # 1 = a small message when a 1h candle closes above/below the 3h 5 EMA (always, with or without a trade)
EMA3_EVERY = str(env("EMA3_EVERY", "0")).strip().lower() in ("1", "true", "yes", "on")        # 0 = only when the close moves to the OTHER side of the EMA | 1 = after every 1h close
TSI_TIMEFRAME = str(env("TSI_TIMEFRAME", "45"))     # 45 = TSI on 45m candles read on the 1h chart (normal plan) | 60 = TSI on 1h candles (the slower plan for choppy markets).
                                                     # You can also switch from Telegram: send  1h  or  45  to the bot (the latest change, variable or message, wins).
SIGNAL_MAP = env("SIGNAL_MAP", "B").strip().strip("\"'").upper()   # "B" = confirmed (default): | "L" = FAST: at the 1h close use the 45m candle still forming, as the chart shows it at that moment | (B:) the 45m candle that OPENS inside the 1h candle, known up to 45 min after the 1h close | "A" = last 45m candle already closed at the 1h close
PLAN_TAG = env("PLAN", "").strip()                # set by a cron job: "45" = only run while the 45m plan is on, "60" = only while the 1h plan is on ("" = always)
WAIT_MAX_SEC = env("WAIT_MAX_SEC", 240)           # a run that starts at most this many seconds before the next signal moment waits for it, then trades at once
LIVE = SIGNAL_MAP == "L"                          # changed for the run by apply_mode (Telegram: fast / confirmed)
CANDLE_MEASURE = env("CANDLE_MEASURE", "change").strip().strip("\"'").lower()   # "change" = |close - previous close| (what TradingView shows) | "range" = high - low
LOOKBACK_CANDLES = env("LOOKBACK_CANDLES", 2)
MAX_LOSS_PTS = env("MAX_LOSS_PTS", 800)
HARD_STOP_PTS = env("HARD_STOP_PTS", 1200)    # second exchange stop, 0 = off

CAPITAL_INR = env("CAPITAL_INR", 1000)        # 500 or 1000
WALLET_ASSET = env("WALLET_ASSET", "USD")
INR_PER_USD = env("INR_PER_USD", 0.0)         # rupees per dollar (needed if the wallet is USD)
LEVERAGE = env("LEVERAGE", 25)
MARGIN_BUFFER = 0.10
FULL_BUDGET = str(env("FULL_BUDGET", "0")).strip().lower() in ("1", "true", "yes", "on")   # 1 = use the whole CAPITAL_INR as margin
MAX_LEVERAGE = int(float(env("MAX_LEVERAGE", 50)))                                       # the most leverage FULL_BUDGET may use
MAX_SIGNAL_AGE_MIN = env("MAX_SIGNAL_AGE_MIN", 25)
HEARTBEAT_HOUR_IST = 9
PAUSE = env("BOT_PAUSE", "") == "1"           # 1 = watch and report only, place no new trades
# ========================================================

DEMO_BASE = "https://cdn-ind.testnet.deltaex.org"
LIVE_BASE = "https://api.india.delta.exchange"
DATA_BASE = "https://api.india.delta.exchange"
LIVE_PHRASE = "YES I ACCEPT REAL LOSSES"
STATE_FILE = env("STATE_FILE", "bot_state.json")
TRADE_LOG = env("TRADE_LOG", "trades_log.csv")
IST = timezone(timedelta(hours=5, minutes=30))
UA = "python-rest-client"
B15 = 900


class ApiError(Exception):
    pass


class Halt(Exception):
    """Something unexpected: stop trading until --resume."""


def ist(ts, fmt="%d %b %H:%M"):
    return datetime.fromtimestamp(ts, tz=IST).strftime(fmt)


# ============================ allocation ============================
def allocation():
    """The rupee allocation expressed in wallet units (INR wallet: as is, USD wallet: converted)."""
    if INR_PER_USD <= 0:
        raise SystemExit("Set INR_PER_USD (rupees per dollar). It is needed to size the position. Nothing traded.")
    if WALLET_ASSET.upper() == "INR":
        return float(CAPITAL_INR)
    return round(CAPITAL_INR / INR_PER_USD, 4)


def fx():
    """Wallet units per 1 USD of contract value (Delta India BTCUSD is quoted in USD but margined and settled in INR)."""
    return INR_PER_USD if WALLET_ASSET.upper() == "INR" else 1.0


# ============================ Delta API ============================
def sign(secret, method, ts, path, query, body):
    return hmac.new(secret.encode(), (method + ts + path + query + body).encode(), hashlib.sha256).hexdigest()


class Delta:
    def __init__(self, base, key, secret, proxy=""):
        self.base, self.key, self.secret = base.rstrip("/"), key, secret
        self.proxies = {"http": proxy, "https": proxy} if proxy else None

    def request(self, method, path, params=None, payload=None, auth=True):
        query = ("?" + urlencode(params)) if params else ""
        body = json.dumps(payload) if payload is not None else ""
        last = None
        for signed_query in ([query] + ([query[1:]] if query else [])):
            headers = {"User-Agent": UA, "Accept": "application/json", "Content-Type": "application/json"}
            if auth:
                ts = str(int(time.time()))
                headers.update({"api-key": self.key, "timestamp": ts,
                                "signature": sign(self.secret, method, ts, path, signed_query, body)})
            r = requests.request(method, self.base + path + query, headers=headers, data=body or None,
                                 timeout=20, proxies=self.proxies if auth else None)
            try:
                j = r.json()
            except Exception:
                j = {"raw": r.text[:300]}
            if not (r.status_code >= 400 or (isinstance(j, dict) and j.get("success") is False)):
                return j
            last = ApiError("HTTP %s: %s" % (r.status_code, json.dumps(j)[:400]))
            if not (auth and "signature" in json.dumps(j).lower()):
                break
        raise last

    def product(self):
        res = self.request("GET", "/v2/products/%s" % SYMBOL, auth=False)["result"]
        ctype = str(res.get("contract_type") or "")
        if ctype and ctype != "perpetual_futures":
            raise SystemExit("Product %s is %s, not a perpetual future. Refusing to trade." % (SYMBOL, ctype))
        self.product_info = "contract_type=%s, settling asset=%s, state=%s" % (
            ctype or "?", (res.get("settling_asset") or {}).get("symbol", "?"), res.get("state", "?"))
        return int(res["id"]), float(res.get("contract_value") or 0.001), float(res.get("tick_size") or 0.5)

    def all_wallets(self):
        res = self.request("GET", "/v2/wallet/balances").get("result", [])
        return ["%s free %s / total %s" % (b.get("asset_symbol"), b.get("available_balance"), b.get("balance"))
                for b in (res if isinstance(res, list) else [])]

    def position(self, pid):
        res = self.request("GET", "/v2/positions", params={"product_id": pid}).get("result")
        if isinstance(res, list):
            res = res[0] if res else {}
        res = res or {}
        return float(res.get("size") or 0), res

    def available(self, asset):
        res = self.request("GET", "/v2/wallet/balances").get("result", [])
        for b in res if isinstance(res, list) else []:
            if str(b.get("asset_symbol", "")).upper() == asset.upper():
                return float(b.get("available_balance") or 0), float(b.get("balance") or 0)
        raise ApiError("No %s wallet found. Wallets on this account: %s. Set the WALLET_ASSET variable to one of them." % (
            asset, ", ".join(str(b.get("asset_symbol")) for b in (res if isinstance(res, list) else [])) or "none"))

    def get_leverage(self, pid):
        res = self.request("GET", "/v2/products/%s/orders/leverage" % pid).get("result", {})
        if isinstance(res, dict) and res.get("leverage") not in (None, ""):
            return float(res["leverage"])
        raise ApiError("Cannot read leverage: %s" % json.dumps(res)[:200])

    def set_leverage(self, pid, lev):
        self.request("POST", "/v2/products/%s/orders/leverage" % pid, payload={"leverage": int(lev) if float(lev).is_integer() else float(lev)})

    def last_price(self):
        res = self.request("GET", "/v2/tickers/%s" % SYMBOL, auth=False).get("result", {})
        return float(res.get("mark_price") or res.get("close"))

    def order(self, side, size, reduce_only=False):
        payload = {"product_symbol": SYMBOL, "size": int(size), "side": side, "order_type": "market_order",
                   "client_order_id": "t%d" % int(time.time() * 1000)}
        if reduce_only:
            payload["reduce_only"] = True
        try:
            return self.request("POST", "/v2/orders", payload=payload)
        except ApiError as e:
            if reduce_only and "reduce_only" in str(e).lower():
                payload["reduce_only"] = "true"
                return self.request("POST", "/v2/orders", payload=payload)
            raise

    def stop_order(self, side, size, stop_price):
        """Exchange stop-loss: reduce-only stop-market order. (Field names to be confirmed on the demo account.)"""
        payload = {"product_symbol": SYMBOL, "size": int(size), "side": side, "order_type": "market_order",
                   "stop_order_type": "stop_loss_order", "stop_price": "%.1f" % stop_price,
                   "stop_trigger_method": "mark_price", "reduce_only": True,
                   "client_order_id": "s%d" % int(time.time() * 1000)}
        return self.request("POST", "/v2/orders", payload=payload)

    def cancel(self, order_id, pid):
        return self.request("DELETE", "/v2/orders", payload={"id": int(order_id), "product_id": int(pid)})

    def order_info(self, order_id):
        return self.request("GET", "/v2/orders/%s" % order_id).get("result", {})


# ============================ market data & signals ============================
def fetch_15m(n=1500):
    now = int(time.time())
    r = requests.get(DATA_BASE + "/v2/history/candles",
                     params={"symbol": SYMBOL, "resolution": "15m", "start": str(now - n * B15), "end": str(now)},
                     headers={"User-Agent": UA}, timeout=25)
    r.raise_for_status()
    j = r.json()
    rows = j.get("result", []) if isinstance(j, dict) else j
    rows = sorted(rows, key=lambda x: int(x["time"]))
    return [(int(x["time"]), float(x["open"]), float(x["high"]), float(x["low"]), float(x["close"]))
            for x in rows if int(x["time"]) + B15 <= now]


def aggregate(c15, minutes):
    bar = minutes * 60
    buckets = {}
    for t, o, h, l, c in c15:
        buckets.setdefault(t - t % bar, []).append((t, o, h, l, c))
    need = bar // B15
    out = []
    for b in sorted(buckets):
        g = sorted(buckets[b])
        if len(g) != need or g[0][0] != b:
            continue
        out.append({"t": b, "end": b + bar, "o": g[0][1], "h": max(x[2] for x in g),
                    "l": min(x[3] for x in g), "c": g[-1][4]})
    return out


def ema(values, n):
    k = 2.0 / (n + 1)
    out = [values[0]]
    for v in values[1:]:
        out.append(v * k + out[-1] * (1 - k))
    return out


def tsi_series(closes):
    mom = [0.0] + [closes[i] - closes[i - 1] for i in range(1, len(closes))]
    a = ema(ema(mom, TSI_LONG), TSI_SHORT)
    b = ema(ema([abs(x) for x in mom], TSI_LONG), TSI_SHORT)
    tsi = [100.0 * x / y if y else 0.0 for x, y in zip(a, b)]
    return tsi, ema(tsi, TSI_SIGNAL)


def cross(prev_diff, cur_diff):
    if prev_diff <= 0 < cur_diff:
        return 1
    if prev_diff >= 0 > cur_diff:
        return -1
    return 0


def size_of(bars, k):
    """Size of candle k: |close - previous candle close| (default) or high - low."""
    if CANDLE_MEASURE == "range" or k < 1:
        return bars[k]["h"] - bars[k]["l"]
    return abs(bars[k]["c"] - bars[k - 1]["c"])


def chart_signals(bars1h, bars45, tsi, sig):
    """Per 1h candle: crossover (+1/-1/0), biggest 45m move added since the last reading, (tsi, signal) shown,
    and the time (end of the 45m candle used) at which the reading became known."""
    ends = [b["end"] for b in bars45]
    index = {b["t"]: k for k, b in enumerate(bars45)}
    step = CALC_MIN * 60
    out, extra, shown, known, prev, prev_j = [], [], [], [], None, None
    for cb in bars1h:
        if SIGNAL_MAP == "A":
            j = bisect_right(ends, cb["end"]) - 1
        else:                                               # B: the 45m candle that opened last before the 1h close
            j = index.get(((cb["end"] - 1) // step) * step, -1)   # -1 = that 45m candle is not closed yet
        if j < 1:
            out.append(0)
            extra.append(0.0)
            shown.append(None)
            known.append(cb["end"])
            continue
        first = prev_j + 1 if prev_j is not None else j
        extra.append(max([size_of(bars45, k) for k in range(first, j + 1)] or [0.0]))
        cur = tsi[j] - sig[j]
        out.append(cross(prev, cur) if prev is not None else 0)
        shown.append((tsi[j], sig[j]))
        known.append(cb["end"] if bars45[j].get("partial") else max(cb["end"], bars45[j]["end"]))
        prev, prev_j = cur, j
    return out, extra, shown, known


def skip_flags(bars, extra, lookback, thr):
    flags = []
    for i in range(len(bars)):
        r = max(size_of(bars, k) for k in range(max(0, i - lookback + 1), i + 1))
        flags.append(bool(thr) and max(r, extra[i]) >= thr)
    return flags


def parse_tf(text):
    """45 or 60 from words like "1h", "1 hour", "60", "45m", "TSI 45m"; None if it does not say."""
    t = (text or "").lower()
    if re.search(r"(?<!\d)(1\s*h|1\s*hr|1\s*hour|60)(?!\d)", t):
        return 60
    if re.search(r"(?<!\d)45(?!\d)", t):
        return 45
    return None


TF = parse_tf(TSI_TIMEFRAME) or 45                  # the plan in use during this run


def live_partial(c15, bars45):
    """The 45m candle that is still forming, built from the 15m candles finished so far (what the chart shows at the 1h close). [] if none."""
    if not c15:
        return []
    step = CALC_MIN * 60
    b = c15[-1][0] - c15[-1][0] % step
    if bars45 and bars45[-1]["t"] >= b:
        return []                                        # that 45m candle is already complete
    parts = [x for x in c15 if x[0] >= b]
    if not parts or parts[0][0] != b:
        return []
    return [{"t": b, "end": b + step, "o": parts[0][1], "h": max(x[2] for x in parts), "l": min(x[3] for x in parts),
             "c": parts[-1][4], "partial": True}]


def load_market(tf=None):
    tf = tf or TF
    c15 = fetch_15m()
    bars45, bars1h = aggregate(c15, CALC_MIN), aggregate(c15, CHART_MIN)
    if LIVE and tf != 60:
        bars45 = bars45 + live_partial(c15, bars45)
    if len(bars1h) < 100 or (tf != 60 and len(bars45) < 150):
        raise RuntimeError("too few candles")
    if tf == 60:                                        # TSI on the 1h candles themselves: the signal is known when the 1h candle closes
        tsi, sig = tsi_series([b["c"] for b in bars1h])
        sg, shown, prev = [0], [(tsi[0], sig[0])], tsi[0] - sig[0]
        for k in range(1, len(bars1h)):
            cur = tsi[k] - sig[k]
            sg.append(cross(prev, cur))
            shown.append((tsi[k], sig[k]))
            prev = cur
        extra, known = [0.0] * len(bars1h), [b["end"] for b in bars1h]
    else:
        tsi, sig = tsi_series([b["c"] for b in bars45])
        sg, extra, shown, known = chart_signals(bars1h, bars45, tsi, sig)
    skip = skip_flags(bars1h, extra, LOOKBACK_CANDLES, MAX_CANDLE_PTS)
    return {"c15": c15, "bars": bars1h, "sg": sg, "skip": skip, "extra": extra, "shown": shown, "known": known}


# ============================ state, logs, Telegram ============================
def load_state():
    try:
        with open(STATE_FILE) as f:
            st = json.load(f)
    except Exception:
        st = {}
    st.setdefault("handled", [])
    st.setdefault("halted", False)
    st.setdefault("trade", None)
    st.setdefault("totals", {"closed": 0, "wins": 0, "pts": 0.0, "wallet": 0.0, "days": {}})
    st.setdefault("last_hb_date", "")
    st.setdefault("warned", [])
    return st


def save_state(st):
    st["handled"] = st["handled"][-80:]
    st["warned"] = st["warned"][-40:]
    with open(STATE_FILE, "w") as f:
        json.dump(st, f, indent=1)


def log_row(row):
    new = not os.path.exists(TRADE_LOG)
    with open(TRADE_LOG, "a", newline="") as f:
        w = csv.writer(f)
        if new:
            w.writerow(["time_ist", "mode", "event", "side", "entry", "exit", "contracts", "pts", "wallet_pnl", "note"])
        w.writerow(row)


def send_keyboard(text):
    """A message with two buttons under it. Tapping a button sends its text to the bot as a normal message."""
    print(text, flush=True)
    try:
        requests.post("https://api.telegram.org/bot%s/sendMessage" % TG_TOKEN, timeout=20, json={
            "chat_id": TG_CHAT_ID, "text": text,
            "reply_markup": {"keyboard": [[{"text": "TSI 1h"}, {"text": "TSI 45m"}]], "resize_keyboard": True, "is_persistent": True}})
    except Exception as e:
        print("Telegram send failed:", e, flush=True)


def read_telegram(st):
    """What you sent the bot since the last run (only from your own chat)."""
    texts = []
    try:
        r = requests.get("https://api.telegram.org/bot%s/getUpdates" % TG_TOKEN,
                         params={"offset": st.get("tg_offset", 0), "timeout": 0}, timeout=20).json()
    except Exception as e:
        print("Telegram read failed:", e, flush=True)
        return texts
    if not r.get("ok"):
        print("Telegram read problem:", str(r)[:150], flush=True)
        return texts
    for u in r.get("result", []):
        st["tg_offset"] = u["update_id"] + 1
        m = u.get("message") or {}
        if str((m.get("chat") or {}).get("id")) == str(TG_CHAT_ID) and m.get("text"):
            texts.append(m["text"])
    return texts


def tf_name(tf):
    return "1h candles (slower plan)" if tf == 60 else "45m candles (normal plan)"


def apply_mode(st):
    """Decides the TSI plan for this run: the GitHub variable TSI_TIMEFRAME or your Telegram message, whichever changed last."""
    global TF, LIVE
    live_want = None
    env_tf = parse_tf(TSI_TIMEFRAME) or 45
    cur = st.get("tf") or env_tf
    want, ask = None, False
    if "env_tf" in st and st["env_tf"] != env_tf:
        want = env_tf                                       # you changed the variable in GitHub
    st["env_tf"] = env_tf
    for text in read_telegram(st):
        low = text.strip().lower()
        tf = parse_tf(low) if ("tsi" in low or len(low) <= 12) else None
        if low in ("fast", "fast entry", "/fast"):
            live_want = True
        elif low in ("confirmed", "confirmed entry", "/confirmed"):
            live_want = False
        elif tf:
            want = tf
        elif low in ("mode", "/mode", "status", "/status", "plan", "tsi"):
            ask = True
    if want and want != cur:
        try:                                                # the crossover already standing in the new plan is not traded; wait for the next one
            m = load_market(want)
            i = len(m["bars"]) - 1
            if m["sg"][i]:
                st["handled"].append("%d|%d" % (m["bars"][i]["end"], m["sg"][i]))
        except Exception as e:
            print("could not read the market while switching:", str(e)[:100], flush=True)
        cur = want
        send_keyboard("🔀 [%s] TSI plan changed: TSI is now calculated on %s. An open trade stays until its stop or the next crossover in this plan. "
                      "Tap a button any time to switch." % (MODE.upper(), tf_name(cur)))
        st["kb_sent"] = True
    elif ask or not st.get("kb_sent"):
        send_keyboard("ℹ️ [%s] TSI plan now: %s. Tap TSI 1h for the slower plan (choppy market) or TSI 45m for the normal plan." % (MODE.upper(), tf_name(cur)))
        st["kb_sent"] = True
    if live_want is not None:
        st["live"] = live_want
        send_keyboard("🔀 [%s] Entry mode: %s" % (MODE.upper(), "FAST - the trade is placed within seconds of the 1h close, using the 45m candle as it stands then (a few signals may not hold)."
                                                    if live_want else "CONFIRMED - the bot waits until the 45m candle has finished, as before (later, but the signal cannot change)."))
        st["kb_sent"] = True
    LIVE = st["live"] if "live" in st else (SIGNAL_MAP == "L")
    st["tf"] = cur
    TF = cur
    return cur


def send_alert(text):
    print(text, flush=True)
    try:
        r = requests.post("https://api.telegram.org/bot%s/sendMessage" % TG_TOKEN,
                          data={"chat_id": TG_CHAT_ID, "text": text}, timeout=20)
        if not r.json().get("ok"):
            print("Telegram error:", r.text, flush=True)
    except Exception as e:
        print("Telegram send failed:", e, flush=True)


def money(wallet_amount):
    """Wallet amount as text, with rupees when we can."""
    s = "%+.4f %s" % (wallet_amount, WALLET_ASSET)
    if WALLET_ASSET.upper() == "USD" and INR_PER_USD > 0:
        s += " (about Rs %+.0f)" % (wallet_amount * INR_PER_USD)
    elif WALLET_ASSET.upper() == "INR":
        s = "Rs %+.0f" % wallet_amount
    return s


def pnl_of(trade, exit_px):
    pts = trade["side"] * (exit_px - trade["entry"])
    wallet = pts * trade["cv"] * trade["n"] * fx()
    pct = wallet / allocation() * 100.0 if allocation() else 0.0
    return pts, wallet, pct


def book_close(st, trade, exit_px, why, now):
    pts, wallet, pct = pnl_of(trade, exit_px)
    t = st["totals"]
    t["closed"] += 1
    t["wins"] += 1 if pts > 0 else 0
    t["pts"] += pts
    t["wallet"] += wallet
    day = ist(now, "%Y-%m-%d")
    t["days"][day] = t["days"].get(day, 0.0) + wallet
    st["trade"] = None
    log_row([ist(now, "%Y-%m-%d %H:%M"), MODE, "CLOSE " + why, "LONG" if trade["side"] == 1 else "SHORT",
             trade["entry"], exit_px, trade["n"], round(pts, 1), round(wallet, 6), ""])
    return pts, wallet, pct


def close_text(trade, exit_px, why, pts, wallet, pct, now):
    side = "LONG" if trade["side"] == 1 else "SHORT"
    icon = "✅" if pts > 0 else "❌"
    return ("%s CLOSED %s (%s)\nEntry %.1f (%s) -> Exit %.1f (%s)\nResult %+.0f points x %d contract(s) = %s | %+.1f%% of allocation\n"
            "(before exchange fees)" % (icon, side, why, trade["entry"], trade["opened_label"], exit_px,
                                        ist(now, "%d %b %H:%M IST"), pts, trade["n"], money(wallet), pct))


def totals_text(st):
    t = st["totals"]
    today = ist(time.time(), "%Y-%m-%d")
    wr = "%.0f%%" % (100.0 * t["wins"] / t["closed"]) if t["closed"] else "n/a"
    return ("Running total: %d closed trades, win rate %s, %+.0f points, %s | today %s" %
            (t["closed"], wr, t["pts"], money(t["wallet"]), money(t["days"].get(today, 0.0))))


def balance_text(api):
    try:
        free, total = api.available(WALLET_ASSET)
        return "Balance: free %.4f / total %.4f %s" % (free, total, WALLET_ASSET)
    except Exception as e:
        return "Balance unavailable (%s)" % str(e)[:60]


# ============================ trading actions ============================
def wait_position(api, pid, ok, tries=8, delay=1.5):
    size = None
    for _ in range(tries):
        time.sleep(delay)
        size, _raw = api.position(pid)
        if ok(size):
            return size
    return size


def fill_price(resp, fallback):
    try:
        res = resp.get("result", resp) or {}
        return float(res.get("average_fill_price")) if res.get("average_fill_price") else fallback
    except Exception:
        return fallback


def cancel_stops(api, pid, trade):
    for name, oid in (trade.get("stop_ids") or {}).items():
        try:
            api.cancel(oid, pid)
        except Exception as e:
            print("cancel %s failed: %s" % (name, str(e)[:120]), flush=True)


def round_tick(px, tick):
    return round(round(px / tick) * tick, 8)


def close_position(api, pid, size, price_hint):
    side = "sell" if size > 0 else "buy"
    resp = api.order(side, abs(size), reduce_only=True)
    left = wait_position(api, pid, lambda s: s == 0)
    if left != 0:
        raise ApiError("Close not confirmed (position still %g). Nothing new opened." % left)
    return fill_price(resp, price_hint)


def open_position(api, pid, cv, tick, side, price, now, info):
    """Opens LONG (side=1) or SHORT (-1) with stops. Returns (trade or None, message lines)."""
    lines = []
    capital = allocation()
    free, total = api.available(WALLET_ASSET)
    if free < capital:
        return None, ["⚠️ SKIPPED OPEN: free balance %.4f %s is below the allocation %.4f. No order placed." % (free, WALLET_ASSET, capital)]
    unit = price * cv * fx()                      # one contract's value in wallet units
    lev = LEVERAGE
    if FULL_BUDGET:
        # as many whole contracts as MAX_LEVERAGE allows, then the LOWEST leverage that lets them use the whole budget
        n = int(math.floor(capital * MAX_LEVERAGE / unit))
        if n >= 1:
            lev = min(MAX_LEVERAGE, max(1, int(math.ceil(n * unit / capital - 1e-9))))
    else:
        n = int(math.floor(capital * LEVERAGE / unit))
    per = unit / lev                              # margin for one contract in wallet units
    while n >= 1 and n * per * (1 + MARGIN_BUFFER) > free:
        n -= 1
    if n < 1:
        return None, ["⚠️ SKIPPED OPEN: not enough margin for 1 contract (needs about %.4f %s, free %.4f). No order placed." % (per, WALLET_ASSET, free)]
    api.set_leverage(pid, lev)
    got = api.get_leverage(pid)
    if abs(got - lev) > 1e-9:
        raise ApiError("Leverage is %gx, expected %dx. No order placed." % (got, lev))
    resp = api.order("buy" if side == 1 else "sell", n)
    size = wait_position(api, pid, lambda s: s != 0)
    if size == 0:
        raise Halt("Order sent but no position appeared. Check the Delta account before resuming.")
    if abs(size) > n or (size > 0) != (side == 1):
        raise Halt("Unexpected position %g after ordering %d. Check the account." % (size, n))
    _, raw = api.position(pid)
    entry = float(raw.get("entry_price") or fill_price(resp, price))
    trade = {"side": side, "entry": entry, "n": int(abs(size)), "cv": cv, "opened_ts": now,
             "opened_label": ist(now, "%d %b %H:%M IST"), "sl1": entry - side * MAX_LOSS_PTS, "stop_ids": {}}
    close_side = "sell" if side == 1 else "buy"
    problems = []
    for name, dist in (("sl1", MAX_LOSS_PTS), ("sl3", HARD_STOP_PTS)):
        if not dist or (name == "sl3" and dist <= MAX_LOSS_PTS):
            continue
        px = round_tick(entry - side * dist, tick)
        try:
            r = api.stop_order(close_side, trade["n"], px)
            trade["stop_ids"][name] = (r.get("result", {}) or {}).get("id")
            lines.append("🛡 %s placed at %.1f (%d points from entry)" %
                         ("Stop-loss" if name == "sl1" else "Hard stop", px, dist))
        except Exception as e:
            problems.append("%s: %s" % (name, str(e)[:120]))
    trade["stop_ids"] = {k: v for k, v in trade["stop_ids"].items() if v is not None}
    if problems:
        lines.append("⚠️ Exchange stop NOT placed (%s). The bot checks the %d-point stop on every run and will close at market." %
                     ("; ".join(problems), MAX_LOSS_PTS))
    lines.insert(0, "📌 OPENED %s %d contract(s) at %.1f | %dx | margin about %.4f %s" %
                 ("LONG" if side == 1 else "SHORT", trade["n"], entry, lev, trade["n"] * per, WALLET_ASSET))
    log_row([ist(now, "%Y-%m-%d %H:%M"), MODE, "OPEN", "LONG" if side == 1 else "SHORT", entry, "", trade["n"], "", "", info])
    return trade, lines


# ============================ one run ============================
def place_stops(api, trade, tick):
    """The bot's exchange stops (800 and 1200 points from the entry) for the trade record. Returns message lines."""
    side, lines, problems = trade["side"], [], []
    close_side = "sell" if side == 1 else "buy"
    trade["stop_ids"] = {}
    for name, dist in (("sl1", MAX_LOSS_PTS), ("sl3", HARD_STOP_PTS)):
        if not dist or (name == "sl3" and dist <= MAX_LOSS_PTS):
            continue
        px = round_tick(trade["entry"] - side * dist, tick)
        try:
            r = api.stop_order(close_side, trade["n"], px)
            trade["stop_ids"][name] = (r.get("result", {}) or {}).get("id")
            lines.append("🛡 %s placed at %.1f (%d points from entry)" % ("Stop-loss" if name == "sl1" else "Hard stop", px, dist))
        except Exception as e:
            problems.append("%s: %s" % (name, str(e)[:120]))
    trade["stop_ids"] = {k: v for k, v in trade["stop_ids"].items() if v is not None}
    if problems:
        lines.append("⚠️ Exchange stop NOT placed (%s). The bot checks the %d-point stop on every run and will close at market." %
                     ("; ".join(problems), MAX_LOSS_PTS))
    return lines


def confirm_position(api, pid, size):
    """Before reacting to a position that differs from the bot's memory, read it twice more so one bad answer from Delta cannot fool the bot."""
    raw = {}
    for _ in range(2):
        time.sleep(2)
        s2, raw = api.position(pid)
        if s2 != size:
            raise Halt("Delta's position keeps changing (%g, then %g). Check the account, then run resume." % (size, s2))
    return raw


def adopt_position(api, pid, st, mkt, now, tick, size, raw, old):
    """You changed the position by hand. The real position on Delta is the truth: the bot closes its old record and manages yours."""
    lines = []
    last_px = mkt["c15"][-1][4]
    if old:
        cancel_stops(api, pid, old)
        pts, wallet, pct = book_close(st, old, last_px, "closed by you by hand (price estimated at the latest candle)", now)
        lines.append(close_text(old, last_px, "closed by you by hand, price estimated", pts, wallet, pct, now))
    entry = float(raw.get("entry_price") or last_px)
    sd = 1 if size > 0 else -1
    trade = {"side": sd, "entry": entry, "n": int(abs(size)), "cv": 0.001, "opened_ts": now,
             "opened_label": ist(now, "%d %b %H:%M IST") + " (your trade, not opened by the bot)", "sl1": entry - sd * MAX_LOSS_PTS, "stop_ids": {}}
    lines += place_stops(api, trade, tick)
    st["trade"] = trade
    st["halted"] = False
    log_row([ist(now, "%Y-%m-%d %H:%M"), MODE, "ADOPT", "LONG" if sd == 1 else "SHORT", entry, "", trade["n"], "", "", "position changed by hand"])
    word = "LONG" if sd == 1 else "SHORT"
    send_alert("ℹ️ [%s] I see you changed the position by hand: Delta now has %s %d contract(s) at %.1f.\n%s%s\n"
               "The bot now manages this trade. Same-direction crossover: nothing changes. Opposite crossover: it closes all %d contract(s) and opens its own trade."
               % (MODE.upper(), word, trade["n"], entry, ("\n".join(lines) + "\n") if lines else "", "", trade["n"]))


def reconcile(api, pid, st, mkt, now, tick=None):
    """Compare the bot's memory with Delta. The real position on Delta wins. Returns the current signed size."""
    tick = tick or 0.5
    size, raw = api.position(pid)
    trade = st["trade"]
    if trade and size == 0:                                   # stopped out, liquidated or closed by hand
        exit_px, why = None, "closed outside the bot (manual?)"
        for name in ("sl1", "sl3"):
            oid = (trade.get("stop_ids") or {}).get(name)
            if not oid:
                continue
            try:
                info = api.order_info(oid)
                if str(info.get("state", "")).lower() in ("closed", "filled") and info.get("average_fill_price"):
                    exit_px, why = float(info["average_fill_price"]), "stop-loss hit" if name == "sl1" else "hard stop hit"
                    break
            except Exception:
                pass
        if exit_px is None:
            since = [c for c in mkt["c15"] if c[0] >= trade["opened_ts"] - trade["opened_ts"] % B15]
            hit = bool(since) and ((trade["side"] == 1 and min(c[3] for c in since) <= trade["sl1"]) or
                                   (trade["side"] == -1 and max(c[2] for c in since) >= trade["sl1"]))
            if hit:
                exit_px, why = trade["sl1"], "stop-loss hit (price estimated at the stop level)"
            else:
                exit_px = mkt["c15"][-1][4]
        cancel_stops(api, pid, trade)
        pts, wallet, pct = book_close(st, trade, exit_px, why, now)
        send_alert(close_text(trade, exit_px, why, pts, wallet, pct, now) + "\nBot is flat; the next valid crossover opens a trade.\n"
                   + totals_text(st) + "\n" + balance_text(api))
    elif trade and (size > 0) != (trade["side"] == 1):        # you closed the bot's trade and opened the opposite one
        raw = confirm_position(api, pid, size)
        adopt_position(api, pid, st, mkt, now, tick, size, raw, trade)
    elif not trade and size != 0:                             # a position opened by hand while the bot was flat
        raw = confirm_position(api, pid, size)
        adopt_position(api, pid, st, mkt, now, tick, size, raw, None)
    elif trade and int(abs(size)) != int(trade["n"]):         # same direction, but you added or reduced contracts
        raw = confirm_position(api, pid, size)
        cancel_stops(api, pid, trade)
        old_n, trade["n"] = trade["n"], int(abs(size))
        lines = place_stops(api, trade, tick)
        send_alert("ℹ️ [%s] The quantity changed by hand: %s %d -> %d contract(s). The stops were replaced to match.\n%s"
                   % (MODE.upper(), "LONG" if trade["side"] == 1 else "SHORT", old_n, trade["n"], "\n".join(lines)))
    return 0 if (trade and size == 0) else size


def bot_stop_check(api, pid, st, mkt, size, now):
    trade = st["trade"]
    if not trade or size == 0:
        return size
    since = [c for c in mkt["c15"] if c[0] >= trade["opened_ts"] - trade["opened_ts"] % B15]
    if not since:
        return size
    sd = trade["side"]
    touched = (sd == 1 and min(c[3] for c in since) <= trade["sl1"]) or (sd == -1 and max(c[2] for c in since) >= trade["sl1"])
    if not touched:
        return size
    px = api.last_price()
    exit_px = close_position(api, pid, size, px)
    cancel_stops(api, pid, trade)
    pts, wallet, pct = book_close(st, trade, exit_px, "stop-loss by bot check", now)
    send_alert("🛑 The %d-point stop level was touched but the exchange stop had not closed the trade, so the bot closed it at market.\n" % MAX_LOSS_PTS
               + close_text(trade, exit_px, "stop-loss by bot check", pts, wallet, pct, now) + "\n" + totals_text(st) + "\n" + balance_text(api))
    return 0


def ema_watch(st, mkt, now):
    """MESSAGE ONLY. While a trade is open: LONG -> tell me when a 1h candle CLOSES BELOW the 2h 5 EMA, SHORT -> when it closes ABOVE it.
    The 1h close is compared with the EMA of the last 2h candle that had finished when that 1h candle opened. Only candles that close
    after the trade was opened count, and it speaks once each time the close moves to the wrong side."""
    trade = st.get("trade")
    if not EMA_ALERT or not trade:
        st.pop("ema_watch", None)
        return
    w = st.get("ema_watch")
    if not w or w.get("trade_ts") != trade["opened_ts"]:
        w = st["ema_watch"] = {"trade_ts": trade["opened_ts"], "seen_end": 0, "side": 0}
    b120 = aggregate(mkt["c15"], 120)
    if len(b120) < EMA_LEN + 3:
        return
    e2 = ema([b["c"] for b in b120], EMA_LEN)
    ends2 = [b["end"] for b in b120]
    bad = -trade["side"]                                       # LONG is hurt by a close BELOW (-1), SHORT by a close ABOVE (+1)
    for hb in mkt["bars"]:
        if hb["end"] <= trade["opened_ts"] or hb["end"] <= w["seen_end"]:
            continue
        j = bisect_right(ends2, hb["t"]) - 1
        if j < EMA_LEN:
            continue
        side = 1 if hb["c"] > e2[j] else -1 if hb["c"] < e2[j] else 0
        w["seen_end"] = hb["end"]
        if side == bad and w["side"] != bad and now - hb["end"] <= 3 * 3600:
            pts = (hb["c"] - trade["entry"]) * trade["side"]
            send_alert("🔔 [%s] %s trade: the 1h candle %s-%s IST closed %s the 2h 5 EMA (close %.1f vs EMA %.1f).\n"
                       "Alert only - nothing was changed. Trade opened %s at %.1f; now %+.0f pts at the candle close; stop %.1f."
                       % (MODE.upper(), "LONG" if trade["side"] == 1 else "SHORT", ist(hb["t"], "%H:%M"), ist(hb["end"], "%H:%M"),
                          "BELOW" if side == -1 else "ABOVE", hb["c"], e2[j], trade["opened_label"], trade["entry"], pts, trade["sl1"]))
        w["side"] = side


def ema3_note(st, mkt, now):
    """MESSAGE ONLY, trade or no trade: a small note when a 1h candle CLOSES above or below the 5 EMA of the 3h candles (3h EMA on the 1h chart).
    The 1h close is compared with the EMA of the last 3h candle that had finished when that 1h candle opened. By default it speaks when the close
    moves to the other side of the EMA (EMA3_EVERY=1: after every 1h close)."""
    if not EMA3_ALERT:
        return
    b180 = aggregate(mkt["c15"], 180)
    if len(b180) < EMA_LEN + 3 or not mkt["bars"]:
        return
    e3 = ema([b["c"] for b in b180], EMA_LEN)
    ends3 = [b["end"] for b in b180]

    def side_of(hb):
        j = bisect_right(ends3, hb["t"]) - 1
        if j < EMA_LEN:
            return None, None
        return (1 if hb["c"] > e3[j] else -1 if hb["c"] < e3[j] else 0), e3[j]
    w = st.get("ema3")
    if not w:                                                  # first run: start from now, no old alerts
        last = mkt["bars"][-1]
        w = st["ema3"] = {"seen_end": last["end"], "side": side_of(last)[0] or 0}
        return
    for hb in mkt["bars"]:
        if hb["end"] <= w["seen_end"]:
            continue
        side, e = side_of(hb)
        w["seen_end"] = hb["end"]
        if side is None:
            continue
        if side != 0 and (EMA3_EVERY or side != w["side"]) and now - hb["end"] <= 3 * 3600:
            send_alert("📏 [%s] 1h candle %s-%s IST closed %s the 3h 5 EMA: close %.1f vs EMA %.1f (%+.1f)"
                       % (MODE.upper(), ist(hb["t"], "%H:%M"), ist(hb["end"], "%H:%M"), "ABOVE" if side == 1 else "BELOW", hb["c"], e, hb["c"] - e))
        w["side"] = side if side != 0 else w["side"]


def handle_crossover(api, pid, cv, tick, st, mkt, size, now):
    bars, i = mkt["bars"], len(mkt["bars"]) - 1
    d = mkt["sg"][i]
    if not d:
        return
    bar = bars[i]
    key = "%d|%d" % (bar["end"], d)
    if key in st["handled"]:
        return
    word = "BULLISH" if d == 1 else "BEARISH"
    tv = mkt["shown"][i]
    head = "%s [%s] %s TSI %s crossover on the 1h candle labelled %s (closed %s IST)" % (
        "🟢" if d == 1 else "🔴", MODE.upper(), SYMBOL, word, ist(bar["t"], "%H:%M"), ist(bar["end"], "%H:%M"))
    kn = (mkt.get("known") or [bar["end"]] * (i + 1))[i]
    if kn > bar["end"]:
        head += ", confirmed %s IST when the 45m candle closed" % ist(kn, "%H:%M")
    elif LIVE and TF != 60:
        head += " (FAST signal: the 45m candle was still forming)"
    tail = "\nTSI %.2f vs signal %.2f | candle move %.0f pts (range %.0f) | price %.1f" % (tv[0], tv[1], size_of(bars, i), bar["h"] - bar["l"], bar["c"]) if tv else ""
    tail += "\nTSI plan: %s" % tf_name(TF)
    age = (now - (mkt.get("known") or [bar["end"]] * (i + 1))[i]) / 60.0       # minutes since the signal became known
    if age > MAX_SIGNAL_AGE_MIN:
        st["handled"].append(key)
        send_alert("%s\nExpired (%.0f min old, limit %d). No order placed.%s" % (head, age, MAX_SIGNAL_AGE_MIN, tail))
        return
    if mkt["skip"][i]:
        st["handled"].append(key)
        r1, r2 = size_of(bars, i), mkt["extra"][i]
        prev = max(size_of(bars, k) for k in range(max(0, i - LOOKBACK_CANDLES + 1), i + 1))
        send_alert("%s\n⚪ SKIPPED: a candle move of %d+ points is involved (1h/previous %.0f, 45m %.0f; %s). Nothing closed or opened; waiting for the next crossover.%s"
                   % (head, MAX_CANDLE_PTS, prev, r2, "close-to-close change" if CANDLE_MEASURE != "range" else "high-low range", tail))
        log_row([ist(now, "%Y-%m-%d %H:%M"), MODE, "SKIP", word, "", "", "", "", "", "big candle"])
        return
    if st["halted"] or PAUSE:
        st["handled"].append(key)
        send_alert("%s\nPaused (%s). No order placed.%s" % (head, "safety halt: run --resume after checking the account" if st["halted"] else "BOT_PAUSE=1", tail))
        return
    lines = []
    if size != 0 and (size > 0) == (d == 1):
        st["handled"].append(key)
        send_alert("%s\nAlready %s: no change.%s" % (head, "LONG" if d == 1 else "SHORT", tail))
        return
    if size != 0:                                             # reverse: close first
        trade = st["trade"]
        exit_px = close_position(api, pid, size, bar["c"])
        if trade:
            cancel_stops(api, pid, trade)
            pts, wallet, pct = book_close(st, trade, exit_px, "reversed by crossover", now)
            lines.append(close_text(trade, exit_px, "reversed by crossover", pts, wallet, pct, now))
        save_state(st)
    new, more = open_position(api, pid, cv, tick, d, bar["c"], now, "%s crossover" % word)
    lines += more
    if new:
        st["trade"] = new
    st["handled"].append(key)
    save_state(st)
    send_alert(head + "\n" + "\n".join(lines) + "\n" + totals_text(st) + "\n" + balance_text(api) + tail)


def heartbeat(api, pid, st, now):
    day = ist(now, "%Y-%m-%d")
    if st["last_hb_date"] == day or int(ist(now, "%H")) < HEARTBEAT_HOUR_IST:
        return
    trade = st["trade"]
    pos = "flat" if not trade else "%s %d contract(s) from %.1f (since %s), stop %.1f" % (
        "LONG" if trade["side"] == 1 else "SHORT", trade["n"], trade["entry"], trade["opened_label"], trade["sl1"])
    send_alert("💚 [%s] bot running | TSI on %s | %s\n%s\n%s%s" % (MODE.upper(), "1h candles" if TF == 60 else "45m candles", pos, totals_text(st), balance_text(api),
                                                    " | PAUSED" if PAUSE else (" | HALTED" if st["halted"] else "")))
    st["last_hb_date"] = day


def candle_published(ts):
    """True when Delta already lists the finished 15m candle that started at ts."""
    try:
        r = requests.get(DATA_BASE + "/v2/history/candles",
                         params={"symbol": SYMBOL, "resolution": "15m", "start": str(ts - 900), "end": str(int(time.time()))},
                         headers={"User-Agent": UA}, timeout=10)
        rows = r.json().get("result", [])
        return any(int(x["time"]) == ts for x in rows)
    except Exception:
        return False


def next_signal_time(now):
    """The next moment a crossover can become known: the 45m candle close that decides a 1h candle (45m plan, confirmed mode),
    or the 1h close itself (1h plan, or fast mode)."""
    step = CALC_MIN * 60
    base = int(now) // 3600 * 3600
    for E in (base, base + 3600):                                # the last 1h close and the next one
        k = E if (TF == 60 or LIVE) else ((E - 1) // step) * step + step
        if k > now:
            return k
    return None


def next_wait_target(now):
    """The next moment worth staying awake for: when a TSI crossover can become known, and (while the 3h EMA note is on) every 1h close."""
    cands = [next_signal_time(now)]
    if EMA3_ALERT:
        cands.append(int(now) // 3600 * 3600 + 3600)
    cands = [c for c in cands if c]
    return min(cands) if cands else None


def wait_for_close():
    """If the next such moment is within WAIT_MAX_SEC, stay awake until that candle has closed and Delta lists it. True if it waited."""
    now = time.time()
    nxt = next_wait_target(now)
    if nxt is None or nxt - now > WAIT_MAX_SEC:
        return False
    print("waiting %.0f s for the candle to close (%s IST)" % (nxt - now, ist(nxt, "%H:%M")), flush=True)
    while time.time() < nxt:
        time.sleep(min(0.5, max(0.0, nxt - time.time())))
    end = time.time() + 25
    while time.time() < end:
        if candle_published(nxt - 900):
            break
        time.sleep(0.4)
    time.sleep(0.3)
    print("candle closed and published %.1f s after the close" % (time.time() - nxt), flush=True)
    return True


def run_once(api, pid, cv, tick, st):
    now = time.time()
    try:
        apply_mode(st)
        save_state(st)
    except Exception as e:
        print("mode check problem:", str(e)[:150], flush=True)
    tag = parse_tf(PLAN_TAG) if PLAN_TAG else None
    if tag and tag != TF:                                       # this cron job belongs to the other plan: do nothing
        print("This job is for the %s plan, but the %s plan is on. Nothing to do." % (tf_name(tag), tf_name(TF)), flush=True)
        return
    mkt = load_market(TF)
    try:
        size = reconcile(api, pid, st, mkt, now, tick)
        save_state(st)
        size = bot_stop_check(api, pid, st, mkt, size, now)
        save_state(st)
        if wait_for_close():                                    # the candle has just closed: read it again and trade at once
            now = time.time()
            mkt = load_market(TF)
            fresh, _ = api.position(pid)
            if fresh != size:                                   # something changed while waiting (stop hit, trade by hand): book it first
                size = reconcile(api, pid, st, mkt, now, tick)
                save_state(st)
            else:
                size = fresh
        handle_crossover(api, pid, cv, tick, st, mkt, size, now)
        try:
            ema_watch(st, mkt, now)
        except Exception as e:                                  # an alert problem must never disturb trading
            print("ema watch problem:", str(e)[:150], flush=True)
        try:
            ema3_note(st, mkt, now)
        except Exception as e:
            print("3h ema note problem:", str(e)[:150], flush=True)
        heartbeat(api, pid, st, now)
    except Halt as h:
        st["halted"] = True
        send_alert("🛑 [%s] HALTED: %s\nNo more orders until you run --resume." % (MODE.upper(), h))
    except Exception as e:
        key = "err|" + str(e)[:60]
        if key not in st["warned"]:
            st["warned"].append(key)
            send_alert("❌ [%s] problem: %s\nIP Delta sees: %s (must be whitelisted). The bot retries on the next run; no new trade "
                       "until the position is re-read." % (MODE.upper(), str(e)[:300], outgoing_ip(api)))
        else:
            print("repeat problem:", str(e)[:150], flush=True)
    finally:
        save_state(st)


def outgoing_ip(api):
    for url in ("https://api.ipify.org", "https://api6.ipify.org"):
        try:
            return requests.get(url, timeout=10, proxies=api.proxies).text.strip()
        except Exception:
            pass
    return "unknown"


# ============================ commands ============================
def build_api():
    if MODE not in ("demo", "live"):
        raise SystemExit('MODE must be "demo" or "live" (the bot received: %r).' % MODE)
    if MODE == "live" and LIVE_CONFIRM != LIVE_PHRASE:
        raise SystemExit('Live mode uses REAL MONEY. Set LIVE_CONFIRM to exactly: %s' % LIVE_PHRASE)
    if "PASTE_" in API_KEY or "PASTE_" in API_SECRET:
        raise SystemExit("Set DELTA_API_KEY and DELTA_API_SECRET.")
    return Delta(LIVE_BASE if MODE == "live" else DEMO_BASE, API_KEY, API_SECRET, PROXY_URL)


def cmd_check(api):
    print("MODE:", MODE, "| address:", api.base)
    print("IP Delta will see:", outgoing_ip(api), "| via proxy" if api.proxies else "| direct")
    pid, cv, tick = api.product()
    print("Product %s: id %s, contract %s BTC, tick %s" % (SYMBOL, pid, cv, tick))
    print("Product details: %s" % getattr(api, "product_info", "?"))
    print("ALL wallets on this account: %s" % ("; ".join(api.all_wallets()) or "none"))
    free, total = api.available(WALLET_ASSET)
    print("Wallet %s: free %s / total %s" % (WALLET_ASSET, free, total))
    size, raw = api.position(pid)
    print("Position:", size, "| entry:", raw.get("entry_price"))
    try:
        print("Leverage on Delta:", api.get_leverage(pid), "x (bot wants", LEVERAGE, "x)")
    except Exception as e:
        print("Could not read leverage:", e)
    mkt = load_market()
    i = len(mkt["bars"]) - 1
    print("Last closed 1h candle labelled %s IST: move %.0f pts (range %.0f) | crossover now: %s | skipped by big-candle rule: %s" %
          (ist(mkt["bars"][i]["t"], "%d %b %H:%M"), size_of(mkt["bars"], i), mkt["bars"][i]["h"] - mkt["bars"][i]["l"], mkt["sg"][i] or "none", mkt["skip"][i]))
    print("Allocation:", CAPITAL_INR, "INR =", allocation(), WALLET_ASSET)
    print("Check finished: no orders were sent.")


def cmd_test_order(api):
    pid, cv, tick = api.product()
    size, _ = api.position(pid)
    if size != 0:
        raise SystemExit("The account already has a position (%g). Close it first." % size)
    if MODE == "live":
        send_alert("⚠️ [LIVE] TEST ORDER starting: the bot will REALLY buy 1 contract (about 0.001 BTC), place and cancel a stop order, "
                   "then sell it. Cost: only trading fees and a tiny spread.")
    api.set_leverage(pid, LEVERAGE)
    print("Leverage now:", api.get_leverage(pid))
    api.order("buy", 1)
    s = wait_position(api, pid, lambda x: x != 0)
    print("position after buy:", s)
    if s == 0:
        raise SystemExit("No position after buy; check the demo site.")
    _, raw = api.position(pid)
    entry = float(raw.get("entry_price") or api.last_price())
    try:
        r = api.stop_order("sell", 1, round_tick(entry - MAX_LOSS_PTS, tick))
        sid = (r.get("result", {}) or {}).get("id")
        print("stop order placed, id", sid)
        api.cancel(sid, pid)
        print("stop order cancelled")
    except Exception as e:
        print("STOP ORDER PROBLEM (tell Claude this exact text):", e)
    api.order("sell", abs(s), reduce_only=True)
    print("position after close:", wait_position(api, pid, lambda x: x == 0))
    send_alert("🧪 [%s] test cycle finished: bought 1 contract, stop order placed and cancelled, closed. %s" % (MODE.upper(), balance_text(api)))


if __name__ == "__main__":
    api = build_api()
    if "--check" in sys.argv:
        allocation()
        cmd_check(api)
    elif "--test-order" in sys.argv:
        cmd_test_order(api)
    elif "--resume" in sys.argv:
        s = load_state()
        s["halted"] = False
        save_state(s)
        print("Halt cleared. Check your Delta position first.")
    elif "--status" in sys.argv:
        s = load_state()
        print(json.dumps({"trade": s["trade"], "halted": s["halted"], "totals": s["totals"]}, indent=1))
    else:
        allocation()
        pid, cv, tick = api.product()
        if "--loop" in sys.argv:
            send_alert("🚀 [%s] TSI bot started (loop) | %s | allocation %s INR | %dx | stop %d pts" % (MODE.upper(), SYMBOL, CAPITAL_INR, LEVERAGE, MAX_LOSS_PTS))
            while True:
                run_once(api, pid, cv, tick, load_state())
                time.sleep(60)
        else:
            run_once(api, pid, cv, tick, load_state())
