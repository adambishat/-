#!/usr/bin/env python3
"""בוט התראות בורסה לטלגרם — רץ ב-GitHub Actions.

קורא TELEGRAM_TOKEN ו-TELEGRAM_CHAT_ID מהסביבה, בודק את רשימת המעקב והחדשות,
ושולח הודעות בעברית. state.json משמש למניעת כפילויות (נשמר 3 ימים).
הרצה לבדיקה בלי שליחה:  DRY_RUN=1 python bot.py
"""

import calendar
import hashlib
import html
import json
import os
import re
import sys
import time
from datetime import date, datetime, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

import feedparser
import pandas as pd
import requests
import yfinance as yf

# ============================================================
# הגדרות — אפשר לערוך כאן
# ============================================================
PRICE_MOVE_PCT = 3            # תנועה יומית באחוזים (עלייה או ירידה)
VOLUME_MULT = 2               # מחזור גדול פי X מהממוצע (20 ימים)
RSI_LOW = 30                  # RSI יורד מתחת ל-30 (מכירת יתר)
RSI_HIGH = 70                 # RSI עולה מעל 70 (קניית יתר)
RSI_PERIOD = 14
MA_SHORT = 20
MA_LONG = 50
EARNINGS_DAYS_AHEAD = 3       # התראה על דוחות עד X ימים קדימה
NEWS_MAX_AGE_MIN = 90         # כותרות מה-X דקות האחרונות
NEWS_MAX_PER_RUN = 8          # תקרת כותרות בהרצה אחת
DEDUPE_DAYS = 3               # כמה זמן לזכור התראות ב-state.json

WATCHLIST = [
    # מדד ת"א 125 ומניות מובילות
    "^TA125.TA",
    "LUMI.TA", "POLI.TA", "DSCT.TA", "MZTF.TA", "FIBI.TA",
    "ICL.TA", "TEVA.TA", "NICE.TA", "ESLT.TA", "BEZQ.TA",
    "AZRG.TA", "NVMI.TA", "TSEM.TA", "ENLT.TA", "DLEKG.TA",
    "PHOE.TA", "HARL.TA", "MGDL.TA", "SAE.TA", "STRS.TA",
    # וול סטריט
    "^GSPC", "^IXIC",
    "AAPL", "MSFT", "NVDA", "GOOGL", "AMZN", "META", "TSLA",
    "AVGO", "NFLX", "AMD", "JPM",
]

# שמות תצוגה (לא חובה; מה שלא כאן מוצג לפי הסימול)
NAMES = {
    "^TA125.TA": "ת״א 125",
    "^GSPC": "S&P 500",
    "^IXIC": "נאסד״ק",
}

NEWS_FEEDS = {
    "BBC Business": "http://feeds.bbci.co.uk/news/business/rss.xml",
    "CNBC": "https://www.cnbc.com/id/100003114/device/rss/rss.html",
    "Yahoo Finance": "https://finance.yahoo.com/news/rssindex",
    "גלובס": "https://www.globes.co.il/webservice/rss/rssfeeder.asmx/FeederNode?iID=585",
}

NEWS_KEYWORDS = [
    "Fed", "interest rate", "inflation", "tariff", "tariffs", "war",
    "recession", "Bank of Israel", "rate cut", "rate hike", "sanctions",
    "ריבית", "אינפלציה", "מלחמה", "מכס", "בנק ישראל", "הפד",
]
# מילים שמותאמות רק באותיות גדולות/קטנות בדיוק (כדי ש-"fed" בפועל לא יתפוס)
CASE_SENSITIVE_KEYWORDS = {"Fed"}

# ============================================================
# קבועים טכניים
# ============================================================
STATE_FILE = Path(__file__).with_name("state.json")
TZ = ZoneInfo("Asia/Jerusalem")
HISTORY_PERIOD = "6mo"
MAX_BAR_AGE_DAYS = 5          # נרות ישנים יותר נחשבים לא רלוונטיים
HTTP_TIMEOUT = 20
RLM = "\u200f"                # סימן כתיבה מימין לשמאל
UA = {"User-Agent": "Mozilla/5.0 (stock-alerts-bot)"}


def log(msg):
    print(msg, flush=True)


# ------------------------------------------------------------
# state
# ------------------------------------------------------------
def load_state():
    try:
        data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def prune_state(state):
    """state: {key: expiry_epoch}. מוחק מפתחות שפג תוקפם."""
    now = time.time()
    return {k: v for k, v in state.items() if isinstance(v, (int, float)) and v > now}


def save_state(state):
    STATE_FILE.write_text(
        json.dumps(state, ensure_ascii=False, indent=1, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def mark(state, key, ttl_days=DEDUPE_DAYS):
    state[key] = time.time() + ttl_days * 86400


# ------------------------------------------------------------
# עזרים
# ------------------------------------------------------------
def label(sym):
    return NAMES.get(sym, sym.replace(".TA", ""))


def fmt_price(sym, price):
    if sym.startswith("^"):
        return f"{price:,.2f}"
    if sym.endswith(".TA"):
        return f"{price:,.2f} אג׳"   # ב-Yahoo מניות ת"א נסחרות באגורות
    return f"${price:,.2f}"


def rtl(text):
    return "\n".join(RLM + ln if ln else ln for ln in text.split("\n"))


def esc(s):
    return html.escape(str(s), quote=False)


def compute_rsi(close, n=RSI_PERIOD):
    delta = close.diff()
    up = delta.clip(lower=0)
    down = -delta.clip(upper=0)
    avg_up = up.ewm(alpha=1 / n, adjust=False, min_periods=n).mean()
    avg_down = down.ewm(alpha=1 / n, adjust=False, min_periods=n).mean()
    rs = avg_up / avg_down
    return 100 - 100 / (1 + rs)


# ------------------------------------------------------------
# בדיקות למניה
# ------------------------------------------------------------
def analyze_symbol(sym, state):
    """מחזיר רשימת (key, text, ttl_days)."""
    alerts = []
    ticker = yf.Ticker(sym)
    df = ticker.history(period=HISTORY_PERIOD, interval="1d", auto_adjust=False)
    if df is None or df.empty:
        raise ValueError("אין נתונים")
    df = df.dropna(subset=["Close"])
    if len(df) < 3:
        raise ValueError("מעט מדי נתונים")

    bar_date = df.index[-1].date()
    if (datetime.now(TZ).date() - bar_date).days > MAX_BAR_AGE_DAYS:
        raise ValueError(f"הנתון האחרון ישן ({bar_date})")

    close = df["Close"]
    volume = df["Volume"] if "Volume" in df else None
    price = float(close.iloc[-1])
    name = esc(label(sym))
    d = bar_date.isoformat()

    # 1) תנועה יומית
    prev_close = float(close.iloc[-2])
    if prev_close:
        pct = (price / prev_close - 1) * 100
        if abs(pct) >= PRICE_MOVE_PCT:
            up = pct > 0
            alerts.append((
                f"move:{sym}:{d}:{'up' if up else 'down'}",
                f"{'📈' if up else '📉'} <b>{name}</b> {'עלייה' if up else 'ירידה'} של "
                f"{abs(pct):.1f}% | {fmt_price(sym, price)}",
                DEDUPE_DAYS,
            ))

    # 2) זינוק במחזור (לא רלוונטי למדדים ללא מחזור)
    if volume is not None and len(volume) > 21:
        avg_vol = float(volume.iloc[-21:-1].mean())
        last_vol = float(volume.iloc[-1])
        if avg_vol > 0 and last_vol >= VOLUME_MULT * avg_vol:
            alerts.append((
                f"vol:{sym}:{d}",
                f"🔊 <b>{name}</b> זינוק במחזור: פי {last_vol / avg_vol:.1f} "
                f"מהממוצע | {fmt_price(sym, price)}",
                DEDUPE_DAYS,
            ))

    # 3) RSI חוצה 30 / 70
    rsi = compute_rsi(close).dropna()
    if len(rsi) >= 2:
        r_prev, r_now = float(rsi.iloc[-2]), float(rsi.iloc[-1])
        if r_prev >= RSI_LOW > r_now:
            alerts.append((
                f"rsi:{sym}:{d}:low",
                f"🟢 <b>{name}</b> RSI ירד מתחת ל-{RSI_LOW} ({r_now:.0f}) — מכירת יתר | "
                f"{fmt_price(sym, price)}",
                DEDUPE_DAYS,
            ))
        elif r_prev <= RSI_HIGH < r_now:
            alerts.append((
                f"rsi:{sym}:{d}:high",
                f"🔴 <b>{name}</b> RSI עלה מעל {RSI_HIGH} ({r_now:.0f}) — קניית יתר | "
                f"{fmt_price(sym, price)}",
                DEDUPE_DAYS,
            ))

    # 4) חציית ממוצעים MA20 / MA50
    if len(close) > MA_LONG + 1:
        diff = (close.rolling(MA_SHORT).mean() - close.rolling(MA_LONG).mean()).dropna()
        if len(diff) >= 2:
            d_prev, d_now = float(diff.iloc[-2]), float(diff.iloc[-1])
            if d_prev <= 0 < d_now:
                alerts.append((
                    f"ma:{sym}:{d}:golden",
                    f"✨ <b>{name}</b> חציית זהב: MA{MA_SHORT} חצה מעל MA{MA_LONG} | "
                    f"{fmt_price(sym, price)}",
                    DEDUPE_DAYS,
                ))
            elif d_prev >= 0 > d_now:
                alerts.append((
                    f"ma:{sym}:{d}:death",
                    f"⚠️ <b>{name}</b> חציית מוות: MA{MA_SHORT} חצה מתחת ל-MA{MA_LONG} | "
                    f"{fmt_price(sym, price)}",
                    DEDUPE_DAYS,
                ))

    # 5) דוחות קרובים (לא למדדים)
    if not sym.startswith("^"):
        try:
            alerts += analyze_earnings(sym, ticker, state)
        except Exception as e:  # noqa: BLE001
            log(f"[earnings] {sym}: {e}")

    return alerts


def _to_date(x):
    if isinstance(x, datetime):
        return x.date()
    if isinstance(x, pd.Timestamp):
        return x.date()
    if isinstance(x, date):
        return x
    return pd.Timestamp(x).date()


def upcoming_earnings_dates(ticker):
    cal = ticker.calendar
    raw = []
    if isinstance(cal, dict):
        v = cal.get("Earnings Date")
        raw = list(v) if isinstance(v, (list, tuple)) else ([v] if v is not None else [])
    elif isinstance(cal, pd.DataFrame) and "Earnings Date" in cal.index:
        raw = [x for x in cal.loc["Earnings Date"].tolist() if pd.notna(x)]
    return [_to_date(x) for x in raw]


def analyze_earnings(sym, ticker, state):
    # בודקים פעם ביום למניה, כדי לא להעמיס על Yahoo
    today = datetime.now(TZ).date()
    check_key = f"earncheck:{sym}:{today.isoformat()}"
    if check_key in state:
        return []
    dates = upcoming_earnings_dates(ticker)
    mark(state, check_key)

    alerts = []
    for ed in dates:
        days = (ed - today).days
        if 0 <= days <= EARNINGS_DAYS_AHEAD:
            when = "היום" if days == 0 else ("מחר" if days == 1 else f"בעוד {days} ימים")
            alerts.append((
                f"earn:{sym}:{ed.isoformat()}",
                f"📅 <b>{esc(label(sym))}</b> מפרסמת דוחות {when} ({ed.strftime('%d.%m')})",
                EARNINGS_DAYS_AHEAD + 2,   # חלון ארוך מ-3 ימים כדי שלא יישלח שוב
            ))
    return alerts


# ------------------------------------------------------------
# חדשות
# ------------------------------------------------------------
def keyword_hits(text):
    low = text.lower()
    hits = []
    for kw in NEWS_KEYWORDS:
        if kw in CASE_SENSITIVE_KEYWORDS:
            pattern, hay = r"(?<!\w)" + re.escape(kw) + r"(?!\w)", text
        elif kw.isascii():
            pattern, hay = r"(?<!\w)" + re.escape(kw.lower()) + r"(?!\w)", low
        else:
            if kw.lower() in low:
                hits.append(kw)
            continue
        if re.search(pattern, hay):
            hits.append(kw)
    return hits


def analyze_feed(name, url):
    resp = requests.get(url, headers=UA, timeout=HTTP_TIMEOUT)
    resp.raise_for_status()
    feed = feedparser.parse(resp.content)
    now = time.time()
    alerts = []
    for e in feed.entries:
        ts = e.get("published_parsed") or e.get("updated_parsed")
        if not ts:
            continue
        age_min = (now - calendar.timegm(ts)) / 60
        if age_min > NEWS_MAX_AGE_MIN or age_min < -10:
            continue
        title = e.get("title", "").strip()
        summary = re.sub(r"<[^>]+>", " ", e.get("summary", ""))
        hits = keyword_hits(f"{title} {summary}")
        if not hits:
            continue
        link = e.get("link", "")
        uid = hashlib.sha1((link or title).encode("utf-8")).hexdigest()[:16]
        text = f"📰 <b>{esc(name)}</b>: {esc(title)}\nמילות מפתח: {esc(', '.join(hits))}"
        if link:
            text += f'\n<a href="{html.escape(link, quote=True)}">לכתבה</a>'
        alerts.append((f"news:{uid}", text, DEDUPE_DAYS))
    return alerts


# ------------------------------------------------------------
# טלגרם
# ------------------------------------------------------------
def send_telegram(text, token, chat_id):
    if os.environ.get("DRY_RUN"):
        print("---- DRY RUN ----\n" + text + "\n-----------------")
        return True
    try:
        r = requests.post(
            f"https://api.telegram.org/bot{token}/sendMessage",
            json={
                "chat_id": chat_id,
                "text": text,
                "parse_mode": "HTML",
                "disable_web_page_preview": True,
            },
            timeout=HTTP_TIMEOUT,
        )
        if r.status_code != 200:
            # בכוונה לא מדפיסים את ה-URL (מכיל את הטוקן)
            log(f"[telegram] שגיאה {r.status_code}: {r.text[:300]}")
            return False
        return True
    except requests.RequestException as e:
        log(f"[telegram] שגיאת רשת: {type(e).__name__}")
        return False


def chunked(alerts, limit=3600):
    cur, size = [], 0
    for a in alerts:
        n = len(a[1]) + 2
        if cur and size + n > limit:
            yield cur
            cur, size = [], 0
        cur.append(a)
        size += n
    if cur:
        yield cur


# ------------------------------------------------------------
# main
# ------------------------------------------------------------
def main():
    token = os.environ.get("TELEGRAM_TOKEN", "").strip()
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "").strip()
    if not os.environ.get("DRY_RUN") and (not token or not chat_id):
        log("חסרים TELEGRAM_TOKEN / TELEGRAM_CHAT_ID")
        return 1

    state = prune_state(load_state())
    collected = []

    for sym in WATCHLIST:
        try:
            collected += analyze_symbol(sym, state)
        except Exception as e:  # noqa: BLE001
            log(f"[ticker] {sym}: {e}")

    news = []
    for name, url in NEWS_FEEDS.items():
        try:
            news += analyze_feed(name, url)
        except Exception as e:  # noqa: BLE001
            log(f"[feed] {name}: {e}")

    # סינון כפילויות (מול state ובתוך ההרצה)
    seen, alerts = set(), []
    for key, text, ttl in collected:
        if key not in state and key not in seen:
            seen.add(key)
            alerts.append((key, text, ttl))
    news_alerts = []
    for key, text, ttl in news:
        if key not in state and key not in seen:
            seen.add(key)
            news_alerts.append((key, text, ttl))
    alerts += news_alerts[:NEWS_MAX_PER_RUN]

    log(f"נמצאו {len(alerts)} התראות חדשות")

    stamp = datetime.now(TZ).strftime("%d.%m %H:%M")
    for group in chunked(alerts):
        body = f"📊 <b>התראות בורסה</b> — {stamp}\n\n" + "\n\n".join(a[1] for a in group)
        if send_telegram(rtl(body), token, chat_id):
            for key, _, ttl in group:
                mark(state, key, ttl)   # מסמנים רק אחרי שליחה מוצלחת
        time.sleep(0.5)

    save_state(prune_state(state))
    return 0


if __name__ == "__main__":
    sys.exit(main())
