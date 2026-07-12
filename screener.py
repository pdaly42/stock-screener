#!/usr/bin/env python3
"""
screener.py  --  stock screener: Piotroski F-Score + Greenblatt Magic Formula

WHAT THIS IS
------------
Pulls annual financial statements for a list of tickers straight from SEC
EDGAR's XBRL data (the same filings companies submit with their 10-Ks),
caches them locally so re-runs are free, computes each company's Piotroski
F-Score (a fully mechanical, 9-point quality signal) AND its Greenblatt
Magic Formula rank (cheapness + quality via Return on Capital and Earnings
Yield, which needs a current stock price on top of the XBRL fundamentals),
and writes a ranked results.json that a webpage front end can read later.

WHY PIOTROSKI FIRST
-------------------
It's deterministic (no judgment calls), and computing it forces you to touch
all three financial statements -- income, balance sheet, cash flow -- which
is the exact plumbing every other model reuses.

WHY MAGIC FORMULA SECOND
-------------------------
Same XBRL plumbing plus one new ingredient: price (for market cap / EV), the
first non-fundamental data this project needs. Ranks every qualifying name
by combining Return on Capital (EBIT / (net working capital + net fixed
assets)) and Earnings Yield (EBIT / enterprise value); low combined rank =
best. Simplifications vs. Greenblatt's original: net working capital is
current_assets - current_liab (he nets out excess cash and non-interest-
bearing current liabilities); shares outstanding is the diluted weighted
average from the income statement, not a period-end share count, so market
cap is an approximation. Financials and Utilities are excluded when a
sector map is available (sp500_sectors.json from fetch_sp500.py) since
Greenblatt excludes them too -- their balance sheets don't map cleanly onto
"invested capital".

WHY SEC EDGAR (not a paid data vendor)
---------------------------------------
No API key, no signup, no daily call cap, and no paywalled tickers -- every
US public filer's data is here because it's the primary source companies
report to. The tradeoff: companies don't all use the same XBRL tag for the
same line item (e.g. revenue might be tagged "Revenues" or
"RevenueFromContractWithCustomerExcludingAssessedTax" depending on the
company and filing year), so field lookups try a list of candidate tags
per line item. Run with --inspect TICKER to see which tag matched and what
values it found.

SEC's only real requirement: identify yourself in the User-Agent header
(SEC_CONTACT below) and don't hammer the API. This script paces itself
well under their informal ~10 requests/second guidance.

PRICE DATA
----------
SEC EDGAR has no price data (it's a fundamentals-only filing archive), so
Magic Formula's price input comes from Yahoo Finance's unauthenticated
chart endpoint (no key needed, same one yahoo finance's own charts call).
Cached separately with a 1-day TTL since price is time-sensitive, unlike
fundamentals which barely move week to week.

RUN
---
   python3 screener.py --self-test          # no network needed; checks the math
   python3 screener.py                       # screens the default universe
   python3 screener.py --tickers my.txt      # one ticker per line
   python3 screener.py --min-score 7         # only print names scoring 7+ on F-Score
   python3 screener.py --refresh             # ignore cache, re-fetch everything
   python3 screener.py --inspect AAPL        # show which XBRL tags matched for one ticker

No third-party packages required -- this runs on stock Python 3.
"""

import argparse
import json
import os
import sqlite3
import sys
import time
import urllib.error
import urllib.request
from datetime import date, datetime, timezone

# ----------------------------------------------------------------------------
# CONFIG
# ----------------------------------------------------------------------------

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CACHE_DB = os.path.join(SCRIPT_DIR, "screener_cache.db")       # created next to this file
RESULTS_JSON = os.path.join(SCRIPT_DIR, "results.json")        # what the webpage will read
TICKER_MAP_CACHE = os.path.join(SCRIPT_DIR, "sec_ticker_map.json")
CACHE_TTL_DAYS = 7            # re-fetch a company's facts if cache older than this
PRICE_CACHE_TTL_DAYS = 1      # prices are time-sensitive; refresh daily
TICKER_MAP_TTL_DAYS = 30      # the ticker->CIK map barely changes; refetch monthly
MIN_YEARS_REQUIRED = 3        # F-Score needs 3 years of data
STALE_DATA_MAX_AGE_DAYS = 730 # skip rather than silently score off a multi-year-old 10-K
REQUEST_PAUSE_SEC = 0.15      # stay comfortably under SEC's ~10 req/sec guidance
MAX_RETRIES = 3               # retry on 429 / transient errors

SEC_CONTACT = "pdaly42@gmail.com"   # SEC requires a contact-identifying User-Agent
SEC_USER_AGENT = f"PersonalStockScreener/1.0 ({SEC_CONTACT})"
SEC_TICKER_MAP_URL = "https://www.sec.gov/files/company_tickers.json"
SEC_FACTS_URL_TMPL = "https://data.sec.gov/api/xbrl/companyfacts/CIK{cik:010d}.json"

# Yahoo's unauthenticated chart endpoint -- no key/crumb needed, unlike its
# newer quote/quoteSummary endpoints which now require an auth token.
YAHOO_USER_AGENT = f"Mozilla/5.0 (compatible; PersonalStockScreener/1.0; +{SEC_CONTACT})"
YAHOO_CHART_URL_TMPL = "https://query1.finance.yahoo.com/v8/finance/chart/{symbol}?interval=1d&range=1d"

# Optional ticker->GICS sector map from fetch_sp500.py. Magic Formula uses
# this to exclude Financials/Utilities (see module docstring); screening a
# custom list without this file just means that exclusion doesn't apply.
SECTOR_MAP_CACHE = os.path.join(SCRIPT_DIR, "sp500_sectors.json")
MAGIC_FORMULA_EXCLUDED_SECTORS = {"Financials", "Utilities"}

# A small starter universe; swap in the full S&P 500 whenever you like --
# there's no daily call budget to ration against with SEC EDGAR.
DEFAULT_UNIVERSE = [
    "AAPL", "MSFT", "GOOG", "NVDA", "AMZN", "META", "V", "PG", "WMT",
    "HD", "JNJ", "KO", "PEP", "CRM", "ADBE", "COST", "MCD", "CAT",
    "TXN", "QCOM", "LMT", "UNH", "LIN", "NKE", "SBUX",
]

# ----------------------------------------------------------------------------
# XBRL FIELD MAP
# ----------------------------------------------------------------------------
# Each line item: (candidate tag names in priority order, unit, is_instant).
# "Instant" facts (balance sheet items) are a snapshot at a date ("end" only).
# "Duration" facts (income/cash flow items) cover a period ("start" to "end"),
# so we filter to ~365-day spans to get annual figures and skip quarterly ones.

XBRL_FIELD_SPECS = {
    "revenue": ([
        "RevenueFromContractWithCustomerExcludingAssessedTax",
        "RevenueFromContractWithCustomerIncludingAssessedTax",
        "Revenues",
        "SalesRevenueNet",
        "SalesRevenueGoodsNet",
    ], "USD", False),
    "gross_profit": (["GrossProfit"], "USD", False),
    # Not every filer tags GrossProfit (many present no gross-profit subtotal
    # at all) -- cost_of_revenue is a fallback used to derive it below.
    "cost_of_revenue": ([
        "CostOfRevenue",
        "CostOfGoodsAndServicesSold",
        "CostOfServices",
        "CostOfGoodsSold",
    ], "USD", False),
    "net_income": (["NetIncomeLoss", "ProfitLoss"], "USD", False),
    "shares": ([
        "WeightedAverageNumberOfDilutedSharesOutstanding",
        "WeightedAverageNumberOfSharesOutstandingBasic",
    ], "shares", False),
    "total_assets": (["Assets"], "USD", True),
    "current_assets": (["AssetsCurrent"], "USD", True),
    "current_liab": (["LiabilitiesCurrent"], "USD", True),
    "long_term_debt": ([
        "LongTermDebtNoncurrent",
        "LongTermDebt",
        "LongTermDebtAndCapitalLeaseObligations",
    ], "USD", True),
    "op_cash_flow": ([
        "NetCashProvidedByUsedInOperatingActivities",
        "NetCashProvidedByUsedInOperatingActivitiesContinuingOperations",
    ], "USD", False),
    # -- Magic Formula only, below --
    "ebit": (["OperatingIncomeLoss"], "USD", False),
    "ppe_net": (["PropertyPlantAndEquipmentNet"], "USD", True),
    "cash": ([
        "CashAndCashEquivalentsAtCarryingValue",
        "CashCashEquivalentsRestrictedCashAndRestrictedCashEquivalents",
        "Cash",
    ], "USD", True),
    "current_debt": ([
        "LongTermDebtCurrent",
        "DebtCurrent",
        "ShortTermBorrowings",
        "NotesPayableCurrent",
    ], "USD", True),
}

# Fields that must be present for every year we score; long_term_debt is
# excluded on purpose -- a missing tag there just means "no long-term debt".
REQUIRED_FIELDS = [
    "revenue", "gross_profit", "net_income", "shares",
    "total_assets", "current_assets", "current_liab", "op_cash_flow",
]

# Magic Formula fields, and the subset that must be present (long_term_debt
# and current_debt default to 0 -- "no debt of that kind" -- if untagged).
MAGIC_FORMULA_FIELDS = [
    "ebit", "current_assets", "current_liab", "long_term_debt",
    "current_debt", "cash", "ppe_net", "shares",
]
MAGIC_FORMULA_REQUIRED = [
    "ebit", "current_assets", "current_liab", "cash", "ppe_net", "shares",
]

# Some filers' "shares" XBRL tag is reported pre-scaled to millions instead
# of a raw share count -- e.g. MCD's own 10-Ks did this for FY2021+ data
# once restated in 2024 filings (716.4 instead of 716,400,000), a real
# filer-side tagging error, not a parsing bug here. No genuine S&P 500
# constituent has a diluted share count this low, so treat it as corrupted
# and skip Magic Formula for that ticker rather than compute a garbage
# market cap.
MIN_PLAUSIBLE_SHARES = 1_000_000

# ----------------------------------------------------------------------------
# CACHE LAYER (SQLite for per-company facts; a flat file for the ticker map)
# ----------------------------------------------------------------------------

def init_db():
    conn = sqlite3.connect(CACHE_DB)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS statements (
            symbol      TEXT,
            statement   TEXT,
            payload     TEXT,       -- raw JSON, as returned by the source
            fetched_at  REAL,       -- unix timestamp
            PRIMARY KEY (symbol, statement)
        )
    """)
    conn.commit()
    return conn

def cache_get(conn, symbol, statement, ttl_days=CACHE_TTL_DAYS):
    row = conn.execute(
        "SELECT payload, fetched_at FROM statements WHERE symbol=? AND statement=?",
        (symbol, statement),
    ).fetchone()
    if not row:
        return None
    payload, fetched_at = row
    age_days = (time.time() - fetched_at) / 86400.0
    if age_days > ttl_days:
        return None                       # stale -> force a re-fetch
    return json.loads(payload)

def cache_set(conn, symbol, statement, payload):
    conn.execute(
        "REPLACE INTO statements (symbol, statement, payload, fetched_at) "
        "VALUES (?, ?, ?, ?)",
        (symbol, statement, json.dumps(payload), time.time()),
    )
    conn.commit()

def resolve_cik(cik_map, symbol):
    """Look up a ticker's CIK, falling back to dash notation for share
    classes -- sources disagree on "BRK.B" vs SEC's own "BRK-B"."""
    return cik_map.get(symbol) or cik_map.get(symbol.replace(".", "-"))

def load_ticker_cik_map(refresh=False):
    """Ticker -> CIK, from SEC's master list. Cached to a flat file since
    it's one big shared blob, not per-symbol."""
    if not refresh and os.path.exists(TICKER_MAP_CACHE):
        age_days = (time.time() - os.path.getmtime(TICKER_MAP_CACHE)) / 86400.0
        if age_days <= TICKER_MAP_TTL_DAYS:
            with open(TICKER_MAP_CACHE) as f:
                return json.load(f)

    req = urllib.request.Request(SEC_TICKER_MAP_URL, headers={"User-Agent": SEC_USER_AGENT})
    with urllib.request.urlopen(req, timeout=30) as resp:
        raw = json.loads(resp.read().decode("utf-8"))
    mapping = {v["ticker"].upper(): v["cik_str"] for v in raw.values()}

    with open(TICKER_MAP_CACHE, "w") as f:
        json.dump(mapping, f)
    return mapping

def load_sector_map():
    """Optional ticker -> GICS sector map (see SECTOR_MAP_CACHE above).
    Empty dict (no Magic Formula sector exclusions) if it doesn't exist."""
    if not os.path.exists(SECTOR_MAP_CACHE):
        return {}
    with open(SECTOR_MAP_CACHE) as f:
        return json.load(f)

# ----------------------------------------------------------------------------
# FETCH LAYER
# ----------------------------------------------------------------------------

class FetchError(Exception):
    pass

# SEC's companyfacts blob includes every XBRL concept a filer has ever used --
# hundreds of tags, years of quarterly data, several MB per company. We only
# ever look at the handful of tags in XBRL_FIELD_SPECS, so trim to those
# before caching (a full S&P 500 cache would otherwise run into gigabytes).
_ALL_CANDIDATE_TAGS = sorted({
    tag for candidates, _, _ in XBRL_FIELD_SPECS.values() for tag in candidates
})

def _trim_facts(raw):
    gaap = raw.get("facts", {}).get("us-gaap", {})
    trimmed_gaap = {tag: gaap[tag] for tag in _ALL_CANDIDATE_TAGS if tag in gaap}
    return {
        "cik": raw.get("cik"),
        "entityName": raw.get("entityName"),
        "facts": {"us-gaap": trimmed_gaap},
    }

def fetch_company_facts(conn, symbol, cik, refresh=False):
    """Return SEC's full XBRL company-facts blob for one company (1 call
    covers every line item, unlike statement-by-statement vendor APIs)."""
    if not refresh:
        cached = cache_get(conn, symbol, "secfacts")
        if cached is not None:
            return cached

    url = SEC_FACTS_URL_TMPL.format(cik=cik)
    req = urllib.request.Request(url, headers={"User-Agent": SEC_USER_AGENT})

    last_err = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            break
        except urllib.error.HTTPError as e:
            if e.code == 404:
                raise FetchError(f"no SEC XBRL data for {symbol} (CIK {cik})") from e
            if e.code == 429 and attempt < MAX_RETRIES:
                time.sleep(2 * attempt)
                last_err = e
                continue
            raise FetchError(f"HTTP {e.code} fetching SEC facts for {symbol}") from e
        except OSError as e:
            # Covers urllib.error.URLError (connection failures) and raw
            # socket.timeout, which can surface uncaught mid-response-read
            # without being wrapped in URLError.
            if attempt < MAX_RETRIES:
                time.sleep(2 * attempt)
                last_err = e
                continue
            raise FetchError(f"network error for {symbol}: {e}") from e
    else:
        raise FetchError(f"gave up on {symbol} after {MAX_RETRIES} tries: {last_err}")

    data = _trim_facts(data)
    cache_set(conn, symbol, "secfacts", data)
    time.sleep(REQUEST_PAUSE_SEC)
    return data

def fetch_price(conn, symbol, refresh=False):
    """Latest close/regular-market price for one ticker, via Yahoo's
    unauthenticated chart endpoint. Magic Formula's only non-SEC input."""
    if not refresh:
        cached = cache_get(conn, symbol, "price", ttl_days=PRICE_CACHE_TTL_DAYS)
        if cached is not None:
            return cached["price"]

    url = YAHOO_CHART_URL_TMPL.format(symbol=symbol)
    req = urllib.request.Request(url, headers={"User-Agent": YAHOO_USER_AGENT})

    last_err = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            with urllib.request.urlopen(req, timeout=15) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            break
        except urllib.error.HTTPError as e:
            if e.code == 404:
                raise FetchError(f"no Yahoo Finance data for {symbol}") from e
            if e.code == 429 and attempt < MAX_RETRIES:
                time.sleep(2 * attempt)
                last_err = e
                continue
            raise FetchError(f"HTTP {e.code} fetching price for {symbol}") from e
        except OSError as e:
            if attempt < MAX_RETRIES:
                time.sleep(2 * attempt)
                last_err = e
                continue
            raise FetchError(f"network error fetching price for {symbol}: {e}") from e
    else:
        raise FetchError(f"gave up on price for {symbol} after {MAX_RETRIES} tries: {last_err}")

    result = data.get("chart", {}).get("result")
    if not result:
        err = data.get("chart", {}).get("error") or {}
        raise FetchError(f"no price data for {symbol}: {err.get('description', 'unknown')}")

    price = result[0].get("meta", {}).get("regularMarketPrice")
    if price is None:
        raise FetchError(f"no regularMarketPrice for {symbol}")

    cache_set(conn, symbol, "price", {"price": price})
    time.sleep(REQUEST_PAUSE_SEC)
    return price

# ----------------------------------------------------------------------------
# NORMALIZE
# ----------------------------------------------------------------------------
# Pull each line item's annual time series out of the raw XBRL facts blob,
# then intersect by fiscal-year-end date so the scoring function gets a
# clean per-year dict without ever knowing an XBRL tag name existed.

def extract_field(gaap, candidates, unit_key, instant):
    """Merge every candidate tag's annual (10-K) data into one {end_date:
    value} series. Companies sometimes switch which XBRL tag they use for
    the same line item mid-history (e.g. LMT tagged revenue as
    RevenueFromContractWithCustomerExcludingAssessedTax through 2019, then
    switched to plain Revenues from 2020 on) -- stopping at the first
    non-empty candidate would silently drop the years under the other tag.
    Where two tags both cover the same date, the earlier-listed (preferred)
    candidate wins.

    Returns (list_of_tags_that_contributed_data, {end_date: value})."""
    matched_tags = []
    combined = {}   # end_date -> (candidate_rank, filed_date, value)

    for rank, tag in enumerate(candidates):
        node = gaap.get(tag)
        if not node:
            continue
        entries = node.get("units", {}).get(unit_key)
        if not entries:
            continue

        found_any = False
        for e in entries:
            if e.get("form") != "10-K":
                continue
            end = e.get("end")
            if not end:
                continue
            if not instant:
                start = e.get("start")
                if not start:
                    continue
                try:
                    span_days = (date.fromisoformat(end) - date.fromisoformat(start)).days
                except ValueError:
                    continue
                if not (350 <= span_days <= 380):   # keep annual spans, drop quarterly ones
                    continue
            found_any = True
            filed = e.get("filed", "")
            prev = combined.get(end)
            if prev is None or rank < prev[0] or (rank == prev[0] and filed >= prev[1]):
                combined[end] = (rank, filed, e["val"])
        if found_any:
            matched_tags.append(tag)

    return matched_tags, {end: v for end, (_, _, v) in combined.items()}

def normalize_from_facts(facts):
    """Return a list of yearly dicts, newest first, for every fiscal-year-end
    date where all REQUIRED_FIELDS have a value."""
    gaap = facts.get("facts", {}).get("us-gaap", {})

    series = {}
    for field, (candidates, unit_key, instant) in XBRL_FIELD_SPECS.items():
        _, values = extract_field(gaap, candidates, unit_key, instant)
        series[field] = values

    # Fill any year missing a direct GrossProfit tag with revenue - cost_of_revenue.
    # Some filers (AMZN, COST) tag GrossProfit for only a handful of stray years,
    # so this must patch gaps rather than only apply when GrossProfit is empty.
    derived_gp = {
        d: series["revenue"][d] - series["cost_of_revenue"][d]
        for d in series["revenue"]
        if d in series["cost_of_revenue"] and d not in series["gross_profit"]
    }
    series["gross_profit"] = {**derived_gp, **series["gross_profit"]}

    if any(not series[f] for f in REQUIRED_FIELDS):
        return []

    common_dates = set(series[REQUIRED_FIELDS[0]])
    for f in REQUIRED_FIELDS[1:]:
        common_dates &= set(series[f])
    common_dates = sorted(common_dates, reverse=True)

    years = []
    for d in common_dates:
        years.append({
            "date":           d,
            "revenue":        series["revenue"][d],
            "gross_profit":   series["gross_profit"][d],
            "net_income":     series["net_income"][d],
            "shares":         series["shares"][d],
            "total_assets":   series["total_assets"][d],
            "current_assets": series["current_assets"][d],
            "current_liab":   series["current_liab"][d],
            "long_term_debt": series["long_term_debt"].get(d, 0),   # 0 is a valid "no LT debt"
            "op_cash_flow":   series["op_cash_flow"][d],
        })
    return years

def normalize_for_magic_formula(facts):
    """Return the single most recent fiscal-year dict with everything Magic
    Formula needs, or None. Unlike F-Score this only looks at the latest
    year -- Magic Formula is a point-in-time cheapness/quality ranking, not
    a multi-year trend, so there's no 3-year requirement here."""
    gaap = facts.get("facts", {}).get("us-gaap", {})

    series = {}
    for field in MAGIC_FORMULA_FIELDS:
        candidates, unit_key, instant = XBRL_FIELD_SPECS[field]
        _, values = extract_field(gaap, candidates, unit_key, instant)
        series[field] = values

    if any(not series[f] for f in MAGIC_FORMULA_REQUIRED):
        return None

    common_dates = set(series[MAGIC_FORMULA_REQUIRED[0]])
    for f in MAGIC_FORMULA_REQUIRED[1:]:
        common_dates &= set(series[f])
    if not common_dates:
        return None
    d = max(common_dates)

    try:
        age_days = (date.today() - date.fromisoformat(d)).days
    except ValueError:
        age_days = None
    if age_days is not None and age_days > STALE_DATA_MAX_AGE_DAYS:
        return None

    if series["shares"][d] < MIN_PLAUSIBLE_SHARES:
        return None

    return {
        "date":            d,
        "ebit":            series["ebit"][d],
        "current_assets":  series["current_assets"][d],
        "current_liab":    series["current_liab"][d],
        "long_term_debt":  series["long_term_debt"].get(d, 0),
        "current_debt":    series["current_debt"].get(d, 0),
        "cash":            series["cash"][d],
        "ppe_net":         series["ppe_net"][d],
        "shares":          series["shares"][d],
    }

# ----------------------------------------------------------------------------
# THE MODEL: Piotroski F-Score  (pure function -- no network, easy to test)
# ----------------------------------------------------------------------------
# 9 binary signals across three groups. Score is their sum (0-9). 8-9 is
# strong, 0-2 is weak. All "change" signals compare the most recent year (y0)
# to the prior year (y1). ROA and asset turnover are scaled by BEGINNING-of-
# year assets (i.e. the prior year's ending assets), per Piotroski (2000),
# which is why we need a third year (y2) to compute y1's ratios.
#
# Simplifications (fine for a screen; noted so you know what you're looking at):
#   - Leverage ratio uses each year's own ending assets, not a 2-year average.
#   - Uses reported net income rather than income-before-extraordinary-items.

def _safe_div(a, b):
    if a is None or b in (None, 0):
        return None
    return a / b

def compute_fscore(years):
    """`years` = list of normalized yearly dicts, newest first (needs >= 3).
    Returns (score, signals_dict, metrics_dict) or (None, reason, {})."""
    if len(years) < MIN_YEARS_REQUIRED:
        return None, "insufficient_years", {}

    y0, y1, y2 = years[0], years[1], years[2]

    # Some filers stop tagging a field we need (e.g. gross margin) years
    # before their most recent 10-K, so the newest *fully scoreable* year
    # can be much older than their newest filing. Better to skip than to
    # report a stale score sitting next to names scored off 2025 data.
    try:
        asof_age_days = (date.today() - date.fromisoformat(y0["date"])).days
    except ValueError:
        asof_age_days = None
    if asof_age_days is not None and asof_age_days > STALE_DATA_MAX_AGE_DAYS:
        return None, "stale_data", {}

    # Ratios we reuse. `roa` and `turnover` use beginning-of-year assets.
    roa0 = _safe_div(y0["net_income"], y1["total_assets"])
    roa1 = _safe_div(y1["net_income"], y2["total_assets"])
    turn0 = _safe_div(y0["revenue"], y1["total_assets"])
    turn1 = _safe_div(y1["revenue"], y2["total_assets"])
    cr0 = _safe_div(y0["current_assets"], y0["current_liab"])
    cr1 = _safe_div(y1["current_assets"], y1["current_liab"])
    gm0 = _safe_div(y0["gross_profit"], y0["revenue"])
    gm1 = _safe_div(y1["gross_profit"], y1["revenue"])
    lev0 = _safe_div(y0["long_term_debt"], y0["total_assets"])
    lev1 = _safe_div(y1["long_term_debt"], y1["total_assets"])

    # Any missing input needed below means we can't score this name honestly.
    required = [y0["net_income"], y0["op_cash_flow"], roa0, roa1,
                turn0, turn1, cr0, cr1, gm0, gm1, lev0, lev1,
                y0["shares"], y1["shares"]]
    if any(v is None for v in required):
        return None, "missing_fields", {}

    s = {}
    # -- Profitability (4) --
    s["positive_net_income"]   = int(y0["net_income"] > 0)
    s["positive_op_cash_flow"] = int(y0["op_cash_flow"] > 0)
    s["roa_improving"]         = int(roa0 > roa1)
    s["accruals_ok"]           = int(y0["op_cash_flow"] > y0["net_income"])  # cash-backed earnings
    # -- Leverage / Liquidity / Funding (3) --
    s["lower_leverage"]        = int(lev0 < lev1)
    s["higher_current_ratio"]  = int(cr0 > cr1)
    s["no_new_shares"]         = int(y0["shares"] <= y1["shares"] * 1.001)   # tiny tolerance
    # -- Operating efficiency (2) --
    s["higher_gross_margin"]   = int(gm0 > gm1)
    s["higher_asset_turnover"] = int(turn0 > turn1)

    score = sum(s.values())
    metrics = {
        "asof": y0["date"],
        "roa": round(roa0, 4), "roa_prior": round(roa1, 4),
        "current_ratio": round(cr0, 3), "gross_margin": round(gm0, 4),
        "leverage_ratio": round(lev0, 4), "asset_turnover": round(turn0, 3),
    }
    return score, s, metrics

# ----------------------------------------------------------------------------
# THE MODEL: Greenblatt Magic Formula  (pure function -- no network, easy to test)
# ----------------------------------------------------------------------------
# Ranks by combining two things: Return on Capital (quality -- how much
# operating profit a company squeezes out of the capital tied up in the
# business) and Earnings Yield (cheapness -- how much operating profit
# you're buying per dollar of enterprise value). Low combined rank = best.
# Ranking against the rest of the universe happens in screen(), after every
# ticker's raw ROC/EY are known -- this function only computes one company's
# raw inputs.

def compute_magic_formula_raw(year, price):
    """`year` = normalize_for_magic_formula() output; `price` = current
    share price. Returns (metrics_dict, None) or (None, reason)."""
    invested_capital = (year["current_assets"] - year["current_liab"]) + year["ppe_net"]
    if invested_capital <= 0:
        return None, "invalid_invested_capital"
    roc = year["ebit"] / invested_capital

    total_debt = year["long_term_debt"] + year["current_debt"]
    market_cap = year["shares"] * price
    enterprise_value = market_cap + total_debt - year["cash"]
    if enterprise_value <= 0:
        return None, "invalid_enterprise_value"
    earnings_yield = year["ebit"] / enterprise_value

    return {
        "asof": year["date"],
        "roc": round(roc, 4),
        "earnings_yield": round(earnings_yield, 4),
        "ebit": year["ebit"],
        "price": price,
        "market_cap": round(market_cap),
        "enterprise_value": round(enterprise_value),
    }, None

# ----------------------------------------------------------------------------
# RUNNER
# ----------------------------------------------------------------------------

def screen(tickers, refresh=False):
    conn = init_db()
    cik_map = load_ticker_cik_map(refresh=refresh)
    sector_map = load_sector_map()
    results, errors = [], []

    for i, symbol in enumerate(tickers, 1):
        symbol = symbol.strip().upper()
        if not symbol:
            continue

        cik = resolve_cik(cik_map, symbol)
        if cik is None:
            errors.append((symbol, "no_cik_found"))
            print(f"  [{i}/{len(tickers)}] {symbol:6s}  SKIP  (no CIK found in SEC ticker map)")
            continue

        try:
            facts = fetch_company_facts(conn, symbol, cik, refresh)
        except FetchError as e:
            errors.append((symbol, str(e)))
            print(f"  [{i}/{len(tickers)}] {symbol:6s}  SKIP  ({e})")
            continue

        sector = sector_map.get(symbol)

        years = normalize_from_facts(facts)
        fscore, f_signals, f_metrics = compute_fscore(years)
        if fscore is None:
            f_signals, f_metrics = None, None

        mf_metrics = None
        if sector not in MAGIC_FORMULA_EXCLUDED_SECTORS:
            mf_year = normalize_for_magic_formula(facts)
            if mf_year is not None:
                try:
                    price = fetch_price(conn, symbol, refresh)
                except FetchError:
                    price = None
                if price is not None:
                    mf_metrics, _ = compute_magic_formula_raw(mf_year, price)

        if fscore is None and mf_metrics is None:
            reason = f_signals if isinstance(f_signals, str) else "unscoreable"
            errors.append((symbol, reason))
            print(f"  [{i}/{len(tickers)}] {symbol:6s}  n/a   ({reason})")
            continue

        results.append({
            "symbol": symbol,
            "sector": sector,
            "fscore": fscore,
            "f_signals": f_signals,
            "f_metrics": f_metrics,
            "mf_metrics": mf_metrics,
        })
        fscore_disp = f"F={fscore}/9" if fscore is not None else "F=n/a"
        mf_disp = (f"ROC={mf_metrics['roc']:.1%} EY={mf_metrics['earnings_yield']:.1%}"
                   if mf_metrics else "MF=n/a")
        print(f"  [{i}/{len(tickers)}] {symbol:6s}  {fscore_disp}   {mf_disp}")

    # Magic Formula rank is relative to the rest of the scored universe, so
    # it's computed here, after every ticker's raw ROC/EY are in hand.
    mf_rows = [r for r in results if r["mf_metrics"] is not None]
    ey_rank = {r["symbol"]: i for i, r in enumerate(
        sorted(mf_rows, key=lambda r: r["mf_metrics"]["earnings_yield"], reverse=True), 1)}
    roc_rank = {r["symbol"]: i for i, r in enumerate(
        sorted(mf_rows, key=lambda r: r["mf_metrics"]["roc"], reverse=True), 1)}
    for r in mf_rows:
        r["mf_metrics"]["ey_rank"] = ey_rank[r["symbol"]]
        r["mf_metrics"]["roc_rank"] = roc_rank[r["symbol"]]
    mf_rows.sort(key=lambda r: (ey_rank[r["symbol"]] + roc_rank[r["symbol"]], r["symbol"]))
    for rank, r in enumerate(mf_rows, 1):
        r["mf_metrics"]["magic_rank"] = rank

    results.sort(key=lambda r: (-(r["fscore"] if r["fscore"] is not None else -1), r["symbol"]))

    out = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "models": ["piotroski_f_score", "magic_formula"],
        "data_source": "sec_edgar_xbrl + yahoo_finance_price",
        "universe_size": len(tickers),
        "scored": len(results),
        "scored_f_score": sum(1 for r in results if r["fscore"] is not None),
        "scored_magic_formula": len(mf_rows),
        "results": results,
    }
    with open(RESULTS_JSON, "w") as f:
        json.dump(out, f, indent=2)

    conn.close()
    return out, errors

# ----------------------------------------------------------------------------
# INSPECT  (debug helper: show which XBRL tag matched each field, and why)
# ----------------------------------------------------------------------------

def inspect_ticker(symbol):
    cik_map = load_ticker_cik_map()
    cik = resolve_cik(cik_map, symbol)
    if cik is None:
        print(f"{symbol}: no CIK found in SEC ticker map")
        return

    sector = load_sector_map().get(symbol)
    print(f"{symbol} -> CIK {cik}  (sector: {sector or 'unknown'})\n")

    conn = init_db()
    try:
        facts = fetch_company_facts(conn, symbol, cik, refresh=True)
    except FetchError as e:
        print(f"{symbol}: FETCH ERROR: {e}")
        return

    gaap = facts.get("facts", {}).get("us-gaap", {})
    for field, (candidates, unit_key, instant) in XBRL_FIELD_SPECS.items():
        tags, values = extract_field(gaap, candidates, unit_key, instant)
        if not tags:
            print(f"{field:16s}  NO MATCH among {candidates}")
            continue
        recent = sorted(values.items(), reverse=True)[:4]
        print(f"{field:16s}  tags={tags}")
        for d, v in recent:
            print(f"    {d}: {v:,}")

    print("\n-- Magic Formula --")
    mf_year = normalize_for_magic_formula(facts)
    if mf_year is None:
        print("insufficient fields for Magic Formula's latest year")
        conn.close()
        return
    try:
        price = fetch_price(conn, symbol, refresh=True)
    except FetchError as e:
        print(f"price fetch failed: {e}")
        conn.close()
        return
    metrics, reason = compute_magic_formula_raw(mf_year, price)
    conn.close()
    if metrics is None:
        print(f"unscoreable: {reason}")
    else:
        print(f"price={price}  {metrics}")

# ----------------------------------------------------------------------------
# SELF-TEST  (proves the scoring math -- no network, no XBRL parsing)
# ----------------------------------------------------------------------------

def self_test():
    """A hand-built 3-year company engineered to score a perfect 9, so every
    signal is exercised. If this passes, the scoring engine is wired correctly.
    Bypasses the SEC-parsing layer entirely -- compute_fscore only cares
    about the normalized shape, not where the numbers came from."""
    years = [
        {"date": "2025", "revenue": 1200, "gross_profit": 600, "net_income": 150,
         "shares": 100, "total_assets": 1000, "current_assets": 500,
         "current_liab": 200, "long_term_debt": 100, "op_cash_flow": 200},
        {"date": "2024", "revenue": 1000, "gross_profit": 450, "net_income": 100,
         "shares": 100, "total_assets": 900, "current_assets": 400,
         "current_liab": 200, "long_term_debt": 150, "op_cash_flow": 120},
        {"date": "2023", "revenue": 900, "gross_profit": 400, "net_income": 80,
         "shares": 100, "total_assets": 800, "current_assets": 350,
         "current_liab": 200, "long_term_debt": 200, "op_cash_flow": 90},
    ]

    score, signals, metrics = compute_fscore(years)

    print("Self-test scoring:")
    for name, val in signals.items():
        print(f"  {val}  {name}")
    print(f"  ----> total F-Score = {score}/9")
    print(f"  metrics: {metrics}")

    assert score == 9, f"expected 9, got {score}"
    assert all(v == 1 for v in signals.values()), "a signal did not fire as expected"
    print("\nPASS: all 9 signals fired and the total is 9. Scoring engine is correct.")
    return True

def self_test_magic_formula():
    """Hand-built inputs with a hand-computed ROC/EY, no network needed.
    invested_capital = (500-200) + 400 = 700 -> roc = 200/700 = 0.2857
    enterprise_value = 100*20 + 100 - 50 = 2050 -> ey = 200/2050 = 0.0976"""
    year = {
        "date": "2025", "ebit": 200, "current_assets": 500, "current_liab": 200,
        "long_term_debt": 100, "current_debt": 0, "cash": 50, "ppe_net": 400,
        "shares": 100,
    }
    metrics, reason = compute_magic_formula_raw(year, price=20.0)

    print("\nSelf-test Magic Formula:")
    print(f"  metrics: {metrics}")

    assert metrics is not None, f"expected valid metrics, got reason={reason}"
    assert abs(metrics["roc"] - 0.2857) < 0.001, f"ROC mismatch: {metrics['roc']}"
    assert abs(metrics["earnings_yield"] - 0.0976) < 0.001, f"EY mismatch: {metrics['earnings_yield']}"
    print("PASS: Magic Formula ROC/EY math is correct.")
    return True

# ----------------------------------------------------------------------------
# CLI
# ----------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description="Piotroski F-Score + Magic Formula screener -- SEC EDGAR backed")
    ap.add_argument("--tickers", help="file with one ticker per line")
    ap.add_argument("--min-score", type=int, default=0, help="only print names at/above this F-Score")
    ap.add_argument("--refresh", action="store_true", help="ignore cache; re-fetch from SEC")
    ap.add_argument("--self-test", action="store_true", help="verify scoring math (no network)")
    ap.add_argument("--inspect", metavar="TICKER", help="show matched XBRL tags for one ticker and exit")
    args = ap.parse_args()

    if args.self_test:
        self_test()
        self_test_magic_formula()
        return

    if args.inspect:
        inspect_ticker(args.inspect.strip().upper())
        return

    if args.tickers:
        with open(args.tickers) as f:
            tickers = [line for line in f if line.strip() and not line.startswith("#")]
    else:
        tickers = DEFAULT_UNIVERSE

    print(f"Screening {len(tickers)} tickers via SEC EDGAR (cache TTL {CACHE_TTL_DAYS}d)...\n")
    out, errors = screen(tickers, refresh=args.refresh)

    print(f"\n=== F-SCORE (>= {args.min_score}) ===")
    for r in out["results"]:
        if r["fscore"] is not None and r["fscore"] >= args.min_score:
            print(f"  {r['symbol']:6s}  F={r['fscore']}/9   (as of {r['f_metrics']['asof']})")

    print(f"\n=== MAGIC FORMULA (top 20) ===")
    mf_top = sorted(
        (r for r in out["results"] if r["mf_metrics"] is not None),
        key=lambda r: r["mf_metrics"]["magic_rank"],
    )[:20]
    for r in mf_top:
        m = r["mf_metrics"]
        print(f"  #{m['magic_rank']:<4d}{r['symbol']:6s}  ROC={m['roc']:.1%}  EY={m['earnings_yield']:.1%}"
              f"   (as of {m['asof']})")

    print(f"\nScored {out['scored']}/{out['universe_size']} "
          f"(F-Score: {out['scored_f_score']}, Magic Formula: {out['scored_magic_formula']}). "
          f"Wrote {RESULTS_JSON}. Skipped {len(errors)}.")

if __name__ == "__main__":
    main()
