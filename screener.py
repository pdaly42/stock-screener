#!/usr/bin/env python3
"""
screener.py  --  stock screener: Piotroski F-Score + Greenblatt Magic Formula
                  + Graham Defensive Investor + Peter Lynch's PEG Ratio

WHAT THIS IS
------------
Pulls annual financial statements for a list of tickers straight from SEC
EDGAR's XBRL data (the same filings companies submit with their 10-Ks),
caches them locally so re-runs are free, computes each company's Piotroski
F-Score (a fully mechanical, 9-point quality signal), Greenblatt Magic
Formula rank (cheapness + quality via Return on Capital and Earnings Yield),
Graham Defensive Investor score (Benjamin Graham's 7-point margin-of-safety
checklist from The Intelligent Investor), and Peter Lynch's PEG Ratio rank
(P/E relative to trailing EPS growth), then writes a ranked results.json
that a webpage front end can read later.

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

WHY GRAHAM DEFENSIVE INVESTOR THIRD
-------------------------------------
Ben Graham -- "the father of value investing", who co-wrote Security
Analysis (1934) and mentored Buffett directly -- laid out a 7-point
checklist for defensive investors in The Intelligent Investor (1973 ed.,
ch. 14): adequate size, a strong current ratio + low debt, a decade of
positive earnings, two decades of uninterrupted dividends, earnings growth,
a moderate P/E, and a moderate P/B (or the combined "Graham Number":
P/E x P/B <= 22.5). Graham's original 10-year/20-year lookback windows are
relaxed here (GRAHAM_EARNINGS_YEARS / GRAHAM_DIVIDEND_YEARS below) since SEC
XBRL data reliably covers roughly a decade for most filers -- a strict
20-year dividend check would disqualify almost the entire modern S&P 500
(recent IPOs, any tech name, anyone who ever cut a dividend decades ago).
This is a real, deliberate simplification, not an oversight -- it trades
Graham's literal thresholds for something the data can actually support
while keeping the spirit of each rule intact.

WHY LYNCH'S PEG RATIO FOURTH
------------------------------
Graham's checklist has a structural weakness: it uses absolute valuation
thresholds (P/E <= 15, Graham Number <= 22.5), so in a richly-valued market
the count of names passing can go to zero regardless of how the lookback
windows are tuned -- and in practice, across the S&P 500, it does. Peter
Lynch's PEG Ratio (P/E divided by trailing EPS growth, as a whole-number
percent) fixes this two ways: it needs a much shorter earnings history
(LYNCH_GROWTH_YEARS = 5, vs. Graham's 7) so more companies are even
eligible, and rather than a pass/fail bar, every qualifying company is
*ranked* by PEG (same mechanism as Magic Formula) so the site always
surfaces a full list. Lynch's own descriptive bands (PEG < 0.5 "excellent",
< 1.0 "attractive", < 1.5 "fair", else "expensive", from "One Up On Wall
Street") are shown for color but never used to filter anyone out.
Simplification: growth is a trailing 5-year EPS CAGR, since SEC data has no
forward analyst estimates -- Lynch himself worked from his own forward
growth estimates, which isn't something a mechanical screen can replicate.

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
from datetime import date, datetime, timedelta, timezone

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

# Graham's Defensive Investor checklist, relaxed lookback windows (see
# "WHY GRAHAM DEFENSIVE INVESTOR THIRD" above for why 10yr/20yr don't fit
# SEC XBRL's practical depth). Thresholds below are Graham's own numbers;
# only the lookback windows are shortened.
GRAHAM_EARNINGS_YEARS = 7        # relaxed from Graham's original 10
GRAHAM_DIVIDEND_YEARS = 5        # relaxed from Graham's original 20
GRAHAM_MIN_REVENUE = 250_000_000 # relaxed "adequate size" (Graham used ~$100M sales, 1970s dollars)
GRAHAM_MAX_PE = 15               # rule 6: price <= 15x average earnings (last 3 yrs)
GRAHAM_MAX_PB = 1.5              # rule 7: price <= 1.5x book value
GRAHAM_MAX_GRAHAM_NUMBER = 22.5  # Graham's own shortcut: PE x PB <= 22.5 satisfies rules 6+7 together
GRAHAM_MIN_EPS_GROWTH = 0.15     # relaxed from 33%/10yr given our shorter window

# Peter Lynch's PEG Ratio: P/E divided by the trailing EPS growth rate (as a
# whole number, e.g. 15 for 15% growth). Lynch's own rule of thumb from
# "One Up On Wall Street": PEG < 1 is attractive, < 0.5 is excellent. Unlike
# Graham, this isn't a hard pass/fail gate here -- every qualifying company
# gets *ranked* by PEG (ascending, lowest = best), same mechanism as Magic
# Formula, so the site always surfaces a full list instead of the whole
# universe scoring zero when the market is expensive. Growth is a trailing
# 5-year EPS CAGR (no analyst forward estimates available from SEC data),
# a meaningfully shorter/more available window than Graham's 7-10 years.
LYNCH_GROWTH_YEARS = 5
LYNCH_EXCELLENT_PEG = 0.5
LYNCH_ATTRACTIVE_PEG = 1.0
LYNCH_FAIR_PEG = 1.5

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
    "net_income": ([
        "NetIncomeLoss",
        "ProfitLoss",
        # Fallback: some filers (e.g. Booking Holdings) stop tagging plain
        # NetIncomeLoss in their 10-Ks at some point and only tag this
        # "available to common stockholders" variant going forward -- close
        # enough for a screen when a company has no preferred stock.
        "NetIncomeLossAvailableToCommonStockholdersBasic",
    ], "USD", False),
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
    "ppe_net": ([
        "PropertyPlantAndEquipmentNet",
        # Alphabet switched to this combined "PP&E + finance lease
        # right-of-use asset" concept starting its Q2 2025 10-Q -- a real,
        # deliberate ASC 842 accounting choice by the filer (not a tagging
        # error), but it means the plain PropertyPlantAndEquipmentNet tag
        # simply stops appearing in GOOG's facts from that quarter on.
        "PropertyPlantAndEquipmentAndFinanceLeaseRightOfUseAssetAfterAccumulatedDepreciationAndAmortization",
    ], "USD", True),
    # Fallback source for ppe_net: some filers (e.g. GE Vernova) tag gross
    # PP&E and accumulated depreciation separately instead of a combined
    # "net" figure. Not in MAGIC_FORMULA_REQUIRED itself -- derived below.
    "ppe_gross": ([
        "PropertyPlantAndEquipmentGross",
        "PropertyPlantAndEquipmentAndFinanceLeaseRightOfUseAssetBeforeAccumulatedDepreciationAndAmortization",
    ], "USD", True),
    "accum_depreciation": ([
        "AccumulatedDepreciationDepletionAndAmortizationPropertyPlantAndEquipment",
        "PropertyPlantAndEquipmentAndFinanceLeaseRightOfUseAssetAccumulatedDepreciationAndAmortization",
    ], "USD", True),
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
    # -- Graham Defensive Investor only, below --
    "dividends_paid": ([
        "PaymentsOfDividends",
        "PaymentsOfDividendsCommonStock",
        "PaymentsOfOrdinaryDividends",
    ], "USD", False),
    "stockholders_equity": ([
        "StockholdersEquity",
        "StockholdersEquityIncludingPortionAttributableToNoncontrollingInterest",
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
    "current_debt", "cash", "ppe_net", "ppe_gross", "accum_depreciation", "shares",
]
MAGIC_FORMULA_REQUIRED = [
    "ebit", "current_assets", "current_liab", "cash", "ppe_net", "shares",
]

# Graham fields, and the subset required every year in the earnings window.
# dividends_paid defaults to 0 (no dividend that year) if untagged, same
# convention as long_term_debt/current_debt elsewhere -- absence of a
# dividend payment tag legitimately means no dividend was paid.
GRAHAM_FIELDS = [
    "net_income", "shares", "revenue", "current_assets", "current_liab",
    "long_term_debt", "stockholders_equity", "dividends_paid",
]
GRAHAM_REQUIRED = [
    "net_income", "shares", "revenue", "current_assets", "current_liab",
    "stockholders_equity",
]

# Some filers' "shares" XBRL tag is reported pre-scaled to millions instead
# of a raw share count -- e.g. MCD's own 10-Ks did this for FY2021+ data
# once restated in 2024 filings (716.4 instead of 716,400,000), a real
# filer-side tagging error, not a parsing bug here. No genuine S&P 500
# constituent has a diluted share count this low, so treat it as corrupted
# and skip Magic Formula for that ticker rather than compute a garbage
# market cap.
MIN_PLAUSIBLE_SHARES = 1_000_000

# Trailing-twelve-month (TTM) reconstruction, used only by Magic Formula and
# Lynch PEG (see reconstruct_ttm() below for why F-Score and Graham stay
# annual-only): those two models each look at only one "current" data point
# rather than a multi-year trend, so refreshing that one point from the
# latest 10-Q -- rather than waiting for the next 10-K -- is a clean fit.
# TTM = last full fiscal year (10-K) + this year's year-to-date (10-Q)
#       - the same year-to-date stretch a year ago (10-Q).
TTM_PARTIAL_SPAN_MAX_DAYS = 349          # quarterly (~90d) up to 3-quarter YTD (~275d); 350+ is annual
TTM_PARTIAL_SPAN_TOLERANCE_DAYS = 20     # how closely this year's and last year's YTD spans must match
TTM_ANCHOR_SLACK_DAYS = 15               # slack when matching the anchor 10-K's end to the YTD window's start
TTM_STALE_MAX_AGE_DAYS = 150             # a "quarterly" figure over ~5 months old isn't quarterly-fresh anymore
# PP&E specifically: several large filers (HD, LIN, AMZN observed) only
# re-disclose the granular net/gross/accumulated-depreciation breakdown
# alongside their annual 10-K, not every 10-Q, even though every other
# balance-sheet line (current assets/liab, cash) updates quarterly for the
# same companies. Since PP&E moves slowly relative to earnings, using a
# same-name-but-a-quarter-or-two-old PP&E figure alongside fresh EBIT/
# current-assets/cash is still meaningfully more current than falling all
# the way back to a full fiscal-year-old snapshot -- a deliberate, narrow
# simplification, not a bug.
TTM_PPE_SLACK_DAYS = 200

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

def extract_field(gaap, candidates, unit_key, instant, forms=("10-K",)):
    """Merge every candidate tag's annual data into one {end_date: value}
    series. Companies sometimes switch which XBRL tag they use for the same
    line item mid-history (e.g. LMT tagged revenue as
    RevenueFromContractWithCustomerExcludingAssessedTax through 2019, then
    switched to plain Revenues from 2020 on) -- stopping at the first
    non-empty candidate would silently drop the years under the other tag.
    Where two tags both cover the same date, the earlier-listed (preferred)
    candidate wins.

    `forms` defaults to 10-K only (annual filings), matching every model
    except Magic Formula/Lynch's TTM path, which passes ("10-K", "10-Q") for
    *instant* (balance-sheet) fields so a fresher quarter-end snapshot can
    win over the last 10-K's. Duration fields still only keep ~365-day
    spans here regardless of `forms` -- 10-Qs rarely produce one by
    accident, and the handful that could (a 52/53-week fiscal calendar
    quirk) aren't worth the ambiguity; use extract_field_periods() instead
    when a duration field's quarterly/YTD spans are wanted on purpose.

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
            if e.get("form") not in forms:
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

def extract_field_periods(gaap, candidates, unit_key, forms=("10-K", "10-Q")):
    """Like extract_field(), but for duration facts headed into TTM
    reconstruction: returns *every* distinct (start, end) period found
    across the candidate tags, instead of collapsing to one value per
    end-date. That collapsing is exactly what breaks for this purpose -- a
    single 10-Q reports two overlapping periods ending on the same date
    (e.g. Q3's own 3-month figure and the Jan-Sep 9-month year-to-date
    figure both end September 30), and extract_field() keyed only on `end`
    would silently discard one of them. Same candidate-tag preference and
    filed-date tie-break as extract_field().

    Returns {(start_date, end_date): value}."""
    combined = {}   # (start, end) -> (candidate_rank, filed_date, value)
    for rank, tag in enumerate(candidates):
        node = gaap.get(tag)
        if not node:
            continue
        entries = node.get("units", {}).get(unit_key)
        if not entries:
            continue
        for e in entries:
            if e.get("form") not in forms:
                continue
            start, end = e.get("start"), e.get("end")
            if not start or not end:
                continue
            key = (start, end)
            filed = e.get("filed", "")
            prev = combined.get(key)
            if prev is None or rank < prev[0] or (rank == prev[0] and filed >= prev[1]):
                combined[key] = (rank, filed, e["val"])
    return {key: v for key, (_, _, v) in combined.items()}

def latest_period_value(periods):
    """From an extract_field_periods() dict, the value for whichever period
    ends most recently. Used for shares outstanding: we want the latest
    reported figure (a 10-Q's 3-month or year-to-date weighted average),
    not a TTM sum -- unlike income, a share count doesn't accumulate across
    periods, so "most recent" is the right reduction, not "add them up".

    Returns (value, end_date) or (None, None)."""
    if not periods:
        return None, None
    key = max(periods, key=lambda k: k[1])
    return periods[key], key[1]

def value_asof(series, target_date, max_slack_days=10):
    """From a {date: value} instant series (as returned by extract_field
    for an instant field), the value exactly at target_date, or the
    closest earlier date within max_slack_days if there's no exact match --
    covers the rare case where a filing's balance-sheet "as of" date and
    income-statement period-end date land a day or two apart."""
    if target_date in series:
        return series[target_date]
    try:
        target = date.fromisoformat(target_date)
    except ValueError:
        return None
    candidates = []
    for d, v in series.items():
        try:
            delta = (target - date.fromisoformat(d)).days
        except ValueError:
            continue
        if 0 <= delta <= max_slack_days:
            candidates.append((d, v))
    if not candidates:
        return None
    return max(candidates, key=lambda dv: dv[0])[1]

def _span_days(start, end):
    try:
        return (date.fromisoformat(end) - date.fromisoformat(start)).days
    except (ValueError, TypeError):
        return None

def reconstruct_ttm(periods):
    """`periods` = {(start,end): value} from extract_field_periods(), for
    one duration field (net_income or ebit). Reconstructs a trailing-
    twelve-month figure anchored on the most recently ended 10-Q period:

        TTM = last full fiscal year (10-K)
              + this year's year-to-date figure (10-Q)
              - the same year-to-date stretch a year ago (10-Q)

    This is the standard way to turn quarterly filings into a rolling
    annual figure without needing a single discrete quarter's number --
    10-Qs report cumulative year-to-date for Q2/Q3 (not a standalone
    quarter), so differencing two aligned YTD points is the robust
    approach rather than trying to isolate one quarter by subtraction
    within a single filing (which breaks the moment a company's own
    year-to-date tagging is inconsistent).

    Returns (value, asof_date, reason); reason is None on success and a
    human-readable explanation of what's missing otherwise."""
    if not periods:
        return None, None, "no data"

    annual, partial = {}, {}
    for (start, end), val in periods.items():
        span = _span_days(start, end)
        if span is None:
            continue
        if 350 <= span <= 380:
            annual[(start, end)] = val
        elif 0 < span <= TTM_PARTIAL_SPAN_MAX_DAYS:
            partial[(start, end)] = val

    if not partial:
        return None, None, "no 10-Q period found (no partial-year data)"

    latest_key = max(partial, key=lambda k: k[1])
    latest_start, latest_end = latest_key
    latest_val = partial[latest_key]
    latest_span = _span_days(latest_start, latest_end)

    age_days = (date.today() - date.fromisoformat(latest_end)).days
    if age_days > TTM_STALE_MAX_AGE_DAYS:
        return None, None, f"latest 10-Q period ({latest_end}) is more than {TTM_STALE_MAX_AGE_DAYS} days old"

    prior_candidates = []
    for (start, end), val in partial.items():
        if (start, end) == latest_key:
            continue
        span = _span_days(start, end)
        if span is None or abs(span - latest_span) > TTM_PARTIAL_SPAN_TOLERANCE_DAYS:
            continue
        gap_days = (date.fromisoformat(latest_end) - date.fromisoformat(end)).days
        if 340 <= gap_days <= 390:
            prior_candidates.append(((start, end), val, abs(gap_days - 365)))
    if not prior_candidates:
        return None, None, "no matching year-ago quarterly period to difference against"
    _, prior_val, _ = min(prior_candidates, key=lambda t: t[2])

    annual_candidates = []
    for (start, end), val in annual.items():
        gap_days = (date.fromisoformat(latest_start) - date.fromisoformat(end)).days
        if gap_days >= -TTM_ANCHOR_SLACK_DAYS:
            annual_candidates.append((val, end, gap_days))
    if not annual_candidates:
        return None, None, "no completed fiscal year (10-K) precedes the latest 10-Q period"
    annual_val, annual_end, anchor_gap = max(annual_candidates, key=lambda t: t[1])
    if anchor_gap > 400:
        return None, None, f"most recent 10-K ({annual_end}) is too far before the latest 10-Q period to anchor a TTM figure"

    ttm_value = annual_val + latest_val - prior_val
    return ttm_value, latest_end, None

def normalize_from_facts(facts):
    """Return (years, reason). `years` is a list of yearly dicts, newest
    first, for every fiscal-year-end date where all REQUIRED_FIELDS have a
    value; `reason` is None on success or a human-readable explanation of
    why `years` came up short (surfaced on the site so a skipped ticker
    isn't just a silent absence)."""
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

    missing = [f for f in REQUIRED_FIELDS if not series[f]]
    if missing:
        return [], f"filer never reports: {', '.join(missing)}"

    common_dates = set(series[REQUIRED_FIELDS[0]])
    for f in REQUIRED_FIELDS[1:]:
        common_dates &= set(series[f])
    common_dates = sorted(common_dates, reverse=True)

    if len(common_dates) < MIN_YEARS_REQUIRED:
        return [], (f"only {len(common_dates)} fiscal year(s) with every required "
                     f"field reported together (need {MIN_YEARS_REQUIRED})")

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
    return years, None

def _ttm_snapshot_for_magic_formula(gaap):
    """Try to assemble a trailing-twelve-month snapshot for Magic Formula
    from the latest 10-Q (see reconstruct_ttm() for the TTM formula).
    Returns a year-shaped dict on success, or None if a clean TTM can't be
    put together (no recent 10-Q, mismatched quarterly history, a missing
    balance-sheet field at the anchor date, etc.) -- the caller falls back
    to the prior fiscal-year-only approach on None, so this never trades
    away existing coverage."""
    ebit_periods = extract_field_periods(gaap, XBRL_FIELD_SPECS["ebit"][0], "USD")
    ttm_ebit, ttm_asof, _reason = reconstruct_ttm(ebit_periods)
    if ttm_ebit is None:
        return None

    instant_fields = ["current_assets", "current_liab", "long_term_debt",
                       "current_debt", "cash", "ppe_net", "ppe_gross", "accum_depreciation"]
    instant_series = {}
    for field in instant_fields:
        candidates, unit_key, instant = XBRL_FIELD_SPECS[field]
        _, values = extract_field(gaap, candidates, unit_key, instant, forms=("10-K", "10-Q"))
        instant_series[field] = values

    current_assets = value_asof(instant_series["current_assets"], ttm_asof)
    current_liab = value_asof(instant_series["current_liab"], ttm_asof)
    cash = value_asof(instant_series["cash"], ttm_asof)
    ppe_net = value_asof(instant_series["ppe_net"], ttm_asof, max_slack_days=TTM_PPE_SLACK_DAYS)
    if ppe_net is None:
        gross = value_asof(instant_series["ppe_gross"], ttm_asof, max_slack_days=TTM_PPE_SLACK_DAYS)
        accum = value_asof(instant_series["accum_depreciation"], ttm_asof, max_slack_days=TTM_PPE_SLACK_DAYS)
        if gross is not None and accum is not None:
            ppe_net = gross - accum
    long_term_debt = value_asof(instant_series["long_term_debt"], ttm_asof) or 0
    current_debt = value_asof(instant_series["current_debt"], ttm_asof) or 0

    if current_assets is None or current_liab is None or cash is None or ppe_net is None:
        return None

    shares_val, shares_end = latest_period_value(
        extract_field_periods(gaap, XBRL_FIELD_SPECS["shares"][0], "shares"))
    if shares_val is None or shares_end is None:
        return None
    if abs((date.fromisoformat(shares_end) - date.fromisoformat(ttm_asof)).days) > 100:
        return None   # shares figure isn't from around the same reporting period as the TTM anchor

    return {
        "date": ttm_asof,
        "ebit": ttm_ebit,
        "current_assets": current_assets,
        "current_liab": current_liab,
        "long_term_debt": long_term_debt,
        "current_debt": current_debt,
        "cash": cash,
        "ppe_net": ppe_net,
        "shares": shares_val,
    }

def normalize_for_magic_formula(facts):
    """Return (year, reason, basis). `year` is the single most recent
    snapshot dict with everything Magic Formula needs, or None; `reason` is
    None on success or a human-readable explanation otherwise; `basis` is
    "TTM" when reconstructed from a recent 10-Q (see
    _ttm_snapshot_for_magic_formula(), tried first since it's the freshest
    available data) or "FY" when it falls back to the last full fiscal year
    from a 10-K, same behavior as before 10-Q support existed -- the fallback
    covers filers with no recent 10-Q (e.g. foreign private issuers that
    file 20-F/6-K instead) or whose quarterly history doesn't cleanly
    reconstruct. Unlike F-Score this only looks at the latest data point --
    Magic Formula is a point-in-time cheapness/quality ranking, not a
    multi-year trend, so there's no 3-year requirement here."""
    gaap = facts.get("facts", {}).get("us-gaap", {})

    ttm_year = _ttm_snapshot_for_magic_formula(gaap)
    if ttm_year is not None:
        if ttm_year["shares"] < MIN_PLAUSIBLE_SHARES:
            return None, "implausible share count (likely a filer tagging error, e.g. shares reported in millions)", None
        return ttm_year, None, "TTM"

    series = {}
    for field in MAGIC_FORMULA_FIELDS:
        candidates, unit_key, instant = XBRL_FIELD_SPECS[field]
        _, values = extract_field(gaap, candidates, unit_key, instant)
        series[field] = values

    # Fall back to gross PP&E - accumulated depreciation where the filer
    # doesn't tag a combined "net" figure directly (e.g. GE Vernova).
    derived_ppe = {
        d: series["ppe_gross"][d] - series["accum_depreciation"][d]
        for d in series["ppe_gross"]
        if d in series["accum_depreciation"] and d not in series["ppe_net"]
    }
    series["ppe_net"] = {**derived_ppe, **series["ppe_net"]}

    missing = [f for f in MAGIC_FORMULA_REQUIRED if not series[f]]
    if missing:
        return None, f"filer never reports: {', '.join(missing)}", None

    common_dates = set(series[MAGIC_FORMULA_REQUIRED[0]])
    for f in MAGIC_FORMULA_REQUIRED[1:]:
        common_dates &= set(series[f])
    if not common_dates:
        return None, "no single fiscal year has every required field reported together", None
    d = max(common_dates)

    try:
        age_days = (date.today() - date.fromisoformat(d)).days
    except ValueError:
        age_days = None
    if age_days is not None and age_days > STALE_DATA_MAX_AGE_DAYS:
        return None, f"most recent complete year ({d}) is more than {STALE_DATA_MAX_AGE_DAYS} days old", None

    if series["shares"][d] < MIN_PLAUSIBLE_SHARES:
        return None, "implausible share count (likely a filer tagging error, e.g. shares reported in millions)", None

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
    }, None, "FY"

def normalize_for_graham(facts):
    """Return (years, reason). `years` is up to GRAHAM_EARNINGS_YEARS yearly
    dicts, newest first, for Graham's Defensive Investor checklist; `reason`
    is None on success (a full window) or a human-readable explanation
    otherwise. Unlike Magic Formula, Graham's earnings-stability and
    dividend-record rules genuinely need multiple years, so this keeps the
    full available window rather than collapsing to one snapshot."""
    gaap = facts.get("facts", {}).get("us-gaap", {})

    series = {}
    for field in GRAHAM_FIELDS:
        candidates, unit_key, instant = XBRL_FIELD_SPECS[field]
        _, values = extract_field(gaap, candidates, unit_key, instant)
        series[field] = values

    missing = [f for f in GRAHAM_REQUIRED if not series[f]]
    if missing:
        return [], f"filer never reports: {', '.join(missing)}"

    common_dates = set(series[GRAHAM_REQUIRED[0]])
    for f in GRAHAM_REQUIRED[1:]:
        common_dates &= set(series[f])
    all_common_dates = sorted(common_dates, reverse=True)
    common_dates = all_common_dates[:GRAHAM_EARNINGS_YEARS]

    if len(common_dates) < GRAHAM_EARNINGS_YEARS:
        return [], (f"only {len(common_dates)} fiscal year(s) with every required field "
                     f"reported together (need {GRAHAM_EARNINGS_YEARS}) -- often a recent "
                     f"IPO/spinoff, or a filer that changes which balance-sheet fields it tags")

    years = []
    for d in common_dates:
        years.append({
            "date":                d,
            "net_income":          series["net_income"][d],
            "shares":              series["shares"][d],
            "revenue":             series["revenue"][d],
            "current_assets":      series["current_assets"][d],
            "current_liab":        series["current_liab"][d],
            "long_term_debt":      series["long_term_debt"].get(d, 0),
            "stockholders_equity": series["stockholders_equity"][d],
            "dividends_paid":      series["dividends_paid"].get(d, 0),
        })

    # Same MIN_PLAUSIBLE_SHARES filer-tagging bug as Magic Formula (see
    # above): if any year in the window has a corrupted share count, EPS
    # and book-value-per-share are garbage for that year, which would
    # silently break the earnings-growth trend and moderate_pe/moderate_
    # valuation signals. Bail out entirely rather than score off it.
    if any(y["shares"] < MIN_PLAUSIBLE_SHARES for y in years):
        return [], "implausible share count in one or more years (likely a filer tagging error)"

    return years, None

def _ttm_snapshot_for_lynch(gaap):
    """Try to assemble a Lynch PEG growth window whose most recent point is
    a trailing-twelve-month EPS figure reconstructed from the latest 10-Q,
    with the remaining LYNCH_GROWTH_YEARS-1 points filled in from annual
    10-K history (only the current point needs to be quarterly-fresh -- the
    growth-rate anchor further back doesn't). Returns a years list (newest
    first) or None if a clean TTM point can't be assembled, in which case
    the caller falls back to the prior pure-FY window."""
    ni_candidates, ni_unit, _ = XBRL_FIELD_SPECS["net_income"]
    ni_periods = extract_field_periods(gaap, ni_candidates, ni_unit)
    ttm_ni, ttm_asof, _reason = reconstruct_ttm(ni_periods)
    if ttm_ni is None:
        return None

    sh_candidates, sh_unit, _ = XBRL_FIELD_SPECS["shares"]
    shares_val, shares_end = latest_period_value(extract_field_periods(gaap, sh_candidates, sh_unit))
    if shares_val is None or shares_end is None:
        return None
    if abs((date.fromisoformat(shares_end) - date.fromisoformat(ttm_asof)).days) > 100:
        return None

    _, annual_ni = extract_field(gaap, ni_candidates, ni_unit, False)
    _, annual_sh = extract_field(gaap, sh_candidates, sh_unit, False)
    annual_common = sorted(set(annual_ni) & set(annual_sh), reverse=True)
    older_years = [d for d in annual_common if d < ttm_asof][:LYNCH_GROWTH_YEARS - 1]
    if len(older_years) < LYNCH_GROWTH_YEARS - 1:
        return None

    years = [{"date": ttm_asof, "net_income": ttm_ni, "shares": shares_val}]
    years += [{"date": d, "net_income": annual_ni[d], "shares": annual_sh[d]} for d in older_years]
    return years

def normalize_for_lynch(facts):
    """Return (years, reason, basis). `years` is up to LYNCH_GROWTH_YEARS
    yearly {date, net_income, shares} dicts, newest first, for PEG's
    trailing EPS growth rate; `reason` is None on success (a full window) or
    a human-readable explanation otherwise; `basis` is "TTM" when the most
    recent point is a trailing-twelve-month figure reconstructed from the
    latest 10-Q (see _ttm_snapshot_for_lynch(), tried first) or "FY" when it
    falls back to the prior all-annual window -- same behavior as before
    10-Q support existed."""
    gaap = facts.get("facts", {}).get("us-gaap", {})

    ttm_years = _ttm_snapshot_for_lynch(gaap)
    if ttm_years is not None and not any(y["shares"] < MIN_PLAUSIBLE_SHARES for y in ttm_years):
        return ttm_years, None, "TTM"

    ni_candidates, ni_unit, ni_instant = XBRL_FIELD_SPECS["net_income"]
    sh_candidates, sh_unit, sh_instant = XBRL_FIELD_SPECS["shares"]
    _, net_income = extract_field(gaap, ni_candidates, ni_unit, ni_instant)
    _, shares = extract_field(gaap, sh_candidates, sh_unit, sh_instant)

    common_dates = sorted(set(net_income) & set(shares), reverse=True)[:LYNCH_GROWTH_YEARS]
    if len(common_dates) < LYNCH_GROWTH_YEARS:
        return [], (f"only {len(common_dates)} fiscal year(s) of clean EPS history available "
                     f"(need {LYNCH_GROWTH_YEARS})"), None

    # A filer can switch which net_income tag it uses (e.g. Booking Holdings
    # stopped tagging plain NetIncomeLoss in its 10-Ks after 2015), which
    # would otherwise silently produce a "growth window" of ancient years
    # even though shares data is current. Every other model already guards
    # against exactly this kind of staleness -- Lynch needs the same check.
    try:
        age_days = (date.today() - date.fromisoformat(common_dates[0])).days
    except ValueError:
        age_days = None
    if age_days is not None and age_days > STALE_DATA_MAX_AGE_DAYS:
        return [], (f"most recent overlapping net_income/shares year ({common_dates[0]}) is more "
                     f"than {STALE_DATA_MAX_AGE_DAYS} days old -- likely a filer tag change, not a real gap"), None

    years = [{"date": d, "net_income": net_income[d], "shares": shares[d]} for d in common_dates]

    # Same MIN_PLAUSIBLE_SHARES filer-tagging bug as Magic Formula/Graham.
    if any(y["shares"] < MIN_PLAUSIBLE_SHARES for y in years):
        return [], "implausible share count in one or more years (likely a filer tagging error)", None

    return years, None, "FY"

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
# THE MODEL: Graham Defensive Investor  (pure function -- no network, easy to test)
# ----------------------------------------------------------------------------
# 7 binary signals, same spirit as Piotroski's checklist but aimed squarely
# at valuation + margin of safety rather than fundamental trend. Score is
# their sum (0-7); graham_pass (all 7) is Graham's original all-or-nothing
# reading, but the 0-7 score is far more useful for sorting/filtering.
# See GRAHAM_EARNINGS_YEARS/GRAHAM_DIVIDEND_YEARS above for the relaxed
# lookback windows -- everything else follows Graham's own thresholds.

def compute_graham(years, price):
    """`years` = normalize_for_graham() output (newest first), `price` =
    current share price. Returns (score, signals_dict, metrics_dict) or
    (None, reason, {})."""
    if len(years) < GRAHAM_EARNINGS_YEARS:
        return None, "insufficient_years", {}

    y0 = years[0]

    try:
        asof_age_days = (date.today() - date.fromisoformat(y0["date"])).days
    except ValueError:
        asof_age_days = None
    if asof_age_days is not None and asof_age_days > STALE_DATA_MAX_AGE_DAYS:
        return None, "stale_data", {}

    current_ratio = _safe_div(y0["current_assets"], y0["current_liab"])
    net_current_assets = y0["current_assets"] - y0["current_liab"]
    book_value_per_share = _safe_div(y0["stockholders_equity"], y0["shares"])

    earnings_window = years[:GRAHAM_EARNINGS_YEARS]
    dividend_window = years[:GRAHAM_DIVIDEND_YEARS]

    # Rule 6 uses "average earnings of the past three years"; growth (rule 5)
    # compares that same recent 3-yr average against the earliest 3 years of
    # the window (Graham's own recipe, just over our shorter span).
    recent_eps = [_safe_div(y["net_income"], y["shares"]) for y in earnings_window[:3]]
    early_eps = [_safe_div(y["net_income"], y["shares"]) for y in earnings_window[-3:]]
    if any(v is None for v in recent_eps + early_eps) or book_value_per_share is None or current_ratio is None:
        return None, "missing_fields", {}

    avg_recent_eps = sum(recent_eps) / len(recent_eps)
    avg_early_eps = sum(early_eps) / len(early_eps)
    eps_growth = (avg_recent_eps - avg_early_eps) / abs(avg_early_eps) if avg_early_eps else None

    pe = _safe_div(price, avg_recent_eps) if avg_recent_eps > 0 else None
    pb = _safe_div(price, book_value_per_share) if book_value_per_share > 0 else None
    graham_number = pe * pb if (pe is not None and pb is not None) else None

    s = {}
    s["adequate_size"]               = int(y0["revenue"] >= GRAHAM_MIN_REVENUE)
    s["strong_financial_condition"]  = int(current_ratio >= 2 and y0["long_term_debt"] < net_current_assets)
    s["earnings_stability"]          = int(all(y["net_income"] > 0 for y in earnings_window))
    s["dividend_record"]             = int(all(y["dividends_paid"] > 0 for y in dividend_window))
    s["earnings_growth"]             = int(eps_growth is not None and eps_growth >= GRAHAM_MIN_EPS_GROWTH)
    s["moderate_pe"]                 = int(pe is not None and pe <= GRAHAM_MAX_PE)
    s["moderate_valuation"]          = int(graham_number is not None and graham_number <= GRAHAM_MAX_GRAHAM_NUMBER)

    score = sum(s.values())
    metrics = {
        "asof": y0["date"],
        "current_ratio": round(current_ratio, 3),
        "pe": round(pe, 2) if pe is not None else None,
        "pb": round(pb, 2) if pb is not None else None,
        "graham_number": round(graham_number, 2) if graham_number is not None else None,
        "eps_growth": round(eps_growth, 4) if eps_growth is not None else None,
        "earnings_years_checked": len(earnings_window),
        "dividend_years_checked": len(dividend_window),
    }
    return score, s, metrics

# ----------------------------------------------------------------------------
# THE MODEL: Peter Lynch's PEG Ratio  (pure function -- no network, easy to test)
# ----------------------------------------------------------------------------
# PEG = P/E / trailing EPS growth rate (whole-number percent, e.g. 15 for
# 15%). Lower is better -- ranked across the universe in screen(), same
# mechanism as Magic Formula, so this always produces a full ranked list
# rather than an absolute bar the whole market can fail. `rating` is
# Lynch's own descriptive bands (excellent/attractive/fair/expensive),
# shown for color but not used to filter anyone out.

def compute_lynch_peg(years, price):
    """`years` = normalize_for_lynch() output (newest first, >= 2 needed for
    a growth rate), `price` = current share price. Returns (metrics_dict,
    None) or (None, reason)."""
    if len(years) < 2:
        return None, "insufficient_years"

    eps_newest = _safe_div(years[0]["net_income"], years[0]["shares"])
    eps_oldest = _safe_div(years[-1]["net_income"], years[-1]["shares"])
    if eps_newest is None or eps_newest <= 0:
        return None, "negative or zero trailing EPS -- P/E isn't meaningful"
    if eps_oldest is None or eps_oldest <= 0:
        return None, "negative or zero EPS at the start of the growth window -- growth rate isn't meaningful"

    n_periods = len(years) - 1
    growth_rate = (eps_newest / eps_oldest) ** (1 / n_periods) - 1
    if growth_rate <= 0:
        return None, "flat or declining EPS over the trailing window -- PEG isn't meaningful without positive growth"

    pe = price / eps_newest
    peg = pe / (growth_rate * 100)

    if peg < LYNCH_EXCELLENT_PEG:
        rating = "excellent"
    elif peg < LYNCH_ATTRACTIVE_PEG:
        rating = "attractive"
    elif peg < LYNCH_FAIR_PEG:
        rating = "fair"
    else:
        rating = "expensive"

    return {
        "asof": years[0]["date"],
        "eps": round(eps_newest, 2),
        "eps_growth": round(growth_rate, 4),
        "pe": round(pe, 2),
        "peg": round(peg, 3),
        "rating": rating,
        "years_checked": len(years),
    }, None

# ----------------------------------------------------------------------------
# RUNNER
# ----------------------------------------------------------------------------

def _empty_row(symbol, sector, reason):
    """A results.json row for a ticker that never got as far as fetching
    financials (no CIK, or SEC fetch failed) -- still listed, with a reason,
    so a ticker search on the site always explains an absence rather than
    the row just not existing."""
    return {
        "symbol": symbol, "sector": sector, "universe_reason": reason,
        "fscore": None, "f_signals": None, "f_metrics": None, "f_skip_reason": reason,
        "mf_metrics": None, "mf_skip_reason": reason,
        "graham_score": None, "graham_signals": None, "graham_metrics": None, "graham_skip_reason": reason,
        "lynch_metrics": None, "lynch_skip_reason": reason,
    }

def screen(tickers, refresh=False):
    conn = init_db()
    cik_map = load_ticker_cik_map(refresh=refresh)
    sector_map = load_sector_map()
    results, errors = [], []

    for i, symbol in enumerate(tickers, 1):
        symbol = symbol.strip().upper()
        if not symbol:
            continue

        sector = sector_map.get(symbol)

        cik = resolve_cik(cik_map, symbol)
        if cik is None:
            reason = "no CIK found in SEC's ticker map (check the symbol, or a share-class dot/dash mismatch)"
            errors.append((symbol, "no_cik_found"))
            results.append(_empty_row(symbol, sector, reason))
            print(f"  [{i}/{len(tickers)}] {symbol:6s}  SKIP  ({reason})")
            continue

        try:
            facts = fetch_company_facts(conn, symbol, cik, refresh)
        except FetchError as e:
            errors.append((symbol, str(e)))
            results.append(_empty_row(symbol, sector, str(e)))
            print(f"  [{i}/{len(tickers)}] {symbol:6s}  SKIP  ({e})")
            continue

        years, years_reason = normalize_from_facts(facts)
        fscore, f_signals, f_metrics = compute_fscore(years)
        f_skip_reason = None
        if fscore is None:
            f_skip_reason = years_reason or f_signals
            f_signals, f_metrics = None, None

        # Price is shared by Magic Formula and Graham -- fetch once per
        # ticker rather than once per model (the cache would dedupe this
        # anyway within a run, but doing it once is simpler to reason about).
        price, price_reason = None, None
        try:
            price = fetch_price(conn, symbol, refresh)
        except FetchError as e:
            price_reason = str(e)

        mf_metrics, mf_skip_reason = None, None
        if sector in MAGIC_FORMULA_EXCLUDED_SECTORS:
            mf_skip_reason = f"{sector} sector excluded (Greenblatt's own methodology -- no clean 'invested capital' for these balance sheets)"
        elif price is None:
            mf_skip_reason = price_reason or "no price data available"
        else:
            mf_year, mf_year_reason, mf_basis = normalize_for_magic_formula(facts)
            if mf_year is None:
                mf_skip_reason = mf_year_reason
            else:
                mf_metrics, mf_skip_reason = compute_magic_formula_raw(mf_year, price)
                if mf_metrics is not None:
                    mf_metrics["basis"] = mf_basis

        graham_score, graham_signals, graham_metrics, graham_skip_reason = None, None, None, None
        if price is None:
            graham_skip_reason = price_reason or "no price data available"
        else:
            graham_years, graham_years_reason = normalize_for_graham(facts)
            g_score, g_signals, g_metrics = compute_graham(graham_years, price)
            if g_score is None:
                graham_skip_reason = graham_years_reason or g_signals
            else:
                graham_score, graham_signals, graham_metrics = g_score, g_signals, g_metrics

        lynch_metrics, lynch_skip_reason = None, None
        if price is None:
            lynch_skip_reason = price_reason or "no price data available"
        else:
            lynch_years, lynch_years_reason, lynch_basis = normalize_for_lynch(facts)
            if not lynch_years:
                lynch_skip_reason = lynch_years_reason
            else:
                lynch_metrics, lynch_skip_reason = compute_lynch_peg(lynch_years, price)
                if lynch_metrics is not None:
                    lynch_metrics["basis"] = lynch_basis

        results.append({
            "symbol": symbol,
            "sector": sector,
            "universe_reason": None,
            "fscore": fscore,
            "f_signals": f_signals,
            "f_metrics": f_metrics,
            "f_skip_reason": f_skip_reason,
            "mf_metrics": mf_metrics,
            "mf_skip_reason": mf_skip_reason,
            "graham_score": graham_score,
            "graham_signals": graham_signals,
            "graham_metrics": graham_metrics,
            "graham_skip_reason": graham_skip_reason,
            "lynch_metrics": lynch_metrics,
            "lynch_skip_reason": lynch_skip_reason,
        })
        if fscore is None and mf_metrics is None and graham_score is None and lynch_metrics is None:
            errors.append((symbol, f_skip_reason or "unscoreable"))
        fscore_disp = f"F={fscore}/9" if fscore is not None else "F=n/a"
        mf_disp = (f"ROC={mf_metrics['roc']:.1%} EY={mf_metrics['earnings_yield']:.1%}"
                   if mf_metrics else "MF=n/a")
        graham_disp = f"G={graham_score}/7" if graham_score is not None else "G=n/a"
        lynch_disp = f"PEG={lynch_metrics['peg']}" if lynch_metrics else "PEG=n/a"
        print(f"  [{i}/{len(tickers)}] {symbol:6s}  {fscore_disp}   {mf_disp}   {graham_disp}   {lynch_disp}")

    # Magic Formula and PEG ranks are relative to the rest of the scored
    # universe, so they're computed here, after every ticker's raw metrics
    # are in hand.
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

    lynch_rows = [r for r in results if r["lynch_metrics"] is not None]
    lynch_rows.sort(key=lambda r: (r["lynch_metrics"]["peg"], r["symbol"]))
    for rank, r in enumerate(lynch_rows, 1):
        r["lynch_metrics"]["peg_rank"] = rank

    results.sort(key=lambda r: (-(r["fscore"] if r["fscore"] is not None else -1), r["symbol"]))

    out = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "models": ["piotroski_f_score", "magic_formula", "graham_defensive", "lynch_peg"],
        # Magic Formula and Lynch PEG refresh from the latest 10-Q (TTM) when
        # one cleanly reconstructs, falling back to the last 10-K (FY)
        # otherwise -- see reconstruct_ttm(). F-Score and Graham are
        # multi-year checklists and stay purely annual (10-K only).
        "quarterly_models": ["magic_formula", "lynch_peg"],
        "data_source": "sec_edgar_xbrl + yahoo_finance_price",
        "universe_size": len(tickers),
        "scored": sum(1 for r in results
                      if r["fscore"] is not None or r["mf_metrics"] is not None
                      or r["graham_score"] is not None or r["lynch_metrics"] is not None),
        "scored_f_score": sum(1 for r in results if r["fscore"] is not None),
        "scored_magic_formula": len(mf_rows),
        "scored_magic_formula_ttm": sum(1 for r in mf_rows if r["mf_metrics"]["basis"] == "TTM"),
        "scored_graham": sum(1 for r in results if r["graham_score"] is not None),
        "scored_lynch": len(lynch_rows),
        "scored_lynch_ttm": sum(1 for r in lynch_rows if r["lynch_metrics"]["basis"] == "TTM"),
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

    try:
        price = fetch_price(conn, symbol, refresh=True)
    except FetchError as e:
        print(f"\nprice fetch failed: {e}")
        conn.close()
        return

    print("\n-- Magic Formula --")
    mf_year, mf_reason, mf_basis = normalize_for_magic_formula(facts)
    if mf_year is None:
        print(f"not scored: {mf_reason}")
    else:
        metrics, reason = compute_magic_formula_raw(mf_year, price)
        if metrics is None:
            print(f"not scored: {reason}")
        else:
            metrics["basis"] = mf_basis
            print(f"price={price}  basis={mf_basis}  {metrics}")

    print("\n-- Graham Defensive Investor --")
    graham_years, graham_years_reason = normalize_for_graham(facts)
    if len(graham_years) < GRAHAM_EARNINGS_YEARS:
        print(f"not scored: {graham_years_reason}")
    else:
        score, signals, metrics = compute_graham(graham_years, price)
        if score is None:
            print(f"not scored: {signals}")
        else:
            print(f"price={price}  score={score}/7")
            for name, val in signals.items():
                print(f"    {val}  {name}")
            print(f"    metrics: {metrics}")

    print("\n-- Peter Lynch PEG --")
    lynch_years, lynch_years_reason, lynch_basis = normalize_for_lynch(facts)
    if not lynch_years:
        print(f"not scored: {lynch_years_reason}")
    else:
        metrics, reason = compute_lynch_peg(lynch_years, price)
        if metrics is None:
            print(f"not scored: {reason}")
        else:
            metrics["basis"] = lynch_basis
            print(f"price={price}  basis={lynch_basis}  {metrics}")

    conn.close()

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

def self_test_graham():
    """A hand-built 7-year company engineered to pass all 7 Graham signals,
    no network needed. EPS grows from 1.00 to 2.00 across the window (recent
    3yr avg ~1.90 vs early 3yr avg ~1.17 -> comfortably over the 15% growth
    bar), current ratio is 3.0, no long-term debt, dividends paid every
    year, and price is set so PE=10 exactly (Graham Number well under 22.5)."""
    years = []
    for i in range(7):
        yr = 2025 - i
        eps_path = [2.00, 1.90, 1.80, 1.50, 1.30, 1.20, 1.00]  # newest first
        net_income = eps_path[i] * 100          # 100 shares outstanding
        years.append({
            "date": f"{yr}-12-31", "net_income": net_income, "shares": 100,
            "revenue": 5_000_000_000, "current_assets": 600, "current_liab": 200,
            "long_term_debt": 0, "stockholders_equity": 2000, "dividends_paid": 50,
        })

    avg_recent_eps = sum(eps_path[:3]) / 3   # 1.90
    price = avg_recent_eps * 10              # PE = 10 exactly

    score, signals, metrics = compute_graham(years, price)

    print("\nSelf-test Graham Defensive Investor:")
    for name, val in signals.items():
        print(f"  {val}  {name}")
    print(f"  ----> total Graham score = {score}/7")
    print(f"  metrics: {metrics}")

    assert score == 7, f"expected 7, got {score}"
    assert all(v == 1 for v in signals.values()), "a signal did not fire as expected"
    print("PASS: all 7 signals fired and the total is 7. Graham scoring engine is correct.")
    return True

def self_test_ttm_reconstruction():
    """Hand-built period data (no network), proving the TTM formula itself:
        TTM = last full fiscal year + this year's year-to-date
              - the same year-to-date stretch a year ago.
    Dates are relative to today so this stays valid whenever it's run
    (the "latest" period must be recent or reconstruct_ttm's staleness
    guard rejects it)."""
    latest_end   = date.today() - timedelta(days=30)     # a fresh quarter-end -- anchors the TTM
    latest_start = latest_end - timedelta(days=274)        # ~9-month year-to-date span
    prior_end    = latest_end - timedelta(days=365)        # same stretch, one year earlier
    prior_start  = prior_end - timedelta(days=274)
    fy_end       = latest_start - timedelta(days=1)        # last full fiscal year, ending right
    fy_start     = fy_end - timedelta(days=364)             # before the year-to-date periods began

    periods = {
        (fy_start.isoformat(), fy_end.isoformat()): 400.0,          # last full fiscal year (10-K)
        (prior_start.isoformat(), prior_end.isoformat()): 280.0,    # year-ago YTD (10-Q)
        (latest_start.isoformat(), latest_end.isoformat()): 340.0,  # latest YTD (10-Q) -- anchor
    }
    value, asof, reason = reconstruct_ttm(periods)

    print("\nSelf-test TTM reconstruction:")
    print(f"  value={value}  asof={asof}  reason={reason}")

    assert value == 460, f"expected 460 (400 + 340 - 280), got {value}"
    assert asof == latest_end.isoformat(), f"expected asof {latest_end.isoformat()}, got {asof}"
    assert reason is None
    print("PASS: TTM reconstruction math is correct.")

    # A stale "latest" period (well past TTM_STALE_MAX_AGE_DAYS) should be
    # rejected rather than silently used.
    stale_end = date.today() - timedelta(days=TTM_STALE_MAX_AGE_DAYS + 30)
    stale_start = stale_end - timedelta(days=274)
    stale_periods = dict(periods)
    del stale_periods[(latest_start.isoformat(), latest_end.isoformat())]
    stale_periods[(stale_start.isoformat(), stale_end.isoformat())] = 340.0
    value, asof, reason = reconstruct_ttm(stale_periods)
    assert value is None and reason is not None, "a stale latest period should be rejected, not scored"
    print("PASS: a stale latest 10-Q period is correctly rejected.")
    return True

def self_test_lynch():
    """A hand-built 5-year company with EPS compounding at exactly 10%/year
    (1.00 -> 1.4641), no network needed. Price is set so PE=8, giving
    peg = 8 / 10 = 0.8 exactly ("attractive": 0.5 <= peg < 1.0)."""
    eps_path = [1.4641, 1.331, 1.21, 1.10, 1.00]  # newest first, +10%/yr
    years = [
        {"date": f"{2025 - i}-12-31", "net_income": eps * 100, "shares": 100}
        for i, eps in enumerate(eps_path)
    ]
    price = 8 * eps_path[0]  # PE = 8 exactly

    metrics, reason = compute_lynch_peg(years, price)

    print("\nSelf-test Peter Lynch PEG:")
    print(f"  metrics: {metrics}")

    assert metrics is not None, f"expected valid metrics, got reason={reason}"
    assert abs(metrics["eps_growth"] - 0.10) < 0.001, f"growth mismatch: {metrics['eps_growth']}"
    assert abs(metrics["pe"] - 8.0) < 0.01, f"PE mismatch: {metrics['pe']}"
    assert abs(metrics["peg"] - 0.8) < 0.01, f"PEG mismatch: {metrics['peg']}"
    assert metrics["rating"] == "attractive", f"rating mismatch: {metrics['rating']}"
    print("PASS: Lynch PEG math is correct.")
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
        self_test_graham()
        self_test_lynch()
        self_test_ttm_reconstruction()
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
              f"   (as of {m['asof']}, {m['basis']})")

    print(f"\n=== GRAHAM DEFENSIVE INVESTOR (score 7/7) ===")
    for r in out["results"]:
        if r["graham_score"] == 7:
            m = r["graham_metrics"]
            print(f"  {r['symbol']:6s}  G=7/7  PE={m['pe']}  PB={m['pb']}  "
                  f"Graham#={m['graham_number']}   (as of {m['asof']})")

    print(f"\n=== PETER LYNCH PEG (top 20) ===")
    lynch_top = sorted(
        (r for r in out["results"] if r["lynch_metrics"] is not None),
        key=lambda r: r["lynch_metrics"]["peg_rank"],
    )[:20]
    for r in lynch_top:
        m = r["lynch_metrics"]
        print(f"  #{m['peg_rank']:<4d}{r['symbol']:6s}  PEG={m['peg']}  ({m['rating']}, "
              f"PE={m['pe']} growth={m['eps_growth']:.1%})   (as of {m['asof']}, {m['basis']})")

    print(f"\nScored {out['scored']}/{out['universe_size']} "
          f"(F-Score: {out['scored_f_score']}, "
          f"Magic Formula: {out['scored_magic_formula']} [{out['scored_magic_formula_ttm']} TTM / "
          f"{out['scored_magic_formula'] - out['scored_magic_formula_ttm']} FY], "
          f"Graham: {out['scored_graham']}, "
          f"Lynch PEG: {out['scored_lynch']} [{out['scored_lynch_ttm']} TTM / "
          f"{out['scored_lynch'] - out['scored_lynch_ttm']} FY]). "
          f"Wrote {RESULTS_JSON}. Skipped {len(errors)}.")

if __name__ == "__main__":
    main()
