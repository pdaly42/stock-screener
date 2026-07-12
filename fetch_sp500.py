#!/usr/bin/env python3
"""
fetch_sp500.py -- pulls the current S&P 500 constituent list (and each
member's GICS sector) from Wikipedia. Writes sp500_tickers.txt (one ticker
per line, the format screener.py's --tickers flag expects) and
sp500_sectors.json (ticker -> GICS sector). screener.py reads the sector
file to exclude Financials/Utilities from the Magic Formula model, per
Greenblatt's own methodology -- it's optional, so screening a custom ticker
list without this file just skips that exclusion.

Wikipedia's "List of S&P 500 companies" table is community-maintained and
updated promptly on index changes -- there's no free official feed for
index membership (S&P Global's own data is a paid product), so this is the
standard workaround. Re-run this occasionally; membership changes a few
times a year.

RUN
---
   python3 fetch_sp500.py
   python3 screener.py --tickers sp500_tickers.txt
"""

import html
import json
import re
import urllib.request

WIKI_URL = "https://en.wikipedia.org/wiki/List_of_S%26P_500_companies"
OUT_FILE = "sp500_tickers.txt"
SECTOR_FILE = "sp500_sectors.json"
USER_AGENT = "PersonalStockScreener/1.0 (pdaly42@gmail.com)"

def fetch_sp500_constituents():
    """Returns a list of (symbol, gics_sector) tuples."""
    req = urllib.request.Request(WIKI_URL, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=30) as resp:
        page = resp.read().decode("utf-8")

    table_match = re.search(
        r'<table[^>]*id="constituents"[^>]*>(.*?)</table>', page, re.S
    )
    if not table_match:
        raise RuntimeError("couldn't find the constituents table -- Wikipedia's page layout may have changed")

    constituents = []
    for row in re.findall(r"<tr[^>]*>(.*?)</tr>", table_match.group(1), re.S):
        cells = re.findall(r"<td[^>]*>(.*?)</td>", row, re.S)
        if len(cells) < 3:   # header row (<th>) or malformed row
            continue
        symbol = html.unescape(re.sub(r"<[^>]+>", "", cells[0])).strip()
        sector = html.unescape(re.sub(r"<[^>]+>", "", cells[2])).strip()
        if symbol:
            constituents.append((symbol, sector))
    return constituents

def main():
    constituents = fetch_sp500_constituents()
    tickers = sorted({sym for sym, _ in constituents})
    sectors = {sym: sector for sym, sector in constituents}

    with open(OUT_FILE, "w") as f:
        f.write("\n".join(tickers) + "\n")
    with open(SECTOR_FILE, "w") as f:
        json.dump(sectors, f, indent=2, sort_keys=True)

    print(f"Wrote {len(tickers)} tickers to {OUT_FILE}")
    print(f"Wrote sector map ({len(sectors)} entries) to {SECTOR_FILE}")

if __name__ == "__main__":
    main()
