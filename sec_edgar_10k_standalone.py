#!/usr/bin/env python3
# -----------------------------------------------------------------------------
# sec_edgar_10k_financials.py
#
# WHAT THIS DOES
#   Builds a firm-year panel of annual accounting variables from SEC EDGAR
#   10-K filings, for a user-supplied universe of U.S. public companies.
#
#   Primary data path (fast, reliable):
#       1. https://data.sec.gov/submissions/CIK##########.json
#          -> company name, SIC code, and the list of 10-K filings with their
#             filing dates and period-of-report (fiscal period end) dates.
#       2. https://data.sec.gov/api/xbrl/companyfacts/CIK##########.json
#          -> every XBRL fact the company has ever reported, which we align to
#             the fiscal period ends found in step 1.
#
#   Fallback path (only used when companyfacts is missing/incomplete):
#       3. The raw XBRL instance document inside the filing's EDGAR directory
#          (e.g. .../aapl-20240928_htm.xml), parsed with ElementTree.
#       NOTE: essentially every 10-K filed since ~2011 has XBRL, so the
#       fallback rarely fires for a 2020+ sample. There is deliberately NO
#       free-text HTML table scraper here: for modern filings it adds a large
#       amount of fragile code for almost no incremental coverage. See
#       "LIMITATIONS" at the bottom of this header.
#
# HOW TO RUN
#   python3 sec_edgar_10k_financials.py \
#       --input  firms.csv \
#       --output firm_year_financials.csv \
#       --start-year 2020 \
#       --end-year   2024 \
#       --user-agent "Your Name your.email@university.edu" \
#       --log-file run.log
#
#   Every argument has a default set in the CONFIG block below, so a bare
#   `python3 sec_edgar_10k_financials.py` also works once you edit those.
#   Requires Python 3.8+. No third-party packages needed (stdlib only).
#
# INPUT
#   A CSV with a header row containing at least one of `ticker` or `cik`:
#       ticker,cik
#       AAPL,320189
#       MSFT,0000789019
#       NVDA,
#       ,0000019617
#   - CIK may be zero-padded or not; leading zeros are added automatically.
#   - If `cik` is blank, the ticker is resolved via SEC's company_tickers.json.
#   - Extra columns are ignored.
#
# OUTPUT
#   A CSV with one row per firm-fiscal-year, columns:
#       cik, ticker, company_name, fiscal_year, filing_date, sic,
#       total_revenue, cogs, gross_profit, operating_income, net_income,
#       total_assets, total_liabilities, shareholders_equity,
#       cash_and_equivalents, capex, rd_expense
#   plus provenance columns (safe to delete if you don't want them):
#       fiscal_period_end, form_type, accession_number, sic_description,
#       data_source, missing_fields
#   Missing values are written as empty cells.
#
# FISCAL YEAR CONVENTION  (important - read this)
#   A 10-K's period end date is mapped to a fiscal year label using
#   --fy-convention:
#     "compustat" (default): FY = year of period end if the period ends in
#         June-December, else year-1. This matches Compustat's DATADATE/FYEAR
#         rule, so e.g. Walmart's period ending 2024-01-31 becomes FY2023.
#         Use this if you plan to merge with Compustat/CRSP.
#     "calendar": FY = calendar year of the period end date, always.
#   The raw period end is always kept in `fiscal_period_end` so you can
#   re-label after the fact.
#
# RATE LIMITING / ETIQUETTE
#   SEC asks for a descriptive User-Agent with contact info and caps traffic at
#   ~10 requests/second. Defaults here are conservative (~5 req/s). Do not
#   raise --rate-limit above 0.1 without good reason. Responses are cached on
#   disk so re-runs are nearly free.
#
# LIMITATIONS (be aware of these before using the output in a paper)
#   - Only consolidated, non-dimensional facts are used. Segment-level and
#     geographic breakdowns are ignored by design.
#   - Values are as-reported in the *latest* 10-K covering that period, so
#     restatements are reflected. Set --prefer-original to take the earliest
#     reported value instead.
#   - Revenue/COGS tag choice varies by filer; the fallback ladders below are
#     good but not perfect. Spot-check a random sample against the filings.
#   - `capex` is the cash-flow-statement purchases-of-PP&E line, which for some
#     filers excludes capitalized software or acquired assets.
#   - No currency conversion. Only USD-denominated facts are collected; foreign
#     private issuers filing 20-F are out of scope entirely.
# -----------------------------------------------------------------------------

import argparse
import csv
import gzip
import hashlib
import json
import logging
import os
import re
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from datetime import date, datetime
from typing import Any, Dict, Iterable, List, Optional, Tuple

# =============================================================================
# CONFIG - adjust these (or override on the command line)
# =============================================================================

# >>> ADJUST: SEC requires a User-Agent identifying you, with contact info.
#     Format: "Organization Name contact@example.com"
DEFAULT_USER_AGENT = "Research Project PLACEHOLDER-NAME placeholder@example.edu"

# >>> ADJUST: input CSV path (columns: ticker, cik)
DEFAULT_INPUT_PATH = "firms.csv"

# >>> ADJUST: output CSV path
DEFAULT_OUTPUT_PATH = "firm_year_financials.csv"

# >>> ADJUST: minimum seconds between HTTP requests. SEC's ceiling is 10 req/s
#     (0.10s). 0.20s = 5 req/s and is a safe default for long unattended runs.
DEFAULT_RATE_LIMIT_SECONDS = 0.20

# >>> ADJUST: on-disk HTTP cache. Delete this directory to force a refetch.
#     Set --no-cache to disable. companyfacts payloads can be 10-50 MB each,
#     so budget disk space accordingly for a large universe.
DEFAULT_CACHE_DIR = ".edgar_cache"

# >>> ADJUST: fiscal year range
DEFAULT_START_YEAR = 2020
DEFAULT_END_YEAR = 2024

# Network retry behaviour
MAX_RETRIES = 4
RETRY_BACKOFF_SECONDS = 2.0
REQUEST_TIMEOUT_SECONDS = 60

# Which forms count as an annual report
ANNUAL_FORMS = ("10-K", "10-K/A", "10-K405", "10-KSB", "10-KT")

# How many days a period end may differ from the 10-K's period-of-report and
# still be considered the same fiscal period (filers sometimes use 52/53-week
# calendars, so the XBRL end date can drift a few days from reportDate).
PERIOD_END_TOLERANCE_DAYS = 10

# Acceptable length of an "annual" duration fact, in days.
ANNUAL_MIN_DAYS = 300
ANNUAL_MAX_DAYS = 430

SUBMISSIONS_URL = "https://data.sec.gov/submissions/CIK{cik10}.json"
SUBMISSIONS_PAGE_URL = "https://data.sec.gov/submissions/{name}"
COMPANYFACTS_URL = "https://data.sec.gov/api/xbrl/companyfacts/CIK{cik10}.json"
COMPANY_TICKERS_URL = "https://www.sec.gov/files/company_tickers.json"
FILING_DIR_INDEX_URL = (
    "https://www.sec.gov/Archives/edgar/data/{cik_int}/{accn_nodash}/index.json"
)
FILING_FILE_URL = (
    "https://www.sec.gov/Archives/edgar/data/{cik_int}/{accn_nodash}/{filename}"
)

# =============================================================================
# Tag mapping
# =============================================================================
# Each output field maps to an ordered list of us-gaap tags. The first tag that
# yields a value for the period wins, so put the most specific / most modern
# tag first. ASC 606 (2018+) pushed most filers onto the
# RevenueFromContractWithCustomer* tags; older or unusual filers still use
# Revenues / SalesRevenueNet.
#
# "duration" = income statement / cash flow item (has start and end dates)
# "instant"  = balance sheet item (has an end date only)

DURATION_TAGS: Dict[str, List[str]] = {
    "total_revenue": [
        "RevenueFromContractWithCustomerExcludingAssessedTax",
        "RevenueFromContractWithCustomerIncludingAssessedTax",
        "Revenues",
        "SalesRevenueNet",
        "SalesRevenueGoodsNet",
        "SalesRevenueServicesNet",
        "RevenuesNetOfInterestExpense",  # banks / broker-dealers
        "RegulatedAndUnregulatedOperatingRevenue",  # utilities
    ],
    "cogs": [
        "CostOfGoodsAndServicesSold",
        "CostOfRevenue",
        "CostOfGoodsSold",
        "CostOfServices",
        "CostOfGoodsAndServicesSoldExcludingDepreciationDepletionAndAmortization",
    ],
    "gross_profit": [
        "GrossProfit",
    ],
    "operating_income": [
        "OperatingIncomeLoss",
        "IncomeLossFromContinuingOperationsBeforeIncomeTaxesExtraordinaryItemsNoncontrollingInterest",
    ],
    "net_income": [
        "NetIncomeLoss",
        "ProfitLoss",
        "NetIncomeLossAvailableToCommonStockholdersBasic",
        "IncomeLossFromContinuingOperations",
    ],
    "capex": [
        "PaymentsToAcquirePropertyPlantAndEquipment",
        "PaymentsToAcquireProductiveAssets",
        "PaymentsToAcquirePropertyPlantAndEquipmentAndIntangibleAssets",
        "PaymentsForCapitalImprovements",
        "PaymentsToAcquireOtherPropertyPlantAndEquipment",
        "PaymentsToAcquireMachineryAndEquipment",
    ],
    "rd_expense": [
        "ResearchAndDevelopmentExpense",
        "ResearchAndDevelopmentExpenseExcludingAcquiredInProcessCost",
        "ResearchAndDevelopmentExpenseSoftwareExcludingAcquiredInProcessCost",
    ],
}

INSTANT_TAGS: Dict[str, List[str]] = {
    "total_assets": [
        "Assets",
    ],
    "total_liabilities": [
        "Liabilities",
    ],
    "shareholders_equity": [
        "StockholdersEquity",
        "StockholdersEquityIncludingPortionAttributableToNoncontrollingInterest",
        "MembersEquity",
        "PartnersCapital",
    ],
    "cash_and_equivalents": [
        "CashAndCashEquivalentsAtCarryingValue",
        "CashCashEquivalentsRestrictedCashAndRestrictedCashEquivalents",
        "CashAndCashEquivalentsAtCarryingValueIncludingDiscontinuedOperations",
        "CashCashEquivalentsAndShortTermInvestments",
    ],
    # Helper tags used only for deriving total_liabilities when `Liabilities`
    # is absent (common for banks and for filers using a classified balance
    # sheet without the summary line).
    "_equity_incl_nci": [
        "StockholdersEquityIncludingPortionAttributableToNoncontrollingInterest",
        "StockholdersEquity",
    ],
    "_liabilities_and_equity": [
        "LiabilitiesAndStockholdersEquity",
    ],
}

# Column order of the output CSV.
OUTPUT_COLUMNS = [
    "cik",
    "ticker",
    "company_name",
    "fiscal_year",
    "filing_date",
    "sic",
    "total_revenue",
    "cogs",
    "gross_profit",
    "operating_income",
    "net_income",
    "total_assets",
    "total_liabilities",
    "shareholders_equity",
    "cash_and_equivalents",
    "capex",
    "rd_expense",
    # --- provenance columns; delete these from the list if you don't want them
    "fiscal_period_end",
    "form_type",
    "accession_number",
    "sic_description",
    "data_source",
    "missing_fields",
]

LOG = logging.getLogger("edgar")


# =============================================================================
# HTTP layer: throttling, retries, caching
# =============================================================================


class EdgarClient:
    """Minimal throttled + cached HTTP client for SEC endpoints."""

    def __init__(
        self,
        user_agent: str,
        rate_limit_seconds: float,
        cache_dir: Optional[str],
    ):
        self.user_agent = user_agent
        self.rate_limit_seconds = rate_limit_seconds
        self.cache_dir = cache_dir
        self._last_request_ts = 0.0
        if self.cache_dir:
            os.makedirs(self.cache_dir, exist_ok=True)

    # -- cache helpers -------------------------------------------------------

    def _cache_path(self, url: str) -> Optional[str]:
        if not self.cache_dir:
            return None
        digest = hashlib.sha256(url.encode("utf-8")).hexdigest()[:32]
        return os.path.join(self.cache_dir, digest)

    # -- throttle ------------------------------------------------------------

    def _throttle(self) -> None:
        elapsed = time.monotonic() - self._last_request_ts
        wait = self.rate_limit_seconds - elapsed
        if wait > 0:
            time.sleep(wait)
        self._last_request_ts = time.monotonic()

    # -- core fetch ----------------------------------------------------------

    def get(self, url: str, allow_404: bool = True) -> Optional[bytes]:
        """Fetch a URL. Returns raw bytes, or None on a 404/permanent failure."""
        cache_path = self._cache_path(url)
        if cache_path and os.path.exists(cache_path):
            with open(cache_path, "rb") as fh:
                payload = fh.read()
            # A zero-byte cache entry records a previous 404.
            return payload if payload else None

        request = urllib.request.Request(
            url,
            headers={
                "User-Agent": self.user_agent,
                "Accept-Encoding": "gzip, deflate",
                "Accept": "application/json, text/html, */*",
            },
        )

        last_error: Optional[str] = None
        for attempt in range(1, MAX_RETRIES + 1):
            self._throttle()
            try:
                with urllib.request.urlopen(
                    request, timeout=REQUEST_TIMEOUT_SECONDS
                ) as response:
                    raw = response.read()
                    if response.headers.get("Content-Encoding") == "gzip":
                        raw = gzip.decompress(raw)
                if cache_path:
                    with open(cache_path, "wb") as fh:
                        fh.write(raw)
                return raw

            except urllib.error.HTTPError as exc:
                if exc.code == 404 and allow_404:
                    LOG.debug("404 for %s", url)
                    if cache_path:  # remember the 404 so we don't refetch
                        open(cache_path, "wb").close()
                    return None
                if exc.code in (403, 429, 500, 502, 503, 504):
                    last_error = f"HTTP {exc.code}"
                    sleep_for = RETRY_BACKOFF_SECONDS * (2 ** (attempt - 1))
                    LOG.warning(
                        "%s on %s (attempt %d/%d), backing off %.1fs",
                        last_error, url, attempt, MAX_RETRIES, sleep_for,
                    )
                    time.sleep(sleep_for)
                    continue
                last_error = f"HTTP {exc.code}"
                break

            except (urllib.error.URLError, TimeoutError, OSError) as exc:
                last_error = f"{type(exc).__name__}: {exc}"
                sleep_for = RETRY_BACKOFF_SECONDS * (2 ** (attempt - 1))
                LOG.warning(
                    "network error on %s (attempt %d/%d): %s; retrying in %.1fs",
                    url, attempt, MAX_RETRIES, last_error, sleep_for,
                )
                time.sleep(sleep_for)

        LOG.error("giving up on %s (%s)", url, last_error)
        return None

    def get_json(self, url: str) -> Optional[Any]:
        raw = self.get(url)
        if raw is None:
            return None
        try:
            return json.loads(raw.decode("utf-8", errors="replace"))
        except json.JSONDecodeError as exc:
            LOG.error("malformed JSON from %s: %s", url, exc)
            return None


# =============================================================================
# Small utilities
# =============================================================================


def normalize_cik(raw: Any) -> Optional[str]:
    """Return a 10-digit zero-padded CIK string, or None if unparseable."""
    if raw is None:
        return None
    text = str(raw).strip().upper()
    if not text:
        return None
    text = text[3:] if text.startswith("CIK") else text
    text = text.lstrip("-").strip()
    digits = re.sub(r"\D", "", text)
    if not digits:
        return None
    return digits.zfill(10)


def parse_date(text: Optional[str]) -> Optional[date]:
    if not text:
        return None
    try:
        return datetime.strptime(text[:10], "%Y-%m-%d").date()
    except ValueError:
        return None


def fiscal_year_for(period_end: date, convention: str) -> int:
    """Map a fiscal period end date to a fiscal year label."""
    if convention == "calendar":
        return period_end.year
    # Compustat rule: periods ending Jan-May belong to the prior fiscal year.
    return period_end.year if period_end.month >= 6 else period_end.year - 1


def days_between(a: date, b: date) -> int:
    return abs((a - b).days)


# =============================================================================
# Step 1 - firm universe
# =============================================================================


def load_firm_list(path: str) -> List[Dict[str, str]]:
    """Read the input CSV. Requires a `ticker` and/or `cik` column."""
    firms: List[Dict[str, str]] = []
    with open(path, "r", encoding="utf-8-sig", newline="") as fh:
        reader = csv.DictReader(fh)
        if reader.fieldnames is None:
            raise ValueError(f"{path} appears to be empty")
        lowered = {name.lower().strip(): name for name in reader.fieldnames}
        if "ticker" not in lowered and "cik" not in lowered:
            raise ValueError(
                f"{path} must have a 'ticker' and/or 'cik' column; "
                f"found {reader.fieldnames}"
            )
        for row_number, row in enumerate(reader, start=2):
            ticker = (row.get(lowered.get("ticker", ""), "") or "").strip().upper()
            cik = normalize_cik(row.get(lowered.get("cik", ""), ""))
            if not ticker and not cik:
                LOG.warning("input row %d has neither ticker nor cik; skipping", row_number)
                continue
            firms.append({"ticker": ticker, "cik": cik or ""})
    LOG.info("loaded %d firms from %s", len(firms), path)
    return firms


def build_ticker_to_cik_map(client: EdgarClient) -> Dict[str, str]:
    """Fetch SEC's official ticker -> CIK mapping (one small request)."""
    data = client.get_json(COMPANY_TICKERS_URL)
    if not data:
        LOG.warning("could not fetch company_tickers.json; ticker-only rows will fail")
        return {}
    mapping: Dict[str, str] = {}
    for entry in data.values():
        ticker = str(entry.get("ticker", "")).strip().upper()
        cik = normalize_cik(entry.get("cik_str"))
        if ticker and cik:
            mapping[ticker] = cik
    LOG.info("resolved ticker->CIK map with %d entries", len(mapping))
    return mapping


# =============================================================================
# Step 2 - locate 10-K filings for a CIK
# =============================================================================


def fetch_submissions(client: EdgarClient, cik10: str) -> Optional[Dict[str, Any]]:
    return client.get_json(SUBMISSIONS_URL.format(cik10=cik10))


def iter_filing_rows(filings_block: Dict[str, Any]) -> Iterable[Dict[str, str]]:
    """Turn EDGAR's column-oriented filing arrays into row dicts."""
    forms = filings_block.get("form") or []
    count = len(forms)
    columns = {
        key: filings_block.get(key) or [None] * count
        for key in (
            "form",
            "filingDate",
            "reportDate",
            "accessionNumber",
            "primaryDocument",
            "isXBRL",
        )
    }
    for i in range(count):
        yield {key: values[i] if i < len(values) else None
               for key, values in columns.items()}


def collect_annual_filings(
    client: EdgarClient,
    cik10: str,
    submissions: Dict[str, Any],
    start_year: int,
    end_year: int,
    fy_convention: str,
    include_amendments: bool,
) -> Dict[int, Dict[str, Any]]:
    """
    Return {fiscal_year: filing_record} for 10-Ks whose fiscal year falls in
    [start_year, end_year]. If a fiscal year has multiple 10-Ks (original plus
    amendments, or a transition period), the one filed most recently wins.
    """
    allowed_forms = set(ANNUAL_FORMS) if include_amendments else {
        f for f in ANNUAL_FORMS if not f.endswith("/A")
    }

    rows: List[Dict[str, str]] = []
    filings = submissions.get("filings") or {}
    rows.extend(iter_filing_rows(filings.get("recent") or {}))

    # `filings.recent` holds roughly the last 1,000 filings. Prolific filers
    # need the paginated older files too.
    for extra in filings.get("files") or []:
        name = extra.get("name")
        if not name:
            continue
        # Skip pages entirely outside our window where we can tell cheaply.
        page_end = parse_date(extra.get("filingTo"))
        if page_end and page_end.year < start_year:
            continue
        page = client.get_json(SUBMISSIONS_PAGE_URL.format(name=name))
        if page:
            rows.extend(iter_filing_rows(page))

    best_by_year: Dict[int, Dict[str, Any]] = {}
    for row in rows:
        form = (row.get("form") or "").strip()
        if form not in allowed_forms:
            continue
        period_end = parse_date(row.get("reportDate"))
        filing_date = parse_date(row.get("filingDate"))
        if period_end is None:
            LOG.debug("CIK %s: %s filing with no reportDate; skipping", cik10, form)
            continue
        fy = fiscal_year_for(period_end, fy_convention)
        if not (start_year <= fy <= end_year):
            continue

        record = {
            "fiscal_year": fy,
            "period_end": period_end,
            "filing_date": filing_date,
            "form": form,
            "accession": (row.get("accessionNumber") or "").strip(),
        }
        incumbent = best_by_year.get(fy)
        if incumbent is None:
            best_by_year[fy] = record
            continue
        # Prefer the later filing date; break ties by preferring the later
        # period end (handles transition periods).
        incumbent_key = (incumbent["filing_date"] or date.min, incumbent["period_end"])
        candidate_key = (filing_date or date.min, period_end)
        if candidate_key > incumbent_key:
            best_by_year[fy] = record

    return best_by_year


# =============================================================================
# Step 3 - XBRL facts from the companyfacts API
# =============================================================================


def fetch_company_facts(client: EdgarClient, cik10: str) -> Optional[Dict[str, Any]]:
    return client.get_json(COMPANYFACTS_URL.format(cik10=cik10))


def index_company_facts(company_facts: Dict[str, Any]) -> Dict[str, List[Dict[str, Any]]]:
    """
    Flatten companyfacts into {tag_local_name: [fact, ...]} keeping only
    USD-denominated us-gaap facts. Each fact is normalized to:
        {start: date|None, end: date, val: float, form: str,
         filed: date|None, accn: str}
    """
    index: Dict[str, List[Dict[str, Any]]] = {}
    us_gaap = (company_facts.get("facts") or {}).get("us-gaap") or {}
    for tag, tag_body in us_gaap.items():
        units = tag_body.get("units") or {}
        # "USD" only; "USD/shares" and "shares" are per-share/count units we
        # don't want for any of the target variables.
        entries = units.get("USD")
        if not entries:
            continue
        normalized: List[Dict[str, Any]] = []
        for entry in entries:
            end = parse_date(entry.get("end"))
            value = entry.get("val")
            if end is None or value is None:
                continue
            try:
                value = float(value)
            except (TypeError, ValueError):
                continue
            normalized.append(
                {
                    "start": parse_date(entry.get("start")),
                    "end": end,
                    "val": value,
                    "form": (entry.get("form") or "").strip(),
                    "filed": parse_date(entry.get("filed")),
                    "accn": (entry.get("accn") or "").strip(),
                }
            )
        if normalized:
            index[tag] = normalized
    return index


def _rank_fact(fact: Dict[str, Any], target_accession: str, prefer_original: bool) -> Tuple:
    """Sort key: exact filing match first, then annual forms, then by date."""
    same_filing = 1 if fact.get("accn") == target_accession else 0
    annual_form = 1 if fact.get("form", "").startswith("10-K") else 0
    filed = fact.get("filed") or date.min
    date_rank = -filed.toordinal() if prefer_original else filed.toordinal()
    return (same_filing, annual_form, date_rank)


def select_duration_fact(
    facts: List[Dict[str, Any]],
    period_end: date,
    target_accession: str,
    prefer_original: bool,
) -> Optional[Dict[str, Any]]:
    """Pick the annual (≈365-day) fact whose period ends at `period_end`."""
    candidates = [
        f for f in facts
        if f["start"] is not None
        and days_between(f["end"], period_end) <= PERIOD_END_TOLERANCE_DAYS
        and ANNUAL_MIN_DAYS <= (f["end"] - f["start"]).days <= ANNUAL_MAX_DAYS
    ]
    if not candidates:
        return None
    return max(candidates, key=lambda f: _rank_fact(f, target_accession, prefer_original))


def select_instant_fact(
    facts: List[Dict[str, Any]],
    period_end: date,
    target_accession: str,
    prefer_original: bool,
) -> Optional[Dict[str, Any]]:
    """Pick the balance-sheet (point-in-time) fact as of `period_end`."""
    candidates = [
        f for f in facts
        if f["start"] is None
        and days_between(f["end"], period_end) <= PERIOD_END_TOLERANCE_DAYS
    ]
    if not candidates:
        return None
    return max(candidates, key=lambda f: _rank_fact(f, target_accession, prefer_original))


def extract_from_index(
    fact_index: Dict[str, List[Dict[str, Any]]],
    period_end: date,
    accession: str,
    prefer_original: bool,
) -> Dict[str, Optional[float]]:
    """Walk the tag ladders and pull one value per field."""
    values: Dict[str, Optional[float]] = {}

    for field, tags in DURATION_TAGS.items():
        values[field] = None
        for tag in tags:
            facts = fact_index.get(tag)
            if not facts:
                continue
            hit = select_duration_fact(facts, period_end, accession, prefer_original)
            if hit is not None:
                values[field] = hit["val"]
                LOG.debug("  %s <- us-gaap:%s = %s", field, tag, hit["val"])
                break

    for field, tags in INSTANT_TAGS.items():
        values[field] = None
        for tag in tags:
            facts = fact_index.get(tag)
            if not facts:
                continue
            hit = select_instant_fact(facts, period_end, accession, prefer_original)
            if hit is not None:
                values[field] = hit["val"]
                LOG.debug("  %s <- us-gaap:%s = %s", field, tag, hit["val"])
                break

    return values


def apply_derivations(values: Dict[str, Optional[float]]) -> Dict[str, Optional[float]]:
    """
    Fill gaps using accounting identities. Only fires when the tagged value is
    genuinely absent - a reported value is never overwritten.
    """
    # Gross profit = revenue - COGS
    if values.get("gross_profit") is None:
        revenue, cogs = values.get("total_revenue"), values.get("cogs")
        if revenue is not None and cogs is not None:
            values["gross_profit"] = revenue - cogs

    # COGS = revenue - gross profit (some filers tag GrossProfit but not COGS)
    if values.get("cogs") is None:
        revenue, gross = values.get("total_revenue"), values.get("gross_profit")
        if revenue is not None and gross is not None:
            values["cogs"] = revenue - gross

    # Total liabilities = (liabilities + equity) - equity, or assets - equity.
    if values.get("total_liabilities") is None:
        equity = values.get("_equity_incl_nci")
        base = values.get("_liabilities_and_equity") or values.get("total_assets")
        if base is not None and equity is not None:
            values["total_liabilities"] = base - equity

    # Capex is a cash outflow; some filers tag it positive, some negative.
    # Normalize to a positive magnitude so cross-firm comparisons work.
    if values.get("capex") is not None:
        values["capex"] = abs(values["capex"])

    # Drop internal helper keys before writing.
    for helper in ("_equity_incl_nci", "_liabilities_and_equity"):
        values.pop(helper, None)
    return values


# =============================================================================
# Step 4 - fallback: parse the raw XBRL instance document in the filing
# =============================================================================
# Used only when companyfacts has no usable data for a firm-year. Modern 10-Ks
# are inline XBRL, and EDGAR publishes an extracted instance (e.g.
# `aapl-20240928_htm.xml`) alongside the filing; that's what we parse here.

XBRLI_NS = "http://www.xbrl.org/2003/instance"
_INSTANCE_SKIP_SUFFIXES = ("_cal.xml", "_def.xml", "_lab.xml", "_pre.xml", "_ref.xml")


def find_instance_document(
    client: EdgarClient, cik10: str, accession: str
) -> Optional[str]:
    """Locate the XBRL instance file inside a filing's EDGAR directory."""
    accn_nodash = accession.replace("-", "")
    cik_int = str(int(cik10))
    listing = client.get_json(
        FILING_DIR_INDEX_URL.format(cik_int=cik_int, accn_nodash=accn_nodash)
    )
    if not listing:
        return None
    names = [
        item.get("name", "")
        for item in ((listing.get("directory") or {}).get("item") or [])
    ]
    candidates = [
        n for n in names
        if n.lower().endswith(".xml")
        and not n.lower().endswith(_INSTANCE_SKIP_SUFFIXES)
        and n != "FilingSummary.xml"
        and not re.match(r"^R\d+\.xml$", n)
    ]
    # The extracted inline-XBRL instance is conventionally named *_htm.xml.
    for name in candidates:
        if name.lower().endswith("_htm.xml"):
            return name
    return candidates[0] if candidates else None


def parse_instance_facts(xml_bytes: bytes) -> Dict[str, List[Dict[str, Any]]]:
    """
    Parse an XBRL instance into the same {tag: [fact, ...]} shape as
    index_company_facts. Contexts carrying dimensions (segment/scenario) are
    skipped so we only keep consolidated totals.
    """
    try:
        root = ET.fromstring(xml_bytes)
    except ET.ParseError as exc:
        LOG.warning("could not parse XBRL instance: %s", exc)
        return {}

    contexts: Dict[str, Dict[str, Optional[date]]] = {}
    for context in root.findall(f"{{{XBRLI_NS}}}context"):
        context_id = context.get("id")
        if not context_id:
            continue
        entity = context.find(f"{{{XBRLI_NS}}}entity")
        if entity is not None and entity.find(f"{{{XBRLI_NS}}}segment") is not None:
            continue  # dimensional fact, not a consolidated total
        if context.find(f"{{{XBRLI_NS}}}scenario") is not None:
            continue
        period = context.find(f"{{{XBRLI_NS}}}period")
        if period is None:
            continue
        instant = period.find(f"{{{XBRLI_NS}}}instant")
        if instant is not None:
            contexts[context_id] = {"start": None, "end": parse_date(instant.text)}
        else:
            start = period.find(f"{{{XBRLI_NS}}}startDate")
            end = period.find(f"{{{XBRLI_NS}}}endDate")
            if start is None or end is None:
                continue
            contexts[context_id] = {
                "start": parse_date(start.text),
                "end": parse_date(end.text),
            }

    index: Dict[str, List[Dict[str, Any]]] = {}
    for element in root.iter():
        tag = element.tag
        if not tag.startswith("{") or "us-gaap" not in tag:
            continue
        local_name = tag.split("}", 1)[1]
        context_id = element.get("contextRef")
        if not context_id or context_id not in contexts:
            continue
        if not element.get("unitRef"):
            continue  # non-numeric fact
        text = (element.text or "").strip().replace(",", "")
        if not text:
            continue
        try:
            value = float(text)
        except ValueError:
            continue
        if element.get("sign") == "-":
            value = -value
        period = contexts[context_id]
        if period["end"] is None:
            continue
        index.setdefault(local_name, []).append(
            {
                "start": period["start"],
                "end": period["end"],
                "val": value,
                "form": "10-K",
                "filed": None,
                "accn": "",
            }
        )
    return index


def fetch_instance_index(
    client: EdgarClient, cik10: str, accession: str
) -> Dict[str, List[Dict[str, Any]]]:
    filename = find_instance_document(client, cik10, accession)
    if not filename:
        return {}
    raw = client.get(
        FILING_FILE_URL.format(
            cik_int=str(int(cik10)),
            accn_nodash=accession.replace("-", ""),
            filename=filename,
        )
    )
    if raw is None:
        return {}
    LOG.info("  fallback: parsing instance document %s", filename)
    return parse_instance_facts(raw)


# =============================================================================
# Step 5 - per-firm orchestration
# =============================================================================

# Fields we consider "core"; if all of these are missing we treat the firm-year
# as a failure rather than emitting a near-empty row.
CORE_FIELDS = ("total_revenue", "net_income", "total_assets")


def process_firm(
    client: EdgarClient,
    firm: Dict[str, str],
    args: argparse.Namespace,
    stats: Dict[str, int],
) -> List[Dict[str, Any]]:
    """Return a list of output rows for one firm. Never raises."""
    cik10 = firm["cik"]
    ticker = firm.get("ticker", "")
    label = f"{ticker or '?'} (CIK {cik10})"

    submissions = fetch_submissions(client, cik10)
    if not submissions:
        LOG.error("%s: submissions JSON unavailable; skipping firm", label)
        stats["firms_failed"] += 1
        return []

    company_name = (submissions.get("name") or "").strip()
    sic = (submissions.get("sic") or "").strip()
    sic_description = (submissions.get("sicDescription") or "").strip()
    if not ticker:
        exchange_tickers = submissions.get("tickers") or []
        ticker = exchange_tickers[0] if exchange_tickers else ""

    filings_by_year = collect_annual_filings(
        client,
        cik10,
        submissions,
        args.start_year,
        args.end_year,
        args.fy_convention,
        args.include_amendments,
    )

    requested_years = list(range(args.start_year, args.end_year + 1))
    for year in requested_years:
        if year not in filings_by_year:
            LOG.warning("%s: no 10-K found for fiscal year %d", label, year)
            stats["missing_filing"] += 1

    if not filings_by_year:
        stats["firms_failed"] += 1
        return []

    company_facts = fetch_company_facts(client, cik10)
    if company_facts:
        fact_index = index_company_facts(company_facts)
    else:
        LOG.warning("%s: companyfacts XBRL not available; will try per-filing fallback",
                    label)
        fact_index = {}

    rows: List[Dict[str, Any]] = []
    for year in sorted(filings_by_year):
        filing = filings_by_year[year]
        period_end = filing["period_end"]
        accession = filing["accession"]
        source = "companyfacts"

        values: Dict[str, Optional[float]] = {}
        if fact_index:
            values = extract_from_index(
                fact_index, period_end, accession, args.prefer_original
            )

        core_present = any(values.get(f) is not None for f in CORE_FIELDS)
        if not core_present:
            LOG.info("%s FY%d: companyfacts had nothing usable; trying instance doc",
                     label, year)
            fallback_index = fetch_instance_index(client, cik10, accession)
            if fallback_index:
                fallback_values = extract_from_index(
                    fallback_index, period_end, accession, args.prefer_original
                )
                # Merge: fallback fills only what companyfacts left empty.
                for key, val in fallback_values.items():
                    if values.get(key) is None and val is not None:
                        values[key] = val
                source = "xbrl_instance" if values else source

        values = apply_derivations(values)

        missing = [
            field for field in OUTPUT_COLUMNS
            if field in DURATION_TAGS or field in INSTANT_TAGS
            if values.get(field) is None
        ]

        if not any(values.get(f) is not None for f in CORE_FIELDS):
            disposition = "row emitted empty" if args.emit_empty_rows else "row skipped"
            LOG.error(
                "%s FY%d: no core financials extracted (accession %s); %s",
                label, year, accession, disposition,
            )
            stats["years_failed"] += 1
            if not args.emit_empty_rows:
                continue
        else:
            stats["years_ok"] += 1
            LOG.info(
                "%s FY%d: ok (period end %s, %d/%d fields populated)",
                label, year, period_end.isoformat(),
                len(DURATION_TAGS) + len(INSTANT_TAGS) - 2 - len(missing),
                len(DURATION_TAGS) + len(INSTANT_TAGS) - 2,
            )

        rows.append(
            {
                "cik": cik10,
                "ticker": ticker,
                "company_name": company_name,
                "fiscal_year": year,
                "filing_date": filing["filing_date"].isoformat()
                if filing["filing_date"] else "",
                "sic": sic,
                "total_revenue": values.get("total_revenue"),
                "cogs": values.get("cogs"),
                "gross_profit": values.get("gross_profit"),
                "operating_income": values.get("operating_income"),
                "net_income": values.get("net_income"),
                "total_assets": values.get("total_assets"),
                "total_liabilities": values.get("total_liabilities"),
                "shareholders_equity": values.get("shareholders_equity"),
                "cash_and_equivalents": values.get("cash_and_equivalents"),
                "capex": values.get("capex"),
                "rd_expense": values.get("rd_expense"),
                "fiscal_period_end": period_end.isoformat(),
                "form_type": filing["form"],
                "accession_number": accession,
                "sic_description": sic_description,
                "data_source": source,
                "missing_fields": ";".join(missing),
            }
        )

    stats["firms_ok"] += 1
    return rows


# =============================================================================
# CLI + main
# =============================================================================


def configure_logging(log_file: Optional[str], verbose: bool) -> None:
    handlers: List[logging.Handler] = [logging.StreamHandler(sys.stderr)]
    if log_file:
        handlers.append(logging.FileHandler(log_file, mode="w", encoding="utf-8"))
    logging.basicConfig(
        level=logging.DEBUG if verbose else logging.INFO,
        format="%(asctime)s %(levelname)-7s %(message)s",
        datefmt="%H:%M:%S",
        handlers=handlers,
    )


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Collect annual financials from SEC EDGAR 10-K filings.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--input", default=DEFAULT_INPUT_PATH,
                        help="input CSV with ticker and/or cik columns")
    parser.add_argument("--output", default=DEFAULT_OUTPUT_PATH,
                        help="output CSV path")
    parser.add_argument("--start-year", type=int, default=DEFAULT_START_YEAR)
    parser.add_argument("--end-year", type=int, default=DEFAULT_END_YEAR)
    parser.add_argument("--user-agent", default=DEFAULT_USER_AGENT,
                        help="SEC requires 'Name email@domain' contact info")
    parser.add_argument("--rate-limit", type=float,
                        default=DEFAULT_RATE_LIMIT_SECONDS,
                        help="minimum seconds between HTTP requests")
    parser.add_argument("--cache-dir", default=DEFAULT_CACHE_DIR,
                        help="directory for the on-disk HTTP cache")
    parser.add_argument("--no-cache", action="store_true",
                        help="disable the HTTP cache entirely")
    parser.add_argument("--fy-convention", choices=("compustat", "calendar"),
                        default="compustat",
                        help="how period end dates map to fiscal year labels")
    parser.add_argument("--include-amendments", action="store_true",
                        help="also consider 10-K/A amendments")
    parser.add_argument("--prefer-original", action="store_true",
                        help="use as-first-reported values instead of restated")
    parser.add_argument("--emit-empty-rows", action="store_true",
                        help="write a row even when no financials were found")
    parser.add_argument("--limit", type=int, default=None,
                        help="process only the first N firms (for testing)")
    parser.add_argument("--log-file", default=None,
                        help="also write logs to this file")
    parser.add_argument("--verbose", action="store_true",
                        help="DEBUG-level logging, incl. which tag fed each field")
    return parser


def main(argv: Optional[List[str]] = None) -> int:
    args = build_arg_parser().parse_args(argv)
    configure_logging(args.log_file, args.verbose)

    if "PLACEHOLDER" in args.user_agent:
        LOG.warning(
            "User-Agent still contains a placeholder. SEC may throttle or block "
            "you. Edit DEFAULT_USER_AGENT or pass --user-agent 'Name email@dom'."
        )
    if args.start_year > args.end_year:
        LOG.error("--start-year must be <= --end-year")
        return 2

    client = EdgarClient(
        user_agent=args.user_agent,
        rate_limit_seconds=args.rate_limit,
        cache_dir=None if args.no_cache else args.cache_dir,
    )

    try:
        firms = load_firm_list(args.input)
    except (OSError, ValueError) as exc:
        LOG.error("could not read input file: %s", exc)
        return 2

    if args.limit:
        firms = firms[: args.limit]

    needs_lookup = any(not firm["cik"] for firm in firms)
    ticker_map = build_ticker_to_cik_map(client) if needs_lookup else {}
    resolved: List[Dict[str, str]] = []
    for firm in firms:
        if not firm["cik"]:
            cik = ticker_map.get(firm["ticker"])
            if not cik:
                LOG.error("could not resolve CIK for ticker %s; skipping",
                          firm["ticker"] or "<blank>")
                continue
            firm["cik"] = cik
        resolved.append(firm)

    stats = {
        "firms_ok": 0,
        "firms_failed": 0,
        "years_ok": 0,
        "years_failed": 0,
        "missing_filing": 0,
    }

    output_dir = os.path.dirname(os.path.abspath(args.output))
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)

    started = time.time()
    total_rows = 0
    # Rows are streamed to disk as they are produced, so an interrupted run
    # still leaves usable partial output.
    with open(args.output, "w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=OUTPUT_COLUMNS, extrasaction="ignore")
        writer.writeheader()
        for position, firm in enumerate(resolved, start=1):
            LOG.info("[%d/%d] processing %s (CIK %s)",
                     position, len(resolved), firm["ticker"] or "?", firm["cik"])
            try:
                rows = process_firm(client, firm, args, stats)
            except Exception as exc:  # noqa: BLE001 - one firm must not kill the run
                LOG.exception("unhandled error on CIK %s: %s", firm["cik"], exc)
                stats["firms_failed"] += 1
                continue
            for row in rows:
                writer.writerow({
                    key: ("" if value is None else value) for key, value in row.items()
                })
            total_rows += len(rows)
            fh.flush()

    elapsed = time.time() - started
    LOG.info("-" * 68)
    LOG.info("done in %.1fs", elapsed)
    LOG.info("firms processed ok     : %d", stats["firms_ok"])
    LOG.info("firms failed           : %d", stats["firms_failed"])
    LOG.info("firm-years written     : %d", total_rows)
    LOG.info("firm-years with data   : %d", stats["years_ok"])
    LOG.info("firm-years w/o data    : %d", stats["years_failed"])
    LOG.info("requested years w/o 10-K: %d", stats["missing_filing"])
    LOG.info("output -> %s", os.path.abspath(args.output))
    return 0


if __name__ == "__main__":
    sys.exit(main())
