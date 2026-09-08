#!/usr/bin/env python3
# -----------------------------------------------------------------------------
# sec_edgar_10k_slim.py  -  compact variant of sec_edgar_10k_financials.py
#
# SETUP
#   pip install requests pandas requests-cache tqdm
#
# HOW TO RUN
#   python3 sec_edgar_10k_slim.py --input firms.csv --output panel.csv \
#       --start-year 2020 --end-year 2024 \
#       --user-agent "Your Name you@university.edu"
#
# INPUT   CSV with a `ticker` and/or `cik` column (blank ciks resolved by ticker)
# OUTPUT  CSV, one row per firm-fiscal-year, columns as listed in FIELDS below.
#         Missing values are empty cells.
#
# WHAT'S DIFFERENT FROM THE STDLIB VERSION
#   Same data path (submissions JSON + companyfacts XBRL API), same tag ladders,
#   same fiscal-year convention, same derived fields - roughly a quarter of the
#   code because the libraries absorb the boilerplate:
#     requests + urllib3 Retry  -> retry/backoff, gzip, timeouts
#     requests-cache            -> transparent on-disk HTTP cache
#     pandas                    -> fact filtering/ranking, CSV I/O
#   DROPPED: the raw-XBRL-instance fallback parser. Firm-years with no usable
#   companyfacts data are logged and skipped instead. For a 2020+ sample this
#   costs you almost nothing (>99% of 10-K filers tag XBRL); if you extend the
#   panel back before ~2011, use the full version instead.
# -----------------------------------------------------------------------------

import argparse, logging, re, sys, time
import pandas as pd, requests, requests_cache
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from tqdm import tqdm

# ============================ ADJUST THESE ===================================
UA         = "Research Project PLACEHOLDER you@example.edu"  # SEC requires contact info
IN_PATH    = "firms.csv"          # input CSV path
OUT_PATH   = "firm_year_financials.csv"  # output CSV path
RATE_LIMIT = 0.20                 # seconds between requests (SEC cap is 10/s = 0.10)
CACHE_NAME = "edgar_cache"        # sqlite HTTP cache; delete the .sqlite to refetch
# =============================================================================

TOL, ANNUAL = 10, (300, 430)      # period-end tolerance (days); annual duration window

# Ordered tag ladders: first tag that yields a value for the period wins.
DUR = {  # income statement / cash flow (duration facts)
    "total_revenue": ["RevenueFromContractWithCustomerExcludingAssessedTax",
        "RevenueFromContractWithCustomerIncludingAssessedTax", "Revenues",
        "SalesRevenueNet", "SalesRevenueGoodsNet", "SalesRevenueServicesNet",
        "RevenuesNetOfInterestExpense", "RegulatedAndUnregulatedOperatingRevenue"],
    "cogs": ["CostOfGoodsAndServicesSold", "CostOfRevenue", "CostOfGoodsSold",
        "CostOfServices",
        "CostOfGoodsAndServicesSoldExcludingDepreciationDepletionAndAmortization"],
    "gross_profit": ["GrossProfit"],
    "operating_income": ["OperatingIncomeLoss",
        "IncomeLossFromContinuingOperationsBeforeIncomeTaxesExtraordinaryItemsNoncontrollingInterest"],
    "net_income": ["NetIncomeLoss", "ProfitLoss",
        "NetIncomeLossAvailableToCommonStockholdersBasic",
        "IncomeLossFromContinuingOperations"],
    "capex": ["PaymentsToAcquirePropertyPlantAndEquipment",
        "PaymentsToAcquireProductiveAssets",
        "PaymentsToAcquirePropertyPlantAndEquipmentAndIntangibleAssets",
        "PaymentsForCapitalImprovements",
        "PaymentsToAcquireOtherPropertyPlantAndEquipment"],
    "rd_expense": ["ResearchAndDevelopmentExpense",
        "ResearchAndDevelopmentExpenseExcludingAcquiredInProcessCost"],
}
INST = {  # balance sheet (instant facts)
    "total_assets": ["Assets"],
    "total_liabilities": ["Liabilities"],
    "shareholders_equity": ["StockholdersEquity",
        "StockholdersEquityIncludingPortionAttributableToNoncontrollingInterest",
        "MembersEquity", "PartnersCapital"],
    "cash_and_equivalents": ["CashAndCashEquivalentsAtCarryingValue",
        "CashCashEquivalentsRestrictedCashAndRestrictedCashEquivalents",
        "CashAndCashEquivalentsAtCarryingValueIncludingDiscontinuedOperations"],
    # helpers, used only to derive total_liabilities; dropped before output
    "_eq_nci": ["StockholdersEquityIncludingPortionAttributableToNoncontrollingInterest",
        "StockholdersEquity"],
    "_liab_eq": ["LiabilitiesAndStockholdersEquity"],
}
# Output column order (kept explicit so it matches the full version exactly).
FIELDS = ["cik", "ticker", "company_name", "fiscal_year", "filing_date", "sic",
    "total_revenue", "cogs", "gross_profit", "operating_income", "net_income",
    "total_assets", "total_liabilities", "shareholders_equity",
    "cash_and_equivalents", "capex", "rd_expense",
    # provenance columns - delete from this list if you don't want them
    "fiscal_period_end", "form_type", "accession_number", "missing_fields"]
VARS = [f for f in FIELDS if f in DUR or f in INST]   # the 11 financial variables
CORE = ["total_revenue", "net_income", "total_assets"]

log = logging.getLogger("edgar")


def make_session(user_agent, cache_name):
    """Session with SEC headers, automatic retries, and a transparent disk cache."""
    s = (requests_cache.CachedSession(cache_name, expire_after=None,
                                      allowable_codes=[200, 404])
         if cache_name else requests.Session())
    s.headers.update({"User-Agent": user_agent, "Accept-Encoding": "gzip, deflate"})
    retry = Retry(total=4, backoff_factor=2,
                  status_forcelist=[403, 429, 500, 502, 503, 504],
                  allowed_methods=["GET"])
    s.mount("https://", HTTPAdapter(max_retries=retry))
    return s


def get(session, url, rate_limit):
    """GET -> parsed JSON, or None. Only sleeps on a real (uncached) request."""
    try:
        r = session.get(url, timeout=60)
        if not getattr(r, "from_cache", False):
            time.sleep(rate_limit)
        if r.status_code == 404:
            return None
        r.raise_for_status()
        return r.json()
    except Exception as e:                      # network, HTTP, or JSON failure
        log.error("fetch failed %s: %s", url, e)
        return None


def fiscal_year(end, convention):
    """Compustat rule: periods ending Jan-May belong to the prior fiscal year."""
    return end.year if (convention == "calendar" or end.month >= 6) else end.year - 1


def annual_filings(session, subs, args):
    """-> DataFrame of 10-K filings in range, one row per fiscal year (latest wins)."""
    frames = [pd.DataFrame(subs["filings"]["recent"])]
    for f in subs["filings"].get("files", []):   # older filings, paginated
        page = get(session, f"https://data.sec.gov/submissions/{f['name']}",
                   args.rate_limit)
        if page:
            frames.append(pd.DataFrame(page))
    df = pd.concat(frames, ignore_index=True)

    forms = ["10-K", "10-K405", "10-KSB", "10-KT"] + (["10-K/A"] if args.include_amendments else [])
    df = df[df.form.isin(forms)].copy()
    df["period_end"] = pd.to_datetime(df.reportDate, errors="coerce")
    df["filing_date"] = pd.to_datetime(df.filingDate, errors="coerce")
    df = df.dropna(subset=["period_end"])
    df["fy"] = df.period_end.map(lambda d: fiscal_year(d, args.fy_convention))
    df = df[df.fy.between(args.start_year, args.end_year)]
    # latest filing wins when a fiscal year has more than one 10-K
    return (df.sort_values(["fy", "filing_date", "period_end"])
              .groupby("fy", as_index=False).last())


def facts_frame(companyfacts):
    """Flatten companyfacts -> DataFrame of USD us-gaap facts."""
    rows = [dict(tag=tag, **f)
            for tag, body in companyfacts.get("facts", {}).get("us-gaap", {}).items()
            for f in body.get("units", {}).get("USD", [])]   # USD only: skips per-share
    df = pd.DataFrame(rows)
    if df.empty:
        return df
    for c in ("start", "end", "filed"):
        df[c] = pd.to_datetime(df.get(c), errors="coerce")
    df["days"] = (df.end - df.start).dt.days      # NaN for instant (balance sheet) facts
    return df


def pick(df, tags, period_end, duration, prefer_original):
    """First tag in the ladder with a fact matching the period; latest filed wins."""
    sub = df[df.tag.isin(tags) & ((df.end - period_end).dt.days.abs() <= TOL)]
    sub = sub[sub.days.between(*ANNUAL)] if duration else sub[sub.days.isna()]
    if sub.empty:
        return None
    rank = {t: i for i, t in enumerate(tags)}     # ladder position = priority
    sub = sub.assign(_r=sub.tag.map(rank)).sort_values(
        ["_r", "filed"], ascending=[True, bool(prefer_original)])
    return float(sub.iloc[0].val)


def extract(df, period_end, prefer_original):
    v = {f: pick(df, tags, period_end, True, prefer_original) for f, tags in DUR.items()}
    v |= {f: pick(df, tags, period_end, False, prefer_original) for f, tags in INST.items()}

    # Fill gaps via accounting identities; never overwrite a reported value.
    if v["gross_profit"] is None and None not in (v["total_revenue"], v["cogs"]):
        v["gross_profit"] = v["total_revenue"] - v["cogs"]
    if v["cogs"] is None and None not in (v["total_revenue"], v["gross_profit"]):
        v["cogs"] = v["total_revenue"] - v["gross_profit"]
    if v["total_liabilities"] is None:
        base = v["_liab_eq"] or v["total_assets"]
        if None not in (base, v["_eq_nci"]):
            v["total_liabilities"] = base - v["_eq_nci"]
    if v["capex"] is not None:
        v["capex"] = abs(v["capex"])              # normalize outflow sign
    return {k: val for k, val in v.items() if not k.startswith("_")}


def process_firm(session, cik, ticker, args):
    subs = get(session, f"https://data.sec.gov/submissions/CIK{cik}.json", args.rate_limit)
    if not subs:
        log.error("%s (CIK %s): submissions unavailable", ticker or "?", cik)
        return []
    label = f"{ticker or subs.get('name', '?')} (CIK {cik})"
    filings = annual_filings(session, subs, args)
    for y in range(args.start_year, args.end_year + 1):
        if y not in set(filings.fy):
            log.warning("%s: no 10-K found for fiscal year %d", label, y)
    if filings.empty:
        return []

    cf = get(session, f"https://data.sec.gov/api/xbrl/companyfacts/CIK{cik}.json",
             args.rate_limit)
    facts = facts_frame(cf) if cf else pd.DataFrame()
    if facts.empty:
        log.error("%s: XBRL companyfacts not available; skipping firm", label)
        return []

    rows = []
    for f in filings.itertuples():
        v = extract(facts, f.period_end, args.prefer_original)
        missing = [k for k in VARS if v[k] is None]
        if all(v[c] is None for c in CORE):
            log.error("%s FY%d: no core financials extracted; row skipped", label, f.fy)
            continue
        log.info("%s FY%d: ok (%d/%d fields)", label, f.fy, len(v) - len(missing), len(v))
        rows.append({"cik": cik, "ticker": ticker or (subs.get("tickers") or [""])[0],
            "company_name": subs.get("name", ""), "fiscal_year": f.fy,
            "filing_date": f.filing_date.date(), "sic": subs.get("sic", ""), **v,
            "fiscal_period_end": f.period_end.date(), "form_type": f.form,
            "accession_number": f.accessionNumber,
            "missing_fields": ";".join(missing)})
    return rows


def main(argv=None):
    p = argparse.ArgumentParser(description="Collect 10-K financials from SEC EDGAR.",
                                formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    p.add_argument("--input", default=IN_PATH)
    p.add_argument("--output", default=OUT_PATH)
    p.add_argument("--start-year", type=int, default=2020)
    p.add_argument("--end-year", type=int, default=2024)
    p.add_argument("--user-agent", default=UA)
    p.add_argument("--rate-limit", type=float, default=RATE_LIMIT)
    p.add_argument("--cache-name", default=CACHE_NAME)
    p.add_argument("--no-cache", action="store_true")
    p.add_argument("--fy-convention", choices=("compustat", "calendar"), default="compustat",
                   help="compustat: periods ending Jan-May are labelled the prior year")
    p.add_argument("--include-amendments", action="store_true", help="also accept 10-K/A")
    p.add_argument("--prefer-original", action="store_true",
                   help="as-first-reported values instead of restated")
    p.add_argument("--limit", type=int, help="process only the first N firms")
    p.add_argument("--log-file")
    p.add_argument("--verbose", action="store_true")
    args = p.parse_args(argv)

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)-7s %(message)s", datefmt="%H:%M:%S",
        handlers=[logging.StreamHandler(sys.stderr)] +
                 ([logging.FileHandler(args.log_file, mode="w")] if args.log_file else []))
    if "PLACEHOLDER" in args.user_agent:
        log.warning("User-Agent is still a placeholder; SEC may block you.")

    session = make_session(args.user_agent, None if args.no_cache else args.cache_name)

    firms = pd.read_csv(args.input, dtype=str).rename(columns=str.lower)
    for col in ("ticker", "cik"):
        if col not in firms:
            firms[col] = None
    firms["ticker"] = firms.ticker.fillna("").str.strip().str.upper()
    firms["cik"] = (firms.cik.fillna("").map(lambda c: re.sub(r"\D", "", str(c)))
                    .map(lambda c: c.zfill(10) if c else ""))
    if (firms.cik == "").any():   # resolve missing CIKs from SEC's ticker map
        tmap = get(session, "https://www.sec.gov/files/company_tickers.json", args.rate_limit) or {}
        lookup = {e["ticker"].upper(): str(e["cik_str"]).zfill(10) for e in tmap.values()}
        firms["cik"] = [c or lookup.get(t, "") for c, t in zip(firms.cik, firms.ticker)]
    unresolved = firms[firms.cik == ""]
    for t in unresolved.ticker:
        log.error("could not resolve CIK for ticker %s; skipping", t or "<blank>")
    firms = firms[firms.cik != ""].head(args.limit) if args.limit else firms[firms.cik != ""]

    rows = []
    for f in tqdm(list(firms.itertuples()), desc="firms", unit="firm"):
        try:
            rows += process_firm(session, f.cik, f.ticker, args)
        except Exception as e:            # one firm must never kill the run
            log.exception("unhandled error on CIK %s: %s", f.cik, e)

    out = pd.DataFrame(rows, columns=FIELDS)
    out.to_csv(args.output, index=False)
    log.info("wrote %d firm-years (%d firms) -> %s",
             len(out), out.cik.nunique() if len(out) else 0, args.output)
    return 0


if __name__ == "__main__":
    sys.exit(main())
