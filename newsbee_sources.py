"""
Newsbee Source Explorer
=======================

Type a place ("Ballard, Seattle, WA") and the app:
  1. finds the place (OpenStreetMap / Nominatim),
  2. builds its source map automatically, for any US place — nothing is hand-entered:
       - the city's and county's own websites and feeds (OpenStreetMap records),
       - websites of libraries, schools, community centres, town halls and venues inside the
         place's boundary (OpenStreetMap),
       - the city's / county's meeting-software accounts (Legistar, CivicClerk, PrimeGov,
         CivicPlus Agenda Center),
       - open-data portals for the city, county or state on the Socrata network, and their
         police, fire, permit, inspection, licence and 311 datasets,
       - news searches for the place, then the publishers those searches show covering it,
       - weather alerts; optional Claude-discovered sources, curated sources and your own URLs,
  3. crawls every source for publishable items, using every method a site offers:
       RSS/Atom feeds · iCal event calendars · schema.org structured data (events, articles)
       · sitemaps · article links on the page,
  4. sorts everything into newsletter sections (events, council, schools, police & fire,
     real estate, business, obituaries, community, weather, other news),
  5. optional: Claude ranks every item for this neighbourhood and writes a one-line blurb
     using only the item's own title and summary,
  6. locality filter: keeps only items provably about the place — a location inside its
     OpenStreetMap boundary, a street address that maps inside it, or naming the place or a
     landmark inside it (reading the article when the headline doesn't say) — and lays them
     out as a newsletter. The first-pass results stay available unchanged.

Run
---
    pip install -r requirements.txt
    streamlit run newsbee_sources.py

Optional AI features:  export ANTHROPIC_API_KEY=sk-ant-...

Ground rules built in (see "Compliance" below — every request goes through it)
---------------------
* Identifies itself with a User-Agent carrying your contact email; no cookies, logins or disguises.
* robots.txt (RFC 9309) before every page, feed, sitemap and calendar, incl. Crawl-delay; unreadable
  robots.txt = no. AI opt-outs (AI-crawler blocks, noai, TDM reservation) = no.
* Page directives: noindex → not used; nosnippet / noarchive / paywalled → headline and link only.
* Public pages only (401/403 and login redirects skipped); backs off on 429/503.
* Never scrapes Facebook, Nextdoor, Instagram, X/Twitter, Reddit, TikTok or Legacy.com.
* Police & fire locations shown to the block.
* Headlines, short summaries and links only by default. Full text is for internal review;
  newspaper, blog and obituary text is copyrighted — summarise and link when publishing.
"""
from __future__ import annotations

import collections
import concurrent.futures as cf
import datetime as dt
import email.utils
import fnmatch
import functools
import html
import io
import json
import math
import os
import re
import threading
import time
import urllib.parse
import urllib.robotparser
from dataclasses import asdict, dataclass, field
from zoneinfo import ZoneInfo

import feedparser
import httpx
import pandas as pd
import streamlit as st

try:
    import trafilatura
except ImportError:
    trafilatura = None
try:
    import icalendar
except ImportError:
    icalendar = None
try:
    import anthropic
except ImportError:
    anthropic = None
try:
    import pypdf
except ImportError:
    pypdf = None


# --------------------------------------------------------------------------------------
# Settings
# --------------------------------------------------------------------------------------
AGENT_NAME = "NewsbeeSourceExplorer"
DISCOVERY_MODEL = "claude-sonnet-5-5"
RANKING_MODEL = "claude-haiku-5-5"
WEB_SEARCH_TOOL = "web_search_20250305"
TIMEOUT = httpx.Timeout(20.0, connect=10.0)
MIN_SECONDS_PER_HOST = 0.75
HOST_INTERVALS = {"nominatim.openstreetmap.org": 1.1, "overpass-api.de": 2.0,   # their usage policies
                  "overpass.kumi.systems": 2.0}
SLOW_HOSTS = {"overpass-api.de": 90.0, "overpass.kumi.systems": 90.0}           # long-running queries
OVERPASS_ENDPOINTS = ("https://overpass-api.de/api/interpreter", "https://overpass.kumi.systems/api/interpreter")
DO_NOT_SCRAPE = (
    "facebook.com", "nextdoor.com", "instagram.com", "x.com", "twitter.com",
    "reddit.com", "tiktok.com", "legacy.com",
)

SECTIONS = {
    "events": "Events & things to do",
    "civic": "Council & government",
    "schools": "Schools & youth",
    "public_safety": "Police, fire & safety",
    "real_estate": "Real estate & development",
    "business": "Business openings & closings",
    "obituaries": "Obituaries & milestones",
    "community": "Community & neighbours",
    "weather": "Weather & alerts",
    "news": "Other local news",
}

# Keyword rules: checked in this order; the first match wins.
SECTION_RULES = [
    ("obituaries", r"obituar|passed away|celebration of life|memorial service|in loving memory|\bfuneral\b|\bdied\b"),
    ("public_safety", r"\bpolice\b|sheriff|arrest|\bcrash|collision|\bfire\b|shooting|stabb|burglar|theft|robber|"
                      r"\b911\b|\bmedic\b|aid response|rescue|\bcrime|missing person|suspect"),
    ("weather", r"weather|\bstorm|windstorm|flood|heat wave|\bsmoke\b|air quality|advisory|snow|king tide"),
    ("real_estate", r"real estate|home sale|\bsold for\b|listing|\bpermit|zoning|rezone|land use|development|"
                    r"construction|housing|apartment|townhome|\bparcel|demolition|single-family"),
    ("schools", r"\bschool|student|teacher|\bpta\b|ptsa|graduat|scholar|national merit|athlet|varsity|"
                r"football|soccer|basketball|volleyball|swim meet|\bgame\b|playoff|homecoming"),
    ("civic", r"council|commission|\bboard\b|ordinance|\bcity\b|county|\blevy\b|budget|\bvote|election|"
              r"hearing|mayor|legislat|agenda|public comment"),
    ("business", r"now open|grand opening|\bopens\b|opening|closing|\bcloses\b|restaurant|\bcafe|bakery|brewery|"
                 r"\bshop\b|\bstore\b|business|liquor|licen[cs]e|inspection|layoff|ribbon cutting"),
    ("events", r"festival|concert|\bmarket\b|\bfair\b|\bclass\b|workshop|storytime|\btour\b|exhibit|screening|"
               r"\bwalk\b|fun run|meetup|celebrat|\bevent|parade|cleanup|volunteer"),
]
_SECTION_RES = [(s, re.compile(p, re.I)) for s, p in SECTION_RULES]


@dataclass
class Source:
    name: str
    url: str
    category: str               # a SECTIONS key
    method: str                 # "web" (crawl), "feed" (feed only), "api", or "listed"
    origin: str = "curated"     # curated | nationwide | city website | county website | OpenStreetMap |
                                # meeting software | open-data catalog | news search | news publisher |
                                # Claude + web search | you
    feed_url: str | None = None
    fetcher: str | None = None
    params: dict = field(default_factory=dict)
    notes: str = ""
    status: str = "not fetched"
    n_items: int = 0
    jurisdiction: str = ""      # the government this source belongs to (e.g. "Seattle")
    rules: str = ""             # what the compliance layer did (robots.txt, opt-outs, back-offs)


@dataclass
class Item:
    source: str
    section: str
    title: str
    url: str
    published: dt.datetime | None = None    # when posted / when it happened
    starts: dt.datetime | None = None       # events only
    where: str = ""
    summary: str = ""
    text: str = ""
    via: str = ""
    found_by: str = ""                      # feed | calendar | structured data | sitemap | page link | api | news search
    publisher_url: str = ""                 # news searches: the publisher's homepage
    score: int | None = None
    blurb: str = ""
    lat: float | None = None
    lon: float | None = None
    jurisdiction: str = ""
    body: str = ""                          # article text fetched only for the locality check (not shown)
    local: bool | None = None
    local_why: str = ""
    local_tier: str = ""                    # coordinates | address | name | landmark | jurisdiction | search match
    use: str = ""                           # how Newsbee may use it: public record | their writing | headline & link only
    map_url: str = ""                       # police & fire: a map pin for where it happened
    attachments: list = field(default_factory=list)   # [(name, url)] agendas, minutes, staff reports (PDFs)


# --------------------------------------------------------------------------------------
# HTTP: identification, per-site pacing, robots.txt
# --------------------------------------------------------------------------------------
def user_agent(contact: str) -> str:
    return f"{AGENT_NAME}/0.3 (+{contact or 'no-contact-set'})"


_pace_lock = threading.Lock()
_next_slot: dict[str, float] = {}
_host_interval: dict[str, float] = {}   # per-site gaps raised by robots.txt Crawl-delay or by 429/503 replies


def _host(url: str) -> str:
    return urllib.parse.urlsplit(url).netloc.lower()


def _pace(url: str) -> None:
    host = _host(url)
    with _pace_lock:
        now = time.monotonic()
        slot = max(now, _next_slot.get(host, 0.0))
        gap = max(HOST_INTERVALS.get(host, MIN_SECONDS_PER_HOST), _host_interval.get(host, 0.0))
        _next_slot[host] = slot + gap
    if slot > now:
        time.sleep(slot - now)


def http_get(url: str, contact: str, params: dict | None = None, accept: str | None = None) -> httpx.Response:
    """The single low-level request: paced per site, identifies itself, no cookies, no login."""
    _pace(url)
    headers = {"User-Agent": user_agent(contact)}
    if accept:
        headers["Accept"] = accept
    slow = SLOW_HOSTS.get(_host(url))
    timeout = httpx.Timeout(slow, connect=15.0) if slow else TIMEOUT
    return httpx.get(url, params=params, headers=headers, timeout=timeout, follow_redirects=True)


# --------------------------------------------------------------------------------------
# Compliance: the rules every request goes through
# --------------------------------------------------------------------------------------
#  1. Platforms whose terms forbid scraping are never fetched (DO_NOT_SCRAPE + your own list).
#  2. robots.txt (RFC 9309) is read for every website before any page, feed, sitemap or calendar:
#       · Disallow rules for our agent (or *) are obeyed;
#       · Crawl-delay / Request-rate are honoured; a delay longer than POLICY["max_crawl_delay"] means we skip the site;
#       · robots.txt that errors (5xx) or can't be reached means "no" for that site, as the standard requires;
#       · a missing robots.txt (404) means no rules;
#       · rules are re-read after 24 hours.
#  3. AI opt-outs are treated as a "no": if robots.txt blocks the common AI crawlers (GPTBot, ClaudeBot,
#     CCBot, Google-Extended …), if a page says noai, or if the site reserves text-and-data-mining rights
#     (TDMRep: tdm-reservation header/meta or /.well-known/tdmrep.json).
#  4. Page-level directives: noindex/none → not used; nosnippet / noarchive / max-snippet:0 / paywalled
#     (schema.org isAccessibleForFree=false) → headline and link only, no text kept.
#  5. Only public pages: anything answering 401/403 (login or permission) is skipped, never worked around.
#  6. 429/503 replies: we wait as long as Retry-After asks (up to 30 s), slow down for the rest of the run,
#     and stop contacting a site that asks three times.
#  7. Documented public APIs (weather.gov, OpenStreetMap, Socrata, Legistar, CivicClerk) are used within their
#     published usage policies (rate limits, identification) instead of robots.txt, which covers crawling.
AI_AGENTS = ("GPTBot", "ChatGPT-User", "ClaudeBot", "Claude-Web", "anthropic-ai", "CCBot", "Google-Extended",
             "PerplexityBot", "Applebot-Extended", "Bytespider", "cohere-ai", "meta-externalagent", "Amazonbot")
POLICY = {"ai_optout": True, "max_crawl_delay": 30.0, "extra_blocked": ()}
ROBOTS_TTL = 24 * 3600
_DISALLOW_ALL = "disallow-all"


class Disallowed(httpx.HTTPError):
    """A request we chose not to make (robots.txt, terms, opt-out, login wall, rate limit)."""


_robots_cache: dict[str, tuple[float, object]] = {}
_robots_lock = threading.Lock()
_too_slow: set[str] = set()
_strikes: collections.Counter = collections.Counter()
_rules_log: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
_log_lock = threading.Lock()


def note_rule(url: str, what: str) -> None:
    with _log_lock:
        _rules_log[_host(url).removeprefix("www.")][what] += 1


def reset_run_state() -> None:
    """Per-run counters (robots.txt itself stays cached for 24 hours)."""
    with _log_lock:
        _rules_log.clear()
    _strikes.clear()


def _robots_for(url: str, contact: str):
    parts = urllib.parse.urlsplit(url)
    root, host = f"{parts.scheme}://{parts.netloc}", parts.netloc.lower()
    with _robots_lock:
        hit = _robots_cache.get(root)
        if hit and time.time() - hit[0] < ROBOTS_TTL:
            return hit[1]
    parser = None
    try:
        r = http_get(root + "/robots.txt", contact)
        if r.status_code == 200:
            parser = urllib.robotparser.RobotFileParser()
            parser.parse(r.text.splitlines())
            delay = parser.crawl_delay(AGENT_NAME) or 0
            rate = parser.request_rate(AGENT_NAME)
            if rate and rate.requests:
                delay = max(float(delay), rate.seconds / rate.requests)
            if delay:
                delay = float(delay)
                if delay > POLICY["max_crawl_delay"]:
                    _too_slow.add(host)
                else:
                    with _pace_lock:
                        _host_interval[host] = max(_host_interval.get(host, 0.0), delay)
                    note_rule(url, f"crawl-delay {delay:g}s honoured")
        elif r.status_code >= 500 or r.status_code == 429:
            parser = _DISALLOW_ALL                       # RFC 9309 §2.3.1.4: unreachable → assume disallow
    except httpx.HTTPError:
        parser = _DISALLOW_ALL
    with _robots_lock:
        _robots_cache[root] = (time.time(), parser)
    return parser


def robots_reason(url: str, contact: str) -> str:
    """Why robots.txt rules us out for this URL ('' when allowed)."""
    parser = _robots_for(url, contact)
    if parser is _DISALLOW_ALL:
        return "robots.txt couldn't be read — treated as a no"
    if _host(url) in _too_slow:
        return f"crawl-delay is longer than {POLICY['max_crawl_delay']:g}s — skipped"
    if parser is None:
        return ""
    if not parser.can_fetch(AGENT_NAME, url):
        return "robots.txt disallows"
    if POLICY["ai_optout"]:
        blocked = [a for a in AI_AGENTS if not parser.can_fetch(a, url)]
        if blocked:
            return f"site opts out of AI crawlers in robots.txt ({blocked[0]})"
    return ""


def robots_allows(url: str, contact: str) -> bool:
    return not robots_reason(url, contact)


def robots_sitemaps(url: str, contact: str) -> list[str]:
    parser = _robots_for(url, contact)
    return list(parser.site_maps() or []) if parser not in (None, _DISALLOW_ALL) else []


def is_blocked(url: str) -> bool:
    host = _host(url)
    return any(host == d or host.endswith("." + d) for d in (*DO_NOT_SCRAPE, *POLICY["extra_blocked"]))


def _retry_after(r: httpx.Response) -> float:
    value = r.headers.get("retry-after", "")
    if value.strip().isdigit():
        return float(value)
    try:
        when = email.utils.parsedate_to_datetime(value)
        return max(0.0, (when - dt.datetime.now(dt.timezone.utc)).total_seconds())
    except (TypeError, ValueError):
        return 10.0


def polite_get(url: str, contact: str, params: dict | None = None, accept: str | None = None) -> httpx.Response:
    """Any request (APIs included): backs off on 429/503 and stops after a site asks three times."""
    host = _host(url)
    if _strikes[host] >= 3:
        raise Disallowed(f"{host} asked us to slow down — stopped for this run")
    r = http_get(url, contact, params=params, accept=accept)
    if r.status_code in (429, 503):
        _strikes[host] += 1
        wait = min(_retry_after(r), 30.0)
        note_rule(url, "asked to slow down (429/503) — backed off")
        with _pace_lock:
            _host_interval[host] = max(_host_interval.get(host, MIN_SECONDS_PER_HOST) * 2, wait)
        time.sleep(wait)
        if _strikes[host] >= 3:
            raise Disallowed(f"{host} asked us to slow down — stopped for this run")
        r = http_get(url, contact, params=params, accept=accept)
    return r


def web_get(url: str, contact: str, accept: str | None = None) -> httpx.Response:
    """A website request (page, feed, sitemap, calendar): terms, robots.txt and login walls checked first."""
    if is_blocked(url):
        note_rule(url, "platform terms forbid scraping")
        raise Disallowed("this platform's terms don't allow scraping")
    reason = robots_reason(url, contact)
    if reason:
        note_rule(url, reason)
        raise Disallowed(reason)
    r = polite_get(url, contact, accept=accept)
    if r.status_code in (401, 403, 407):
        note_rule(url, "login or permission required — skipped")
        raise Disallowed("login or permission required")
    if r.url and str(r.url) != url and re.search(r"/(login|signin|sign-in|account/login|subscribe)\b", r.url.path, re.I):
        note_rule(url, "redirected to a login or subscribe page — skipped")
        raise Disallowed("redirected to a login or subscribe page")
    return r


@functools.lru_cache(maxsize=512)
def _tdmrep(root: str, contact: str) -> tuple:
    """TDMRep (W3C community spec): /.well-known/tdmrep.json lists paths where mining rights are reserved."""
    try:
        r = http_get(root + "/.well-known/tdmrep.json", contact)
        rules = r.json() if r.status_code == 200 else []
    except (httpx.HTTPError, ValueError):
        return ()
    return tuple((str(x.get("location", "")), str(x.get("tdm-reservation", "0")))
                 for x in rules if isinstance(x, dict)) if isinstance(rules, list) else ()


_DIRECTIVES = {"noindex", "none", "nosnippet", "noarchive", "noai", "noimageai", "max-snippet:0"}


def page_rights(r: httpx.Response, page_html: str = "", contact: str = "") -> set[str]:
    """Usage signals a page or feed sends: robots directives, AI opt-outs, TDM reservations, paywalls."""
    ours = {AGENT_NAME.lower(), "*"} | ({a.lower() for a in AI_AGENTS} if POLICY["ai_optout"] else set())
    raw = []
    for value in r.headers.get_list("x-robots-tag") if hasattr(r.headers, "get_list") else [r.headers.get("x-robots-tag", "")]:
        for piece in value.split(","):
            piece = piece.strip().lower()
            if ":" in piece and piece.split(":")[0].strip() not in ("max-snippet", "unavailable_after", "max-image-preview", "max-video-preview"):
                agent, piece = (x.strip() for x in piece.split(":", 1))
                if agent not in ours:
                    continue
            raw.append(piece.replace(" ", ""))
    if page_html:
        for name in ("robots", AGENT_NAME.lower()) + (tuple(a.lower() for a in AI_AGENTS) if POLICY["ai_optout"] else ()):
            content = _meta(page_html[:200_000], name)
            raw += [x.strip().lower().replace(" ", "") for x in content.split(",") if x.strip()]
        if re.search(r"[\"']isAccessibleForFree[\"']\s*:\s*[\"']?false", page_html[:300_000], re.I):
            raw.append("paywalled")
        if _meta(page_html[:200_000], "tdm-reservation").strip() == "1":
            raw.append("tdm-reserved")
    if r.headers.get("tdm-reservation", "").strip() == "1":
        raw.append("tdm-reserved")
    if contact and POLICY["ai_optout"]:
        parts = urllib.parse.urlsplit(str(r.url))
        for location, reserved in _tdmrep(f"{parts.scheme}://{parts.netloc}", contact):
            if reserved == "1" and fnmatch.fnmatch(parts.path or "/", location or "/*"):
                raw.append("tdm-reserved")
                break
    return {x for x in raw if x in _DIRECTIVES or x in ("paywalled", "tdm-reserved")}


def rights_action(flags: set[str]) -> str:
    """'skip' — don't use the page; 'link-only' — headline and link, no text; 'ok'."""
    if flags & {"noindex", "none"}:
        return "skip"
    if POLICY["ai_optout"] and flags & {"noai", "tdm-reserved"}:
        return "skip"
    if flags & {"nosnippet", "noarchive", "max-snippet:0", "paywalled"}:
        return "link-only"
    return "ok"


def apply_rights(items: list[Item], flags: set[str], url: str) -> list[Item]:
    action = rights_action(flags)
    if action == "skip":
        note_rule(url, "page opts out (" + ", ".join(sorted(flags)) + ") — not used")
        return []
    if action == "link-only":
        note_rule(url, "headline & link only (" + ", ".join(sorted(flags)) + ")")
        for it in items:
            it.summary = it.text = it.body = ""
            it.use = "headline & link only (site's rule)"
    return items


def rules_for(src: Source) -> str:
    """What the compliance layer did for this source, for the Sources tab."""
    if src.method == "api":
        return "public API — used within its published usage policy"
    if src.method == "listed":
        return "not fetched — listed only"
    hosts = {_host(u).removeprefix("www.") for u in (src.url, src.feed_url) if u}
    bits = collections.Counter()
    with _log_lock:
        for h in hosts:
            bits.update(_rules_log.get(h, {}))
    robots = []
    with _robots_lock:
        for u in (src.url, src.feed_url):
            if u:
                p = urllib.parse.urlsplit(u)
                hit = _robots_cache.get(f"{p.scheme}://{p.netloc}")
                if hit:
                    robots.append("robots.txt followed" if hit[1] not in (None, _DISALLOW_ALL)
                                  else "no robots.txt" if hit[1] is None else "robots.txt unreadable")
    head = robots[0] if robots else "robots.txt checked"
    return " · ".join([head] + [f"{k} ×{n}" if n > 1 else k for k, n in bits.most_common()])


def same_site(a: str, b: str) -> bool:
    ha = urllib.parse.urlsplit(a).netloc.lower().removeprefix("www.")
    hb = urllib.parse.urlsplit(b).netloc.lower().removeprefix("www.")
    return ha == hb


# --------------------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------------------
def clean(text: str, limit: int = 400) -> str:
    text = re.sub(r"<[^>]+>", " ", text or "")
    text = re.sub(r"\s+", " ", html.unescape(text)).strip()
    return text if len(text) <= limit else text[: limit - 1].rsplit(" ", 1)[0] + "…"


def parse_date(value, tz: str = "UTC") -> dt.datetime | None:
    """Accepts struct_time, date, datetime or ISO strings; returns an aware datetime."""
    if not value:
        return None
    zone = ZoneInfo(tz)
    if isinstance(value, time.struct_time):
        return dt.datetime(*value[:6], tzinfo=dt.timezone.utc)
    if isinstance(value, dt.datetime):
        return value if value.tzinfo else value.replace(tzinfo=zone)
    if isinstance(value, dt.date):
        return dt.datetime(value.year, value.month, value.day, tzinfo=zone)
    s = str(value).strip().replace("Z", "+00:00")
    try:
        d = dt.datetime.fromisoformat(s)
    except ValueError:
        try:
            d = dt.datetime.fromisoformat(s[:10])
        except ValueError:
            return None
    return d if d.tzinfo else d.replace(tzinfo=zone)


def pick(row: dict, keys: list[str], default: str = "") -> str:
    for k in keys:
        if row.get(k):
            return str(row[k])
    return default


def km_between(lat1, lon1, lat2, lon2) -> float:
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = math.radians(lat2 - lat1), math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * 6371.0 * math.asin(math.sqrt(a))


def classify(item: Item, hint: str) -> str:
    """Section for an item: single-purpose sources keep their section; dated events are events;
    everything else is sorted by keywords."""
    if item.found_by == "api" or hint in ("public_safety", "weather"):
        return hint
    if item.found_by in ("agenda", "document"):   # government business: council, or the topic it is about
        full = item.summary.split("Full title:", 1)[1] if "Full title:" in item.summary else ""
        for section, rx in _SECTION_RES:
            if section in ("real_estate", "schools", "business") and rx.search(f"{item.title} {full}"):
                return section
        return "civic"
    if item.starts:
        return "events"
    path = urllib.parse.urlsplit(item.url).path.replace("-", " ").replace("/", " ")
    text = f"{item.title} {item.summary} {path}"
    for section, rx in _SECTION_RES:
        if rx.search(text):
            return section
    return hint if hint in SECTIONS else "news"


# --------------------------------------------------------------------------------------
# Step 1 — find the place
# --------------------------------------------------------------------------------------
@st.cache_data(ttl=86400, show_spinner=False)
def geocode(query: str, contact: str) -> dict | None:
    r = polite_get("https://nominatim.openstreetmap.org/search", contact,
                 params={"q": query, "format": "jsonv2", "addressdetails": 1, "namedetails": 1, "limit": 1,
                         "countrycodes": "us", "polygon_geojson": 1, "polygon_threshold": 0.0002})
    r.raise_for_status()
    hits = r.json()
    if not hits:
        return None
    hit, a = hits[0], hits[0].get("address", {})
    shape = hit.get("geojson") or {}
    names = hit.get("namedetails") or {}
    aliases = sorted({v for k, v in names.items()
                      if k in ("name", "name:en", "alt_name", "old_name", "short_name", "official_name")
                      and isinstance(v, str) and len(v) >= 3})
    place = {
        "query": query, "display": hit.get("display_name", query),
        "lat": float(hit["lat"]), "lon": float(hit["lon"]),
        "neighbourhood": a.get("neighbourhood") or a.get("suburb") or a.get("quarter"),
        "city": a.get("city") or a.get("town") or a.get("village") or a.get("hamlet"),
        "county": a.get("county"), "state": a.get("state"),
        "state_code": (a.get("ISO3166-2-lvl4") or "").replace("US-", ""), "postcode": a.get("postcode"),
        "boundary": shape if shape.get("type") in ("Polygon", "MultiPolygon") else None,
        "aliases": aliases,
    }
    place["label"] = place["neighbourhood"] or place["city"] or place["county"] or query
    return place


# --------------------------------------------------------------------------------------
# Step 2 — the source map
# --------------------------------------------------------------------------------------
def news_sources(place: dict, days: int) -> list[Source]:
    label = place["label"]
    area = place.get("city") or place.get("county") or place.get("state") or ""
    base = f'"{label}"' + (f" {area}" if area and area.lower() != label.lower() else "")
    searches = [
        ("Local news", "news", ""),
        ("Events & things to do", "events", " (events OR festival OR market OR concert OR storytime)"),
        ("Schools, council & safety", "civic", ' ("school board" OR council OR police OR fire)'),
        ("Real estate & development", "real_estate", ' ("real estate" OR "sold for" OR permit OR zoning OR development)'),
        ("Business openings & closings", "business", ' ("now open" OR "grand opening" OR closing OR restaurant OR shop)'),
        ("Obituaries", "obituaries", ' (obituary OR "passed away" OR "celebration of life")'),
    ]
    out = []
    for name, cat, extra in searches:
        url = "https://news.google.com/rss/search?" + urllib.parse.urlencode(
            {"q": f"{base}{extra} when:{days}d", "hl": "en-US", "gl": "US", "ceid": "US:en"})
        out.append(Source(name=f"News search: {name}", url=url, feed_url=url, category=cat, method="web",
                          origin="news search", notes="Headlines and links only; follow the link for the story."))
    return out


def socrata(name, domain, dataset, category, notes, **params) -> Source:
    page = f"https://{domain}/d/{dataset}"
    return Source(name=name, url=page, category=category, method="api", fetcher="socrata_geo",
                  params={"domain": domain, "dataset": dataset, **params}, notes=notes)


def registry_for(place: dict) -> list[Source]:
    q = place["query"].lower()
    nb = (place.get("neighbourhood") or "").lower()
    city = (place.get("city") or "").lower()
    county = (place.get("county") or "").lower()
    state = place.get("state_code") or ""

    out: list[Source] = [Source(
        name="National Weather Service alerts", url="https://www.weather.gov/", category="weather",
        method="api", fetcher="nws", notes="Active watches and warnings for this exact point.")]

    local_sites = {
        "ballard": [("My Ballard", "https://www.myballard.com/", "news")],
        "west seattle": [("West Seattle Blog", "https://westseattleblog.com/", "news")],
        "capitol hill": [("Capitol Hill Seattle Blog", "https://www.capitolhillseattle.com/", "news")],
        "wedgwood": [("Wedgwood in Seattle History", "https://wedgwoodinseattlehistory.com/", "community"),
                     ("Wedgwood Community Council", "https://www.wedgwoodcc.org/", "community")],
        "beacon hill": [("Beacon Business Alliance", "https://www.beaconbusinessalliance.org/", "business"),
                        ("Beacon Arts", "https://www.beacon-arts.org/", "events")],
        "bainbridge": [("Bainbridge Newsbee", "https://www.bainbridgenewsbee.com/", "news"),
                       ("Bainbridge Island Review", "https://www.bainbridgereview.com/", "news"),
                       ("Kitsap Regional Library", "https://www.krl.org/", "events")],
    }
    for key, sites in local_sites.items():
        if key == nb or key in q or key in city:
            out += [Source(name=n, url=u, category=c, method="web") for n, u, c in sites]

    if city == "seattle":
        out += [
            socrata("Seattle Fire 911 calls", "data.seattle.gov", "kzjm-xkqj", "public_safety",
                    "Real-time city open data, filtered to your radius.",
                    title_fields=["type"], address_fields=["address"], date_fields=["datetime"]),
            socrata("Seattle Police calls for service", "data.seattle.gov", "33kz-ixgy", "public_safety",
                    "Calls, not confirmed crimes. Locations are blurred to the block.",
                    title_fields=["final_call_type", "initial_call_type", "call_type"]),
            socrata("Seattle building permits", "data.seattle.gov", "76t5-zqzr", "real_estate",
                    "New construction, additions, demolitions. Dataset ID unverified — errors show here.",
                    title_fields=["description", "permittypedesc", "permitclass"],
                    address_fields=["originaladdress1", "address"],
                    date_fields=["issueddate", "applieddate"]),
            socrata("King County food establishment inspections", "data.kingcounty.gov", "f29f-zza5", "business",
                    "Signals new and changing restaurants; publish scores with care.",
                    title_fields=["name", "program_identifier"], address_fields=["address"],
                    date_fields=["inspection_date"], extra_fields=["inspection_result", "inspection_score"]),
            Source(name="Seattle City Council meetings (Legistar)", url="https://seattle.legistar.com/",
                   category="civic", method="api", fetcher="legistar", params={"client": "seattle"},
                   notes="Some Legistar clients need an API token; an error here means ask the clerk.",
                   jurisdiction="Seattle"),
            Source(name="Seattle Public Library events", url="https://www.spl.org/event-calendar",
                   category="events", method="web"),
            Source(name="The Seattle Times — Local", url="https://www.seattletimes.com/seattle-news/",
                   category="news", method="web", notes="Copyrighted: headlines and links only."),
            Source(name="King County Assessor — property sales (bulk download)",
                   url="https://info.kingcounty.gov/assessor/DataDownload/default.aspx",
                   category="real_estate", method="listed", notes="Weekly sales files; needs a separate import."),
        ]
    if "bainbridge" in city or "bainbridge" in q:
        out += [
            Source(name="City of Bainbridge Island — council & planning (CivicClerk)",
                   url="https://bainbridgeislandwa.portal.civicclerk.com/", category="civic",
                   method="api", fetcher="civicclerk", params={"tenant": "bainbridgeislandwa"},
                   notes="Public CivicClerk API (undocumented by the vendor; keep volume low).",
                   jurisdiction="Bainbridge Island"),
            Source(name="Bainbridge Island School District board (BoardDocs)",
                   url="https://go.boarddocs.com/wa/bisd/Board.nsf", category="schools", method="listed",
                   notes="No public API — agendas are HTML/PDF."),
        ]
    if county == "king county":
        out.append(Source(name="King County Council meetings (Legistar)", url="https://mkcclegisearch.kingcounty.gov/",
                          category="civic", method="api", fetcher="legistar", params={"client": "kingcounty"},
                          jurisdiction="King County"))
    if county == "kitsap county":
        out += [
            Source(name="Kitsap Sheriff — booked in last 72 hours",
                   url="https://www.kitsap.gov/sheriff/Pages/BookedLast72Hours.aspx", category="public_safety",
                   method="listed", notes="Arrest is not conviction — set an editorial policy first."),
            Source(name="Kitsap County open data (parcels & property)",
                   url="https://kitsap-od-kitcowa.hub.arcgis.com/", category="real_estate", method="listed",
                   notes="ArcGIS open data; licence not stated — ask before republishing."),
        ]
    if state == "WA":
        out += [
            Source(name="WA Liquor & Cannabis Board — new licence applications",
                   url="https://data.wa.gov/d/vgcw-qfjm", category="business", method="api",
                   fetcher="socrata_search", params={"domain": "data.wa.gov", "dataset": "vgcw-qfjm"},
                   notes="Early signal for new restaurants, bars and shops. Searched by ZIP or city."),
            Source(name="WA Employment Security — WARN layoff & closure notices",
                   url="https://fortress.wa.gov/esd/file/warn/Public/SearchWARN.aspx",
                   category="business", method="listed", notes="Statewide; filter by city on the site."),
            Source(name="WA Superior Courts — Odyssey Portal", url="https://odysseyportal.courts.wa.gov/odyportal",
                   category="civic", method="listed",
                   notes="Court rule GR 31; bulk use needs a dissemination contract. Not scraped."),
            Source(name="Washington Public Notices (probate, foreclosures, hearings)",
                   url="https://www.wapublicnotices.com/", category="civic", method="listed",
                   notes="Terms restrict bulk collection — check manually or license."),
        ]
    out.append(Source(name="Legacy.com obituaries", url="https://www.legacy.com/", category="obituaries",
                      method="listed", notes="Terms forbid scraping. Ask local funeral homes for a feed instead."))
    return out


def discover_with_claude(place: dict, api_key: str, model: str, max_searches: int) -> tuple[list[Source], str]:
    client = anthropic.Anthropic(api_key=api_key)
    location = {k: v for k, v in {"type": "approximate", "city": place.get("city"),
                                  "region": place.get("state"), "country": "US"}.items() if v}
    prompt = f"""You are building a source map for a hyperlocal weekly newsletter about {place['label']}
({place['display']}).

Use web search to find 15–25 publicly accessible sources of local information for THIS place:
city/county agenda portals, school district and school pages, police/fire/sheriff news, library and parks
event calendars, community centres, chambers and business associations, community councils, local news
sites and blogs, farmers markets, festivals, local funeral homes (obituaries), youth sports leagues.
Prefer pages that list many items (calendars, news listings). Check each URL exists.
Do not include Facebook, Nextdoor, Instagram, X/Twitter, Reddit, TikTok or Legacy.com.

Reply with ONLY a JSON array. Each item:
{{"name": str, "url": str, "category": one of {list(SECTIONS)},
  "access": one of ["rss", "ical", "api", "html", "pdf"], "feed_url": str or null,
  "why": str (under 15 words)}}"""
    tools = [{"type": WEB_SEARCH_TOOL, "name": "web_search", "max_uses": max_searches,
              "blocked_domains": list(DO_NOT_SCRAPE), "user_location": location}]
    messages = [{"role": "user", "content": prompt}]
    response = client.messages.create(model=model, max_tokens=6000, messages=messages, tools=tools)
    for _ in range(3):
        if response.stop_reason != "pause_turn":
            break
        messages.append({"role": "assistant", "content": response.content})
        response = client.messages.create(model=model, max_tokens=6000, messages=messages, tools=tools)
    text = "".join(getattr(b, "text", "") for b in response.content if getattr(b, "type", "") == "text")
    items = _json_array(text)
    out = []
    for it in items:
        if not isinstance(it, dict) or not str(it.get("url", "")).startswith("http"):
            continue
        access = str(it.get("access", "html")).lower()
        cat = it.get("category") if it.get("category") in SECTIONS else "community"
        out.append(Source(name=str(it.get("name") or it["url"]), url=it["url"], category=cat,
                          method="listed" if access in ("api", "pdf") else "web",
                          feed_url=it.get("feed_url") or None, origin="Claude + web search",
                          notes=f"{access.upper()} · {it.get('why', '')}".strip(" ·")))
    return out, f"Claude suggested {len(out)} sources." if out else "Claude returned no usable list."


def _json_array(text: str) -> list:
    match = re.search(r"\[.*\]", text or "", re.S)
    if not match:
        return []
    try:
        data = json.loads(match.group(0))
    except json.JSONDecodeError:
        return []
    return data if isinstance(data, list) else []


def dedupe_sources(sources: list[Source]) -> list[Source]:
    seen, out = set(), []
    for s in sources:
        p = urllib.parse.urlsplit(s.feed_url or s.url)
        key = (p.netloc.lower().removeprefix("www."), p.path.rstrip("/"), p.query)
        if key not in seen:
            seen.add(key)
            out.append(s)
    return out


# --------------------------------------------------------------------------------------
# Step 2b — automatic source discovery for any US place (nothing hand-entered)
# --------------------------------------------------------------------------------------
# Every source below is found from public directories at run time:
#   · the city's and county's own websites (OpenStreetMap / Wikidata tags), plus any feeds they publish
#   · websites of libraries, schools, community centres, town halls, arts venues… inside the boundary (OpenStreetMap)
#   · meeting-software accounts the city or county has (Legistar, CivicClerk, PrimeGov, CivicPlus Agenda Center)
#   · open-data portals on the Socrata network serving the city, county or state, and their incident,
#     permit, inspection, licence and 311 datasets
#   · publishers that the news searches show covering the place (second pass, after the searches run)

def slug(text: str | None) -> str:
    return re.sub(r"[^a-z0-9]", "", (text or "").lower())


def nws_source() -> Source:
    return Source(name="National Weather Service alerts", url="https://www.weather.gov/", category="weather",
                  method="api", fetcher="nws", origin="nationwide",
                  notes="Active watches and warnings for this exact point.")


def _website(tags: dict) -> str:
    url = (tags.get("website") or tags.get("contact:website") or tags.get("url") or "").split(";")[0].strip()
    if url and not url.startswith("http"):
        url = "https://" + url.lstrip("/")
    return url if re.match(r"https?://[^/\s]+\.[a-z]{2,}", url, re.I) else ""


@st.cache_data(ttl=7 * 86400, show_spinner=False)
def government_websites(city: str, county: str, state: str, contact: str) -> dict:
    """The official websites of the place's city and county, from their OpenStreetMap records."""
    out = {}
    for level, name in (("city", city), ("county", county)):
        if not name or not state:
            continue
        params = {"format": "jsonv2", "extratags": 1, "limit": 5, "countrycodes": "us", "state": state}
        params["county" if level == "county" else "city"] = name
        try:
            r = polite_get("https://nominatim.openstreetmap.org/search", contact, params=params)
            r.raise_for_status()
            hits = r.json()
        except (httpx.HTTPError, ValueError):
            continue
        for hit in hits if isinstance(hits, list) else []:
            site = _website(hit.get("extratags") or {})
            if site and hit.get("category", hit.get("class")) in ("boundary", "place"):
                out[level] = site
                break
    return out


_CIVICPLUS_MODS = {"1": ("News flash", "news"), "58": ("Calendar", "events"), "65": ("Agendas", "civic"),
                   "63": ("Alerts", "public_safety"), "51": ("Job postings", "community")}
_RSS_LINK = re.compile(r"<a\b[^>]*href=[\"']([^\"']*RSSFeed\.aspx\?[^\"']+)[\"'][^>]*>(.*?)</a>", re.I | re.S)


def government_site_sources(level: str, site: str, gov_name: str, contact: str) -> list[Source]:
    """The government's homepage, plus its CivicPlus Agenda Center and RSS feeds if it runs on CivicPlus."""
    label = f"{gov_name} — official website" if level == "city" else f"{gov_name} — county website"
    out = [Source(name=label, url=site, category="civic", method="web", origin=f"{level} website",
                  jurisdiction=gov_name if level == "city" else "")]
    root = site.rstrip("/")
    # Department newsrooms linked from the homepage (police blotter, fire news, press releases, notices)
    try:
        home = web_get(site, contact)
        base = ".".join(_host(str(home.url)).split(".")[-2:])
        rooms = {}
        for href, text in _DOC_LINK.findall(home.text[:400_000]):
            url = urllib.parse.urljoin(str(home.url), html.unescape(href)).split("#")[0]
            label = clean(text, 80)
            host = _host(url)
            if not (host == base or host.endswith("." + base)) or url.rstrip("/") == site.rstrip("/"):
                continue
            if re.search(r"news|press|blotter|newsroom|media release|announcement|alerts?|public notice|blog", f"{label} {url}", re.I) \
                    and not re.search(r"subscribe|signup|sign-up|login|facebook|twitter|instagram", url, re.I) \
                    and url not in rooms.values() and len(rooms) < 5:
                rooms[label or url] = url
        for label, url in rooms.items():
            cat = "public_safety" if re.search(r"police|fire|blotter|sheriff|emergency", f"{label} {url}", re.I) else "news"
            out.append(Source(name=f"{gov_name} — {label}"[:90], url=url, category=cat, method="web",
                              origin=f"{level} website", jurisdiction=out[0].jurisdiction,
                              notes="Newsroom on the government's own site — a primary source."))
    except httpx.HTTPError:
        pass
    try:
        r = web_get(root + "/AgendaCenter", contact)
        if r.status_code == 200 and "agendacenter" in r.text.lower():
            out.append(Source(name=f"{gov_name} — Agenda Center", url=str(r.url), category="civic",
                              method="web", origin="meeting software", jurisdiction=out[0].jurisdiction,
                              notes="CivicPlus Agenda Center: agendas and minutes."))
    except httpx.HTTPError:
        pass
    try:
        r = web_get(root + "/rss.aspx", contact)
        if r.status_code == 200:
            feeds = {}
            for href, text in _RSS_LINK.findall(r.text):
                href = urllib.parse.urljoin(str(r.url), html.unescape(href))
                mod = (urllib.parse.parse_qs(urllib.parse.urlsplit(href).query).get("ModID") or [""])[0]
                if mod in _CIVICPLUS_MODS and mod not in feeds and "All" in href:
                    feeds[mod] = href
            for mod, href in feeds.items():
                title, cat = _CIVICPLUS_MODS[mod]
                out.append(Source(name=f"{gov_name} — {title} (RSS)", url=href, feed_url=href, category=cat,
                                  method="feed", origin=f"{level} website", jurisdiction=out[0].jurisdiction))
    except httpx.HTTPError:
        pass
    return out


_OSM_KINDS = {  # tag value: (priority, newsletter section)
    "townhall": (0, "civic"), "government": (0, "civic"), "library": (1, "events"),
    "community_centre": (1, "community"), "marketplace": (2, "events"), "social_centre": (2, "community"),
    "school": (3, "schools"), "college": (4, "schools"), "arts_centre": (4, "events"),
    "theatre": (5, "events"), "museum": (5, "events"), "association": (6, "community"),
}


@st.cache_data(ttl=7 * 86400, show_spinner=False)
def _overpass_websites(lat: float, lon: float, reach_m: int, contact: str) -> list[dict]:
    around = f"(around:{reach_m},{lat},{lon})"
    has_site = '[~"^(website|contact:website)$"~"."]'
    query = f"""[out:json][timeout:60];
(
  nwr{around}["name"]["amenity"~"^(townhall|library|community_centre|marketplace|social_centre|school|college|arts_centre|theatre)$"]{has_site};
  nwr{around}["name"]["tourism"="museum"]{has_site};
  nwr{around}["name"]["office"~"^(government|association)$"]{has_site};
);
out tags center 400;"""
    out = []
    for el in overpass(query, contact).get("elements", []):
        tags, pt = el.get("tags", {}), el.get("center") or el
        kind = tags.get("amenity") or (tags.get("tourism") if tags.get("tourism") == "museum" else tags.get("office"))
        site = _website(tags)
        if tags.get("name") and site and kind in _OSM_KINDS and "lat" in pt and "lon" in pt:
            out.append({"name": tags["name"], "url": site, "kind": kind, "lat": float(pt["lat"]), "lon": float(pt["lon"])})
    return out


def overpass(query: str, contact: str) -> dict:
    """Runs an Overpass query, falling back to a mirror if the main server is busy or times out."""
    last = None
    for endpoint in OVERPASS_ENDPOINTS:
        try:
            r = polite_get(endpoint, contact, params={"data": query})
            if r.status_code == 200:
                return r.json()
            last = httpx.HTTPStatusError(f"HTTP {r.status_code}", request=r.request, response=r)
        except (httpx.HTTPError, ValueError) as e:
            last = e
    raise last or httpx.HTTPError("Overpass unavailable")


def osm_sources(place: dict, contact: str, radius_km: float, cap: int) -> list[Source]:
    """Websites of the libraries, schools, community centres, town halls and venues inside the place."""
    found = [f for f in _overpass_websites(place["lat"], place["lon"], _reach_m(place, radius_km), contact)
             if inside_locality(f["lat"], f["lon"], place, radius_km) and not is_blocked(f["url"])]
    found.sort(key=lambda f: (_OSM_KINDS[f["kind"]][0], f["name"]))
    out, per_host, seen = [], collections.Counter(), set()
    for f in found:
        host = urllib.parse.urlsplit(f["url"]).netloc.lower().removeprefix("www.")
        key = f["url"].rstrip("/").lower()
        if key in seen or per_host[host] >= 2:   # e.g. one school district hosting every school's page
            continue
        seen.add(key)
        per_host[host] += 1
        out.append(Source(name=f["name"], url=f["url"], category=_OSM_KINDS[f["kind"]][1], method="web",
                          origin="OpenStreetMap", notes=f"{f['kind'].replace('_', ' ')} inside {place['label']}"))
        if len(out) >= cap:
            break
    return out


def _json_ok(r: httpx.Response):
    if r.status_code != 200:
        return None
    try:
        return r.json()
    except ValueError:
        return None


def meeting_software_sources(place: dict, contact: str) -> list[Source]:
    """Checks whether the city or county has an account on the common public-meeting platforms."""
    st_code = (place.get("state_code") or "").lower()
    govs = []
    if place.get("city"):
        c = slug(place["city"])
        govs.append((place["city"], [c, c + st_code, "cityof" + c, "cityof" + c + st_code]))
    if place.get("county"):
        k = slug(place["county"])                      # "kingcounty"
        bare = k.removesuffix("county")
        govs.append((place["county"], [k, k + st_code, bare + "county" + st_code]))
    out = []
    for gov, candidates in govs:
        candidates = list(dict.fromkeys(x for x in candidates if len(x) >= 4))
        juris = gov if gov == place.get("city") else ""
        for client in candidates:                                   # Legistar (Granicus)
            try:
                data = _json_ok(polite_get(f"https://webapi.legistar.com/v1/{client}/bodies", contact,
                                         params={"$top": 1}))
            except httpx.HTTPError:
                data = None
            if isinstance(data, list) and data:
                out.append(Source(name=f"{gov} — meetings (Legistar)", url=f"https://{client}.legistar.com/",
                                  category="civic", method="api", fetcher="legistar", params={"client": client},
                                  origin="meeting software", jurisdiction=juris,
                                  notes=f"Legistar account '{client}' matched by name — confirm it is this {gov}."))
                break
        for tenant in candidates:                                   # CivicClerk
            try:
                data = _json_ok(polite_get(f"https://{tenant}.api.civicclerk.com/v1/Events", contact,
                                         params={"$top": 1}))
            except httpx.HTTPError:
                data = None
            if isinstance(data, dict) and isinstance(data.get("value"), list):
                out.append(Source(name=f"{gov} — meetings (CivicClerk)",
                                  url=f"https://{tenant}.portal.civicclerk.com/", category="civic", method="api",
                                  fetcher="civicclerk", params={"tenant": tenant}, origin="meeting software",
                                  jurisdiction=juris, notes=f"CivicClerk tenant '{tenant}' matched by name."))
                break
        for tenant in candidates:                                   # PrimeGov: portal only, no public API
            url = f"https://{tenant}.primegov.com/public/portal"
            try:
                r = web_get(url, contact)
            except httpx.HTTPError:
                continue
            if r.status_code == 200 and slug(gov.split()[0]) in slug(r.text[:20000]):
                out.append(Source(name=f"{gov} — meetings (PrimeGov)", url=url, category="civic", method="listed",
                                  origin="meeting software", jurisdiction=juris,
                                  notes="PrimeGov portal found; agendas are PDFs — open the link."))
                break
    return out


# Socrata open-data network (used by hundreds of US cities, counties and states)
SOCRATA_CATALOG = "https://api.us.socrata.com/api/catalog/v1"
SOCRATA_TOPICS = [  # (section, catalogue search, dataset-name rule, names to avoid)
    ("public_safety", "crime data", r"crime|offen[cs]e|incident report",
     r"hate|use of force|officer|complaint|terry|stops?\b|arrests? by|summary|rate"),
    ("public_safety", "police calls", r"police|calls? for service|call data|dispatch|\b911\b",
     r"officer|use of force|complaint|stations?|boundar|beats?\b|budget|staff"),
    ("public_safety", "fire 911", r"fire|\bems\b|911|emergency", r"stations?|hydrant|inspection|budget"),
    ("real_estate", "building permits", r"permit",
     r"right.of.way|street use|sign|tree|electrical|side ?sewer|trade|fees?|parking|special event|film"),
    ("real_estate", "land use permits", r"land use|design review|zoning|development (permit|application)", r"map|plan\b"),
    ("real_estate", "property sales", r"\bsales?\b|deeds?|transfers?|conveyance",
     r"liquor|tax(able)?\b|retail|vehicle|food|ticket|cannabis|surplus"),
    ("business", "food inspections", r"inspection|restaurant|food establishment", r"elevator|boiler|vehicle|building|fire"),
    ("business", "business licenses", r"business licen|tax certificate|new business|business registr",
     r"transport|vehicle|dealer|for hire|limousine|taxi|contractor|towing"),
    ("business", "liquor license applications", r"liquor|cannabis", r"violation|enforcement|sales report|tax"),
    ("civic", "311 service requests", r"\b311\b|service request|code (enforcement|violation|complaint)", r"summary"),
]
_STATE_TOPICS = {"business licenses", "liquor license applications", "property sales"}


def stale_name(name: str) -> bool:
    """Archived or single-year datasets; '2008-Present' style names are fine."""
    n = re.sub(r"\b(19|20)\d\d\s*(-|–|to)\s*(present|current|now|today)\b", "", name, flags=re.I)
    return bool(re.search(r"archiv|historic|summary|statistic|totals|\bby (year|month)\b|\b(19\d\d|20[01]\d|202[0-4])\b",
                          n, re.I))


_DATE_TYPES = {"calendar_date", "floating_timestamp", "fixed_timestamp", "date"}
_GEO_TYPES = {"point", "location", "multipoint"}


@st.cache_data(ttl=7 * 86400, show_spinner=False)
def socrata_domains(contact: str) -> list[str]:
    r = polite_get(SOCRATA_CATALOG + "/domains", contact)
    r.raise_for_status()
    return [d.get("domain", "") for d in r.json().get("results", []) if isinstance(d, dict) and d.get("domain")]


def match_socrata_domains(domains: list[str], place: dict) -> list[tuple[str, str]]:
    """Portals whose web address names the city, county or state: [(domain, level)]."""
    city, county = slug(place.get("city")), slug(place.get("county"))
    st_code, state = (place.get("state_code") or "").lower(), slug(place.get("state"))
    found = []
    for d in domains:
        labels = d.lower().removeprefix("www.").split(".")
        names = set(labels[:-1])
        if len(city) >= 4 and (names & {city, "cityof" + city, city + st_code, city + "gov"}):
            found.append((d, "city"))
        elif len(county) >= 6 and (names & {county, county + st_code}):
            found.append((d, "county"))
        elif labels[-1] == "gov" and (names & {st_code, state}) and len(names) <= 2:
            found.append((d, "state"))
    order = {"city": 0, "county": 1, "state": 2}
    return sorted(dict.fromkeys(found), key=lambda x: order[x[1]])


def _dt_any(value) -> dt.datetime | None:
    if isinstance(value, (int, float)):
        return dt.datetime.fromtimestamp(value, dt.timezone.utc)
    return parse_date(value) if value else None


def socrata_sources(place: dict, contact: str, cap: int = 12, max_age_days: int = 60) -> list[Source]:
    """Finds the place's open-data portals and their incident, permit, inspection, licence and 311 datasets."""
    try:
        portals = match_socrata_domains(socrata_domains(contact), place)
    except (httpx.HTTPError, ValueError):
        portals = []
    if not portals:  # fall back to a catalogue search for the city's name
        try:
            r = polite_get(SOCRATA_CATALOG, contact, params={"q": place.get("city") or place["label"], "limit": 50})
            data = _json_ok(r)
            doms = [(x.get("metadata") or {}).get("domain", "") for x in
                    (data.get("results", []) if isinstance(data, dict) else []) if isinstance(x, dict)]
            portals = match_socrata_domains([d for d in doms if d], place)
        except httpx.HTTPError:
            portals = []
    portals = portals[:4]
    fresh_after = dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=max_age_days)
    out: list[Source] = []
    for domain, level in portals:
        for section, q, rule, avoid in SOCRATA_TOPICS:
            if level == "state" and q not in _STATE_TOPICS:   # statewide: licences and sales only
                continue
            try:
                r = polite_get(SOCRATA_CATALOG, contact, params={"domains": domain, "only": "dataset", "q": q, "limit": 20})
                data = _json_ok(r)
                results = data.get("results", []) if isinstance(data, dict) else []
            except httpx.HTTPError:
                continue
            best = None
            for res in results:
                rs = (res.get("resource") or {}) if isinstance(res, dict) else {}
                ds_id, name = rs.get("id", ""), rs.get("name", "")
                if not re.fullmatch(r"[a-z0-9]{4}-[a-z0-9]{4}", ds_id or "") or not re.search(rule, name, re.I) \
                        or (avoid and re.search(avoid, name, re.I)) or stale_name(name) \
                        or any(s.params.get("dataset") == ds_id for s in out):
                    continue
                updated = _dt_any(rs.get("data_updated_at") or rs.get("updatedAt"))
                if updated and updated < fresh_after:
                    continue
                types = {str(t).lower().replace(" ", "_") for t in rs.get("columns_datatype") or []}
                fields = [str(f).lower() for f in rs.get("columns_field_name") or []]
                has_date = bool(types & _DATE_TYPES) or not types
                has_geo = bool(types & _GEO_TYPES) or any(re.search(r"(^|_)lat(itude)?$", f) for f in fields) or not types
                has_area = any(re.search(r"zip|postal|city", f) for f in fields)
                if not has_date:
                    continue
                views = ((rs.get("page_views") or {}).get("page_views_total") or 0)
                if has_geo and level != "state":
                    kind = "socrata_geo"
                elif has_area and (place.get("postcode") or place.get("city")):
                    kind = "socrata_search"
                elif has_geo:
                    kind = "socrata_geo"
                else:
                    continue
                if best is None or views > best[0]:
                    best = (views, ds_id, name, kind)
            if best:
                _, ds_id, name, kind = best
                params = {"domain": domain, "dataset": ds_id, "require_date": True}
                out.append(Source(name=f"{name} ({domain})", url=f"https://{domain}/d/{ds_id}", category=section,
                                  method="api", fetcher=kind, params=params, origin="open-data catalog",
                                  notes=f"Found on the {level} open-data portal. "
                                        + ("Filtered to your radius." if kind == "socrata_geo" else "Searched by ZIP.")))
            if len(out) >= cap:
                return out
    return out


_AGGREGATORS = ("news.google.com", "yahoo.com", "msn.com", "aol.com", "newsbreak.com", "apple.news", "flipboard.com",
                "ground.news", "nytimes.com", "washingtonpost.com", "cnn.com", "foxnews.com", "apnews.com",
                "usatoday.com", "nbcnews.com", "cbsnews.com", "abcnews.go.com", "reuters.com", "bloomberg.com",
                "wsj.com", "theguardian.com", "npr.org", "bbc.com", "bbc.co.uk", "youtube.com")


def publisher_sources(items: list[Item], existing: list[Source], min_hits: int = 2, cap: int = 8) -> list[Source]:
    """Publishers the news searches show covering this place, so their own sites can be crawled too."""
    counts, names = collections.Counter(), {}
    for it in items:
        if it.found_by != "news search" or not it.publisher_url.startswith("http"):
            continue
        host = urllib.parse.urlsplit(it.publisher_url).netloc.lower().removeprefix("www.")
        if not host or is_blocked(it.publisher_url) or any(host == a or host.endswith("." + a) for a in _AGGREGATORS):
            continue
        counts[it.publisher_url] += 1
        names[it.publisher_url] = it.source
    have = [s.url for s in existing]
    out = []
    for url, n in counts.most_common():
        if n < min_hits or any(same_site(url, h) for h in have):
            continue
        have.append(url)
        out.append(Source(name=names[url], url=url, category="news", method="web", origin="news publisher",
                          notes=f"Covered this place in {n} search results."))
        if len(out) >= cap:
            break
    return out


def discover_sources(place: dict, contact: str, opts: dict) -> tuple[list[Source], list[str]]:
    """Runs every discovery method in parallel (they hit different services) and reports what each found."""
    city, county = place.get("city"), place.get("county")

    def gov_sites():
        sites = government_websites(city or "", county or "", place.get("state") or "", contact)
        out = []
        for level, site in sites.items():
            out += government_site_sources(level, site, city if level == "city" else county, contact)
        return out

    jobs = {
        "City & county websites": gov_sites,
        "OpenStreetMap": lambda: osm_sources(place, contact, opts["locality_km"], opts["osm_cap"]),
        "Meeting software": lambda: meeting_software_sources(place, contact),
        "Open-data catalog": lambda: socrata_sources(place, contact, opts["data_cap"]),
    }
    sources, notes = [nws_source()], []
    with cf.ThreadPoolExecutor(max_workers=len(jobs)) as pool:
        futures = {name: pool.submit(fn) for name, fn in jobs.items()}
        for name, fut in futures.items():
            try:
                found = fut.result()
                sources += found
                notes.append(f"{name}: {len(found)} found" + (f" ({', '.join(s.name for s in found[:4])}"
                                                              f"{'…' if len(found) > 4 else ''})" if found else ""))
            except Exception as e:
                notes.append(f"{name}: skipped — {type(e).__name__}: {str(e)[:100]}")
    return sources, notes


# --------------------------------------------------------------------------------------
# Step 3 — crawl: every method a website offers
# --------------------------------------------------------------------------------------
_LINK_TAG = re.compile(r"<link\b[^>]*>", re.I)
_LD_JSON = re.compile(r"<script[^>]+type=[\"']application/ld\+json[\"'][^>]*>(.*?)</script>", re.S | re.I)
_ICS_HREF = re.compile(r"href=[\"']([^\"']*(?:\.ics\b|[?&]ical=1|/ical/?|webcal:)[^\"']*)[\"']", re.I)
_A_HREF = re.compile(r"<a\b[^>]*href=[\"']([^\"'#]+)[\"']", re.I)
_ARTICLE_HINT = re.compile(r"/20\d{2}/|/news/|/events?/|/stor(y|ies)/|/articles?/|/blog/|/obituar|/posts?/|/calendar/", re.I)
_SKIP_PATH = re.compile(r"/(tag|tags|category|categories|author|page|wp-content|wp-json|feed|login|search|"
                        r"cart|account|privacy|terms|contact|about|subscribe)(/|$)|\.(jpe?g|png|gif|pdf|zip|mp3|mp4|ics)$",
                        re.I)
_ARTICLE_TYPES = {"NewsArticle", "Article", "BlogPosting", "Report", "LiveBlogPosting", "AnalysisNewsArticle"}


def find_feed_in_html(page_html: str, page_url: str) -> str | None:
    for tag in _LINK_TAG.findall(page_html[:300_000]):
        low = tag.lower()
        if "alternate" in low and ("rss+xml" in low or "atom+xml" in low) and "comment" not in low:
            m = re.search(r"href=[\"']([^\"']+)", tag, re.I)
            if m:
                return urllib.parse.urljoin(page_url, html.unescape(m.group(1)))
    return None


def guess_feed(page_url: str, contact: str) -> str | None:
    base = page_url.rstrip("/") + "/"
    for guess in ("feed/", "rss", "feed.xml", "rss.xml", "index.xml"):
        url = urllib.parse.urljoin(base, guess)
        try:
            g = web_get(url, contact)
        except httpx.HTTPError:
            continue
        if g.status_code == 200 and re.search(r"<(rss|feed)\b", g.text[:3000], re.I):
            return url
    return None


def items_from_feed(src: Source, feed_url: str, contact: str, tz: str) -> list[Item]:
    r = web_get(feed_url, contact)
    r.raise_for_status()
    flags = page_rights(r, "", contact)
    feed = feedparser.parse(r.content)
    news = src.origin == "news search"
    out = []
    for e in feed.entries:
        pub = (e.get("source") or {}) if news else {}
        out.append(Item(
            source=pub.get("title") or src.name, section=src.category, title=clean(e.get("title", ""), 220),
            url=e.get("link", src.url),
            published=parse_date(e.get("published_parsed") or e.get("updated_parsed"), tz),
            summary="" if news else clean(e.get("summary", ""), 400), via=src.name,
            found_by="news search" if news else "feed", publisher_url=pub.get("href", "") or "",
        ))
    return apply_rights(out, flags, feed_url)


def _ld_objects(page_html: str) -> list[dict]:
    out = []
    for blob in _LD_JSON.findall(page_html):
        try:
            data = json.loads(blob.strip())
        except json.JSONDecodeError:
            continue
        stack = [data]
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                stack.extend(x)
            elif isinstance(x, dict):
                out.append(x)
                for key in ("@graph", "itemListElement", "item", "mainEntity", "subEvent"):
                    if key in x:
                        stack.append(x[key])
    return out


def _types(obj: dict) -> list[str]:
    t = obj.get("@type", [])
    return [t] if isinstance(t, str) else [str(v) for v in t]


def _place_text(loc) -> str:
    if isinstance(loc, list):
        loc = loc[0] if loc else {}
    if isinstance(loc, str):
        return loc
    if isinstance(loc, dict):
        addr = loc.get("address", "")
        if isinstance(addr, dict):
            addr = ", ".join(str(addr.get(k, "")) for k in ("streetAddress", "addressLocality") if addr.get(k))
        return ", ".join(p for p in (str(loc.get("name", "")), str(addr)) if p)
    return ""


def _geo(loc) -> tuple[float | None, float | None]:
    if isinstance(loc, list):
        loc = loc[0] if loc else {}
    geo = loc.get("geo") if isinstance(loc, dict) else None
    if isinstance(geo, dict):
        try:
            return float(geo["latitude"]), float(geo["longitude"])
        except (KeyError, TypeError, ValueError):
            pass
    return None, None


def items_from_structured_data(page_html: str, src: Source, page_url: str, tz: str, found_by: str) -> list[Item]:
    out = []
    for obj in _ld_objects(page_html):
        types = _types(obj)
        url = obj.get("url") or obj.get("@id") or page_url
        url = url if isinstance(url, str) and url.startswith("http") else page_url
        if any(t.endswith("Event") for t in types):
            name = clean(str(obj.get("name", "")), 220)
            if not name:
                continue
            lat, lon = _geo(obj.get("location"))
            out.append(Item(source=src.name, section="events", title=name, url=url,
                            starts=parse_date(obj.get("startDate"), tz), where=clean(_place_text(obj.get("location")), 160),
                            summary=clean(str(obj.get("description", "")), 400), via=src.name, found_by=found_by,
                            lat=lat, lon=lon))
        elif _ARTICLE_TYPES.intersection(types):
            title = clean(str(obj.get("headline") or obj.get("name") or ""), 220)
            if not title or url.rstrip("/") == src.url.rstrip("/"):
                continue
            out.append(Item(source=src.name, section=src.category, title=title, url=url,
                            published=parse_date(obj.get("datePublished") or obj.get("dateCreated"), tz),
                            summary=clean(str(obj.get("description", "")), 400), via=src.name, found_by=found_by))
    return out


def items_from_calendar(src: Source, ics_url: str, contact: str, tz: str) -> list[Item]:
    if icalendar is None:
        return []
    r = web_get(ics_url.replace("webcal://", "https://"), contact)
    r.raise_for_status()
    flags = page_rights(r, "", contact)
    cal = icalendar.Calendar.from_ical(r.content)
    out = []
    for ev in cal.walk("VEVENT"):
        start = ev.get("DTSTART")
        out.append(Item(
            source=src.name, section="events", title=clean(str(ev.get("SUMMARY", "Event")), 220),
            url=str(ev.get("URL") or src.url), starts=parse_date(start.dt if start else None, tz),
            where=clean(str(ev.get("LOCATION", "")), 160), summary=clean(str(ev.get("DESCRIPTION", "")), 400),
            via=src.name, found_by="calendar",
        ))
    return apply_rights(out, flags, ics_url)


def sitemap_urls(site_url: str, contact: str, cutoff: dt.datetime, cap: int, tz: str) -> list[str]:
    """Recent page URLs from the site's sitemaps (robots.txt Sitemap lines, then common paths)."""
    p = urllib.parse.urlsplit(site_url)
    root = f"{p.scheme}://{p.netloc}"
    queue = robots_sitemaps(site_url, contact) or [
        root + "/sitemap.xml", root + "/sitemap_index.xml", root + "/wp-sitemap.xml", root + "/news-sitemap.xml"]
    seen, found = set(), []
    while queue and len(seen) < 6 and len(found) < cap * 3:
        sm = queue.pop(0)
        if sm in seen or sm.endswith(".gz"):
            continue
        seen.add(sm)
        try:
            r = web_get(sm, contact)
        except httpx.HTTPError:
            continue
        if r.status_code != 200 or "<" not in r.text[:200]:
            continue
        xml = r.text
        if "<sitemapindex" in xml:
            children = []
            for block in re.findall(r"<sitemap>(.*?)</sitemap>", xml, re.S):
                loc = re.search(r"<loc>\s*(.*?)\s*</loc>", block, re.S)
                mod = re.search(r"<lastmod>\s*(.*?)\s*</lastmod>", block, re.S)
                if not loc:
                    continue
                when = parse_date(mod.group(1), tz) if mod else None
                if when and when < cutoff:
                    continue
                score = 1 if re.search(r"post|news|article|event|obit|stor", loc.group(1), re.I) else 0
                children.append((score, when or cutoff, html.unescape(loc.group(1))))
            children.sort(reverse=True)
            queue.extend(c[2] for c in children[:3])
            continue
        for block in re.findall(r"<url>(.*?)</url>", xml, re.S):
            loc = re.search(r"<loc>\s*(.*?)\s*</loc>", block, re.S)
            mod = re.search(r"<(?:news:publication_date|lastmod)>\s*(.*?)\s*</", block, re.S)
            if not loc:
                continue
            when = parse_date(mod.group(1), tz) if mod else None
            if when and when >= cutoff:
                found.append((when, html.unescape(loc.group(1))))
    found.sort(reverse=True)
    out = [u for _, u in found if not _SKIP_PATH.search(urllib.parse.urlsplit(u).path)]
    return out[:cap]


def page_links(page_html: str, page_url: str, cap: int) -> list[str]:
    """Same-site links that look like individual articles, events or posts."""
    out, seen = [], set()
    for href in _A_HREF.findall(page_html):
        u = urllib.parse.urljoin(page_url, html.unescape(href)).split("#")[0]
        p = urllib.parse.urlsplit(u)
        if p.scheme not in ("http", "https") or not same_site(u, page_url) or _SKIP_PATH.search(p.path) \
                or "ical" in p.query.lower():
            continue
        if u.rstrip("/") == page_url.rstrip("/") or u in seen:
            continue
        slug = p.path.rstrip("/").rsplit("/", 1)[-1]
        if _ARTICLE_HINT.search(p.path) or slug.count("-") >= 3:
            seen.add(u)
            out.append(u)
            if len(out) >= cap:
                break
    return out


def _meta(page_html: str, *names: str) -> str:
    for n in names:
        m = re.search(rf"<meta[^>]+(?:property|name)=[\"']{re.escape(n)}[\"'][^>]+content=[\"']([^\"']+)", page_html, re.I) \
            or re.search(rf"<meta[^>]+content=[\"']([^\"']+)[\"'][^>]+(?:property|name)=[\"']{re.escape(n)}[\"']", page_html, re.I)
        if m:
            return html.unescape(m.group(1))
    return ""


def item_from_page(url: str, src: Source, contact: str, tz: str, want_text: bool, found_by: str) -> list[Item]:
    try:
        r = web_get(url, contact)
    except httpx.HTTPError:
        return []
    if r.status_code >= 400 or "html" not in r.headers.get("content-type", "html"):
        return []
    page = r.text
    flags = page_rights(r, page, contact)
    if rights_action(flags) == "skip":
        return apply_rights([], flags, url)
    if rights_action(flags) == "link-only":
        want_text = False
    structured = items_from_structured_data(page, src, str(r.url), tz, found_by)
    text = ""
    if want_text and trafilatura is not None:
        text = (trafilatura.extract(page, url=str(r.url), include_comments=False) or "")[:8000]
    if structured:
        for it in structured:
            it.text = it.text or text
        return apply_rights(structured[:5], flags, url)
    # Explicit publication metadata first; the extractor's date guess only as a fallback, and never a
    # bare "1 January" (that is what a year mention like "1941–2026" in an obituary title produces).
    title = _meta(page, "og:title")
    date = parse_date(_meta(page, "article:published_time", "og:published_time", "date", "pubdate"), tz)
    desc = _meta(page, "og:description", "description")
    if trafilatura is not None and not (title and date):
        try:
            meta = trafilatura.extract_metadata(page, default_url=str(r.url),
                                                date_config={"extensive_search": False, "original_date": True})
        except TypeError:
            meta = trafilatura.extract_metadata(page, default_url=str(r.url))
        if meta is not None:
            title = title or meta.title or ""
            guess = parse_date(meta.date, tz)
            if guess and not (guess.month == 1 and guess.day == 1):
                date = date or guess
            desc = desc or meta.description or ""
    title = title or clean((re.search(r"<title>(.*?)</title>", page, re.S | re.I) or [None, ""])[1], 220)
    desc = desc or _meta(page, "og:description", "description")
    if not title:
        return []
    return apply_rights([Item(source=src.name, section=src.category, title=clean(title, 220), url=str(r.url),
                              published=date, summary=clean(desc, 400), text=text, via=src.name, found_by=found_by)],
                        flags, url)


def extract_full_text(url: str, contact: str) -> str:
    """Main article text of a page (robots.txt respected). Empty string when not allowed or not found."""
    if trafilatura is None or not url.startswith("http"):
        return ""
    try:
        r = web_get(url, contact)
    except httpx.HTTPError:
        return ""
    if r.status_code >= 400 or "html" not in r.headers.get("content-type", "html"):
        return ""
    if rights_action(page_rights(r, r.text, contact)) != "ok":
        return ""
    return (trafilatura.extract(r.text, url=str(r.url), include_comments=False) or "")[:8000]


def crawl_site(src: Source, contact: str, cutoff: dt.datetime, opts: dict) -> list[Item]:
    tz = opts["tz"]
    items: list[Item] = []
    if src.feed_url:  # given feed (news searches, city-site feeds, Claude-supplied feeds)
        items += items_from_feed(src, src.feed_url, contact, tz)
    if src.origin == "news search" or src.method == "feed":
        return items
    try:
        r = web_get(src.url, contact)
    except Disallowed as e:
        src.notes = (src.notes + f" · {e}").strip(" ·")
        if items:
            return items
        raise
    r.raise_for_status()
    page, page_url = r.text, str(r.url)
    flags = page_rights(r, page, contact)
    if rights_action(flags) == "skip":
        apply_rights([], flags, page_url)
        src.notes = (src.notes + " · homepage opts out (" + ", ".join(sorted(flags)) + ")").strip(" ·")
        return items

    feed = find_feed_in_html(page, page_url) or (None if src.feed_url else guess_feed(page_url, contact))
    if feed and feed != src.feed_url:
        src.feed_url = feed
        try:
            items += items_from_feed(src, feed, contact, tz)
        except httpx.HTTPError:
            pass
    if not opts["deep"]:
        return items

    items += apply_rights(items_from_structured_data(page, src, page_url, tz, "structured data"), flags, page_url)
    if src.category == "civic" or src.origin in ("city website", "county website", "meeting software"):
        items += apply_rights(document_items(page, page_url, src, tz), flags, page_url)
    for ics in list(dict.fromkeys(_ICS_HREF.findall(page)))[:2]:
        try:
            items += items_from_calendar(src, urllib.parse.urljoin(page_url, html.unescape(ics)), contact, tz)
        except Exception:
            pass

    budget = opts["pages_per_source"]
    if budget and len(items) < opts["limit"]:
        have = {i.url for i in items}
        candidates = [("sitemap", u) for u in sitemap_urls(page_url, contact, cutoff, budget, tz)]
        if len(candidates) < budget:
            candidates += [("page link", u) for u in page_links(page, page_url, budget * 2)]
        fetched = 0
        for how, u in candidates:
            if u in have or fetched >= budget:
                continue
            have.add(u)
            fetched += 1
            items += item_from_page(u, src, contact, tz, opts["full_text"] and fetched <= opts["full_text_n"], how)
    return items


# --------------------------------------------------------------------------------------
# Step 3b — open-data and civic APIs
# --------------------------------------------------------------------------------------
def api_nws(src, place, contact, cutoff, opts):
    r = polite_get("https://api.weather.gov/alerts/active", contact,
                 params={"point": f"{place['lat']:.4f},{place['lon']:.4f}"}, accept="application/geo+json")
    r.raise_for_status()
    return [Item(source=src.name, section="weather", title=p.get("headline") or p.get("event", "Weather alert"),
                 url=p.get("@id") or src.url, published=parse_date(p.get("sent")),
                 summary=clean(p.get("description", ""), 400), via=src.name, found_by="api")
            for p in (f.get("properties", {}) for f in r.json().get("features", []))]


@functools.lru_cache(maxsize=64)
def socrata_columns(domain: str, dataset: str, contact: str) -> tuple:
    r = polite_get(f"https://{domain}/api/views/{dataset}.json", contact)
    r.raise_for_status()
    return tuple((c.get("fieldName", ""), c.get("dataTypeName", "")) for c in r.json().get("columns", []))


# Police & fire calls: what happened, when, where — in plain words, located to the block
CALL_PLAIN = [  # (pattern in the agency's call type, plain-English label) — first match wins
    (r"low acuity", "Non-urgent medical or assistance call"),
    (r"scenes? of violence", "Medical response to a violent incident"),
    (r"\bmvi\b|motor vehicle incident", "Traffic collision"),
    (r"rescue elevator|elevator", "Elevator rescue"),
    (r"trans(port)? to amr|\bamr\b", "Patient taken to hospital by ambulance"),
    (r"hang.?up", "911 hang-up — crew checked"),
    (r"water job|water leak|flood", "Water leak or flooding"),
    (r"fuel spill|spill", "Fuel or chemical spill"),
    (r"out of service", "Crew investigated a reported problem"),
    (r"aid response|\baid\b|first aid", "Medical aid call"),
    (r"medic|\bems\b|medical|person down|unconscious|overdose|cardiac|breathing", "Medical emergency (paramedics)"),
    (r"car prowl|vehicle prowl|auto prowl|theft from (auto|vehicle)", "Car break-in"),
    (r"auto theft|vehicle theft|stolen (car|vehicle|auto)|\bmvt\b", "Stolen vehicle"),
    (r"shoplift", "Shoplifting"),
    (r"burglar", "Burglary"),
    (r"robbery", "Robbery"),
    (r"shots? fired|shooting|gunfire|\bshots\b", "Shots fired"),
    (r"assault|\bfight\b", "Assault or fight"),
    (r"domestic|\bdv\b", "Domestic dispute"),
    (r"weapon|\bgun\b|knife", "Weapon reported"),
    (r"trespass", "Trespassing"),
    (r"suspicious", "Suspicious person or vehicle"),
    (r"noise|disturb|nuisance", "Disturbance or noise"),
    (r"traffic stop|onview.*traffic|traffic violation", "Traffic stop"),
    (r"collision|\bmvc\b|\bmva\b|crash|accident|hit and run", "Traffic collision"),
    (r"\bdui\b|impaired", "Impaired driving"),
    (r"fire alarm|\bafa\b|automatic alarm", "Automatic fire alarm"),
    (r"(building|structure|residential|commercial|house|apartment) fire", "Building fire"),
    (r"(vehicle|car|auto) fire", "Vehicle fire"),
    (r"(brush|grass|rubbish|dumpster|trash|outside|bark) fire", "Outdoor fire"),
    (r"\bfire\b", "Fire"),
    (r"gas leak|odor|hazmat|hazardous|natural gas", "Gas leak or hazardous materials"),
    (r"water rescue|rescue", "Rescue"),
    (r"theft|larceny|stolen", "Theft"),
    (r"vandal|graffiti|property damage|destruction|mischief", "Vandalism"),
    (r"welfare|check on", "Welfare check"),
    (r"missing|runaway", "Missing person"),
    (r"narcotic|drug", "Drug activity"),
    (r"alarm", "Alarm"),
    (r"parking|abandoned vehicle", "Parking or abandoned vehicle"),
]
_CALL_RES = [(re.compile(rx, re.I), label) for rx, label in CALL_PLAIN]
_WHAT_COLS = r"final_call_type|initial_call_type|call_?type|^type$|incident_?type|event_?type|offen[cs]e(_?(type|description|category))?$|crime_?type|nature|^category$|description$"
_OUTCOME_COLS = r"disposition|clearance|outcome|resolution|^status$|result"
_AREA_COLS = r"beat|sector|precinct|district|neighbou?rhood|mcpp|zone"
_ADDR_COLS = r"address|block|street|location_?(text|desc)|hundred"


def tidy_code(text: str) -> str:
    """'--THEFT - CAR PROWL' → 'Theft - car prowl'."""
    t = re.sub(r"\s+", " ", re.sub(r"^[^A-Za-z0-9]+", "", str(text or ""))).strip(" -")
    return t[:1].upper() + t[1:].lower() if t.isupper() else t


def plain_call(raw: str) -> str:
    for rx, label in _CALL_RES:
        if rx.search(raw or ""):
            return label
    return tidy_code(raw) or "Call for service"


def to_block(address: str) -> str:
    """'5432 Ballard Ave NW' → '5400 block of Ballard Ave NW' (privacy: no exact house numbers)."""
    a = re.sub(r"\s+", " ", str(address or "")).strip()
    m = re.match(r"^(\d+)[A-Za-z]?\s+(?!block\b|blk\b)(.+)$", a, re.I)
    if m:
        return f"{int(m.group(1)) // 100 * 100} block of {name_case(m.group(2))}"
    return name_case(re.sub(r"\b(\d+)\s+blk\b", r"\1 block of", a, flags=re.I))


def map_link(lat: float | None, lon: float | None) -> str:
    if lat is None or lon is None:
        return ""
    return f"https://www.openstreetmap.org/?mlat={lat:.5f}&mlon={lon:.5f}#map=17/{lat:.5f}/{lon:.5f}"


def incident_details(row: dict, cols: dict, title_fields: list, address_fields: list) -> dict:
    """What happened (agency wording + plain words), outcome, priority, area and block-level address."""
    def first(pattern: str, unless: str = "") -> str:
        for c in cols:
            if re.search(pattern, c, re.I) and not (unless and re.search(unless, c, re.I)) \
                    and row.get(c) not in (None, ""):
                if isinstance(row[c], (str, int, float)):
                    return str(row[c])
        return ""
    raw = pick(row, title_fields) or first(_WHAT_COLS, unless=_OUTCOME_COLS)
    outcome = first(_OUTCOME_COLS)
    priority = first(r"priority")
    area_bits = [f"{c.replace('_', ' ').title()} {row[c]}" for c in cols
                 if re.search(_AREA_COLS, c, re.I) and isinstance(row.get(c), (str, int)) and str(row[c]).strip()][:2]
    address = pick(row, address_fields) or first(_ADDR_COLS)
    return {"raw": tidy_code(raw), "what": plain_call(raw), "outcome": tidy_code(outcome),
            "priority": priority, "area": ", ".join(area_bits), "block": to_block(address) if address else ""}


def describe_where(items: list[Item], points: list[tuple[str, float, float]], max_m: float = 350) -> None:
    """Police & fire calls without an address get 'near <landmark>' from the nearest named place."""
    for it in items:
        if it.section != "public_safety" or it.lat is None or it.lon is None or not points:
            continue
        name, plat, plon = min(points, key=lambda p: km_between(it.lat, it.lon, p[1], p[2]))
        d = km_between(it.lat, it.lon, plat, plon) * 1000
        if d <= max_m:
            near = f"near {name}"
            it.where = f"{it.where} ({near})" if it.where and near not in it.where else (it.where or near)


# Permits, property sales, business licences and inspections: readable records, newsworthy ones first
def _col(row: dict, cols, pattern: str, unless: str = "") -> str:
    for c in cols:
        if re.search(pattern, c, re.I) and not (unless and re.search(unless, c, re.I)):
            v = row.get(c)
            if isinstance(v, dict):                     # Socrata URL columns: {"url": ...}
                v = v.get("url") or ""
            if isinstance(v, (str, int, float)) and str(v).strip():
                return str(v).strip()
    return ""


def _num(value: str) -> float | None:
    try:
        return float(re.sub(r"[^\d.\-]", "", str(value))) if value not in (None, "") else None
    except ValueError:
        return None


def money(x: float) -> str:
    return f"${x / 1e6:.1f}M" if x >= 1e6 else f"${x / 1e3:.0f}K" if x >= 1e4 else f"${x:,.0f}"


def sentence(text: str, limit: int = 110) -> str:
    t = re.sub(r"\s+", " ", str(text or "")).strip(" .;")
    if t.isupper():
        t = t.lower()
    t = re.split(r"(?<=[a-z0-9\)])\.\s", t)[0]
    t = t[:1].upper() + t[1:]
    return t if len(t) <= limit else t[: limit - 1].rsplit(" ", 1)[0] + "…"


_DIRS = {"N", "S", "E", "W", "NE", "NW", "SE", "SW", "LLC", "INC", "PLLC", "LP", "USA", "WA", "US"}


def name_case(text: str) -> str:
    """'5432 24TH AVE NW' → '5432 24th Ave NW'; leaves mixed-case text alone."""
    t = re.sub(r"\s+", " ", str(text or "")).strip()
    if not t.isupper():
        return t
    words = []
    for w in t.split(" "):
        core = w.strip(".,")
        if core in _DIRS or re.fullmatch(r"\d+X+", core):
            words.append(w)
        elif core in ("OF", "AND", "THE", "AT", "BLOCK"):
            words.append(w.lower())
        elif re.fullmatch(r"\d+(ST|ND|RD|TH)", core):
            words.append(w.lower())
        else:
            words.append(w.capitalize() if "/" not in w else "/".join(x.capitalize() for x in w.split("/")))
    return " ".join(words)


def pick_date_col(cols: dict, prefer: list) -> str | None:
    for c in prefer or []:
        if c in cols:
            return c
    dated = [c for c, t in cols.items() if t in ("calendar_date", "floating_timestamp", "fixed_timestamp", "date")]
    good = [c for c in dated if not re.search(r"expir|end|clos|due|complet|updated|modified|created", c, re.I)]
    for rx in (r"sale|issue|appl|start|recei|open|first|inspection|report|occur|offen[cs]e|incident|datetime|date"):
        for c in good:
            if re.search(rx, c, re.I):
                return c
    return (good or dated or [None])[0]


_MINOR_WORK = r"re-?roof|furnace|water heater|electrical|plumbing|mechanical|solar|\bsign\b|fence|\bdeck\b|repair|" \
              r"replace (windows|siding)|hvac|boiler|side sewer|gas piping|heat pump"


def record_details(section: str, row: dict, cols) -> dict | None:
    """Title, where, summary, link and a newsworthiness score for one open-data row (None = leave it out)."""
    addr = _col(row, cols, _ADDR_COLS, unless=r"city|state|zip|postal|mail|owner|business_?street")
    link = _col(row, cols, r"^link$|url|hyperlink")
    link = link if link.startswith("http") else ""
    status = _col(row, cols, r"status")
    if section == "real_estate":
        price = _num(_col(row, cols, r"sale_?price|price|amount|consideration", unless=r"per|tax|assess"))
        if price is not None and _col(row, cols, r"sale|deed|transfer|grantor|grantee|excise"):
            if price < 10_000:                     # gifts, quit-claims and other non-market transfers
                return None
            kind = _col(row, cols, r"property_?(type|class|use)|land_?use|prop_?type|class")
            return {"title": f"Sold for {money(price)}" + (f": {name_case(addr)}" if addr else ""), "where": name_case(addr),
                    "summary": " · ".join(b for b in (name_case(kind), status) if b), "url": link, "score": 2}
        desc = (_col(row, cols, r"^description$") or _col(row, cols, r"work_?desc|project_?desc|scope|proposal")
                or _col(row, cols, r"desc(ription)?$", unless=r"type|class|status"))
        kind = _col(row, cols, r"permit_?type|permittype|permit_?class|permitclass|work_?class|^category$|^type$")
        added = _num(_col(row, cols, r"units?_?added|unitsadded|new_?units|dwelling_?units|housing_?units$"))
        removed = _num(_col(row, cols, r"units?_?removed|unitsremoved"))
        cost = _num(_col(row, cols, r"cost|valuation|value", unless=r"per|fee"))
        number = _col(row, cols, r"permit_?num|permitnum|record_?(id|num)|application_?num|project_?num")
        text = f"{desc} {kind}".lower()
        score = 0
        score += 3 if added and added > 0 else 0
        score += 2 if re.search(r"demoli", text) else 0
        score += 2 if re.search(r"new (construction|building|single|townhouse|rowhouse|apartment|mixed)|"
                                r"construct (a |an )?(new|\d)|erect|establish use", text) else 0
        score += (2 if cost >= 1_000_000 else 1 if cost >= 250_000 else 0) if cost else 0
        score += 1 if re.search(r"mixed.use|apartment|townhouse|rowhouse|\badu\b|accessory dwelling|restaurant|retail|"
                                r"school|park|change of use|grocery|cafe|brewery|daycare|child care", text) else 0
        score -= 2 if re.search(_MINOR_WORK, text) else 0
        bits = [f"adds {added:g} home{'s' if added != 1 else ''}" if added and added > 0 else "",
                f"removes {removed:g}" if removed and removed > 0 else "",
                f"est. cost {money(cost)}" if cost else "", f"status: {status.lower()}" if status else "",
                name_case(kind) if kind and desc else "", f"permit {number}" if number else ""]
        return {"title": sentence(desc) or name_case(kind) or "Building permit", "where": name_case(addr),
                "summary": " · ".join(b for b in bits if b), "url": link, "score": score}
    if section == "business":
        if status and re.search(r"expired|terminat|closed|inactive|revoked|cancel|discontinu|surrender|withdrawn", status, re.I):
            return None
        name = _col(row, cols, r"trade_?name|tradename|\bdba\b|doing_?business|business_?name|establishment|"
                               r"program_?identifier|^name$|licensee")
        kind = _col(row, cols, r"licen[cs]e_?(type|desc)|privilege|naics_?desc|business_?type|activity|^description$")
        result = _col(row, cols, r"inspection_?result|^result$|grade|violation_?desc")
        score_ = _col(row, cols, r"inspection_?score|^score$")
        bits = [name_case(kind), f"result: {result.lower()}" if result else "", f"score {score_}" if score_ else "",
                f"status: {status.lower()}" if status else ""]
        return {"title": name_case(name) or name_case(kind) or "Business record", "where": name_case(addr),
                "summary": " · ".join(b for b in bits if b), "url": link,
                "score": 2 if re.search(r"new|pending|appl|issued|active", status or "new", re.I) else 1}
    title = sentence(_col(row, cols, r"type|description|name|subject|category")) or "Record"
    return {"title": title, "where": name_case(addr), "summary": status, "url": link, "score": 1}


def api_socrata_geo(src, place, contact, cutoff, opts):
    """Any Socrata dataset: finds its date and location columns, filters to the radius and window."""
    p = src.params
    cols = dict(socrata_columns(p["domain"], p["dataset"], contact))
    date_col = pick_date_col(cols, p.get("date_fields", []))
    if p.get("require_date") and not date_col:
        raise ValueError("this dataset has no date column")
    point_col = next((c for c, t in cols.items() if t in ("point", "location")), None)
    lat_col = next((c for c in cols if re.search(r"(^|_)lat(itude)?$", c)), None)
    lon_col = next((c for c in cols if re.search(r"(^|_)(lon|lng|longitude)$", c)), None)

    where = []
    if date_col:
        since = cutoff.astimezone(ZoneInfo(opts["tz"])).strftime("%Y-%m-%dT%H:%M:%S")
        where.append(f"{date_col} > '{since}'")
    radius_m = int(opts["radius_km"] * 1000)
    geo = f"within_circle({point_col}, {place['lat']}, {place['lon']}, {radius_m})" if point_col else None
    def query(clauses: list[str]) -> dict:
        q = {"$limit": 2000}
        if date_col:
            q["$order"] = f"{date_col} DESC"
        if clauses:
            q["$where"] = " AND ".join(clauses)
        return q

    url = f"https://{p['domain']}/resource/{p['dataset']}.json"
    r = polite_get(url, contact, params=query(where + ([geo] if geo else [])))
    server_geo = bool(geo)
    if r.status_code == 400 and geo:  # geo filter not supported on this column: filter locally
        r = polite_get(url, contact, params=query(where))
        server_geo = False
    r.raise_for_status()

    out, rank = [], {}
    for row in r.json():
        dist = lat = lon = None
        if lat_col and lon_col:
            try:
                lat, lon = float(row[lat_col]), float(row[lon_col])
                dist = km_between(place["lat"], place["lon"], lat, lon)
            except (KeyError, TypeError, ValueError):
                dist = lat = lon = None
        if lat is None and point_col and isinstance(row.get(point_col), dict):  # {"type": "Point", ...} or legacy
            pt = row[point_col]
            try:
                lon, lat = map(float, pt["coordinates"][:2]) if "coordinates" in pt else \
                    (float(pt["longitude"]), float(pt["latitude"]))
                dist = km_between(place["lat"], place["lon"], lat, lon)
            except (KeyError, TypeError, ValueError):
                dist = lat = lon = None
        if not server_geo and (dist is None or dist > opts["radius_km"]):
            continue
        when = parse_date(row.get(date_col), opts["tz"]) if date_col else None
        extra = " · ".join(f"{k.replace('_', ' ')}: {row[k]}" for k in p.get("extra_fields", []) if row.get(k))
        if src.category == "public_safety":   # what happened · when · where
            d = incident_details(row, cols, p.get("title_fields") or [], p.get("address_fields") or [])
            bits = [f"Reported as: {d['raw']}" if d["raw"] and d["raw"].lower() != d["what"].lower() else "",
                    f"Outcome: {d['outcome']}" if d["outcome"] else "",
                    f"Priority {d['priority']}" if d["priority"] else "", d["area"], extra]
            out.append(Item(source=src.name, section=src.category, title=d["what"], url=src.url, published=when,
                            summary=" · ".join(b for b in bits if b), via=src.name, found_by="api", lat=lat, lon=lon,
                            where=d["block"] or "", map_url=map_link(lat, lon)))
        else:
            d = record_details(src.category, row, cols)
            if d is None or (src.category == "real_estate" and d["score"] < 1):   # routine repairs etc.
                continue
            if p.get("title_fields"):
                d["title"] = pick(row, p["title_fields"]) or d["title"]
            where_ = pick(row, p.get("address_fields", [])) or d["where"]
            out.append(Item(source=src.name, section=src.category, title=d["title"], url=d["url"] or src.url,
                            published=when, summary=" · ".join(b for b in (d["summary"], extra) if b), via=src.name,
                            found_by="api", lat=lat, lon=lon, where=where_, score=None,
                            map_url=map_link(lat, lon) if src.category == "real_estate" else ""))
            rank[id(out[-1])] = d["score"]
        if len(out) >= opts["limit"] * (4 if rank else 1):
            break
    if rank:   # most newsworthy first: new homes, demolitions, big projects
        out.sort(key=lambda i: (rank.get(id(i), 0), i.published or dt.datetime.min.replace(tzinfo=dt.timezone.utc)),
                 reverse=True)
    return out[: opts["limit"]]


def api_socrata_search(src, place, contact, cutoff, opts):
    """Datasets without coordinates (e.g. statewide licences or county sales): searched by ZIP code, recent rows only."""
    p = src.params
    cols = dict(socrata_columns(p["domain"], p["dataset"], contact))
    date_col = pick_date_col(cols, p.get("date_fields", []))
    if p.get("require_date") and not date_col:
        raise ValueError("this dataset has no date column")
    term = place.get("postcode") or place.get("city") or place["label"]
    params = {"$q": term, "$limit": min(opts["limit"] * 5, 1000)}
    if date_col:
        since = cutoff.astimezone(ZoneInfo(opts["tz"])).strftime("%Y-%m-%dT%H:%M:%S")
        params["$where"], params["$order"] = f"{date_col} > '{since}'", f"{date_col} DESC"
    url = f"https://{p['domain']}/resource/{p['dataset']}.json"
    r = polite_get(url, contact, params=params)
    if r.status_code == 400 and "$where" in params:
        params.pop("$where"), params.pop("$order", None)
        r = polite_get(url, contact, params=params)
    r.raise_for_status()
    out = []
    for row in r.json():
        if "title_fields" in p:                                   # curated sources keep their own fields
            d = {"title": pick(row, p["title_fields"], "Record"), "where": "", "url": "", "score": 1, "summary": ""}
        else:
            d = record_details(src.category, row, cols)
        if d is None:
            continue
        out.append(Item(source=src.name, section=src.category, title=d["title"], url=d["url"] or src.url,
                        published=parse_date(row.get(date_col), opts["tz"]) if date_col else None,
                        summary=d["summary"], where=d["where"], via=src.name, found_by="api"))
    return out


# Council & board meetings: every agenda item, its vote, and its attached documents
_PROCEDURAL = re.compile(
    r"^\s*(\d+[\.\)]\s*)?(call to order|roll call|approval of (the )?(agenda|minutes|journal)|adjourn|public comment|"
    r"items? of business|presentations?\s*$|executive session|consent (calendar|agenda)\s*$|reports? of (the )?(chair|president)|"
    r"payment of (the )?bills|introduction and referral|preliminary items|other business|announcements?|pledge|"
    r"chair'?s report|briefings?\s*$|council president'?s report|land acknowledg|approval of the journal)", re.I)
PUBLIC_RECORD = "public record — facts free to report"


def agenda_headline(title: str, matter_type: str = "", matter_name: str = "") -> str:
    """'AN ORDINANCE relating to land use and zoning; amending … 5601 24th Ave NW …' →
    'Ordinance: Land use and zoning — 5601 24th Ave NW'."""
    t = clean(title, 3000)
    kind = re.sub(r"\s*\(.*?\)\s*", " ", matter_type or "").strip()
    m = re.search(r"\brelating to\s+(.+?)(?:;|:|\.\s|$)", t, re.I)
    subject = re.sub(r"^the\s+", "", m.group(1).strip(" ,"), flags=re.I) if m else ""
    if subject:
        head = f"{kind or 'Legislation'}: {sentence(subject, 90)}"
    else:
        head = sentence(matter_name if matter_name and len(matter_name) > 12 else t, 110)
    addr = _ADDRESS.search(t)
    if addr and addr.group(0).strip().lower() not in head.lower():
        head += f" — {addr.group(0).strip()}"
    return head


def api_legistar(src, place, contact, cutoff, opts):
    client, tz = src.params["client"], opts["tz"]
    base = f"https://webapi.legistar.com/v1/{client}"
    params = {"$filter": f"EventDate ge datetime'{cutoff.date().isoformat()}'",
              "$orderby": "EventDate desc", "$top": opts["limit"]}
    r = polite_get(f"{base}/events", contact, params=params)
    r.raise_for_status()
    events = [ev for ev in r.json() if isinstance(ev, dict)]
    now = dt.datetime.now(dt.timezone.utc)
    out = []
    for ev in events:
        agenda = "agenda posted" if ev.get("EventAgendaFile") else "agenda not posted yet"
        docs = [(n, ev.get(k)) for n, k in (("Agenda", "EventAgendaFile"), ("Minutes", "EventMinutesFile"))
                if str(ev.get(k) or "").startswith("http")]
        when = parse_date(ev.get("EventDate"), tz)
        past = bool(when and when < now - dt.timedelta(hours=12))
        out.append(Item(source=src.name, section="civic", title=f"{ev.get('EventBodyName', 'Meeting')} meeting",
                        url=ev.get("EventInSiteURL") or ev.get("EventAgendaFile") or src.url,
                        starts=None if past else when, published=when if past else None,
                        where=clean(ev.get("EventLocation") or "", 160),
                        summary=clean(f"{ev.get('EventTime') or ''} · {agenda}" + (" · minutes posted" if len(docs) > 1 else ""), 300),
                        via=src.name, found_by="api", attachments=docs, use=PUBLIC_RECORD))

    # Open the agendas of the meetings closest to today: each item is a possible story
    deep = sorted((ev for ev in events if ev.get("EventId")),
                  key=lambda ev: abs(((parse_date(ev.get("EventDate"), tz) or now) - now).total_seconds()))
    for ev in deep[: opts.get("agenda_events", 10)]:
        try:
            rr = polite_get(f"{base}/events/{ev['EventId']}/eventitems", contact,
                            params={"AgendaNote": 1, "MinutesNote": 1, "Attachments": 1})
        except httpx.HTTPError:
            continue
        rows = _json_ok(rr)
        when = parse_date(ev.get("EventDate"), tz)
        body = ev.get("EventBodyName") or "council"
        day = f"{when:%a} {when.day} {when:%b}" if when else "a date not listed"
        for ei in rows if isinstance(rows, list) else []:
            title = str(ei.get("EventItemTitle") or "").strip()
            if len(title) < 15 or (_PROCEDURAL.match(title) and not ei.get("EventItemMatterId")):
                continue
            action = " ".join(str(x) for x in (ei.get("EventItemActionName"), ei.get("EventItemTally")) if x)
            if when and when < now:
                lead = f"{action.capitalize()} at the {body} meeting on {day}" if action else \
                    f"Taken up at the {body} meeting on {day}"
            else:
                lead = f"On the agenda for the {body} meeting on {day}"
            mid, guid = ei.get("EventItemMatterId"), ei.get("EventItemMatterGuid")
            url = (f"https://{client}.legistar.com/LegislationDetail.aspx?ID={mid}&GUID={guid}" if mid and guid
                   else ev.get("EventInSiteURL") or src.url)
            note = clean(ei.get("EventItemMinutesNote") or ei.get("EventItemAgendaNote") or "", 300)
            atts = [(clean(a.get("MatterAttachmentName") or "Attachment", 120), a.get("MatterAttachmentHyperlink"))
                    for a in ei.get("EventItemMatterAttachments") or []
                    if isinstance(a, dict) and str(a.get("MatterAttachmentHyperlink") or "").startswith("http")]
            out.append(Item(source=src.name, section="civic", url=url, published=when, via=src.name, found_by="agenda",
                            title=agenda_headline(title, ei.get("EventItemMatterType") or "", ei.get("EventItemMatterName") or ""),
                            summary=" · ".join(b for b in (lead, ei.get("EventItemMatterFile") or "", note,
                                                           f"Full title: {clean(title, 700)}") if b),
                            attachments=atts[:6], use=PUBLIC_RECORD))
    return out


def api_civicclerk(src, place, contact, cutoff, opts):
    tenant = src.params["tenant"]
    url = f"https://{tenant}.api.civicclerk.com/v1/Events"
    r = polite_get(url, contact, params={"$orderby": "startDateTime desc", "$top": opts["limit"]})
    if r.status_code == 400:
        r = polite_get(url, contact)
    r.raise_for_status()
    data = r.json()
    rows = data.get("value", []) if isinstance(data, dict) else data
    out = []
    for ev in rows if isinstance(rows, list) else []:
        docs = []
        for f in ev.get("publishedFiles") or []:     # agenda / minutes / packet (field names not vendor-documented)
            if not isinstance(f, dict):
                continue
            fid = f.get("fileId") or f.get("id")
            link = f.get("url") or (f"https://{tenant}.api.civicclerk.com/v1/Meetings/GetMeetingFileStream"
                                    f"(fileId={fid},plainText=false)" if fid else "")
            if str(link).startswith("http"):
                docs.append((clean(str(f.get("name") or f.get("type") or "Document"), 120), link))
        out.append(Item(source=src.name, section="civic",
                        title=pick(ev, ["eventName", "name", "title", "categoryName"], "Meeting"),
                        url=src.url, starts=parse_date(pick(ev, ["startDateTime", "eventDate", "date"]), opts["tz"]),
                        summary=clean(pick(ev, ["eventDescription", "description", "location"]), 300),
                        via=src.name, found_by="api", attachments=docs[:6], use=PUBLIC_RECORD))
    return out


# Documents: PDFs of agendas, minutes, staff reports and notices, read for mentions of the place
PDF_MAX_BYTES, PDF_MAX_PAGES = 15_000_000, 60
_DOC_LINK = re.compile(r"<a\b[^>]*href=[\"']([^\"'#]+)[\"'][^>]*>(.*?)</a>", re.I | re.S)
_DOC_HREF = re.compile(r"\.pdf($|\?)|/AgendaCenter/ViewFile/|View\.ashx|DocumentCenter/View|GetMeetingFileStream", re.I)
_DOC_WORDS = re.compile(r"agenda|minutes|packet|notice|hearing|staff report|report|ordinance|resolution|plan|budget", re.I)
_MONTHS = "jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec"


def date_in(text: str, tz: str) -> dt.datetime | None:
    """A date written in a link or file name: 2026-10-27, 10/27/2026, Oct 27, 2026, or CivicPlus _10272026."""
    t = text or ""
    for rx, order in ((r"(20\d\d)-(\d{1,2})-(\d{1,2})", "ymd"), (r"(\d{1,2})/(\d{1,2})/(20\d\d)", "mdy"),
                      (r"_(\d{2})(\d{2})(20\d\d)\b", "mdy")):
        if m := re.search(rx, t):
            a, b, c = (int(x) for x in m.groups())
            y, mo, d = (a, b, c) if order == "ymd" else (c, a, b)
            try:
                return dt.datetime(y, mo, d, tzinfo=ZoneInfo(tz))
            except ValueError:
                pass
    if m := re.search(rf"\b({_MONTHS})[a-z]*\.?[\s\-_]+(\d{{1,2}}),?[\s\-_]+(20\d\d)", t, re.I):
        try:
            return dt.datetime.strptime(f"{m.group(1)[:3].title()} {m.group(2)} {m.group(3)}", "%b %d %Y") \
                .replace(tzinfo=ZoneInfo(tz))
        except ValueError:
            pass
    return None


def document_items(page_html: str, page_url: str, src: Source, tz: str, cap: int = 10) -> list[Item]:
    """Agenda, minutes and report PDFs linked from a government page, with the date in their name."""
    out, seen = [], set()
    for href, text in _DOC_LINK.findall(page_html):
        url = urllib.parse.urljoin(page_url, html.unescape(href))
        label = clean(text, 160) or urllib.parse.unquote(urllib.parse.urlsplit(url).path.rsplit("/", 1)[-1])
        if url in seen or not _DOC_HREF.search(url) or not (_DOC_WORDS.search(label) or _DOC_WORDS.search(url)):
            continue
        when = date_in(f"{label} {url}", tz)
        if not when:                       # undated documents could be years old — leave them out
            continue
        seen.add(url)
        out.append(Item(source=src.name, section="civic", title=sentence(label, 120), url=url, published=when,
                        summary=f"Document posted by {src.name}", via=src.name, found_by="document",
                        attachments=[(sentence(label, 80), url)], use=PUBLIC_RECORD, jurisdiction=src.jurisdiction))
        if len(out) >= cap:
            break
    return out


@functools.lru_cache(maxsize=512)
def pdf_text(url: str, contact: str) -> str:
    """Text of a public PDF (robots.txt and opt-outs respected; size and page caps)."""
    if pypdf is None:
        return ""
    try:
        r = web_get(url, contact)
    except httpx.HTTPError:
        return ""
    data = r.content
    if r.status_code != 200 or len(data) > PDF_MAX_BYTES or not data.lstrip()[:5] == b"%PDF-":
        return ""
    if rights_action(page_rights(r, "", contact)) != "ok":
        return ""
    try:
        reader = pypdf.PdfReader(io.BytesIO(data))
        text = "\n".join((pg.extract_text() or "") for pg in reader.pages[:PDF_MAX_PAGES])
    except Exception:
        return ""
    return re.sub(r"[ \t]+", " ", text)[:300_000]


def snippet_around(text: str, start: int, end: int, width: int = 200, drop: str = "") -> str:
    """The sentence around a match (or a window of text when sentences run long)."""
    a = text.rfind(".", max(0, start - width), start)
    b = text.find(".", end, end + width)
    if a != -1 and b != -1:
        s = re.sub(r"\s+", " ", text[a + 1: b + 1]).strip()
        if drop and s.lower().startswith(drop.lower()):
            s = s[len(drop):].strip(" :-")
        return s
    a, b = max(0, start - width), min(len(text), end + width)
    s = re.sub(r"\s+", " ", text[a:b]).strip()
    if drop and s.lower().startswith(drop.lower()):
        s, a = s[len(drop):].strip(" :-"), 0
    if a > 0:
        s = "…" + s.split(" ", 1)[-1]
    if b < len(text):
        s = s.rsplit(" ", 1)[0] + "…"
    return s


API_FETCHERS = {
    "nws": api_nws,
    "socrata_geo": api_socrata_geo,
    "socrata_search": api_socrata_search,
    "legistar": api_legistar,
    "civicclerk": api_civicclerk,
}


# --------------------------------------------------------------------------------------
# Step 4 — filter, sort into sections, optional AI ranking
# --------------------------------------------------------------------------------------
def in_window(item: Item, cutoff: dt.datetime, now: dt.datetime, days_ahead: int) -> bool:
    if item.starts:
        return now - dt.timedelta(days=1) <= item.starts <= now + dt.timedelta(days=days_ahead)
    if item.published:
        return item.published >= cutoff
    return True  # undated: kept and flagged


def fetch_source(src: Source, place: dict, contact: str, cutoff: dt.datetime, opts: dict) -> list[Item]:
    if is_blocked(src.url):
        src.status = "listed only — this platform's terms don't allow scraping"
        return []
    if src.method == "listed":
        src.status = "listed — open the link"
        return []
    try:
        if src.method == "api":
            items = API_FETCHERS[src.fetcher](src, place, contact, cutoff, opts)
        else:
            items = crawl_site(src, contact, cutoff, opts)
    except Disallowed as e:
        src.status = f"skipped — {e}"
        src.rules = rules_for(src)
        return []
    except httpx.HTTPStatusError as e:
        src.status = f"error — HTTP {e.response.status_code}"
        src.rules = rules_for(src)
        return []
    except Exception as e:
        src.status = f"error — {type(e).__name__}: {str(e)[:100]}"
        src.rules = rules_for(src)
        return []

    now = dt.datetime.now(dt.timezone.utc)
    seen, kept = set(), []
    for it in items:
        key = (it.url if it.found_by not in ("api", "agenda") else
               (it.url, it.title) if it.found_by == "agenda" else (it.title, it.published, it.starts, it.summary))
        if not it.title or key in seen or not in_window(it, cutoff, now, opts["days_ahead"]):
            continue
        seen.add(key)
        it.section = classify(it, src.category)
        it.jurisdiction = src.jurisdiction
        if not it.use:
            it.use = ("public record — facts free to report" if it.found_by == "api"
                      else "their writing — link, and rewrite facts in your own words")
        kept.append(it)
    kept = kept[: opts["limit"] * (8 if src.fetcher in ("legistar", "civicclerk") else 1)]  # agenda items
    src.n_items = len(kept)
    src.rules = rules_for(src)
    if kept:
        how = ", ".join(f"{n} {k}" for k, n in collections.Counter(i.found_by for i in kept).most_common())
        src.status = f"ok — {len(kept)} items ({how})"
    else:
        src.status = "reached, but no items in the date window" + ("" if src.feed_url or src.method == "api"
                                                                  else " (no feed, calendar or article links found)")
    return kept


def ai_rank(items: list[Item], place: dict, api_key: str, model: str) -> str:
    """Claude assigns a section, a 1–5 usefulness score and a blurb from the item's own text only."""
    client = anthropic.Anthropic(api_key=api_key)
    done = 0
    for start in range(0, len(items), 60):
        batch = items[start:start + 60]
        rows = [{"i": start + k, "title": it.title[:160], "summary": it.summary[:220],
                 "source": it.source, "section_guess": it.section} for k, it in enumerate(batch)]
        prompt = f"""You edit a free weekly newsletter for parents and homeowners in {place['label']} ({place['display']}).
For each item give:
- "section": one of {list(SECTIONS)}
- "score": 1–5 usefulness for readers in THIS neighbourhood (1 = not about this place or not useful, 5 = must run)
- "blurb": under 20 words, using ONLY facts in the item's title and summary. Never add facts.
Return ONLY a JSON array of {{"i": int, "section": str, "score": int, "blurb": str}}.

Items:
{json.dumps(rows, ensure_ascii=False)}"""
        resp = client.messages.create(model=model, max_tokens=8000, messages=[{"role": "user", "content": prompt}])
        text = "".join(getattr(b, "text", "") for b in resp.content if getattr(b, "type", "") == "text")
        for r in _json_array(text):
            try:
                it = items[int(r["i"])]
            except (KeyError, ValueError, TypeError, IndexError):
                continue
            if r.get("section") in SECTIONS:
                it.section = r["section"]
            try:
                it.score = max(1, min(5, int(r.get("score"))))
            except (TypeError, ValueError):
                pass
            it.blurb = clean(str(r.get("blurb", "")), 200)
            done += 1
    return f"Claude ranked {done} of {len(items)} items."


# --------------------------------------------------------------------------------------
# Step 5 — locality filter: keep only items provably tied to the place
# --------------------------------------------------------------------------------------
_ADDRESS = re.compile(
    r"\b\d{2,6}\s+(?:[NSEW]{1,2}\.?\s+)?(?:\d{1,3}(?:st|nd|rd|th)|[A-Za-z][A-Za-z'.]+)(?:\s+[A-Za-z][A-Za-z'.]+){0,3}?"
    r"\s+(?:Ave(?:nue)?|St(?:reet)?|Rd|Road|Blvd|Boulevard|Way|Pl(?:ace)?|Dr(?:ive)?|Ln|Lane|Ct|Court|Pkwy|Parkway|"
    r"Hwy|Highway|Ter(?:race)?|Cir(?:cle)?)\b\.?(?:\s+(?:NE|NW|SE|SW|N|S|E|W)\b)?", re.I)
_GENERIC_LANDMARKS = {"park", "playground", "library", "school", "community center", "fire station",
                      "police station", "garden", "museum", "marina", "elementary school", "high school"}


def _in_ring(x: float, y: float, ring: list) -> bool:
    inside = False
    for i in range(len(ring)):
        x1, y1 = ring[i][0], ring[i][1]
        x2, y2 = ring[(i + 1) % len(ring)][0], ring[(i + 1) % len(ring)][1]
        if (y1 > y) != (y2 > y) and x < (x2 - x1) * (y - y1) / ((y2 - y1) or 1e-12) + x1:
            inside = not inside
    return inside


def _in_shape(lon: float, lat: float, shape: dict) -> bool:
    polys = [shape["coordinates"]] if shape["type"] == "Polygon" else shape["coordinates"]
    return any(_in_ring(lon, lat, p[0]) and not any(_in_ring(lon, lat, h) for h in p[1:]) for p in polys)


def inside_locality(lat: float, lon: float, place: dict, radius_km: float) -> bool:
    """Inside the place's OpenStreetMap boundary, or within radius_km of its centre when there is none."""
    if place.get("boundary"):
        return _in_shape(lon, lat, place["boundary"])
    return km_between(place["lat"], place["lon"], lat, lon) <= radius_km


def _reach_m(place: dict, radius_km: float) -> int:
    b = place.get("boundary")
    if not b:
        return int(radius_km * 1000)
    polys = [b["coordinates"]] if b["type"] == "Polygon" else b["coordinates"]
    far = max(km_between(place["lat"], place["lon"], pt[1], pt[0]) for p in polys for pt in p[0])
    return int(min(far, 6.0) * 1000)


@st.cache_data(ttl=7 * 86400, show_spinner=False)
def _overpass_names(lat: float, lon: float, reach_m: int, contact: str) -> list[tuple[str, float, float]]:
    query = f"""[out:json][timeout:60];
(
  nwr(around:{reach_m},{lat},{lon})["name"]["amenity"~"^(school|college|library|community_centre|marketplace|theatre|arts_centre|townhall|cinema)$"];
  nwr(around:{reach_m},{lat},{lon})["name"]["leisure"~"^(park|playground|sports_centre|stadium|marina|nature_reserve|garden)$"];
  nwr(around:{reach_m},{lat},{lon})["name"]["tourism"~"^(attraction|museum|viewpoint)$"];
  nwr(around:{reach_m},{lat},{lon})["name"]["place"~"^(neighbourhood|quarter|suburb|locality)$"];
);
out tags center 600;"""
    out = []
    for el in overpass(query, contact).get("elements", []):
        pt = el.get("center") or el
        if "lat" in pt and "lon" in pt and el.get("tags", {}).get("name"):
            out.append((el["tags"]["name"], float(pt["lat"]), float(pt["lon"])))
    return out


def landmark_points(place: dict, contact: str, radius_km: float) -> list[tuple[str, float, float]]:
    """Named schools, parks, libraries, community centres etc. inside the place, with where they are."""
    city = (place.get("city") or "").lower()
    out = []
    for name, lat, lon in _overpass_names(place["lat"], place["lon"], _reach_m(place, radius_km), contact):
        n = name.strip()
        if n.lower() in _GENERIC_LANDMARKS or n.lower() == city or (len(n) < 8 and " " not in n):
            continue
        if inside_locality(lat, lon, place, radius_km):
            out.append((n, lat, lon))
    return out


def landmarks_for(place: dict, contact: str, radius_km: float) -> list[str]:
    return sorted({n for n, _, _ in landmark_points(place, contact, radius_km)})


def name_pattern(names: list[str]) -> re.Pattern | None:
    names = sorted({n.strip() for n in names if n and len(n.strip()) >= 3}, key=len, reverse=True)
    if not names:
        return None
    alts = "|".join(re.escape(n).replace(r"\ ", r"[\s\-_]+") for n in names)
    return re.compile(rf"(?<![A-Za-z])(?:{alts})(?![A-Za-z])", re.I)


@functools.lru_cache(maxsize=4096)
def geocode_address(address: str, city: str, state: str, lat: float, lon: float, contact: str):
    """Look up a street address near the place (bounded box), returns (lat, lon) or None."""
    box = f"{lon - 0.25},{lat + 0.25},{lon + 0.25},{lat - 0.25}"
    try:
        r = polite_get("https://nominatim.openstreetmap.org/search", contact,
                     params={"q": ", ".join(p for p in (address, city, state) if p), "format": "jsonv2",
                             "limit": 1, "countrycodes": "us", "viewbox": box, "bounded": 1})
        hits = r.json() if r.status_code == 200 else []
    except (httpx.HTTPError, ValueError):
        return None
    return (float(hits[0]["lat"]), float(hits[0]["lon"])) if hits else None


def item_text(it: Item) -> str:
    path = urllib.parse.urlsplit(it.url).path
    for ch in "-_/":
        path = path.replace(ch, " ")
    return " ".join([it.title, it.summary, it.where, it.blurb, it.text or it.body, path])


def check_local(it: Item, place: dict, ctx: dict) -> tuple[bool | None, str, str]:
    """(True, why, tier) if tied to the place; (False, why, '') if its location rules it out; (None, …) if undecided."""
    label = place["label"]
    if it.lat is not None and it.lon is not None:  # a location is decisive either way
        if inside_locality(it.lat, it.lon, place, ctx["radius_km"]):
            d = km_between(place["lat"], place["lon"], it.lat, it.lon)
            return True, f"happens inside {label} ({d:.1f} km from the centre)", "coordinates"
        return False, f"location is outside {label}", ""
    if it.via == "National Weather Service alerts":
        return True, f"weather alert covering {label}", "coordinates"
    if it.jurisdiction and it.jurisdiction.lower() == label.lower():
        return True, f"{it.jurisdiction}'s own government", "jurisdiction"
    text = item_text(it)
    if ctx["names"] is not None and (m := ctx["names"].search(text)):
        return True, f"names “{m.group(0)}”", "name"
    if ctx["marks"] is not None and (m := ctx["marks"].search(text)):
        return True, f"mentions {m.group(0)}, which is in {label}", "landmark"
    return None, "", ""


def localize(items: list[Item], place: dict, contact: str, opts: dict, landmarks: list[str]) -> dict:
    """Marks every item local or not, with the reason. Cheap checks first, then reads articles,
    then looks up street addresses on the map."""
    ctx = {"radius_km": opts["locality_km"],
           "names": name_pattern([place["label"], *place.get("aliases", []), *opts["extra_names"]]),
           "marks": name_pattern(landmarks)}
    stats = collections.Counter()

    def run(pending: list[Item]) -> list[Item]:
        rest = []
        for it in pending:
            ok, why, tier = check_local(it, place, ctx)
            if ok is None:
                rest.append(it)
                continue
            it.local, it.local_why, it.local_tier = ok, why, tier
            if ok:
                stats[tier] += 1
        return rest

    for it in items:
        it.local, it.local_why, it.local_tier = None, "", ""
    pending = run(items)

    # Read the article for items whose headline and summary don't settle it
    to_read = [it for it in pending if it.found_by not in ("api", "news search")
               and not (it.text or it.body)][: opts["body_checks"]]
    if to_read:
        with cf.ThreadPoolExecutor(max_workers=8) as pool:
            for it, body in zip(to_read, pool.map(lambda i: extract_full_text(i.url, contact), to_read)):
                it.body = body
        stats["articles read"] = len(to_read)
        pending = run(pending)

    # Read attached documents (agenda items' staff reports, agendas, minutes) for the place or its landmarks
    jobs = []
    civic_words = r"land use|zoning|rezone|park|street|transport|transit|school|library|housing|permit|development|" \
                  r"levy|budget|neighbo|bridge|sidewalk|bike|bus|traffic|community"
    with_docs = sorted((it for it in pending if it.attachments),
                       key=lambda it: (not re.search(civic_words, f"{it.title} {it.summary}", re.I),
                                       it.found_by != "agenda"))
    for it in with_docs:
        for name, url in it.attachments[:3]:
            jobs.append((it, name, url))
    jobs = jobs[: opts.get("pdf_checks", 0)]
    if jobs:
        with cf.ThreadPoolExecutor(max_workers=4) as pool:
            texts = list(pool.map(lambda j: pdf_text(j[2], contact), jobs))
        stats["documents read"] = sum(1 for t in texts if t)
        for (it, name, url), text in zip(jobs, texts):
            if not text or it.local:
                continue
            for pattern, tier in ((ctx["names"], "name"), (ctx["marks"], "landmark")):
                m = pattern.search(text) if pattern is not None else None
                if m:
                    it.local, it.local_tier = True, tier
                    it.local_why = (f"“{name}” names “{m.group(0)}”" if tier == "name"
                                    else f"“{name}” mentions {m.group(0)}, which is in {place['label']}")
                    quote = f"From “{name}”: “{snippet_around(text, m.start(), m.end(), drop=name)}”"
                    lead, _, rest = it.summary.partition(" · ")   # keep the vote / meeting date first
                    it.summary = " · ".join(x for x in (lead, quote, rest) if x)
                    stats[tier] += 1
                    stats["found in documents"] += 1
                    break
        pending = [it for it in pending if not it.local]

    # Look up street addresses and keep the item if one falls inside the boundary
    looked = 0
    city, state = place.get("city") or place.get("county") or "", place.get("state") or ""
    for it in pending:
        if looked >= opts["address_checks"]:
            break
        for addr in dict.fromkeys(m.group(0).strip() for m in _ADDRESS.finditer(item_text(it))):
            if looked >= opts["address_checks"]:
                break
            looked += 1
            pt = geocode_address(addr, city, state, round(place["lat"], 4), round(place["lon"], 4), contact)
            if pt and inside_locality(pt[0], pt[1], place, opts["locality_km"]):
                it.local, it.local_why, it.local_tier = True, f"address {addr} is inside {place['label']}", "address"
                stats["address"] += 1
                break
    stats["addresses looked up"] = looked

    for it in items:
        if it.local is None and opts["trust_search"] and it.found_by == "news search":
            it.local, it.local_tier = True, "search match"
            it.local_why = f"news search for “{place['label']}” (not checked in the article)"
            stats["search match"] += 1
        if it.local is None:
            it.local = False
            it.local_why = "doesn't name the place, a landmark in it, or an address or location inside it"
    stats["kept"] = sum(1 for i in items if i.local)
    stats["checked"] = len(items)
    return dict(stats)


# --------------------------------------------------------------------------------------
# Step 6 — the newsletter view
# --------------------------------------------------------------------------------------
NEWSLETTER_CSS = """
<style>
.nb{max-width:760px;margin:0 auto;background:#fffdf8;color:#1f2328;border:1px solid #e7e2d6;border-radius:14px;
    padding:32px 36px;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;
    line-height:1.5}
.nb a{color:#1f2328;text-decoration:none;border-bottom:1px solid #d9c9a3}
.nb a:hover{color:#b45309;border-color:#b45309}
.nb-kicker{font-size:12px;letter-spacing:.12em;text-transform:uppercase;color:#b45309;font-weight:600}
.nb h1{font-family:Georgia,"Times New Roman",serif;font-size:34px;line-height:1.15;margin:6px 0 4px;color:#1f2328}
.nb-date{color:#6b7280;font-size:14px}
.nb-intro{font-size:16px;margin:18px 0 8px;padding-bottom:18px;border-bottom:2px solid #1f2328}
.nb h2{font-family:Georgia,"Times New Roman",serif;font-size:22px;margin:28px 0 10px;padding-bottom:6px;
       border-bottom:1px solid #e7e2d6;color:#1f2328}
.nb-alert{background:#fef3c7;border:1px solid #f59e0b;border-radius:10px;padding:10px 14px;margin:14px 0;font-size:14px}
.nb-day{font-weight:700;font-size:13px;text-transform:uppercase;letter-spacing:.06em;color:#6b7280;margin:14px 0 4px}
.nb-ev{display:flex;gap:14px;padding:8px 0;border-bottom:1px dashed #ece6d8}
.nb-time{min-width:64px;font-variant-numeric:tabular-nums;color:#b45309;font-weight:600;font-size:14px}
.nb-story{padding:10px 0 12px;border-bottom:1px dashed #ece6d8}
.nb-head{font-family:Georgia,"Times New Roman",serif;font-size:18px;font-weight:600}
.nb-story p{margin:4px 0 6px;font-size:15px}
.nb-meta{font-size:12.5px;color:#6b7280}
.nb-why{display:inline-block;font-size:11.5px;background:#f1ece0;color:#5b4a26;border-radius:999px;padding:1px 8px;margin-left:4px}
.nb-blotter{list-style:none;padding:0;margin:0}
.nb-blotter li{padding:8px 0;border-bottom:1px dashed #ece6d8;font-size:14px}
.nb-call{display:flex;gap:10px;padding:2px 0 2px 2px;font-size:13.5px}
.nb-when{min-width:118px;color:#b45309;font-variant-numeric:tabular-nums}
.nb-note{font-size:12.5px;color:#6b7280;margin:-4px 0 6px}
.nb-more{font-size:13px;color:#6b7280;margin-top:6px}
.nb-foot{margin-top:28px;padding-top:14px;border-top:2px solid #1f2328;font-size:12.5px;color:#6b7280}
.nb-empty{color:#6b7280;font-style:italic}
</style>"""

NEWSLETTER_ORDER = ["civic", "schools", "community", "business", "real_estate", "public_safety", "obituaries", "news"]


@dataclass
class Entry:
    """One line in the newsletter: the best copy of a headline, plus what was merged into it."""
    item: Item
    count: int = 1
    also_sources: list = field(default_factory=list)
    also_starts: list = field(default_factory=list)
    title: str = ""   # best-formatted wording of the headline across the merged copies
    members: list = field(default_factory=list)   # police & fire: every call of this kind, newest first

    def __post_init__(self):
        self.title = self.title or self.item.title


_TIER_RANK = {"coordinates": 6, "address": 5, "name": 4, "landmark": 3, "jurisdiction": 2, "search match": 1}
_PUNCT = str.maketrans({"‘": "'", "’": "'", "“": '"', "”": '"',
                        "–": "-", "—": "-", " ": " "})


def headline_key(it: Item) -> str:
    """The headline as text, ignoring case, spacing, quote/dash styles and a trailing ' - Publisher'."""
    t = it.title or ""
    src = (it.source or "").strip()
    if src and t.lower().endswith(" - " + src.lower()):
        t = t[: -(len(src) + 3)]
    t = re.sub(r"\s+", " ", t.translate(_PUNCT).lower())
    return t.strip(" .!?:;-'\"")


def dedupe_for_newsletter(items: list[Item], tz: str) -> tuple[list[Entry], int]:
    """Collapse items whose headlines are exactly the same. Returns the entries and how many were merged."""
    zone = ZoneInfo(tz)
    epoch = dt.datetime.min.replace(tzinfo=dt.timezone.utc)
    groups: dict[str, list[Item]] = {}
    for it in items:
        groups.setdefault(headline_key(it), []).append(it)

    def quality(i: Item):
        return (_TIER_RANK.get(i.local_tier, 0), i.found_by != "news search", bool(i.published or i.starts),
                len(i.blurb or i.summary), i.score or 0)

    entries, merged = [], 0
    for key, grp in groups.items():
        if not key or len(grp) == 1:
            entries.extend(Entry(i, members=[i]) for i in grp)
            continue
        dated = [i for i in grp if i.starts]
        if dated:  # an event: show it once, at its next date
            best = min(dated, key=lambda i: (i.starts, -_TIER_RANK.get(i.local_tier, 0)))
            first_day = best.starts.astimezone(zone).date()
            others = sorted({i.starts.astimezone(zone).date() for i in dated} - {first_day})
            also_starts = [dt.datetime(d.year, d.month, d.day, tzinfo=zone) for d in others]
        elif all(i.section == "public_safety" for i in grp):  # same kind of call: one line, every call listed
            best, also_starts = max(grp, key=lambda i: i.published or epoch), []
            grp = sorted(grp, key=lambda i: i.published or epoch, reverse=True)
        else:
            best, also_starts = max(grp, key=quality), []
        wordings = []
        for i in grp:
            t, src = i.title.strip(), (i.source or "").strip()
            if src and t.lower().endswith(" - " + src.lower()):
                t = t[: -(len(src) + 3)].strip()
            wordings.append(re.sub(r"\s+", " ", t))
        title = max(wordings, key=lambda t: (t[:1].isupper(), sum(c.isupper() for c in t), -len(t)))
        entries.append(Entry(best, count=len(grp), also_starts=also_starts, title=title, members=list(grp),
                             also_sources=sorted({i.source for i in grp if i.source and i.source != best.source})))
        merged += len(grp) - 1
    return entries, merged


def _href(url: str) -> str:
    return html.escape(url, quote=True) if url.startswith(("http://", "https://")) else "#"


def build_newsletter(place: dict, items: list[Item], tz: str, days: int, days_ahead: int, stats: dict) -> str:
    e = html.escape
    label = place["label"]
    zone = ZoneInfo(tz)
    today = dt.datetime.now(zone)
    entries, merged = dedupe_for_newsletter([i for i in items if i.local], tz)
    far = dt.datetime.max.replace(tzinfo=dt.timezone.utc)
    epoch = dt.datetime.min.replace(tzinfo=dt.timezone.utc)
    weather = [en for en in entries if en.item.section == "weather"]
    events = sorted((en for en in entries if en.item.section == "events"), key=lambda en: en.item.starts or far)
    stories = {s: sorted((en for en in entries if en.item.section == s),
                         key=lambda en: (en.item.score or 0, en.item.published or epoch), reverse=True)
               for s in NEWSLETTER_ORDER}
    n_stories = sum(len(v) for k, v in stories.items() if k != "public_safety")

    def why(it: Item) -> str:
        return f'<span class="nb-why">{e(it.local_why)}</span>' if it.local_why else ""

    def also(en: Entry) -> str:
        bits = []
        if en.also_starts:
            dates = ", ".join(f"{d:%a} {d.day} {d:%b}" for d in en.also_starts[:4])
            bits.append(f"also {dates}" + (" and more" if len(en.also_starts) > 4 else ""))
        if en.also_sources:
            bits.append("also from " + ", ".join(en.also_sources[:3]) +
                        (f" +{len(en.also_sources) - 3}" if len(en.also_sources) > 3 else ""))
        return f" · {e('; '.join(bits))}" if bits else ""

    out = [NEWSLETTER_CSS, '<div class="nb">',
           f'<div class="nb-kicker">Newsbee · {e(label)}</div>',
           f"<h1>This week in {e(label)}</h1>",
           f'<div class="nb-date">{today:%A %d %B %Y} · news from the last {days} days, '
           f"events for the next {days_ahead}</div>"]
    bits = [f"{len(events)} thing{'s' if len(events) != 1 else ''} to do", f"{n_stories} local stor{'ies' if n_stories != 1 else 'y'}"]
    if stories["public_safety"]:
        n_calls = sum(len(en.members or [en.item]) for en in stories["public_safety"])
        bits.append(f"{n_calls} police & fire call{'s' if n_calls != 1 else ''} nearby")
    out.append(f'<p class="nb-intro">Here’s what’s happening in {e(label)}: {", ".join(bits)}. '
               f"Everything below is tied to {e(label)} by where it happens, an address inside it, or by naming it.</p>")

    for w in (en.item for en in weather[:3]):
        out.append(f'<div class="nb-alert"><b>⚠ {e(w.title)}</b> — {e(clean(w.summary, 200))}</div>')

    out.append("<h2>Coming up</h2>")
    if not events:
        out.append('<p class="nb-empty">No upcoming events found for this place yet.</p>')
    last_day = None
    for en in events[:25]:
        ev = en.item
        when = ev.starts.astimezone(zone) if ev.starts else None
        day = when.strftime("%A %d %B") if when else "Date not listed — check the link"
        if day != last_day:
            out.append(f'<div class="nb-day">{e(day)}</div>')
            last_day = day
        if not when:
            t = "—"
        elif when.hour or when.minute:
            t = when.strftime("%I:%M %p").lstrip("0").lower()
        else:
            t = "All day"
        meta = " · ".join(x for x in (ev.where, ev.source) if x)
        out.append(f'<div class="nb-ev"><div class="nb-time">{e(t)}</div><div>'
                   f'<a href="{_href(ev.url)}" target="_blank">{e(en.title)}</a>'
                   f'<div class="nb-meta">{e(meta)}{also(en)} {why(ev)}</div></div></div>')
    if len(events) > 25:
        out.append(f'<div class="nb-more">…and {len(events) - 25} more events.</div>')

    for s in NEWSLETTER_ORDER:
        lst = stories[s]
        if not lst:
            continue
        out.append(f"<h2>{e(SECTIONS[s])}</h2>")
        if s == "public_safety":
            out.append('<p class="nb-note">What was reported, when and where. Calls for service are reports, '
                       'not confirmed crimes; locations are shown to the block. Fire &amp; medical data lists only the '
                       'type of response — patient details are private by law.</p><ul class="nb-blotter">')
            for en in lst[:12]:
                calls = en.members or [en.item]
                count = f" · {len(calls)} calls" if len(calls) > 1 else ""
                rows = []
                for c in calls[:5]:
                    if c.published:
                        lt = c.published.astimezone(zone)
                        when = f"{lt:%a} {lt.day} {lt:%b}, " + lt.strftime("%I:%M %p").lstrip("0").lower()
                    else:
                        when = "time not given"
                    pin = f' · <a href="{_href(c.map_url)}" target="_blank">map</a>' if c.map_url else ""
                    detail = f'<div class="nb-meta">{e(clean(c.summary, 160))}</div>' if c.summary else ""
                    rows.append(f'<div class="nb-call"><span class="nb-when">{e(when)}</span>'
                                f'<span>{e(c.where or "location not given")}{pin}{detail}</span></div>')
                more = f'<div class="nb-meta">+{len(calls) - 5} more</div>' if len(calls) > 5 else ""
                src_line = f'<div class="nb-meta">{e(en.item.source)}{also(en)} {why(en.item)}</div>'
                out.append(f"<li><b>{e(en.title)}</b>{e(count)}{''.join(rows)}{more}{src_line}</li>")
            out.append("</ul>")
            if len(lst) > 12:
                out.append(f'<div class="nb-more">…and {len(lst) - 12} more kinds of call.</div>')
            continue
        for en in lst[:8]:
            it = en.item
            when = it.published.astimezone(zone).strftime("%d %b") if it.published else ""
            text = it.blurb or clean(re.sub(r" · Full title: .*$", "", it.summary), 380 if s == "civic" else 240)
            meta = " · ".join(x for x in (it.source, when) if x)
            out.append(f'<div class="nb-story"><a class="nb-head" href="{_href(it.url)}" target="_blank">{e(en.title)}</a>'
                       + (f"<p>{e(text)}</p>" if text else "")
                       + f'<div class="nb-meta">{e(meta)}{also(en)} {why(it)}</div></div>')
        if len(lst) > 8:
            out.append(f'<div class="nb-more">…and {len(lst) - 8} more in {e(SECTIONS[s].lower())}.</div>')

    dup_note = (f" {merged} repeated headline{'s were' if merged != 1 else ' was'} merged so each appears once."
                if merged else "")
    out.append(f'<div class="nb-foot">Made by Newsbee from public sources. {stats.get("kept", 0)} of '
               f'{stats.get("checked", 0)} items found passed the {e(label)} check.{dup_note} Headlines link to the '
               f"original publishers; read the full stories there.</div></div>")
    return "\n".join(out)


def newsletter_document(place: dict, body: str) -> str:
    return (f'<!doctype html><html lang="en"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">'
            f"<title>This week in {html.escape(place['label'])}</title></head>"
            f'<body style="background:#f4f1ea;margin:0;padding:24px 12px">{body}</body></html>')


# --------------------------------------------------------------------------------------
# UI
# --------------------------------------------------------------------------------------
def fmt_date(d: dt.datetime | None, tz: str) -> str:
    if not d:
        return ""
    try:
        return d.astimezone(ZoneInfo(tz)).strftime("%a %d %b %Y, %H:%M").replace(", 00:00", "")
    except Exception:
        return d.strftime("%Y-%m-%d")


def md_text(s: str) -> str:
    return re.sub(r"([\[\]*_`#|<>])", r"\\\1", s)


def render_items(items: list[Item], tz: str, cap: int = 200) -> None:
    for it in items[:cap]:
        with st.container(border=True):
            stars = f"  ·  {'★' * it.score}{'☆' * (5 - it.score)}" if it.score else ""
            st.markdown(f"**[{md_text(it.title) or 'Untitled'}]({it.url})**{stars}")
            when = (f"Starts {fmt_date(it.starts, tz)}" if it.starts else fmt_date(it.published, tz)) or "no date"
            bits = [it.source, when, SECTIONS.get(it.section, it.section)]
            if it.where:
                bits.append(it.where)
            bits.append(f"found by {it.found_by}")
            st.caption(" · ".join(md_text(b) for b in bits) + (f" · [map]({it.map_url})" if it.map_url else ""))
            if it.blurb or it.summary:
                st.write(it.blurb or it.summary)
            if it.use:
                st.caption(f"Use: {it.use}")
            if it.text:
                with st.expander("Full text (internal review only — don't republish)"):
                    st.write(it.text)
    if len(items) > cap:
        st.caption(f"…and {len(items) - cap} more — narrow with the filters or download the CSV.")


def main() -> None:
    st.set_page_config(page_title="Newsbee Source Explorer", page_icon="🐝", layout="wide")
    st.title("Newsbee Source Explorer")
    st.caption("Enter a place. See every source of local information and everything publishable from them, "
               "sorted into newsletter sections.")

    key = os.getenv("ANTHROPIC_API_KEY", "")
    can_ai = bool(key) and anthropic is not None

    with st.sidebar:
        st.header("Place")
        query = st.text_input("Location", "Ballard, Seattle, WA",
                              help="Neighbourhood, town or county. Include the state.")
        contact = st.text_input("Your contact email", os.getenv("NEWSBEE_CONTACT", ""),
                                help="Sent in the User-Agent. Nominatim and weather.gov require one.")
        days = st.slider("News: look back (days)", 1, 30, 7)
        days_ahead = st.slider("Events: look ahead (days)", 7, 60, 30)
        radius_km = st.slider("Police / fire / permits radius (km)", 0.5, 5.0, 1.5, 0.5)
        tz = st.text_input("Time zone", "America/Los_Angeles")

        st.header("Sources")
        use_auto = st.checkbox("Find sources automatically (works for any US place)", True,
                               help="City & county websites, OpenStreetMap places inside the boundary, "
                                    "meeting-software accounts, open-data portals, and publishers the news "
                                    "searches surface. Nothing hand-entered.")
        osm_cap = st.slider("Max local websites from OpenStreetMap", 0, 50, 20, disabled=not use_auto)
        data_cap = st.slider("Max open-data datasets", 0, 20, 10, disabled=not use_auto)
        use_registry = st.checkbox("Also add curated sources (hand-picked: Seattle, Bainbridge, WA)", False)
        use_news = st.checkbox("News searches (6 topics)", True)
        use_ai_discover = st.checkbox("Discover more sources with Claude + web search", can_ai, disabled=not can_ai,
                                      help="Needs ANTHROPIC_API_KEY and the anthropic package.")
        max_searches = st.slider("Max web searches", 1, 10, 6, disabled=not use_ai_discover)
        extra = st.text_area("Add your own URLs (one per line)",
                             placeholder="https://www.example-funeral-home.com/obituaries\n"
                                         "https://www.example-school.org/events")

        st.header("Crawling")
        deep = st.checkbox("Deep crawl sites (calendars, structured data, sitemaps, article links)", True)
        pages_per_source = st.slider("Pages to open per site", 0, 40, 12, disabled=not deep,
                                     help="Each page is fetched politely, so more pages = slower.")
        limit = st.slider("Max items kept per source", 10, 100, 40)
        agenda_events = st.slider("Council meetings to open (agenda items, votes, attachments)", 0, 30, 10)
        pdf_checks = st.slider("Documents (PDFs) to read for the place", 0, 100, 30, disabled=pypdf is None,
                               help="Agendas, minutes and staff reports attached to meetings. Needs the pypdf package.")
        full_text = st.checkbox("Extract full text (slower)", False, disabled=trafilatura is None)
        full_text_n = st.slider("Full text: pages per site", 1, 10, 3, disabled=not full_text)

        st.header("Compliance")
        st.caption("Always on: robots.txt (incl. crawl-delay), site terms, login walls, page "
                   "noindex/nosnippet/paywall signals, back-off on 429/503, public APIs within their limits.")
        ai_optout = st.checkbox("Treat AI opt-outs as a no (robots.txt AI bots, noai, TDM reservation)", True)
        extra_blocked = st.text_area("Never fetch these sites (one domain per line)", "",
                                     placeholder="example-paper.com")

        st.header("Ranking")
        use_ai_rank = st.checkbox("Rank & blurb items with Claude", can_ai, disabled=not can_ai)
        rank_model = st.text_input("Ranking model", RANKING_MODEL, disabled=not use_ai_rank)

        st.header("Locality filter")
        extra_names = st.text_input("Other names for this place (comma-separated)", "",
                                    help="Spellings and nicknames people use, e.g. Wedgewood, Old Ballard.")
        use_landmarks = st.checkbox("Match landmarks inside the place (parks, schools, libraries)", True,
                                    help="Named places inside the boundary, from OpenStreetMap.")
        locality_km = st.slider("Radius if no boundary is found (km)", 0.3, 5.0, 1.2, 0.1,
                                help="Used only when OpenStreetMap has no boundary shape for the place.")
        body_checks = st.slider("Articles to open and check for the place name", 0, 80, 30,
                                help="For items whose headline and summary don't mention the place.")
        address_checks = st.slider("Street addresses to look up on the map", 0, 60, 20,
                                   help="OpenStreetMap allows about one lookup per second.")
        trust_search = st.checkbox("Also keep news-search hits not confirmed in the article", False)
        go = st.button("Find everything", type="primary", use_container_width=True)

    if go:
        if not contact:
            st.warning("Add a contact email in the sidebar first — public APIs require it.")
            st.stop()
        try:
            with st.spinner("Finding the place…"):
                place = geocode(query, contact)
        except httpx.HTTPError as e:
            st.error(f"Couldn't reach the geocoder: {e}")
            st.stop()
        if not place:
            st.error("Couldn't find that place. Try adding the city and state.")
            st.stop()

        reset_run_state()
        POLICY["ai_optout"] = ai_optout
        POLICY["extra_blocked"] = tuple(d.strip().lower().removeprefix("www.") for d in extra_blocked.split()
                                        if "." in d)
        cutoff = dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=days)
        sources: list[Source] = []
        notes = []
        if use_auto:
            with st.spinner(f"Finding sources for {place['label']} (websites, meeting software, open data)…"):
                found, dnotes = discover_sources(place, contact, {"locality_km": locality_km, "osm_cap": osm_cap,
                                                                  "data_cap": data_cap})
            sources += found
            notes += dnotes
        else:
            sources.append(nws_source())
        if use_registry:
            sources += registry_for(place)
        if use_news:
            sources += news_sources(place, days)
        if use_ai_discover:
            with st.spinner("Claude is searching the web for this place's sources…"):
                try:
                    found, note = discover_with_claude(place, key, DISCOVERY_MODEL, max_searches)
                    sources += found
                    notes.append(note)
                except Exception as e:
                    notes.append(f"Claude discovery failed: {type(e).__name__}: {str(e)[:150]}")
        for line in extra.splitlines():
            url = line.strip()
            if url.startswith("http"):
                sources.append(Source(name=urllib.parse.urlsplit(url).netloc.removeprefix("www."), url=url,
                                      category="community", method="web", origin="you"))
        sources = dedupe_sources(sources)

        opts = {"limit": limit, "radius_km": radius_km, "full_text": full_text, "full_text_n": full_text_n,
                "deep": deep, "pages_per_source": pages_per_source if deep else 0,
                "days_ahead": days_ahead, "tz": tz, "agenda_events": agenda_events}
        def crawl(batch: list[Source], label: str) -> list[Item]:
            got: list[Item] = []
            progress = st.progress(0.0, text=label)
            with cf.ThreadPoolExecutor(max_workers=8) as pool:
                futures = [pool.submit(fetch_source, s, place, contact, cutoff, opts) for s in batch]
                for i, fut in enumerate(cf.as_completed(futures), 1):
                    got += fut.result()
                    progress.progress(i / len(futures), text=f"{label} {i} of {len(futures)}")
            progress.empty()
            return got

        items: list[Item] = crawl(sources, "Crawling sources…")
        if use_auto and use_news:  # second pass: publishers the news searches show covering this place
            pubs = publisher_sources(items, sources)
            if pubs:
                sources += pubs
                items += crawl(pubs, "Crawling local publishers…")
            notes.append(f"News publishers: {len(pubs)} found"
                         + (f" ({', '.join(s.name for s in pubs[:4])}{'…' if len(pubs) > 4 else ''})" if pubs else ""))

        if use_ai_rank and items:
            with st.spinner("Claude is ranking items…"):
                try:
                    notes.append(ai_rank(items, place, key, rank_model))
                except Exception as e:
                    notes.append(f"Ranking failed: {type(e).__name__}: {str(e)[:150]}")

        marks: list[str] = []
        with st.spinner("Listing landmarks inside the place…"):
            try:
                points = landmark_points(place, contact, locality_km)
                describe_where(items, points)            # 'near Golden Gardens Park' for calls without an address
                if use_landmarks:
                    marks = sorted({n for n, _, _ in points})
            except Exception as e:
                notes.append(f"Landmark lookup skipped: {type(e).__name__}: {str(e)[:120]}")
        lopts = {"locality_km": locality_km, "body_checks": body_checks, "address_checks": address_checks,
                 "pdf_checks": pdf_checks,
                 "trust_search": trust_search,
                 "extra_names": [n.strip() for n in extra_names.split(",") if n.strip()]}
        with st.spinner(f"Checking which items are really about {place['label']}…"):
            lstats = localize(items, place, contact, lopts, marks)

        st.session_state["result"] = {"place": place, "sources": sources, "items": items, "notes": notes,
                                      "tz": tz, "lstats": lstats, "landmarks": marks,
                                      "days": days, "days_ahead": days_ahead}

    result = st.session_state.get("result")
    if not result:
        st.info("Enter a location in the sidebar and press **Find everything**.")
        return

    place, sources, items, tz = result["place"], result["sources"], result["items"], result["tz"]
    lstats = result.get("lstats", {})
    local_items = [i for i in items if i.local]
    left, right = st.columns([2, 1])
    with left:
        st.subheader(place["label"])
        st.caption(place["display"] + (" · boundary from OpenStreetMap" if place.get("boundary")
                                       else " · no boundary found, using the radius"))
        m1, m2, m3, m4 = st.columns(4)
        m1.metric("Sources", len(sources))
        m2.metric("Sources with items", sum(1 for s in sources if s.n_items))
        m3.metric("Items found", len(items))
        m4.metric(f"About {place['label']}", len(local_items))
        for n in result["notes"]:
            st.caption(n)
    with right:
        pts = [{"lat": place["lat"], "lon": place["lon"]}] + \
              [{"lat": i.lat, "lon": i.lon} for i in local_items if i.lat is not None and i.lon is not None]
        st.map(pd.DataFrame(pts), zoom=13)

    tab_local, tab_items, tab_sources, tab_export = st.tabs(
        [f"Local newsletter ({len(local_items)})", f"All items, first pass ({len(items)})", "Sources", "Export"])

    with tab_local:
        if lstats:
            tiers = [("coordinates", "location inside"), ("address", "address inside"), ("name", "names the place"),
                     ("landmark", "names a landmark"), ("jurisdiction", "own government"),
                     ("search match", "search match")]
            _, merged = dedupe_for_newsletter(local_items, tz)
            st.caption("Why items were kept: " + " · ".join(f"{label} {lstats[k]}" for k, label in tiers if lstats.get(k))
                       + f"  |  articles read: {lstats.get('articles read', 0)}"
                       + f" · addresses looked up: {lstats.get('addresses looked up', 0)}"
                       + f" · documents read: {lstats.get('documents read', 0)}"
                       + f" (place found in {lstats.get('found in documents', 0)})"
                       + f" · repeated headlines merged: {merged}")
        st.html(build_newsletter(place, items, tz, result.get("days", 7), result.get("days_ahead", 30), lstats))
        dropped = [i for i in items if i.local is False]
        with st.expander(f"Left out ({len(dropped)}) — and why"):
            st.dataframe(pd.DataFrame([{"Item": i.title, "Source": i.source, "Section": SECTIONS.get(i.section, i.section),
                                        "Reason": i.local_why, "Link": i.url} for i in dropped]),
                         hide_index=True, column_config={"Link": st.column_config.LinkColumn("Link")})
        if result.get("landmarks"):
            with st.expander(f"Landmarks used to recognise {place['label']} ({len(result['landmarks'])})"):
                st.write(", ".join(result["landmarks"]))

    with tab_items:
        if not items:
            st.info("Nothing found in this window. Widen the dates, raise pages per site, or add sources.")
        else:
            c1, c2, c3, c4 = st.columns([2, 2, 1, 1])
            srcs = c1.multiselect("Source", sorted({i.source for i in items}))
            needle = c2.text_input("Search")
            hide_undated = c3.checkbox("Hide undated", False)
            min_score = c4.slider("Min score", 1, 5, 1, disabled=not any(i.score for i in items))
            shown = [i for i in items
                     if (not srcs or i.source in srcs)
                     and (not needle or needle.lower() in f"{i.title} {i.summary} {i.blurb}".lower())
                     and not (hide_undated and not (i.published or i.starts))
                     and (i.score is None or i.score >= min_score)]
            far = dt.datetime.max.replace(tzinfo=dt.timezone.utc)
            epoch = dt.datetime.min.replace(tzinfo=dt.timezone.utc)
            by_section = {s: [] for s in SECTIONS}
            for it in shown:
                by_section.setdefault(it.section, []).append(it)
            for s, lst in by_section.items():
                if s == "events":
                    lst.sort(key=lambda i: i.starts or far)
                else:
                    lst.sort(key=lambda i: ((i.score or 0), i.published or epoch), reverse=True)
            present = [s for s, lst in by_section.items() if lst]
            tabs = st.tabs([f"All ({len(shown)})"] + [f"{SECTIONS[s]} ({len(by_section[s])})" for s in present])
            with tabs[0]:
                for s in present:
                    st.markdown(f"#### {SECTIONS[s]}")
                    render_items(by_section[s], tz, cap=15)
            for tab, s in zip(tabs[1:], present):
                with tab:
                    render_items(by_section[s], tz)

    with tab_sources:
        st.dataframe(pd.DataFrame([{
            "Source": s.name, "Section": SECTIONS.get(s.category, s.category), "Access": s.method,
            "Found by": s.origin, "Status": s.status, "Items": s.n_items, "Rules applied": s.rules,
            "Link": s.url, "Feed": s.feed_url or "", "Notes": s.notes,
        } for s in sources]), hide_index=True, column_config={
            "Link": st.column_config.LinkColumn("Link"), "Feed": st.column_config.LinkColumn("Feed")})

    with tab_export:
        def table(lst: list[Item]) -> str:
            rows = [{**{k: v for k, v in asdict(i).items() if k not in ("body", "text")},  # no copied article text
                     "section": SECTIONS.get(i.section, i.section),
                     "published": i.published.isoformat() if i.published else "",
                     "starts": i.starts.isoformat() if i.starts else ""} for i in lst]
            return pd.DataFrame(rows).to_csv(index=False)

        label = place["label"].replace(" ", "_")
        page = newsletter_document(place, build_newsletter(place, items, tz, result.get("days", 7),
                                                           result.get("days_ahead", 30), lstats))
        st.download_button(f"Download the {place['label']} newsletter (HTML)", page,
                           file_name=f"newsbee_{label}.html", mime="text/html")
        st.download_button(f"Download items about {place['label']} (CSV)", table(local_items),
                           file_name=f"newsbee_local_items_{label}.csv", mime="text/csv")
        st.download_button("Download all items, first pass (CSV)", table(items),
                           file_name=f"newsbee_items_{label}.csv", mime="text/csv")
        st.download_button("Download source map (JSON)", json.dumps([asdict(s) for s in sources], indent=2),
                           file_name=f"newsbee_sources_{label}.json", mime="application/json")


if __name__ == "__main__":
    main()