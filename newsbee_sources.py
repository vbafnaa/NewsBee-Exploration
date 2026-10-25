"""
Newsbee Source Explorer
=======================

Type a place ("Ballard, Seattle, WA") and the app:
  1. finds the place (OpenStreetMap / Nominatim),
  2. builds its source map:
       - civic & open-data connectors (weather alerts, 911 fire and police calls, building
         permits, restaurant inspections, council meetings, liquor-licence applications),
       - news searches for the place (local news, events, schools & council, real estate,
         business openings, obituaries),
       - local websites we know about, Claude-discovered sources (optional), and your own URLs,
  3. crawls every source for publishable items, using every method a site offers:
       RSS/Atom feeds · iCal event calendars · schema.org structured data (events, articles)
       · sitemaps · article links on the page,
  4. sorts everything into newsletter sections (events, council, schools, police & fire,
     real estate, business, obituaries, community, weather, other news),
  5. optional: Claude ranks every item for this neighbourhood and writes a one-line blurb
     using only the item's own title and summary.

Run
---
    pip install -r requirements.txt
    streamlit run newsbee_sources.py

Optional AI features:  export ANTHROPIC_API_KEY=sk-ant-...

Ground rules built in
---------------------
* Identifies itself with a User-Agent carrying your contact email.
* Checks robots.txt before fetching any web page, waits between requests to the same site,
  and caps pages per source. RSS feeds, calendars and documented APIs are read directly.
* Never scrapes Facebook, Nextdoor, Instagram, X/Twitter, Reddit, TikTok or Legacy.com.
* Headlines, short summaries and links only by default. Full text is for internal review;
  newspaper, blog and obituary text is copyrighted — summarise and link when publishing.
"""
from __future__ import annotations

import collections
import concurrent.futures as cf
import datetime as dt
import functools
import html
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


# --------------------------------------------------------------------------------------
# Settings
# --------------------------------------------------------------------------------------
AGENT_NAME = "NewsbeeSourceExplorer"
DISCOVERY_MODEL = "claude-sonnet-5-5"
RANKING_MODEL = "claude-haiku-5-5"
WEB_SEARCH_TOOL = "web_search_20250305"
TIMEOUT = httpx.Timeout(20.0, connect=10.0)
MIN_SECONDS_PER_HOST = 0.75
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
    method: str                 # "web" (crawl), "api", or "listed"
    origin: str = "built-in"    # built-in | news search | Claude + web search | you
    feed_url: str | None = None
    fetcher: str | None = None
    params: dict = field(default_factory=dict)
    notes: str = ""
    status: str = "not fetched"
    n_items: int = 0


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
    score: int | None = None
    blurb: str = ""


# --------------------------------------------------------------------------------------
# HTTP: identification, per-site pacing, robots.txt
# --------------------------------------------------------------------------------------
def user_agent(contact: str) -> str:
    return f"{AGENT_NAME}/0.3 (+{contact or 'no-contact-set'})"


_pace_lock = threading.Lock()
_next_slot: dict[str, float] = {}


def _pace(url: str) -> None:
    host = urllib.parse.urlsplit(url).netloc.lower()
    with _pace_lock:
        now = time.monotonic()
        slot = max(now, _next_slot.get(host, 0.0))
        _next_slot[host] = slot + MIN_SECONDS_PER_HOST
    if slot > now:
        time.sleep(slot - now)


def http_get(url: str, contact: str, params: dict | None = None, accept: str | None = None) -> httpx.Response:
    _pace(url)
    headers = {"User-Agent": user_agent(contact)}
    if accept:
        headers["Accept"] = accept
    return httpx.get(url, params=params, headers=headers, timeout=TIMEOUT, follow_redirects=True)


_robots_cache: dict[str, urllib.robotparser.RobotFileParser | None] = {}
_robots_lock = threading.Lock()


def _robots_for(url: str, contact: str) -> urllib.robotparser.RobotFileParser | None:
    parts = urllib.parse.urlsplit(url)
    root = f"{parts.scheme}://{parts.netloc}"
    with _robots_lock:
        if root in _robots_cache:
            return _robots_cache[root]
    parser = None
    try:
        r = http_get(root + "/robots.txt", contact)
        if r.status_code == 200:
            parser = urllib.robotparser.RobotFileParser()
            parser.parse(r.text.splitlines())
    except httpx.HTTPError:
        parser = None
    with _robots_lock:
        _robots_cache[root] = parser
    return parser


def robots_allows(url: str, contact: str) -> bool:
    parser = _robots_for(url, contact)
    return True if parser is None else parser.can_fetch(AGENT_NAME, url)


def robots_sitemaps(url: str, contact: str) -> list[str]:
    parser = _robots_for(url, contact)
    return list(parser.site_maps() or []) if parser else []


def is_blocked(url: str) -> bool:
    host = urllib.parse.urlsplit(url).netloc.lower()
    return any(host == d or host.endswith("." + d) for d in DO_NOT_SCRAPE)


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
    r = http_get("https://nominatim.openstreetmap.org/search", contact,
                 params={"q": query, "format": "jsonv2", "addressdetails": 1, "limit": 1, "countrycodes": "us"})
    r.raise_for_status()
    hits = r.json()
    if not hits:
        return None
    hit, a = hits[0], hits[0].get("address", {})
    place = {
        "query": query, "display": hit.get("display_name", query),
        "lat": float(hit["lat"]), "lon": float(hit["lon"]),
        "neighbourhood": a.get("neighbourhood") or a.get("suburb") or a.get("quarter"),
        "city": a.get("city") or a.get("town") or a.get("village") or a.get("hamlet"),
        "county": a.get("county"), "state": a.get("state"),
        "state_code": (a.get("ISO3166-2-lvl4") or "").replace("US-", ""), "postcode": a.get("postcode"),
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
                   notes="Some Legistar clients need an API token; an error here means ask the clerk."),
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
                   notes="Public CivicClerk API (undocumented by the vendor; keep volume low)."),
            Source(name="Bainbridge Island School District board (BoardDocs)",
                   url="https://go.boarddocs.com/wa/bisd/Board.nsf", category="schools", method="listed",
                   notes="No public API — agendas are HTML/PDF."),
        ]
    if county == "king county":
        out.append(Source(name="King County Council meetings (Legistar)", url="https://mkcclegisearch.kingcounty.gov/",
                          category="civic", method="api", fetcher="legistar", params={"client": "kingcounty"}))
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
            g = http_get(url, contact)
        except httpx.HTTPError:
            continue
        if g.status_code == 200 and re.search(r"<(rss|feed)\b", g.text[:3000], re.I):
            return url
    return None


def items_from_feed(src: Source, feed_url: str, contact: str, tz: str) -> list[Item]:
    r = http_get(feed_url, contact)
    r.raise_for_status()
    feed = feedparser.parse(r.content)
    news = src.origin == "news search"
    out = []
    for e in feed.entries:
        publisher = (e.get("source") or {}).get("title") if news else None
        out.append(Item(
            source=publisher or src.name, section=src.category, title=clean(e.get("title", ""), 220),
            url=e.get("link", src.url),
            published=parse_date(e.get("published_parsed") or e.get("updated_parsed"), tz),
            summary="" if news else clean(e.get("summary", ""), 400), via=src.name,
            found_by="news search" if news else "feed",
        ))
    return out


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
            out.append(Item(source=src.name, section="events", title=name, url=url,
                            starts=parse_date(obj.get("startDate"), tz), where=clean(_place_text(obj.get("location")), 160),
                            summary=clean(str(obj.get("description", "")), 400), via=src.name, found_by=found_by))
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
    r = http_get(ics_url.replace("webcal://", "https://"), contact)
    r.raise_for_status()
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
    return out


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
            r = http_get(sm, contact)
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
    if is_blocked(url) or not robots_allows(url, contact):
        return []
    try:
        r = http_get(url, contact)
    except httpx.HTTPError:
        return []
    if r.status_code >= 400 or "html" not in r.headers.get("content-type", "html"):
        return []
    page = r.text
    structured = items_from_structured_data(page, src, str(r.url), tz, found_by)
    text = ""
    if want_text and trafilatura is not None:
        text = (trafilatura.extract(page, url=str(r.url), include_comments=False) or "")[:8000]
    if structured:
        for it in structured:
            it.text = it.text or text
        return structured[:5]
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
    return [Item(source=src.name, section=src.category, title=clean(title, 220), url=str(r.url), published=date,
                 summary=clean(desc, 400), text=text, via=src.name, found_by=found_by)]


def crawl_site(src: Source, contact: str, cutoff: dt.datetime, opts: dict) -> list[Item]:
    tz = opts["tz"]
    items: list[Item] = []
    if src.feed_url:  # given feed (news searches, Claude-supplied feeds)
        items += items_from_feed(src, src.feed_url, contact, tz)
    if src.origin == "news search":
        return items
    if not robots_allows(src.url, contact):
        src.notes = (src.notes + " · robots.txt disallows the page").strip(" ·")
        return items
    r = http_get(src.url, contact)
    r.raise_for_status()
    page, page_url = r.text, str(r.url)

    feed = find_feed_in_html(page, page_url) or (None if src.feed_url else guess_feed(page_url, contact))
    if feed and feed != src.feed_url:
        src.feed_url = feed
        try:
            items += items_from_feed(src, feed, contact, tz)
        except httpx.HTTPError:
            pass
    if not opts["deep"]:
        return items

    items += items_from_structured_data(page, src, page_url, tz, "structured data")
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
    r = http_get("https://api.weather.gov/alerts/active", contact,
                 params={"point": f"{place['lat']:.4f},{place['lon']:.4f}"}, accept="application/geo+json")
    r.raise_for_status()
    return [Item(source=src.name, section="weather", title=p.get("headline") or p.get("event", "Weather alert"),
                 url=p.get("@id") or src.url, published=parse_date(p.get("sent")),
                 summary=clean(p.get("description", ""), 400), via=src.name, found_by="api")
            for p in (f.get("properties", {}) for f in r.json().get("features", []))]


@functools.lru_cache(maxsize=64)
def socrata_columns(domain: str, dataset: str, contact: str) -> tuple:
    r = http_get(f"https://{domain}/api/views/{dataset}.json", contact)
    r.raise_for_status()
    return tuple((c.get("fieldName", ""), c.get("dataTypeName", "")) for c in r.json().get("columns", []))


def api_socrata_geo(src, place, contact, cutoff, opts):
    """Any Socrata dataset: finds its date and location columns, filters to the radius and window."""
    p = src.params
    cols = dict(socrata_columns(p["domain"], p["dataset"], contact))
    date_col = next((c for c in p.get("date_fields", []) if c in cols), None) or \
        next((c for c, t in cols.items() if t in ("calendar_date", "floating_timestamp")), None)
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
    r = http_get(url, contact, params=query(where + ([geo] if geo else [])))
    server_geo = bool(geo)
    if r.status_code == 400 and geo:  # geo filter not supported on this column: filter locally
        r = http_get(url, contact, params=query(where))
        server_geo = False
    r.raise_for_status()

    titles = p.get("title_fields") or [c for c in cols if re.search(r"type|description|name", c)]
    out = []
    for row in r.json():
        dist = None
        if lat_col and lon_col:
            try:
                dist = km_between(place["lat"], place["lon"], float(row[lat_col]), float(row[lon_col]))
            except (KeyError, TypeError, ValueError):
                dist = None
        if not server_geo and (dist is None or dist > opts["radius_km"]):
            continue
        address = pick(row, p.get("address_fields", []))
        extra = " · ".join(f"{k.replace('_', ' ')}: {row[k]}" for k in p.get("extra_fields", []) if row.get(k))
        bits = [b for b in (f"{dist:.1f} km from the centre" if dist is not None else "", extra) if b]
        out.append(Item(source=src.name, section=src.category,
                        title=" — ".join(b for b in (pick(row, titles, "Record"), address) if b),
                        url=src.url, published=parse_date(row.get(date_col), opts["tz"]) if date_col else None,
                        summary=" · ".join(bits), via=src.name, found_by="api"))
        if len(out) >= opts["limit"]:
            break
    return out


def api_socrata_search(src, place, contact, cutoff, opts):
    term = place.get("postcode") or place.get("city") or place["label"]
    url = f"https://{src.params['domain']}/resource/{src.params['dataset']}.json"
    r = http_get(url, contact, params={"$q": term, "$limit": opts["limit"]})
    r.raise_for_status()
    out = []
    for row in r.json():
        title = pick(row, ["tradename", "trade_name", "business_name", "dba", "licensee", "name"], "Record")
        detail = ", ".join(f"{k}: {v}" for k, v in row.items()
                           if isinstance(v, str) and len(v) < 80 and not k.startswith(":"))
        out.append(Item(source=src.name, section=src.category, title=title, url=src.url,
                        summary=clean(detail, 400), via=src.name, found_by="api"))
    return out


def api_legistar(src, place, contact, cutoff, opts):
    params = {"$filter": f"EventDate ge datetime'{cutoff.date().isoformat()}'",
              "$orderby": "EventDate desc", "$top": opts["limit"]}
    r = http_get(f"https://webapi.legistar.com/v1/{src.params['client']}/events", contact, params=params)
    r.raise_for_status()
    out = []
    for ev in r.json():
        agenda = "agenda posted" if ev.get("EventAgendaFile") else "agenda not posted yet"
        out.append(Item(source=src.name, section="civic", title=f"{ev.get('EventBodyName', 'Meeting')} meeting",
                        url=ev.get("EventInSiteURL") or ev.get("EventAgendaFile") or src.url,
                        starts=parse_date(ev.get("EventDate"), opts["tz"]), where=clean(ev.get("EventLocation") or "", 160),
                        summary=clean(f"{ev.get('EventTime') or ''} · {agenda}", 300), via=src.name, found_by="api"))
    return out


def api_civicclerk(src, place, contact, cutoff, opts):
    url = f"https://{src.params['tenant']}.api.civicclerk.com/v1/Events"
    r = http_get(url, contact, params={"$orderby": "startDateTime desc", "$top": opts["limit"]})
    if r.status_code == 400:
        r = http_get(url, contact)
    r.raise_for_status()
    data = r.json()
    rows = data.get("value", []) if isinstance(data, dict) else data
    return [Item(source=src.name, section="civic", title=pick(ev, ["eventName", "name", "title", "categoryName"], "Meeting"),
                 url=src.url, starts=parse_date(pick(ev, ["startDateTime", "eventDate", "date"]), opts["tz"]),
                 summary=clean(pick(ev, ["eventDescription", "description", "location"]), 300),
                 via=src.name, found_by="api") for ev in rows]


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
    except httpx.HTTPStatusError as e:
        src.status = f"error — HTTP {e.response.status_code}"
        return []
    except Exception as e:
        src.status = f"error — {type(e).__name__}: {str(e)[:100]}"
        return []

    now = dt.datetime.now(dt.timezone.utc)
    seen, kept = set(), []
    for it in items:
        key = it.url if it.found_by != "api" else (it.title, it.published, it.starts, it.summary)
        if not it.title or key in seen or not in_window(it, cutoff, now, opts["days_ahead"]):
            continue
        seen.add(key)
        it.section = classify(it, src.category)
        kept.append(it)
    kept = kept[: opts["limit"]]
    src.n_items = len(kept)
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
            st.caption(" · ".join(bits))
            if it.blurb or it.summary:
                st.write(it.blurb or it.summary)
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
        use_registry = st.checkbox("Built-in civic, open-data & local sites", True)
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
        full_text = st.checkbox("Extract full text (slower)", False, disabled=trafilatura is None)
        full_text_n = st.slider("Full text: pages per site", 1, 10, 3, disabled=not full_text)

        st.header("Ranking")
        use_ai_rank = st.checkbox("Rank & blurb items with Claude", can_ai, disabled=not can_ai)
        rank_model = st.text_input("Ranking model", RANKING_MODEL, disabled=not use_ai_rank)
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

        cutoff = dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=days)
        sources: list[Source] = []
        if use_registry:
            sources += registry_for(place)
        if use_news:
            sources += news_sources(place, days)
        notes = []
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
                "days_ahead": days_ahead, "tz": tz}
        items: list[Item] = []
        progress = st.progress(0.0, text="Crawling sources…")
        with cf.ThreadPoolExecutor(max_workers=8) as pool:
            futures = [pool.submit(fetch_source, s, place, contact, cutoff, opts) for s in sources]
            for i, fut in enumerate(cf.as_completed(futures), 1):
                items += fut.result()
                progress.progress(i / len(futures), text=f"Crawled {i} of {len(futures)} sources")
        progress.empty()

        if use_ai_rank and items:
            with st.spinner("Claude is ranking items…"):
                try:
                    notes.append(ai_rank(items, place, key, rank_model))
                except Exception as e:
                    notes.append(f"Ranking failed: {type(e).__name__}: {str(e)[:150]}")

        st.session_state["result"] = {"place": place, "sources": sources, "items": items,
                                      "notes": notes, "tz": tz}

    result = st.session_state.get("result")
    if not result:
        st.info("Enter a location in the sidebar and press **Find everything**.")
        return

    place, sources, items, tz = result["place"], result["sources"], result["items"], result["tz"]
    left, right = st.columns([2, 1])
    with left:
        st.subheader(place["label"])
        st.caption(place["display"])
        m1, m2, m3, m4 = st.columns(4)
        m1.metric("Sources", len(sources))
        m2.metric("Sources with items", sum(1 for s in sources if s.n_items))
        m3.metric("Items", len(items))
        m4.metric("Upcoming events", sum(1 for i in items if i.section == "events"))
        for n in result["notes"]:
            st.caption(n)
    with right:
        st.map(pd.DataFrame({"lat": [place["lat"]], "lon": [place["lon"]]}), zoom=12)

    tab_items, tab_sources, tab_export = st.tabs(["Newsletter items", "Sources", "Export"])

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
            "Found by": s.origin, "Status": s.status, "Items": s.n_items, "Link": s.url,
            "Feed": s.feed_url or "", "Notes": s.notes,
        } for s in sources]), hide_index=True, column_config={
            "Link": st.column_config.LinkColumn("Link"), "Feed": st.column_config.LinkColumn("Feed")})

    with tab_export:
        rows = [{**asdict(i), "section": SECTIONS.get(i.section, i.section),
                 "published": i.published.isoformat() if i.published else "",
                 "starts": i.starts.isoformat() if i.starts else ""} for i in items]
        label = place["label"].replace(" ", "_")
        st.download_button("Download all items (CSV)", pd.DataFrame(rows).to_csv(index=False),
                           file_name=f"newsbee_items_{label}.csv", mime="text/csv")
        st.download_button("Download source map (JSON)", json.dumps([asdict(s) for s in sources], indent=2),
                           file_name=f"newsbee_sources_{label}.json", mime="application/json")


if __name__ == "__main__":
    main()