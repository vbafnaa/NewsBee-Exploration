# Newsbee Source Explorer

**Live app:** [https://vbafnaa-newsbee-exploration-newsbee-sources-kht4re.streamlit.app/](https://vbafnaa-newsbee-exploration-newsbee-sources-kht4re.streamlit.app/)

Type a place — a neighbourhood, town or county — and the app finds where that place's local information lives, collects everything publishable from those sources, and builds a newsletter from only the items that are provably about that place.

It is the research tool behind Newsbee, an AI-assisted hyperlocal newsletter for communities that have lost their local paper. It answers two questions for any location: *what sources exist here?* and *what would this week's issue look like?*

---

## Using the app

1. **Enter a location** in the sidebar, e.g. `Ballard, Seattle, WA`. Include the state.
2. **Enter your contact email.** Public services (OpenStreetMap, the National Weather Service) require one in every request.
3. Adjust the options if you want (defaults work), then press **Find everything**.
4. Wait about a minute. The app paces its requests to each website, so a full run is not instant.
5. Read the results in the four tabs.

### The tabs

| Tab                       | What it shows                                                                                                                                                                                                                                                                                                                          |
| ------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Local newsletter**      | The finished product: only items tied to your place, laid out like a weekly newsletter — upcoming events by day, then council, schools, community, business, real estate, police & fire, and obituaries. Each item carries a tag saying *why* it was kept. Below it, **Left out — and why** lists every excluded item with its reason. |
| **All items, first pass** | Everything collected from every source before the locality check, sorted into section tabs, with filters for source, keyword, undated items and (if ranking is on) score.                                                                                                                                                              |
| **Sources**               | The source map: every source found, how it is accessed, whether it returned items, how many, and any problem (blocked, no feed, error).                                                                                                                                                                                                |
| **Export**                | Downloads: the newsletter as an HTML page, the local items as CSV, all first-pass items as CSV, and the source map as JSON.                                                                                                                                                                                                            |

### Sidebar settings

| Group               | Setting                                 | What it does                                                                                                                        |
| ------------------- | --------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| **Place**           | Look back / Look ahead                  | News from the last *N* days; events in the next *N* days.                                                                           |
|                     | Police / fire / permits radius          | How far around the centre to pull incident and permit records.                                                                      |
| **Sources**         | Built-in sources                        | Civic APIs, open data and known local sites for the place.                                                                          |
|                     | News searches                           | Six topic searches for the place (news, events, schools & council, real estate, business, obituaries).                              |
|                     | Discover with Claude                    | Claude searches the web for more sources specific to this place. Needs an API key.                                                  |
|                     | Add your own URLs                       | Any page to crawl — a funeral home's obituaries page, a school calendar, a community council site.                                  |
| **Crawling**        | Deep crawl / pages per site             | How hard to look inside each website. Fewer pages = faster.                                                                         |
|                     | Extract full text                       | Pulls article text for internal review (not for republishing).                                                                      |
| **Ranking**         | Rank & blurb with Claude                | Scores each item 1–5 for usefulness to local parents and writes a one-line summary from the item's own text only. Needs an API key. |
| **Locality filter** | Other names                             | Nicknames and spellings, e.g. `Wedgewood`.                                                                                          |
|                     | Match landmarks                         | Recognise named parks, schools, libraries etc. inside the place.                                                                    |
|                     | Radius if no boundary                   | Fallback area when OpenStreetMap has no outline for the place.                                                                      |
|                     | Articles to open / addresses to look up | How much extra checking to do for items whose headline doesn't settle it.                                                           |
|                     | Keep unconfirmed news-search hits       | Off by default; turns on a weaker match for search results.                                                                         |

---

## How it works

```
 Place ──▶ Source map ──▶ Crawl ──▶ Sort into sections ──▶ (Rank) ──▶ Locality filter ──▶ Merge repeats ──▶ Newsletter

```

**1. Find the place.** OpenStreetMap returns the place's centre, its boundary outline where one exists, its alternative names, city, county and ZIP.

**2. Build the source map.**

- *Civic & open data* where they apply: weather alerts, Seattle fire 911 and police calls, Seattle building permits, King County restaurant inspections, Seattle / King County / Bainbridge council meetings, Washington liquor-licence applications.
- *News searches* scoped to the place across six topics.
- *Known local sites* for the place (e.g. My Ballard, Wedgwood Community Council, Beacon Arts).
- *Claude-discovered sources* and *your own URLs*.
- Sources that can't be scraped (court portals, legal notices, [Legacy.com](http://Legacy.com), Nextdoor) are listed with a link instead.

**3. Crawl every source using every method it offers:** RSS/Atom feeds, iCal event calendars, [schema.org](http://schema.org) structured data embedded in pages (events with dates and venues, articles), sitemaps of recently updated pages, and links on the page that look like individual stories, events or obituaries. Open-data sources are queried through their APIs.

**4. Sort into newsletter sections** — events, council & government, schools & youth, police & fire, real estate & development, business openings & closings, obituaries & milestones, community, weather, other news — using the source type, event dates and keywords.

**5. Rank (optional).** Claude scores and summarises items using only facts in each item.

**6. Filter to the locality.** An item is kept only if one of these is true:

| Check                            | Example                                                                                                                                                  |
| -------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Location inside the boundary** | A 911 call or event whose coordinates fall inside Ballard's outline. A location *outside* is decisive: the item is dropped even if it mentions the name. |
| **Address inside the boundary**  | "Service at 2400 NW 85th St" — the address is looked up on the map and falls inside.                                                                     |
| **Names the place**              | Headline, summary, venue, URL or (if needed) the article text says "Ballard" or one of its aliases.                                                      |
| **Names a landmark inside it**   | "Cleanup at Golden Gardens Park" — a park inside Ballard's boundary, from OpenStreetMap.                                                                 |
| **The place's own government**   | For a city like Bainbridge Island, its own council meetings.                                                                                             |

**7. Merge repeated headlines.** In the newsletter only, items with exactly the same headline (ignoring capitals, spacing, quote styles and a trailing "- Publisher") appear once:

- **Stories:** the best copy is kept — most strongly tied to the place, a direct publisher link, dated, fullest summary — with "also from …" crediting the other sources.
- **Events:** a recurring event is shown once at its next date, with "also Wed 4 Nov, Wed 11 Nov".
- **Police & fire:** repeat calls with the same heading collapse to "3 calls, latest …".

The first-pass tab is not de-duplicated, so nothing is hidden there.

**8. Lay out the newsletter** from the kept items, newest and highest-ranked first, with events in date order.

---

## Ground rules built in

- Identifies itself in every request with your contact email.
- Checks each site's `robots.txt` before reading a page, waits between requests to the same site, and caps pages per site.
- Never scrapes Facebook, Nextdoor, Instagram, X/Twitter, Reddit, TikTok or [Legacy.com](http://Legacy.com).
- Court records and legal notices are linked, not scraped (court rule GR 31 and site terms).
- Shows headlines, short summaries and links. News, blog and obituary text is copyrighted — summarise and link when publishing.
- Arrests and police calls are not convictions or confirmed crimes; set an editorial policy before publishing names.

---

## Run it yourself

```bash
pip install -r requirements.txt
streamlit run newsbee_sources.py

```

Optional settings (environment variables, or **Settings → Secrets** on Streamlit Community Cloud):

```toml
ANTHROPIC_API_KEY = "sk-ant-..."     # turns on Claude source discovery and ranking
NEWSBEE_CONTACT   = "team@example.org"  # pre-fills the contact email

```

Python 3.10+. Dependencies: Streamlit, httpx, feedparser, pandas, trafilatura, icalendar, anthropic (optional).

---

## Known limitations

- **Coverage is strongest for Seattle, King County, Kitsap and Bainbridge**, where open-data connectors are built in. Elsewhere it relies on news searches, local sites, Claude discovery and URLs you add.
- **Some built-in endpoints are unverified** in production: the Seattle building-permits dataset ID, and Seattle's council-meeting API (which may need a token). Failures show in the Sources tab without stopping the run.
- **Neighbourhood boundaries depend on OpenStreetMap.** If a neighbourhood has no outline, the radius setting is used instead — tune it.
- **Landmark names can repeat elsewhere** (e.g. "Lincoln Park"). Sources are mostly local, so this is rare, but check the *why* tag.
- **Some sites block automated readers** or have no feed or sitemap; those show as "no items" with the reason.
- **Address lookups are rate-limited** to about one per second by OpenStreetMap.
