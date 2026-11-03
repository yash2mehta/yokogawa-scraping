#!/usr/bin/env python3
"""
yokogawa_kb_scraper.py - build a RAG-ready knowledge base from Yokogawa's
"Products & Services" section (default region: Singapore /sg/).

WHAT IT DOES
  1. Discovers every page under /<region>/solutions/products-and-services/
     (Information, Control, Measurement, Consulting, Project Execution,
     Lifecycle Services, Life Science, Announcements ...) using the regional
     sitemap + mega-menu / side-nav / card links (async BFS).
  2. On each page reads the white anchor ribbon (Overview, Details, Resources,
     Downloads, Videos, News, ...) and every tab inside each section
     (References, White Papers, Yokogawa Technical Reports, Media Publications,
     Application Notes, Brochures, Instruction Manuals, ...).
  3. Downloads direct files (PDF etc.), follows library / news detail pages,
     saves their text as Markdown (with YAML front-matter) and downloads their
     attachments ("Download" buttons).
  4. Sweep pass: every library item / news article in the regional sitemap that
     was NOT linked from a product tab (e.g. hidden behind "View more") is
     fetched and filed under its related product(s), else _library/ or _news/.

OUTPUT LAYOUT
  <out>/
    products-and-services/
      <family>/                         e.g. measurement
        _page.md  _meta.json
        <category>/.../<product>/       mirrors the site's URL hierarchy
          _page.md                      full page text by section/tab
          _meta.json                    title, url, breadcrumb, sections, children
          Resources/
            Application Notes/
              <title>.md                library page text + front-matter
              <title> [<doc-id>].pdf    attachment
          Downloads/
            Brochures/<title> [<doc-id>].pdf
            Instruction Manuals/...
          Videos/Product Overviews/<title>.md
          News/<date> - <title>.md
    _library/<Section>/<Type>/...       sweep items with no related product
    _news/<category>/<year>/...         sweep news not linked from any product
    _cache/                             de-duplicated downloads + gz HTML (resume)
    manifest.jsonl                      one row per saved item (RAG metadata)
    failures.jsonl                      gated / failed downloads
    crawl_report.json                   run statistics

  Each unique file is downloaded ONCE into _cache/files and hard-linked into
  every folder that references it (no duplicate disk usage). Re-running the
  script resumes: cached files/pages are not fetched again.

INSTALL
  pip install aiohttp beautifulsoup4 lxml markdownify

USAGE
  python yokogawa_kb_scraper.py                                # everything
  python yokogawa_kb_scraper.py --families measurement control # subset
  python yokogawa_kb_scraper.py --max-pages 15 --no-sweep      # quick test
  python yokogawa_kb_scraper.py --rate 0.7 --file-rate 0.7     # gentler, if you get blocked

NOTES
  * The site sits behind CloudFront/AWS WAF with a per-IP rate limit. Bursting
    gets your IP blocked (403 "Request blocked") for several minutes. The
    script therefore:
      - paces requests per host (--rate pages/s, --file-rate files/s),
      - detects a block, pauses everything (--cooldown s, doubling each time),
        slows itself down, then retries the SAME request (nothing is lost),
      - stops cleanly after --max-blocks consecutive blocks; just re-run the
        same command later and it resumes from cache.
  * robots.txt is always respected (e.g. /*/technical-library/, oprex pages).
  * Software packages (.zip/.exe DD/DTM files) sit behind an "Agree & Download"
    licence button and are useless for RAG, so they are skipped by default.
    Use --include-binaries only if you have accepted those licence terms.
  * Files that need a login return HTML instead of the file; they are logged as
    "gated" in failures.jsonl instead of being saved as broken PDFs.
"""
from __future__ import annotations

import argparse
import asyncio
import gzip
import hashlib
import html as htmllib
import json
import logging
import mimetypes
import os
import random
import re
import shutil
import sys
import time
from collections import Counter
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional
from urllib.parse import unquote, urljoin, urlsplit, urlunsplit

try:
    import aiohttp
    from bs4 import BeautifulSoup
except ImportError:  # pragma: no cover
    sys.exit("Missing dependencies. Run:  pip install aiohttp beautifulsoup4 lxml markdownify")

try:
    from markdownify import markdownify as _markdownify
except ImportError:  # falls back to plain text
    _markdownify = None

try:
    import lxml  # noqa: F401
    PARSER = "lxml"
except ImportError:
    PARSER = "html.parser"

log = logging.getLogger("ykb")

# --------------------------------------------------------------------------- #
# Constants
# --------------------------------------------------------------------------- #
SITE = "https://www.yokogawa.com"
SITE_HOST = "www.yokogawa.com"

DOC_EXTS = {".pdf", ".doc", ".docx", ".xls", ".xlsx", ".xlsm", ".ppt", ".pptx",
            ".pps", ".ppsx", ".txt", ".csv", ".rtf", ".odt", ".ods", ".odp", ".epub"}
BIN_EXTS = {".zip", ".exe", ".msi", ".7z", ".rar", ".gz", ".tgz", ".tar", ".cab",
            ".iso", ".dd", ".bin", ".dmg", ".jar", ".apk"}
MEDIA_EXTS = {".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".bmp", ".ico",
              ".mp4", ".mov", ".avi", ".wmv", ".webm", ".mp3", ".wav", ".m4a"}
SCRIPT_EXTS = {".aspx", ".php", ".ashx", ".jsp", ".cfm", ".html", ".htm"}
FILE_EXTS = DOC_EXTS | BIN_EXTS | MEDIA_EXTS

RETRY_STATUS = {408, 425, 429, 500, 502, 503, 504}
WIN_RESERVED = {"CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)),
                *(f"LPT{i}" for i in range(1, 10))}

# /library/<group>/<type>/<slug>/  ->  (Section folder, Tab folder)
LIB_SECTION = {"resources": "Resources", "documents-downloads": "Downloads", "videos": "Videos"}
LIB_TYPE = {
    "faqs": "FAQs", "msds-sds": "MSDS-SDS", "ebooks": "eBooks", "how-tos": "How-Tos",
    "yokogawa-technical-reports": "Yokogawa Technical Reports",
    "references-videos": "Reference Videos",
    "general-specifications": "General Specifications",
}

# Elements removed before converting a product section to Markdown
PAGE_JUNK = ["script", "style", "noscript", "svg", "template", "form", "button", "iframe",
             ".tooltip_templates", ".section__nav", ".tabs", ".anchor-nav", ".anchor-nav-links"]
# Extra elements removed from library / news pages
DOC_JUNK = PAGE_JUNK + ["nav", ".breadcrumbs", "[class*=breadcrumb]", "[class*=sidenav]",
                        ".card", "[class*=related]", "[class*=share]", "[class*=social]",
                        "#geoBanner"]


# --------------------------------------------------------------------------- #
# Small helpers
# --------------------------------------------------------------------------- #
_WS = re.compile(r"\s+")
_BAD_FS = re.compile(r'[<>:"/\\|?*\x00-\x1f]')


def txt(el) -> str:
    return _WS.sub(" ", el.get_text(" ", strip=True)).strip() if el is not None else ""


def safe_name(s: str, maxlen: int = 100, default: str = "untitled") -> str:
    s = _BAD_FS.sub(" ", unquote(s or ""))
    s = _WS.sub(" ", s).strip().strip(".")
    if len(s) > maxlen:
        s = s[:maxlen].rstrip(" .-_")
    if s.upper() in WIN_RESERVED:
        s = "_" + s
    return s or default


def sha1(s: str) -> str:
    return hashlib.sha1(s.encode("utf-8")).hexdigest()


def now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def norm_url(href: str, base: Optional[str] = None) -> Optional[str]:
    """Absolute https URL without fragment (query kept)."""
    if not href:
        return None
    href = href.strip()
    if href.startswith(("mailto:", "tel:", "javascript:", "#", "data:")):
        return None
    url = urljoin(base, href) if base else href
    u = urlsplit(url)
    if u.scheme not in ("http", "https") or not u.netloc:
        return None
    path = re.sub(r"/{2,}", "/", u.path or "/")
    return urlunsplit(("https", u.netloc.lower(), path, u.query, ""))


def page_key(url: str) -> str:
    """Canonical page URL: no query/fragment, trailing slash for directory-style paths."""
    u = urlsplit(url)
    path = u.path or "/"
    if not os.path.splitext(path)[1] and not path.endswith("/"):
        path += "/"
    return urlunsplit(("https", u.netloc.lower(), path, "", ""))


def file_key(url: str) -> str:
    u = urlsplit(url)
    return urlunsplit(("https", u.netloc.lower(), u.path, "", ""))


def url_ext(url: str) -> str:
    return os.path.splitext(unquote(urlsplit(url).path))[1].lower()


def is_yoko(host: str) -> bool:
    return host == "yokogawa.com" or host.endswith(".yokogawa.com")


def classify(url: str, product_prefix: str) -> str:
    u = urlsplit(url)
    host, path, ext = u.netloc, u.path, url_ext(url)
    if ext in FILE_EXTS:
        return "file"
    if is_yoko(host) and host.startswith("web-material"):
        return "file"
    if is_yoko(host):
        if path.startswith(product_prefix):
            return "product"
        if "/library/" in path:
            return "library"
        if "/news/" in path:
            return "news"
        return "internal"
    return "external"


def is_detail_page(url: str) -> bool:
    """True for a single library item / news article (not a listing page)."""
    p = urlsplit(url).path
    if "/library/" in p:
        rest = [s for s in p.split("/library/", 1)[1].split("/") if s]
        return len(rest) >= 3 and rest[0] != "search"
    if "/news/" in p:
        rest = [s for s in p.split("/news/", 1)[1].split("/") if s]
        if len(rest) >= 3:
            return True
        return len(rest) == 2 and not re.fullmatch(r"\d{4}", rest[-1])
    return False


def lib_section_tab(url: str) -> tuple[str, str]:
    m = re.search(r"/library/([^/]+)/([^/]+)/", urlsplit(url).path)
    if not m:
        return "Resources", "Other"
    grp, typ = m.groups()
    return (LIB_SECTION.get(grp, grp.replace("-", " ").title()),
            LIB_TYPE.get(typ, typ.replace("-", " ").title()))


def cd_filename(cd: Optional[str]) -> str:
    if not cd:
        return ""
    m = re.search(r"filename\*\s*=\s*[^']*'[^']*'([^;]+)", cd, re.I)
    if m:
        return unquote(m.group(1).strip().strip('"'))
    m = re.search(r'filename\s*=\s*"?([^";]+)"?', cd, re.I)
    return m.group(1).strip() if m else ""


def guess_ext(url: str, ctype: str, cd: Optional[str]) -> str:
    e = url_ext(url)
    if e and len(e) <= 6 and e not in SCRIPT_EXTS:
        return e
    e2 = os.path.splitext(cd_filename(cd))[1].lower()
    if e2:
        return e2
    return mimetypes.guess_extension(ctype or "") or ".bin"


def build_file_name(title: str, m: dict) -> str:
    ext = m.get("ext") or ".bin"
    remote = m.get("remote_name") or os.path.basename(unquote(urlsplit(m["url"]).path)) or "file"
    stem = os.path.splitext(remote)[0]
    t = safe_name(title, 100, "")
    if t and stem and stem.lower() not in t.lower():
        name = f"{t} [{safe_name(stem, 60)}]"
    else:
        name = t or safe_name(stem, 120, "file")
    return name + ext


def front_matter(d: dict) -> str:
    lines = ["---"]
    for k, v in d.items():
        if v in (None, "", [], {}):
            continue
        lines.append(f"{k}: {json.dumps(v, ensure_ascii=False)}")  # JSON scalars are valid YAML
    lines.append("---")
    return "\n".join(lines) + "\n\n"


def strip_elements(root, selectors) -> None:
    for sel in selectors:
        for t in root.select(sel):
            if not getattr(t, "decomposed", False):
                t.decompose()


def html_to_md(el) -> str:
    if el is None:
        return ""
    if _markdownify:
        s = _markdownify(str(el), heading_style="ATX", bullets="-",
                         strip=["a", "img", "button", "input", "select", "option", "label"])
    else:
        s = el.get_text("\n", strip=True)
    s = re.sub(r"[ \t]+\n", "\n", s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


def page_title(soup) -> str:
    h1 = soup.find("h1")
    t = txt(h1)
    if not t and soup.title:
        t = txt(soup.title).split("|")[0].strip()
    return t


# --------------------------------------------------------------------------- #
# robots.txt (supports * and $ wildcards, longest-match wins)
# --------------------------------------------------------------------------- #
class Robots:
    def __init__(self, fetch):
        self.fetch = fetch          # async (url) -> (text, final_url) | None  (rate-limited)
        self._rules: dict[str, asyncio.Task] = {}

    @staticmethod
    def _compile(v: str):
        anchor = v.endswith("$")
        body = v[:-1] if anchor else v
        return re.compile("^" + re.escape(body).replace(r"\*", ".*") + ("$" if anchor else ""))

    async def _load(self, host: str):
        rules = []
        res = await self.fetch(f"https://{host}/robots.txt")
        if not res:
            return rules
        body = res[0]
        active, rules_seen = False, False
        for raw in body.splitlines():
            line = raw.split("#", 1)[0].strip()
            if ":" not in line:
                continue
            k, v = (x.strip() for x in line.split(":", 1))
            k = k.lower()
            if k == "user-agent":
                if rules_seen:                       # a new group starts
                    active, rules_seen = False, False
                if v == "*":
                    active = True
            elif k in ("allow", "disallow"):
                rules_seen = True
                if active and v:
                    rules.append((k == "allow", self._compile(v), len(v)))
        return rules

    async def allowed(self, url: str) -> bool:
        u = urlsplit(url)
        t = self._rules.get(u.netloc)
        if t is None:
            t = self._rules[u.netloc] = asyncio.ensure_future(self._load(u.netloc))
        rules = await t
        target = u.path + (f"?{u.query}" if u.query else "")
        best = None
        for allow, rx, ln in rules:
            if rx.match(target) and (best is None or ln > best[1] or (ln == best[1] and allow)):
                best = (allow, ln)
        return best is None or best[0]


# --------------------------------------------------------------------------- #
# Rate limiting + WAF block handling
# --------------------------------------------------------------------------- #
class Aborted(Exception):
    """Raised to unwind everything once the run has been stopped."""


async def is_block(r: aiohttp.ClientResponse) -> bool:
    """True if the response is a rate-limit / WAF block rather than a real answer."""
    if r.status == 429:
        return True
    if r.status != 403:
        return False
    if "x-amzn-waf-action" in {k.lower() for k in r.headers.keys()}:
        return True
    try:
        body = (await r.content.read(4096)).decode("utf-8", "replace")
    except Exception:
        body = ""
    # CloudFront/WAF block page (a genuine S3 403 says "AccessDenied" instead)
    return "Request blocked" in body or "could not be satisfied" in body


class HostGate:
    """
    Paces requests to one host (FIFO, one slot every `interval` seconds) and
    acts as a circuit breaker: on a block it closes for a cool-down, slows the
    pace, and reopens. In-flight requests that were sent before the gate
    reopened don't trip it again - they just retry.
    """

    def __init__(self, name: str, rate: float, cooldown: float, max_blocks: int):
        self.name = name
        self.interval = 1.0 / max(rate, 0.01)
        self.cooldown = cooldown
        self.max_blocks = max_blocks
        self.lock = asyncio.Lock()
        self.open = asyncio.Event()
        self.open.set()
        self.next = 0.0
        self.reopened_at = 0.0
        self.strikes = 0           # consecutive blocks without a success in between
        self.total_blocks = 0
        self.aborted = False
        self.on_abort = None

    async def _wait_open(self):
        await self.open.wait()
        if self.aborted:
            raise Aborted()

    async def wait(self) -> float:
        """Wait for this request's turn; returns its start time (monotonic)."""
        async with self.lock:
            await self._wait_open()
            d = self.next - time.monotonic()
            if d > 0:
                await asyncio.sleep(d)
            await self._wait_open()
            self.next = time.monotonic() + self.interval * random.uniform(0.75, 1.25)
            return time.monotonic()

    def ok(self):
        self.strikes = 0

    async def blocked(self, started: float):
        if started < self.reopened_at or not self.open.is_set():
            await self._wait_open()          # stale response, or someone else is handling it
            return
        self.open.clear()
        self.strikes += 1
        self.total_blocks += 1
        if self.strikes > self.max_blocks:
            log.error("%s: still blocked after %d cool-downs - stopping. Wait 30-60 min and "
                      "re-run the same command (it resumes from cache).", self.name, self.max_blocks)
            if self.on_abort:
                self.on_abort()
            raise Aborted()
        cool = min(self.cooldown * (2 ** (self.strikes - 1)), 1800)
        self.interval *= 1.6
        log.warning("%s: the site is rate-limiting/blocking us (403/429). Pausing %d s "
                    "(block %d/%d), then continuing at %.2f req/s.",
                    self.name, cool, self.strikes, self.max_blocks, 1 / self.interval)
        await asyncio.sleep(cool)
        self.reopened_at = time.monotonic()
        self.next = 0.0
        self.open.set()
        if self.aborted:
            raise Aborted()

    def abort(self):
        self.aborted = True
        self.open.set()       # wake every waiter so it can raise Aborted


# --------------------------------------------------------------------------- #
# Data containers
# --------------------------------------------------------------------------- #
@dataclass
class Item:
    section: str
    tab: Optional[str]
    url: str
    kind: str
    title: str = ""
    meta: dict = field(default_factory=dict)


@dataclass
class PageData:
    url: str
    title: str
    description: str
    breadcrumb: list
    parts: list        # [(section, tab, markdown)]
    items: list        # [Item]
    children: set      # product-page URLs found anywhere on the page


@dataclass
class Doc:
    url: str
    kind: str          # library | news
    title: str
    date: str
    md: str
    files: list        # [(url, label)]
    related: list      # related product-page URLs (most specific)
    videos: list


@dataclass
class Ctx:
    folder: Path
    url: str = ""
    title: str = ""
    family: str = ""
    product_path: str = ""


# --------------------------------------------------------------------------- #
# Parsers (CPU-bound; run in worker threads)
# --------------------------------------------------------------------------- #
def parse_product_page(html: str, url: str, prefix: str) -> PageData:
    soup = BeautifulSoup(html, PARSER)
    title = page_title(soup)
    md_tag = soup.find("meta", attrs={"name": "description"})
    description = (md_tag.get("content") or "").strip() if md_tag else ""
    crumbs = soup.select(".breadcrumbs li") or soup.select(".breadcrumbs a")
    breadcrumb = [t for t in (txt(c) for c in crumbs) if t]
    main = soup.select_one("main.page-content") or soup.find("main") or soup.body or soup

    # 1) child product pages (mega-menu, side-nav, category cards, link lists ...)
    children = set()
    for a in soup.find_all("a", href=True):
        u = norm_url(a["href"], url)
        if u:
            s = urlsplit(u)
            if s.netloc == SITE_HOST and s.path.startswith(prefix):
                children.add(page_key(u))
    children.discard(url)

    # 2) sections: anchor ribbon first, then any other top-level <section id>
    ribbon, seen_ids = [], set()
    for a in soup.select(".anchor-nav-link a[href^='#'], .anchor-nav-links a[href^='#']"):
        sid = a["href"][1:].strip()
        if sid and sid not in seen_ids:
            seen_ids.add(sid)
            ribbon.append((sid, txt(a)))
    sec_els = []
    for sid, label in ribbon:
        el = soup.find(id=sid)
        if el is not None:
            sec_els.append((sid, label, el))
    picked = {id(e) for _, _, e in sec_els}
    for el in main.find_all("section", id=True):
        if id(el) in picked or any(id(p) in picked for p in el.parents):
            continue
        if el.find_parent("section", id=True) is not None:
            continue
        sec_els.append((el["id"], "", el))
        picked.add(id(el))

    # 3) split sections into tabs  ->  [(section, tab, element)]
    raw_parts = []
    for sid, label, el in sec_els:
        hdr = el.find("header", class_="section__header")
        name = txt(hdr.find(class_="section__title")) if hdr else ""
        name = name or label or sid.replace("-", " ").replace("_", " ")
        tab_names = {}
        for a in el.select(".tabs a[href]"):
            h = a["href"]
            if "#" in h:
                tab_names[h.split("#", 1)[1]] = txt(a)
        pat = re.compile("^" + re.escape(sid) + r"__(.+)_content$")
        blocks = el.find_all(id=pat)
        if blocks:
            for b in blocks:
                key = b["id"][: -len("_content")]
                tab = tab_names.get(key) or pat.match(b["id"]).group(1).replace("-", " ")
                raw_parts.append((name, tab, b))
        else:
            raw_parts.append((name, None, el))
    if not raw_parts:
        raw_parts.append(("Content", None, main))

    # 4) resource items in each part (before junk removal - tooltips hold descriptions)
    items: list[Item] = []
    for name, tab, el in raw_parts:
        found: dict[str, Item] = {}
        for a in el.find_all("a", href=True):
            if a.find_parent(class_="tabs") or a.find_parent(class_="section__nav"):
                continue
            u = norm_url(a["href"], url)
            if not u:
                continue
            kind = classify(u, prefix)
            if kind == "product":
                continue                      # handled by the crawler
            key = file_key(u) if kind == "file" else page_key(u)
            if key == url:
                continue
            meta, title = {}, ""
            card = a.find_parent(class_="infobox-card")
            news = a.find_parent("article", class_="card--news")
            if card is not None:
                title = txt(card.select_one(".infobox-card-title-link")) or txt(a)
                meta["label"] = txt(card.select_one(".infobox-card-header"))
                tip = card.parent.select_one(".tooltip_templates") if card.parent else None
                if tip is not None:
                    meta["description"] = txt(tip)[:1500]
            elif news is not None:
                title = txt(a) or txt(news.select_one(".card__body"))
                meta["date"] = txt(news.select_one(".card__header"))
            else:
                title = txt(a)
                li = a.find_parent("li")
                if li is not None and li.find_parent(class_="downloads-list") is not None:
                    meta["size"] = txt(li.find("span")).strip("() ")
                    h5 = a.find_previous("h5")
                    if h5 is not None and any(p is el for p in h5.parents):
                        g = txt(h5)
                        if g and g != tab:
                            meta["group"] = g
            title = title or a.get("title") or a.get("aria-label") or ""
            prev = found.get(key)
            if prev is None:
                found[key] = Item(name, tab, u if kind == "file" else key, kind, title, meta)
            else:
                if len(title) > len(prev.title):
                    prev.title = title
                for k, v in meta.items():
                    prev.meta.setdefault(k, v)
        items.extend(found.values())

    # 5) Markdown per part
    strip_elements(main, PAGE_JUNK)
    parts = []
    for name, tab, el in raw_parts:
        md = html_to_md(el)
        if md:
            parts.append((name, tab, md))

    return PageData(url, title, description, breadcrumb, parts, items, children)


def parse_doc_page(html: str, url: str, prefix: str) -> Doc:
    soup = BeautifulSoup(html, PARSER)
    title = page_title(soup) or urlsplit(url).path.rstrip("/").rsplit("/", 1)[-1].replace("-", " ")
    main = soup.select_one("main.page-content") or soup.find("main") or soup.body or soup

    related, files, seen = set(), [], set()
    for a in main.find_all("a", href=True):
        if a.find_parent(class_=re.compile("breadcrumb")):
            continue
        u = norm_url(a["href"], url)
        if not u:
            continue
        k = classify(u, prefix)
        if k == "product":
            related.add(page_key(u))
        elif k == "file":
            fk = file_key(u)
            if fk in seen:
                continue
            seen.add(fk)
            label = txt(a)
            if (not label or re.match(r"^(agree\W*(&|and)?\W*)?download\b", label, re.I)
                    or re.fullmatch(r"\(?[\d.,]+\s*[KMG]?B\)?", label, re.I)):
                label = ""
            files.append((u, label))

    rel = sorted(related)
    rel = [r for r in rel if not any(o != r and o.startswith(r) for o in rel)]  # most specific only

    videos = []
    for f in main.find_all("iframe", src=True):
        v = norm_url(f["src"], url)
        if v and v not in videos:
            videos.append(v)

    m = re.search(r"(\d{4}-\d{2}-\d{2})", url)
    date = m.group(1) if m else ""
    if not date:
        t = soup.find("time")
        date = (t.get("datetime") or txt(t))[:10] if t is not None else ""

    strip_elements(main, DOC_JUNK)
    md = html_to_md(main)
    kind = "news" if "/news/" in urlsplit(url).path else "library"
    return Doc(url, kind, title, date, md, files, rel, videos)


# --------------------------------------------------------------------------- #
# Scraper
# --------------------------------------------------------------------------- #
class TooBig(Exception):
    pass


class Scraper:
    def __init__(self, cfg: argparse.Namespace):
        self.cfg = cfg
        self.out = Path(cfg.out).resolve()
        self.cache_dir = self.out / "_cache"
        self.files_dir = self.cache_dir / "files"
        self.html_dir = self.cache_dir / "html"
        self.region = cfg.region.strip("/")
        self.prefix = f"/{self.region}/solutions/products-and-services/"
        self.families = {f.lower() for f in (cfg.families or [])}
        self.max_bytes = int(cfg.max_file_mb * 1024 * 1024)

        self.seen_pages: set[str] = set()
        self.captured_docs: set[str] = set()
        self.page_titles: dict[str, str] = {}
        self.memo: dict[str, asyncio.Future] = {}
        self.bg: set[asyncio.Task] = set()
        self.reserved: dict[Path, str] = {}
        self.stats: Counter = Counter()
        self.err_reasons: Counter = Counter()
        self.aborted = False
        self.t0 = time.time()

    def gate_for(self, url: str) -> HostGate:
        return self.page_gate if urlsplit(url).netloc == SITE_HOST else self.file_gate

    def abort(self):
        if not self.aborted:
            self.aborted = True
            for g in (self.page_gate, self.file_gate):
                g.abort()

    # ---------------- infrastructure ---------------- #
    def _once(self, key, factory):
        t = self.memo.get(key)
        if t is None:
            t = self.memo[key] = asyncio.ensure_future(factory())
        return t

    def spawn(self, coro):
        t = asyncio.create_task(self._guard(coro))
        self.bg.add(t)
        t.add_done_callback(self.bg.discard)

    async def _guard(self, coro):
        try:
            await coro
        except asyncio.CancelledError:
            raise
        except Exception as e:  # never let one item kill the run
            log.debug("task failed", exc_info=True)
            self.fail("", f"task error: {e!r}")

    async def _drain(self):
        while self.bg:
            await asyncio.gather(*list(self.bg), return_exceptions=True)

    def record(self, **row):
        lp = row.get("local_path")
        if isinstance(lp, Path):
            try:
                row["local_path"] = lp.relative_to(self.out).as_posix()
            except ValueError:
                row["local_path"] = str(lp)
        row = {k: v for k, v in row.items() if v not in (None, "", [], {})}
        self.manifest_fh.write(json.dumps(row, ensure_ascii=False) + "\n")

    def fail(self, url, reason, **kw):
        self.stats["errors"] += 1
        self.err_reasons[re.sub(r"\(.*", "", reason)[:60].strip()] += 1
        self.failures_fh.write(json.dumps({"url": url, "reason": reason, **kw}, ensure_ascii=False) + "\n")

    # ---------------- scope & paths ---------------- #
    def in_scope(self, url: str) -> bool:
        u = urlsplit(url)
        if u.netloc != SITE_HOST or not u.path.startswith(self.prefix):
            return False
        if self.families:
            fam = u.path[len(self.prefix):].split("/")[0]
            return fam == "" or fam in self.families
        return True

    def _segs(self, url: str) -> list[str]:
        path = urlsplit(url).path
        base = f"/{self.region}/solutions/"
        rel = path[len(base):] if path.startswith(base) else path.lstrip("/")
        return [s for s in rel.split("/") if s]

    def folder_for(self, url: str) -> Path:
        f = self.out
        for s in self._segs(url):
            f /= safe_name(s, 80)
        return f

    def ctx_for(self, url: str) -> Ctx:
        segs = self._segs(url)
        return Ctx(folder=self.folder_for(url), url=url, title=self.page_titles.get(url, ""),
                   family=segs[1] if len(segs) > 1 else "", product_path="/".join(segs))

    def section_dir(self, base: Path, section: str, tab: Optional[str], group: Optional[str] = None) -> Path:
        d = base / safe_name(section, 60)
        if tab:
            d /= safe_name(tab, 80)
        if group:
            d /= safe_name(group, 80)
        return d

    def _reserve(self, dest_dir: Path, name: str, owner: str) -> Path:
        dest_dir.mkdir(parents=True, exist_ok=True)
        stem, suf = os.path.splitext(name)
        cand, i = dest_dir / name, 2
        while True:
            o = self.reserved.get(cand)
            if o is None:
                self.reserved[cand] = owner
                return cand
            if o == owner:
                return cand
            cand = dest_dir / f"{stem} ({i}){suf}"
            i += 1

    def write_text(self, dest_dir: Path, name: str, text: str, owner: str) -> Path:
        p = self._reserve(dest_dir, name, owner)
        p.write_text(text, encoding="utf-8")
        return p

    def _materialize(self, src: Path, dest: Path):
        mode = self.cfg.link_mode
        if mode == "hardlink":
            try:
                os.link(src, dest)
                return
            except OSError:
                pass
        elif mode == "symlink":
            try:
                os.symlink(os.path.relpath(src, dest.parent), dest)
                return
            except OSError:
                pass
        shutil.copy2(src, dest)

    def place_file(self, m: dict, dest_dir: Path, title: str) -> Path:
        src = self.files_dir / m["file"]
        dest = self._reserve(dest_dir, build_file_name(title, m), owner=file_key(m["url"]))
        if dest.exists() or dest.is_symlink():
            try:
                if os.path.samefile(src, dest) or dest.stat().st_size == m["size"]:
                    return dest
            except OSError:
                pass
            dest.unlink()
        self._materialize(src, dest)
        self.stats["files_placed"] += 1
        return dest

    # ---------------- HTTP ---------------- #
    async def _get_text(self, url: str, record_fail: bool = True):
        """Rate-limited GET for HTML/XML/text. Blocks pause and retry; they never count as failures."""
        gate = self.gate_for(url)
        delay, attempt, err = 1.0, 0, ""
        while True:
            try:
                started = await gate.wait()
                async with self.session.get(url, allow_redirects=True) as r:
                    if await is_block(r):
                        self.stats["blocked_responses"] += 1
                        await gate.blocked(started)
                        continue                       # same request again, attempt not consumed
                    if r.status == 200:
                        gate.ok()
                        ct = r.headers.get("Content-Type", "").lower()
                        if ct and not any(x in ct for x in ("html", "xml", "text")):
                            return None
                        return await r.text(errors="replace"), str(r.url)
                    if r.status not in RETRY_STATUS:
                        if r.status != 404 and record_fail:
                            self.fail(url, f"HTTP {r.status}")
                        return None
                    ra = r.headers.get("Retry-After", "")
                    wait = float(ra) if ra.isdigit() else delay
                    err = f"HTTP {r.status}"
            except Aborted:
                return None
            except (aiohttp.ClientError, asyncio.TimeoutError) as e:
                wait, err = delay, type(e).__name__
            attempt += 1
            if attempt >= self.cfg.retries:
                if record_fail:
                    self.fail(url, f"page: {err} after {attempt} tries")
                return None
            await asyncio.sleep(wait + random.random() * 0.5)
            delay = min(delay * 2, 30)

    async def fetch_html(self, url: str):
        cp = self.html_dir / (sha1(url) + ".html.gz")
        if self.cfg.html_cache and not self.cfg.refresh and cp.exists():
            try:
                data = await asyncio.to_thread(cp.read_bytes)
                self.stats["html_cache_hits"] += 1
                return gzip.decompress(data).decode("utf-8", "replace"), url
            except Exception:
                pass
        async with self.page_sem:
            res = await self._get_text(url)
        if res:
            self.stats["html_fetched"] += 1
            if self.cfg.html_cache:
                await asyncio.to_thread(cp.write_bytes, gzip.compress(res[0].encode("utf-8"), 5))
        return res

    def download(self, url: str):
        return self._once("dl:" + file_key(url), lambda: self._download(url))

    async def _download(self, url: str) -> dict:
        key = file_key(url)
        h = sha1(key)
        meta_p = self.files_dir / (h + ".json")
        if meta_p.exists() and not (self.cfg.refresh and "gated" in meta_p.read_text()):
            try:
                m = json.loads(meta_p.read_text(encoding="utf-8"))
                if m.get("status") != "ok" or (self.files_dir / m["file"]).exists():
                    self.stats["dl_cache_hits"] += 1
                    return m
            except Exception:
                pass

        ext = url_ext(url)
        if ext in MEDIA_EXTS:
            self.stats["dl_skipped"] += 1
            return {"status": "skipped", "url": url, "reason": "image/media"}
        if ext in BIN_EXTS and not self.cfg.include_binaries:
            self.stats["dl_skipped"] += 1
            return {"status": "skipped", "url": url, "reason": "binary/software (use --include-binaries)"}
        if not await self.robots.allowed(url):
            self.stats["robots_blocked"] += 1
            return {"status": "skipped", "url": url, "reason": "robots.txt"}

        timeout = aiohttp.ClientTimeout(total=self.cfg.download_timeout, sock_connect=20, sock_read=120)
        gate = self.gate_for(url)
        delay, last_err, attempt = 1.0, "", 0
        async with self.dl_sem:
            while True:
                tmp = None
                try:
                    started = await gate.wait()
                    async with self.session.get(url, allow_redirects=True, timeout=timeout) as r:
                        if await is_block(r):
                            self.stats["blocked_responses"] += 1
                            await gate.blocked(started)
                            continue                   # retry the same file, attempt not consumed
                        if r.status == 200:
                            gate.ok()
                            ctype = r.headers.get("Content-Type", "").split(";")[0].strip().lower()
                            if ctype in ("text/html", "application/xhtml+xml") and ext not in SCRIPT_EXTS:
                                m = {"status": "gated", "url": url, "final_url": str(r.url),
                                     "reason": "server returned HTML (login / consent / missing file)"}
                                meta_p.write_text(json.dumps(m), encoding="utf-8")
                                self.stats["dl_gated"] += 1
                                return m
                            cd = r.headers.get("Content-Disposition")
                            real_ext = guess_ext(url, ctype, cd)
                            if real_ext in BIN_EXTS and not self.cfg.include_binaries:
                                self.stats["dl_skipped"] += 1
                                return {"status": "skipped", "url": url, "reason": "binary/software"}
                            if r.content_length and r.content_length > self.max_bytes:
                                raise TooBig()
                            final = self.files_dir / (h + real_ext)
                            tmp = final.with_name(final.name + ".part")
                            digest, n = hashlib.sha256(), 0
                            with open(tmp, "wb") as fh:
                                async for chunk in r.content.iter_chunked(1 << 17):
                                    n += len(chunk)
                                    if n > self.max_bytes:
                                        raise TooBig()
                                    digest.update(chunk)
                                    fh.write(chunk)
                            os.replace(tmp, final)
                            m = {"status": "ok", "url": url, "final_url": str(r.url), "file": final.name,
                                 "ext": real_ext, "size": n, "content_type": ctype,
                                 "sha256": digest.hexdigest(),
                                 "remote_name": cd_filename(cd) or os.path.basename(unquote(urlsplit(str(r.url)).path))}
                            meta_p.write_text(json.dumps(m), encoding="utf-8")
                            self.stats["downloaded"] += 1
                            self.stats["bytes"] += n
                            return m
                        if r.status not in RETRY_STATUS:
                            self.stats["dl_error"] += 1
                            self.err_reasons[f"download: HTTP {r.status}"] += 1
                            return {"status": "error", "url": url, "reason": f"HTTP {r.status}"}
                        last_err = f"HTTP {r.status}"
                except Aborted:
                    if tmp is not None:
                        tmp.unlink(missing_ok=True)
                    return {"status": "aborted", "url": url}
                except TooBig:
                    if tmp is not None:
                        tmp.unlink(missing_ok=True)
                    m = {"status": "skipped", "url": url, "reason": f"larger than {self.cfg.max_file_mb} MB"}
                    meta_p.write_text(json.dumps(m), encoding="utf-8")
                    self.stats["dl_skipped"] += 1
                    return m
                except (aiohttp.ClientError, asyncio.TimeoutError, OSError) as e:
                    last_err = type(e).__name__
                    if tmp is not None:
                        tmp.unlink(missing_ok=True)
                attempt += 1
                if attempt >= self.cfg.retries:
                    break
                await asyncio.sleep(delay + random.random())
                delay = min(delay * 2, 30)
        self.stats["dl_error"] += 1
        self.err_reasons[f"download: {last_err}"] += 1
        return {"status": "error", "url": url, "reason": f"retries exhausted: {last_err}"}

    def doc(self, url: str):
        k = page_key(url)
        return self._once("doc:" + k, lambda: self._doc(k))

    async def _doc(self, url: str) -> Optional[Doc]:
        if self.aborted:
            return None
        if not await self.robots.allowed(url):
            self.stats["robots_blocked"] += 1
            return None
        res = await self.fetch_html(url)
        if not res:
            return None
        d = await asyncio.to_thread(parse_doc_page, res[0], url, self.prefix)
        self.stats["docs"] += 1
        return d

    # ---------------- crawling ---------------- #
    def enqueue(self, url: str):
        k = page_key(url)
        if k in self.seen_pages or not self.in_scope(k):
            return
        if self.cfg.max_pages and len(self.seen_pages) >= self.cfg.max_pages:
            return
        self.seen_pages.add(k)
        self.queue.put_nowait(k)

    async def _worker(self):
        while True:
            url = await self.queue.get()
            try:
                await self.process_page(url)
            except Exception as e:
                log.debug("page failed", exc_info=True)
                self.fail(url, f"page error: {e!r}")
            finally:
                self.queue.task_done()

    async def process_page(self, url: str):
        if self.aborted:
            return
        if not await self.robots.allowed(url):
            self.stats["robots_blocked"] += 1
            return
        res = await self.fetch_html(url)
        if not res:
            if not self.aborted:
                self.stats["pages_failed"] += 1
            return
        html, final = res
        if page_key(final) != url and not self.in_scope(page_key(final)):
            self.stats["redirected_out"] += 1
            return
        pd: PageData = await asyncio.to_thread(parse_product_page, html, url, self.prefix)
        for c in pd.children:
            self.enqueue(c)

        self.page_titles[url] = pd.title
        ctx = self.ctx_for(url)
        ctx.folder.mkdir(parents=True, exist_ok=True)

        # _page.md - full text by section / tab
        out = [front_matter({
            "title": pd.title, "source_url": url, "family": ctx.family,
            "product_path": ctx.product_path, "breadcrumb": pd.breadcrumb,
            "description": pd.description, "fetched_at": now_iso()}),
            f"# {pd.title}\n"]
        if pd.breadcrumb:
            out.append("> " + " > ".join(pd.breadcrumb) + "\n")
        if pd.description:
            out.append(pd.description + "\n")
        last = None
        for sec, tab, md in pd.parts:
            if sec != last:
                out.append(f"\n## {sec}\n")
                last = sec
            if tab:
                out.append(f"\n### {tab}\n")
            out.append(md + "\n")
        page_md = ctx.folder / "_page.md"
        page_md.write_text("\n".join(out), encoding="utf-8")

        sections: dict[str, list] = {}
        for sec, tab, _ in pd.parts:
            sections.setdefault(sec, [])
            if tab and tab not in sections[sec]:
                sections[sec].append(tab)
        (ctx.folder / "_meta.json").write_text(json.dumps({
            "title": pd.title, "url": url, "family": ctx.family, "product_path": ctx.product_path,
            "breadcrumb": pd.breadcrumb, "description": pd.description, "sections": sections,
            "item_count": len(pd.items), "children": sorted(c for c in pd.children if self.in_scope(c)),
            "fetched_at": now_iso()}, ensure_ascii=False, indent=2), encoding="utf-8")
        self.record(type="page", local_path=page_md, source_url=url, family=ctx.family,
                    product_path=ctx.product_path, title=pd.title)

        for it in pd.items:
            self.spawn(self.handle_item(ctx, it))
        self.stats["pages"] += 1

    async def handle_item(self, ctx: Ctx, it: Item):
        if self.aborted:
            return
        dest =self.section_dir(ctx.folder, it.section, it.tab, it.meta.get("group"))
        if it.kind == "file":
            m = await self.download(it.url)
            self.handle_dl(m, dest, it.title, ctx, it.section, it.tab, parent=ctx.url, extra=it.meta)
        elif it.kind in ("library", "news"):
            if not is_detail_page(it.url):
                self.record(type="link", source_url=it.url, parent_url=ctx.url, section=it.section,
                            tab=it.tab, title=it.title, product_path=ctx.product_path)
                return
            self.captured_docs.add(page_key(it.url))
            d = await self.doc(it.url)
            if d:
                await self.place_doc(d, dest, ctx, it.section, it.tab, it.meta, it.title)
        else:  # internal / external link - keep as metadata only
            self.record(type=f"{it.kind}_link", source_url=it.url, parent_url=ctx.url,
                        section=it.section, tab=it.tab, title=it.title, product_path=ctx.product_path)

    def handle_dl(self, m, dest, title, ctx, section, tab, parent, extra=None):
        if m.get("status") == "aborted":
            return
        base =dict(source_url=m.get("url"), parent_url=parent, family=ctx.family,
                    product_path=ctx.product_path, product_title=ctx.title,
                    section=section, tab=tab, title=title)
        if extra:
            base.update({k: v for k, v in extra.items() if k in ("group", "label", "date", "description")})
        if m.get("status") == "ok":
            p = self.place_file(m, dest, title)
            self.record(type="file", local_path=p, size=m["size"], content_type=m.get("content_type"),
                        sha256=m.get("sha256"), **base)
        else:
            row = dict(type=m.get("status"), reason=m.get("reason"), **base)
            self.record(**row)
            if m.get("status") in ("gated", "error"):
                self.failures_fh.write(json.dumps(row, ensure_ascii=False) + "\n")

    async def place_doc(self, d: Doc, dest: Path, ctx: Ctx, section: str, tab: Optional[str],
                        extra: Optional[dict] = None, link_title: str = ""):
        extra = extra or {}
        date = d.date or extra.get("date", "")
        title = d.title or link_title or "untitled"
        stem = f"{date} - {title}" if (d.kind == "news" and date) else title
        fm = {
            "title": title, "source_url": d.url, "doc_kind": d.kind,
            "doc_type": f"{section}/{tab}" if tab else section, "date": date,
            "family": ctx.family, "product": ctx.title, "product_path": ctx.product_path,
            "product_url": ctx.url, "label": extra.get("label"), "summary": extra.get("description"),
            "video_urls": d.videos, "attachments": [u for u, _ in d.files],
            "related_products": d.related, "fetched_at": now_iso(),
        }
        p = self.write_text(dest, safe_name(stem, 120) + ".md",
                            front_matter(fm) + f"# {title}\n\n{d.md}\n", owner=d.url)
        self.record(type="resource_page", local_path=p, source_url=d.url, parent_url=ctx.url,
                    family=ctx.family, product_path=ctx.product_path, section=section, tab=tab,
                    title=title, date=date)
        if d.files:
            results = await asyncio.gather(*(self.download(u) for u, _ in d.files))
            for (u, label), m in zip(d.files, results):
                self.handle_dl(m, dest, label or title, ctx, section, tab, parent=d.url)

    # ---------------- sweep (library + news not linked from product tabs) ---------------- #
    async def sweep(self, sitemap: list[str]):
        lib_p, news_p = f"/{self.region}/library/", f"/{self.region}/news/"
        todo = []
        for u in sitemap:
            k = page_key(u)
            p = urlsplit(k).path
            if k in self.captured_docs or not is_detail_page(k):
                continue
            if p.startswith(lib_p) or p.startswith(news_p):
                todo.append(k)
        eta = len(todo) * self.page_gate.interval / 60
        log.info("Sweep: %d extra library/news pages not linked from product tabs "
                 "(~%.0f min at the current pace, less for pages already cached)", len(todo), eta)
        for k in todo:
            self.spawn(self._sweep_one(k))
        await self._drain()

    async def _sweep_one(self, url: str):
        d = await self.doc(url)
        if not d:
            return
        self.stats["sweep_docs"] += 1
        if d.kind == "library":
            sec, tab = lib_section_tab(url)
            targets = [r for r in d.related if self.in_scope(r)]
            if targets:
                for r in targets:
                    await self.place_doc(d, self.section_dir(self.folder_for(r), sec, tab),
                                         self.ctx_for(r), sec, tab)
            elif not self.families:
                dest = self.out / "_library" / safe_name(sec) / safe_name(tab)
                await self.place_doc(d, dest, Ctx(folder=dest), sec, tab)
        else:
            if self.families:
                return
            rest = [s for s in urlsplit(url).path.split(f"/{self.region}/news/", 1)[1].split("/") if s][:-1]
            dest = self.out / "_news"
            for s in rest:
                dest /= safe_name(s, 60)
            await self.place_doc(d, dest, Ctx(folder=dest), "News", None)

    # ---------------- sitemap ---------------- #
    async def load_sitemap(self) -> list[str]:
        urls: list[str] = []
        res = await self._get_text(f"{SITE}/sitemaps/sitemap-{self.region}.xml")
        if not res:
            idx = await self._get_text(f"{SITE}/sitemap_index.xml")
            if idx:
                for loc in re.findall(r"<loc>\s*([^<\s]+)\s*</loc>", idx[0]):
                    if f"sitemap-{self.region}." in loc:
                        res = await self._get_text(htmllib.unescape(loc))
                        break
        if res:
            urls = [htmllib.unescape(u) for u in re.findall(r"<loc>\s*([^<\s]+)\s*</loc>", res[0])]
        log.info("Sitemap: %d URLs", len(urls))
        return urls

    # ---------------- progress ---------------- #
    async def _ticker(self):
        while True:
            await asyncio.sleep(15)
            s = self.stats
            paused = [g.name for g in (self.page_gate, self.file_gate) if not g.open.is_set()]
            log.info("pages %d (queued %d) | docs %d | files %d new (%.1f MB), %d placed | "
                     "cache hits %d | skipped %d | gated %d | errors %d | blocks %d | "
                     "pace %.2f/%.2f req/s%s | %.0fs",
                     s["pages"], self.queue.qsize(), s["docs"], s["downloaded"], s["bytes"] / 1e6,
                     s["files_placed"], s["dl_cache_hits"] + s["html_cache_hits"], s["dl_skipped"],
                     s["dl_gated"], s["errors"] + s["dl_error"],
                     self.page_gate.total_blocks + self.file_gate.total_blocks,
                     1 / self.page_gate.interval, 1 / self.file_gate.interval,
                     f" | PAUSED ({', '.join(paused)})" if paused else "", time.time() - self.t0)
            self.manifest_fh.flush()
            self.failures_fh.flush()

    # ---------------- main ---------------- #
    async def run(self):
        for d in (self.out, self.files_dir, self.html_dir):
            d.mkdir(parents=True, exist_ok=True)
        self.manifest_fh = open(self.out / "manifest.jsonl", "w", encoding="utf-8")
        self.failures_fh = open(self.out / "failures.jsonl", "w", encoding="utf-8")
        self.queue: asyncio.Queue = asyncio.Queue()
        self.page_sem = asyncio.Semaphore(self.cfg.page_concurrency)
        self.dl_sem = asyncio.Semaphore(self.cfg.download_concurrency)

        connector = aiohttp.TCPConnector(
            limit=self.cfg.page_concurrency + self.cfg.download_concurrency + 4,
            limit_per_host=self.cfg.per_host, ttl_dns_cache=600)
        timeout = aiohttp.ClientTimeout(total=None, sock_connect=20, sock_read=90)
        headers = {"User-Agent": self.cfg.user_agent, "Accept-Language": "en-SG,en;q=0.9"}

        ticker = None
        try:
            async with aiohttp.ClientSession(connector=connector, timeout=timeout, headers=headers) as session:
                self.session = session
                self.page_gate = HostGate(SITE_HOST, self.cfg.rate, self.cfg.cooldown, self.cfg.max_blocks)
                self.file_gate = HostGate("file hosts", self.cfg.file_rate, self.cfg.cooldown, self.cfg.max_blocks)
                for g in (self.page_gate, self.file_gate):
                    g.on_abort = self.abort
                self.robots = Robots(lambda u: self._get_text(u, record_fail=False))
                ticker = asyncio.create_task(self._ticker())

                sitemap = await self.load_sitemap()
                if self.aborted:
                    return
                if not sitemap:
                    log.warning("Sitemap could not be loaded - discovering pages from links only.")
                self.enqueue(SITE + self.prefix)
                for f in sorted(self.families):
                    self.enqueue(f"{SITE}{self.prefix}{f}/")
                for u in sitemap:
                    if urlsplit(u).path.startswith(self.prefix):
                        self.enqueue(u)

                log.info("Phase 1: crawling product pages (%d seeded)", len(self.seen_pages))
                workers = [asyncio.create_task(self._worker()) for _ in range(self.cfg.page_concurrency)]
                await self.queue.join()
                for w in workers:
                    w.cancel()
                log.info("Phase 1: %d pages parsed, finishing resource downloads ...", self.stats["pages"])
                await self._drain()

                if not self.cfg.no_sweep and not self.aborted:
                    log.info("Phase 2: sweeping library & news from sitemap")
                    await self.sweep(sitemap)
        finally:
            if ticker:
                ticker.cancel()
            self.manifest_fh.close()
            self.failures_fh.close()
            gates = [g for g in (getattr(self, "page_gate", None), getattr(self, "file_gate", None)) if g]
            report = {"finished_at": now_iso(), "seconds": round(time.time() - self.t0, 1),
                      "aborted": self.aborted,
                      "pages_discovered": len(self.seen_pages), "stats": dict(self.stats),
                      "error_reasons": dict(self.err_reasons.most_common()),
                      "rate_limit": {g.name: {"blocks": g.total_blocks, "final_req_per_s": round(1 / g.interval, 3)}
                                     for g in gates},
                      "config": {k: v for k, v in vars(self.cfg).items()}}
            (self.out / "crawl_report.json").write_text(json.dumps(report, indent=2, default=str),
                                                        encoding="utf-8")
            s = self.stats
            log.info("DONE in %.0fs | pages %d | docs %d | files downloaded %d (%.1f MB) | placed %d | "
                     "gated %d | skipped %d | errors %d  ->  %s",
                     time.time() - self.t0, s["pages"], s["docs"], s["downloaded"], s["bytes"] / 1e6,
                     s["files_placed"], s["dl_gated"], s["dl_skipped"], s["errors"] + s["dl_error"], self.out)
            if self.err_reasons:
                log.info("Top error reasons: %s",
                         "; ".join(f"{k} x{v}" for k, v in self.err_reasons.most_common(6)))
            if self.aborted:
                log.warning("Run stopped early because the site kept blocking this IP. Wait 30-60 min, "
                            "then re-run the same command (optionally with lower --rate/--file-rate). "
                            "Everything already fetched is cached and will be skipped.")
            elif s["pages_failed"]:
                log.warning("%d pages failed - re-run the same command to retry just those.", s["pages_failed"])


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(description="Scrape Yokogawa Products & Services into a RAG knowledge base.")
    ap.add_argument("--out", default="yokogawa_kb", help="output folder (default: yokogawa_kb)")
    ap.add_argument("--region", default="sg", help="site region prefix, e.g. sg, us, in (default: sg)")
    ap.add_argument("--families", nargs="*",
                    help="limit to families, e.g. information control measurement consulting "
                         "project-execution lifecycle-services life-science announcements")
    ap.add_argument("--rate", type=float, default=1.0,
                    help="max page requests/second to www.yokogawa.com (default 1.0)")
    ap.add_argument("--file-rate", type=float, default=1.0,
                    help="max file downloads started/second on file hosts (default 1.0)")
    ap.add_argument("--cooldown", type=float, default=300,
                    help="pause (s) after the first block; doubles each time, max 30 min (default 300)")
    ap.add_argument("--max-blocks", type=int, default=5,
                    help="stop after this many consecutive blocks (default 5)")
    ap.add_argument("--page-concurrency", type=int, default=4, help="parallel HTML fetches (default 4)")
    ap.add_argument("--download-concurrency", type=int, default=4, help="parallel file downloads (default 4)")
    ap.add_argument("--per-host", type=int, default=6, help="max connections per host (default 6)")
    ap.add_argument("--retries", type=int, default=4)
    ap.add_argument("--max-pages", type=int, default=0, help="stop discovering after N product pages (testing)")
    ap.add_argument("--max-file-mb", type=float, default=300, help="skip files larger than this (default 300)")
    ap.add_argument("--download-timeout", type=int, default=900, help="per-file timeout in seconds")
    ap.add_argument("--include-binaries", action="store_true",
                    help="also download software packages (.zip/.exe) - licence-gated, not useful for RAG")
    ap.add_argument("--no-sweep", action="store_true", help="skip the sitemap library/news sweep")
    ap.add_argument("--refresh", action="store_true", help="ignore cached HTML (downloaded files are kept)")
    ap.add_argument("--no-html-cache", dest="html_cache", action="store_false", help="don't cache HTML pages")
    ap.add_argument("--link-mode", choices=["hardlink", "copy", "symlink"], default="hardlink",
                    help="how a shared file is placed into each folder (default hardlink)")
    ap.add_argument("--user-agent", default="Mozilla/5.0 (compatible; YokogawaKB-Builder/1.0; research)")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format="%(asctime)s %(levelname)-7s %(message)s", datefmt="%H:%M:%S")
    if args.verbose:
        logging.getLogger("asyncio").setLevel(logging.WARNING)
    if _markdownify is None:
        log.warning("markdownify not installed - pages will be saved as plain text (pip install markdownify)")
    if sys.platform.startswith("win"):
        asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

    try:
        asyncio.run(Scraper(args).run())
    except KeyboardInterrupt:
        log.warning("Interrupted - partial results kept. Re-run the same command to resume.")


if __name__ == "__main__":
    main()
