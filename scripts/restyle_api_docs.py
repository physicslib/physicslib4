#!/usr/bin/env python3
"""Give the API docs (doc-gen4's HTML) the look of the rest of the physicslib4 site.

Usage: python3 scripts/restyle_api_docs.py DOCS_DIR [--jobs N]

DOCS_DIR is doc-gen4's output directory, as published at /physicslib4/docs/. The script rewrites its
pages in place:

- the site's shared header (web/docs-theme/site-header.html, with "API docs" as the active entry)
  takes the place of doc-gen4's top bar; doc-gen4's search form moves into it, between the wordmark
  and the links, and the page name of a module page moves to the top of the text;
- every page, and the module list (navbar.html), loads the site's fonts, the stylesheet
  physicslib4-docs.css (web/docs-theme/), the site's theme script physicslib4-theme.js
  (blueprint/src/webtheme/) and physicslib4-docs.js (web/docs-theme/), which keeps doc-gen4's colour
  scheme in step with the site's theme; these three files are copied into DOCS_DIR;
- the icon is the site's.

A rewritten page carries the marker <meta name="physicslib4-restyle">, and pages with the marker are
left alone, so running the script again changes nothing. Standard library only.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
THEME_DIR = REPO / "web" / "docs-theme"
HEADER_TEMPLATE = THEME_DIR / "site-header.html"
# File name in DOCS_DIR -> source in the repository.
ASSETS = {
    "physicslib4-docs.css": THEME_DIR / "physicslib4-docs.css",
    "physicslib4-docs.js": THEME_DIR / "physicslib4-docs.js",
    "physicslib4-theme.js": REPO / "blueprint" / "src" / "webtheme" / "physicslib4-theme.js",
}
SITE_ICON = "/physicslib4/favicon.png"

MARKER = b'<meta name="physicslib4-restyle" content="1">'
MARKER_PROBE = b'name="physicslib4-restyle"'
# doc-gen4 opens the body of every page but the module list with its checkbox and its top bar.
BODY_START = b'<body><input id="nav_toggle" type="checkbox"></input><header>'
HEADER_END = b"</header>"
FORM_START = b'<form id="search_form">'
FORM_END = b"</form>"
SEARCH_INPUT = b'<input type="text" name="q" autocomplete="off"></input>'
SEARCH_INPUT_NEW = (
    b'<input type="search" name="q" autocomplete="off" placeholder="Search the API docs"'
    b' aria-label="Search the API docs"></input>'
)
PAGE_NAME = re.compile(rb'<h2 class="header_filename break_within">(.*?)</h2>', re.S)
ICON = re.compile(rb'<link rel="icon" href="[^"]*favicon\.svg"></link>')
FONTS = (
    b'<link rel="preconnect" href="https://fonts.googleapis.com">'
    b'<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin="anonymous">'
    b'<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Fira+Code:wght@300..700'
    b'&amp;family=Open+Sans:ital,wght@0,300..800;1,300..800&amp;display=swap">'
)


def load_header() -> bytes:
    """The shared header, without its leading comment, on one line, with a slot for the form."""
    text = HEADER_TEMPLATE.read_text(encoding="utf-8")
    text = re.sub(r"\A\s*<!--.*?-->\s*", "", text, flags=re.S)
    if "\nSEARCH_FORM\n" not in text:
        raise SystemExit(f"{HEADER_TEMPLATE}: no SEARCH_FORM line")
    # Whitespace between tags only separates flex items here, so it can go.
    text = re.sub(r">\s*\n\s*", ">", text).replace("SEARCH_FORM", "\x00").strip()
    text = re.sub(r"\s*\x00\s*", "\x00", text)
    return text.encode("utf-8")


def head_additions(prefix: str) -> bytes:
    p = prefix.encode()
    return (
        FONTS
        + b'<link rel="stylesheet" href="' + p + b'physicslib4-docs.css">'
        + b'<script src="' + p + b'physicslib4-theme.js"></script>'
        + b'<script src="' + p + b'physicslib4-docs.js"></script>'
    )


def restyle(data: bytes, prefix: str, header: bytes) -> tuple[bytes | None, str]:
    """The rewritten page and what was done: 'page', 'navbar', 'done' (marked) or 'other'."""
    head_end = data.find(b"</head>")
    if head_end < 0:
        return None, "other"
    if MARKER_PROBE in data[:head_end]:
        return None, "done"
    head_start = data.find(b"<head>")
    if head_start < 0 or head_start > head_end:
        return None, "other"
    head = data[head_start + len(b"<head>"):head_end]
    body_start = data.find(BODY_START, head_end)
    if body_start >= 0:
        kind = "page"
    elif b'class="navframe"' in data and b'<base target="_parent">' in head:
        kind = "navbar"
    else:
        return None, "other"

    head = ICON.sub(b'<link rel="icon" href="' + SITE_ICON.encode() + b'"></link>', head, count=1)
    new_head = b"<head>" + MARKER + head + head_additions(prefix) + b"</head>"
    if kind == "navbar":
        return data[:head_start] + new_head + data[head_end + len(b"</head>"):], kind

    old_start = body_start + len(BODY_START) - len(b"<header>")
    old_end = data.find(HEADER_END, old_start)
    if old_end < 0:
        return None, "other"
    old_end += len(HEADER_END)
    old_header = data[old_start:old_end]
    f0 = old_header.find(FORM_START)
    f1 = old_header.find(FORM_END, f0)
    if f0 < 0 or f1 < 0:
        return None, "other"
    form = old_header[f0:f1 + len(FORM_END)].replace(SEARCH_INPUT, SEARCH_INPUT_NEW, 1)
    rest = data[old_end:]
    # A module page: the page name (from doc-gen4's top bar) goes to the top of the text.
    name = PAGE_NAME.search(old_header)
    main = rest.find(b"<main>") if name and b"const MODULE_NAME=" in head else -1
    if main >= 0:
        main += len(b"<main>")
        rest = (rest[:main] + b'<div class="docs-page-name break_within">' + name.group(1)
                + b"</div>" + rest[main:])
    new_header = header.replace(b"\x00", form)
    return (data[:head_start] + new_head + data[head_end + len(b"</head>"):old_start]
            + new_header + rest), kind


def process(path: str, prefix: str, header: bytes) -> str:
    with open(path, "rb") as f:
        data = f.read()
    new, kind = restyle(data, prefix, header)
    if new is not None:
        with open(path, "wb") as f:
            f.write(new)
    return kind


def process_chunk(chunk: tuple[bytes, list[tuple[str, str]]]) -> list[tuple[str, str]]:
    header, jobs = chunk
    return [(path, process(path, prefix, header)) for path, prefix in jobs]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("docs_dir", type=Path, help="doc-gen4's output directory")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 1,
                        help="worker processes (default: the number of CPUs)")
    args = parser.parse_args()
    docs = args.docs_dir
    if not (docs / "navbar.html").is_file():
        print(f"error: {docs} has no navbar.html; is it doc-gen4's output?", file=sys.stderr)
        return 1
    started = time.monotonic()
    header = load_header()
    for name, source in ASSETS.items():
        shutil.copyfile(source, docs / name)

    jobs = []
    for dirpath, _dirnames, filenames in os.walk(docs):
        rel = Path(dirpath).relative_to(docs)
        depth = 0 if rel == Path(".") else len(rel.parts)
        prefix = "../" * depth if depth else "./"
        for filename in filenames:
            if filename.endswith(".html"):
                jobs.append((os.path.join(dirpath, filename), prefix))

    chunks = [(header, jobs[i:i + 200]) for i in range(0, len(jobs), 200)]
    counts: dict[str, int] = {}
    others = []
    if args.jobs > 1 and len(chunks) > 1:
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            results = [r for chunk in pool.map(process_chunk, chunks) for r in chunk]
    else:
        results = [r for chunk in chunks for r in process_chunk(chunk)]
    for path, kind in results:
        counts[kind] = counts.get(kind, 0) + 1
        if kind == "other":
            others.append(os.path.relpath(path, docs))

    elapsed = time.monotonic() - started
    print(f"{len(jobs)} HTML files in {docs}: {counts.get('page', 0)} pages and "
          f"{counts.get('navbar', 0)} module list restyled, {counts.get('done', 0)} already "
          f"restyled, {counts.get('other', 0)} left as they are ({elapsed:.1f}s)")
    for path in sorted(others)[:20]:
        print(f"  left as it is: {path}")
    if counts.get("page", 0) + counts.get("done", 0) == 0:
        print("error: no page has doc-gen4's top bar; has doc-gen4's HTML changed?", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
