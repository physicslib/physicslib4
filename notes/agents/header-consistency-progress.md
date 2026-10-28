# Header consistency: website, tutorial, reference manual (2026-10-28)

## Cause

- `Book.bookCss` set `.site-header .nav-link { font-size: var(--fs-base) }` (16px), while the
  website uses `navbar.css`'s `0.9rem` (14.4px). Root font size is 16px on all three pages, so the
  difference came only from that override.
- The manual genre's search script appends `#search-wrapper` to `<header>`; it was a 256px flex item
  beside `.navbar`, shrinking the nav row and shifting the links 289px left.
- Other drift: header height 93px (site, `--nav-padding-y`) vs 73px (books), wordmark line height
  (site 1.2 from `layout.css`, books from `book.css`), and on phones the books' wordmark was pushed
  right (x=72 vs 24) to make room for the table-of-contents burger.

## Fix (files: `web/Site/Theme.lean`, `web/Book/Theme.lean`)

- `Site.headerCss`: one rule set pinning the header's height (`--site-header-height: 4.5rem`),
  padding, container width, font family/size/weight/line height of wordmark and links, list and
  button resets, on `header.site-header` selectors. Included in the website's `<style>` and in the
  books' `physicslib4.css`. The books' `--verso-header-height` is `var(--site-header-height)`.
- `bookCss` keeps only `position: fixed` for the header; the font-size override is gone.
- Search: `Book.searchToToc` (inline script, MutationObserver) moves `#search-wrapper` from the
  header to the top of the table of contents, under the book title, full sidebar width. On phones it
  is in the slide-in table of contents (previously hidden below 1024px).
- On phones (<=700px) the table-of-contents button is placed in the header left of the navigation
  button (lines of unequal length, to tell the two apart), so the wordmark keeps x=24.

## Measurements (headless Chromium, playwright-core, served from /tmp/srv on :8765)

Identical on site, tutorial and manual, in light and dark mode:

| width | header | wordmark (x,y w x h, font) | nav menu | links x/width/font |
|---|---|---|---|---|
| 1280 | 1280x72 | 48,22.06 121.05x26.88, 22.4px | 193.05,13.50 1038.95x44 | 661.5/85.0, 754.5/156.3, 918.8/95.6, 1022.4/89.6, 1120.0/52.0, 1180.0/52.0; all 14.4px |
| 390 | 390x72 | 24,22.05 121.05x26.88, 22.4px | hidden; toggle 313.86,4.30 52.14x62.39 | 14.4px |

Before: books' links at 372.3 ... 924.0, 16px; site header 93px tall; phone wordmark x=72 in books.

Search box after: in `#toc .first`, 288px wide at x=0 (desktop); results list 272px wide below it.

Screenshots: `notes/agents/header-consistency/{before,after}-*.png`, plus
`after-1280-manual-search-in-toc.png` and `after-390-manual-toc-open.png`.

`python3 scripts/check_temporal_wording.py`: OK.
