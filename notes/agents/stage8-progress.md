# Stage 8 progress: home page refresh

- Scripts: /tmp/hp/extract.py (HTML + tex + PDF data), /tmp/hp/apply.py (entries, insertion, old->new item renumbering in prose, summary pages/counts).
- All home_page/*.md: entries renumbered, Lean names refreshed from `\lean{}` (10 entries changed their "+N more"), 13 new entries inserted (9 in sec10-5, 2 in sec10-6, 2 in sec10-7); item numbers in prose remapped old->new by label; summary/heading pages and item counts recomputed.
- Pages: /tmp/hp/pages.py recomputed section ranges (TOC heading pages; printed page = PDF page - 2), layer and subsection pages from item heading pages in the PDF, in all section pages, index.md and guide.md.
- Prose: sec10-5 (146 items; sentences for Definitions 336, 339, Lemmas 337-338, 390, 437-440), sec10-6 (162 items; Lemma 604, Theorem 605), sec10-7 (51 items; Theorem 645, Lemma 647, §10.7.1 items 646-647), sec10-2 ("largest by proposition count", since §10.5 and §10.6 are now larger).
- index.md / guide.md: 345 pages, 675 declarations (153 def, 159 thm, 259 lem, 99 prop, 5 cor), 1,188 distinct Lean declarations, 522 provable / 482 with written proof, table rows and pages.
- Checks: 681 blueprint links, 0 bad anchors; check_temporal_wording.py OK.
