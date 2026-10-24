# Home page renumber, 2026-10-24

- Scripts: /tmp/hp4/extract.py (HTML labels/kinds/numbers/titles/page files + `\lean{}` from tex -> nodes.json), /tmp/hp4/check.py (entry number, "+N more" and first Lean name vs nodes.json), /tmp/hp4/apply.py (entry renumber by label + "+N more"; prose remap 529–693 -> +5; §10.6.N for N >= 6 -> N+1). Backup of home_page in /tmp/hp4/backup.
- Chapter 10: 686 items, 13–698; 683 declarations (157 def, 160 thm, 262 lem, 99 prop, 5 cor) + 3 conventions; 1,268 distinct Lean names. Old->new: 529–693 +5; new Definition 529 (def:unitary-conjugation), Lemma 530 (lmm:automorphism-commutant), Definition 531 (def:factor), Lemma 532 (lmm:factor-conj), Lemma 533 (lmm:restrict-star-alg-equiv), in new subsection §10.6.6 Conjugation by a Unitary (with Theorems 534–536); later §10.6 subsections renumber §10.6.7–§10.6.16.
- PDF: 348 pages; printed = PDF - 2; §10.6 290–332 (§10.6.5 310, §10.6.6 311, §10.6.7 313, §10.6.8 314, §10.6.9 318, §10.6.10 319, §10.6.11 320, §10.6.12 323, §10.6.13 324, §10.6.14–15 330, §10.6.16 331); §10.7 332–344 (subsections 336/336/338/340/340/341/342); §10.8 344–346.
- sec10-6-haag-kastler.md: entries renumbered 529–644; inserted entries 529–533 and a new `<details>` block "§10.6.6 Conjugation by a Unitary (p. 311) — 8 items" (529–536), §10.6.5 now 10 items (519–528); new summary bullet for §10.6.6 (Theorems 534–536 sentence moved there from §10.6.5); subsection numbers and pages updated; 169 items; `Conjugation` added to "Where the Lean lives". Done.
- sec10-7-curved.md: entries 645–696; prose remapped; §10.6.6 -> §10.6.7 reference; §10.7.2 mirrors "§10.6.5 and §10.6.6"; pages 332–344 and subsections. Done.
- sec10-8-general-covariance.md: entries 697–698; pages 344–346, subsection p. 344. Done.
- axioms.md: Definitions 646–648, 650–652, 698 remapped. Done.
- index.md: 348 pages, 683 declarations (157 def, 262 lem), 1,268 Lean, items 13–698, 526 provable / 486 written proof (the three new lemmas carry proofs), §10.6 row 290–332 43/72/54 = 169, §10.7 332–344, §10.8 344–346, totals row, Definitions 646–651/651/652/698. Done.
- guide.md: 348 pages, 683 declarations (157 def, 262 lem), 1,268 Lean, items 13–698, section page ranges, `Conjugation` in §10.6 Lean row. Done.
- sec10-1–sec10-5: no change (check.py: only the known hand-ordered lmm:isometry-preserves-classification).
- Checks: 686 blueprint links, 0 bad anchors; prose kind/number cross-check clean (one false positive: range "Definitions 330–475" in sec10-5); check_temporal_wording.py OK.
