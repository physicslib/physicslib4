# Home page renumber, 2026-10-21

- Scripts: /tmp/hp2/extract.py (HTML labels/kinds/numbers/titles + `\lean{}` from tex -> nodes.json), /tmp/hp2/oldmap.py (old->new number map by label from current entries), /tmp/hp2/apply.py (entry renumber + "+N more", prose remap of 548–690).
- Chapter 10: 680 items, 13–692; 677 declarations (154 def, 160 thm, 259 lem, 99 prop, 5 cor) + 3 conventions. Old->new: 548–602 +1, 603->606, 604 unchanged, 605–690 +2.
- PDF: 346 pages; printed = PDF - 2; §10.5 250–290, §10.6 290–331, §10.7 331–341, §10.8 341–344.
- sec10-1-gns.md: "+N more" for lmm:cauchy-schwarz-inequality, lmm:lmm1, lmm:lmm2. Done.
- sec10-2-spectral.md: "+N more" for def:bounded-sesquilinear-form, def:bump-function (tex already had these names). Done.
- sec10-3-unbounded.md, sec10-4-stone.md: no change needed.
- sec10-5-spacetime.md: "+N more" for def:alexandrov-topology, lmm:isometry-preserves-classification (+4), def:lorentz-path; pages: section 250–290, §10.5.3 p. 268. Done.
- sec10-6-haag-kastler.md: entries renumbered (164, 476–639, in order); "+N more" for thrm:state-space-convex-bridge (+3), def:disjoint-representations (+3), thrm:purity-covariance-invariant (+2); inserted Definition 548 (def:generated-von-neumann-algebra) before Theorem 549 and Theorem 605 (thrm:invariant-state-gns-unitary-general) before Theorem 606; Lemma 604 moved before Theorem 605; summary counts §10.6.7 24, §10.6.12 30; prose remapped, 164 items, sentences for Definition 548 and Theorems 604–607; pages 290–331, layers 290–306 and 306–308, §10.6.9 318, §10.6.12 323, §10.6.13–14 329, §10.6.15 330. Done.
- Fix: apply.py's first version skipped item numbers followed by a comma; re-applied the map to those 3 in sec10-6 and 4 in sec10-7 (regex corrected in /tmp/hp2/apply.py).
- sec10-7-curved.md: entries 640–690 (51); prose remapped; pages +1 (331–341, subsections 334/334/336/338/338/339/340). Done.
- sec10-8-general-covariance.md: entries 691–692; pages 341–344. Done.
- axioms.md: Definitions 640–646, 692, Lemma 598 remapped. Done.
- index.md, guide.md: 346 pages, 677 declarations (154 def, 160 thm), 1,219 Lean, items 13–692, 523 provable / 483 written proof, table rows and section pages. Done.
- Checks: 683 blueprint links, 0 bad anchors; prose kind/number cross-check clean; check_temporal_wording.py OK.
