# Home page renumber, 2026-10-22

- Scripts: /tmp/hp3/extract.py (HTML labels/kinds/numbers/titles/page files + `\lean{}` from tex -> nodes.json), /tmp/hp3/check.py (entry number, "+N more" and first Lean name vs nodes.json), /tmp/hp3/apply.py (entry renumber by label + "+N more"; prose remap 640–692 -> +1).
- Chapter 10: 681 items, 13–693; 678 declarations (155 def, 160 thm, 259 lem, 99 prop, 5 cor) + 3 conventions; 1,231 distinct Lean names. Old->new: 640–692 +1; new Definition 640 (def:abstract-lorentzian-spacetime-interface).
- PDF: 347 pages; printed = PDF - 2; §10.1–§10.6 unchanged; §10.7 331–343 (subsections 335/335/337/339/339/340/341), §10.8 343–345.
- sec10-7-curved.md: entries renumbered 641–691; "+N more" for def:isotony (+1), def:local-observable (+2), def:isometric-covariance (+1), thrm:...-nonempty (+6), def:stabilizer-action (+1), lmm:stabilizer-action-laws (+2); inserted Definition 640 entry at head of §10.7 with one prose sentence; prose remapped; 52 items, Definitions 640–691; pages 331–343 and subsections. Done.
- sec10-8-general-covariance.md: entries 692–693; prose remapped; pages 343–345, subsection p. 343. Done.
- axioms.md: Definitions 641–643, 645–647, 693 remapped (curved table, design notes). Done.
- index.md, guide.md: 347 pages, 678 declarations (155 def), 1,231 Lean, items 13–693 (last item Definition 693), §10.7 row 18/30/4 = 52, §10.7 pp. 331–343, §10.8 pp. 343–345; index axioms bullet remapped (Definitions 641–646, 647, 693). Done.
- sec10-2-spectral.md: dropped "(+2 more)" on def:bounded-sesquilinear-form and "(+1 more)" on def:bump-function; the tex `\lean{}` of each lists one name. No numbers changed. Done.
- sec10-1, sec10-3–sec10-6: numbers and "+N more" match; no change. (sec10-5 lmm:isometry-preserves-classification shows its second name first by hand; count +4 correct.)
- Checks: 684 blueprint links, 0 bad anchors; check_temporal_wording.py OK; prose kind/number cross-check run.
