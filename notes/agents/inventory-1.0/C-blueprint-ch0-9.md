# Inventory C: blueprint Chapters 0–9, content, macros, print/web (backward-looking wording)

Read-only inventory, 2026-10-08. Scope: `blueprint/src/sections/sec0`–`sec9`, `blueprint/src/content.tex`, `blueprint/src/macros/*.tex`, `blueprint/src/print.tex`, `blueprint/src/web.tex`. Proposals are exact old → new wording for item-by-item approval.

| file:line | exact old text (full sentence) | category | action | exact new text |
|---|---|---|---|---|
| content.tex | (no hits; chapter/`\input` skeleton only) | — | none | — |
| macros/common.tex, macros/print.tex, macros/web.tex, print.tex, web.tex | (no hits; template/LaTeX comments only, no version strings, no blog wording) | — | none | — |
| sec0/abstract.tex | (no hits) | — | none | — |
| sec1/introduction.tex, sec1/original-haag-kastler-axioms.tex | (no hits) | — | none | — |
| sec2/* (4 sections + introduction) | (no hits; "a new topology" at alexandrov:6 means "another topology", and "had not confronted this earlier" at alexandrov:8 refers to the history of physics, not to this document) | — | none | — |
| sec3/introduction.tex:1 | Next let us consider Axiom 1 (Local Algebras) which states | positional-keep | keep | — (count: 1) |
| sec3/regions-of-measurement.tex:34,46,58 | "We chose regions …" (34); footnote "…which we none-the-less present later." (46); "So, all of this implies that our original choice … was the right one." (58) | positional-keep | keep | — (count: 3; "original choice" refers to the choice made at line 20 of the same section, not to an earlier version) |
| sec4/introduction.tex:1 | Now let us consider Axiom 2 (Isotony) which states | positional-keep | keep | — (count: 1) |
| sec4/gns-construction.tex:4,21 | "…the ``GNS construction'', which we now describe." (4); "(Again, without a unit …)" (21) | positional-keep | keep | — (count: 2) |
| sec4/isotony.tex:2,4,8,30 | "we can now examine isotony" (2); "As mentioned when we introduced the GNS construction" (4); "Consider again our main theme" (8); "as one will recall" (30) | positional-keep | keep | — (count: 4) |
| sec4/common-unit.tex:10 | footnote "Again, technically, …" | positional-keep | keep | — (count: 1) |
| sec5/introduction.tex:1 | Let us now consider Axiom 3 (Local Commutativity) which states | positional-keep | keep | — (count: 1) |
| sec5/completely-spacelike.tex | (no hits) | — | none | — |
| sec5/quasilocal-algebra.tex:2,30 | "The second point that requires clarification is a bit more subtle." (2); "…the quasilocal algebra $\mathfrak{U}$ of the next chapter contains every $\mathfrak{U}(\mathbf{B})$, …" (30) | positional-keep | keep | — (count: 2; the "formulation … is preferred because …" passage at 32–35 is already present-tense design rationale) |
| sec5/quasilocal-algebra.tex:37 | Clarification. | process (stray fragment) | delete | — (delete). Not temporal wording; it is a one-word leftover line after the section's last paragraph that reads as an editing note. Flagged for the user only; delete only if the user agrees. |
| sec6/introduction.tex, completion-of-the-set-theoretic-union.tex, set-theoretic-union.tex | (no hits apart from positional "Next let's consider Axiom 4" at introduction:1) | positional-keep | keep | — (count: 1) |
| sec6/all-observables-of-interest.tex:8,24 | "As we've seen, given a state $\omega$ we can use the GNS construction …" (8); "Furthermore, our slight modification of Axiom 2 (Isotony) implies that $\mathfrak{U}$ is unital, …" (24) | positional-keep | keep | — (count: 2; "our slight modification" refers to Section~\ref{sctn:common-unit}, not to a document revision) |
| sec7/introduction.tex:1,9 | "Next let us consider Axiom 5 (Lorentz Covariance)" (1); "This axiom is the most straightforward axiom of all that we have encountered." (9) | positional-keep | keep | — (count: 2) |
| sec7/inhomogeneous-lorentz-group.tex, action-of-…-identity-component.tex | (no hits; "This original formulation of Axiom 5" refers to the 1964 paper) | — | none | — |
| sec8/introduction.tex:1 | Finally we will examine Axiom 6 (Primitivity) | positional-keep | keep | — (count: 1) |
| sec8/faithful-representations.tex, faithful-and-irreducible-representations.tex | (no hits; "in later versions of the axioms presented by Haag" at f-a-i:17 is literature history, not document history) | — | none | — |
| sec9/introduction.tex:1 | As we've recounted the axioms of AQFT in Minkowski spacetime, we are now in a position to generalize this to curved spacetime, i.e. ``Lorentzian spacetime''. | positional-keep | keep | — (count: 1) |
| sec9/prologue.tex:12 | In particular, as we have seen previously, the required structure follows from the theorem (Theorem 2.69 from \href{https://doi.org/10.1007/978-3-319-91755-9}{Lee}) | blog (dangling reference: this theorem appears nowhere earlier in the blueprint, so "seen previously" can only point to an earlier blog post of the series) | rewrite | In particular, the required structure follows from the theorem (Theorem 2.69 from \href{https://doi.org/10.1007/978-3-319-91755-9}{Lee}) |
| sec9/prologue.tex:23,52 | "In the case of Minkowski spacetime we introduced sets of the form … showed that they are open … Furthermore, we showed that the Alexandrov topology is equivalent to the Euclidean topology …" (23, refers to Section~\ref{sctn:alexandrov-topology-on-minkowski-space}); "The previous theorem implies that for the more general case we are dealing with now on $M$, …" (52) | positional-keep | keep | — (count: 3) |
| sec9/axiom-1-local-algebras.tex:2 | With the prologue complete, we are now in a position to state the axioms of AQFT on Lorentzian spacetime. | positional-keep | keep | — (count: 1) |
| sec9/axiom-2-isotony.tex | (no hits) | — | none | — |
| sec9/axiom-3-local-commutativity.tex:2,19 | "So far the axioms have differed little from those of AQFT in Minkowski spacetime." (2); "… (Section~\ref{sctn:quasilocal-algebra}) …" (19) | positional-keep | keep | — (count: 2) |
| sec9/axiom-4-local-algebra.tex:18 | As shown in earlier in this blueprint, this axiom is essentially the statement that there exist ``observables'' that are not local observables, but such ``observables'' are ``experimentally indistinguishable'' from local observables and thus can be ignored. | positional-keep | keep (optional typo fix) | — (count: 1). Optional, not temporal: "As shown in earlier in this blueprint" has a stray "in"; a precise positional form would be "As shown in Section~\ref{sctn:all-observables-of-interest}, this axiom is essentially …". "changes slightly from its analog" / "the reason for the change" at line 2 compare the Minkowski and Lorentzian axioms, not document versions: no hit. |
| sec9/axiom-5-isometric-covariance.tex:2 | Now we present the final, and most interesting, axiom in the case of Lorentzian spacetimes. | positional-keep | keep | — (count: 1) |
| sec9/axiom-5-isometric-covariance.tex:18 | The Lean formalization works with the latter description: it intersects the identity component with the (explicitly orientation-preserving) subgroup, because the inclusion of the identity component into the orientation-preserving isometries relies on a Myers--Steenrod-type rigidity result not yet available in Mathlib. | version-dated | rewrite | The Lean formalization works with the latter description: it intersects the identity component with the (explicitly orientation-preserving) subgroup, because the inclusion of the identity component into the orientation-preserving isometries relies on a Myers--Steenrod-type rigidity result that Mathlib does not provide. |

## To CHANGELOG

- None required. No change notice, history or retraction was found in Chapters 0–9, so nothing removed here needs a CHANGELOG entry. (The two rewrites drop a dangling blog-series cross-reference and the word "yet"; neither records project history.)

## Totals

- Files read: 34 `.tex` under `sec0`–`sec9` (there is no `proposal/` directory under `blueprint/src/sections/`), plus `content.tex`, `macros/common.tex`, `macros/print.tex`, `macros/web.tex`, `print.tex`, `web.tex`: 40 files, 821 lines.
- Proposed rewrites: 2 (1 blog at sec9/prologue.tex:12; 1 version-dated at sec9/axiom-5-isometric-covariance.tex:18).
- Flagged, not temporal: 1 stray fragment "Clarification." (sec5/quasilocal-algebra.tex:37); 1 optional typo fix (sec9/axiom-4-local-algebra.tex:18).
- change-notice 0, history 0, process 0 (besides the stray fragment), retraction 0, rationale 0, explicit blog/post/series wording 0, Lean/Mathlib version strings 0.
- positional-keep: 30 (sec3: 4, sec4: 8, sec5: 3, sec6: 3, sec7: 2, sec8: 1, sec9: 9).
