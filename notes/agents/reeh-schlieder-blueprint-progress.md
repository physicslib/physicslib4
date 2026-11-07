# Reeh–Schlieder blueprint section: progress

Source: `proposal-reeh-schlieder-2026-11-05.md` (D1–D4 approved as recommended).

- 2026-11-07. Read the proposal and every existing node the draft cites. Findings:
  - All ten cited labels exist in `sections/sec10/`.
  - `lmm:bicommutant-single-vector` (haag-kastler-axioms.tex) already proves G5 for a unital
    *-homomorphism; `lmm:bicommutant-orbit-closure` is restated as its instance for
    π restricted to 𝔄_B and cites it, not `lmm:cyclic-subspace-reduces`.
  - Alexandrov basis sets include the empty set, so `lmm:diamond-small-translates` needs an
    empty case.
  - `IsVacuumState` is existential in its representation, so Corollary D is stated for the
    witnessing data, not for an arbitrary representative.
  - Statistical independence takes completely spacelike regions.
  - House notation: spectral measure μ^A, translates written L·B, β_L for the quasilocal lift.
- 2026-11-07. Steps 1-2: wrote `blueprint/src/sections/sec10/reeh-schlieder.tex` (draft plus
  fixes) and added its `\input` after general covariance in `content.tex`. `print.tex` and
  `web.tex` only `\input{content}`; nothing else to change. Split the theorem's proof into
  `lmm:reeh-schlieder-translated-products` and `lmm:reeh-schlieder-correlations-vanish`.
- 2026-11-07. Step 6: refresh parsed 702 declarations including all 20 new ones; validate reports only the 14 pre-existing `conv:` unknown-dependency errors.
- 2026-11-07. Step 7a: `leanblueprint pdf` succeeds; the new section has no undefined refs or overfull boxes (two underfull lines reworded away).
- 2026-11-07. Step 7b: `leanblueprint web` succeeds (warnings are the pre-existing includegraphics/PostScript ones); the section is rendered and its nodes appear in the dependency graph. `scripts/check_temporal_wording.py` passes. Done.
- 2026-11-07. Reviewer REVISE round. Rewrote `reeh-schlieder.tex` (my own file) with: nonempty
  diamonds in the additivity definitions and corollaries A–E; nonempty interval in
  `lmm:edge-vanishing`; the removability node `lmm:horizontal-line-removable`; the requested
  splits; the missing `\uses`; an "Analytic Preliminaries" subsection. Added
  `\uses{lmm:horizontal-line-removable}` to the proof of `thrm:strip-periodic-extension` in
  `haag-kastler-axioms.tex` (the only edit to an existing section).
- 2026-11-07. Set `lmm:horizontal-line-removable` leanDeclaration/leanFile and status proved (tool
  wrote its `\lean`/`\leanok`). Refresh: 721 declarations; validate: only the 14 pre-existing
  `conv:` errors. `leanblueprint pdf` and `web` succeed; final print.log has no undefined
  references and no overfull boxes; three cosmetic underfull lines in the section. Temporal check
  passes. Revision done.
- 2026-11-07. Second review: added `lmm:reeh-schlieder-monomial-orthogonal` (covers n = 0),
  `lmm:reflection-domain-open`, `lmm:schwarz-reflection-continuous`; spectral-support union step
  through the scalar measure μ_ψ; `lmm:diamond-translate` cites `def:inhomogeneous-lorentz-group`
  (which states (L, a)·x = Lx + a); optional items 5 and 6 applied.
- 2026-11-07. Second-review checks: refresh 724 declarations; validate only the 14 pre-existing `conv:` errors; pdf and web succeed (no undefined refs, no overfull boxes, one cosmetic underfull heading); temporal check passes; cited Mathlib names confirmed by grep. Done.
