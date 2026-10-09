# Inventory of backward-looking wording (Stage 1 of the 1.0 present-tense plan)

Date: 2026-10-09. Plan: `../plan-release-1.0-present-tense-2026-10-08.md`. Read-only; no
project file was changed.

| File | Area | Rows | Notes |
|---|---|---|---|
| `A-blueprint-ch10-hk.md` | Ch. 10: HK axioms (Minkowski, curved), general covariance, GNS, introduction | 79 | 21 history, 18 process, 15 change-notice, 10 retraction, 9 version-dated, 3 rationale, 3 blog; 64 rows in `haag-kastler-axioms.tex`, mostly inside statements/proofs |
| `B-blueprint-ch10-spectral-spacetime.md` | Ch. 10: spectral (bounded, unbounded), Stone, spacetime | 27 | 21 in `spacetime.tex` (pullback / cross-metric part); **coverage gap:** `spectral-theorems.tex` and the second half of `unbounded-spectral-theorems.tex` were only grep-checked |
| `C-blueprint-ch0-9.md` | Ch. 0–9 (user's text) | 2 | 1 blog-origin clause (`sec9/prologue.tex:12`), 1 version-dated (`sec9/axiom-5-isometric-covariance.tex:18`); 30 positional references kept |
| `D-lean.md` | Lean docstrings and comments | 46 | 15 history, 14 process, 8 version-dated, 6 change-notice, 3 rationale; 28 files |
| `E-home-page-readme.md` | Home page and README | 60 | 25 change-notice, 9 history, 8 process, 8 version-dated, 6 rationale, 2 blog (config comments only) |

About 214 action items in total. Each file ends with a "To CHANGELOG" list and totals.

## Findings beyond wording (need a decision or a fix in a later stage)

1. **Stale or false statements in docs** (fix in Stages 3, 5 and 6, as present-tense corrections):
   - `haag-kastler-axioms.tex:1620` says `lmm:von-neumann-inter-general` "is not yet formalized",
     but the node is `\leanok`.
   - `HaagKastler/Net.lean:56` says the net bundles `def:quasilocal-completeness`, but no such field
     exists.
   - `HaagKastler/Net.lean:41` promises Axiom 6 fields later, but the blueprint abandons Axiom 6.
   - `GNS/Construction.lean` says `H : Type`, but the code uses `Type u`.
   - `LorentzCone.lean:33` says the cone sign "is not available", but `bilin_neg_of_inner_t_neg`
     proves it.
   - `HaagKastlerCurved/GeometricCovariance.lean:22` says the interface lacks `isBasisSet_smul`, but
     it is a field.
   - `GNS/PureStateExists.lean:29`: one of the two "missing instance" claims is now false at
     v4.34.1 (`IsScalarTower ℝ ℂ (A →L[ℂ] ℂ)` resolves).
   - README lines 61 and 63 ("what remains open", "items not yet linked to Lean proofs").
   - `home_page/guide.md:38` says the items run to "Definition 678". The last item is
     Definition 677, an orchestrator error from the Axiom 3 refresh.
   - `guide.md:32–34` repeats a sentence.
   - `sec10-6-haag-kastler.md:15` is missing the bicommutant `''`.
2. **Docs describing finished work as unfinished:** `QuasilocalIntertwiner` ("the remaining step
   will use"), `KMS.lean` ("left for later development"), the curved `Spacetime.lean` ("the eventual
   … construction will instantiate this interface"). Rewrite in the present tense.
3. **Formalizer instructions inside blueprint proofs** (`spacetime.tex:2001, 2015, 2067`: "Do not
   re-derive this", "Take the skeleton from the repository"). These are process text; the inventory
   proposes rewriting them as references.
4. **Version strings:**
   - None of the Lean/Mathlib version strings that D6 targets appear in `home_page/` or
     `README.md`. D6 needs two *additions* there (index.md "Contributing", README) plus one sentence
     in `sec10/introduction.tex`.
   - Mathlib source line numbers in the blueprint (`Completion.lean:75`, `ContMDiffMFDeriv.lean:241`,
     …) are version-dated. The proposal drops the line numbers and keeps the file paths.
5. **Decisions for the user:**
   - **Chapters 0–9 items:**
     - `sec9/prologue.tex:12`: delete "as we have seen previously," (the theorem is not earlier in
       the blueprint).
     - `sec9/axiom-5-isometric-covariance.tex:18`: "not yet available in Mathlib" → "that Mathlib
       does not provide".
     - `sec5/quasilocal-algebra.tex:37`: a stray one-word line, "Clarification.", which the
       inventory suggests deleting.
     - `sec9/axiom-4-local-algebra.tex:18`: "As shown in earlier in this blueprint" (stray "in").
   - **A possible missing `**Restriction:**` line** for `orientedIdentityComponent`
     (`Spacetime/IsometryCausality.lean:192`). That is a convention question, not wording.
   - **Highlights:** two "Recently completed" topics, the von Neumann density theorem and the inverse
     musical isomorphism, are not among the four D8 highlights, so they disappear from the landing
     page (their section pages keep them).

## Next

Stage 2 (CHANGELOG) can start from the "To CHANGELOG" lists. Before Stage 3, re-read
`spectral-theorems.tex` and the second half of `unbounded-spectral-theorems.tex` in full to close
the coverage gap in inventory B.
