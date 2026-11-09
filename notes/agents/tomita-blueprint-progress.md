# Tomita blueprint progress

- 2026-11-08: created `blueprint/src/sections/sec10/tomita-takesaki.tex` with the introduction and subsection "The Tomita Operator" (stage 1, 20 nodes).
- 2026-11-08: added subsection "The Modular Operator and the Modular Conjugation" (stage 2: von Neumann, functional-calculus composition and core, |T|, polar decomposition, Delta, J).
- 2026-11-09: checks pass: refresh (788 entries), validate (only the 14 known `conv:` errors), temporal-wording check OK, `leanblueprint pdf` (no undefined references) and `leanblueprint web` succeed.
- 2026-11-09: review pass 1: REVISE (no false statements; fix separability, add unbounded inverse nodes, lmm:fc-core closedness, range-criterion node for von Neumann, split 12 proofs). Memo: review-tomita-blueprint-2026-11-09.md. Revision pending.
- 2026-11-09: review fixes: finding 1 (separability dropped, IsClosed.completeSpace_coe), optional findings 7, 8, 10 (Sigma for the sigma-algebra), and the split of lmm:antiunitary-composition.
- 2026-11-09: findings 3 (lmm:fc-core restricted to real f) and 4 (lmm:self-adjoint-of-range-eq-top), optional finding 6 (withDensity form, thrm:hall-10.4 edges), and splits of the von Neumann theorem, lmm:fc-dominated-convergence, lmm:pushforward-pvm, lmm:closure-transfer-common-core, lmm:absolute-value-norm-on-core, lmm:polar-isometry.
- 2026-11-09: finding 2 (def:inverse-of-operator, lmm:inverse-of-product-with-bijection, lmm:tomita-inverse-is-self) and splits of lmm:antiunitary-conjugate-pvm, lmm:inverse-functional-calculus, crllr:inverse-square-root, lmm:tomita-inverse-polar, crllr:modular-conjugation-inverts.
- 2026-11-09: review fixes checked: refresh (811 entries), validate (only the 14 known `conv:` errors), wording check OK, `leanblueprint pdf` (no undefined references) and `leanblueprint web` succeed.
- 2026-11-09: revision applied (87 nodes, 897 lines); review pass 2: PASS. Optional items in the review memo. Open design decisions: T*T def vs graph hypothesis, antiunitaries as H ≃ₗᵢ⋆[ℂ] H, splitting the file.
- 2026-11-09: final round A: antiunitaries as LinearIsometryEquiv (starRingEnd C), new lmm:conjugate-linear-isometry-inner, pointwise C(Cx) = x and J(Jx) = x; new def:adjoint-product-operator (T*T as a Lean definition) cited by von Neumann, |T| and Delta.
- 2026-11-09: final round B: square-root proof via lintegral_eq_zero_iff, splits (lmm:square-root-positive, lmm:antiunitary-conjugate-spectral-measure, lmm:antiunitary-conjugate-positive, lmm:fc-real-closed), integral_map cited, S^{-1} = S kept in lmm:tomita-inverse-is-self.
- 2026-11-09: final round checked: refresh (817 entries), validate (only the 14 known `conv:` errors), wording check OK, pdf (no undefined references) and web succeed.
