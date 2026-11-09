# Tomita–Takesaki formalization progress

- 2026-11-09: Stage 1 part 1 — six antiunitary/closability nodes recorded in `Physicslib4/Operators/Modular/Antiunitary.lean` (def:antiunitary-operator → Mathlib `LinearIsometryEquiv`); four lemmas sorry'd, lmm:antiunitary-composition proved via `LinearIsometryEquiv.trans`; module builds.
- 2026-11-09: next: the remaining stage-1 nodes need new defs (C, von Neumann setting, separating vectors, S₀/F₀, S₀′, S); waiting for guard approval of Physicslib4/Operators/Modular/Tomita.lean.
- 2026-11-09: Stage 1 part 2 — all 19 remaining stage-1 nodes stated in `Physicslib4/Operators/Modular/Tomita.lean` (defs: referenceConjugation, IsVonNeumannSet, IsSeparatingVector, IsCyclicSeparatingVector, tomitaPreDomain, tomitaPre, linearizedTomitaPre, tomitaOperator; 11 sorry'd lemmas); diagnostics clean apart from sorry; module added to Physicslib4.lean.
- 2026-11-09: Review fixes — module docstring corrected (LinearPMap is semilinear; graph/toLinearPMap/closure/IsClosable/adjoint are linear-only); bridge lemmas for lmm:tomita-pre-operators-apply added (span_eq_of_isVonNeumannSet, tomitaPre_apply, linearizedTomitaPre_domain, linearizedTomitaPre_apply), sorry'd; module builds.
- 2026-11-09: stage-1 review REVISE: docstring fixed; lmm:tomita-pre-operators-apply added (blueprint, orchestrator) and formalized (4 lemmas). All 26 stage-1 nodes formalized.
