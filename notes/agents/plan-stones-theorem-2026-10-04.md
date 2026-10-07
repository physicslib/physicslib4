# Plan: Stone's Theorem section and the §10.3 additions

Date: 2026-10-04. Toolchain: Lean / Mathlib v4.34.1. Branch: `numina/stones-theorem` off
`numina/aqft-in-lean`. Status: approved 2026-10-04; stage 1 started.

## What the user added (uncommitted, files possibly still open in Vim)

- `unbounded-spectral-theorems.tex`: item 4 of `prpstn:convergence-facts` (sequential
  characterisation of limits, linked to `Filter.tendsto_iff_seq_tendsto`);
  `lmm:self-adjoint-maximally-symmetric` (with proof); `def:hall-10.5` (functional calculus of an
  unbounded self-adjoint operator).
- New `stones-theorem.tex` (§10.4, 404 lines), inserted in `content.tex` before Spacetime:
  def:hall-10.11 (one-parameter unitary group), def:hall-10.13 (infinitesimal generator),
  lmm:generator-symmetry-identity, thrm:bochner-integral, lmm:smooth-approximate-identity,
  prpstn:calculus-facts (imported results), prpstn:hall-10.14 (exponentiating), lmm:hall-10.17,
  lmm:hall-10.18 (density of the generator's domain), thrm:hall-10.15 (Stone's theorem), Summary.
- Chapter 10 renumbering: Spacetime 10.4→10.5, Minkowski HK 10.5→10.6, curved 10.6→10.7,
  general covariance 10.7→10.8.

## Existing API to build on

- Unbounded operators are `H →ₗ.[ℂ] H` (`LinearPMap`); `IsSelfAdjoint`, `IsSymmetric`,
  closure, adjoint `T†`, essential self-adjointness criterion (`isEssentiallySelfAdjoint_iff_dense_range`).
- `pmapIntegral μ f` (integral of a measurable function against a PVM) with domain
  `integralDomain`; coincidence with the bounded integral; bounded integral multiplicative,
  conjugation, norm identity (§10.2).
- `existsUnique_spectralMeasure_unbounded hA : ∃! μ, pmapIntegral μ id = A` — no named
  spectral-measure definition yet.
- Unitary groups elsewhere in the project are `ℝ → (H ≃ₗᵢ[ℂ] H)` (`IsPositiveEnergy`,
  GNS covariance).

## Decisions (2026-10-04)

1. User edits finished.
2. Unitary groups as `ℝ → (H ≃ₗᵢ[ℂ] H)`.
3. Long proofs (10.14, 10.18, 10.15) may be decomposed into sub-lemma nodes.
4. Of the def:hall-10.5 remarks, formalise only the bounded-`f` remark (as its own lemma);
   the Summary bijection is not formalised.
5. Home pages renamed (sec10-4-spacetime → sec10-5-spacetime, etc.) with a new §10.4 page.
6. The IsPositiveEnergy follow-up waits until this work is complete.
7. (After review, 2026-10-04) Accepted: lmm:hall-10.18 rebuilt on Mathlib convolution
   (`HasCompactSupport.hasDerivAt_convolution_left`, `ContDiffBump.convolution_tendsto_right_of_continuous`);
   prpstn:hall-10.14 uses `tendsto_integral_filter_of_dominated_convergence` and
   `Real.norm_exp_I_mul_ofReal_sub_one_le`; prpstn:calculus-facts generalised (point 2 to normed
   spaces, point 3 simplified, points 4–5 dropped if unused).

## Stages

1. **Blueprint check and decomposition** (blueprint-reviewer, then writer with user consent).
   Validate; check the new Mathlib name; check `\uses`; split the long proofs
   (prpstn:hall-10.14 ~70 lines, lmm:hall-10.18, thrm:hall-10.15) into sub-lemmas, per the
   project's "small proofs" convention; add Mathlib `\lean{}` names to the three imported results.
2. **Renumbering** (mechanical): Lean docstrings (17 references in 16 files), home page
   (183 references; new §10.4 page; later section pages renamed). Blueprint `.tex` has no
   hard-coded numbers. Historical notes are left as they are.
3. **§10.3 additions**: verify convergence-facts item 4; prove
   `lmm:self-adjoint-maximally-symmetric` (short, from existing lemmas); define
   `spectralMeasure hA` (from the ∃!) and the functional calculus `f(A) := pmapIntegral
   (spectralMeasure hA) f`, with the bounded-`f` coincidence lemma.
4. **Stone section, definitions and easy lemmas**: one-parameter unitary group, strong
   continuity, infinitesimal generator (orchestrator writes defs); generator symmetry identity;
   lmm:hall-10.17; the imported results linked to Mathlib (calculus-facts points 3–4 need short
   local proofs).
5. **prpstn:hall-10.14** (exponentiating): unitarity, group law, strong continuity (DCT),
   derivative at 0 on Dom(A) (DCT), generator = A (maximal symmetry).
6. **lmm:hall-10.18** (Bochner averaging, mollifiers) — hardest analysis.
7. **thrm:hall-10.15** (Stone): symmetry, essential self-adjointness via the ODE argument,
   uniqueness via ‖w(t)‖² constant, A = A^cl, uniqueness of B.
8. **Clean-up**: blueprint statuses, PDF/web, home page, merge.
9. **Optional follow-up (user decision)**: remove the bounded-generator Restriction on
   `IsPositiveEnergy` (and VacuumState, QuasilocalKMS, StabilizerKMS) now that Stone's theorem
   exists — a definition change.

Each stage: build, lint, checkdecls, commit, progress entry here.

## Progress log

(empty)
- 2026-10-04, Stage 1 done: reviewer (REVISE ×2) and writer revisions applied. New labels:
  def:spectral-measure, lmm:functional-calculus-bounded (§10.3); in §10.4 the section now has 35
  nodes (see stones-theorem.tex), incl. lmm:generator-spec, def:exp-unitary-group, the 10.14 /
  10.17 / 10.18 / 10.15 decompositions, lmm:convolution-facts, lmm:linear-ode-scalar,
  lmm:orbit-difference-hasDerivAt, lmm:norm-const-of-symmetric-derivative. Writer dropped the
  user's (unused) B_f boundedness paragraph; lmm:strongly-continuous-iff-at-zero has no
  dependents. thrm:dominated-convergence-theorem \lean gained the filter-form DCT name.
- 2026-10-04, Stage 2 done: 17 Lean docstring section references shifted (10.4–10.7 → 10.5–10.8).
  Home page: sec10-4..7 pages renamed to sec10-5-spacetime, sec10-6-haag-kastler, sec10-7-curved,
  sec10-8-general-covariance; new sec10-4-stone.md (35 items); §10.3 page gained Lemma 187 and
  items 284–286; item numbers, pages, nav bars, table and counts regenerated from the rebuilt PDF
  (338 pages, 646 declarations, 606 formalised). Jekyll builds, no broken links. checkdecls flags six
  ContDiffBump names (Normed / Convolution modules not yet imported); stage 4 must import
  Mathlib.Analysis.Calculus.BumpFunction.{Normed,Convolution}.
- 2026-10-04, Stage 3 done: `eq_of_isSelfAdjoint_of_isSymmetric_of_le` (Basic.lean, 4 lines);
  new `Spectral/Unbounded/FunctionalCalculus.lean` with `spectralMeasure`,
  `pmapIntegral_spectralMeasure`, `eq_spectralMeasure_of_pmapIntegral`,
  `domain_eq_integralDomain_spectralMeasure`, `functionalCalculus` (+ `_domain`, `_id`) and
  `functionalCalculus_of_bddMeasurable`. All four §10.3 nodes proved/formalised; build, lint clean.
  Home page still shows them as not formalised (refresh in stage 8).
- 2026-10-04, Stage 4 done: new `Physicslib4/Spectral/Stone/Basic.lean` (orchestrator defs:
  `IsOneParameterUnitaryGroup` (pointwise map_zero/map_add), `IsStronglyContinuous`,
  `generatorQuotient`, `generatorDomain`, `generator`). Proved: strongly-continuous-iff-at-zero,
  unitary-group-inner-adjoint (inner + adjoint forms), generator-spec, generator-symmetry-identity,
  linear-ode-scalar, orbit-hasDerivAt, generator-commutes, hall-10.17 (strong continuity dropped,
  unused). Imported results linked and marked proved; BumpFunction imports added, so checkdecls
  is clean. Build, lint clean; no sorry.
- 2026-10-06, Stage 5 done: new `Physicslib4/Spectral/Stone/Exponential.lean`. Defs `expFun`,
  `expUnitary` (bounded integral via `Unitary.linearIsometryEquiv`; `functionalCalculus_expFun`
  links to f_t(A)). Proved exp-unitary (any PVM on ℝ), group law, strong continuity (DCT),
  functional-calculus-sub-bounded (as `(g - f)(A) = g(A) - f(A)` of LinearPMaps, via general
  private PVM helpers), quotient norm identity (for all t, review dropped `t ≠ 0`), derivative at 0
  (DCT; bound (3|x|)² via `Complex.norm_exp_sub_one_le` instead of the blueprint's
  `Real.norm_exp_I_mul_ofReal_sub_one_le`, to avoid an import), and prpstn:hall-10.14 as
  `generator (expUnitary hA) = A`. Three proofs are 40–56 lines; candidates for the stage 8 golf.
- 2026-10-06, Stage 6 done: new `Physicslib4/Spectral/Stone/Density.lean`. Def `average`
  (∫ f τ • U τ ψ). Proved averaging-translate (as `average_eq_convolution`, for every f and with
  no continuity hypotheses; they were unused), averaging-in-generator-domain (Mathlib convolution
  derivative), averaging-approximates (stated for any bumps with rOut → 0 along a filter), and
  lmm:hall-10.18 as `HasDenseDomain (generator U)`. Build, lint, checkdecls clean.
- 2026-10-06, Stage 7 done: new `Physicslib4/Spectral/Stone/Theorem.lean`. Proved all nine
  §10.4.5 nodes, ending in `stone` (thrm:hall-10.15): ∃ hA : IsSelfAdjoint (generator U),
  HasDenseDomain ∧ (∀ t, U t = expUnitary hA t) ∧ uniqueness among self-adjoint B. Axioms: propext,
  Classical.choice, Quot.sound only. Generalisations: orbit-inner-ode for any ε ∈ ℂ,
  bounded-exp-solution-zero for any real ε ≠ 0. norm-const lemma proved via the complex inner
  product ⟪w, w⟫ (terms cancel by symmetry) instead of Re/‖w‖². Remaining: stage 8 cleanup.
- 2026-10-07, Stage 8: golfed Exponential.lean (54/41/39-line proofs → 9/6/6, eight private
  helpers; derivative bound now the blueprint's `Real.norm_exp_I_mul_ofReal_sub_one_le`).
  Home page refreshed: 645 of 646 formalised (only Lemma 350 open), §10.3/§10.4 entries carry
  their Lean names, Stone "recently completed", guide Lean-location row. Jekyll builds, no broken
  links. Merged into numina/aqft-in-lean (not pushed). Stage 9 (IsPositiveEnergy) awaits a decision.
