# Plan: a Levi-Civita connection for `Spacetime` and a real `IsGeodesic`

Date: 2026-09-29. Toolchain: Lean / Mathlib v4.34.1 (commit `3ff1a59`).
Status: plan only. Nothing below is implemented.

## Goal

Replace the placeholder `IsGeodesic := True` (`Physicslib4/Spacetime/Causality.lean`,
with its `**Restriction:**` line) by "γ is a geodesic of the Levi-Civita connection of
the spacetime metric", built on Mathlib's covariant-derivative API rather than on
hand-written chart Christoffel symbols (the alternative in
`notes/agents/scout/isgeodesic-christoffel-2026-09-29.md`). Then retire the 57
formalization notes in `blueprint/src/sections/sec10/spacetime.tex`.

## What Mathlib v4.34.1 provides

Folder `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/`:

| File | Content | Usable for a Lorentzian metric? |
|---|---|---|
| `Basic.lean` | `IsCovariantDerivativeOn`, bundled `CovariantDerivative I F V`, `ContMDiffCovariantDerivative`, `difference`, `addOneForm` | Yes, as is (any field, any bundle, no metric) |
| `Torsion.lean` | `CovariantDerivative.torsion`, `torsion_eq_zero_iff` | Yes, as is |
| `Metric.lean` | `derivMetricTensorAux/derivMetricTensor`, `IsMetricCompatible` | Pattern only: stated with `inner`/`innerSL` and `[IsContMDiffRiemannianBundle I 1 F V]` |
| `LeviCivita.lean` | `IsLeviCivitaConnection` (structure), `.uniqueness`, Koszul `leviCivitaAuxInner`, `leviCivitaAux`, `leviCivitaConnection`, `isLeviCivitaConnection_leviCivitaConnection` | Pattern only: uses `InnerProductSpace.toDual` (line ~313) and `injective_inner_*` lemmas |

Mathlib has no covariant derivative along a curve, no parallel transport, no geodesics.

Our side (`Physicslib4/Spacetime/Basic.lean`, `structure Spacetime`): the metric is
`val : ∀ x, TangentSpace model x →L[ℝ] TangentSpace model x →L[ℝ] ℝ`, with fields
`symm`, `nondegenerate`, `lorentzian`, `tangent_findim`, and a `contMDiff` field stating
smoothness as a bundle section, deliberately the same shape as
`Bundle.ContMDiffRiemannianMetric.contMDiff`. So Mathlib's constructions transfer once
`innerSL ℝ v` is replaced by `M.val x v` and `InnerProductSpace.toDual` by the
musical isomorphism obtained from `nondegenerate` + finite dimension.

## Design decisions for the user (settle before Stage 2)

1. **Generality.** DECIDED (2026-09-29): build a small general pseudo-Riemannian layer
   and instantiate it by `Spacetime`. Original note: build the metric-compatibility / Levi-Civita layer for a general
   smooth nondegenerate symmetric bilinear bundle metric (reusable, closer to a future
   Mathlib pseudo-Riemannian API), or specialise directly to `Spacetime`. Recommendation:
   a small general layer (`PseudoRiemannian`-style section `g` + `symm` + `nondegenerate`)
   instantiated by `Spacetime`, in a new folder `Physicslib4/Geometry/`.
2. **Derivative along a curve** (Mathlib has none). DECIDED (2026-09-29): chart-free
   extension definition. `μ` is a geodesic iff for every `s` in the parameter space and
   every smooth vector field `X` with `X (μ t) = μ' t` for `t` near `s` (within the
   parameter space), `(∇_X X)(μ s) = 0`. Required lemmas: (i) independence: `∇_X Y` at
   `μ s` in direction `μ' s` depends only on `Y` along `μ` near `s` (local frames inside
   the proof only); (ii) existence of such extensions near each `s` (smooth paths have
   nonvanishing velocity, hence are local injective immersions), which rules out
   vacuity. No chart appears in any definition. Original options:
   - (a) Pullback connection: define `D_t V` for vector fields `V` along γ via
     `∇` applied to a local extension, prove independence of the extension
     (needs a tensoriality-in-direction plus "depends only on values along γ" lemma).
   - (b) Local frame: in the chart trivialization at γ(t), `D_t V = V' + A(γ')(V)`, where
     `A` is the connection one-form of `∇` in that trivialization (Mathlib's
     `difference` of `∇` and the trivial connection of the trivialization). Chart
     independence is then a lemma, not part of the definition.
   Recommendation: (b) for the definition (concrete, reuses `difference`), prove the
   extension characterisation (a) as a theorem later if needed.
3. **Which curves.** DECIDED (2026-09-29): affinely parametrised geodesics on paths
   (`IsGeodesic μ` means `μ` itself satisfies the geodesic equation); the curve-level
   notion stays "some representative path is a geodesic", as in the trip definitions.
   Original note: Geodesic condition for `M.SmoothPath` on its parameter space
   (closed interval, possibly with endpoints): use within-derivatives on the parameter
   space, matching the existing `SmoothPath.tangent` API. Affinely parametrised (the
   usual definition) vs. pregeodesic up to reparametrisation: trips use curves up to
   reparametrisation (`SmoothCurve`), so decide whether `IsGeodesic` on a path means
   "affinely parametrised geodesic" (then trips quantify over a representative, as now)
   or "pregeodesic". Recommendation: affinely parametrised on the path; the curve-level
   notion is "some representative is a geodesic", as the trip definitions already do.
4. **Scope of the blueprint.** These are new chapter-10 definitions (§10.4), not
   motivation. The blueprint text is the spec, so it must be written and reviewed first.

## Stages

Each stage ends with `lake build`, `lake lint`, `leanblueprint checkdecls`, a commit,
and (for stages touching statements) a formalizer-reviewer or lean-auditor pass.

### Stage 1: blueprint (fuse:blueprint + fuse:blueprint-reviewer)

Add to `spacetime.tex`, after the metric / time-orientation definitions and before
`def:trip`:
- `def:metric-compatible-connection`: a covariant derivative ∇ on TM is compatible with
  g if X(g(σ,τ)) = g(∇_Xσ,τ) + g(σ,∇_Xτ).
- `def:levi-civita-connection`: torsion-free and metric-compatible.
- `lmm:koszul-formula`: 2g(∇_XY,Z) = X g(Y,Z) + Y g(X,Z) − Z g(X,Y)
  + g([X,Y],Z) − g([X,Z],Y) − g([Y,Z],X).
- `lmm:musical-isomorphism`: nondegeneracy gives an isomorphism T_xM ≅ T_x*M
  (finite dimension).
- `thrm:levi-civita-exists-unique`: every spacetime has a unique Levi-Civita connection.
- `lmm:covariant-derivative-along-curve-local`: for vector fields X, Y, Y' with
  Y = Y' along a smooth path μ near s and X(μ s) = μ'(s), (∇_X Y)(μ s) = (∇_X Y')(μ s).
- `lmm:velocity-extends`: the velocity of a smooth path extends near each parameter to a
  smooth vector field.
- `def:geodesic`: extension definition of decision 2 (affinely parametrised).
- `lmm:isometry-preserves-levi-civita`: an isometry φ intertwines ∇ (by uniqueness).
- `lmm:isometry-preserves-geodesics`: φ ∘ γ is a geodesic iff γ is.
- `lmm:minkowski-levi-civita-flat` and `lmm:minkowski-lines-are-geodesics`: in standard
  Minkowski space ∇ is the trivial connection, and affine lines are geodesics.
Update `def:trip` / `def:causal-trip` to cite `def:geodesic`. Mark the 57 notes for
removal only after Stage 5.
Deliverable: reviewed blueprint; `blueprint_validate` clean apart from the known `conv:`
errors.

### Stage 2: definitions and sorry'd statements (fuse:formalizer + reviewer)

New file(s), e.g. `Physicslib4/Geometry/PseudoRiemannian/Musical.lean`,
`.../MetricCompatible.lean`, `.../LeviCivita.lean`:
- `musical` : `TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ)` from `val x`,
  `nondegenerate`, `tangent_findim` (via `LinearMap.BilinForm`/`ContinuousLinearMap`
  and `LinearEquiv.ofInjectiveEndo`-style finite-dimensional arguments).
- `derivMetricTensor` / `IsMetricCompatible` mirroring `Metric.lean` with `val` in
  place of `innerSL`.
- `IsLeviCivitaConnection` (torsion `= 0` via Mathlib `torsion`, plus
  `IsMetricCompatible`).
- Statements (sorry): `IsLeviCivitaConnection.uniqueness`, `exists_leviCivita`,
  `leviCivita : CovariantDerivative ...` (as `Classical.choose` of existence, or direct
  construction once Stage 3 lands).
This stage is cheap (definitions only), about 150–250 lines.

### Stage 3: existence and uniqueness (fuse:prover, parallel where independent)

Port `LeviCivita.lean` (414 lines) with these substitutions:
- `injective_inner_mdifferentiableAt_vectorField` etc. → injectivity of
  `v ↦ val x v` from `nondegenerate`.
- `leviCivitaAuxInner` (the Koszul right-hand side) → same, with `val`.
- `InnerProductSpace.toDual.symm` → `musical.symm`.
- smoothness of `musical.symm` in `x` from the `contMDiff` field (the inverse of a
  smooth family of invertible maps is smooth: `ContMDiff` of `Ring.inverse`/
  `ContinuousLinearEquiv` inverse in the hom-bundle trivialization). This is the one
  genuinely new analytic lemma; budget it separately.
Proof decomposition (each ≤ ~10 tactic lines, per project style): tensoriality of the
Koszul expression in each slot; Leibniz rule; additivity; torsion-free; metric
compatibility; uniqueness (Koszul determines g(∇_XY, ·), then nondegeneracy).
Expected size: 400–700 lines. Largest risk: the smooth inverse of the metric.

### Stage 4: derivative along curves and the new `IsGeodesic` (definition change)

- Define `IsGeodesic M μ` by the chart-free extension condition of decision 2, with the
  independence and existence lemmas proved first (the existence lemma is what makes the
  definition non-vacuous).
- Replace the placeholder in `Causality.lean`; remove its `**Restriction:**` line.
- Proofs that currently get the geodesic conjunct for free and must be repaired
  (from the scout memo §4; re-grep `IsGeodesic`, `IsTripSegment`,
  `IsCausalTripSegment` before starting):
  `Spacetime/IsometryCausality.lean` (isometry pushforward of trips),
  `Spacetime/CrossMetricIsometry.lean`, `Spacetime/DiffeoPath.lean`,
  `Spacetime/LorentzCausality.lean` (Lorentz images of trips),
  `Spacetime/Minkowski.lean` (straight-line trips, the trip-tangent lemma).
- New supporting lemmas:
  - Minkowski: the Levi-Civita connection of the constant metric in the identity chart
    is the trivial connection (by uniqueness: the trivial connection is torsion-free and
    compatible); affine lines have zero covariant acceleration. Moderate.
  - Isometries: φ*∇ is Levi-Civita for φ*g = g, so equals ∇ (uniqueness); hence
    `covDerivAlong` commutes with φ and geodesics map to geodesics. Moderate given
    Stage 3; this is where the connection approach beats hand-written Christoffel
    symbols.
  - Cross-metric isometries (`CrossMetricIsometry.lean`): same argument between two
    metrics; check the existing hypotheses supply smoothness of the map.
Expected size: 300–600 lines, depending on decision 2.

### Stage 5: clean-up

- Remove the 57 "Formalization note" paragraphs in `spacetime.tex` and the remark after
  `def:causal-trip`; update docstrings of `IsTripSegment`, `IsCausalTripSegment`.
- Re-run `leanblueprint pdf/web`, `checkdecls`, refresh `home_page/index.md`.
- Full chapter-10 §10.4 review (lean-auditor) against the new blueprint text.

## Risks and mitigations

- **Smooth inverse metric** (Stage 3): if the hom-bundle smoothness of `musical.symm`
  is hard, first prove existence pointwise and smoothness in charts, or add
  smoothness of the inverse as a derived lemma via the chart matrix inverse.
- **Mathlib API churn**: the covariant-derivative files are new (2025–26) and may change
  in later Mathlib versions. Keep the port close to Mathlib's naming to ease rebasing,
  and consider upstreaming the pseudo-Riemannian generalisation.
- **Boundary behaviour**: parameter spaces are closed intervals; use within-derivatives
  on `μ.parameterSpace` consistently (`Path.uniqueDiffOn_parameterSpace` exists).
- **Downstream breakage in Stage 4**: do Stage 4 on its own branch; the build stays
  green through Stages 1–3 because nothing uses the new definitions yet.
- **Guard hook**: new `def`s and changes to `IsGeodesic` are protected; the orchestrator
  (or the user via `lean_guard.py approve`) must apply or approve those edits.

## Suggested session breakdown

1. Stage 1 + design decisions 1–3 (one session).
2. Stage 2 (short) and the start of Stage 3.
3. Finish Stage 3 (possibly two sessions; the smooth inverse lemma first).
4. Stage 4 on a branch.
5. Stage 5 and review.

## Progress log

- 2026-09-29, Stage 1: blueprint nodes drafted in `spacetime.tex` (fuse:blueprint) and
  reviewed (fuse:blueprint-reviewer: REVISE, then PASS). Not committed.
  - Refinement of decision 2 adopted on review: the geodesic condition is imposed only at
    interior parameters of Σ (non-vacuous, since the interior of a non-degenerate
    interval is non-empty). This removes the need for a Borel-lemma extension of paths
    past their endpoints (not in Mathlib).
  - Open decision for the user: the general layer assumes a boundaryless model; the Lean
    `Spacetime` does not currently require `model.Boundaryless`. Either add that field /
    hypothesis or keep "a spacetime is pseudo-Riemannian" informal.
  - Reviewer note: `lmm:musical-inverse-smooth` is not needed for existence, uniqueness or
    geodesics (Mathlib's `IsCovariantDerivativeOn` imposes no smoothness), so the plan's
    "largest risk" is off the critical path. Two claims in `def:geodesic` (endpoint
    continuity, affine reparametrisations) are informal remarks, not targets.
- 2026-09-30, Stage 2: `Physicslib4/Geometry/PseudoRiemannian/Basic.lean`
  (`PseudoRiemannianMetric`, `bijective_val` [sorry], `Spacetime.toPseudoRiemannianMetric`)
  and `.../LeviCivita.lean` (`IsMetricCompatibleWith`, `IsLeviCivitaFor`, `koszul`,
  `uniqueness`, `exists_isLeviCivitaFor` [all sorry], `leviCivita` via `choose`).
  Spacetime gained `boundaryless : model.Boundaryless` (commit `334c309`); the reviewer
  notes the layer itself does not need it yet (keep it out of these statements).
  Formalizer-reviewer: PASS. Blueprint statuses recorded. Not yet formalized: the Koszul
  construction helpers (`lmm:koszul-expression-tensorial`, `...-is-covariant-derivative`,
  `...-is-levi-civita`) and `lmm:musical-inverse-smooth` (off the critical path); these
  belong with the Stage 3 proofs.
- 2026-09-30, Stage 2 committed as `b581f07`. Stage 3 started: `bijective_val`,
  `IsLeviCivitaFor.koszul` and `IsLeviCivitaFor.uniqueness` proved (standard axioms only;
  uniqueness via Mathlib's `VectorBundle.injective_eval_mdifferentiableAt_sec`). Remaining
  in Stage 3: `exists_isLeviCivitaFor` (port `leviCivitaAuxInner`/`leviCivitaAux`/
  `isCovariantDerivativeOn_leviCivitaAux` and the torsion/compatibility checks from
  Mathlib's LeviCivita.lean, with `(g.val x)`'s inverse from `bijective_val` in place of
  `InnerProductSpace.toDual.symm`). Not committed.
- 2026-09-30, Stage 3 complete (commit of the first three proofs: `7947eeb`). Existence
  proved via `koszulAux`, `flatEquiv`, `leviCivitaAux`, `koszulConnection` (defs written by
  the orchestrator; guard blocks agent defs), with helpers `mdifferentiableAt_val_apply`,
  `mfderiv_apply_eq_mvfderiv`, `eq_of_forall_val_apply_eq`. No sorry in the layer; standard
  axioms only. `thrm:levi-civita-exists-unique` proved. Not yet committed. Next: Stage 4.
- 2026-09-30, Stage 3 committed as `9068056`. Stage 4 started on branch `numina/geodesics`:
  new `Physicslib4/Spacetime/AlongPath.lean` with the five along-the-curve lemmas, all
  proved (standard axioms): `SmoothPath.mfderiv_apply_tangent_eq_zero`,
  `SmoothPath.covDeriv_eq_of_eventuallyEq` (local frame from `trivializationAt` +
  `Basis.ofVectorSpace`), `exists_contMDiff_vectorField_eventuallyEq` (Mathlib
  `ContMDiffOn.smul_section_of_tsupport`), `SmoothPath.exists_localLeftInverse` (1-D inverse
  function theorem), `SmoothPath.exists_vectorField_eq_tangent`. Not yet committed.
  Next: define the new `IsGeodesic` and repair the trip proofs.
- 2026-09-30, along-path lemmas committed as `ac2fa2e`. New `IsGeodesic` defined in
  `Causality.lean` (chart-free, interior parameters, `M.toPseudoRiemannianMetric.leviCivita`);
  placeholder and its Restriction line removed. Not committed: the build breaks at exactly
  five places that discharged the geodesic conjunct with `trivial`:
  1. `Minkowski.lean:1381` (straight segment trip) — needs `lmm:minkowski-lines-are-geodesics`
     (via `lmm:minkowski-levi-civita-flat`).
  2. `IsometryCausality.lean:230` `segmentPrecedes_pushforward` — needs
     `lmm:isometry-preserves-geodesics`.
  3. `CrossMetricIsometry.lean:327` `CrossIsometry.segmentPrecedes` — needs the cross-metric
     version (blueprint currently marks it deferred).
  4–5. `LorentzCausality.lean:309` `causalSegmentPrecedes_smul` and `:395` (timelike
     version) — needs Lorentz transformations (affine isometries of Minkowski) to preserve
     geodesics; via the isometry lemma plus a bridge from the Lorentz action to `Isometry`,
     or directly from flatness (∇ = directional derivative, affine maps preserve it).
  Every other module failed only because it imports one of these files.
- 2026-09-30, breakages 1, 2, 4, 5 repaired (not committed): new
  `Physicslib4/Geometry/PseudoRiemannian/Flat.lean` (`flatConnection`, Levi-Civita for a
  constant metric, `leviCivita_apply_eq_fderiv`); in `Minkowski.lean`
  `standardMinkowski_leviCivita_apply`, `standardMinkowski_isGeodesic_iff` (geodesic ⟺ velocity
  has derivative 0 at interior parameters), `standardMinkowskiLineSegmentPath_isGeodesic`; in
  `LorentzCausality.lean` `lorentzPath_isGeodesic`; in `IsometryCausality.lean`
  `Isometry.pushforwardPath_isGeodesic` via `mfderiv_leviCivita_mpullback` (naturality proved
  term-by-term from the Koszul formula, not via a pullback connection, so
  `lmm:diffeo-pullback-connection`, `lmm:diffeo-pullback-torsion-free`,
  `lmm:isometry-pullback-compatible` remain unformalized — the blueprint proof route differs).
  Standard axioms only. Remaining: breakage 3 (`CrossMetricIsometry.lean:327`), which blocks
  `lake lint` and the modules importing that file.
- 2026-09-30, breakage 3 repaired: `CrossIsometry.pushforwardPath_isGeodesic` with cross-metric
  ports of the naturality helpers (incl. `CrossIsometry.mfderiv_leviCivita_mpullback`). Build,
  lint, checkdecls green; only the deliberate StrongDensity sorry remains. Stage 4 committed on
  `numina/geodesics`. Remaining: Stage 5 (retire the 57 formalization notes, the remark after
  def:causal-trip, and update the blueprint proof route of the isometry lemmas; refresh home page).
- 2026-09-30, Stage 5 started (not committed): removed the 57 formalization notes and the
  placeholder remark after def:causal-trip; updated stale placeholder docstrings in
  Causality.lean and Minkowski.lean; blueprint isometry section rewritten to the
  Koszul-invariance route (new lmm:isometry-pullback-metric, -metric-derivative,
  -lie-bracket; old pullback-connection nodes deleted), all linked and proved. Remaining:
  rebuild blueprint PDF/web, refresh home_page/index.md (still describes the placeholder),
  merge numina/geodesics into numina/aqft-in-lean. Only unformalized new node:
  lmm:musical-inverse-smooth (unused).
