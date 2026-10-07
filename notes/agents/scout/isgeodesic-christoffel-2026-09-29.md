# Scout memo: giving `IsGeodesic` real content via chart Christoffel symbols

Status: COMPLETE (read-only research; no `.lean`/`.tex` edited)

## Target

Can `Physicslib4.Spacetime.IsGeodesic` (placeholder `:= True`,
`Physicslib4/Spacetime/Causality.lean:66-82`, with a `**Restriction:**`
docstring) be given real content via chart Christoffel symbols of the
Lorentzian metric, **without new dependencies**? Context: `qinz1yang/differential-geometry`
defines geodesics only for positive-definite `SmoothRiemannianMetric` via
chart Christoffel contractions and pins Lean v4.33.1 (this repo is v4.32.0),
so it cannot be imported; it is a model only.

**Answer, short version:** Yes, chart-local Christoffel symbols and a chart
ODE definition are buildable from primitives already in Mathlib (matrix
inverse of a nondegenerate Gram matrix, `extChartAt`, `fderivWithin`,
`derivWithin`). It is a genuine, non-trivial `def` (blocked by policy for
agents; requires user approval), and it creates real downstream proof
obligations — see §4 — most of which are currently *vacuous* consequences of
`IsGeodesic = True` and would become real theorems needing an actual
differential-geometric argument (isometries preserve Christoffel symbols /
are affine). This is not a small refactor.

## 1. Representation of the metric (`Physicslib4/Spacetime/Basic.lean`)

`Spacetime` (`Physicslib4/Spacetime/Basic.lean:117-176`) bundles:
- `Carrier : Type*` with `TopologicalSpace`, `T2Space`, `ConnectedSpace`,
  `ChartedSpace SpacetimeModel Carrier` where
  `SpacetimeModel := EuclideanSpace ℝ (Fin 4)` (`Basic.lean:69`);
- `model : ModelWithCorners ℝ SpacetimeModel SpacetimeModel` (typically
  `modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))`, i.e. **boundaryless**,
  so `extChartAt` targets all of `EuclideanSpace ℝ (Fin 4)` with no corner
  cutting — good news for the ODE definition below);
- `isManifold : IsManifold model ∞ Carrier`;
- `val : ∀ x, TangentSpace model x →L[ℝ] TangentSpace model x →L[ℝ] ℝ`, the
  metric as a family of continuous bilinear forms on tangent spaces (not
  chart components — see below);
- `symm`, `nondegenerate` (`∀ w, val x v w = 0 → v = 0`, i.e. the
  linear-algebra notion, not `Matrix.Nondegenerate` directly), `lorentzian`
  (`LorentzianAt`, existence of a basis with Gram matrix `diag(-1,1,1,1)`,
  `Basic.lean:76-88`);
- `contMDiff`: smoothness of `g` as a **bundle section** of continuous
  bilinear forms on the tangent bundle (the same shape as
  `Bundle.ContMDiffRiemannianMetric.contMDiff`), *not* stated chart-by-chart.

**Chart-local components `g_ij(x)`.** Not directly a field; must be built:
`TangentSpace model x` for a boundaryless model with `E = H` is (definitionally,
via `Mathlib.Geometry.Manifold.VectorBundle.Tangent`) the fibre of the tangent
bundle, trivialized over `(chartAt H x).source` by
`trivializationAt E (TangentSpace I) x` (`.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean:206-234`),
with the standard-basis coordinate vectors of `EuclideanSpace ℝ (Fin 4)`
pulled back through this trivialization giving the chart frame `∂_i|_x`. Then
`g_ij(x) := val x (frame i) (frame j)`, a `Fin 4 → Fin 4 → ℝ`-valued function
of `x` in the chart. `ContMDiff.clm_bundle_apply₂`
(`.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Hom.lean:445`)
is exactly the lemma the `Basic.lean` docstring cites to get smoothness of
`x ↦ g x (V x) (W x)` for smooth vector fields `V, W`; instantiating `V, W`
with the (smooth, since chart-constant-coefficient) frame fields gives
`ContMDiff` of each `g_ij` in the chart — this is the route to differentiate
the `g_ij` (needed for `∂_i g_jl` in Christoffel symbols).

**Inverse metric `g^{ij}`.** Not a field, but easy to define pointwise:
`nondegenerate` + `symm` give a symmetric bilinear form on a 4-dimensional
space whose Gram matrix `M i j := val x (frame i) (frame j)` is
`Matrix.Nondegenerate` (via `Matrix.Nondegenerate.toMatrix'`,
`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/BilinearForm.lean:490`,
after transporting `val x` along `frame` to a form on `Fin 4 → ℝ`), hence
`Matrix.nondegenerate_iff_det_ne_zero`
(`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Nondegenerate.lean:159`,
proved later in the same hierarchy) gives `M.det ≠ 0`, hence `M⁻¹` via
`Matrix.nonsing_inv` (`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`)
is an honest two-sided inverse. So `g^{kl}(x) := M⁻¹ k l` is definable, no
new axioms, no new imports beyond what `Basic.lean`/`LorentzianAt` already
pull in (`Mathlib.LinearAlgebra.Matrix.BilinearForm` is already imported).

## 2. Proposed definition

```
Γ (M : Spacetime) (x : M.Carrier) (hx : x ∈ (chartAt _ x).source) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun k i j => (1/2) * ∑ l,
    ginv M x k l * (∂_i (g M · j l) x + ∂_j (g M · i l) x - ∂_l (g M · i j) x)
```
where `g M · j l : SpacetimeModel → ℝ` is the chart-component function of
§1 read in `extChartAt M.model x`-coordinates, and `∂_i F x` is the partial
derivative in direction `i`, i.e. `fderiv ℝ F (extChartAt M.model x x') (EuclideanSpace.single i 1)`
composed appropriately, or (cleaner) `derivWithin (fun t => F (update y i t)) univ (y i)`—
in practice this is best phrased via `fderivWithin ℝ (g-component) (extChartAt...).target`
and evaluated on the standard basis vectors, since `extChartAt` targets are
open subsets of `EuclideanSpace ℝ (Fin 4)` (`.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:454-477`
gives `extChartAt_source`, `extChartAt_target`).

Then, for `μ : M.SmoothPath` with chart curve
`c := (extChartAt M.model (μ.toFun s₀)) ∘ μ.toFun` (well-defined near `s₀`
while `μ.toFun s ∈ (chartAt _ (μ.toFun s₀)).source`):

```
IsGeodesic (μ : M.SmoothPath) : Prop :=
  ∀ s ∈ μ.parameterSpace, ∀ k : Fin 4,
    derivWithin (fun t => derivWithin (fun u => (c u) k) μ.parameterSpace t)
        μ.parameterSpace s
    + ∑ i, ∑ j, Γ M (μ.toFun s) k i j
        * derivWithin (fun t => (c t) i) μ.parameterSpace s
        * derivWithin (fun t => (c t) j) μ.parameterSpace s
    = 0
```
i.e. `c'' + Γ(c)(c',c') = 0` component-wise, `derivWithin`/`derivWithin`
composed for the second derivative (`Mathlib.Analysis.Calculus.Deriv.Basic`,
already imported in `Curves.lean`; `UniqueDiffOn` needed for well-behaved
`derivWithin` is exactly `Path.uniqueDiffOn_parameterSpace`, already proved
in `Curves.lean:118-133`, so the analytic prerequisite is in hand).

**"Every chart" vs "the preferred chart".** The natural definition quantifies
`∀` chart containing `μ.toFun s` (or equivalently, fixes `chartAt _ (μ.toFun s)`,
Mathlib's canonical choice, since `Spacetime` does not distinguish an atlas).
Because `Fin 4 → Fin 4 → Fin 4 → ℝ` Christoffel symbols are **not** tensorial
— they transform inhomogeneously under a chart change (the standard
"Γ' = J⁻¹ Γ (J,J) + J⁻¹ J''" transformation law) — the geodesic *equation*
`c'' + Γ(c',c') = 0` is chart-independent (a standard fact) but this needs
a **chart-change lemma** to prove: if `c₁ = φ₁ ∘ μ` and `c₂ = φ₂ ∘ μ` are the
representations in two overlapping charts, and `c₁` satisfies the ODE with
`Γ₁` computed from `g` in chart 1, then `c₂` satisfies the ODE with `Γ₂`
computed from `g` in chart 2. Without this lemma, "is a geodesic" is only
provably well-defined if stated with a fixed canonical chart
(`chartAt _ (μ.toFun s)`, Mathlib's choice) and the chart-independence is
then a **theorem to prove**, not built into the definition. Recommend:
define via `chartAt`/`extChartAt` at each point (so the definition typechecks
immediately, no existential over charts), and state chart-independence as a
separate lemma, `IsGeodesic_chart_change` or similar, proved once via the
Jacobian transformation law for `Γ` — this is itself a moderately-sized
differential-geometry lemma (the standard "Christoffel symbols transform as
a connection, not a tensor" computation) that Mathlib does not provide
(§3: no hits for `Christoffel`/`Connection`/`LeviCivita` under
`Mathlib/Geometry`).

## 3. Relevant Mathlib API (verified by grep on `.lake/packages/mathlib/`, pinned to the repo's Mathlib for Lean v4.32.0)

- `extChartAt` (def) and `extChartAt_coe`, `extChartAt_coe_symm`,
  `extChartAt_source`, `extChartAt_target`:
  `.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:454-480`.
- Tangent-bundle trivialization: `trivializationAt`, `trivializationAt_source/target/baseSet/apply/fst`,
  `continuousLinearMapAt_trivializationAt_eq_core`, `symmL_trivializationAt_eq_core`,
  `tangentBundleCore_coordChange_achart`:
  `.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean:86-282`.
- `ContMDiff.clm_bundle_apply`, `ContMDiff.clm_bundle_apply₂`:
  `.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Hom.lean:335,445`
  (already the load-bearing lemma cited in `Basic.lean`'s own docstring for
  extracting smoothness of `g(V,W)`).
- Matrix inverse of a nondegenerate Gram matrix:
  `Matrix.Nondegenerate` (def), `Matrix.nondegenerate_iff_det_ne_zero`
  (`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Nondegenerate.lean:159`),
  `BilinForm.Nondegenerate.toMatrix'` (`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/BilinearForm.lean:487-491`),
  `Matrix.nonsing_inv` (`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`).
- Derivatives: `derivWithin`, `fderivWithin` (`Mathlib.Analysis.Calculus.Deriv.Basic`,
  `Mathlib.Analysis.Calculus.FDeriv.Basic`), `UniqueDiffOn` — the project already
  has `Path.uniqueDiffOn_parameterSpace` (`Physicslib4/Spacetime/Curves.lean:118-133`)
  proving `UniqueDiffOn ℝ μ.parameterSpace`, the exact prerequisite for
  well-behaved `derivWithin`/second-`derivWithin`.
- **No Christoffel/connection API in Mathlib**: `grep -rl "Christoffel\|LeviCivita\|Levi-Civita\|AffineConnection" .lake/packages/mathlib/Mathlib/` returns **no files**. The only Riemannian-adjacent material is
  `.lake/packages/mathlib/Mathlib/Geometry/Manifold/Riemannian/` and
  `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`, which define
  `ContMDiffRiemannianMetric` (positive-definite, with `isVonNBounded`) and
  no connection, curvature, or geodesic notion. This confirms the docstring's
  claim and the premise of the question: any Christoffel/geodesic definition
  here is genuinely new content, buildable only from the primitives above.

## 4. Impact: what would need real proofs

`grep -rn IsGeodesic` (excluding `.lake`) hits, besides the definition itself:

- **`Causality.lean:108,153`** — `IsTrip`/`IsCausalTrip` segment predicates
  include `M.IsGeodesic rep` as a conjunct. Currently vacuous; would become
  a real constraint. *Difficulty: definitional, no proof burden by itself,*
  but every downstream construction of a trip (e.g. straight lines in
  Minkowski) must now *prove* the geodesic equation instead of getting it
  for free.
- **`Minkowski.lean:670`** (`minkowskiForwardCone_subset_chronologicalFuture_standardMinkowski`
  reverse-direction proof): builds the straight-line path
  `s ↦ p + s•(q-p)` and currently discharges `IsGeodesic` for free
  (`"IsGeodesic = True is automatic"`). With real content: need
  `Γ = 0` for the flat Minkowski metric in the standard chart (since `g_ij`
  is literally the constant matrix `lorentzSignature`, all `∂_i g_jl = 0`,
  so `Γ ≡ 0` and `c'' = 0` for a straight line — an easy but nonzero proof,
  needs the constant-metric computation). *Difficulty: low–moderate*
  (mostly bookkeeping: showing `derivWithin` of an affine function is
  constant hence its `derivWithin` again is `0`, and `Γ = 0` from
  `contMDiff_const`/`fderiv_const`).
- **`IsometryCausality.lean`** (`pushforwardPath_isTimelike/isCausal/...`,
  `segmentPrecedes_pushforward`, `chronologicallyPrecedes_pushforward`,
  `chronologicalFuture_image[_subset]`, `chronologicalPast_image[_subset]`,
  `alexandrovBasis_image*`) and **`CrossMetricIsometry.lean`**
  (`CrossIsometry.chronologicallyPrecedes`, `chronologicalFuture_image`,
  `chronologicalPast_image`, `pullback_alexandrovBasis_*`) — these prove that
  isometries (resp. cross-metric isometries between two spacetimes) carry
  trips to trips, hence `≪`/`≺` forward, hence chronological/causal
  futures/pasts and Alexandrov-topology basis sets forward. Every one of
  these currently gets the geodesic conjunct for free. With real content,
  each needs: **isometries send geodesics to geodesics.** This is the
  standard fact that an isometry (metric-preserving diffeomorphism, exactly
  `Isometry.preserves : ∀ x v w, val (φ x) (dφ v) (dφ w) = val x v w`,
  `Physicslib4/Spacetime/Isometry.lean:62-67`) pulls back the Christoffel
  symbols computed from `g` to the Christoffel symbols of the pulled-back
  chart — i.e. isometries are *affine* maps of the (unique, torsion-free,
  metric-compatible) connection determined by `g`. **This is a real,
  moderately hard differential-geometry lemma with no Mathlib support**
  (no connections, no naturality-of-Levi-Civita-under-isometry lemma
  exists anywhere in Mathlib) — it must be proved from scratch by chasing
  the definition of `Γ` through the chain rule for `g` in the pushed-forward
  chart, using exactly the `mfderivWithin_comp_diffeo`/chain-rule machinery
  already built in `IsometryCausality.lean:48-58`, generalized to second
  derivatives. *Difficulty: high* — this is the crux of the whole
  refactor's added proof burden, and it must be done once (as a general
  "isometries preserve `Γ`" or "isometries preserve `IsGeodesic`" lemma) and
  then threaded through every one of the ~10 downstream theorems listed
  above.
- **`LorentzCausality.lean`** (`lorentzPath_isCausal/isFutureOriented/...`,
  `causallyPrecedes_smul[_iff]`, `chronologicallyPrecedes_smul[_iff]`,
  `isCompletelySpacelike_smul[_iff]`) — same shape as `IsometryCausality.lean`
  but specialized to the (linear, hence trivially affine) action of the
  inhomogeneous Lorentz group on `StandardMinkowskiSpacetime`. Since Lorentz
  transformations are affine and `Γ ≡ 0` on flat Minkowski in the standard
  chart, these reduce to the same "linear map ⇒ preserves `c'' = 0`" style
  argument as the `Minkowski.lean` case. *Difficulty: low–moderate*, can
  likely reuse the general isometry lemma once proved, or be done directly
  and more easily since `Γ ≡ 0`.
- **Blueprint**: `grep -c "Formalization note" blueprint/src/sections/sec10/spacetime.tex` → **57** occurrences of the boilerplate
  "this statement rests on ... IsGeodesic is True ..." formalization note
  (lines 341, 358, 370, 387, ... through 982), one narrative remark
  (line 341) plus 56 repeated per-theorem notes. All 57 could be retired
  (deleted, since the geodesic clause would then be faithful) once
  `IsGeodesic` carries real content and the downstream theorems above are
  reproved with it.

## 5. Recommendation and staged plan

**Recommendation: yes, worth doing, but budget for the isometry-invariance
lemma as the dominant cost, not the definition itself.** The definition is
mechanically buildable today from Mathlib primitives with zero new imports
(§1–2), which answers the literal question affirmatively. The real work,
and the reason to stage this, is §4: every existing "isometries/Lorentz
transformations preserve trips" theorem currently gets its geodesic conjunct
for free and will need a genuine differential-geometric argument once
`IsGeodesic` is real.

Staged plan:
1. **Definition-only PR** (needs user approval — `def` is a blocked new
   declaration for agents per `.claude/lean-policy.json`): add
   `christoffelSymbols`/`Γ` and the real `IsGeodesic`, chart-fixed at
   `chartAt _ (μ.toFun s)` (§2), *without* touching any of the downstream
   files in §4 yet. This alone breaks nothing structurally since `IsTrip`
   would now require the new hypothesis, but no theorem currently proves
   `IsTrip`/`IsCausalTrip` except via the `IsGeodesic = True` shortcut — so
   every existing trip-producing proof (Minkowski straight lines,
   pushforwards) breaks and must be patched in the same PR or immediately
   after.
2. **Discharge the flat-Minkowski case** (`Minkowski.lean`,
   `LorentzCausality.lean`): show `Γ ≡ 0` for the constant Lorentzian metric
   in the standard chart, then straight lines and their Lorentz-linear
   images are geodesics for free (`c'' = 0` for affine `c`). Low-to-moderate
   difficulty; unblocks the largest fraction of the 57 blueprint notes.
3. **Prove the general isometry/diffeomorphism-invariance lemma**
   (`IsometryCausality.lean`, `CrossMetricIsometry.lean`): "if `φ` is an
   isometry (or `CrossIsometry`) and `μ` is a geodesic, `φ ∘ μ` is a
   geodesic," by chasing `Γ` through the pushforward chart using the
   existing chain-rule lemmas (`mfderivWithin_comp_diffeo`) generalized to
   second derivatives. This is the expensive, novel step — no Mathlib
   support exists.
4. **Chart-independence lemma** (§2): needed only if trips are ever
   compared across different charts explicitly (not needed for step 2–3 if
   `chartAt`/`extChartAt` is used consistently), but worth doing once for
   robustness and to justify the "the preferred chart" design choice in the
   docstring.
5. **Retire the 57 blueprint formalization notes** once steps 1–3 land.

**Risks:**
- The nondegeneracy field in `Spacetime` is the linear-algebra form
  (`∀ w, val x v w = 0 → v = 0`), not `Matrix.Nondegenerate` directly;
  bridging to `Matrix.nondegenerate_iff_det_ne_zero` needs an explicit
  transport lemma via the chosen frame/basis (`Module.Basis.toMatrix` /
  `BilinForm.toMatrix'`) — mechanical but must be done once, carefully,
  to avoid basis-dependence bugs (the *value* `g^{kl}` in a fixed chart
  frame is basis-independent once the frame is fixed, but the intermediate
  lemma statements are easy to get subtly wrong).
- `chartAt`/`extChartAt` are **classical, non-canonical choices**
  (`Classical.choice`-backed in general `ChartedSpace`); the resulting `Γ`
  and hence `IsGeodesic` are well-defined `Prop`s but any two agents'
  proofs must be careful to use the *same* `chartAt` instance consistently,
  or the chart-independence lemma of §2 becomes load-bearing sooner than
  planned.
- The isometry-invariance lemma (step 3) is the one place this plan could
  stall: it is a real theorem (isometries are affine for the Levi-Civita
  connection), with no partial credit from Mathlib, and no local precedent
  in this codebase to imitate (the `qinz1yang` library does not prove an
  analogous lemma either, since it has no notion of isometry).
- This is a **definition change** to `IsGeodesic` (and a new `def` for `Γ`,
  both blocked to agents by `new_declarations` in `.claude/lean-policy.json`)
  and must be approved by the user before any agent implements it.
