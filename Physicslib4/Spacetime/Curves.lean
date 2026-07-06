/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Basic
import Physicslib4.Spacetime.CausalStructure
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Connected.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.Topology

/-!
# Paths and curves on a spacetime

This file formalises the various flavours of paths and curves used in
section 10.2 of the AQFT-in-Lean blueprint.

## Main definitions

* `Physicslib4.Spacetime.Path`: a continuous map from a closed, connected,
  non-singleton subset `Σ ⊆ ℝ` ("parameter space") to a spacetime `M`.
* `Physicslib4.Spacetime.SmoothPath`: a path that is also smooth with
  non-vanishing derivative.
* `Physicslib4.Spacetime.PathEquiv`, `SmoothPathEquiv`: the equivalence
  relations on paths/smooth paths corresponding to reparametrisation by
  homeomorphisms / diffeomorphisms of the parameter space.
* `Physicslib4.Spacetime.Curve`, `SmoothCurve`: the corresponding quotient
  types.
* `Physicslib4.Spacetime.IsTimelikeSmoothCurve`, `IsCausalSmoothCurve`:
  predicates singling out smooth curves whose tangent vector at every point
  is timelike / causal.
* `Physicslib4.Spacetime.IsFutureOrientedSmoothCurve` /
  `IsPastOrientedSmoothCurve`: future/past orientation predicates relative
  to a given time orientation.
* `Physicslib4.Spacetime.IsEndpoint`, `IsPastEndpoint`, `IsFutureEndpoint`:
  the endpoint terminology for paths and their associated curves.

## Modelling notes

The notion of "smooth at a boundary point of a closed interval" is delicate
in general. In this file we follow the conservative convention used in
Mathlib for `ContMDiff` of a function on a subset, and state the
"non-vanishing derivative" condition pointwise on the parameter space `Σ`.
These are genuine `Prop` fields of `SmoothPath` — `smoothOn : ContMDiffOn …`
and `nonvanishing : ∀ s ∈ Σ, mfderivWithin _ _ toFun Σ s 1 ≠ 0` — carried by
the structure, not `sorry` placeholders. They are discharged for concrete
paths via named lemmas; for the straight-line path see
`standardMinkowskiLineSegmentPath_smoothOn` and
`standardMinkowskiLineSegmentPath_nonvanishing` in `Minkowski.lean`.
-/

namespace Physicslib4

namespace Spacetime

variable (M : Spacetime)

attribute [instance] Spacetime.topology Spacetime.hausdorff Spacetime.connected
  Spacetime.chartedSpace Spacetime.isManifold Spacetime.tangent_findim

/-! ### Paths -/

/--
A *path* in a spacetime `M` is a continuous map `μ : Σ → M.Carrier` whose
domain `Σ`, called the *parameter space*, is a closed, connected subset of
`ℝ` containing more than one point.

Following the blueprint we store `Σ` as a `Set ℝ` along with proofs that it
is closed, connected and not a singleton (i.e. contains more than one
point).
-/
structure Path where
  /-- The parameter space, a subset of `ℝ`. -/
  parameterSpace : Set ℝ
  /-- The parameter space is closed in `ℝ`. -/
  isClosed : IsClosed parameterSpace
  /-- The parameter space is connected. -/
  isConnected : IsConnected parameterSpace
  /-- The parameter space contains at least two distinct points. -/
  nontrivial : ∃ s t, s ∈ parameterSpace ∧ t ∈ parameterSpace ∧ s ≠ t
  /-- The underlying continuous map `Σ → M.Carrier`. -/
  toFun : ℝ → M.Carrier
  /-- Continuity of the underlying map on the parameter space. -/
  continuousOn : ContinuousOn toFun parameterSpace

/--
A *smooth path* in a spacetime `M` is a path `μ : Σ → M` which is smooth and
has a non-vanishing derivative along `Σ`.

The smoothness condition is `ContMDiffOn` on the parameter space, relative to
the identity model with corners on `ℝ` and the spacetime's model. The
non-vanishing-derivative condition states that the manifold derivative
`mfderiv` of `μ`, applied to the basis vector `1 : ℝ`, is non-zero at every
point of `Σ`.
-/
structure SmoothPath extends M.Path where
  /-- Smoothness of the underlying map on the parameter space. -/
  smoothOn :
    ContMDiffOn (modelWithCornersSelf ℝ ℝ) M.model ⊤ toFun parameterSpace
  /-- The tangent vector along the path is non-vanishing on the parameter
  space: the manifold derivative of `toFun` applied to `1 : ℝ` is non-zero
  at each interior point of the parameter space. -/
  nonvanishing : ∀ s ∈ parameterSpace,
    mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model toFun parameterSpace s
        (1 : ℝ) ≠ 0

/-- The parameter space of a path has unique differentials: being a closed
connected subset of `ℝ` with at least two points, it is a non-degenerate
interval, hence convex with non-empty interior. This is the analytic
prerequisite for differentiating compositions along a path via the
`mfderivWithin` chain rule. -/
theorem Path.uniqueDiffOn_parameterSpace (μ : M.Path) :
    UniqueDiffOn ℝ μ.parameterSpace := by
  have hoc : μ.parameterSpace.OrdConnected :=
    μ.isConnected.isPreconnected.ordConnected
  have hconv : Convex ℝ μ.parameterSpace := convex_iff_ordConnected.mpr hoc
  apply uniqueDiffOn_convex hconv
  obtain ⟨a, b, ha, hb, hab⟩ := μ.nontrivial
  rcases lt_or_gt_of_ne hab with h | h
  · have hIoo : Set.Ioo a b ⊆ interior μ.parameterSpace :=
      isOpen_Ioo.subset_interior_iff.mpr
        (Set.Ioo_subset_Icc_self.trans (hoc.out ha hb))
    exact ⟨(a + b) / 2, hIoo (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)⟩
  · have hIoo : Set.Ioo b a ⊆ interior μ.parameterSpace :=
      isOpen_Ioo.subset_interior_iff.mpr
        (Set.Ioo_subset_Icc_self.trans (hoc.out hb ha))
    exact ⟨(a + b) / 2, hIoo (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)⟩

/-! ### Tangent vector -/

/-- The **tangent vector** of a smooth path `μ` at parameter `s`: the manifold
derivative of `μ` along its parameter space, applied to the basis vector `1 : ℝ`.
This is the object all the causal predicates below are phrased in terms of. -/
noncomputable def SmoothPath.tangent {M : Spacetime} (μ : M.SmoothPath) (s : ℝ) :
    TangentSpace M.model (μ.toFun s) :=
  mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model μ.toFun μ.parameterSpace s (1 : ℝ)

/-- Unfolding lemma for `SmoothPath.tangent` to the raw `mfderivWithin` form. -/
theorem SmoothPath.tangent_def {M : Spacetime} (μ : M.SmoothPath) (s : ℝ) :
    μ.tangent s
      = mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model
          μ.toFun μ.parameterSpace s (1 : ℝ) := rfl

/-- The tangent vector of a smooth path is non-vanishing on the parameter
space (the `nonvanishing` field, restated via `tangent`). -/
theorem SmoothPath.tangent_ne_zero {M : Spacetime} (μ : M.SmoothPath) {s : ℝ}
    (hs : s ∈ μ.parameterSpace) : μ.tangent s ≠ 0 :=
  μ.nonvanishing s hs

/-- **Reparametrisation chain rule for the tangent vector.** Composing a smooth
path `μ` with a (manifold-)differentiable reparametrisation `φ : ℝ → ℝ` that maps
`Σ'` into `μ`'s parameter space scales the tangent vector by the derivative of
`φ`: `tangent (μ ∘ φ) s = (φ'(s)) • tangent μ (φ s)`, where the scalar is the
one-dimensional manifold derivative of `φ`. This is the analytic heart of the
reparametrisation-invariance of the causal type of a curve. -/
theorem SmoothPath.mfderivWithin_comp_reparam {M : Spacetime} (μ : M.SmoothPath)
    {φ : ℝ → ℝ} {u : Set ℝ} {s : ℝ}
    (hφ : MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ℝ) φ u s)
    (hmaps : Set.MapsTo φ u μ.parameterSpace)
    (huniq : UniqueMDiffWithinAt (modelWithCornersSelf ℝ ℝ) u s)
    (hs : s ∈ u) :
    mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model (μ.toFun ∘ φ) u s (1 : ℝ)
      = (derivWithin φ u s) • μ.tangent (φ s) := by
  have hg : MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ) M.model
      μ.toFun μ.parameterSpace (φ s) :=
    (μ.smoothOn (φ s) (hmaps hs)).mdifferentiableWithinAt (by simp)
  have hcomp := mfderivWithin_comp s hg hφ hmaps huniq
  rw [hcomp]
  change mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model μ.toFun μ.parameterSpace (φ s)
      (mfderivWithin (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) φ u s (1 : ℝ))
    = derivWithin φ u s • μ.tangent (φ s)
  rw [SmoothPath.tangent_def, ← ContinuousLinearMap.map_smul]
  congr 1
  rw [mfderivWithin_eq_fderivWithin]
  change (fderivWithin ℝ φ u s) 1 = (derivWithin φ u s : ℝ) • (1 : ℝ)
  rw [smul_eq_mul, mul_one]
  rfl

/-- **Tangent vector under a reparametrisation.** If a reparametrisation
`φ : ℝ → ℝ` (differentiable, mapping `μ₁`'s parameter space into `μ₂`'s) identifies
the two paths pointwise (`μ₂ (φ s') = μ₁ s'` on `μ₁`'s parameter space), then the
tangent vectors are related by the derivative of `φ`:
`tangent μ₁ s = (φ'(s)) • tangent μ₂ (φ s)`. Combines the reparametrisation chain
rule with `mfderivWithin_congr` (the two paths agree on the parameter space, so
have equal within-derivatives). -/
theorem SmoothPath.tangent_reparam_eq {M : Spacetime} (μ₁ μ₂ : M.SmoothPath)
    {φ : ℝ → ℝ} {s : ℝ}
    (hφ : MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ℝ) φ μ₁.parameterSpace s)
    (hmaps : Set.MapsTo φ μ₁.parameterSpace μ₂.parameterSpace)
    (heq : ∀ s' ∈ μ₁.parameterSpace, μ₂.toFun (φ s') = μ₁.toFun s')
    (hs : s ∈ μ₁.parameterSpace) :
    μ₁.tangent s = (derivWithin φ μ₁.parameterSpace s) • μ₂.tangent (φ s) := by
  have huniq : UniqueMDiffWithinAt (modelWithCornersSelf ℝ ℝ) μ₁.parameterSpace s :=
    (Path.uniqueDiffOn_parameterSpace M μ₁.toPath s hs).uniqueMDiffWithinAt
  have hcongr : mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model
        μ₁.toFun μ₁.parameterSpace s
      = mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model
          (μ₂.toFun ∘ φ) μ₁.parameterSpace s :=
    mfderivWithin_congr (fun s' hs' => (heq s' hs').symm) (heq s hs).symm
  rw [SmoothPath.tangent_def, hcongr]
  exact μ₂.mfderivWithin_comp_reparam hφ hmaps huniq hs

/-- **Non-vanishing of a reparametrisation derivative.** If `ψ ∘ φ = id` on a set
`u` (with `φ` mapping `u` into `v`, both maps differentiable within their sets, and
`u` having unique differentials at `x`), then the within-derivative of `φ` is
non-zero at `x`. This is the real-analytic fact behind the `derivWithin φ ≠ 0`
hypothesis of the pointwise reparametrisation lemmas, obtained by differentiating
the left-inverse identity via the chain rule. -/
theorem derivWithin_ne_zero_of_leftInverse {φ ψ : ℝ → ℝ} {u v : Set ℝ} {x : ℝ}
    (hφ : DifferentiableWithinAt ℝ φ u x)
    (hψ : DifferentiableWithinAt ℝ ψ v (φ x))
    (hmaps : Set.MapsTo φ u v)
    (huniq : UniqueDiffWithinAt ℝ u x)
    (hx : x ∈ u)
    (hinv : ∀ y ∈ u, ψ (φ y) = y) :
    derivWithin φ u x ≠ 0 := by
  intro hzero
  have hcomp : derivWithin (ψ ∘ φ) u x
      = derivWithin ψ v (φ x) * derivWithin φ u x :=
    derivWithin_comp x hψ hφ hmaps
  have hid : derivWithin (ψ ∘ φ) u x = 1 :=
    (derivWithin_congr (fun y hy => hinv y hy) (hinv x hx)).trans
      (derivWithin_id' x u huniq)
  rw [hzero, mul_zero, hid] at hcomp
  exact one_ne_zero hcomp

/-- A `C^⊤` function `ℝ → ℝ` is manifold-differentiable within a set, for the
self models on `ℝ`. Bridges the `ContDiffOn` datum stored in `SmoothPathEquiv` to
the `MDifferentiableWithinAt` hypothesis required by the tangent reparametrisation
lemmas. -/
theorem mdifferentiableWithinAt_of_contDiffOn {φ : ℝ → ℝ} {u : Set ℝ}
    (h : ContDiffOn ℝ ⊤ φ u) {x : ℝ} (hx : x ∈ u) :
    MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      φ u x :=
  ((h.contDiffWithinAt hx).contMDiffWithinAt).mdifferentiableWithinAt (by simp)

/-! ### Reparametrisation equivalence -/

/--
Two paths `μ₁ : Σ₁ → M`, `μ₂ : Σ₂ → M` are equivalent if there is a
homeomorphism `φ` of `ℝ` mapping `Σ₁` bijectively onto `Σ₂` such that
`μ₂ ∘ φ = μ₁` on `Σ₁`. We package the homeomorphism on the parameter spaces
via its underlying function on `ℝ` together with the relevant restriction
conditions.
-/
def PathEquiv (μ₁ μ₂ : M.Path) : Prop :=
  ∃ φ : ℝ → ℝ,
    Continuous φ ∧
    (∃ ψ : ℝ → ℝ, Continuous ψ ∧ Function.LeftInverse ψ φ ∧
      Function.RightInverse ψ φ) ∧
    Set.MapsTo φ μ₁.parameterSpace μ₂.parameterSpace ∧
    (∀ s ∈ μ₁.parameterSpace, μ₂.toFun (φ s) = μ₁.toFun s)

/--
Two smooth paths are equivalent if there is a diffeomorphism `φ : ℝ → ℝ`
sending one parameter space to the other and identifying the underlying
maps. We package the diffeomorphism condition by smoothness of `φ` and its
inverse `ψ` on the relevant parameter spaces, paired with their being
two-sided inverses.
-/
def SmoothPathEquiv (μ₁ μ₂ : M.SmoothPath) : Prop :=
  ∃ φ ψ : ℝ → ℝ,
    ContDiffOn ℝ ⊤ φ μ₁.parameterSpace ∧
    ContDiffOn ℝ ⊤ ψ μ₂.parameterSpace ∧
    Set.MapsTo φ μ₁.parameterSpace μ₂.parameterSpace ∧
    Set.MapsTo ψ μ₂.parameterSpace μ₁.parameterSpace ∧
    (∀ s ∈ μ₁.parameterSpace, ψ (φ s) = s) ∧
    (∀ t ∈ μ₂.parameterSpace, φ (ψ t) = t) ∧
    (∀ s ∈ μ₁.parameterSpace, μ₂.toFun (φ s) = μ₁.toFun s)

/--
Two smooth paths are *orientation-preservingly* equivalent if they are related by
a smooth reparametrisation `φ` (as in `SmoothPathEquiv`) whose within-derivative is
everywhere positive on `μ₁`'s parameter space. Positivity of `φ'` is exactly what
distinguishes orientation-preserving from orientation-reversing reparametrisations,
and it is the extra datum needed to transport the *time orientation* of a curve
(future/past-pointing), not merely its causal type.
-/
def OrientedSmoothPathEquiv (μ₁ μ₂ : M.SmoothPath) : Prop :=
  ∃ φ ψ : ℝ → ℝ,
    ContDiffOn ℝ ⊤ φ μ₁.parameterSpace ∧
    ContDiffOn ℝ ⊤ ψ μ₂.parameterSpace ∧
    Set.MapsTo φ μ₁.parameterSpace μ₂.parameterSpace ∧
    Set.MapsTo ψ μ₂.parameterSpace μ₁.parameterSpace ∧
    (∀ s ∈ μ₁.parameterSpace, ψ (φ s) = s) ∧
    (∀ t ∈ μ₂.parameterSpace, φ (ψ t) = t) ∧
    (∀ s ∈ μ₁.parameterSpace, μ₂.toFun (φ s) = μ₁.toFun s) ∧
    (∀ s ∈ μ₁.parameterSpace, 0 < derivWithin φ μ₁.parameterSpace s)

/-- An orientation-preserving smooth reparametrisation is in particular a smooth
reparametrisation. -/
theorem OrientedSmoothPathEquiv.toSmoothPathEquiv {μ₁ μ₂ : M.SmoothPath}
    (h : M.OrientedSmoothPathEquiv μ₁ μ₂) : M.SmoothPathEquiv μ₁ μ₂ := by
  obtain ⟨φ, ψ, hφC, hψC, hφmaps, hψmaps, hψφ, hφψ, heq, _⟩ := h
  exact ⟨φ, ψ, hφC, hψC, hφmaps, hψmaps, hψφ, hφψ, heq⟩

/-! ### Curves -/

/-- A *curve* in a spacetime is an equivalence class of paths under
parameter reparametrisation by homeomorphisms. We package this as a
`Quot` over the (possibly non-equivalence) relation `PathEquiv`; the actual
equivalence-class structure is left implicit. -/
def Curve : Type := Quot M.PathEquiv

/-- A *smooth curve* in a spacetime is an equivalence class of smooth paths
under parameter reparametrisation by diffeomorphisms. -/
def SmoothCurve : Type := Quot M.SmoothPathEquiv

/-- Constructor: every smooth path determines a smooth curve. -/
def SmoothCurve.ofPath (μ : M.SmoothPath) : SmoothCurve M :=
  Quot.mk _ μ

/-- Constructor: every path determines a curve. -/
def Curve.ofPath (μ : M.Path) : Curve M :=
  Quot.mk _ μ

/-! ### Timelike and causal smooth curves -/

/--
A smooth path `μ : Σ → M` is *timelike at parameter `s ∈ Σ`* if its tangent
vector at `s` (the image under `mfderivWithin` of `1 : ℝ`) is a timelike
tangent vector at the spacetime point `μ s`.
-/
def SmoothPath.IsTimelikeAt (μ : M.SmoothPath) (s : ℝ) : Prop :=
  M.IsTimelike (μ.tangent s)

/-- **Pointwise reparametrisation-invariance of timelikeness.** Under a
reparametrisation identifying `μ₁` with `μ₂` (as in `tangent_reparam_eq`) with
non-vanishing derivative `φ'(s) ≠ 0`, `μ₁` is timelike at `s` iff `μ₂` is timelike
at `φ s`. Combines the reparametrisation chain rule with the scaling invariance
`isTimelike_smul_iff`. -/
theorem SmoothPath.isTimelikeAt_reparam {M : Spacetime} (μ₁ μ₂ : M.SmoothPath)
    {φ : ℝ → ℝ} {s : ℝ}
    (hφ : MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ℝ) φ μ₁.parameterSpace s)
    (hmaps : Set.MapsTo φ μ₁.parameterSpace μ₂.parameterSpace)
    (heq : ∀ s' ∈ μ₁.parameterSpace, μ₂.toFun (φ s') = μ₁.toFun s')
    (hs : s ∈ μ₁.parameterSpace)
    (hφ' : derivWithin φ μ₁.parameterSpace s ≠ 0) :
    SmoothPath.IsTimelikeAt M μ₁ s ↔ SmoothPath.IsTimelikeAt M μ₂ (φ s) := by
  simp only [SmoothPath.IsTimelikeAt]
  rw [μ₁.tangent_reparam_eq μ₂ hφ hmaps heq hs,
    show μ₁.toFun s = μ₂.toFun (φ s) from (heq s hs).symm]
  exact M.isTimelike_smul_iff hφ' (μ₂.tangent (φ s))

/-- **Pointwise reparametrisation-invariance of the causal (timelike-or-null)
condition.** The direct analogue of `isTimelikeAt_reparam` for the disjunction
`timelike ∨ null`, via the reparametrisation chain rule together with the scaling
invariances `isTimelike_smul_iff` and `isNull_smul_iff`. -/
theorem SmoothPath.causalAt_reparam {M : Spacetime} (μ₁ μ₂ : M.SmoothPath)
    {φ : ℝ → ℝ} {s : ℝ}
    (hφ : MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ℝ) φ μ₁.parameterSpace s)
    (hmaps : Set.MapsTo φ μ₁.parameterSpace μ₂.parameterSpace)
    (heq : ∀ s' ∈ μ₁.parameterSpace, μ₂.toFun (φ s') = μ₁.toFun s')
    (hs : s ∈ μ₁.parameterSpace)
    (hφ' : derivWithin φ μ₁.parameterSpace s ≠ 0) :
    (M.IsTimelike (μ₁.tangent s) ∨ M.IsNull (μ₁.tangent s))
      ↔ (M.IsTimelike (μ₂.tangent (φ s)) ∨ M.IsNull (μ₂.tangent (φ s))) := by
  rw [μ₁.tangent_reparam_eq μ₂ hφ hmaps heq hs,
    show μ₁.toFun s = μ₂.toFun (φ s) from (heq s hs).symm]
  exact or_congr (M.isTimelike_smul_iff hφ' (μ₂.tangent (φ s)))
    (M.isNull_smul_iff hφ' (μ₂.tangent (φ s)))

/-- **Pointwise reparametrisation-invariance of future-pointing.** Under an
orientation-preserving reparametrisation identifying `μ₁` with `μ₂` (positive
derivative `0 < φ'(s)`), `μ₁`'s tangent is future-pointing at `s` iff `μ₂`'s is at
`φ s`. Combines the reparametrisation chain rule with the positive-scaling
invariance `isFuturePointing_smul_iff`. -/
theorem SmoothPath.isFuturePointing_reparam {M : Spacetime} (μ₁ μ₂ : M.SmoothPath)
    (t : M.TimeOrientation) {φ : ℝ → ℝ} {s : ℝ}
    (hφ : MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ℝ) φ μ₁.parameterSpace s)
    (hmaps : Set.MapsTo φ μ₁.parameterSpace μ₂.parameterSpace)
    (heq : ∀ s' ∈ μ₁.parameterSpace, μ₂.toFun (φ s') = μ₁.toFun s')
    (hs : s ∈ μ₁.parameterSpace)
    (hφ' : 0 < derivWithin φ μ₁.parameterSpace s) :
    M.IsFuturePointing t (μ₁.tangent s)
      ↔ M.IsFuturePointing t (μ₂.tangent (φ s)) := by
  rw [μ₁.tangent_reparam_eq μ₂ hφ hmaps heq hs,
    show μ₁.toFun s = μ₂.toFun (φ s) from (heq s hs).symm]
  exact M.isFuturePointing_smul_iff t hφ' (μ₂.tangent (φ s))

/-- **Pointwise reparametrisation-invariance of past-pointing.** The dual of
`isFuturePointing_reparam`, via `isPastPointing_smul_iff`. -/
theorem SmoothPath.isPastPointing_reparam {M : Spacetime} (μ₁ μ₂ : M.SmoothPath)
    (t : M.TimeOrientation) {φ : ℝ → ℝ} {s : ℝ}
    (hφ : MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ℝ) φ μ₁.parameterSpace s)
    (hmaps : Set.MapsTo φ μ₁.parameterSpace μ₂.parameterSpace)
    (heq : ∀ s' ∈ μ₁.parameterSpace, μ₂.toFun (φ s') = μ₁.toFun s')
    (hs : s ∈ μ₁.parameterSpace)
    (hφ' : 0 < derivWithin φ μ₁.parameterSpace s) :
    M.IsPastPointing t (μ₁.tangent s)
      ↔ M.IsPastPointing t (μ₂.tangent (φ s)) := by
  rw [μ₁.tangent_reparam_eq μ₂ hφ hmaps heq hs,
    show μ₁.toFun s = μ₂.toFun (φ s) from (heq s hs).symm]
  exact M.isPastPointing_smul_iff t hφ' (μ₂.tangent (φ s))

/-- A smooth path is timelike if its tangent vector is timelike at every
point of the parameter space. -/
def SmoothPath.IsTimelike (μ : M.SmoothPath) : Prop :=
  ∀ s ∈ μ.parameterSpace, M.IsTimelike (μ.tangent s)

/-- A smooth path is *causal* if its tangent vector is either timelike or
null at every point of the parameter space. -/
def SmoothPath.IsCausal (μ : M.SmoothPath) : Prop :=
  ∀ s ∈ μ.parameterSpace,
    M.IsTimelike (μ.tangent s) ∨ M.IsNull (μ.tangent s)

/-- **Reparametrisation-invariance of timelikeness.** Two smooth paths related by
a smooth reparametrisation (`SmoothPathEquiv`) are timelike together: one is
timelike iff the other is. The forward direction uses the inverse diffeomorphism
`ψ` for surjectivity onto `μ₂`'s parameter space; both directions rest on the
pointwise `isTimelikeAt_reparam` (via the chain rule and scaling invariance), with
the reparametrisation derivative non-vanishing by
`derivWithin_ne_zero_of_leftInverse`. -/
theorem SmoothPath.isTimelike_iff_of_smoothPathEquiv {M : Spacetime}
    {μ₁ μ₂ : M.SmoothPath} (h : M.SmoothPathEquiv μ₁ μ₂) :
    SmoothPath.IsTimelike M μ₁ ↔ SmoothPath.IsTimelike M μ₂ := by
  obtain ⟨φ, ψ, hφC, hψC, hφmaps, hψmaps, hψφ, hφψ, heq⟩ := h
  have hφmdiff : ∀ x ∈ μ₁.parameterSpace,
      MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        φ μ₁.parameterSpace x :=
    fun x hx => mdifferentiableWithinAt_of_contDiffOn hφC hx
  have hφderiv : ∀ x ∈ μ₁.parameterSpace, derivWithin φ μ₁.parameterSpace x ≠ 0 :=
    fun x hx => derivWithin_ne_zero_of_leftInverse
      ((hφC.differentiableOn (by simp)) x hx)
      ((hψC.differentiableOn (by simp)) (φ x) (hφmaps hx))
      hφmaps (Path.uniqueDiffOn_parameterSpace M μ₁.toPath x hx) hx hψφ
  constructor
  · intro h₁ t ht
    have hs : ψ t ∈ μ₁.parameterSpace := hψmaps ht
    have hiff := μ₁.isTimelikeAt_reparam μ₂ (hφmdiff _ hs) hφmaps heq hs (hφderiv _ hs)
    rw [hφψ t ht] at hiff
    exact hiff.mp (h₁ _ hs)
  · intro h₂ s hs
    have hiff := μ₁.isTimelikeAt_reparam μ₂ (hφmdiff _ hs) hφmaps heq hs (hφderiv _ hs)
    exact hiff.mpr (h₂ _ (hφmaps hs))

/-- **Reparametrisation-invariance of the causal condition.** Two smooth paths
related by a smooth reparametrisation (`SmoothPathEquiv`) are causal together. Same
structure as `isTimelike_iff_of_smoothPathEquiv`, using the pointwise
`causalAt_reparam`. -/
theorem SmoothPath.isCausal_iff_of_smoothPathEquiv {M : Spacetime}
    {μ₁ μ₂ : M.SmoothPath} (h : M.SmoothPathEquiv μ₁ μ₂) :
    SmoothPath.IsCausal M μ₁ ↔ SmoothPath.IsCausal M μ₂ := by
  obtain ⟨φ, ψ, hφC, hψC, hφmaps, hψmaps, hψφ, hφψ, heq⟩ := h
  have hφmdiff : ∀ x ∈ μ₁.parameterSpace,
      MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        φ μ₁.parameterSpace x :=
    fun x hx => mdifferentiableWithinAt_of_contDiffOn hφC hx
  have hφderiv : ∀ x ∈ μ₁.parameterSpace, derivWithin φ μ₁.parameterSpace x ≠ 0 :=
    fun x hx => derivWithin_ne_zero_of_leftInverse
      ((hφC.differentiableOn (by simp)) x hx)
      ((hψC.differentiableOn (by simp)) (φ x) (hφmaps hx))
      hφmaps (Path.uniqueDiffOn_parameterSpace M μ₁.toPath x hx) hx hψφ
  constructor
  · intro h₁ t ht
    have hs : ψ t ∈ μ₁.parameterSpace := hψmaps ht
    have hiff := μ₁.causalAt_reparam μ₂ (hφmdiff _ hs) hφmaps heq hs (hφderiv _ hs)
    rw [hφψ t ht] at hiff
    exact hiff.mp (h₁ _ hs)
  · intro h₂ s hs
    have hiff := μ₁.causalAt_reparam μ₂ (hφmdiff _ hs) hφmaps heq hs (hφderiv _ hs)
    exact hiff.mpr (h₂ _ (hφmaps hs))

/--
A *timelike smooth curve* is a smooth curve all of whose representative
smooth paths are timelike. Since the timelike condition is invariant under
reparametrisation by an orientation-preserving diffeomorphism but not
orientation-reversing ones — and since the underlying tangent vector
condition `g(v,v) < 0` is invariant under non-zero scaling — we state the
predicate by existential quantification over a representative.
-/
def IsTimelikeSmoothCurve (c : SmoothCurve M) : Prop :=
  ∃ μ : M.SmoothPath, c = SmoothCurve.ofPath M μ ∧ SmoothPath.IsTimelike M μ

/-- A *causal smooth curve* is a smooth curve all of whose representative
smooth paths are causal. -/
def IsCausalSmoothCurve (c : SmoothCurve M) : Prop :=
  ∃ μ : M.SmoothPath, c = SmoothCurve.ofPath M μ ∧ SmoothPath.IsCausal M μ

/-! ### Future and past oriented smooth curves -/

/-- A smooth path is *future-oriented* with respect to a time orientation `t`
if its tangent vector is future-pointing at every parameter point. -/
def SmoothPath.IsFutureOriented (μ : M.SmoothPath) (t : M.TimeOrientation) :
    Prop :=
  ∀ s ∈ μ.parameterSpace, M.IsFuturePointing t (μ.tangent s)

/-- A smooth path is *past-oriented* with respect to a time orientation `t`
if its tangent vector is past-pointing at every parameter point. -/
def SmoothPath.IsPastOriented (μ : M.SmoothPath) (t : M.TimeOrientation) :
    Prop :=
  ∀ s ∈ μ.parameterSpace, M.IsPastPointing t (μ.tangent s)

/-- A *future-oriented smooth curve* is a smooth curve admitting a
future-oriented representative smooth path (relative to a fixed time
orientation `t`). -/
def IsFutureOrientedSmoothCurve (t : M.TimeOrientation) (c : SmoothCurve M) :
    Prop :=
  ∃ μ : M.SmoothPath,
    c = SmoothCurve.ofPath M μ ∧ SmoothPath.IsFutureOriented M μ t

/-- A *past-oriented smooth curve* is a smooth curve admitting a
past-oriented representative smooth path (relative to a fixed time
orientation `t`). -/
def IsPastOrientedSmoothCurve (t : M.TimeOrientation) (c : SmoothCurve M) :
    Prop :=
  ∃ μ : M.SmoothPath,
    c = SmoothCurve.ofPath M μ ∧ SmoothPath.IsPastOriented M μ t

/-- **Reparametrisation-invariance of future-orientedness.** Two smooth paths
related by an orientation-preserving smooth reparametrisation
(`OrientedSmoothPathEquiv`) are future-oriented together: one is future-oriented
iff the other is. The forward direction uses the inverse diffeomorphism `ψ` for
surjectivity; both directions rest on the pointwise `isFuturePointing_reparam`,
with the reparametrisation derivative positive by hypothesis. -/
theorem SmoothPath.isFutureOriented_iff_of_orientedSmoothPathEquiv {M : Spacetime}
    {μ₁ μ₂ : M.SmoothPath} (t : M.TimeOrientation)
    (h : M.OrientedSmoothPathEquiv μ₁ μ₂) :
    SmoothPath.IsFutureOriented M μ₁ t ↔ SmoothPath.IsFutureOriented M μ₂ t := by
  obtain ⟨φ, ψ, hφC, hψC, hφmaps, hψmaps, hψφ, hφψ, heq, hpos⟩ := h
  have hφmdiff : ∀ x ∈ μ₁.parameterSpace,
      MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        φ μ₁.parameterSpace x :=
    fun x hx => mdifferentiableWithinAt_of_contDiffOn hφC hx
  constructor
  · intro h₁ p hp
    have hs : ψ p ∈ μ₁.parameterSpace := hψmaps hp
    have hiff :=
      μ₁.isFuturePointing_reparam μ₂ t (hφmdiff _ hs) hφmaps heq hs (hpos _ hs)
    rw [hφψ p hp] at hiff
    exact hiff.mp (h₁ _ hs)
  · intro h₂ s hs
    have hiff :=
      μ₁.isFuturePointing_reparam μ₂ t (hφmdiff _ hs) hφmaps heq hs (hpos _ hs)
    exact hiff.mpr (h₂ _ (hφmaps hs))

/-- **Reparametrisation-invariance of past-orientedness.** The dual of
`isFutureOriented_iff_of_orientedSmoothPathEquiv`, via `isPastPointing_reparam`. -/
theorem SmoothPath.isPastOriented_iff_of_orientedSmoothPathEquiv {M : Spacetime}
    {μ₁ μ₂ : M.SmoothPath} (t : M.TimeOrientation)
    (h : M.OrientedSmoothPathEquiv μ₁ μ₂) :
    SmoothPath.IsPastOriented M μ₁ t ↔ SmoothPath.IsPastOriented M μ₂ t := by
  obtain ⟨φ, ψ, hφC, hψC, hφmaps, hψmaps, hψφ, hφψ, heq, hpos⟩ := h
  have hφmdiff : ∀ x ∈ μ₁.parameterSpace,
      MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        φ μ₁.parameterSpace x :=
    fun x hx => mdifferentiableWithinAt_of_contDiffOn hφC hx
  constructor
  · intro h₁ p hp
    have hs : ψ p ∈ μ₁.parameterSpace := hψmaps hp
    have hiff :=
      μ₁.isPastPointing_reparam μ₂ t (hφmdiff _ hs) hφmaps heq hs (hpos _ hs)
    rw [hφψ p hp] at hiff
    exact hiff.mp (h₁ _ hs)
  · intro h₂ s hs
    have hiff :=
      μ₁.isPastPointing_reparam μ₂ t (hφmdiff _ hs) hφmaps heq hs (hpos _ hs)
    exact hiff.mpr (h₂ _ (hφmaps hs))

/-! ### Well-definedness of the causal type on smooth curves

Timelikeness and causality are invariant under *any* smooth reparametrisation, so
they descend to genuine predicates on `SmoothCurve` (the quotient by
`SmoothPathEquiv`): a curve is timelike/causal iff any chosen representative is.
The transfer along the quotient uses the equivalence closure of `SmoothPathEquiv`
(via `Quot.eqvGen_exact`) together with the per-reparametrisation iffs. -/

/-- Timelikeness is invariant along the equivalence closure of `SmoothPathEquiv`. -/
theorem SmoothPath.isTimelike_iff_of_eqvGen {M : Spacetime} {μ₁ μ₂ : M.SmoothPath}
    (h : Relation.EqvGen M.SmoothPathEquiv μ₁ μ₂) :
    SmoothPath.IsTimelike M μ₁ ↔ SmoothPath.IsTimelike M μ₂ := by
  induction h with
  | rel x y hxy => exact SmoothPath.isTimelike_iff_of_smoothPathEquiv hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Well-definedness of timelikeness on smooth curves.** A smooth curve is
timelike (has a timelike representative) iff the chosen representative `μ` is
timelike; the value does not depend on the representative. -/
theorem isTimelikeSmoothCurve_ofPath_iff {M : Spacetime} (μ : M.SmoothPath) :
    IsTimelikeSmoothCurve M (SmoothCurve.ofPath M μ) ↔ SmoothPath.IsTimelike M μ := by
  constructor
  · rintro ⟨μ', heq, htl⟩
    exact (SmoothPath.isTimelike_iff_of_eqvGen (Quot.eqvGen_exact heq)).mpr htl
  · intro htl
    exact ⟨μ, rfl, htl⟩

/-- Causality is invariant along the equivalence closure of `SmoothPathEquiv`. -/
theorem SmoothPath.isCausal_iff_of_eqvGen {M : Spacetime} {μ₁ μ₂ : M.SmoothPath}
    (h : Relation.EqvGen M.SmoothPathEquiv μ₁ μ₂) :
    SmoothPath.IsCausal M μ₁ ↔ SmoothPath.IsCausal M μ₂ := by
  induction h with
  | rel x y hxy => exact SmoothPath.isCausal_iff_of_smoothPathEquiv hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Well-definedness of causality on smooth curves.** -/
theorem isCausalSmoothCurve_ofPath_iff {M : Spacetime} (μ : M.SmoothPath) :
    IsCausalSmoothCurve M (SmoothCurve.ofPath M μ) ↔ SmoothPath.IsCausal M μ := by
  constructor
  · rintro ⟨μ', heq, hc⟩
    exact (SmoothPath.isCausal_iff_of_eqvGen (Quot.eqvGen_exact heq)).mpr hc
  · intro hc
    exact ⟨μ, rfl, hc⟩

/-! ### Oriented smooth curves and well-definedness of orientation

The time orientation of a curve (future- vs past-pointing) is *not* invariant under
orientation-reversing reparametrisations, so it does not descend to `SmoothCurve`.
It does descend to the finer quotient by `OrientedSmoothPathEquiv`, which is the
correct home for future/past-oriented curves. -/

/-- An *oriented smooth curve*: an equivalence class of smooth paths under
orientation-preserving reparametrisation. Finer than `SmoothCurve` (which also
allows orientation-reversing reparametrisations), it is the natural domain on which
the time orientation of a curve is well-defined. -/
def OrientedSmoothCurve : Type := Quot M.OrientedSmoothPathEquiv

/-- Every smooth path determines an oriented smooth curve. -/
def OrientedSmoothCurve.ofPath (μ : M.SmoothPath) : OrientedSmoothCurve M :=
  Quot.mk _ μ

/-- An oriented smooth curve is *future-oriented* (relative to a time orientation
`t`) if it admits a future-oriented representative smooth path. -/
def IsFutureOrientedCurve (t : M.TimeOrientation) (c : OrientedSmoothCurve M) :
    Prop :=
  ∃ μ : M.SmoothPath,
    c = OrientedSmoothCurve.ofPath M μ ∧ SmoothPath.IsFutureOriented M μ t

/-- An oriented smooth curve is *past-oriented* (relative to a time orientation
`t`) if it admits a past-oriented representative smooth path. -/
def IsPastOrientedCurve (t : M.TimeOrientation) (c : OrientedSmoothCurve M) :
    Prop :=
  ∃ μ : M.SmoothPath,
    c = OrientedSmoothCurve.ofPath M μ ∧ SmoothPath.IsPastOriented M μ t

/-- Future-orientedness is invariant along the equivalence closure of
`OrientedSmoothPathEquiv`. -/
theorem SmoothPath.isFutureOriented_iff_of_eqvGen {M : Spacetime}
    (t : M.TimeOrientation) {μ₁ μ₂ : M.SmoothPath}
    (h : Relation.EqvGen M.OrientedSmoothPathEquiv μ₁ μ₂) :
    SmoothPath.IsFutureOriented M μ₁ t ↔ SmoothPath.IsFutureOriented M μ₂ t := by
  induction h with
  | rel x y hxy =>
      exact SmoothPath.isFutureOriented_iff_of_orientedSmoothPathEquiv t hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Well-definedness of future-orientedness on oriented smooth curves.** -/
theorem isFutureOrientedCurve_ofPath_iff {M : Spacetime} (t : M.TimeOrientation)
    (μ : M.SmoothPath) :
    IsFutureOrientedCurve M t (OrientedSmoothCurve.ofPath M μ)
      ↔ SmoothPath.IsFutureOriented M μ t := by
  constructor
  · rintro ⟨μ', heq, hfo⟩
    exact (SmoothPath.isFutureOriented_iff_of_eqvGen t (Quot.eqvGen_exact heq)).mpr hfo
  · intro hfo
    exact ⟨μ, rfl, hfo⟩

/-- Past-orientedness is invariant along the equivalence closure of
`OrientedSmoothPathEquiv`. -/
theorem SmoothPath.isPastOriented_iff_of_eqvGen {M : Spacetime}
    (t : M.TimeOrientation) {μ₁ μ₂ : M.SmoothPath}
    (h : Relation.EqvGen M.OrientedSmoothPathEquiv μ₁ μ₂) :
    SmoothPath.IsPastOriented M μ₁ t ↔ SmoothPath.IsPastOriented M μ₂ t := by
  induction h with
  | rel x y hxy =>
      exact SmoothPath.isPastOriented_iff_of_orientedSmoothPathEquiv t hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Well-definedness of past-orientedness on oriented smooth curves.** -/
theorem isPastOrientedCurve_ofPath_iff {M : Spacetime} (t : M.TimeOrientation)
    (μ : M.SmoothPath) :
    IsPastOrientedCurve M t (OrientedSmoothCurve.ofPath M μ)
      ↔ SmoothPath.IsPastOriented M μ t := by
  constructor
  · rintro ⟨μ', heq, hpo⟩
    exact (SmoothPath.isPastOriented_iff_of_eqvGen t (Quot.eqvGen_exact heq)).mpr hpo
  · intro hpo
    exact ⟨μ, rfl, hpo⟩

/-! ### Endpoints -/

/--
A point `p` of a spacetime `M` is an *endpoint* of a path `μ : Σ → M` if it
lies in the image of the topological frontier of `Σ` (i.e. its boundary
`∂Σ` in `ℝ`) under `μ`.
-/
def IsEndpoint (μ : M.Path) (p : M.Carrier) : Prop :=
  ∃ s ∈ frontier μ.parameterSpace, μ.toFun s = p

/--
For a smooth path `μ` whose associated smooth curve is timelike and
future-oriented, a *past endpoint* is the image under `μ` of the lesser of
the two boundary components of `∂Σ`.

We capture this as: there exists a value `s ∈ Σ` such that every other
`s' ∈ Σ` satisfies `s ≤ s'`, and `μ s = p`. Quantifying over the parameter
space (rather than its frontier `∂Σ`) ensures the witness is a genuine
minimum of `Σ`, which on a closed connected `Σ ⊆ ℝ` forces `Σ` to be
bounded below; together with `IsFutureEndpoint` this excludes half-lines and
pins `Σ` down to a compact closed interval `[a, b]`.
-/
def IsPastEndpoint (μ : M.SmoothPath) (p : M.Carrier) : Prop :=
  ∃ s ∈ μ.parameterSpace,
    μ.toFun s = p ∧
    (∀ s' ∈ μ.parameterSpace, s ≤ s')

/--
For a smooth path `μ` whose associated smooth curve is timelike and
future-oriented, a *future endpoint* is the image under `μ` of the greater
of the two boundary components of `∂Σ`. Quantifying over the parameter
space (rather than `∂Σ`) ensures the witness is a genuine maximum, forcing
boundedness above; see `IsPastEndpoint` for the dual.
-/
def IsFutureEndpoint (μ : M.SmoothPath) (p : M.Carrier) : Prop :=
  ∃ s ∈ μ.parameterSpace,
    μ.toFun s = p ∧
    (∀ s' ∈ μ.parameterSpace, s' ≤ s)

end Spacetime

end Physicslib4
