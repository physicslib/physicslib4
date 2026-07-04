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
import Mathlib.Geometry.Manifold.MFDeriv.Basic
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

/-- A smooth path is timelike if its tangent vector is timelike at every
point of the parameter space. -/
def SmoothPath.IsTimelike (μ : M.SmoothPath) : Prop :=
  ∀ s ∈ μ.parameterSpace, M.IsTimelike (μ.tangent s)

/-- A smooth path is *causal* if its tangent vector is either timelike or
null at every point of the parameter space. -/
def SmoothPath.IsCausal (μ : M.SmoothPath) : Prop :=
  ∀ s ∈ μ.parameterSpace,
    M.IsTimelike (μ.tangent s) ∨ M.IsNull (μ.tangent s)

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
