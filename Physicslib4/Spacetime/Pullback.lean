/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Diffeo
import Physicslib4.Spacetime.Isometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Pullback of a spacetime metric along a diffeomorphism

This file formalises the first half of the blueprint subsection
*Pullback metrics and cross-metric isometries* (section 10.2 of the
AQFT-in-Lean blueprint): the pullback metric `ψ^*g`, the fact that it is again
a spacetime metric, and the pullback of a time orientation together with the
two-sided transport of future-pointing-ness.

The cross-metric isometry theory built on top of this lives in
`Physicslib4/Spacetime/CrossMetricIsometry.lean`.

The purely differential-geometric input — the type `Physicslib4.Spacetime.Diffeo`
of `C^⊤` diffeomorphisms, the differential `mfderivEquiv` as a continuous linear
equivalence, the round-trip cancellations and the formal inverse — lives in
`Physicslib4/Spacetime/Diffeo.lean`, which mentions no metric and is therefore
imported by the single-metric isometry theory as well.

## Main definitions

* `Physicslib4.Spacetime.pullbackVal` (`def:pullback-metric`): the field of
  continuous bilinear forms `(ψ^*g)_x = g_{ψ x}(dψ_x ·, dψ_x ·)`, realised as an
  inhabitant of the bundled type via `ContinuousLinearMap.bilinearComp`.
* `Physicslib4.Spacetime.pullback` (`thrm:pullback-is-spacetime`): the pullback
  spacetime `ψ^*(M,g)`, keeping all manifold data of `M` and replacing the
  metric by `pullbackVal`.
* `Physicslib4.Spacetime.PreservesFutureOrientation` and
  `PreservesFutureOrientationTwoSided` (`def:preserves-future-orientation`):
  the cross-metric orientation conditions on a bare diffeomorphism, generalising
  the single-metric `Isometry.PreservesFutureOrientation`.
* `Physicslib4.Spacetime.pullbackTimeOrientation`
  (`lmm:pullback-time-orientation`): the pullback time orientation
  `ψ^*t = (dψ_x)⁻¹ t_{ψ x}`, i.e. `VectorField.mpullback`.

## Modelling notes

The blueprint states the pullback only for a diffeomorphism `ψ : M → M` of one
spacetime. The purely differential-geometric statements are stated in
`Physicslib4/Spacetime/Diffeo.lean` for a diffeomorphism between the manifolds
of two spacetimes, since the cross-metric isometry theory downstream needs
exactly that generality and the single-spacetime case is the instance `N := M`.
The genuinely metric-level constructions (`pullbackVal`, `pullback`,
`pullbackTimeOrientation`) are stated for `ψ : Diffeo M M`, matching the
blueprint.
-/

namespace Physicslib4

namespace Spacetime

open scoped Manifold

variable {M N : Spacetime}

/-! ### The pullback metric -/

/-- Two-slot precomposition of a continuous bilinear form on the model space
`ℝ⁴` with a continuous linear map, i.e. `ContinuousLinearMap.bilinearComp` read
on `SpacetimeModel`.

This auxiliary step is needed because `Mathlib`'s `bilinearComp` requires
`SeminormedAddCommGroup` instances on its source spaces, while
`TangentSpace I x` is *not reducible* and carries only topological-module
instances; the two families of instances are definitionally equal, so the
form is built on the model space and transported to the tangent spaces in
`pullbackVal` (exactly the device used for the constant metric in
`Physicslib4/Spacetime/Minkowski.lean`). -/
noncomputable def bilinearPrecomp (g : SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)
    (A : SpacetimeModel →L[ℝ] SpacetimeModel) :
    SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ :=
  g.bilinearComp A A

@[simp] theorem bilinearPrecomp_apply (g : SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)
    (A : SpacetimeModel →L[ℝ] SpacetimeModel) (v w : SpacetimeModel) :
    bilinearPrecomp g A v w = g (A v) (A w) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
**The pullback of a spacetime metric** (`def:pullback-metric`).

`(ψ^*g)_x(v,w) = g_{ψ x}(dψ_x v, dψ_x w)`, realised as an inhabitant of the
bundled type `T_xM →L[ℝ] T_xM →L[ℝ] ℝ` by precomposing `g_{ψ x}` with `dψ_x` in
both slots (`bilinearPrecomp`, i.e. `ContinuousLinearMap.bilinearComp`).
Continuity and bilinearity are then structural rather than facts to be proved,
and `pullbackVal_apply` recovers the displayed formula.

This node is data only; that `ψ^*g` satisfies the metric obligations of
`def:spacetime` is `Physicslib4.Spacetime.pullback`.
-/
noncomputable def pullbackVal (M : Spacetime) (ψ : Diffeo M M) (x : M.Carrier) :
    TangentSpace M.model x →L[ℝ] TangentSpace M.model x →L[ℝ] ℝ :=
  bilinearPrecomp (M.val (ψ x)) (mfderiv M.model M.model ψ x)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem pullbackVal_apply (M : Spacetime) (ψ : Diffeo M M) (x : M.Carrier)
    (v w : TangentSpace M.model x) :
    M.pullbackVal ψ x v w
      = M.val (ψ x) (mfderiv M.model M.model ψ x v) (mfderiv M.model M.model ψ x w) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The pullback metric is symmetric** (`lmm:pullback-metric-symm`). -/
theorem pullbackVal_symm (M : Spacetime) (ψ : Diffeo M M) (x : M.Carrier)
    (v w : TangentSpace M.model x) :
    M.pullbackVal ψ x v w = M.pullbackVal ψ x w v := by
  rw [pullbackVal_apply, pullbackVal_apply]
  exact M.symm (ψ x) (mfderiv M.model M.model ψ x v) (mfderiv M.model M.model ψ x w)

/-- **The pullback metric is non-degenerate**
(`lmm:pullback-metric-nondegenerate`): if `(ψ^*g)_x(v,w) = 0` for all `w` then
`v = 0`. -/
theorem pullbackVal_nondegenerate (M : Spacetime) (ψ : Diffeo M M) (x : M.Carrier)
    (v : TangentSpace M.model x) (h : ∀ w : TangentSpace M.model x,
      M.pullbackVal ψ x v w = 0) : v = 0 := by
  have hnd : mfderiv M.model M.model ψ x v = 0 := by
    apply M.nondegenerate (ψ x)
    intro u
    have hw := h ((mfderivEquiv ψ x).symm u)
    rw [pullbackVal_apply] at hw
    simpa [mfderiv_eq_mfderivEquiv, ContinuousLinearEquiv.apply_symm_apply] using hw
  rw [← mfderivEquiv_coe ψ x] at hnd
  exact (ContinuousLinearEquiv.map_eq_zero_iff (e := mfderivEquiv ψ x)).mp hnd

set_option backward.isDefEq.respectTransparency false in
/-- **The pullback metric is Lorentzian** (`lmm:pullback-metric-lorentzian`):
at every `x` there is a basis of `T_xM` whose Gram matrix under `(ψ^*g)_x` is
`diag(-1,1,1,1)`. The signature basis is transported from `T_{ψ x}M` along the
inverse of `mfderivEquiv` by `Module.Basis.map`; this is where the *existential*
formulation of the Lorentzian condition in `def:spacetime` is essential. -/
theorem pullbackVal_lorentzian (M : Spacetime) (ψ : Diffeo M M) (x : M.Carrier) :
    LorentzianAt (fun v w : TangentSpace M.model x => M.pullbackVal ψ x v w) := by
  change ∃ b : Module.Basis (Fin 4) ℝ (TangentSpace M.model x),
    ∀ i j : Fin 4, M.pullbackVal ψ x (b i) (b j) = lorentzSignature i j
  rcases M.lorentzian (ψ x) with ⟨b, hb⟩
  refine ⟨b.map ((mfderivEquiv ψ x).symm :
      TangentSpace M.model (ψ x) ≃ₗ[ℝ] TangentSpace M.model x), ?_⟩
  intro i j
  rw [pullbackVal_apply]
  simpa [Module.Basis.map_apply, mfderiv_eq_mfderivEquiv,
    ContinuousLinearEquiv.apply_symm_apply] using hb i j

/--
**The pullback metric is a smooth section of the bilinear-form bundle**
(`lmm:pullback-metric-smooth-in-charts`).

The `contMDiff` field of `def:spacetime` for `ψ^*g`, at the same regularity
index `⊤ = ω` as `Spacetime.contMDiff` itself. The label name is historical: the
statement is entirely in the bundle-section idiom and nothing chart-local
remains.
-/
theorem pullbackVal_contMDiff (M : Spacetime) (ψ : Diffeo M M) :
    ContMDiff M.model
      (M.model.prod 𝓘(ℝ, SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)) ⊤
      (fun x ↦ Bundle.TotalSpace.mk'
        (SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)
        (E := fun x ↦ TangentSpace M.model x →L[ℝ] TangentSpace M.model x →L[ℝ] ℝ)
        x (M.pullbackVal ψ x)) := by
  sorry

/--
**The pullback of a spacetime is a spacetime** (`thrm:pullback-is-spacetime`).

`ψ^*(M,g)` keeps the carrier set, topology, Hausdorff and connectedness
properties, charts, model with corners, smooth structure and tangent-space
finite-dimensionality of `(M,g)` unchanged, and replaces the metric field by
`pullbackVal`. The four metric obligations are discharged by
`pullbackVal_symm`, `pullbackVal_nondegenerate`, `pullbackVal_lorentzian` and
`pullbackVal_contMDiff`.
-/
noncomputable def pullback (M : Spacetime) (ψ : Diffeo M M) : Spacetime :=
  { M with
    val := M.pullbackVal ψ
    symm := M.pullbackVal_symm ψ
    nondegenerate := fun x v h => M.pullbackVal_nondegenerate ψ x v h
    lorentzian := M.pullbackVal_lorentzian ψ
    contMDiff := M.pullbackVal_contMDiff ψ }

/-- The carrier of the pullback spacetime is that of `M`. Deliberately not
`@[simp]`: this is an equality of `Type`s, so rewriting with it inside a
dependent goal produces motive-correctness failures rather than progress; the
two carriers are definitionally equal and should be used as such. -/
theorem pullback_Carrier (M : Spacetime) (ψ : Diffeo M M) :
    (M.pullback ψ).Carrier = M.Carrier := rfl

@[simp] theorem pullback_model (M : Spacetime) (ψ : Diffeo M M) :
    (M.pullback ψ).model = M.model := rfl

@[simp] theorem pullback_val (M : Spacetime) (ψ : Diffeo M M) :
    (M.pullback ψ).val = M.pullbackVal ψ := rfl

/-- `ψ` regarded as a diffeomorphism from the pullback spacetime to `M`. The two
types are definitionally equal, since `pullback` changes only the metric field;
this is the coercion used whenever `ψ` has to be read cross-metric. -/
def pullbackDiffeo (M : Spacetime) (ψ : Diffeo M M) : Diffeo (M.pullback ψ) M := ψ

/-! ### Two-sided preservation of the future orientation -/

/--
**Preservation of the future orientation, cross-metric**
(`def:preserves-future-orientation`, one-sided half).

A diffeomorphism `ψ` from the manifold of `M` (with time orientation `t₁`) to
that of `N` (with time orientation `t₂`) *preserves the future orientation* when
`dψ_x` carries vectors that are future-pointing for `(g₁,t₁)` to vectors that are
future-pointing for `(g₂,t₂)`.

Nothing here refers to the metrics beyond the two orientations, so this is a
condition on a diffeomorphism and a pair of oriented metrics, stated
independently of any isometry hypothesis. The single-metric case `N = M`,
`t₂ = t₁` is `Isometry.PreservesFutureOrientation`.
-/
def PreservesFutureOrientation (ψ : Diffeo M N) (t₁ : M.TimeOrientation)
    (t₂ : N.TimeOrientation) : Prop :=
  ∀ (x : M.Carrier) (v : TangentSpace M.model x),
    M.IsFuturePointing t₁ v →
      N.IsFuturePointing t₂ (mfderiv M.model N.model ψ x v)

/--
**The two-sided orientation hypothesis** (`def:preserves-future-orientation`):
both `ψ` preserves the future orientation from `(g₁,t₁)` to `(g₂,t₂)` and `ψ⁻¹`
preserves it from `(g₂,t₂)` back to `(g₁,t₁)`.
-/
def PreservesFutureOrientationTwoSided (ψ : Diffeo M N) (t₁ : M.TimeOrientation)
    (t₂ : N.TimeOrientation) : Prop :=
  PreservesFutureOrientation ψ t₁ t₂ ∧ PreservesFutureOrientation ψ.symm t₂ t₁

/-! ### The pullback time orientation -/

/--
**The pullback of a bundle-smooth vector field along a diffeomorphism is
bundle-smooth** (`lmm:mpullback-vectorField-contMDiff-of-diffeo`).

The hypothesis `hV` is literally the `smooth` field of
`Spacetime.TimeOrientation`, and the conclusion is literally the `smooth` field
to be produced for `ψ^*t`, so no conversion happens on either side. This is
`ContMDiff.mpullback_vectorField`, whose `hf'` hypothesis is supplied by
`isInvertible_mfderiv` and whose exponent gap `⊤ + 1 ≤ ⊤` is `le_top`.

Following the policy of the module docstring, and matching the generality of
`ContMDiff.mpullback_vectorField` itself, this is stated for a diffeomorphism
between the manifolds of two spacetimes; the blueprint's case is the instance
`N := M`, used by `pullbackTimeOrientation`.
-/
theorem contMDiff_mpullback_vectorField
    (ψ : Diffeo M N) (V : ∀ x : N.Carrier, TangentSpace N.model x)
    (hV : ContMDiff N.model N.model.tangent ⊤
      (fun x ↦ Bundle.TotalSpace.mk' SpacetimeModel
        (E := fun x ↦ TangentSpace N.model x) x (V x))) :
    ContMDiff M.model M.model.tangent ⊤
      (fun x ↦ Bundle.TotalSpace.mk' SpacetimeModel
        (E := fun x ↦ TangentSpace M.model x) x
        (VectorField.mpullback M.model N.model ψ V x)) := by
  exact ContMDiff.mpullback_vectorField
    (I := M.model) (I' := N.model)
    (m := ⊤) (n := ⊤)
    (f := (ψ : M.Carrier → N.Carrier))
    (V := V)
    hV
    (Diffeomorph.contMDiff ψ)
    (fun x => isInvertible_mfderiv ψ x)
    le_top

/-- **The pullback time orientation is nowhere vanishing**
(`lmm:pullback-time-orientation-ne-zero`): `(ψ^*t)_x = (dψ_x)⁻¹ t_{ψ x} ≠ 0`.
This needs `inverse_mfderiv_eq_symm`: off the invertible case
`ContinuousLinearMap.inverse` returns the junk value `0` and is not
injective. -/
theorem mpullback_field_ne_zero (M : Spacetime) (ψ : Diffeo M M)
    (t : M.TimeOrientation) (x : M.Carrier) :
    VectorField.mpullback M.model M.model ψ t.field x ≠ 0 := by
  rw [VectorField.mpullback]
  rw [inverse_mfderiv_eq_symm ψ x]
  intro h
  have hz : t.field (ψ x) = 0 :=
    (ContinuousLinearEquiv.map_eq_zero_iff (mfderivEquiv ψ x).symm).mp h
  exact (t.nonvanishing (ψ x)) hz

/-- The metric square of the pullback time orientation is the metric square of
`t` at the image point (`lmm:pullback-time-orientation-timelike`, equation
part):
`(ψ^*g)_x((ψ^*t)_x, (ψ^*t)_x) = g_{ψ x}(t_{ψ x}, t_{ψ x})`. -/
theorem pullbackVal_mpullback_field_self (M : Spacetime) (ψ : Diffeo M M)
    (t : M.TimeOrientation) (x : M.Carrier) :
    M.pullbackVal ψ x (VectorField.mpullback M.model M.model ψ t.field x)
        (VectorField.mpullback M.model M.model ψ t.field x)
      = M.val (ψ x) (t.field (ψ x)) (t.field (ψ x)) := by
  simp [VectorField.mpullback]

/-- **The pullback time orientation is everywhere timelike**
(`lmm:pullback-time-orientation-timelike`). -/
theorem isTimelike_mpullback_field (M : Spacetime) (ψ : Diffeo M M)
    (t : M.TimeOrientation) (x : M.Carrier) :
    (M.pullback ψ).IsTimelike
      (VectorField.mpullback M.model M.model ψ t.field x) := by
  unfold IsTimelike
  change M.pullbackVal ψ x (VectorField.mpullback M.model M.model ψ t.field x)
      (VectorField.mpullback M.model M.model ψ t.field x) < 0
  rw [pullbackVal_mpullback_field_self]
  exact t.timelike_at (ψ x)

/--
**Pullback of a time orientation** (`lmm:pullback-time-orientation`).

`ψ^*t : x ↦ (dψ_x)⁻¹ t_{ψ x}`, which is Mathlib's `VectorField.mpullback`, is a
time orientation of the pullback spacetime: smoothness is
`contMDiff_mpullback_vectorField` applied at `V = t.field`, non-vanishing is
`mpullback_field_ne_zero` and timelikeness is `isTimelike_mpullback_field`.
-/
noncomputable def pullbackTimeOrientation (M : Spacetime) (ψ : Diffeo M M)
    (t : M.TimeOrientation) : (M.pullback ψ).TimeOrientation where
  field := VectorField.mpullback M.model M.model ψ t.field
  nonvanishing := M.mpullback_field_ne_zero ψ t
  timelike_at := M.isTimelike_mpullback_field ψ t
  smooth := contMDiff_mpullback_vectorField ψ t.field t.smooth

@[simp] theorem pullbackTimeOrientation_field (M : Spacetime) (ψ : Diffeo M M)
    (t : M.TimeOrientation) :
    (M.pullbackTimeOrientation ψ t).field
      = VectorField.mpullback M.model M.model ψ t.field := rfl

/-- The mixed metric identity underlying the transport of future-pointing-ness
(`lmm:pullback-future-pointing-timelike`, equation part):
`(ψ^*g)_x((ψ^*t)_x, v) = g_{ψ x}(t_{ψ x}, dψ_x v)`. -/
theorem pullbackVal_mpullback_field_apply (M : Spacetime) (ψ : Diffeo M M)
    (t : M.TimeOrientation) (x : M.Carrier) (v : TangentSpace M.model x) :
    M.pullbackVal ψ x (VectorField.mpullback M.model M.model ψ t.field x) v
      = M.val (ψ x) (t.field (ψ x)) (mfderiv M.model M.model ψ x v) := by
  rw [pullbackVal_apply]
  simp [VectorField.mpullback]

/-- **Transport of future-pointing timelike vectors**
(`lmm:pullback-future-pointing-timelike`). For `v` timelike for `ψ^*g`, `v` is
future-pointing for `(ψ^*g, ψ^*t)` if and only if `dψ_x v` is future-pointing
for `(g,t)`. -/
theorem isFuturePointing_pullback_iff_of_isTimelike (M : Spacetime) (ψ : Diffeo M M)
    (t : M.TimeOrientation) {x : M.Carrier} {v : TangentSpace M.model x}
    (hv : (M.pullback ψ).IsTimelike v) :
    (M.pullback ψ).IsFuturePointing (M.pullbackTimeOrientation ψ t) v
      ↔ M.IsFuturePointing t (mfderiv M.model M.model ψ x v) := by
  have hw : M.IsTimelike (mfderiv M.model M.model ψ x v) := by
    change M.val (ψ x) (mfderiv M.model M.model ψ x v) (mfderiv M.model M.model ψ x v) < 0
    rw [← pullbackVal_apply, ← pullback_val]
    exact hv
  have hEq : (M.pullback ψ).val x ((M.pullbackTimeOrientation ψ t).field x) v
      = M.val (ψ x) (t.field (ψ x)) (mfderiv M.model M.model ψ x v) := by
    rw [pullback_val, pullbackTimeOrientation_field]
    exact pullbackVal_mpullback_field_apply M ψ t x v
  unfold IsFuturePointing
  constructor
  · intro h
    rcases h with h | h
    · rcases h with ⟨_, hI⟩
      exact Or.inl ⟨hw, by rw [hEq] at hI; exact hI⟩
    · exfalso
      exact M.not_isNull_of_isTimelike hv h.1
  · intro h
    rcases h with h | h
    · rcases h with ⟨_, hI⟩
      exact Or.inl ⟨hv, by rw [← hEq] at hI; exact hI⟩
    · exfalso
      exact M.not_isNull_of_isTimelike hw h.1

/-- **Transport of future-pointing null vectors**
(`lmm:pullback-future-pointing-null`). For `v` null for `ψ^*g` the condition is
not a sign condition but the existence of an approximating sequence of
future-pointing timelike vectors, so the witnessing sequence is transported
along the continuous linear map `dψ_x` (and back along its inverse). -/
theorem isFuturePointing_pullback_iff_of_isNull (M : Spacetime) (ψ : Diffeo M M)
    (t : M.TimeOrientation) {x : M.Carrier} {v : TangentSpace M.model x}
    (hv : (M.pullback ψ).IsNull v) :
    (M.pullback ψ).IsFuturePointing (M.pullbackTimeOrientation ψ t) v
      ↔ M.IsFuturePointing t (mfderiv M.model M.model ψ x v) := by
  -- `v` is null for the pullback metric iff `dψ_x v` is null for `g`, so the
  -- timelike disjunct is excluded on both sides and the content is the
  -- approximating-sequence disjunct, transported along `dψ_x` and its inverse.
  have hv' : M.IsNull (mfderiv M.model M.model ψ x v) := by
    change M.val (ψ x) (mfderiv M.model M.model ψ x v) (mfderiv M.model M.model ψ x v) = 0
    unfold IsNull at hv
    rw [pullback_val] at hv
    exact (pullbackVal_apply M ψ x v v) ▸ hv
  -- Transport of the per-term timelikeness conditions.
  have htl_trans : ∀ {u : TangentSpace M.model x}, (M.pullback ψ).IsTimelike u →
      M.IsTimelike (mfderiv M.model M.model ψ x u) := by
    intro u hu
    unfold IsTimelike at hu ⊢
    rw [pullback_val] at hu
    exact (pullbackVal_apply M ψ x u u) ▸ hu
  -- The formal inverse `(dψ_x)⁻¹`, identified with `(mfderivEquiv ψ x).symm` by
  -- `inverse_mfderiv_eq_symm`; it is a continuous linear map, so it transports
  -- the witnessing sequence back to the pullback side.
  let di : TangentSpace M.model (ψ x) →L[ℝ] TangentSpace M.model x :=
    ContinuousLinearMap.inverse (mfderiv M.model M.model ψ x)
  have htl_rev : ∀ {w : TangentSpace M.model (ψ x)}, M.IsTimelike w →
      (M.pullback ψ).IsTimelike (di w) := by
    intro w hw
    unfold IsTimelike at hw ⊢
    rw [pullback_val]
    have hm : M.val (ψ x) (mfderiv M.model M.model ψ x (di w))
        (mfderiv M.model M.model ψ x (di w)) < 0 := by
      dsimp [di]
      rw [mfderiv_apply_inverse_mfderiv]
      exact hw
    exact (pullbackVal_apply M ψ x (di w) (di w)).symm ▸ hm
  -- Transport of the per-term sign conditions `g_{ψ x}(t_{ψ x}, ·) < 0`.
  have hsign_trans : ∀ {u : TangentSpace M.model x},
      (M.pullback ψ).val x ((M.pullbackTimeOrientation ψ t).field x) u < 0 →
      M.val (ψ x) (t.field (ψ x)) (mfderiv M.model M.model ψ x u) < 0 := by
    intro u hu
    rw [pullback_val, pullbackTimeOrientation_field] at hu
    exact (pullbackVal_mpullback_field_apply M ψ t x u) ▸ hu
  have hsign_rev : ∀ {w : TangentSpace M.model (ψ x)},
      M.val (ψ x) (t.field (ψ x)) w < 0 →
      (M.pullback ψ).val x ((M.pullbackTimeOrientation ψ t).field x) (di w) < 0 := by
    intro w hw
    rw [pullback_val, pullbackTimeOrientation_field]
    have hm : M.val (ψ x) (t.field (ψ x))
        (mfderiv M.model M.model ψ x (di w)) < 0 := by
      dsimp [di]
      rw [mfderiv_apply_inverse_mfderiv]
      exact hw
    exact (pullbackVal_mpullback_field_apply M ψ t x (di w)) ▸ hm
  constructor
  · intro h
    rcases h with htl | hnull
    · exfalso
      exact (M.pullback ψ).not_isNull_of_isTimelike htl.1 hv
    · rcases hnull with ⟨_, vs, hvs, htends⟩
      refine Or.inr ⟨hv', fun n => mfderiv M.model M.model ψ x (vs n), ?_, ?_⟩
      · intro n
        exact ⟨htl_trans (hvs n).1, hsign_trans (hvs n).2⟩
      · exact ((ContinuousLinearMap.continuous (mfderiv M.model M.model ψ x)).tendsto v).comp htends
  · intro h
    rcases h with htl | hnull
    · exfalso
      exact M.not_isNull_of_isTimelike htl.1 hv'
    · rcases hnull with ⟨_, us, hus, hutends⟩
      refine Or.inr ⟨hv, fun n => di (us n), ?_, ?_⟩
      · intro n
        exact ⟨htl_rev (hus n).1, hsign_rev (hus n).2⟩
      · have htarget : di (mfderiv M.model M.model ψ x v) = v := by
          dsimp [di]
          exact inverse_mfderiv_apply_mfderiv ψ x v
        change Filter.Tendsto (di ∘ us) Filter.atTop (nhds v)
        rw [← htarget]
        exact ((ContinuousLinearMap.continuous di).tendsto
            (mfderiv M.model M.model ψ x v)).comp hutends

set_option backward.isDefEq.respectTransparency false in
/--
**The pullback preserves the future orientation two-sidedly**
(`lmm:pullback-preserves-future-orientation`).

`ψ`, regarded as carrying `(ψ^*g, ψ^*t)` to `(g,t)`, satisfies the two-sided
orientation hypothesis of `def:preserves-future-orientation`. A future-pointing
vector is timelike or null, and each of the two transport lemmas above is an
*equivalence*, so it yields both the forward direction for `ψ` and the forward
direction for `ψ⁻¹`; the `ψ⁻¹` half is where `mfderiv_symm_cancel_left` is
spent.
-/
theorem pullback_preservesFutureOrientationTwoSided (M : Spacetime) (ψ : Diffeo M M)
    (t : M.TimeOrientation) :
    PreservesFutureOrientationTwoSided (M.pullbackDiffeo ψ)
      (M.pullbackTimeOrientation ψ t) t := by
  constructor
  · intro x v hv
    rcases hv with ⟨htl, hsign⟩ | ⟨hnl, hseq⟩
    · exact (M.isFuturePointing_pullback_iff_of_isTimelike ψ t htl).mp
        (Or.inl ⟨htl, hsign⟩)
    · exact (M.isFuturePointing_pullback_iff_of_isNull ψ t hnl).mp
        (Or.inr ⟨hnl, hseq⟩)
  · intro y u hu
    have hm : mfderiv M.model M.model ψ (ψ.symm y)
        (mfderiv M.model M.model ψ.symm y u) = u := by
      have hc := mfderiv_symm_cancel_left ψ (ψ.symm y) u
      rw [ψ.apply_symm_apply y] at hc
      exact hc
    rcases hu with ⟨htl, hsign⟩ | ⟨hnl, hseq⟩
    · exact (M.isFuturePointing_pullback_iff_of_isTimelike ψ t
          (by
            change M.pullbackVal ψ (ψ.symm y)
                (mfderiv M.model M.model ψ.symm y u)
                (mfderiv M.model M.model ψ.symm y u) < 0
            rw [pullbackVal_apply, hm]
            rw [ψ.apply_symm_apply y]
            exact htl)).mpr (by
          change M.IsFuturePointing t
              (mfderiv M.model M.model ψ (ψ.symm y)
                (mfderiv M.model M.model ψ.symm y u))
          rw [hm]
          rw [ψ.apply_symm_apply y]
          exact Or.inl ⟨htl, hsign⟩)
    · exact (M.isFuturePointing_pullback_iff_of_isNull ψ t
          (by
            change M.pullbackVal ψ (ψ.symm y)
                (mfderiv M.model M.model ψ.symm y u)
                (mfderiv M.model M.model ψ.symm y u) = 0
            rw [pullbackVal_apply, hm]
            rw [ψ.apply_symm_apply y]
            exact hnl)).mpr (by
          change M.IsFuturePointing t
              (mfderiv M.model M.model ψ (ψ.symm y)
                (mfderiv M.model M.model ψ.symm y u))
          rw [hm]
          rw [ψ.apply_symm_apply y]
          exact Or.inr ⟨hnl, hseq⟩)

end Spacetime

end Physicslib4
