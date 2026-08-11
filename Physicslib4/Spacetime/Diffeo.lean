/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.CausalStructure
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Diffeomorphisms of spacetime manifolds and their differentials

This file collects the purely differential-geometric material about a `C^⊤`
diffeomorphism `ψ` between the manifolds underlying two spacetimes: that its
differential `dψ_x` is a continuous linear equivalence, the two round-trip
cancellations against the differential of the global inverse, and the
identification of the *formal* inverse `ContinuousLinearMap.inverse (dψ_x)`.

**No metric appears anywhere in this file.** That is exactly why it sits below
`Physicslib4/Spacetime/Isometry.lean` in the import graph: the single-metric
theory there uses these identities (through `Isometry.toDiffeo`) and must not
re-prove them, and the pullback-metric theory of
`Physicslib4/Spacetime/Pullback.lean` uses them again cross-metric.

## Main definitions

* `Physicslib4.Spacetime.Diffeo`: the type of `C^⊤` diffeomorphisms between the
  underlying manifolds of two spacetimes.
* `Physicslib4.Spacetime.mfderivEquiv` (`lmm:mfderiv-diffeo-linear-equiv`): the
  differential `dψ_x` as a continuous linear equivalence, a thin wrapper around
  Mathlib's `Diffeomorph.mfderivToContinuousLinearEquiv`.

## Modelling notes

Everything is stated for a diffeomorphism between the manifolds of *two*
spacetimes. The blueprint's case is a diffeomorphism of a single `M`, which is
the instance `N := M`; the extra generality costs nothing and is what the
cross-metric theory downstream needs.

Note that `Diffeomorph.mfderivToContinuousLinearEquiv` is *not* built from the
global inverse `ψ.symm`, so its `symm` is not definitionally
`mfderiv ψ.symm (ψ x)`. The two are separated here exactly as in the blueprint:
`inverse_mfderiv_eq_symm` (and the two cancellations derived from it) is about
`ContinuousLinearMap.inverse (dψ_x)`, the formal inverse written into
`VectorField.mpullback`, while `mfderiv_symm_cancel_left` and
`mfderiv_symm_cancel_right` are about `mfderiv ψ.symm`.
-/

namespace Physicslib4

namespace Spacetime

open scoped Manifold

/-- The `C^⊤` diffeomorphisms from the manifold underlying the spacetime `M` to
the manifold underlying the spacetime `N`. For `N = M` this is the type of
diffeomorphisms `ψ` of `M` that the blueprint pulls back along. -/
abbrev Diffeo (M N : Spacetime) : Type _ :=
  Diffeomorph M.model N.model M.Carrier N.Carrier ⊤

variable {M N : Spacetime}

/-! ### The differential of a diffeomorphism -/

/--
**The differential of a diffeomorphism is a linear equivalence**
(`lmm:mfderiv-diffeo-linear-equiv`).

`dψ_x : T_xM → T_{ψ x}N` packaged as a continuous linear equivalence. This is
Mathlib's `Diffeomorph.mfderivToContinuousLinearEquiv` at the smoothness index
`⊤ ≠ 0`; the wrapper exists only to fix that side condition once.

Beware: this deliberately claims *only* that `dψ_x` is an isomorphism, and does
**not** identify its `symm` with `d(ψ⁻¹)_{ψ x}`; see the module docstring.
-/
noncomputable def mfderivEquiv (ψ : Diffeo M N) (x : M.Carrier) :
    TangentSpace M.model x ≃L[ℝ] TangentSpace N.model (ψ x) :=
  ψ.mfderivToContinuousLinearEquiv (by simp) x

/-- The underlying continuous linear map of `mfderivEquiv` is `dψ_x`. -/
theorem mfderivEquiv_coe (ψ : Diffeo M N) (x : M.Carrier) :
    ((mfderivEquiv ψ x : TangentSpace M.model x →L[ℝ] TangentSpace N.model (ψ x)))
      = mfderiv M.model N.model ψ x := by
  exact Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := ψ) (hn := by simp) (x := x)

/-- `mfderivEquiv_coe` read in the direction that *exposes* the equivalence,
i.e. replacing the bare `mfderiv` by the invertible packaging in order to reach
`ContinuousLinearEquiv.symm_apply_apply` and
`ContinuousLinearEquiv.apply_symm_apply`.

This is deliberately **not** `@[simp]`: `mfderiv` is the simp-normal form of the
differential throughout this development (every statement downstream is phrased
in it, and the `@[simp]` cancellations `inverse_mfderiv_apply_mfderiv` and
`mfderiv_apply_inverse_mfderiv` have `mfderiv` in their left-hand sides), so it
has to be rewritten by hand where the equivalence packaging is wanted. -/
theorem mfderiv_eq_mfderivEquiv (ψ : Diffeo M N) (x : M.Carrier) :
    mfderiv M.model N.model ψ x
      = ((mfderivEquiv ψ x : TangentSpace M.model x →L[ℝ] TangentSpace N.model (ψ x))) :=
  (mfderivEquiv_coe ψ x).symm

/-- `dψ_x` is invertible as a continuous linear map. This is the
`ContinuousLinearMap.IsInvertible` *predicate* form of
`lmm:mfderiv-diffeo-linear-equiv`, which is what
`ContMDiff.mpullback_vectorField` and `ContinuousLinearMap.inverse` consume. -/
theorem isInvertible_mfderiv (ψ : Diffeo M N) (x : M.Carrier) :
    (mfderiv M.model N.model ψ x).IsInvertible := by
  rw [← mfderivEquiv_coe ψ x]
  exact ContinuousLinearMap.isInvertible_equiv (f := mfderivEquiv ψ x)

/--
**Round-trip cancellation: `dψ` after `d(ψ⁻¹)`** (`lmm:mfderiv-symm-cancel-left`).

Here `d(ψ⁻¹)_{ψ x}` is `mfderiv N.model M.model ψ.symm (ψ x)`, the differential
of the *global* inverse diffeomorphism, and **not** the `symm` of
`mfderivEquiv`. Mathlib has no `Diffeomorph` analogue of this identity, so it
has to be proved by hand from `mfderiv_comp_apply_of_eq`.

The pointwise form is the primary statement, because that is the form in which
every consumer applies it.
-/
theorem mfderiv_symm_cancel_left (ψ : Diffeo M N) (x : M.Carrier)
    (u : TangentSpace N.model (ψ x)) :
    mfderiv M.model N.model ψ x
        (mfderiv N.model M.model ψ.symm (ψ x) u) = u := by
  have h := mfderiv_comp_apply_of_eq (I := N.model) (I' := M.model) (I'' := N.model)
    (f := (ψ.symm : N.Carrier → M.Carrier)) (g := (ψ : M.Carrier → N.Carrier))
    (x := ψ x) (y := x) (ψ.mdifferentiable (by simp) x)
    (ψ.symm.mdifferentiable (by simp) (ψ x)) (ψ.symm_apply_apply x) u
  have hid : mfderiv N.model N.model
        ((ψ : M.Carrier → N.Carrier) ∘ (ψ.symm : N.Carrier → M.Carrier)) (ψ x)
      = ContinuousLinearMap.id ℝ (TangentSpace N.model (ψ x)) := by
    have h2 : mfderiv N.model N.model (id : N.Carrier → N.Carrier) (ψ x)
        = ContinuousLinearMap.id ℝ (TangentSpace N.model (ψ x)) := mfderiv_id
    rw [← h2]
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards with z
    exact ψ.apply_symm_apply z
  rw [← h, hid]
  rfl

/--
**Round-trip cancellation: `d(ψ⁻¹)` after `dψ`** (`lmm:mfderiv-symm-cancel-right`).

The mirror of `mfderiv_symm_cancel_left`, with the same reading of
`d(ψ⁻¹)_{ψ x}`. The two directions are separate nodes because the base-point
transport in the chain rule is asymmetric between them: here it is `rfl`.
-/
theorem mfderiv_symm_cancel_right (ψ : Diffeo M N) (x : M.Carrier)
    (v : TangentSpace M.model x) :
    mfderiv N.model M.model ψ.symm (ψ x)
        (mfderiv M.model N.model ψ x v) = v := by
  have h := mfderiv_comp_apply_of_eq (I := M.model) (I' := N.model) (I'' := M.model)
    (f := (ψ : M.Carrier → N.Carrier)) (g := (ψ.symm : N.Carrier → M.Carrier))
    (x := x) (y := ψ x) (ψ.symm.mdifferentiable (by simp) (ψ x))
    (ψ.mdifferentiable (by simp) x) (rfl) v
  have hid : mfderiv M.model M.model
        ((ψ.symm : N.Carrier → M.Carrier) ∘ (ψ : M.Carrier → N.Carrier)) x
      = ContinuousLinearMap.id ℝ (TangentSpace M.model x) := by
    have h2 : mfderiv M.model M.model (id : M.Carrier → M.Carrier) x
        = ContinuousLinearMap.id ℝ (TangentSpace M.model x) := mfderiv_id
    rw [← h2]
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards with z
    exact ψ.symm_apply_apply z
  rw [← h, hid]
  rfl

/--
**The formal inverse of `dψ_x` is the inverse equivalence**
(`lmm:mfderiv-inverse-eq-symm`).

`ContinuousLinearMap.inverse` is defined by cases on invertibility and returns
the junk value `0` otherwise, so nothing can be cancelled against it until
invertibility is exhibited. This is the leaf that licenses every `dψ`
cancellation in the `VectorField.mpullback` computations downstream.
-/
theorem inverse_mfderiv_eq_symm (ψ : Diffeo M N) (x : M.Carrier) :
    ContinuousLinearMap.inverse (mfderiv M.model N.model ψ x)
      = ((mfderivEquiv ψ x).symm :
          TangentSpace N.model (ψ x) →L[ℝ] TangentSpace M.model x) := by
  rw [← mfderivEquiv_coe ψ x]
  rw [ContinuousLinearMap.inverse_equiv]

/-- Cancellation `(dψ_x)⁻¹ (dψ_x v) = v` for the *formal* inverse
`ContinuousLinearMap.inverse`. -/
@[simp] theorem inverse_mfderiv_apply_mfderiv (ψ : Diffeo M N) (x : M.Carrier)
    (v : TangentSpace M.model x) :
    ContinuousLinearMap.inverse (mfderiv M.model N.model ψ x)
        (mfderiv M.model N.model ψ x v) = v := by
  rw [inverse_mfderiv_eq_symm ψ x, mfderiv_eq_mfderivEquiv ψ x]
  exact (ContinuousLinearEquiv.symm_apply_apply (mfderivEquiv ψ x) v)

/-- Cancellation `dψ_x ((dψ_x)⁻¹ u) = u` for the *formal* inverse
`ContinuousLinearMap.inverse`. This is the identity spent on every
`VectorField.mpullback` computation. -/
@[simp] theorem mfderiv_apply_inverse_mfderiv (ψ : Diffeo M N) (x : M.Carrier)
    (u : TangentSpace N.model (ψ x)) :
    mfderiv M.model N.model ψ x
        (ContinuousLinearMap.inverse (mfderiv M.model N.model ψ x) u) = u := by
  rw [inverse_mfderiv_eq_symm ψ x, mfderiv_eq_mfderivEquiv ψ x]
  exact (ContinuousLinearEquiv.apply_symm_apply (mfderivEquiv ψ x) u)

end Spacetime

end Physicslib4
