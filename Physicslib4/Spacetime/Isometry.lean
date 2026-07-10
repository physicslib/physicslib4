/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.CausalStructure
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Isometries of a spacetime

This file develops the group of *isometries* of a `Physicslib4.Spacetime`,
used to instantiate the abstract isometry group of the curved-spacetime
Haag-Kastler axioms (`def:isometric-covariance-in-curved-spacetime`,
Axiom 5).

## Main definitions

* `Physicslib4.Spacetime.Isometry`: a *diffeomorphism* of the spacetime
  whose manifold differential `mfderiv` preserves the metric.
* `Group (Isometry M)` and `MulAction (Isometry M) M.Carrier`.

## Modelling notes

An isometry is a genuine `C^∞` diffeomorphism `φ : M → M` (bundled as a
`Diffeomorph`, so smoothness of `φ` and of `φ⁻¹` is built in) whose
*manifold derivative* preserves the metric:
`g_{φ(x)}(dφ_x v, dφ_x w) = g_x(v, w)`, where `dφ_x = mfderiv I I φ x`.
Composition and inverse preserve the metric via the manifold chain rule
(`mfderiv_comp`); for the inverse we use that `φ ∘ φ⁻¹ = id` together with
`Filter.EventuallyEq.mfderiv_eq`, exactly as Mathlib's
`PartialHomeomorph.MDifferentiable.comp_symm_deriv` does. The isometries
thus form a group acting on points.

**On the identity-component restriction.** `Isometry M` is the full
metric-preserving diffeomorphism group. The blueprint's identity-component
("connected to the identity") restriction of Axiom 5 is captured downstream:
`Physicslib4/Spacetime/IsometryTopology.lean` topologizes this group as a
topological group and defines the identity-component subgroup
`Isometry.identityComponent := Subgroup.connectedComponentOfOne`, and
`Isometry.orientedIdentityComponent` (`IsometryCausality.lean`) intersects it
with future-orientation preservation. That subgroup is the `M.Isom` supplied to
the curved Haag-Kastler bridge `toAbstractIdentityComponent`. The full group is
retained here as the substrate and for the axioms that hold under all
isometries (e.g. microcausality).
-/

namespace Physicslib4

namespace Spacetime

/--
An **isometry** of a spacetime `M`: a `C^∞` diffeomorphism whose
manifold differential preserves the metric.
-/
@[ext]
structure Isometry (M : Spacetime) where
  /-- The underlying `C^∞` diffeomorphism of the spacetime. -/
  toDiffeo : Diffeomorph M.model M.model M.Carrier M.Carrier ⊤
  /-- Metric preservation: `g_{φ(x)}(dφ_x v, dφ_x w) = g_x(v, w)`,
  with `dφ_x` the manifold derivative `mfderiv`. -/
  preserves : ∀ (x : M.Carrier) (v w : TangentSpace M.model x),
    M.val (toDiffeo x)
      (mfderiv M.model M.model toDiffeo x v)
      (mfderiv M.model M.model toDiffeo x w)
    = M.val x v w

namespace Isometry

variable {M : Spacetime}

/-- Diffeomorphisms of a spacetime are everywhere `MDifferentiable`
(the smoothness exponent `⊤` is nonzero). -/
private theorem mdiff (h : Diffeomorph M.model M.model M.Carrier M.Carrier ⊤) :
    MDifferentiable M.model M.model h :=
  h.mdifferentiable (by simp)

/-- Applied chain rule for a composition of two spacetime diffeomorphisms. -/
private theorem mfderiv_trans_apply
    (a b : Diffeomorph M.model M.model M.Carrier M.Carrier ⊤)
    (x : M.Carrier) (u : TangentSpace M.model x) :
    mfderiv M.model M.model (b.trans a) x u
      = mfderiv M.model M.model a (b x) (mfderiv M.model M.model b x u) := by
  have h := mfderiv_comp_apply (I := M.model) (I' := M.model) (I'' := M.model)
    (f := (b : M.Carrier → M.Carrier)) (g := (a : M.Carrier → M.Carrier)) (x := x)
    ((mdiff a) (b x)) ((mdiff b) x) u
  rw [← Diffeomorph.coe_trans] at h
  exact h

/-- The differential of `φ` at `φ⁻¹ x` inverts the differential of `φ⁻¹`
at `x`: this is the manifold inverse-function identity for a
diffeomorphism, proved from `φ ∘ φ⁻¹ = id`. -/
private theorem mfderiv_symm_cancel
    (a : Diffeomorph M.model M.model M.Carrier M.Carrier ⊤)
    (x : M.Carrier) (u : TangentSpace M.model x) :
    mfderiv M.model M.model a (a.symm x)
        (mfderiv M.model M.model a.symm x u) = u := by
  have hcomp : (mfderiv M.model M.model a (a.symm x)).comp
        (mfderiv M.model M.model a.symm x)
      = ContinuousLinearMap.id ℝ (TangentSpace M.model x) := by
    have h1 := mfderiv_comp (I := M.model) (I' := M.model) (I'' := M.model)
      (f := (a.symm : M.Carrier → M.Carrier)) (g := (a : M.Carrier → M.Carrier))
      (x := x) ((mdiff a) (a.symm x)) ((mdiff a.symm) x)
    rw [← h1]
    have h2 : mfderiv M.model M.model (id : M.Carrier → M.Carrier) x
        = ContinuousLinearMap.id ℝ (TangentSpace M.model x) := mfderiv_id
    rw [← h2]
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards with y
    exact a.apply_symm_apply y
  have hu := DFunLike.congr_fun hcomp u
  rw [ContinuousLinearMap.comp_apply] at hu
  exact hu

noncomputable instance : Group (Isometry M) where
  mul a b :=
    { toDiffeo := b.toDiffeo.trans a.toDiffeo
      preserves := fun x v w => by
        change M.val (a.toDiffeo (b.toDiffeo x))
              (mfderiv M.model M.model (b.toDiffeo.trans a.toDiffeo) x v)
              (mfderiv M.model M.model (b.toDiffeo.trans a.toDiffeo) x w) = M.val x v w
        rw [mfderiv_trans_apply, mfderiv_trans_apply,
          a.preserves (b.toDiffeo x) (mfderiv M.model M.model b.toDiffeo x v)
            (mfderiv M.model M.model b.toDiffeo x w), b.preserves x v w] }
  one :=
    { toDiffeo := Diffeomorph.refl M.model M.Carrier ⊤
      preserves := fun x v w => by
        have h : mfderiv M.model M.model (Diffeomorph.refl M.model M.Carrier ⊤) x
            = ContinuousLinearMap.id ℝ (TangentSpace M.model x) := by
          rw [Diffeomorph.coe_refl, mfderiv_id]
        rw [h]
        rfl }
  inv a :=
    { toDiffeo := a.toDiffeo.symm
      preserves := fun x v w => by
        have key := a.preserves (a.toDiffeo.symm x)
          (mfderiv M.model M.model a.toDiffeo.symm x v)
          (mfderiv M.model M.model a.toDiffeo.symm x w)
        rw [mfderiv_symm_cancel, mfderiv_symm_cancel,
          a.toDiffeo.apply_symm_apply] at key
        exact key.symm }
  mul_assoc a b c := Isometry.ext rfl
  one_mul a := Isometry.ext rfl
  mul_one a := Isometry.ext rfl
  inv_mul_cancel a := by
    apply Isometry.ext
    ext x
    exact a.toDiffeo.symm_apply_apply x

/-- The action of the isometry group on spacetime points, by applying
the underlying diffeomorphism. -/
noncomputable instance : MulAction (Isometry M) M.Carrier where
  smul g x := g.toDiffeo x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem smul_def (g : Isometry M) (x : M.Carrier) :
    g • x = g.toDiffeo x := rfl

/-- The isometry group acts *faithfully* on the spacetime: an isometry is
determined by its action on points. -/
instance : FaithfulSMul (Isometry M) M.Carrier where
  eq_of_smul_eq_smul h := Isometry.ext (DFunLike.ext _ _ fun x => h x)

/-! ### Invariance of the causal classification

An isometry preserves the metric square of a tangent vector, hence preserves
the timelike/null/spacelike classification. These are the basic facts linking
the isometry group to the causal structure underlying Axiom 5. -/

/-- An isometry preserves the metric square `g(v,v)` of a tangent vector. -/
theorem preserves_self (g : Isometry M) (x : M.Carrier)
    (v : TangentSpace M.model x) :
    M.val (g.toDiffeo x) (mfderiv M.model M.model g.toDiffeo x v)
        (mfderiv M.model M.model g.toDiffeo x v) = M.val x v v :=
  g.preserves x v v

/-- An isometry preserves timelike vectors. -/
theorem isTimelike_mfderiv_iff (g : Isometry M) (x : M.Carrier)
    (v : TangentSpace M.model x) :
    M.IsTimelike (mfderiv M.model M.model g.toDiffeo x v) ↔ M.IsTimelike v := by
  unfold IsTimelike
  rw [g.preserves x v v]

/-- An isometry preserves null vectors. -/
theorem isNull_mfderiv_iff (g : Isometry M) (x : M.Carrier)
    (v : TangentSpace M.model x) :
    M.IsNull (mfderiv M.model M.model g.toDiffeo x v) ↔ M.IsNull v := by
  unfold IsNull
  rw [g.preserves x v v]

/-- An isometry preserves spacelike vectors. -/
theorem isSpacelike_mfderiv_iff (g : Isometry M) (x : M.Carrier)
    (v : TangentSpace M.model x) :
    M.IsSpacelike (mfderiv M.model M.model g.toDiffeo x v) ↔ M.IsSpacelike v := by
  unfold IsSpacelike
  rw [g.preserves x v v]

end Isometry

end Spacetime

end Physicslib4
