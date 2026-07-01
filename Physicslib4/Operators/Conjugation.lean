/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Group.Center
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Conjugation by a unit and by a unitary

Spacetime-agnostic operator-algebra machinery used by the geometric-covariance
results of algebraic QFT (both the Minkowski and curved Haag-Kastler nets), kept
here so neither net depends on the other.

* `Units.conjMulEquiv u` — conjugation by a monoid unit, `x ↦ u x u⁻¹`, as a
  multiplicative automorphism.
* `MulEquiv.image_centralizer` / `image_centralizer_centralizer` — a multiplicative
  automorphism maps centralizers (hence bicommutants) to those of the image.
* `Physicslib4.lieConj U` — conjugation by a unitary `U : H ≃ₗᵢ[ℂ] H` on `B(H)`,
  with `lieConj_apply` and the bridge `lieConj_apply_eq_conjStarAlgEquiv` to
  Mathlib's `LinearIsometryEquiv.conjStarAlgEquiv`.
* `Physicslib4.scalarOperators` / `IsFactor` and `IsFactor.conj` — the factor
  (trivial-center) property and its preservation under conjugation.
* `Physicslib4.restrictStarAlgEquiv` — a `*`-automorphism carrying one
  star-subalgebra's set onto another's restricts to a `*`-algebra equivalence.
-/

namespace Units

variable {M : Type*} [Monoid M]

/-- Conjugation by a unit `u`, as a multiplicative automorphism of the monoid:
`x ↦ u * x * u⁻¹`. -/
def conjMulEquiv (u : Mˣ) : M ≃* M where
  toFun x := ↑u * x * ↑u⁻¹
  invFun x := ↑u⁻¹ * x * ↑u
  left_inv x := by
    calc (↑u⁻¹ : M) * (↑u * x * ↑u⁻¹) * ↑u
        = (↑u⁻¹ * ↑u) * x * (↑u⁻¹ * ↑u) := by noncomm_ring
      _ = x := by rw [u.inv_mul]; noncomm_ring
  right_inv x := by
    calc (↑u : M) * (↑u⁻¹ * x * ↑u) * ↑u⁻¹
        = (↑u * ↑u⁻¹) * x * (↑u * ↑u⁻¹) := by noncomm_ring
      _ = x := by rw [u.mul_inv]; noncomm_ring
  map_mul' x y := by
    calc (↑u : M) * (x * y) * ↑u⁻¹
        = ↑u * x * (↑u⁻¹ * ↑u) * y * ↑u⁻¹ := by rw [u.inv_mul]; noncomm_ring
      _ = (↑u * x * ↑u⁻¹) * (↑u * y * ↑u⁻¹) := by noncomm_ring

@[simp] theorem conjMulEquiv_apply (u : Mˣ) (x : M) :
    conjMulEquiv u x = ↑u * x * ↑u⁻¹ := rfl

end Units

namespace MulEquiv

variable {M : Type*} [Mul M]

/-- A multiplicative automorphism maps the centralizer of a set onto the
centralizer of its image. -/
theorem image_centralizer (φ : M ≃* M) (S : Set M) :
    φ '' Set.centralizer S = Set.centralizer (φ '' S) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [Set.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Set.mem_centralizer_iff.mp hx s hs)
  · intro y hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    rw [Set.mem_centralizer_iff]
    intro s hs
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact Set.mem_centralizer_iff.mp hy (φ s) ⟨s, hs, rfl⟩

/-- A multiplicative automorphism maps bicommutants to bicommutants. -/
theorem image_centralizer_centralizer (φ : M ≃* M) (S : Set M) :
    φ '' Set.centralizer (Set.centralizer S)
      = Set.centralizer (Set.centralizer (φ '' S)) := by
  rw [φ.image_centralizer, φ.image_centralizer]

end MulEquiv

namespace Physicslib4

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Conjugation by a unitary `U : H ≃ₗᵢ[ℂ] H` as a multiplicative automorphism of
the algebra `H →L[ℂ] H` of bounded operators: `T ↦ U T U⁻¹`. -/
noncomputable def lieConj (Uop : H ≃ₗᵢ[ℂ] H) : (H →L[ℂ] H) ≃* (H →L[ℂ] H) :=
  Units.conjMulEquiv (Uop.toContinuousLinearEquiv.toUnit)

omit [CompleteSpace H] in
@[simp] theorem lieConj_apply (Uop : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (x : H) :
    lieConj Uop T x = Uop (T (Uop.symm x)) := by
  change ((Uop.toContinuousLinearEquiv : H →L[ℂ] H) * T
        * (Uop.toContinuousLinearEquiv.symm : H →L[ℂ] H)) x = Uop (T (Uop.symm x))
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

/-- Conjugation by a unitary commutes with the operator exponential:
`exp (W A W⁻¹) = W (exp A) W⁻¹`. Immediate from `NormedSpace.exp_units_conj`, since
`lieConj W` is conjugation by the unit `W`. -/
theorem exp_lieConj (W : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) :
    NormedSpace.exp (lieConj W A) = lieConj W (NormedSpace.exp A) := by
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  simp only [lieConj, Units.conjMulEquiv_apply]
  exact NormedSpace.exp_units_conj _ A

omit [CompleteSpace H] in
/-- Conjugation by a unitary is `ℂ`-linear: `lieConj W (c • A) = c • lieConj W A`. -/
theorem lieConj_smul (W : H ≃ₗᵢ[ℂ] H) (c : ℂ) (A : H →L[ℂ] H) :
    lieConj W (c • A) = c • lieConj W A := by
  simp only [lieConj, Units.conjMulEquiv_apply, mul_smul_comm, smul_mul_assoc]

/-- The scalar operators `{c · 1 : c ∈ ℂ}` of a Hilbert space, the (would-be)
center of any von Neumann algebra acting irreducibly. -/
def scalarOperators (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Set (H →L[ℂ] H) :=
  {T : H →L[ℂ] H | ∃ c : ℂ, T = c • 1}

/-- A von Neumann algebra (a set of operators) is a *factor* when its center
`R ∩ R'` is exactly the scalars. -/
def IsFactor (R : Set (H →L[ℂ] H)) : Prop :=
  R ∩ Set.centralizer R = scalarOperators H

omit [CompleteSpace H] in
/-- Conjugation by a unitary fixes the scalar operators setwise:
`U (c · 1) U⁻¹ = c · 1`. -/
theorem lieConj_image_scalarOperators (Uop : H ≃ₗᵢ[ℂ] H) :
    lieConj Uop '' scalarOperators H = scalarOperators H := by
  have hfix : ∀ c : ℂ, lieConj Uop (c • (1 : H →L[ℂ] H)) = c • 1 := by
    intro c
    ext x
    rw [lieConj_apply]
    simp
  ext T
  simp only [scalarOperators, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, hfix c⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • (1 : H →L[ℂ] H), ⟨c, rfl⟩, hfix c⟩

omit [CompleteSpace H] in
/-- **Conjugation preserves factoriality.** If a von Neumann algebra `R` is a
factor, so is its conjugate `U R U⁻¹`. Conjugation is a multiplicative
automorphism, so it carries the center `R ∩ R'` onto the center of `U R U⁻¹` and
fixes the scalars. -/
theorem IsFactor.conj (Uop : H ≃ₗᵢ[ℂ] H) {R : Set (H →L[ℂ] H)} (h : IsFactor R) :
    IsFactor (lieConj Uop '' R) := by
  unfold IsFactor at h ⊢
  rw [← (lieConj Uop).image_centralizer R, ← Set.image_inter (lieConj Uop).injective, h,
    lieConj_image_scalarOperators]

/-- The conjugation `MulEquiv` `lieConj U` agrees, as a map of operators, with
Mathlib's conjugation `*`-algebra automorphism `LinearIsometryEquiv.conjStarAlgEquiv U`.
This bridges our bare-monoid conjugation to the full `StarAlgEquiv`. -/
theorem lieConj_apply_eq_conjStarAlgEquiv (Uop : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    lieConj Uop T = LinearIsometryEquiv.conjStarAlgEquiv Uop T := by
  ext x
  rw [lieConj_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply]
  simp [ContinuousLinearMap.comp_apply]

/-- A star-algebra automorphism `e` of `A` whose underlying map carries the set of
a star-subalgebra `S` onto that of `T` restricts to a star-algebra equivalence
`S ≃⋆ₐ[ℂ] T`. -/
@[simps! apply]
def restrictStarAlgEquiv {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (e : A ≃⋆ₐ[ℂ] A) {S T : StarSubalgebra ℂ A}
    (hfwd : ∀ x ∈ S, e x ∈ T) (hbwd : ∀ y ∈ T, e.symm y ∈ S) : S ≃⋆ₐ[ℂ] T where
  toFun x := ⟨e x, hfwd x x.2⟩
  invFun y := ⟨e.symm y, hbwd y y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)
  map_star' x := Subtype.ext (map_star e _)

end Physicslib4
