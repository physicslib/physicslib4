/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Antiunitary operators

Basic facts about antiunitary operators on a complex Hilbert space, used by the
Tomita–Takesaki section of the blueprint.

An antiunitary operator is Mathlib's conjugate-linear isometric equivalence
`H ≃ₗᵢ⋆[ℂ] H` (`LinearIsometryEquiv (starRingEnd ℂ) H H`); a conjugate-linear
norm-preserving map whose bijectivity is not known is `H →ₗᵢ⋆[ℂ] H`. Unitaries are
`H ≃ₗᵢ[ℂ] H`.

* `Physicslib4.Modular.antiunitary_isometric` — norm preservation, continuity and the
  inverse of an antiunitary.
* `Physicslib4.Modular.inner_map_map_of_conjLinearIsometry` — a conjugate-linear isometry
  conjugates inner products.
* `Physicslib4.Modular.antiunitary_composition` — composites of antiunitaries and unitaries.
* `Physicslib4.Modular.exists_antiunitary_of_bijective` — a conjugate-linear norm-preserving
  bijection is antiunitary.
* `Physicslib4.Modular.isClosable_of_dense_adjoint` — an operator with densely defined
  adjoint is closable.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An antiunitary operator `W` is isometric and continuous, and its inverse `W.symm`
is a two-sided inverse of `W`; `W.symm` is again an antiunitary by its type.
Blueprint: lmm:antiunitary-isometric -/
theorem antiunitary_isometric (W : H ≃ₗᵢ⋆[ℂ] H) :
    (∀ x, ‖W x‖ = ‖x‖) ∧ Continuous W ∧
      (∀ x, W.symm (W x) = x) ∧ (∀ x, W (W.symm x) = x) :=
  ⟨W.norm_map, W.continuous, W.symm_apply_apply, W.apply_symm_apply⟩

/-- A conjugate-linear norm-preserving map `W`, not necessarily bijective, conjugates
inner products: `⟪W x, W y⟫ = conj ⟪x, y⟫`.
Blueprint: lmm:conjugate-linear-isometry-inner -/
theorem inner_map_map_of_conjLinearIsometry {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (W : E →ₗᵢ⋆[ℂ] F) (x y : E) :
    ⟪W x, W y⟫_ℂ = conj ⟪x, y⟫_ℂ := by
  have hI : ∀ v : E, W ((RCLike.I : ℂ) • v) = -((RCLike.I : ℂ) • W v) := fun v => by
    rw [LinearIsometry.map_smulₛₗ]; simp [neg_smul]
  rw [inner_eq_sum_norm_sq_div_four (W x), inner_eq_sum_norm_sq_div_four x]
  have h1 : W x - (RCLike.I : ℂ) • W y = W (x + (RCLike.I : ℂ) • y) := by
    rw [W.map_add, hI, sub_eq_add_neg]
  have h2 : W x + (RCLike.I : ℂ) • W y = W (x - (RCLike.I : ℂ) • y) := by
    rw [W.map_sub, hI, sub_neg_eq_add]
  rw [← W.map_add, ← W.map_sub, h1, h2]
  simp only [LinearIsometry.norm_map]
  simp [RCLike.I, Complex.conj_I, map_ofNat]
  ring

/-- For antiunitaries `W, W₁, W₂` and a unitary `U`, the composites `W U` and `U W` are
antiunitary and `W₁ W₂` is unitary, each realised by `LinearIsometryEquiv.trans`.
Blueprint: lmm:antiunitary-composition -/
theorem antiunitary_composition (W W₁ W₂ : H ≃ₗᵢ⋆[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) :
    (∃ V : H ≃ₗᵢ⋆[ℂ] H, ⇑V = ⇑W ∘ ⇑U) ∧
      (∃ V : H ≃ₗᵢ⋆[ℂ] H, ⇑V = ⇑U ∘ ⇑W) ∧
      (∃ V : H ≃ₗᵢ[ℂ] H, ⇑V = ⇑W₁ ∘ ⇑W₂) := by
  exact ⟨⟨U.trans W, rfl⟩, ⟨W.trans U, rfl⟩, ⟨W₂.trans W₁, rfl⟩⟩

/-- A conjugate-linear norm-preserving bijection `W` of `H` is antiunitary: it is the
underlying map of some `U : H ≃ₗᵢ⋆[ℂ] H`, and `⟪W x, W y⟫ = conj ⟪x, y⟫`.
Blueprint: lmm:antilinear-isometry-antiunitary -/
theorem exists_antiunitary_of_bijective (W : H →ₗ⋆[ℂ] H) (hnorm : ∀ x, ‖W x‖ = ‖x‖)
    (hbij : Function.Bijective W) :
    ∃ U : H ≃ₗᵢ⋆[ℂ] H, ⇑U = ⇑W ∧ ∀ x y, ⟪U x, U y⟫_ℂ = conj ⟪x, y⟫_ℂ :=
  let U : H ≃ₗᵢ⋆[ℂ] H := ⟨LinearEquiv.ofBijective W hbij, hnorm⟩
  ⟨U, rfl, inner_map_map_of_conjLinearIsometry U.toLinearIsometry⟩

/-- A densely defined operator `T` whose adjoint `T.adjoint` is densely defined is closable.
Blueprint: lmm:closable-of-dense-adjoint -/
theorem isClosable_of_dense_adjoint [CompleteSpace H] {T : H →ₗ.[ℂ] H}
    (hT : Dense (T.domain : Set H)) (hT' : Dense (T.adjoint.domain : Set H)) :
    T.IsClosable :=
  (T.adjoint.adjoint_isClosed hT').isClosable.leIsClosable
    ((T.adjoint_isFormalAdjoint hT).le_adjoint hT')

end Physicslib4.Modular
