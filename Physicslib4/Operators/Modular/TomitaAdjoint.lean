/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.Takesaki
import Physicslib4.Spectral.Unbounded.Commuting
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

/-!
# The adjoint of the Tomita operator and the modular objects of the commutant

For a von Neumann algebra `M` with a cyclic and separating vector `Ω` and a reference
conjugation `C`, this file states van Daele's proof that the antilinear adjoint `S*` of the
Tomita operator is the closure of `F₀`, that `S* = J Δ^{-1/2}`, and that the Tomita operator,
modular operator and modular conjugation of `(M′, Ω)` are `S*`, `Δ⁻¹` and `J`.

## Representation

* **The antilinear adjoint.** `S*` is `(S′)† C`, with `S′ = (linearizedTomitaPre M Ω C).closure`.
  The statement "`(ξ, η) ∈ Γ(S*)`" is written
  `∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
    (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η`,
  and `Γ(S*)` is the set of pairs `p : H × H` satisfying it.
* **The graph of `F₀`.** `Γ(F₀)` is `(fun b => (b Ω, star b Ω)) '' Set.centralizer M`.
* **The operator `a₀`.** The operator `x Ω ↦ x ξ` (`x ∈ M`) is `tomitaLeftMap M Ω ξ`, the
  partial linear map with graph `{(x Ω, x ξ) : x ∈ span M}`; `tomitaLeftMap_properties` gives
  its domain and values. Its closure is `c = (tomitaLeftMap M Ω ξ).closure`, and the
  approximants `x_n` of `approximant_operator` for `c` are bounded operators characterized by
  `x_n ψ = c (R_n ψ)`.
* **Unitaries.** A unitary in `M` that commutes with an unbounded operator is a
  `U : H ≃ₗᵢ[ℂ] H` with `(U : H →L[ℂ] H) ∈ M`, and "commutes" is `UnitaryCommutes U A`
  from `Commuting.lean`. Statements about bounded operators use Mathlib's `unitary (H →L[ℂ] H)`.
* **The commutant.** The modular objects of `(M′, Ω)` are the definitions of `Tomita.lean` and
  `Modular.lean` applied to `Set.centralizer M` with the same `C`; the proofs of their
  hypotheses are those of `isCyclicSeparatingVector_centralizer`.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace ComplexStarModule
open Physicslib4.Spectral.Unbounded
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The antilinear adjoint of `S` -/

/-- `(ξ, η) ∈ Γ(S*)` if and only if `⟪ξ, S ζ⟫ = ⟪ζ, η⟫` for every `ζ ∈ Dom S`.
Blueprint: lmm:tomita-adjoint-intrinsic -/
theorem mem_tomitaAdjoint_iff {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (ξ η : H) :
    (∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) ↔
      ∀ ζ : (linearizedTomitaPre M Ω C).closure.domain,
        ⟪ξ, tomitaOperator M Ω C ζ⟫_ℂ = ⟪(ζ : H), η⟫_ℂ := by
  set T := (linearizedTomitaPre M Ω C).closure
  have hd : Dense (T.domain : Set H) := (linearizedTomita_closure_properties hM hΩ C hC).2.1
  have key : ∀ ζ : T.domain,
      ⟪ξ, tomitaOperator M Ω C ζ⟫_ℂ = starRingEnd ℂ ⟪C ξ, T ζ⟫_ℂ := fun ζ => by
    have := inner_map_map_of_conjLinearIsometry C.toLinearIsometry (C ξ) (T ζ)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry,
      hC] at this
    exact this
  constructor
  · rintro ⟨h, rfl⟩ ζ
    rw [key, ← LinearPMap.adjoint_isFormalAdjoint hd ⟨C ξ, h⟩ ζ, inner_conj_symm]
  · intro hζ
    have h' : ∀ ζ : T.domain, ⟪η, (ζ : H)⟫_ℂ = ⟪C ξ, T ζ⟫_ℂ := fun ζ => by
      rw [← inner_conj_symm, ← hζ, key, RCLike.conj_conj]
    have hmem : C ξ ∈ T.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists _ ⟨η, h'⟩
    exact ⟨hmem, LinearPMap.adjoint_apply_eq hd ⟨C ξ, hmem⟩ h'⟩

/-- `(ξ, η) ∈ Γ(S*)` if and only if `⟪ξ, x* Ω⟫ = ⟪x Ω, η⟫` for every `x ∈ M`.
Blueprint: lmm:tomita-adjoint-intrinsic-core -/
theorem mem_tomitaAdjoint_iff_inner_algebra {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ξ η : H) :
    (∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) ↔
      ∀ x ∈ M, ⟪ξ, star x Ω⟫_ℂ = ⟪x Ω, η⟫_ℂ := by
  rw [mem_tomitaAdjoint_iff hM hΩ C hC]
  constructor
  · intro h a ha
    have hmem : (a Ω, star a Ω) ∈ Set.range (fun x : (linearizedTomitaPre M Ω C).closure.domain =>
        ((x : H), tomitaOperator M Ω C x)) := by
      rw [tomitaOperator_graph_eq_closure hM hΩ C hC]
      exact subset_closure ⟨⟨a Ω, Submodule.mem_map_of_mem (Submodule.subset_span ha)⟩,
        Prod.ext rfl ((tomitaPre_apply hM hΩ).1 a ha)⟩
    obtain ⟨x, hx⟩ := hmem
    have hx1 : (x : H) = a Ω := congrArg Prod.fst hx
    have hx2 : tomitaOperator M Ω C x = star a Ω := congrArg Prod.snd hx
    rw [← hx1, ← hx2]
    exact h x
  · intro h ζ
    obtain ⟨u, huM, h1, h2⟩ := tomitaOperator_exists_seq_tendsto hM hΩ C hC ζ
    exact tendsto_nhds_unique (tendsto_const_nhds.inner h2)
      ((h1.inner tendsto_const_nhds).congr fun n => (h (u n) (huM n)).symm)

/-- The graph `Γ(S*) = {(ξ, η) | C ξ ∈ Dom (S′)†, (S′)† (C ξ) = η}` is closed in `H × H`.
Blueprint: lmm:tomita-adjoint-graph-closed -/
theorem tomitaAdjoint_graph_isClosed {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) :
    IsClosed {p : H × H | ∃ h : C p.1 ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint ⟨C p.1, h⟩ = p.2} := by
  have hcl : IsClosed ((linearizedTomitaPre M Ω C).closure.adjoint.graph : Set (H × H)) :=
    LinearPMap.adjoint_isClosed (tomitaOperator_involution hM hΩ C hC).2.2.1
  convert hcl.preimage (C.continuous.prodMap continuous_id) using 1
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.map, id, SetLike.mem_coe,
    LinearPMap.mem_graph_iff]
  exact ⟨fun ⟨h, e⟩ => ⟨⟨C x, h⟩, rfl, e⟩, fun ⟨⟨z, hz⟩, e1, e2⟩ => by subst e1; exact ⟨hz, e2⟩⟩

/-- The closure of `Γ(F₀) = {(b′ Ω, b′* Ω) | b′ ∈ M′}` is contained in `Γ(S*)`.
Blueprint: lmm:tomita-adjoint-extends-closure -/
theorem mem_tomitaAdjoint_of_mem_closure_graph {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H}
    (hξη : (ξ, η) ∈ closure ((fun b : H →L[ℂ] H => (b Ω, star b Ω)) '' Set.centralizer M)) :
    ∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η := by
  refine closure_minimal (Set.image_subset_iff.mpr fun b hb => ?_)
    (tomitaAdjoint_graph_isClosed hM hΩ C hC) hξη
  refine (mem_tomitaAdjoint_iff hM hΩ C hC _ _).2 fun ζ => ?_
  obtain ⟨x, hx, h1, h2⟩ := tomitaOperator_exists_seq_tendsto hM hΩ C hC ζ
  have key : ∀ n, ⟪b Ω, star (x n) Ω⟫_ℂ = ⟪x n Ω, star b Ω⟫_ℂ := fun n => by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
      ← mul_apply_eq_comp, ← mul_apply_eq_comp, Set.mem_centralizer_iff.mp hb _ (hx n)]
  exact tendsto_nhds_unique (tendsto_const_nhds.inner h2)
    ((h1.inner tendsto_const_nhds).congr fun n => (key n).symm)

/-! ### Unitaries of a von Neumann algebra -/

/-- For self-adjoint `a ∈ M` with `‖a‖ ≤ 1`, `u = a + i √(1 - a²)` is unitary and `u, u* ∈ M`.
Blueprint: lmm:von-neumann-unitary-of-contraction -/
theorem self_add_I_smul_cfcSqrt_mem_of_isVonNeumannSet {M : Set (H →L[ℂ] H)}
    (hM : IsVonNeumannSet M) {a : H →L[ℂ] H} (ha : a ∈ M) (hsa : IsSelfAdjoint a)
    (hnorm : ‖a‖ ≤ 1) :
    a + Complex.I • CFC.sqrt (1 - a ^ 2) ∈ unitary (H →L[ℂ] H) ∧
      a + Complex.I • CFC.sqrt (1 - a ^ 2) ∈ M ∧
      star (a + Complex.I • CFC.sqrt (1 - a ^ 2)) ∈ M := by
  obtain ⟨A, rfl⟩ := (isVonNeumannSet_centralizer hM).2.2.1
  have ha' : a ∈ A := ha
  have hnn : (0 : H →L[ℂ] H) ≤ 1 - a ^ 2 := by
    rwa [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (a ^ 2), sq, hsa.norm_mul_self,
      sq_le_one_iff₀ (by positivity)]
  have hs : CFC.sqrt (1 - a ^ 2) ∈ A := by
    rw [CFC.sqrt_eq_real_sqrt _ hnn, cfcₙ_eq_cfc]
    exact cfc_mem_of_isVonNeumannSet hM (A.sub_mem A.one_mem (A.pow_mem ha' 2)) (by cfc_tac) _
  have hmem : a + Complex.I • CFC.sqrt (1 - a ^ 2) ∈ A := A.add_mem ha' (A.smul_mem hs _)
  exact ⟨IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary a hsa hnorm, hmem,
    star_mem hmem⟩

/-- For `y ∈ M`, the real part `ℜ y` and the imaginary part `ℑ y` lie in `M`.
Blueprint: lmm:von-neumann-real-imaginary-part -/
theorem realPart_imaginaryPart_mem_of_isVonNeumannSet {M : Set (H →L[ℂ] H)}
    (hM : IsVonNeumannSet M) {y : H →L[ℂ] H} (hy : y ∈ M) :
    ((ℜ y : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) ∈ M ∧
      ((ℑ y : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) ∈ M := by
  obtain ⟨A, rfl⟩ := (isVonNeumannSet_centralizer hM).2.2.1
  have hy' : y ∈ A := hy
  rw [realPart_apply_coe, imaginaryPart_apply_coe, RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hs : star y ∈ A := star_mem hy'
  exact ⟨A.smul_mem (A.add_mem hy' hs) _, A.smul_mem (A.smul_mem (A.sub_mem hy' hs) _) _⟩

/-- A nonzero `x ∈ M` is `x = (‖x‖ / 2) (u₁ + u₁* + i (u₂ + u₂*))` for unitaries `u₁, u₂` with
`u₁, u₁*, u₂, u₂* ∈ M`.
Blueprint: lmm:von-neumann-span-unitaries -/
theorem exists_unitary_decomposition_of_isVonNeumannSet {M : Set (H →L[ℂ] H)}
    (hM : IsVonNeumannSet M) {x : H →L[ℂ] H} (hx : x ∈ M) (hx0 : x ≠ 0) :
    ∃ u₁ ∈ unitary (H →L[ℂ] H), ∃ u₂ ∈ unitary (H →L[ℂ] H),
      u₁ ∈ M ∧ star u₁ ∈ M ∧ u₂ ∈ M ∧ star u₂ ∈ M ∧
      x = ‖x‖ • (2⁻¹ : ℝ) • (u₁ + star u₁ + Complex.I • (u₂ + star u₂)) := by
  have h := CStarAlgebra.norm_smul_two_inv_smul_add_four_unitary x hx0
  extract_lets u₁ u₂ at h
  have hy : ‖x‖⁻¹ • x ∈ M := by
    obtain ⟨A, rfl⟩ := (isVonNeumannSet_centralizer hM).2.2.1
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact A.smul_mem (show x ∈ A from hx) _
  obtain ⟨hre, him⟩ := realPart_imaginaryPart_mem_of_isVonNeumannSet hM hy
  obtain ⟨-, h₁, h₁'⟩ := self_add_I_smul_cfcSqrt_mem_of_isVonNeumannSet hM hre
    (ℜ (‖x‖⁻¹ • x)).2 (by
      simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx0)] using! realPart.norm_le x)
  obtain ⟨-, h₂, h₂'⟩ := self_add_I_smul_cfcSqrt_mem_of_isVonNeumannSet hM him
    (ℑ (‖x‖⁻¹ • x)).2 (by
      simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx0)] using! imaginaryPart.norm_le x)
  exact ⟨u₁, u₁.2, u₂, u₂.2, h₁, h₁', h₂, h₂', h⟩

/-- A bounded `b` with `u b = b u` for every unitary `u ∈ M` lies in `M′`.
Blueprint: lmm:commutant-of-unitaries -/
theorem mem_centralizer_of_commute_unitary {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M)
    {b : H →L[ℂ] H} (hb : ∀ u ∈ unitary (H →L[ℂ] H), u ∈ M → u * b = b * u) :
    b ∈ Set.centralizer M := by
  refine Set.mem_centralizer_iff.2 fun x hx => ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  obtain ⟨u₁, hu₁, u₂, hu₂, h₁, h₁', h₂, h₂', hx'⟩ :=
    exists_unitary_decomposition_of_isVonNeumannSet hM hx hx0
  have c₁ := hb _ hu₁ h₁
  have c₁' := hb _ (Unitary.star_mem hu₁) h₁'
  have c₂ := hb _ hu₂ h₂
  have c₂' := hb _ (Unitary.star_mem hu₂) h₂'
  rw [hx']
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, c₁, c₁', c₂, c₂']

/-! ### `M′ Ω` is a core for `S*` -/

/-- The operator `a₀ : x Ω ↦ x ξ` on `M Ω`, as the partial linear map with graph
`{(x Ω, x ξ) : x ∈ span M}`. It acts as `x Ω ↦ x ξ` when `Ω` is separating
(`tomitaLeftMap_properties`).
Blueprint: def:tomita-left-map -/
noncomputable def tomitaLeftMap (M : Set (H →L[ℂ] H)) (Ω ξ : H) : H →ₗ.[ℂ] H :=
  ((Submodule.span ℂ M).map
    ((ContinuousLinearMap.apply ℂ H Ω).toLinearMap.prod
      (ContinuousLinearMap.apply ℂ H ξ).toLinearMap)).toLinearPMap

/-- `Dom a₀ = M Ω`, `a₀ (x Ω) = x ξ` for `x ∈ M`, and `a₀` is densely defined.
Blueprint: lmm:tomita-adjoint-left-map -/
theorem tomitaLeftMap_properties {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (ξ : H) :
    (tomitaLeftMap M Ω ξ).domain = tomitaPreDomain M Ω ∧
      (∀ x ∈ M, ∃ h : x Ω ∈ (tomitaLeftMap M Ω ξ).domain, tomitaLeftMap M Ω ξ ⟨x Ω, h⟩ = x ξ) ∧
      HasDenseDomain (tomitaLeftMap M Ω ξ) := by
  sorry

/-- For `(ξ, η) ∈ Γ(S*)` and `y ∈ M`, `y Ω ∈ Dom a₀†` with `a₀† (y Ω) = y η`, and `a₀†` is
densely defined.
Blueprint: lmm:tomita-adjoint-left-map-adjoint -/
theorem tomitaAdjoint_leftMap_adjoint {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) {ξ η : H}
    (hξη : ∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) :
    (∀ y ∈ M, ∃ h : y Ω ∈ (tomitaLeftMap M Ω ξ).adjoint.domain,
        (tomitaLeftMap M Ω ξ).adjoint ⟨y Ω, h⟩ = y η) ∧
      HasDenseDomain (tomitaLeftMap M Ω ξ).adjoint := by
  sorry

/-- For `(ξ, η) ∈ Γ(S*)`, `a₀` is closable, and its closure `c` is closed and densely defined,
with `c (x Ω) = x ξ` for `x ∈ M`, `c Ω = ξ`, `Ω ∈ Dom c†` and `c† Ω = η`.
Blueprint: lmm:tomita-adjoint-closure-props -/
theorem tomitaAdjoint_leftMap_closure_props {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H}
    (hξη : ∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) :
    (tomitaLeftMap M Ω ξ).IsClosable ∧ (tomitaLeftMap M Ω ξ).closure.IsClosed ∧
      HasDenseDomain (tomitaLeftMap M Ω ξ).closure ∧
      (∀ x ∈ M, ∃ h : x Ω ∈ (tomitaLeftMap M Ω ξ).closure.domain,
        (tomitaLeftMap M Ω ξ).closure ⟨x Ω, h⟩ = x ξ) ∧
      (∃ h : Ω ∈ (tomitaLeftMap M Ω ξ).closure.domain,
        (tomitaLeftMap M Ω ξ).closure ⟨Ω, h⟩ = ξ) ∧
      ∃ h : Ω ∈ (tomitaLeftMap M Ω ξ).closure.adjoint.domain,
        (tomitaLeftMap M Ω ξ).closure.adjoint ⟨Ω, h⟩ = η := by
  sorry

/-- For `(ξ, η) ∈ Γ(S*)`, every unitary `U` in `M` commutes with the closure `c` of `a₀`.
Blueprint: lmm:tomita-adjoint-closure-commutes -/
theorem tomitaAdjoint_leftMap_closure_commute {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H}
    (hξη : ∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η)
    (U : H ≃ₗᵢ[ℂ] H) (hU : (U.toContinuousLinearEquiv : H →L[ℂ] H) ∈ M) :
    UnitaryCommutes U (tomitaLeftMap M Ω ξ).closure := by
  sorry

/-- For `(ξ, η) ∈ Γ(S*)`, the approximant `x_n` (`x_n ψ = c R_n ψ`) of the closure `c` of `a₀`
lies in `M′` for `n ≥ 1`.
Blueprint: lmm:tomita-adjoint-approximants-commutant -/
theorem tomitaAdjoint_approximant_mem_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H}
    (hξη : ∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η)
    (hc : HasDenseDomain (tomitaLeftMap M Ω ξ).closure)
    (hcl : (tomitaLeftMap M Ω ξ).closure.IsClosed) (n : ℕ) (hn : 1 ≤ n)
    (x : H →L[ℂ] H)
    (hx : ∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain,
      ∃ h : functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
          (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ψ ∈ (tomitaLeftMap M Ω ξ).closure.domain,
        x ψ = (tomitaLeftMap M Ω ξ).closure ⟨_, h⟩) :
    x ∈ Set.centralizer M := by
  sorry

/-- For `(ξ, η) ∈ Γ(S*)` and the approximants `x_n` of the closure `c` of `a₀`,
`x_n Ω → ξ` and `x_n* Ω → η`.
Blueprint: lmm:tomita-adjoint-approximants-converge -/
theorem tomitaAdjoint_approximant_tendsto {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H}
    (hξη : ∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η)
    (hc : HasDenseDomain (tomitaLeftMap M Ω ξ).closure)
    (hcl : (tomitaLeftMap M Ω ξ).closure.IsClosed) (x : ℕ → H →L[ℂ] H)
    (hx : ∀ n : ℕ, 1 ≤ n → ∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain,
      ∃ h : functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
          (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ψ ∈ (tomitaLeftMap M Ω ξ).closure.domain,
        x n ψ = (tomitaLeftMap M Ω ξ).closure ⟨_, h⟩) :
    Tendsto (fun n => x n Ω) atTop (𝓝 ξ) ∧
      Tendsto (fun n => ContinuousLinearMap.adjoint (x n) Ω) atTop (𝓝 η) := by
  sorry

/-- `(ξ, η) ∈ Γ(S*)` if and only if `(ξ, η)` lies in the closure of
`Γ(F₀) = {(b′ Ω, b′* Ω) | b′ ∈ M′}`: `S*` is the closure of `F₀`.
Blueprint: thrm:tomita-adjoint-eq-closure -/
theorem mem_tomitaAdjoint_iff_mem_closure_graph {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ξ η : H) :
    (∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) ↔
      (ξ, η) ∈ closure ((fun b : H →L[ℂ] H => (b Ω, star b Ω)) '' Set.centralizer M) := by
  sorry

/-! ### The polar decomposition of `S*` -/

/-- `S* = Δ^{1/2} J`: `(ξ, η) ∈ Γ(S*)` if and only if `J ξ ∈ Dom Δ^{1/2}` and
`Δ^{1/2} (J ξ) = η`.
Blueprint: lmm:tomita-adjoint-sqrt-conjugation -/
theorem mem_tomitaAdjoint_iff_modularOperatorSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ξ η : H) :
    (∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) ↔
      ∃ h : modularConjugation hM hΩ C hC ξ ∈ (modularOperatorSqrt hM hΩ C hC).domain,
        modularOperatorSqrt hM hΩ C hC ⟨_, h⟩ = η := by
  sorry

/-- `S* = J Δ^{-1/2}`: `(ξ, η) ∈ Γ(S*)` if and only if `ξ ∈ Dom Δ^{-1/2}` and
`η = J Δ^{-1/2} ξ`; in particular the closure of `F₀` is `J Δ^{-1/2}`.
Blueprint: crllr:tomita-adjoint-polar -/
theorem mem_tomitaAdjoint_iff_modularOperatorInvSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ξ η : H) :
    ((∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) ↔
      ∃ h : ξ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain,
        η = modularConjugation hM hΩ C hC (modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h⟩)) ∧
    ((ξ, η) ∈ closure ((fun b : H →L[ℂ] H => (b Ω, star b Ω)) '' Set.centralizer M) ↔
      ∃ h : ξ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain,
        η = modularConjugation hM hΩ C hC (modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h⟩)) := by
  sorry

/-! ### The modular objects of the commutant -/

/-- `M′` is a von Neumann algebra and `Ω` is cyclic and separating for `M′`.
Blueprint: lmm:commutant-cyclic-separating -/
theorem isCyclicSeparatingVector_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) :
    IsVonNeumannSet (Set.centralizer M) ∧ IsCyclicSeparatingVector (Set.centralizer M) Ω := by
  sorry

/-- `(ξ, η) ∈ Γ(S_{M′})` if and only if `ξ ∈ Dom Δ^{-1/2}` and `η = J Δ^{-1/2} ξ`, if and only
if `(ξ, η) ∈ Γ(S*)`.
Blueprint: lmm:commutant-tomita-operator -/
theorem tomitaOperator_centralizer_iff {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ξ η : H) :
    ((∃ h : ξ ∈ (linearizedTomitaPre (Set.centralizer M) Ω C).closure.domain,
        tomitaOperator (Set.centralizer M) Ω C ⟨ξ, h⟩ = η) ↔
      ∃ h : ξ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain,
        η = modularConjugation hM hΩ C hC (modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h⟩)) ∧
    ((∃ h : ξ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain,
        η = modularConjugation hM hΩ C hC (modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h⟩)) ↔
      ∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) := by
  sorry

/-- `ψ ∈ Dom Δ_{M′}` with `Δ_{M′} ψ = χ` if and only if `ψ ∈ Dom Δ^{-1/2}` and
`⟪Δ^{-1/2} ψ, Δ^{-1/2} φ⟫ = ⟪χ, φ⟫` for every `φ ∈ Dom Δ^{-1/2}`.
Blueprint: lmm:commutant-modular-operator-intrinsic -/
theorem mem_modularOperator_centralizer_iff {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ψ χ : H) :
    (∃ h : ψ ∈ (modularOperator (Set.centralizer M) Ω C).domain,
        modularOperator (Set.centralizer M) Ω C ⟨ψ, h⟩ = χ) ↔
      ∃ h : ψ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain,
        ∀ φ : (modularOperatorInvSqrt hM hΩ C hC).domain,
          ⟪modularOperatorInvSqrt hM hΩ C hC ⟨ψ, h⟩, modularOperatorInvSqrt hM hΩ C hC φ⟫_ℂ =
            ⟪χ, (φ : H)⟫_ℂ := by
  sorry

/-- `Δ_{M′} = Δ⁻¹`, including domains.
Blueprint: lmm:commutant-modular-operator -/
theorem modularOperator_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    modularOperator (Set.centralizer M) Ω C = (modularOperator M Ω C).inverse := by
  sorry

/-- `Δ_{M′}^{1/2} = Δ^{-1/2}` and `J_{M′} = J`.
Blueprint: lmm:commutant-modular-conjugation -/
theorem modularOperatorSqrt_modularConjugation_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    modularOperatorSqrt (isCyclicSeparatingVector_centralizer hM hΩ).1
        (isCyclicSeparatingVector_centralizer hM hΩ).2 C hC =
      modularOperatorInvSqrt hM hΩ C hC ∧
    ∀ x, modularConjugation (isCyclicSeparatingVector_centralizer hM hΩ).1
        (isCyclicSeparatingVector_centralizer hM hΩ).2 C hC x =
      modularConjugation hM hΩ C hC x := by
  sorry

/-- The modular objects of `(M′, Ω)`: `Ω` is cyclic and separating for `M′`,
`Γ(S_{M′}) = Γ(S*) = Γ(J Δ^{-1/2})`, `Δ_{M′} = Δ⁻¹`, `Δ_{M′}^{1/2} = Δ^{-1/2}` and `J_{M′} = J`.
Blueprint: thrm:commutant-modular-objects -/
theorem commutant_modular_objects {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    IsCyclicSeparatingVector (Set.centralizer M) Ω ∧
    Set.range (fun x : (linearizedTomitaPre (Set.centralizer M) Ω C).closure.domain =>
        ((x : H), tomitaOperator (Set.centralizer M) Ω C x)) =
      {p : H × H | ∃ h : C p.1 ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C p.1, h⟩ = p.2} ∧
    {p : H × H | ∃ h : C p.1 ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C p.1, h⟩ = p.2} =
      {p : H × H | ∃ h : p.1 ∈ (modularOperatorInvSqrt hM hΩ C hC).domain,
        p.2 = modularConjugation hM hΩ C hC (modularOperatorInvSqrt hM hΩ C hC ⟨p.1, h⟩)} ∧
    modularOperator (Set.centralizer M) Ω C = (modularOperator M Ω C).inverse ∧
    modularOperatorSqrt (isCyclicSeparatingVector_centralizer hM hΩ).1
        (isCyclicSeparatingVector_centralizer hM hΩ).2 C hC =
      modularOperatorInvSqrt hM hΩ C hC ∧
    ∀ x, modularConjugation (isCyclicSeparatingVector_centralizer hM hΩ).1
        (isCyclicSeparatingVector_centralizer hM hΩ).2 C hC x =
      modularConjugation hM hΩ C hC x := by
  sorry

end Physicslib4.Modular
