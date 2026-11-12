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
    exact cfc_mem_of_isVonNeumannSet hM (A.sub_mem A.one_mem (A.pow_mem ha' 2)) _
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
  have hdom : (tomitaLeftMap M Ω ξ).domain = tomitaPreDomain M Ω := by
    rw [tomitaLeftMap, Submodule.toLinearPMap_domain, ← Submodule.map_comp]
    rfl
  have hg : ∀ (p : H × H) (_ : p ∈ (Submodule.span ℂ M).map
      ((ContinuousLinearMap.apply ℂ H Ω).toLinearMap.prod
        (ContinuousLinearMap.apply ℂ H ξ).toLinearMap)) (_ : p.1 = 0), p.2 = 0 := by
    rintro _ ⟨a, ha, rfl⟩ h
    have ha' : a ∈ M := span_eq_of_isVonNeumannSet hM ▸ ha
    change a ξ = 0
    rw [(isSeparatingVector_of_isCyclicSeparatingVector hΩ).1 a ha' h, zero_apply]
  refine ⟨hdom, fun x hx => ?_, ?_⟩
  · have hxd : x Ω ∈ (tomitaLeftMap M Ω ξ).domain :=
      hdom ▸ Submodule.mem_map_of_mem (Submodule.subset_span hx)
    refine ⟨hxd, ?_⟩
    have h1 := Submodule.mem_graph_toLinearPMap hg ⟨x Ω, hxd⟩
    have h2 := Submodule.sub_mem _ h1 (Submodule.mem_map_of_mem (Submodule.subset_span hx))
    exact sub_eq_zero.mp (hg _ h2 (sub_self _))
  · rw [HasDenseDomain, hdom]
    exact (tomitaPre_dense_involutive hM hΩ).1

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
  obtain ⟨hdom, hval, hd⟩ := tomitaLeftMap_properties hM hΩ ξ
  have hcore := (mem_tomitaAdjoint_iff_inner_algebra hM hΩ C hC ξ η).1 hξη
  obtain ⟨A, hA⟩ := (isVonNeumannSet_centralizer hM).2.2.1
  have hspan : (Submodule.span ℂ M : Set (H →L[ℂ] H)) = M := by
    rw [← hA]; exact congrArg _ (Submodule.span_eq (A.toSubalgebra.toSubmodule))
  have key : ∀ y ∈ M, ∃ h : y Ω ∈ (tomitaLeftMap M Ω ξ).adjoint.domain,
      (tomitaLeftMap M Ω ξ).adjoint ⟨y Ω, h⟩ = y η := by
    intro y hy
    have h' : ∀ ζ : (tomitaLeftMap M Ω ξ).domain,
        ⟪y η, (ζ : H)⟫_ℂ = ⟪y Ω, tomitaLeftMap M Ω ξ ζ⟫_ℂ := by
      rintro ⟨ζ, hζ⟩
      have hζ' : ζ ∈ tomitaPreDomain M Ω := hdom ▸ hζ
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hζ'
      have hxM : x ∈ M := hspan ▸ hx
      obtain ⟨hx', hxv⟩ := hval x hxM
      have hz : star y * x ∈ M := by
        rw [← hA] at hy hxM ⊢
        exact mul_mem (star_mem (show y ∈ A from hy)) (show x ∈ A from hxM)
      have := hcore _ hz
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply] at hxv ⊢
      have e1 : ⟪y η, x Ω⟫_ℂ = ⟪η, (star y * x) Ω⟫_ℂ := by
        rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
      have e2 : ⟪y Ω, x ξ⟫_ℂ = ⟪(star (star y * x)) Ω, ξ⟫_ℂ := by
        rw [star_mul, star_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_left]
      rw [hxv, e1, e2, ← inner_conj_symm, ← this, inner_conj_symm]
    have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨y η, h'⟩
    exact ⟨hmem, LinearPMap.adjoint_apply_eq hd ⟨y Ω, hmem⟩ h'⟩
  refine ⟨key, hΩ.1.mono ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (key y hy).1

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
  obtain ⟨-, hval, hd⟩ := tomitaLeftMap_properties hM hΩ ξ
  obtain ⟨hadj, hd'⟩ := tomitaAdjoint_leftMap_adjoint hM hΩ C hC hξη
  have hcl : (tomitaLeftMap M Ω ξ).IsClosable := isClosable_of_dense_adjoint hd hd'
  have hle := (tomitaLeftMap M Ω ξ).le_closure
  have hcval : ∀ x ∈ M, ∃ h : x Ω ∈ (tomitaLeftMap M Ω ξ).closure.domain,
      (tomitaLeftMap M Ω ξ).closure ⟨x Ω, h⟩ = x ξ := fun x hx => by
    obtain ⟨h, hv⟩ := hval x hx
    exact ⟨hle.1 h, (hle.2 (x := ⟨x Ω, h⟩) rfl).symm.trans hv⟩
  have h1 : (1 : H →L[ℂ] H) ∈ M := hM.2 ▸ Set.one_mem_centralizer
  refine ⟨hcl, hcl.closure_isClosed, hasDenseDomain_closure hd hcl, hcval, hcval 1 h1, ?_⟩
  rw [adjoint_closure_eq_adjoint hd hcl]
  exact hadj 1 h1

/-- Every unitary `U` in `M` commutes with the closure `c` of `a₀ : x Ω ↦ x ξ`.
Blueprint: lmm:tomita-adjoint-closure-commutes -/
theorem tomitaAdjoint_leftMap_closure_commute {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ξ : H}
    (U : H ≃ₗᵢ[ℂ] H) (hU : (U.toContinuousLinearEquiv : H →L[ℂ] H) ∈ M) :
    UnitaryCommutes U (tomitaLeftMap M Ω ξ).closure := by
  set f := tomitaLeftMap M Ω ξ
  -- a bounded operator commuting with `f` commutes with its closure
  have hcl : ∀ V : H →L[ℂ] H,
      (∀ x (hx : x ∈ f.domain), ∃ h : V x ∈ f.domain, f ⟨V x, h⟩ = V (f ⟨x, hx⟩)) →
      ∀ x (hx : x ∈ f.closure.domain),
        ∃ h : V x ∈ f.closure.domain, f.closure ⟨V x, h⟩ = V (f.closure ⟨x, hx⟩) := by
    intro V hV
    by_cases hf : f.IsClosable
    · intro x hx
      let P : H × H →L[ℂ] H × H := V.prodMap V
      have hsub : f.graph.map (P : H × H →ₗ[ℂ] H × H) ≤ f.graph := by
        rintro _ ⟨p, hp, rfl⟩
        obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff f).1 hp
        obtain ⟨h, he⟩ := hV y y.2
        exact (LinearPMap.mem_graph_iff f).2 ⟨⟨_, h⟩, by simp [P, hy1], by simp [P, he, hy2]⟩
      have hmem : P (x, f.closure ⟨x, hx⟩) ∈ f.closure.graph := by
        rw [← hf.graph_closure_eq_closure_graph]
        exact Submodule.topologicalClosure_mono hsub
          (Submodule.topologicalClosure_map P f.graph (Submodule.mem_map_of_mem
            (hf.graph_closure_eq_closure_graph ▸ f.closure.mem_graph ⟨x, hx⟩)))
      obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hmem
      obtain ⟨y, hy⟩ := y
      simp only [P, ContinuousLinearMap.coe_prodMap', Prod.map_apply] at hy1 hy2
      subst hy1
      exact ⟨hy, hy2⟩
    · rw [LinearPMap.closure_def' hf]
      exact hV
  obtain ⟨hdom, hval, -⟩ := tomitaLeftMap_properties hM hΩ ξ
  have hmul : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M := fun a ha b hb => by
    rw [← hM.2] at ha hb ⊢
    exact Set.mul_mem_centralizer ha hb
  -- a unitary in `M` commutes with `a₀`
  have h0 : ∀ V : H →L[ℂ] H, V ∈ M →
      ∀ x (hx : x ∈ f.domain), ∃ h : V x ∈ f.domain, f ⟨V x, h⟩ = V (f ⟨x, hx⟩) := by
    intro V hV x hx
    have hx' := hx
    rw [hdom] at hx'
    obtain ⟨a, ha, rfl⟩ := hx'
    have ha' : a ∈ M := span_eq_of_isVonNeumannSet hM ▸ ha
    obtain ⟨h1, e1⟩ := hval (V * a) (hmul V hV a ha')
    obtain ⟨h2, e2⟩ := hval a ha'
    refine ⟨h1, ?_⟩
    exact e1.trans (congrArg V e2.symm)
  have hUs : (U.symm.toContinuousLinearEquiv : H →L[ℂ] H) ∈ M := by
    have := hM.1 _ hU
    rwa [show (U.toContinuousLinearEquiv : H →L[ℂ] H) = (U : H →L[ℂ] H) from rfl,
      LinearIsometryEquiv.star_eq_symm] at this
  exact ⟨hcl _ (h0 _ hU), hcl _ (h0 _ hUs)⟩

/-- When the closure `c` of `a₀` is closed and densely defined, the approximant `x_n`
(`x_n ψ = c R_n ψ`) lies in `M′` for `n ≥ 1`.
Blueprint: lmm:tomita-adjoint-approximants-commutant -/
theorem tomitaAdjoint_approximant_mem_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ξ : H}
    (hc : HasDenseDomain (tomitaLeftMap M Ω ξ).closure)
    (hcl : (tomitaLeftMap M Ω ξ).closure.IsClosed) (n : ℕ) (hn : 1 ≤ n)
    (x : H →L[ℂ] H)
    (hx : ∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain,
      ∃ h : functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
          (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ψ ∈ (tomitaLeftMap M Ω ξ).closure.domain,
        x ψ = (tomitaLeftMap M Ω ξ).closure ⟨_, h⟩) :
    x ∈ Set.centralizer M := by
  refine mem_centralizer_of_commute_unitary hM fun u hu huM => ?_
  let U : H ≃ₗᵢ[ℂ] H := Unitary.linearIsometryEquiv ⟨u, hu⟩
  have hcomm := approximant_operator_commute hc hcl U
    (tomitaAdjoint_leftMap_closure_commute hM hΩ U huM) n hn x hx
  exact ContinuousLinearMap.ext hcomm

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
  have hsub : ∀ (T : H →ₗ.[ℂ] H) (a b : H) (ha : a ∈ T.domain) (hb : b ∈ T.domain),
      T ⟨a - b, T.domain.sub_mem ha hb⟩ = T ⟨a, ha⟩ - T ⟨b, hb⟩ := fun T a b ha hb =>
    T.toFun.map_sub ⟨a, ha⟩ ⟨b, hb⟩
  set c := (tomitaLeftMap M Ω ξ).closure
  obtain ⟨-, -, -, -, ⟨hΩc, hcΩ⟩, hΩa, hcaΩ⟩ :=
    tomitaAdjoint_leftMap_closure_props hM hΩ C hC hξη
  obtain ⟨-, -, -, hnorm⟩ := absoluteValue_domain hc hcl
  obtain ⟨hRall, hKall⟩ := approximant_convergence hc hcl
  obtain ⟨hK', hΩabs, hKt⟩ := hKall Ω hΩc
  obtain ⟨hRη, hRt⟩ := hRall η
  constructor
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine (tendsto_iff_norm_sub_tendsto_zero.1 hKt).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨hR, hK, h₁, -, habs, -, -⟩ := approximant_range hc hcl n hn Ω
    obtain ⟨h, hxn⟩ := hx n hn ⟨Ω, hR⟩
    have e1 : c ⟨_, h⟩ - c ⟨Ω, hΩc⟩ = c ⟨_, c.domain.sub_mem h hΩc⟩ :=
      (hsub c _ _ h hΩc).symm
    rw [hcΩ, ← hxn] at e1
    have e2 : absoluteValue c hc hcl ⟨_, (absoluteValue c hc hcl).domain.sub_mem h₁ hΩabs⟩ =
        functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
            (fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)) ⟨Ω, hK' n⟩ -
          absoluteValue c hc hcl ⟨Ω, hΩabs⟩ := by
      rw [← habs]; exact hsub _ _ _ h₁ hΩabs
    rw [e1, ← hnorm _ ((absoluteValue c hc hcl).domain.sub_mem h₁ hΩabs)
      (c.domain.sub_mem h hΩc), e2]
  · refine hRt.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨x', -, huniq, -, hadj⟩ := approximant_operator hc hcl n hn
    rw [huniq (x n) (hx n hn)]
    obtain ⟨h, e⟩ := hadj ⟨Ω, hΩa⟩
    rw [e]
    have key : ∀ (y : H) (hy : y = η) (h' : y ∈ (functionalCalculus
        (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain),
        functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
          (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ⟨y, h'⟩ =
        functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
          (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ⟨η, hRη n⟩ := by
      rintro _ rfl _; rfl
    exact (key _ hcaΩ h).symm

/-- `(ξ, η) ∈ Γ(S*)` if and only if `(ξ, η)` lies in the closure of
`Γ(F₀) = {(b′ Ω, b′* Ω) | b′ ∈ M′}`: `S*` is the closure of `F₀`.
Blueprint: thrm:tomita-adjoint-eq-closure -/
theorem mem_tomitaAdjoint_iff_mem_closure_graph {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ξ η : H) :
    (∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) ↔
      (ξ, η) ∈ closure ((fun b : H →L[ℂ] H => (b Ω, star b Ω)) '' Set.centralizer M) := by
  refine ⟨fun hξη => ?_, mem_tomitaAdjoint_of_mem_closure_graph hM hΩ C hC⟩
  obtain ⟨-, hcl, hc, -⟩ := tomitaAdjoint_leftMap_closure_props hM hΩ C hC hξη
  let x : ℕ → H →L[ℂ] H := fun n =>
    if hn : 1 ≤ n then Classical.choose (approximant_operator hc hcl n hn) else 0
  have hx : ∀ n (hn : 1 ≤ n), x n = Classical.choose (approximant_operator hc hcl n hn) :=
    fun n hn => by simp only [x, hn, dite_true]
  have hxs : ∀ n : ℕ, 1 ≤ n → ∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
      fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain,
      ∃ h : functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
          (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ψ ∈ (tomitaLeftMap M Ω ξ).closure.domain,
        x n ψ = (tomitaLeftMap M Ω ξ).closure ⟨_, h⟩ := fun n hn => by
    rw [hx n hn]
    exact (Classical.choose_spec (approximant_operator hc hcl n hn)).1
  obtain ⟨h1, h2⟩ := tomitaAdjoint_approximant_tendsto hM hΩ C hC hξη hc hcl x hxs
  refine mem_closure_of_tendsto (h1.prodMk_nhds h2) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact ⟨x n, tomitaAdjoint_approximant_mem_centralizer hM hΩ hc hcl n hn _ (hxs n hn),
    by simp only [ContinuousLinearMap.star_eq_adjoint]⟩

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
  set A := modularOperatorSqrt hM hΩ C hC
  set J := modularConjugation hM hΩ C hC
  obtain ⟨hdomS, hJ⟩ := tomitaOperator_eq_modularConjugation_sqrt hM hΩ C hC
  have hJJ : ∀ φ, J (J φ) = φ := (modularConjugation_involution hM hΩ C hC).1
  have hyps := linearizedTomita_closure_polar_hyps hM hΩ C hC
  have hadj : A.adjoint = A :=
    LinearPMap.isSelfAdjoint_def.mp (absoluteValue_domain hyps.1 hyps.2.1).2.1
  have hd : Dense (A.domain : Set H) :=
    hdomS ▸ (linearizedTomita_closure_properties hM hΩ C hC).2.1
  have hinner : ∀ y, ⟪ξ, J y⟫_ℂ = ⟪y, J ξ⟫_ℂ := fun y => by
    have := inner_map_map_of_conjLinearIsometry J.toLinearIsometry (J ξ) y
    simpa [hJJ] using this
  rw [mem_tomitaAdjoint_iff hM hΩ C hC, ← hadj]
  have hcond : (∀ ζ : (linearizedTomitaPre M Ω C).closure.domain,
      ⟪ξ, tomitaOperator M Ω C ζ⟫_ℂ = ⟪(ζ : H), η⟫_ℂ) ↔
      ∀ ζ : A.domain, ⟪η, (ζ : H)⟫_ℂ = ⟪J ξ, A ζ⟫_ℂ := by
    constructor
    · intro h ζ
      have := h ⟨ζ, hdomS.ge ζ.2⟩
      rw [hJ _ _ ζ.2, hinner] at this
      simpa using congrArg (starRingEnd ℂ) this.symm
    · intro h ζ
      have := h ⟨ζ, hdomS.le ζ.2⟩
      rw [hJ _ _ (hdomS.le ζ.2), hinner]
      simpa using congrArg (starRingEnd ℂ) this.symm
  rw [hcond]
  constructor
  · intro h
    have hmem : J ξ ∈ A.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists _ ⟨η, h⟩
    exact ⟨hmem, LinearPMap.adjoint_apply_eq hd ⟨J ξ, hmem⟩ h⟩
  · rintro ⟨h, rfl⟩ ζ
    exact LinearPMap.adjoint_isFormalAdjoint hd ⟨J ξ, h⟩ ζ

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
  set J := modularConjugation hM hΩ C hC
  obtain ⟨hJJ, hconj⟩ := modularConjugation_involution hM hΩ C hC
  have hJs : ∀ x, J.symm x = J x := fun x => by
    conv_lhs => rw [← hJJ x]
    exact J.symm_apply_apply _
  have first : (∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ = η) ↔
      ∃ h : ξ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain,
        η = J (modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h⟩) := by
    rw [mem_tomitaAdjoint_iff_modularOperatorSqrt hM hΩ C hC ξ η, ← hconj]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨show J.symm ξ ∈ _ by rwa [hJs], ?_⟩
      change _ = J (J _)
      rw [hJJ]
      congr 1
      exact Subtype.ext (hJs ξ).symm
    · rintro ⟨h, rfl⟩
      refine ⟨show J ξ ∈ _ by rw [← hJs]; exact h, ?_⟩
      change _ = J (J _)
      rw [hJJ]
      congr 1
      exact Subtype.ext (hJs ξ).symm
  exact ⟨first, (mem_tomitaAdjoint_iff_mem_closure_graph hM hΩ C hC ξ η).symm.trans first⟩

/-! ### The modular objects of the commutant -/

/-- `M′` is a von Neumann algebra and `Ω` is cyclic and separating for `M′`.
Blueprint: lmm:commutant-cyclic-separating -/
theorem isCyclicSeparatingVector_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) :
    IsVonNeumannSet (Set.centralizer M) ∧ IsCyclicSeparatingVector (Set.centralizer M) Ω := by
  obtain ⟨h1, h2, -⟩ := isVonNeumannSet_centralizer hM
  exact ⟨h1, hΩ.2, by rw [h2]; exact hΩ.1⟩

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
  obtain ⟨hM', hΩ'⟩ := isCyclicSeparatingVector_centralizer hM hΩ
  have hF : Set.range (fun x : tomitaPreDomain (Set.centralizer M) Ω =>
      ((x : H), tomitaPre (Set.centralizer M) Ω x)) =
      (fun b : H →L[ℂ] H => (b Ω, star b Ω)) '' Set.centralizer M := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨b, hb, hbx⟩ := Submodule.mem_map.mp x.2
      have hb' : b ∈ Set.centralizer M := (span_eq_of_isVonNeumannSet hM').subset hb
      have e : x = ⟨b Ω, Submodule.mem_map_of_mem (Submodule.subset_span hb')⟩ :=
        Subtype.ext hbx.symm
      rw [e]
      exact ⟨b, hb', Prod.ext rfl ((tomitaPre_apply hM hΩ).2 b hb').symm⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b Ω, Submodule.mem_map_of_mem (Submodule.subset_span hb)⟩,
        Prod.ext rfl ((tomitaPre_apply hM hΩ).2 b hb)⟩
  have hA : (∃ h : ξ ∈ (linearizedTomitaPre (Set.centralizer M) Ω C).closure.domain,
      tomitaOperator (Set.centralizer M) Ω C ⟨ξ, h⟩ = η) ↔
      (ξ, η) ∈ closure ((fun b : H →L[ℂ] H => (b Ω, star b Ω)) '' Set.centralizer M) := by
    rw [← hF, ← tomitaOperator_graph_eq_closure hM' hΩ' C hC]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨⟨ξ, h⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨h1, h2⟩ := Prod.mk.inj hx
      subst h1
      exact ⟨x.2, h2⟩
  obtain ⟨hB, hC'⟩ := mem_tomitaAdjoint_iff_modularOperatorInvSqrt hM hΩ C hC ξ η
  exact ⟨hA.trans hC', hB.symm⟩

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
  obtain ⟨hM', hΩ'⟩ := isCyclicSeparatingVector_centralizer hM hΩ
  set D := modularOperatorInvSqrt hM hΩ C hC
  set J := modularConjugation hM hΩ C hC
  set T := (linearizedTomitaPre (Set.centralizer M) Ω C).closure
  have hJ : ∀ a b, ⟪J a, J b⟫_ℂ = ⟪b, a⟫_ℂ := fun a b =>
    (inner_map_map_of_conjLinearIsometry J.toLinearIsometry a b).trans (inner_conj_symm _ _)
  have hTD : ∀ x (h : x ∈ T.domain), ∃ h' : x ∈ D.domain,
      tomitaOperator (Set.centralizer M) Ω C ⟨x, h⟩ = J (D ⟨x, h'⟩) := fun x h =>
    ((tomitaOperator_centralizer_iff hM hΩ C hC x _).1.mp ⟨h, rfl⟩).imp fun _ e => e
  have hDT : ∀ x (h' : x ∈ D.domain), ∃ h : x ∈ T.domain,
      tomitaOperator (Set.centralizer M) Ω C ⟨x, h⟩ = J (D ⟨x, h'⟩) := fun x h' =>
    (tomitaOperator_centralizer_iff hM hΩ C hC x _).1.mpr ⟨h', rfl⟩
  rw [mem_modularOperator_iff hM' hΩ' C hC]
  constructor
  · rintro ⟨h, H⟩
    obtain ⟨h', e⟩ := hTD ψ h
    refine ⟨h', fun φ => ?_⟩
    obtain ⟨hφ, eφ⟩ := hDT φ φ.2
    have := H ⟨φ, hφ⟩
    rw [eφ, e, hJ] at this
    exact this
  · rintro ⟨h', H⟩
    obtain ⟨h, e⟩ := hDT ψ h'
    refine ⟨h, fun φ => ?_⟩
    obtain ⟨hφ, eφ⟩ := hTD φ φ.2
    rw [eφ, e, hJ]
    exact H ⟨φ, hφ⟩

/-- `Δ_{M′} = Δ⁻¹`, including domains.
Blueprint: lmm:commutant-modular-operator -/
theorem modularOperator_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    modularOperator (Set.centralizer M) Ω C = (modularOperator M Ω C).inverse := by
  obtain ⟨hpos, hsa, -, hker, -, -⟩ := modularOperator_properties hM hΩ C hC
  set P := modularOperatorInvSqrt hM hΩ C hC
  have hPsa : IsSelfAdjoint P := (inv_sqrt_functionalCalculus_positive hsa).2
  have hPd : HasDenseDomain P := hPsa.dense_domain
  have hPP : P.adjoint = P := hPsa.star_eq
  have hg : ∀ (T : H →ₗ.[ℂ] H) x y, (x, y) ∈ T.graph ↔ ∃ h : x ∈ T.domain, T ⟨x, h⟩ = y :=
    fun T x y => by
      rw [LinearPMap.mem_graph_iff]
      constructor
      · rintro ⟨z, rfl, h2⟩
        exact ⟨z.2, h2⟩
      · rintro ⟨h, rfl⟩
        exact ⟨⟨x, h⟩, rfl, rfl⟩
  have key : ∀ w χ : H, (∀ φ : P.domain, ⟪w, P φ⟫_ℂ = ⟪χ, (φ : H)⟫_ℂ) ↔
      ∃ h : w ∈ P.domain, P ⟨w, h⟩ = χ := fun w χ => by
    have e : (∀ φ : P.domain, ⟪w, P φ⟫_ℂ = ⟪χ, (φ : H)⟫_ℂ) ↔
        ∃ h : w ∈ P.adjoint.domain, P.adjoint ⟨w, h⟩ = χ :=
      ⟨fun h => ⟨_, adjoint_apply_eq_of_forall_inner hPd
          ((mem_adjoint_domain_iff_exists hPd w).mpr ⟨χ, h⟩) h⟩,
        fun ⟨hw, e⟩ φ => e ▸ (LinearPMap.adjoint_isFormalAdjoint hPd ⟨w, hw⟩ φ).symm⟩
    rw [hPP] at e
    exact e
  rw [← pmapMul_inv_sqrt_functionalCalculus hsa hpos hker]
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨ψ, χ⟩ => ?_)
  change (ψ, χ) ∈ (modularOperator (Set.centralizer M) Ω C).graph ↔ (ψ, χ) ∈ (pmapMul P P).graph
  rw [mem_graph_pmapMul_iff, hg, mem_modularOperator_centralizer_iff hM hΩ C hC]
  simp only [hg]
  constructor
  · rintro ⟨h, hφ⟩
    exact ⟨_, ⟨h, rfl⟩, (key _ χ).mp hφ⟩
  · rintro ⟨w, ⟨h, rfl⟩, hw⟩
    exact ⟨h, (key _ χ).mpr hw⟩

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
  obtain ⟨hM', hΩ'⟩ := isCyclicSeparatingVector_centralizer hM hΩ
  obtain ⟨hpos, hsa, -, hker, -, -⟩ := modularOperator_properties hM hΩ C hC
  obtain ⟨h, heq⟩ := sqrt_functionalCalculus_inverse hsa hker
  have htr : ∀ {B D : H →ₗ.[ℂ] H} (hB : IsSelfAdjoint B) (hD : IsSelfAdjoint D), B = D →
      functionalCalculus hB (fun x => ((Real.sqrt x : ℝ) : ℂ)) =
        functionalCalculus hD (fun x => ((Real.sqrt x : ℝ) : ℂ)) := by
    rintro _ _ _ _ rfl; rfl
  have h1 : modularOperatorSqrt hM' hΩ' C hC = modularOperatorInvSqrt hM hΩ C hC :=
    (htr (modularOperator_isSelfAdjoint hM' hΩ' C hC) h
      (modularOperator_centralizer hM hΩ C hC)).trans heq
  have happ : ∀ {P Q : H →ₗ.[ℂ] H} (hPQ : P = Q) (ψ : H) (hP : ψ ∈ P.domain)
      (hQ : ψ ∈ Q.domain), P ⟨ψ, hP⟩ = Q ⟨ψ, hQ⟩ := by
    rintro _ _ rfl _ _ _; rfl
  refine ⟨h1, fun x => (eq_modularConjugation_of_continuous hM' hΩ' C hC
    (modularConjugation hM hΩ C hC) (modularConjugation hM hΩ C hC).continuous
    (fun ψ h₁ h₂ => ?_) x).symm⟩
  obtain ⟨h₄, h₅⟩ := ((tomitaOperator_centralizer_iff hM hΩ C hC ψ _).1.mp ⟨h₁, rfl⟩)
  rw [h₅, happ h1 ψ h₂ h₄]

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
  have hT := tomitaOperator_centralizer_iff hM hΩ C hC
  refine ⟨(isCyclicSeparatingVector_centralizer hM hΩ).2, ?_, ?_,
    modularOperator_centralizer hM hΩ C hC,
    modularOperatorSqrt_modularConjugation_centralizer hM hΩ C hC⟩
  · ext ⟨ξ, η⟩
    constructor
    · rintro ⟨x, hx⟩
      cases hx
      exact ((hT _ _).1.trans (hT _ _).2).mp ⟨x.2, rfl⟩
    · intro h
      obtain ⟨h, e⟩ := ((hT ξ η).1.trans (hT ξ η).2).mpr h
      exact ⟨⟨ξ, h⟩, Prod.ext rfl e⟩
  · ext ⟨ξ, η⟩
    exact (hT ξ η).2.symm

end Physicslib4.Modular
