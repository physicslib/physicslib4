/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.ReehSchlieder.CyclicSubspace

/-!
# Correlation functions in the Reeh–Schlieder argument

Let `π` be a `*`-representation of the quasilocal algebra `𝔘` on `H`, `Ω ∈ H`, and `x ↦ U(x)`
unitaries indexed by the translations `ℝ⁴` with `U(x)π(a)Ω = π(β_x a)Ω`, where
`β_x = N.action (translationSub x)`. The local algebra of a diamond `B` inside `𝔘` is
`Set.range (N.quasilocal.ι hB)`.

For `a : Fin n → N.U.algebra B₁` and `ξ : Fin n → ℝ⁴` the ordered product
`U(ξ₁)π(a₁)U(ξ₂)π(a₂) ⋯ U(ξₙ)π(aₙ)` is written
`(List.ofFn fun i => (U (ξ i) : H →L[ℂ] H) * π (N.quasilocal.ι hB₁ (a i))).prod`; the empty
product is the identity. The partial sum `x_k = ξ₁ + ⋯ + ξ_k` at index `i : Fin n` is
`∑ j : Fin (i + 1), ξ (Fin.castLE i.isLt j)`, a sum of the shape used by
`exists_isOpen_sum_mem_of_mem_nhds`. The cyclic subspace `K₀` is
`(Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure`, as in `CyclicSubspace.lean`.

* `action_translationSub_image_range_ι` — translates of a local subalgebra.
* `translated_products_apply` — `U(ξ₁)π(a₁) ⋯ U(ξₙ)π(aₙ)Ω = π(β_{x₁}a₁ ⋯ β_{xₙ}aₙ)Ω`.
* `inner_translated_products_eq_zero_of_mem` — the correlation function vanishes near the origin.
* `inner_translated_products_update_eq_inner` — factorization in one variable.
* `inner_translated_products_eq_zero` — the correlation function vanishes identically.
* `inner_monomial_eq_zero` — orthogonality on monomials of translated local elements.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open scoped InnerProductSpace Pointwise
open Spacetime

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Translates of a local subalgebra.** For diamonds `B₁, B` and `x ∈ ℝ⁴`,
`β_x ι_{B₁}(𝔘(B₁)) = ι_{B₁ + x}(𝔘(B₁ + x))`, and if `B₁ + x ⊆ B` this set is contained in
`ι_B(𝔘(B))`. Here `B₁ + x = translationSub x • B₁`.

Blueprint: lmm:translate-local-subalgebra -/
theorem action_translationSub_image_range_ι (N : HaagKastlerNet)
    {B₁ B : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁) (hB : IsAlexandrovBasisSet B)
    (x : StandardMinkowskiSpacetime.Carrier) :
    N.action (translationSub x) '' Set.range (N.quasilocal.ι hB₁) =
        Set.range (N.quasilocal.ι (isAlexandrovBasisSet_smul (translationSub x) hB₁)) ∧
      (translationSub x • B₁ ⊆ B →
        N.action (translationSub x) '' Set.range (N.quasilocal.ι hB₁) ⊆
          Set.range (N.quasilocal.ι hB)) := by
  have h₁ : N.action (translationSub x) '' Set.range (N.quasilocal.ι hB₁) =
      Set.range (N.quasilocal.ι (isAlexandrovBasisSet_smul (translationSub x) hB₁)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨N.covEquiv _ _ a, (N.action_ι _ hB₁ a).symm⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := (N.covEquiv (translationSub x) B₁).surjective b
      exact ⟨_, ⟨a, rfl⟩, N.action_ι _ hB₁ a⟩
  refine ⟨h₁, fun h => ?_⟩
  rw [h₁]
  rintro _ ⟨a, rfl⟩
  exact ⟨_, N.quasilocal.ι_inclusion _ hB h a⟩

/-- **Translated products.** If `U(x)π(a)Ω = π(β_x a)Ω` for all `x` and `a`, then for
`a₁, …, aₙ ∈ 𝔘` and `ξ₁, …, ξₙ ∈ ℝ⁴`,
`U(ξ₁)π(a₁)U(ξ₂)π(a₂) ⋯ U(ξₙ)π(aₙ)Ω = π(β_{x₁}a₁ β_{x₂}a₂ ⋯ β_{xₙ}aₙ)Ω` with
`x_k = ξ₁ + ⋯ + ξ_k`. For `n = 0` both sides are `Ω`.

Blueprint: lmm:reeh-schlieder-translated-products -/
theorem translated_products_apply {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x a, U x (π a Ω) = π (N.action (translationSub x) a) Ω)
    {n : ℕ} (a : Fin n → N.quasilocal.carrier) (ξ : Fin n → StandardMinkowskiSpacetime.Carrier) :
    (List.ofFn fun i => (U (ξ i) : H →L[ℂ] H) * π (a i)).prod Ω =
      π ((List.ofFn fun i : Fin n =>
        N.action (translationSub (∑ j : Fin (i + 1), ξ (Fin.castLE i.isLt j))) (a i)).prod) Ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : ∀ i : Fin n, (∑ j : Fin (i.succ + 1), ξ (Fin.castLE i.succ.isLt j)) =
        ξ 0 + ∑ j : Fin (i + 1), ξ (Fin.castLE i.isLt j).succ := by
      intro i
      exact Fin.sum_univ_succ (fun j : Fin (i + 1 + 1) => ξ (Fin.castLE i.succ.isLt j))
    have key : ∀ b c, π b (π c Ω) = π (b * c) Ω := fun b c => by rw [map_mul]; rfl
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, map_mul]
    refine Eq.trans (congrArg (fun v => U (ξ 0) (π (a 0) v))
      (ih (fun i => a i.succ) (fun i => ξ i.succ))) ?_
    refine Eq.trans (congrArg (fun v => U (ξ 0) v) (key _ _)) ?_
    rw [hU, ← map_mul π, map_mul, map_list_prod, List.map_ofFn]
    congr 3
    · exact congrArg (fun x => N.action (translationSub x) (a 0)) (Fin.sum_univ_one
        (fun j : Fin 1 => ξ (Fin.castLE (Fin.isLt (0 : Fin (n + 1))) j))).symm
    · refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
      rw [Function.comp_apply, hsum i, translationSub_mul, HaagKastlerNet.action_mul_apply]

/-- **Vanishing near the origin.** Let `π`, `Ω`, `U` be as in
`covariant_translations_cyclicSubspace`. Let `B₁, B` be diamonds, let `ψ ⊥ π(𝔘(B))Ω`, and
`a₁, …, aₙ ∈ 𝔘(B₁)`. If `B₁ + (ξ₁ + ⋯ + ξₖ) ⊆ B` for every partial sum of at most `n` elements of
`V₀`, then `F(ξ) = ⟨ψ, U(ξ₁)π(a₁) ⋯ U(ξₙ)π(aₙ)Ω⟩ = 0` whenever `ξ₁, …, ξₙ ∈ V₀`.

The blueprint's open neighbourhood `V` of `0` with `B₁ + x ⊆ B` for `x ∈ V`, and the choice of
`V₀` with partial sums in `V`, are composed into the single hypothesis `hV₀`; openness of `V` and
`V₀` is not used. The binder groups are the covariant setting (`π`, `Ω`, `U`, `hU`), the diamonds
with the translation condition (`hB₁`, `hB`, `V₀`, `hV₀`), the vector `ψ` with its orthogonality
`hψ`, and the data `n`, `a`, `ξ` with `hξ`.

Blueprint: lmm:reeh-schlieder-vanishing-near-origin -/
theorem inner_translated_products_eq_zero_of_mem {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x a, U x (π a Ω) = π (N.action (translationSub x) a) Ω)
    {B₁ B : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁) (hB : IsAlexandrovBasisSet B)
    {ψ : H} (hψ : ∀ b : N.U.algebra B, ⟪ψ, π (N.quasilocal.ι hB b) Ω⟫_ℂ = 0)
    {n : ℕ} (a : Fin n → N.U.algebra B₁)
    {V₀ : Set StandardMinkowskiSpacetime.Carrier}
    (hV₀ : ∀ k ≤ n, ∀ η : Fin k → StandardMinkowskiSpacetime.Carrier,
      (∀ i, η i ∈ V₀) → translationSub (∑ i, η i) • B₁ ⊆ B)
    (ξ : Fin n → StandardMinkowskiSpacetime.Carrier) (hξ : ∀ i, ξ i ∈ V₀) :
    ⟪ψ, (List.ofFn fun i =>
      (U (ξ i) : H →L[ℂ] H) * π (N.quasilocal.ι hB₁ (a i))).prod Ω⟫_ℂ = 0 := by
  rw [translated_products_apply π Ω U hU]
  obtain ⟨b, hb⟩ : (List.ofFn fun i : Fin n => N.action (translationSub
      (∑ j : Fin (i + 1), ξ (Fin.castLE i.isLt j))) (N.quasilocal.ι hB₁ (a i))).prod ∈
      (N.quasilocal.ι hB).range := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact (action_translationSub_image_range_ι N hB₁ hB _).2
      (hV₀ (i + 1) i.isLt _ fun j => hξ _) ⟨_, ⟨a i, rfl⟩, rfl⟩
  rw [← hb]
  exact hψ b

/-- **Factorization in one variable.** Fix `ξ` and an index `k`. As a function of the `k`-th
variable `t`, `F = ⟨ψ, U(ξ₁)π(a₁) ⋯ U(ξₙ)π(aₙ)Ω⟩` has the form `⟨χ, U(t)φ⟩` with `χ ∈ H` and `φ`
in the cyclic subspace `K₀`; the blueprint's
`χ = (U(ξ₁)π(a₁) ⋯ U(ξ_{k-1})π(a_{k-1}))^* ψ` and
`φ = π(a_k)U(ξ_{k+1})π(a_{k+1}) ⋯ U(ξₙ)π(aₙ)Ω` are not fixed in the statement.

Only the covariance hypothesis is needed from the blueprint's setting, and the factors `aᵢ` may
be any elements of `𝔘`, as in `translated_products_apply`.

Blueprint: lmm:reeh-schlieder-factorization -/
theorem inner_translated_products_update_eq_inner {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x a, U x (π a Ω) = π (N.action (translationSub x) a) Ω)
    (ψ : H) {n : ℕ} (a : Fin n → N.quasilocal.carrier)
    (ξ : Fin n → StandardMinkowskiSpacetime.Carrier) (k : Fin n) :
    ∃ χ : H, ∃ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure,
      ∀ t : StandardMinkowskiSpacetime.Carrier,
        ⟪ψ, (List.ofFn fun i =>
          (U (Function.update ξ k t i) : H →L[ℂ] H) * π (a i)).prod Ω⟫_ℂ =
          ⟪χ, U t φ⟫_ℂ := by
  set K := (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure
  obtain ⟨hΩ, hπ, hUK⟩ := translations_cyclicSubspace_invariant π Ω U hU
  have memK : ∀ {m : ℕ} (b : Fin m → N.quasilocal.carrier)
      (η : Fin m → StandardMinkowskiSpacetime.Carrier),
      (List.ofFn fun i => (U (η i) : H →L[ℂ] H) * π (b i)).prod Ω ∈ K := by
    intro m
    induction m with
    | zero =>
      intro b η
      have : π 1 Ω ∈ K := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, rfl⟩)
      simpa using this
    | succ m ih =>
      intro b η
      rw [List.ofFn_succ, List.prod_cons]
      exact hUK _ _ (hπ _ _ (ih _ _))
  induction n generalizing ψ with
  | zero => exact k.elim0
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun k' => ?_) k
    · refine ⟨ψ, π (a 0) ((List.ofFn fun i =>
        (U (ξ i.succ) : H →L[ℂ] H) * π (a i.succ)).prod Ω), hπ _ _ (memK _ _), fun t => ?_⟩
      simp
    · obtain ⟨χ, φ, hφ, h⟩ := ih (((U (ξ 0) : H →L[ℂ] H) * π (a 0)).adjoint ψ)
        (fun i => a i.succ) (fun i => ξ i.succ) k'
      refine ⟨χ, φ, hφ, fun t => ?_⟩
      rw [← h t]
      have e : ∀ i : Fin m, Function.update ξ k'.succ t i.succ =
          Function.update (fun j => ξ j.succ) k' t i := fun i => by
        by_cases hi : i = k'
        · subst hi; simp
        · rw [Function.update_of_ne (fun h => hi (Fin.succ_injective _ h)),
            Function.update_of_ne hi]
      simp only [Function.update_of_ne (Fin.succ_ne_zero k').symm, e]
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl

/-- **Vanishing of the correlation functions.** In the setting of
`inner_translated_products_eq_zero_of_mem`, with `B₁ + x ⊆ B` for all `x` near `0`, suppose
moreover that every future-timelike translation subgroup `t ↦ U(t n)` has positive energy. Then
`F(ξ) = ⟨ψ, U(ξ₁)π(a₁) ⋯ U(ξₙ)π(aₙ)Ω⟩` vanishes for all `ξ ∈ (ℝ⁴)ⁿ`.

The blueprint's open neighbourhood `V` of `0` with `B₁ + x ⊆ B` for `x ∈ V` is the eventual
statement `hB₁B` in `nhds 0`, for the Euclidean topology of `ℝ⁴`. The binder groups are the
covariant setting (`π`, `Ω`, `U`, `hU`), positive energy (`hpos`), the diamonds with the
translation condition (`hB₁`, `hB`, `hB₁B`), the vector `ψ` with its orthogonality `hψ`, and the
data `n`, `a`, `ξ`.

Blueprint: lmm:reeh-schlieder-correlations-vanish -/
theorem inner_translated_products_eq_zero {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x a, U x (π a Ω) = π (N.action (translationSub x) a) Ω)
    (hpos : ∀ n : StandardMinkowskiSpacetime.Carrier,
      (n : SpacetimeModel) ∈ minkowskiForwardCone 0 → IsPositiveEnergy (fun t : ℝ => U (t • n)))
    {B₁ B : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁) (hB : IsAlexandrovBasisSet B)
    (hB₁B : ∀ᶠ x in nhds 0, translationSub x • B₁ ⊆ B)
    {ψ : H} (hψ : ∀ b : N.U.algebra B, ⟪ψ, π (N.quasilocal.ι hB b) Ω⟫_ℂ = 0)
    {n : ℕ} (a : Fin n → N.U.algebra B₁) (ξ : Fin n → StandardMinkowskiSpacetime.Carrier) :
    ⟪ψ, (List.ofFn fun i =>
      (U (ξ i) : H →L[ℂ] H) * π (N.quasilocal.ι hB₁ (a i))).prod Ω⟫_ℂ = 0 := by
  obtain ⟨V₀, hV₀o, hV₀0, hV₀⟩ :=
    exists_isOpen_sum_mem_of_mem_nhds (V := {x | translationSub x • B₁ ⊆ B}) hB₁B n
  have P : ∀ m, ∀ ξ : Fin n → StandardMinkowskiSpacetime.Carrier,
      (∀ i : Fin n, m ≤ i.val → ξ i ∈ V₀) →
      ⟪ψ, (List.ofFn fun i =>
        (U (ξ i) : H →L[ℂ] H) * π (N.quasilocal.ι hB₁ (a i))).prod Ω⟫_ℂ = 0 := by
    intro m
    induction m with
    | zero =>
      exact fun ξ hξ => inner_translated_products_eq_zero_of_mem π Ω U hU hB₁ hB hψ a
        hV₀ ξ fun i => hξ i (Nat.zero_le _)
    | succ m ih =>
      intro ξ hξ
      by_cases hm : m < n
      · obtain ⟨χ, φ, hφ, h⟩ := inner_translated_products_update_eq_inner π Ω U hU ψ
          (fun i => N.quasilocal.ι hB₁ (a i)) ξ ⟨m, hm⟩
        have hz := inner_translation_eq_zero U (translations_add_cyclicSubspace π Ω U hU φ hφ)
          hpos χ hV₀o ⟨0, hV₀0⟩ fun t ht => by
            rw [← h t]
            refine ih _ fun i hi => ?_
            by_cases hik : i = ⟨m, hm⟩
            · subst hik; simpa using ht
            · have : i.val ≠ m := fun e => hik (Fin.ext e)
              rw [Function.update_of_ne hik]
              exact hξ i (by omega)
        have e := h (ξ ⟨m, hm⟩)
        rw [Function.update_eq_self] at e
        exact e.trans (hz _)
      · exact ih ξ fun i hi => hξ i (by omega)
  exact P n ξ fun i hi => absurd i.isLt (by omega)

/-- **Orthogonality on monomials.** In the setting of `inner_translated_products_eq_zero`, for
every `n ≥ 0`, all `y₁, …, yₙ ∈ ℝ⁴` and all `a₁, …, aₙ ∈ 𝔘(B₁)`,
`⟨ψ, π(β_{y₁}a₁ ⋯ β_{yₙ}aₙ)Ω⟩ = 0`, the empty product being `1`.

The binder groups are the covariant setting (`π`, `Ω`, `U`, `hU`), positive energy (`hpos`), the
diamonds with the translation condition (`hB₁`, `hB`, `hB₁B`), the vector `ψ` with its
orthogonality `hψ`, and the data `n`, `a`, `y`.

Blueprint: lmm:reeh-schlieder-monomial-orthogonal -/
theorem inner_monomial_eq_zero {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x a, U x (π a Ω) = π (N.action (translationSub x) a) Ω)
    (hpos : ∀ n : StandardMinkowskiSpacetime.Carrier,
      (n : SpacetimeModel) ∈ minkowskiForwardCone 0 → IsPositiveEnergy (fun t : ℝ => U (t • n)))
    {B₁ B : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁) (hB : IsAlexandrovBasisSet B)
    (hB₁B : ∀ᶠ x in nhds 0, translationSub x • B₁ ⊆ B)
    {ψ : H} (hψ : ∀ b : N.U.algebra B, ⟪ψ, π (N.quasilocal.ι hB b) Ω⟫_ℂ = 0)
    {n : ℕ} (a : Fin n → N.U.algebra B₁) (y : Fin n → StandardMinkowskiSpacetime.Carrier) :
    ⟪ψ, π ((List.ofFn fun i =>
      N.action (translationSub (y i)) (N.quasilocal.ι hB₁ (a i))).prod) Ω⟫_ℂ = 0 := by
  set ξ : Fin n → StandardMinkowskiSpacetime.Carrier := fun i =>
    y i - (if h : (i : ℕ) = 0 then 0 else y ⟨i - 1, by omega⟩)
  have hx : ∀ k (hk : k < n), ∑ j : Fin (k + 1), ξ (Fin.castLE hk j) = y ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simp [ξ]; rfl
    | succ k ih =>
      intro hk
      rw [Fin.sum_univ_castSucc]
      have := ih (by omega)
      simp only [Fin.castLE_castSucc] at this ⊢
      rw [this]
      simp [ξ, Fin.castLE, Fin.last]
  have h := inner_translated_products_eq_zero π Ω U hU hpos hB₁ hB hB₁B hψ a ξ
  rw [translated_products_apply π Ω U hU] at h
  convert h using 6
  funext i
  rw [hx i i.isLt]

end HaagKastler
end AQFT
end Physicslib4
