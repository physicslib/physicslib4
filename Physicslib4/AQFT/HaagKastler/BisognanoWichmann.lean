/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.Borchers
import Physicslib4.AQFT.HaagKastler.CovariantVacuum

/-!
# The wedge corollary of Borchers' theorem and Bisognano–Wichmann up to an internal symmetry

Borchers' theorem for the commutant `M'` gives the version of the theorem for unitaries that map
`M` into itself under `x ↦ V(-t) x V(t)`, `t ≥ 0`. Applied to the algebra `R(W_R)` of the right
wedge and the lightlike translations `U(t l₊)`, `U(t l₋)` along its edges, it fixes the action of
the wedge modular group on every translation: `Δ^{is} U(a) Δ^{-is} = U(Λ(-2πs) a)`.

Conventions:
* `l₊ = (1, 1, 0, 0)` and `l₋ = (1, -1, 0, 0)` (local notation, as in
  `Physicslib4.AQFT.HaagKastler.Wedges`).
* For `a ∈ ℝ⁴`, `U(a)` is `U (translationSub a)`.
* `V T V⁻¹` for a unitary `V` and a bounded operator `T` is written `conj[V] T` (local notation),
  and `V M V⁻¹` for a set `M` of bounded operators is `(fun a => conj[V] a) '' M`, as in
  `Physicslib4.AQFT.HaagKastler.CovariantVacuum`.
* For a general von Neumann algebra `M` with cyclic and separating `Ω`: `U[t]` is `Δ^{it}`,
  `V[t]` is `V(t)` and `𝒥[T]` is `J T J`, all as bounded operators, for the binders
  `hM hΩ C hC V` in scope, as in `Physicslib4.AQFT.Borchers`.
* For the right wedge: `Δ[s]` is `Δ_{W_R}^{is}`, `𝒥R[T]` is `J_{W_R} T J_{W_R}` and `Tr[a]` is
  `U(a)`, all as bounded operators, for the binders `N π U hΩ C hC` in scope. The standardness of
  `(R(W_R), Ω)` enters as the proof `hΩ` that names the modular objects; under weak additivity it
  is supplied by `IsCovariantVacuumRep.wedge_isCyclicSeparatingVector`.
-/

/-- The conjugate `V a V⁻¹` of a bounded operator `a` by a unitary `V`. -/
local notation "conj[" V "] " a =>
  ContinuousLinearMap.comp (LinearIsometry.toContinuousLinearMap
    (LinearIsometryEquiv.toLinearIsometry V))
    (ContinuousLinearMap.comp a (LinearIsometry.toContinuousLinearMap
      (LinearIsometryEquiv.toLinearIsometry (LinearIsometryEquiv.symm V))))

namespace Physicslib4.Modular

open Physicslib4.AQFT (IsPositiveEnergy)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Commutant

set_option hygiene false in
/-- `Δ^{it}` as a bounded operator, for the binders `hM hΩ C hC` in scope. -/
local notation "U[" t "]" =>
  (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap

set_option hygiene false in
/-- The bounded operator `J T J`, for the binders `hM hΩ C hC` in scope. -/
local notation "𝒥[" T "]" => modularConjugationConj hM hΩ C hC T

set_option hygiene false in
/-- `V(t)` as a bounded operator, for the binder `V` in scope. -/
local notation "V[" t "]" => (V t).toLinearIsometry.toContinuousLinearMap

/-- The modular objects of the commutant: if `Ω` is cyclic and separating for the von Neumann
algebra `M`, then `Ω` is cyclic and separating for `M'`, `Δ_{M'}^{it} = Δ^{-it}` for every real
`t`, and `J_{M'} = J`.

Blueprint: lmm:commutant-modular-unitary-group -/
theorem commutant_modularUnitaryGroup {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    IsCyclicSeparatingVector (Set.centralizer M) Ω ∧
      (∀ t : ℝ,
        modularUnitaryGroup (isCyclicSeparatingVector_centralizer hM hΩ).1
            (isCyclicSeparatingVector_centralizer hM hΩ).2 C hC t =
          modularUnitaryGroup hM hΩ C hC (-t)) ∧
      ∀ x : H,
        modularConjugation (isCyclicSeparatingVector_centralizer hM hΩ).1
            (isCyclicSeparatingVector_centralizer hM hΩ).2 C hC x =
          modularConjugation hM hΩ C hC x := by
  open Physicslib4.Spectral.Unbounded in
  obtain ⟨hΩ', -, -, hinv, -, hJ⟩ := commutant_modular_objects hM hΩ C hC
  refine ⟨hΩ', fun t => ?_, hJ⟩
  set hc := isCyclicSeparatingVector_centralizer hM hΩ
  have hker := (modularOperator_properties hM hΩ C hC).2.2.2.1
  have hΔ' : modularOperator (Set.centralizer M) Ω C =
      functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
        fun x => ((x⁻¹ : ℝ) : ℂ) :=
    hinv.trans (inverse_eq_functionalCalculus_inv _ hker)
  obtain ⟨hfA, -, hcomp⟩ := functionalCalculus_functionalCalculus
    (modularOperator_isSelfAdjoint hM hΩ C hC) measurable_inv
  have hirr : ∀ {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (g : ℝ → ℂ),
      A = B → functionalCalculus hA g = functionalCalculus hB g := by
    intro A B hA hB g h; subst h; rfl
  obtain ⟨hm, -, hfc', -, -⟩ := modularUnitaryGroup_eq_functionalCalculus hc.1 hc.2 C hC t
  obtain ⟨-, -, hfc, -, -⟩ := modularUnitaryGroup_eq_functionalCalculus hM hΩ C hC (-t)
  have hfun : (fun x : ℝ => Complex.exp (Complex.I * (t : ℂ) * (Real.log x : ℂ))) ∘
      (fun x : ℝ => x⁻¹) =
      fun x : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (Real.log x : ℂ)) := by
    funext x; simp only [Function.comp_apply, Real.log_inv]; push_cast; ring_nf
  have h := hfc'.symm.trans ((hirr _ hfA _ hΔ').trans ((hcomp _ hm).trans (hfun ▸ hfc)))
  ext ξ
  obtain ⟨-, hx⟩ := LinearPMap.ext_iff.1 h
  simpa using @hx ξ Submodule.mem_top Submodule.mem_top

/-- Reverse endomorphisms pass to the commutant: if `X` is unitary and `X* x X ∈ M` for every
`x ∈ M`, then `X y X* ∈ M'` for every `y ∈ M'`.

The blueprint states this for a von Neumann algebra `M` with a cyclic and separating vector; the
computation uses neither hypothesis, and they are omitted, as in `commutant_reverse_endomorphism`.

Blueprint: lmm:unitary-reverse-endomorphism-commutant -/
theorem conj_mem_centralizer_of_adjoint_conj_mem {M : Set (H →L[ℂ] H)} {X : H →L[ℂ] H}
    (hX : X ∈ unitary (H →L[ℂ] H))
    (hXM : ∀ x ∈ M, ContinuousLinearMap.adjoint X ∘L x ∘L X ∈ M)
    {y : H →L[ℂ] H} (hy : y ∈ Set.centralizer M) :
    X ∘L y ∘L ContinuousLinearMap.adjoint X ∈ Set.centralizer M := by
  rw [Set.mem_centralizer_iff] at hy ⊢
  intro x hx
  have h1 : ∀ v, X (ContinuousLinearMap.adjoint X v) = v := fun v =>
    congrArg (fun T : H →L[ℂ] H => T v) (Unitary.mul_star_self_of_mem hX)
  have h2 : ∀ v, ContinuousLinearMap.adjoint X (X v) = v := fun v =>
    congrArg (fun T : H →L[ℂ] H => T v) (Unitary.star_mul_self_of_mem hX)
  ext ψ
  have key := congrArg (fun T : H →L[ℂ] H => X (T (ContinuousLinearMap.adjoint X ψ)))
    (hy _ (hXM x hx))
  simpa [h1, h2] using key

/-- Borchers' theorem for negative half-lines: let `V` be a family of unitaries with positive
energy such that `V(t)Ω = Ω` for all `t` and `V(-t) x V(t) ∈ M` for all `t ≥ 0` and `x ∈ M`.
Then `Δ^{is} V(t) Δ^{-is} = V(e^{2πs} t)` and `J V(t) J = V(-t)` for all real `s`, `t`.

The hypotheses make `V` a half-sided translation for `(M', Ω)`, not for `(M, Ω)`.

Blueprint: crllr:borchers-reversed -/
theorem borchers_reversed {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V)
    (hB1 : ∀ t : ℝ, V t Ω = Ω)
    (hB2 : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ M, V[-t] ∘L x ∘L V[t] ∈ M) :
    (∀ s t : ℝ, U[s] ∘L V[t] ∘L U[-s] = V[Real.exp (2 * Real.pi * s) * t]) ∧
      ∀ t : ℝ, 𝒥[V[t]] = V[-t] := by
  have hc := isCyclicSeparatingVector_centralizer hM hΩ
  obtain ⟨-, hU, hJ⟩ := commutant_modularUnitaryGroup hM hΩ C hC
  have hV2 : ∀ a b : ℝ, a + b = 0 → ∀ ψ, V a (V b ψ) = ψ := fun a b hab ψ => by
    rw [← hV.isOneParameterUnitaryGroup.map_add, hab, hV.isOneParameterUnitaryGroup.map_zero]
  have hHST : IsHalfSidedTranslation (Set.centralizer M) Ω V := by
    refine ⟨hV, hB1, fun t ht y hy => ?_⟩
    rw [Set.mem_centralizer_iff] at hy ⊢
    intro x hx
    ext ψ
    have key := congrArg (fun T : H →L[ℂ] H => V t (T (V (-t) ψ))) (hy _ (hB2 t ht x hx))
    simpa [hV2 t (-t) (by ring), hV2 (-t) t (by ring)] using key
  obtain ⟨hD, hR⟩ := borchers hc.1 hc.2 C hC hHST
  refine ⟨fun s t => ?_, fun t => ?_⟩
  · have h := hD (-s) t
    simpa only [hU, neg_neg, mul_neg] using h
  · rw [← hR t]
    ext ψ
    simp [modularConjugationConj, hJ]

end Commutant

end Physicslib4.Modular

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open scoped Pointwise
open Physicslib4.Modular
open Physicslib4.Spectral.Stone (IsOneParameterUnitaryGroup IsStronglyContinuous)

/-- The lightlike vector `l₊ = (1, 1, 0, 0)`. -/
local notation "l₊" => (!₂[1, 1, 0, 0] : SpacetimeModel)

/-- The lightlike vector `l₋ = (1, -1, 0, 0)`. -/
local notation "l₋" => (!₂[1, -1, 0, 0] : SpacetimeModel)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Poincaré conjugation of a translation: for `g = (L, c)` in the inhomogeneous Lorentz group and
`a ∈ ℝ⁴`, `g translationSub(a) g⁻¹ = translationSub(L a)`; in particular
`b(s) translationSub(a) b(s)⁻¹ = translationSub(Λ(s) a)`.

Blueprint: lmm:poincare-conjugates-translation -/
theorem conj_translationSub :
    (∀ (g : InhomogeneousLorentzGroup) (a : SpacetimeModel),
      g * translationSub a * g⁻¹ = translationSub (g.linear a)) ∧
      ∀ (s : ℝ) (a : SpacetimeModel),
        wedgeBoost s * translationSub a * (wedgeBoost s)⁻¹ = translationSub (boostMatrix s a) := by
  have h : ∀ (g : InhomogeneousLorentzGroup) (a : SpacetimeModel),
      g * translationSub a * g⁻¹ = translationSub (g.linear a) := fun g a => by
    refine InhomogeneousLorentzGroup.ext ?_ ?_
    · ext x
      change g.linear (g.linear.symm x) = x
      simp
    · change g.translation + g.linear a + g.linear (-g.linear.symm g.translation) = g.linear a
      rw [map_neg, LinearEquiv.apply_symm_apply]
      abel
  exact ⟨h, fun s a => h (wedgeBoost s) a⟩

/-- The wedge reflection `j(x⁰, x¹, x², x³) = (-x⁰, -x¹, x², x³)`, the reflection of the
`(x⁰, x¹)`-plane. It preserves the Minkowski form and has determinant `1`, but it is not
orthochronous, so `(j, 0)` is not an element of the inhomogeneous Lorentz group; `j` acts only on
translation vectors.

Blueprint: def:wedge-reflection -/
noncomputable def wedgeReflection : SpacetimeModel →ₗ[ℝ] SpacetimeModel where
  toFun x := !₂[-x 0, -x 1, x 2, x 3]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

/-- Light-cone decomposition of a vector: with `α = (a⁰ + a¹)/2`, `β = (a⁰ - a¹)/2` and
`a_⊥ = (0, 0, a², a³)`, `a = α l₊ + β l₋ + a_⊥`, `Λ(s) a = eˢ α l₊ + e⁻ˢ β l₋ + a_⊥` and
`j a = -α l₊ - β l₋ + a_⊥`.

Blueprint: lmm:light-cone-decomposition -/
theorem lightCone_decomposition (a : SpacetimeModel) (s : ℝ) :
    a = ((a 0 + a 1) / 2) • l₊ + ((a 0 - a 1) / 2) • l₋ + !₂[0, 0, a 2, a 3] ∧
      boostMatrix s a = (Real.exp s * ((a 0 + a 1) / 2)) • l₊ +
        (Real.exp (-s) * ((a 0 - a 1) / 2)) • l₋ + !₂[0, 0, a 2, a 3] ∧
      wedgeReflection a =
        (-((a 0 + a 1) / 2)) • l₊ + (-((a 0 - a 1) / 2)) • l₋ + !₂[0, 0, a 2, a 3] := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [boostMatrix_apply, wedgeReflection, Real.cosh_eq, Real.sinh_eq] <;> ring

namespace HaagKastlerNet

variable {N : HaagKastlerNet} {π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
  {U : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H)}

/-- The translation unitaries of a covariant vacuum representation: `U(g)⁻¹ = U(g⁻¹)`;
`U(0) = 1`, `U(a + a') = U(a)U(a')` and `U(a)⁻¹ = U(-a)`; `U(translationFlow n t) = U(t n)`; and
`U(g) U(a) U(g)⁻¹ = U(L a)` for `g = (L, c)`, in particular
`U(b(s)) U(a) U(b(s))⁻¹ = U(Λ(s) a)`.

Blueprint: lmm:translation-unitaries -/
theorem IsCovariantVacuumRep.translation_unitaries (h : N.IsCovariantVacuumRep π Ω U) :
    (∀ g : InhomogeneousLorentzGroup, (U g).symm = U g⁻¹) ∧
      U (translationSub 0) = LinearIsometryEquiv.refl ℂ H ∧
      (∀ a a' : SpacetimeModel,
        U (translationSub (a + a')) = (U (translationSub a')).trans (U (translationSub a))) ∧
      (∀ a : SpacetimeModel, (U (translationSub a)).symm = U (translationSub (-a))) ∧
      (∀ (n : SpacetimeModel) (t : ℝ), U (translationFlow n t) = U (translationSub (t • n))) ∧
      (∀ (g : InhomogeneousLorentzGroup) (a : SpacetimeModel) (ψ : H),
        U g (U (translationSub a) ((U g).symm ψ)) = U (translationSub (g.linear a)) ψ) ∧
      ∀ (s : ℝ) (a : SpacetimeModel) (ψ : H),
        U (wedgeBoost s) (U (translationSub a) ((U (wedgeBoost s)).symm ψ)) =
          U (translationSub (boostMatrix s a)) ψ := by
  have hinv : ∀ g : InhomogeneousLorentzGroup, (U g).symm = U g⁻¹ := fun g => by
    ext ψ
    conv_rhs => rw [← (U g).apply_symm_apply ψ]
    rw [← LinearIsometryEquiv.trans_apply, ← h.map_mul, inv_mul_cancel, h.map_one]
    rfl
  have hconj : ∀ (g : InhomogeneousLorentzGroup) (a : SpacetimeModel) (ψ : H),
      U g (U (translationSub a) ((U g).symm ψ)) = U (translationSub (g.linear a)) ψ :=
    fun g a ψ => by
      rw [← conj_translationSub.1 g a, hinv, h.map_mul, h.map_mul]
      rfl
  refine ⟨hinv, by rw [translationSub_zero, h.map_one], fun a a' =>
    (congrArg U (translationSub_mul a a')).trans (h.map_mul _ _), fun a => by
    rw [hinv]
    rfl,
    fun n t => rfl, hconj, fun s a ψ => hconj (wedgeBoost s) a ψ⟩

/-- Light-cone factorisation of the translation unitaries: with `α = (a⁰ + a¹)/2`,
`β = (a⁰ - a¹)/2` and `a_⊥ = (0, 0, a², a³)`, `U(a) = U(α l₊) U(β l₋) U(a_⊥)`.

Blueprint: lmm:translation-light-cone-factorisation -/
theorem IsCovariantVacuumRep.translation_lightCone_factorisation
    (h : N.IsCovariantVacuumRep π Ω U) (a : SpacetimeModel) (ψ : H) :
    U (translationSub a) ψ =
      U (translationSub (((a 0 + a 1) / 2) • l₊))
        (U (translationSub (((a 0 - a 1) / 2) • l₋))
          (U (translationSub !₂[0, 0, a 2, a 3]) ψ)) := by
  obtain ⟨-, -, hadd, -⟩ := h.translation_unitaries
  conv_lhs => rw [(lightCone_decomposition a 0).1]
  rw [hadd, LinearIsometryEquiv.trans_apply, hadd, LinearIsometryEquiv.trans_apply]

/-- The lightlike translations `t ↦ U(t l₊)` and `t ↦ U(t l₋)` have positive energy, and
`U(t l₊)Ω = U(t l₋)Ω = Ω` for every `t`.

Blueprint: lmm:lightlike-translations-positive-energy -/
theorem IsCovariantVacuumRep.lightlike_translations_positiveEnergy
    (h : N.IsCovariantVacuumRep π Ω U) :
    IsPositiveEnergy (fun t : ℝ => U (translationSub (t • l₊))) ∧
      IsPositiveEnergy (fun t : ℝ => U (translationSub (t • l₋))) ∧
      ∀ t : ℝ, U (translationSub (t • l₊)) Ω = Ω ∧ U (translationSub (t • l₋)) Ω = Ω := by
  have hne : ∀ c : ℝ, (!₂[1, c, 0, 0] : SpacetimeModel) ≠ 0 := fun c h0 => by
    simpa using congrArg (· 0) h0
  refine ⟨h.positiveEnergy _ (by simp) (by simp) (hne 1),
    h.positiveEnergy _ (by simp) (by simp) (hne (-1)),
    fun t => ⟨h.invariant _, h.invariant _⟩⟩

set_option hygiene false in
/-- `U(a)` as a bounded operator, for the binder `U` in scope. -/
local notation "Tr[" a "]" =>
  (U (translationSub a)).toLinearIsometry.toContinuousLinearMap

/-- Half-sided translations of the right wedge algebra: for `t ≥ 0` and `x ∈ R(W_R)`,
`U(t l₊) x U(-t l₊) ∈ R(W_R)` and `U(-t l₋) x U(t l₋) ∈ R(W_R)`. In particular
`t ↦ U(t l₊)` is a half-sided translation for `(R(W_R), Ω)`.

Blueprint: lmm:wedge-half-sided-translations -/
theorem IsCovariantVacuumRep.wedge_halfSidedTranslations (h : N.IsCovariantVacuumRep π Ω U) :
    (∀ t : ℝ, 0 ≤ t → ∀ x ∈ N.regionVonNeumann π rightWedge,
      Tr[t • l₊] ∘L x ∘L Tr[-(t • l₊)] ∈ N.regionVonNeumann π rightWedge ∧
        Tr[-(t • l₋)] ∘L x ∘L Tr[t • l₋] ∈ N.regionVonNeumann π rightWedge) ∧
      IsHalfSidedTranslation (N.regionVonNeumann π rightWedge) Ω
        (fun t : ℝ => U (translationSub (t • l₊))) := by
  have key : ∀ a : SpacetimeModel, translationSub a • rightWedge ⊆ rightWedge →
      ∀ x ∈ N.regionVonNeumann π rightWedge,
        Tr[a] ∘L x ∘L Tr[-a] ∈ N.regionVonNeumann π rightWedge := by
    intro a ha x hx
    have hmem : (conj[U (translationSub a)] x) ∈ N.regionVonNeumann π rightWedge :=
      (N.regionVonNeumann_mono π ha).2
        (h.conj_image_regionVonNeumann (translationSub a) rightWedge ▸ ⟨x, hx, rfl⟩)
    rwa [h.translation_unitaries.2.2.2.1 a] at hmem
  have hW := translationSub_smul_rightWedge_subset.2
  have hfirst : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ N.regionVonNeumann π rightWedge,
      Tr[t • l₊] ∘L x ∘L Tr[-(t • l₊)] ∈ N.regionVonNeumann π rightWedge :=
    fun t ht => key _ (hW t ht).1
  refine ⟨fun t ht x hx => ⟨hfirst t ht x hx, ?_⟩, ?_⟩
  · simpa using key _ (hW t ht).2 x hx
  · obtain ⟨hpos, -, hinv⟩ := h.lightlike_translations_positiveEnergy
    exact ⟨hpos, fun t => (hinv t).1, fun t ht x hx => by
      simpa only [neg_smul] using hfirst t ht x hx⟩

set_option hygiene false in
/-- `Δ_{W_R}^{is}` as a bounded operator, for the binders `N π hΩ C hC` in scope. -/
local notation "Δ[" s "]" =>
  (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC
    s).toLinearIsometry.toContinuousLinearMap

set_option hygiene false in
/-- The bounded operator `J_{W_R} T J_{W_R}`, for the binders `N π hΩ C hC` in scope. -/
local notation "𝒥R[" T "]" =>
  modularConjugationConj (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC T

/-- The wedge modular objects on the `l₊` translations: for all real `s`, `t`,
`Δ^{is} U(t l₊) Δ^{-is} = U(e^{-2πs} t l₊)` and `J U(t l₊) J = U(-t l₊)`, with `Δ^{is}` and `J`
the modular objects of `(R(W_R), Ω)`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`, which `IsCovariantVacuumRep.wedge_isCyclicSeparatingVector` supplies.

Blueprint: lmm:wedge-modular-plus -/
theorem IsCovariantVacuumRep.wedge_modular_plus (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) :
    (∀ s t : ℝ, Δ[s] ∘L Tr[t • l₊] ∘L Δ[-s] = Tr[(Real.exp (-(2 * Real.pi * s)) * t) • l₊]) ∧
      ∀ t : ℝ, 𝒥R[Tr[t • l₊]] = Tr[-(t • l₊)] := by
  obtain ⟨h1, h2⟩ := Physicslib4.Modular.borchers (N.regionVonNeumann_isVonNeumannSet π
    rightWedge).2 hΩ C hC h.wedge_halfSidedTranslations.2
  exact ⟨h1, fun t => by simpa only [neg_smul] using h2 t⟩

/-- The wedge modular objects on the `l₋` translations: for all real `s`, `t`,
`Δ^{is} U(t l₋) Δ^{-is} = U(e^{2πs} t l₋)` and `J U(t l₋) J = U(-t l₋)`, with `Δ^{is}` and `J`
the modular objects of `(R(W_R), Ω)`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`, which `IsCovariantVacuumRep.wedge_isCyclicSeparatingVector` supplies.

Blueprint: lmm:wedge-modular-minus -/
theorem IsCovariantVacuumRep.wedge_modular_minus (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) :
    (∀ s t : ℝ, Δ[s] ∘L Tr[t • l₋] ∘L Δ[-s] = Tr[(Real.exp (2 * Real.pi * s) * t) • l₋]) ∧
      ∀ t : ℝ, 𝒥R[Tr[t • l₋]] = Tr[-(t • l₋)] := by
  obtain ⟨-, hpos, hinv⟩ := h.lightlike_translations_positiveEnergy
  obtain ⟨hD, hJ⟩ := borchers_reversed (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC
    hpos (fun t => (hinv t).2) fun t ht x hx => by
      simpa only [neg_smul] using (h.wedge_halfSidedTranslations.1 t ht x hx).2
  exact ⟨hD, fun t => by simpa only [neg_smul] using hJ t⟩

/-- The wedge modular group on the translations: for every `a ∈ ℝ⁴` and real `s`,
`Δ^{is} U(a) Δ^{-is} = U(Λ(-2πs) a)`, with `Δ^{is}` the modular unitary group of `(R(W_R), Ω)`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`, which `IsCovariantVacuumRep.wedge_isCyclicSeparatingVector` supplies.

Blueprint: lmm:wedge-modular-group-translations -/
theorem IsCovariantVacuumRep.wedge_modularUnitaryGroup_translations
    (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (a : SpacetimeModel) (s : ℝ) :
    Δ[s] ∘L Tr[a] ∘L Δ[-s] = Tr[boostMatrix (-(2 * Real.pi * s)) a] := by
  set Δ := modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC
  have hgrp := (modularUnitaryGroup_properties
    (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC).1
  have hcancel : ∀ φ : H, Δ (-s) (Δ s φ) = φ := fun φ => by
    rw [← hgrp.map_add, neg_add_cancel, hgrp.map_zero]
  have hplus : ∀ (t : ℝ) (φ : H), Δ s (U (translationSub (t • l₊)) (Δ (-s) φ)) =
      U (translationSub ((Real.exp (-(2 * Real.pi * s)) * t) • l₊)) φ := fun t φ =>
    congrArg (fun T : H →L[ℂ] H => T φ) ((h.wedge_modular_plus hΩ C hC).1 s t)
  have hminus : ∀ (t : ℝ) (φ : H), Δ s (U (translationSub (t • l₋)) (Δ (-s) φ)) =
      U (translationSub ((Real.exp (2 * Real.pi * s) * t) • l₋)) φ := fun t φ =>
    congrArg (fun T : H →L[ℂ] H => T φ) ((h.wedge_modular_minus hΩ C hC).1 s t)
  have hperp : ∀ φ : H, U (translationSub !₂[0, 0, a 2, a 3]) (Δ (-s) φ) =
      Δ (-s) (U (translationSub !₂[0, 0, a 2, a 3]) φ) :=
    (h.wedge_stabiliser_commute hΩ C hC).1 _
      (translationSub_smul_rightWedge_of_transverse (by simp) (by simp)) |>.1 (-s)
  obtain ⟨-, -, hadd, -⟩ := h.translation_unitaries
  ext ψ
  change Δ s (U (translationSub a) (Δ (-s) ψ)) = U (translationSub _) ψ
  rw [h.translation_lightCone_factorisation a, hperp,
    ← hcancel (U (translationSub (((a 0 - a 1) / 2) • l₋)) _), hminus, hplus,
    (lightCone_decomposition a _).2.1, hadd, LinearIsometryEquiv.trans_apply, hadd,
    LinearIsometryEquiv.trans_apply, neg_neg]

/-- A unitary `X` with `X R(B) X⁻¹ = R(B)` for every diamond `B` preserves every region:
`X S(O) X⁻¹ = S(O)` and `X R(O) X⁻¹ = R(O)` for every `O ⊆ ℝ⁴`. The condition `XΩ = Ω` is not
needed.

Blueprint: lmm:internal-symmetry-normalizes-regions -/
theorem conj_image_region_of_conj_image_localVonNeumann
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (X : H ≃ₗᵢ[ℂ] H)
    (hX : ∀ (B : Set StandardMinkowskiSpacetime.Carrier) (hB : IsAlexandrovBasisSet B),
      (fun a => conj[X] a) '' N.localVonNeumann π hB = N.localVonNeumann π hB)
    (O : Set StandardMinkowskiSpacetime.Carrier) :
    (fun a => conj[X] a) '' N.regionGeneratingSet π O = N.regionGeneratingSet π O ∧
      (fun a => conj[X] a) '' N.regionVonNeumann π O = N.regionVonNeumann π O := by
  have hS : (fun a => conj[X] a) '' N.regionGeneratingSet π O = N.regionGeneratingSet π O := by
    simp only [regionGeneratingSet, Set.image_iUnion, hX]
  have hfun : (fun a => conj[X] a) = Physicslib4.lieConj X := by
    funext a; ext x; simp
  refine ⟨hS, ?_⟩
  rw [regionVonNeumann, hfun, (Physicslib4.lieConj X).image_centralizer_centralizer, ← hfun, hS]

/-! ### All translations -/

/-- The wedge modular conjugation on the translations: for every `a ∈ ℝ⁴`, `J U(a) J = U(j a)`,
with `J` the modular conjugation of `(R(W_R), Ω)` and `j` the wedge reflection.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`, which `IsCovariantVacuumRep.wedge_isCyclicSeparatingVector` supplies.

Blueprint: lmm:wedge-modular-conjugation-translations -/
theorem IsCovariantVacuumRep.wedge_modularConjugation_translations
    (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (a : SpacetimeModel) :
    𝒥R[Tr[a]] = Tr[wedgeReflection a] := by
  set J := modularConjugation (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC
  have hJJ : ∀ ψ, J (J ψ) = ψ :=
    (modularConjugation_involution (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC).1
  have hp : ∀ (t : ℝ) ψ, U (translationSub (t • l₊)) (J ψ) = J (U (translationSub (-(t • l₊))) ψ) :=
    fun t ψ => by
      have := congrArg (fun T : H →L[ℂ] H => J (T ψ)) ((h.wedge_modular_plus hΩ C hC).2 t)
      simpa [modularConjugationConj, hJJ, J] using this
  have hm : ∀ (t : ℝ) ψ, U (translationSub (t • l₋)) (J ψ) = J (U (translationSub (-(t • l₋))) ψ) :=
    fun t ψ => by
      have := congrArg (fun T : H →L[ℂ] H => J (T ψ)) ((h.wedge_modular_minus hΩ C hC).2 t)
      simpa [modularConjugationConj, hJJ, J] using this
  have ht := ((h.wedge_stabiliser_commute hΩ C hC).2.2 rfl).2 !₂[0, 0, a 2, a 3] (by simp)
    (by simp)
  obtain ⟨-, -, hadd, -⟩ := h.translation_unitaries
  ext ψ
  change J (U (translationSub a) (J ψ)) = U (translationSub (wedgeReflection a)) ψ
  rw [h.translation_lightCone_factorisation a, ht.2, hm, hp, hJJ,
    (lightCone_decomposition a 0).2.2, hadd, LinearIsometryEquiv.trans_apply, hadd,
    LinearIsometryEquiv.trans_apply, neg_smul, neg_smul]

/-- The wedge modular objects act geometrically on the translations: with `Δ^{is}` and `J` the
modular objects of `(R(W_R), Ω)`, for every `a ∈ ℝ⁴` and real `s`,
`Δ^{is} U(a) Δ^{-is} = U(Λ(-2πs) a) = U(b(-2πs)) U(a) U(b(-2πs))⁻¹` and `J U(a) J = U(j a)`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`, which `IsCovariantVacuumRep.wedge_isCyclicSeparatingVector` supplies.

Blueprint: thrm:wedge-modular-translations -/
theorem IsCovariantVacuumRep.wedge_modular_translations (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (a : SpacetimeModel) (s : ℝ) :
    Δ[s] ∘L Tr[a] ∘L Δ[-s] = Tr[boostMatrix (-(2 * Real.pi * s)) a] ∧
      Tr[boostMatrix (-(2 * Real.pi * s)) a] =
        (conj[U (wedgeBoost (-(2 * Real.pi * s)))] Tr[a]) ∧
      𝒥R[Tr[a]] = Tr[wedgeReflection a] := by
  refine ⟨h.wedge_modularUnitaryGroup_translations hΩ C hC a s, ?_,
    h.wedge_modularConjugation_translations hΩ C hC a⟩
  ext ψ
  exact (h.translation_unitaries.2.2.2.2.2.2 _ a ψ).symm

set_option hygiene false in
/-- `Δ_{gW_R}^{is}` as a bounded operator, for the binders `N π g hΩg C hC` in scope. -/
local notation "Δg[" s "]" =>
  (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π (g • rightWedge)).2 hΩg C hC
    s).toLinearIsometry.toContinuousLinearMap

set_option hygiene false in
/-- The bounded operator `J_{gW_R} T J_{gW_R}`, for the binders `N π g hΩg C hC` in scope. -/
local notation "𝒥g[" T "]" =>
  modularConjugationConj (N.regionVonNeumann_isVonNeumannSet π (g • rightWedge)).2 hΩg C hC T

/-- The modular objects of every wedge on the translations: for `g = (L, c)` in the inhomogeneous
Lorentz group, with `Δ_{gW_R}^{is}` and `J_{gW_R}` the modular objects of `(R(gW_R), Ω)`, for
every `a ∈ ℝ⁴` and real `s`,
`Δ_{gW_R}^{is} U(a) Δ_{gW_R}^{-is} = U(L Λ(-2πs) L⁻¹ a) = U(b_g(-2πs)) U(a) U(b_g(-2πs))⁻¹` and
`J_{gW_R} U(a) J_{gW_R} = U(L j L⁻¹ a)`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness of `(R(W_R), Ω)` and `(R(gW_R), Ω)`, the proofs `hΩ` and `hΩg`, which
`IsCovariantVacuumRep.wedge_isCyclicSeparatingVector` supplies. `hΩ` does not appear in the
conclusion; the proof transports the right-wedge result along `U(g)`.

Blueprint: crllr:wedge-modular-translations-general -/
theorem IsCovariantVacuumRep.wedge_modular_translations_general
    (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (g : InhomogeneousLorentzGroup)
    (hΩg : IsCyclicSeparatingVector (N.regionVonNeumann π (g • rightWedge)) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (a : SpacetimeModel) (s : ℝ) :
    Δg[s] ∘L Tr[a] ∘L Δg[-s] =
        Tr[g.linear (boostMatrix (-(2 * Real.pi * s)) (g.linear.symm a))] ∧
      Tr[g.linear (boostMatrix (-(2 * Real.pi * s)) (g.linear.symm a))] =
        (conj[U (wedgeBoostAlong g (-(2 * Real.pi * s)))] Tr[a]) ∧
      𝒥g[Tr[a]] = Tr[g.linear (wedgeReflection (g.linear.symm a))] := by
  obtain ⟨hinv, -, -, -, -, hconj, -⟩ := h.translation_unitaries
  obtain ⟨-, -, -, hU, hJ⟩ := h.wedge_modular_covariance (W := rightWedge)
    ⟨1, (one_smul _ _).symm⟩ g hΩ hΩg C C hC hC
  have hback : ∀ (b : SpacetimeModel) (χ : H),
      (U g).symm (U (translationSub b) (U g χ)) = U (translationSub (g.linear.symm b)) χ :=
    fun b χ => by
      have := hconj g⁻¹ b χ
      rwa [hinv g⁻¹, inv_inv, ← hinv g] at this
  obtain ⟨hΔ, -, hJR⟩ := h.wedge_modular_translations hΩ C hC (g.linear.symm a) s
  have hΔp : ∀ χ : H,
      modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC s
        (U (translationSub (g.linear.symm a))
          (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC (-s)
            χ)) =
        U (translationSub (boostMatrix (-(2 * Real.pi * s)) (g.linear.symm a))) χ :=
    fun χ => DFunLike.congr_fun hΔ χ
  have hJp : ∀ χ : H,
      modularConjugation (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC
        (U (translationSub (g.linear.symm a))
          (modularConjugation (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC χ)) =
        U (translationSub (wedgeReflection (g.linear.symm a))) χ :=
    fun χ => DFunLike.congr_fun hJR χ
  refine ⟨?_, ?_, ?_⟩
  · ext ψ
    change
      modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π (g • rightWedge)).2 hΩg C hC s
        (U (translationSub a)
          (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π (g • rightWedge)).2 hΩg C hC
            (-s) ψ)) =
      U (translationSub (g.linear (boostMatrix (-(2 * Real.pi * s)) (g.linear.symm a)))) ψ
    rw [← hU s, ← hU (-s), hback, hΔp, hconj]
  · ext ψ
    exact (hconj (wedgeBoostAlong g (-(2 * Real.pi * s))) a ψ).symm
  · ext ψ
    change modularConjugation (N.regionVonNeumann_isVonNeumannSet π (g • rightWedge)).2 hΩg C hC
        (U (translationSub a)
          (modularConjugation (N.regionVonNeumann_isVonNeumannSet π (g • rightWedge)).2 hΩg C hC
            ψ)) =
      U (translationSub (g.linear (wedgeReflection (g.linear.symm a)))) ψ
    rw [← hJ, ← hJ, hback, hJp, hconj]

/-! ### The defect `Z(t)` -/

/-- The wedge modular defect `Z(t) = Δ^{it} U(b(2πt))`, with `Δ^{it}` the modular unitary group of
`(R(W_R), Ω)` formed with the reference conjugation `C` and `b` the boost of the right wedge. It
measures how far `Δ^{it}` is from the boost `U(b(-2πt))`; the Bisognano–Wichmann identification
`Δ^{it} = U(b(-2πt))` is the statement `Z ≡ 1`.

The standardness of `(R(W_R), Ω)` enters as the proof `hΩ` that names the modular group; for a
weakly additive covariant vacuum representation it is supplied by
`IsCovariantVacuumRep.wedge_isCyclicSeparatingVector`.

Blueprint: def:wedge-modular-defect -/
noncomputable def wedgeModularDefect (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) {Ω : H}
    (U : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H))
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  (U (wedgeBoost (2 * Real.pi * t))).trans
    (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC t)

set_option hygiene false in
/-- The wedge modular defect `Z(t)`, for the binders `N π U hΩ C hC` in scope. -/
local notation "Z[" t "]" => wedgeModularDefect N π U hΩ C hC t

/-- The defect fixes the vacuum and preserves the wedge algebra: `Z(t)Ω = Ω` and
`Z(t) R(W_R) Z(t)⁻¹ = R(W_R)` for every `t`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`.

Blueprint: lmm:wedge-modular-defect-vacuum -/
theorem IsCovariantVacuumRep.wedgeModularDefect_vacuum (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (t : ℝ) :
    Z[t] Ω = Ω ∧
      (fun a => conj[Z[t]] a) '' N.regionVonNeumann π rightWedge =
        N.regionVonNeumann π rightWedge := by
  have hM := (N.regionVonNeumann_isVonNeumannSet π rightWedge).2
  refine ⟨?_, ?_⟩
  · rw [wedgeModularDefect, LinearIsometryEquiv.trans_apply, h.invariant,
      modularUnitaryGroup_apply_self]
  · have hfun : (fun a : H →L[ℂ] H => conj[Z[t]] a) =
        (fun x : H →L[ℂ] H => Δ[t] ∘L x ∘L Δ[-t]) ∘
          (fun a : H →L[ℂ] H => conj[U (wedgeBoost (2 * Real.pi * t))] a) := by
      funext a; ext ψ
      simp [wedgeModularDefect, ((modularUnitaryGroup_properties hM hΩ C hC).2.2 t).2]
    rw [hfun, Set.image_comp, h.conj_image_regionVonNeumann, (wedgeBoost_smul_wedge _).1,
      modularUnitaryGroup_conj_image]

/-- The defect commutes with the translations: `Z(t) U(a) = U(a) Z(t)` for every `t` and
`a ∈ ℝ⁴`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`.

Blueprint: lmm:wedge-modular-defect-translations -/
theorem IsCovariantVacuumRep.wedgeModularDefect_translations (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (t : ℝ) (a : SpacetimeModel) (ψ : H) :
    Z[t] (U (translationSub a) ψ) = U (translationSub a) (Z[t] ψ) := by
  set Δ := modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC
  have hgrp := (modularUnitaryGroup_properties
    (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC).1
  have hcancel : ∀ φ : H, Δ (-t) (Δ t φ) = φ := fun φ => by
    rw [← hgrp.map_add, neg_add_cancel, hgrp.map_zero]
  have hΔ : ∀ φ : H, Δ t (U (translationSub (boostMatrix (2 * Real.pi * t) a)) (Δ (-t) φ)) =
      U (translationSub a) φ := fun φ => by
    refine (DFunLike.congr_fun (h.wedge_modularUnitaryGroup_translations hΩ C hC
      (boostMatrix (2 * Real.pi * t) a) t) φ).trans ?_
    change U (translationSub (boostMatrix _ _)) φ = _
    rw [← boostMatrix_groupLaw.2.2, LinearEquiv.symm_apply_apply]
  have hb : U (wedgeBoost (2 * Real.pi * t)) (U (translationSub a) ψ) =
      U (translationSub (boostMatrix (2 * Real.pi * t) a))
        (U (wedgeBoost (2 * Real.pi * t)) ψ) := by
    simpa using h.translation_unitaries.2.2.2.2.2.2 (2 * Real.pi * t) a
      (U (wedgeBoost (2 * Real.pi * t)) ψ)
  rw [wedgeModularDefect, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, hb,
    ← hΔ, hcancel]

/-- The defect commutes with the boosts: `Z(t) U(b(s)) = U(b(s)) Z(t)` for all real `s`, `t`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`.

Blueprint: lmm:wedge-modular-defect-boosts -/
theorem IsCovariantVacuumRep.wedgeModularDefect_boosts (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (t s : ℝ) (ψ : H) :
    Z[t] (U (wedgeBoost s) ψ) = U (wedgeBoost s) (Z[t] ψ) := by
  have hcomm : ∀ φ : H, U (wedgeBoost (2 * Real.pi * t)) (U (wedgeBoost s) φ) =
      U (wedgeBoost s) (U (wedgeBoost (2 * Real.pi * t)) φ) := fun φ => by
    rw [← LinearIsometryEquiv.trans_apply, ← LinearIsometryEquiv.trans_apply, ← h.map_mul,
      ← h.map_mul, ← wedgeBoost_groupLaw.2, ← wedgeBoost_groupLaw.2, add_comm]
  rw [wedgeModularDefect, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
    (h.wedge_stabiliser_commute hΩ C hC).1 _ (wedgeBoost_smul_wedge s).1 |>.1 t, hcomm]

/-- The defect is a one-parameter group: `Z(0) = 1` and `Z(s + t) = Z(s) Z(t)` for all real
`s`, `t`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`.

Blueprint: lmm:wedge-modular-defect-group -/
theorem IsCovariantVacuumRep.wedgeModularDefect_group (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) :
    Z[0] = LinearIsometryEquiv.refl ℂ H ∧ ∀ s t : ℝ, Z[s + t] = Z[t].trans Z[s] := by
  have hgrp := (modularUnitaryGroup_properties
    (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC).1
  refine ⟨LinearIsometryEquiv.ext fun ψ => ?_, fun s t => LinearIsometryEquiv.ext fun ψ => ?_⟩
  · rw [wedgeModularDefect, LinearIsometryEquiv.trans_apply, mul_zero, wedgeBoost_groupLaw.1,
      h.map_one, hgrp.map_zero]
  · have hb : U (wedgeBoost (2 * Real.pi * (s + t))) ψ =
        U (wedgeBoost (2 * Real.pi * s)) (U (wedgeBoost (2 * Real.pi * t)) ψ) := by
      rw [← LinearIsometryEquiv.trans_apply, ← h.map_mul, mul_add, wedgeBoost_groupLaw.2]
    rw [wedgeModularDefect, LinearIsometryEquiv.trans_apply, hb, hgrp.map_add,
      ← (h.wedge_stabiliser_commute hΩ C hC).1 _ (wedgeBoost_smul_wedge _).1 |>.1 t]
    rfl

/-- The defect is strongly continuous: `t ↦ Z(t)ψ` is continuous for every `ψ`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`.

Blueprint: lmm:wedge-modular-defect-continuous -/
theorem IsCovariantVacuumRep.wedgeModularDefect_continuous (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (ψ : H) :
    Continuous fun t : ℝ => Z[t] ψ := by
  set V := modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC
  have hV := (modularUnitaryGroup_properties (N.regionVonNeumann_isVonNeumannSet π rightWedge).2
    hΩ C hC).2.1
  have hg : Continuous fun t : ℝ => U (wedgeBoost (2 * Real.pi * t)) ψ :=
    (h.continuous_apply _ isContinuousOneParameterSubgroup_wedgeBoost ψ).comp
      (by fun_prop : Continuous fun t : ℝ => 2 * Real.pi * t)
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun t => ?_)
    (g := fun t => dist (U (wedgeBoost (2 * Real.pi * t)) ψ)
        (U (wedgeBoost (2 * Real.pi * t₀)) ψ) +
      dist (V t (U (wedgeBoost (2 * Real.pi * t₀)) ψ))
        (V t₀ (U (wedgeBoost (2 * Real.pi * t₀)) ψ))) ?_)
  · simp only [wedgeModularDefect, LinearIsometryEquiv.trans_apply]
    refine (dist_triangle _ (V t (U (wedgeBoost (2 * Real.pi * t₀)) ψ)) _).trans_eq ?_
    rw [LinearIsometryEquiv.dist_map]
  · have h1 := tendsto_iff_dist_tendsto_zero.1 (hg.tendsto t₀)
    have h2 := tendsto_iff_dist_tendsto_zero.1
      ((hV (U (wedgeBoost (2 * Real.pi * t₀)) ψ)).tendsto t₀)
    simpa using h1.add h2

/-- The wedge modular group up to a defect: `Z(t) = Δ^{it} U(b(2πt))` is a strongly continuous
one-parameter unitary group with `Δ^{it} = Z(t) U(b(-2πt))`, and for all real `t`, `s` and
`a ∈ ℝ⁴`, `Z(t)Ω = Ω`, `Z(t) R(W_R) Z(t)⁻¹ = R(W_R)`, `Z(t) U(a) = U(a) Z(t)` and
`Z(t) U(b(s)) = U(b(s)) Z(t)`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`.

Blueprint: crllr:wedge-modular-defect -/
theorem IsCovariantVacuumRep.wedgeModularDefect_properties (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) :
    IsOneParameterUnitaryGroup (N.wedgeModularDefect π U hΩ C hC) ∧
      IsStronglyContinuous (N.wedgeModularDefect π U hΩ C hC) ∧
      (∀ (t : ℝ) (ψ : H),
        modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC t ψ =
          Z[t] (U (wedgeBoost (-(2 * Real.pi * t))) ψ)) ∧
      ∀ t : ℝ, Z[t] Ω = Ω ∧
        (fun a => conj[Z[t]] a) '' N.regionVonNeumann π rightWedge =
          N.regionVonNeumann π rightWedge ∧
        (∀ (a : SpacetimeModel) (ψ : H),
          Z[t] (U (translationSub a) ψ) = U (translationSub a) (Z[t] ψ)) ∧
        ∀ (s : ℝ) (ψ : H), Z[t] (U (wedgeBoost s) ψ) = U (wedgeBoost s) (Z[t] ψ) := by
  obtain ⟨h0, hadd⟩ := h.wedgeModularDefect_group hΩ C hC
  refine ⟨⟨fun ψ => by rw [h0]; rfl, fun s t ψ => by rw [hadd]; rfl⟩,
    h.wedgeModularDefect_continuous hΩ C hC, fun t ψ => ?_, fun t =>
    ⟨(h.wedgeModularDefect_vacuum hΩ C hC t).1, (h.wedgeModularDefect_vacuum hΩ C hC t).2,
      h.wedgeModularDefect_translations hΩ C hC t, h.wedgeModularDefect_boosts hΩ C hC t⟩⟩
  have hb : U (wedgeBoost (2 * Real.pi * t)) (U (wedgeBoost (-(2 * Real.pi * t))) ψ) = ψ := by
    rw [← LinearIsometryEquiv.trans_apply, ← h.map_mul, ← wedgeBoost_groupLaw.2, add_neg_cancel,
      wedgeBoost_groupLaw.1, h.map_one]
    rfl
  rw [wedgeModularDefect, LinearIsometryEquiv.trans_apply, hb]

/-! ### Bisognano–Wichmann up to an internal symmetry -/

/-- Modular covariance for the right wedge (MC): for every real `t` and every diamond `B`,
`Δ_{W_R}^{it} R(B) Δ_{W_R}^{-it} = R(b(-2πt) B)`, with `Δ_{W_R}^{it}` the modular unitary group of
`(R(W_R), Ω)` formed with the reference conjugation `C`, `R(B)` the local von Neumann algebra and
`b` the boost of the right wedge. `b(-2πt) B` is a diamond (`isAlexandrovBasisSet_smul`). The
condition is an equality of sets of operators and does not involve the unitaries `U`; it does not
assert `Δ_{W_R}^{it} = U(b(-2πt))`.

The standardness of `(R(W_R), Ω)` enters as the proof `hΩ` that names the modular group.

Blueprint: def:wedge-modular-covariance -/
def IsWedgeModularCovariant (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) {Ω : H}
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) : Prop :=
  ∀ (t : ℝ) (B : Set StandardMinkowskiSpacetime.Carrier) (hB : IsAlexandrovBasisSet B),
    (fun a => conj[modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C
        hC t] a) '' N.localVonNeumann π hB =
      N.localVonNeumann π (isAlexandrovBasisSet_smul (wedgeBoost (-(2 * Real.pi * t))) hB)

/-- An internal symmetry of `(π, Ω)`: a unitary `X` with `XΩ = Ω` and `X R(B) X⁻¹ = R(B)` for
every diamond `B`, with `R(B)` the local von Neumann algebra. Commutation with the translations is
not part of the definition.

Blueprint: def:internal-symmetry -/
structure IsInternalSymmetry (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (X : H ≃ₗᵢ[ℂ] H) : Prop where
  /-- `XΩ = Ω`. -/
  apply_vacuum : X Ω = Ω
  /-- `X R(B) X⁻¹ = R(B)` for every diamond `B`. -/
  conj_image_localVonNeumann : ∀ (B : Set StandardMinkowskiSpacetime.Carrier)
    (hB : IsAlexandrovBasisSet B),
    (fun a => conj[X] a) '' N.localVonNeumann π hB = N.localVonNeumann π hB

set_option hygiene false in
/-- `Δ_W^{is}` as a unitary, for the binders `N π W hΩW C hC` in scope. -/
local notation "ΔW[" s "]" =>
  modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩW C hC s

set_option hygiene false in
/-- The modular conjugation `J_W`, for the binders `N π W hΩW C hC` in scope. -/
local notation "𝒥W" => modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩW C hC

/-- Internal symmetries commute with the wedge modular objects: if `X` is an internal symmetry of
`(π, Ω)`, then `X Δ_W^{is} = Δ_W^{is} X` for every real `s` and `X J_W = J_W X`.

The blueprint states this for every wedge `W` of a weakly additive covariant vacuum
representation; these hypotheses enter only through the standardness of `(R(W), Ω)`, the proof
`hΩW` that names the modular objects, which `IsCovariantVacuumRep.wedge_isCyclicSeparatingVector`
supplies. The statement is made for every region `W` with that property.

Blueprint: lmm:internal-symmetry-commutes-wedge-modular -/
theorem IsInternalSymmetry.commute_modular {X : H ≃ₗᵢ[ℂ] H} (hX : N.IsInternalSymmetry π Ω X)
    {W : Set StandardMinkowskiSpacetime.Carrier}
    (hΩW : IsCyclicSeparatingVector (N.regionVonNeumann π W) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) :
    (∀ (s : ℝ) (ψ : H), X (ΔW[s] ψ) = ΔW[s] (X ψ)) ∧ ∀ ψ : H, X (𝒥W ψ) = 𝒥W (X ψ) := by
  obtain ⟨-, -, -, hU, hJ⟩ := Physicslib4.Modular.modular_objects_unitary_commute
    (N.regionVonNeumann_isVonNeumannSet π W).2 hΩW C hC X
    (N.conj_image_region_of_conj_image_localVonNeumann π X hX.conj_image_localVonNeumann W).2
    hX.apply_vacuum
  exact ⟨hU, hJ⟩

/-- Modular covariance for every wedge: under (MC), for every `g` in the inhomogeneous Lorentz
group, every real `t` and every diamond `B`,
`Δ_{gW_R}^{it} R(B) Δ_{gW_R}^{-it} = R(b_g(-2πt) B)`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness of `(R(W_R), Ω)` and `(R(gW_R), Ω)`, the proofs `hΩ` and `hΩg`.

Blueprint: lmm:modular-covariance-all-wedges -/
theorem IsCovariantVacuumRep.modularCovariant_all_wedges (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (hMC : N.IsWedgeModularCovariant π hΩ C hC)
    (g : InhomogeneousLorentzGroup)
    (hΩg : IsCyclicSeparatingVector (N.regionVonNeumann π (g • rightWedge)) Ω)
    (t : ℝ) (B : Set StandardMinkowskiSpacetime.Carrier) (hB : IsAlexandrovBasisSet B) :
    (fun a => conj[modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π (g • rightWedge)).2
        hΩg C hC t] a) '' N.localVonNeumann π hB =
      N.localVonNeumann π
        (isAlexandrovBasisSet_smul (wedgeBoostAlong g (-(2 * Real.pi * t))) hB) := by
  have hcongr : ∀ {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
      (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂),
      B₁ = B₂ → N.localVonNeumann π h₁ = N.localVonNeumann π h₂ := by
    rintro _ _ _ _ rfl; rfl
  have hinv : ∀ x, U g⁻¹ x = (U g).symm x := fun x => by
    apply (U g).injective
    rw [LinearIsometryEquiv.apply_symm_apply, ← LinearIsometryEquiv.trans_apply, ← h.map_mul,
      mul_inv_cancel, h.map_one]; rfl
  have hconj : ∀ (k : InhomogeneousLorentzGroup) {B' : Set StandardMinkowskiSpacetime.Carrier}
      (hB' : IsAlexandrovBasisSet B'),
      (fun a => conj[U k] a) '' N.localVonNeumann π hB' =
        N.localVonNeumann π (isAlexandrovBasisSet_smul k hB') := fun k B' hB' => by
    have hfun : (fun a => conj[U k] a) = Physicslib4.lieConj (U k) := by
      funext a; ext x; simp
    rw [hfun]; exact lieConj_image_localVonNeumann N π (U k) k hB' (h.covariant k)
  obtain ⟨-, -, -, hU, -⟩ := h.wedge_modular_covariance (W := rightWedge) ⟨1, (one_smul _ _).symm⟩
    g hΩ hΩg C C hC hC
  have hfun : (fun a : H →L[ℂ] H => conj[modularUnitaryGroup
      (N.regionVonNeumann_isVonNeumannSet π (g • rightWedge)).2 hΩg C hC t] a) =
      (fun a : H →L[ℂ] H => conj[U g] a) ∘ (fun a : H →L[ℂ] H => conj[modularUnitaryGroup
        (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC t] a) ∘
        (fun a : H →L[ℂ] H => conj[U g⁻¹] a) := by
    funext a; ext x
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    have hg : ∀ y, (U g⁻¹).symm y = U g y := fun y => by
      rw [LinearIsometryEquiv.symm_apply_eq, hinv, LinearIsometryEquiv.symm_apply_apply]
    rw [hg, hinv, hU]
    congr 2
    rw [LinearIsometryEquiv.symm_apply_eq, ← hU, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [hfun, Set.image_comp, Set.image_comp, hconj, hMC, hconj]
  exact hcongr _ _ (by rw [wedgeBoostAlong, mul_smul, mul_smul])

/-- Under (MC) the defect preserves every local algebra: `Z(t) R(B) Z(t)⁻¹ = R(B)` for every real
`t` and every diamond `B`.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`.

Blueprint: lmm:wedge-modular-defect-local -/
theorem IsCovariantVacuumRep.wedgeModularDefect_local (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (hMC : N.IsWedgeModularCovariant π hΩ C hC)
    (t : ℝ) (B : Set StandardMinkowskiSpacetime.Carrier) (hB : IsAlexandrovBasisSet B) :
    (fun a => conj[Z[t]] a) '' N.localVonNeumann π hB = N.localVonNeumann π hB := by
  have hcongr : ∀ {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
      (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂),
      B₁ = B₂ → N.localVonNeumann π h₁ = N.localVonNeumann π h₂ := by
    rintro _ _ _ _ rfl; rfl
  have hfunU : (fun a => conj[U (wedgeBoost (2 * Real.pi * t))] a) =
      Physicslib4.lieConj (U (wedgeBoost (2 * Real.pi * t))) := by
    funext a; ext x; simp
  have hfun : (fun a : H →L[ℂ] H => conj[Z[t]] a) =
      (fun a : H →L[ℂ] H => conj[modularUnitaryGroup
        (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC t] a) ∘
        (fun a : H →L[ℂ] H => conj[U (wedgeBoost (2 * Real.pi * t))] a) := by
    funext a; ext ψ
    simp [wedgeModularDefect]
  rw [hfun, Set.image_comp, hfunU, lieConj_image_localVonNeumann N π _ _ hB
    (h.covariant (wedgeBoost (2 * Real.pi * t))), hMC]
  exact hcongr _ _ (by rw [← mul_smul, ← wedgeBoost_groupLaw.2, neg_add_cancel,
    wedgeBoost_groupLaw.1, one_smul])

/-- Bisognano–Wichmann up to an internal symmetry (BW-a): for a covariant vacuum representation
satisfying modular covariance for the right wedge (MC), for every real `t` the wedge modular
defect `Z(t) = Δ^{it} U(b(2πt))` satisfies `Δ^{it} = Z(t) U(b(-2πt))`, is an internal symmetry of
`(π, Ω)` (`Z(t)Ω = Ω` and `Z(t) R(B) Z(t)⁻¹ = R(B)` for every diamond `B`), and commutes with the
translations; moreover `J U(a) J = U(j a)` for every `a ∈ ℝ⁴`, with `j` the wedge reflection.

The blueprint assumes `π` weakly additive in the von Neumann sense; it enters only through the
standardness proof `hΩ`, which `IsCovariantVacuumRep.wedge_isCyclicSeparatingVector` supplies.

**Restriction:** assumes modular covariance (MC) for the right wedge and identifies
`Δ_{W_R}^{it}` with the boost `U(b(-2πt))` only up to an internal symmetry `Z(t)`. The intended
form, exact Bisognano–Wichmann for a covariant representation, is Brunetti–Guido–Longo's
Theorem 2.3 with their Corollary 2.8 under the distal split property, and is waiting on the
measurable group cohomology of the Poincaré group and its universal cover.

Blueprint: thrm:bisognano-wichmann-internal -/
theorem IsCovariantVacuumRep.bisognanoWichmann_internal (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (hMC : N.IsWedgeModularCovariant π hΩ C hC) :
    (∀ t : ℝ,
      (∀ ψ : H,
        modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC t ψ =
          Z[t] (U (wedgeBoost (-(2 * Real.pi * t))) ψ)) ∧
      N.IsInternalSymmetry π Ω Z[t] ∧
      ∀ (a : SpacetimeModel) (ψ : H),
        Z[t] (U (translationSub a) ψ) = U (translationSub a) (Z[t] ψ)) ∧
    ∀ a : SpacetimeModel, 𝒥R[Tr[a]] = Tr[wedgeReflection a] :=
  ⟨fun t => ⟨(h.wedgeModularDefect_properties hΩ C hC).2.2.1 t,
    ⟨(h.wedgeModularDefect_vacuum hΩ C hC t).1, h.wedgeModularDefect_local hΩ C hC hMC t⟩,
    h.wedgeModularDefect_translations hΩ C hC t⟩,
    h.wedge_modularConjugation_translations hΩ C hC⟩

/-- The internal symmetry commutes with all wedge modular objects: under (MC), for every real `t`,
`Z(t)` commutes with `Δ_W^{is}` for every real `s` and with `J_W`; it commutes with every boost
`U(b(s))`, and `t ↦ Z(t)` is a strongly continuous one-parameter unitary group.

The blueprint states the commutation for every wedge `W` of a weakly additive covariant vacuum
representation; these hypotheses enter only through the standardness of `(R(W_R), Ω)` and
`(R(W), Ω)`, the proofs `hΩ` and `hΩW`. The statement is made for every region `W` with that
property.

Blueprint: crllr:bw-defect-commutes-wedge-modular -/
theorem IsCovariantVacuumRep.wedgeModularDefect_commute_wedge_modular
    (h : N.IsCovariantVacuumRep π Ω U)
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π rightWedge) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (hMC : N.IsWedgeModularCovariant π hΩ C hC) :
    (∀ (t : ℝ) (W : Set StandardMinkowskiSpacetime.Carrier)
        (hΩW : IsCyclicSeparatingVector (N.regionVonNeumann π W) Ω),
      (∀ (s : ℝ) (ψ : H), Z[t] (ΔW[s] ψ) = ΔW[s] (Z[t] ψ)) ∧
        ∀ ψ : H, Z[t] (𝒥W ψ) = 𝒥W (Z[t] ψ)) ∧
      (∀ (t s : ℝ) (ψ : H), Z[t] (U (wedgeBoost s) ψ) = U (wedgeBoost s) (Z[t] ψ)) ∧
      IsOneParameterUnitaryGroup (N.wedgeModularDefect π U hΩ C hC) ∧
      IsStronglyContinuous (N.wedgeModularDefect π U hΩ C hC) := by
  sorry

end HaagKastlerNet

end HaagKastler
end AQFT
end Physicslib4
