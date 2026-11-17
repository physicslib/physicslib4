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
  sorry

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
  sorry

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
  sorry

end Commutant

end Physicslib4.Modular

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open scoped Pointwise
open Physicslib4.Modular

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
  sorry

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
  sorry

/-- Light-cone factorisation of the translation unitaries: with `α = (a⁰ + a¹)/2`,
`β = (a⁰ - a¹)/2` and `a_⊥ = (0, 0, a², a³)`, `U(a) = U(α l₊) U(β l₋) U(a_⊥)`.

Blueprint: lmm:translation-light-cone-factorisation -/
theorem IsCovariantVacuumRep.translation_lightCone_factorisation
    (h : N.IsCovariantVacuumRep π Ω U) (a : SpacetimeModel) (ψ : H) :
    U (translationSub a) ψ =
      U (translationSub (((a 0 + a 1) / 2) • l₊))
        (U (translationSub (((a 0 - a 1) / 2) • l₋))
          (U (translationSub !₂[0, 0, a 2, a 3]) ψ)) := by
  sorry

/-- The lightlike translations `t ↦ U(t l₊)` and `t ↦ U(t l₋)` have positive energy, and
`U(t l₊)Ω = U(t l₋)Ω = Ω` for every `t`.

Blueprint: lmm:lightlike-translations-positive-energy -/
theorem IsCovariantVacuumRep.lightlike_translations_positiveEnergy
    (h : N.IsCovariantVacuumRep π Ω U) :
    IsPositiveEnergy (fun t : ℝ => U (translationSub (t • l₊))) ∧
      IsPositiveEnergy (fun t : ℝ => U (translationSub (t • l₋))) ∧
      ∀ t : ℝ, U (translationSub (t • l₊)) Ω = Ω ∧ U (translationSub (t • l₋)) Ω = Ω := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end HaagKastlerNet

end HaagKastler
end AQFT
end Physicslib4
