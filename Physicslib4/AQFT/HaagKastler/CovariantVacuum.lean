/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.RegionAlgebra
import Physicslib4.AQFT.HaagKastler.ReehSchlieder.Additivity
import Physicslib4.Operators.Modular.Intertwining
import Physicslib4.AQFT.HaagKastler.GeometricCovariance

/-!
# Covariant vacuum representations

The vacuum data of `HaagKastlerNet.IsVacuumState` and the Reeh–Schlieder theorem implement the
Poincaré action only on the vectors `π(a)Ω`, and require positive energy only along
future-timelike translations. Borchers' theorem and its wedge corollary need operator-level
implementation, the group law, invariance of `Ω`, continuity along boosts and translations, and
positive energy along lightlike translations. `IsCovariantVacuumRep` collects these hypotheses. It
is passed as a hypothesis, as the vacuum data are, and it changes no axiom.

In a covariant vacuum representation the region algebras are covariant,
`U(g) R(O) U(g)⁻¹ = R(g O)`, and under weak additivity `Ω` is cyclic and separating for every
wedge algebra, whose modular objects are then covariant and commute with the stabiliser of the
wedge.

Conventions:
* `V T V⁻¹` for a unitary `V` and a bounded operator `T` is written `conj[V] T` (local notation),
  and `V M V⁻¹` for a set `M` of bounded operators is `(fun a => conj[V] a) '' M`, as in
  `Physicslib4.Operators.Modular.Intertwining`.
* The closed forward cone `V̄₊ = {v | η(v, v) ≤ 0, v⁰ ≥ 0}` is written explicitly.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open scoped Pointwise
open Physicslib4.Modular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The conjugate `V a V⁻¹` of a bounded operator `a` by a unitary `V`. -/
local notation "conj[" V "] " a =>
  ContinuousLinearMap.comp (LinearIsometry.toContinuousLinearMap
    (LinearIsometryEquiv.toLinearIsometry V))
    (ContinuousLinearMap.comp a (LinearIsometry.toContinuousLinearMap
      (LinearIsometryEquiv.toLinearIsometry (LinearIsometryEquiv.symm V))))

namespace HaagKastlerNet

/-- A covariant vacuum representation `(π, Ω, U)` of the quasilocal algebra of a Haag–Kastler net
`N`: a `*`-representation `π` on `H`, a vector `Ω ∈ H` and unitaries `U(g)`, `g` in the
inhomogeneous Lorentz group, such that
1. `U` is a group homomorphism: `U(1) = 1` and `U(L'L) = U(L')U(L)`;
2. `t ↦ U(γ(t))ψ` is continuous for every continuous one-parameter subgroup `γ` and every `ψ`;
3. `U(g) π(a) U(g)⁻¹ = π(β_g a)` for all `g` and `a`;
4. `U(g)Ω = Ω` for all `g`;
5. `t ↦ U((1, tn))` has positive energy for every nonzero `n` in the closed forward cone,
   lightlike directions included;
6. `Ω` is cyclic for `π(𝔘)`.

**Restriction:** continuity is required only along continuous one-parameter subgroups; the
intended general form is strong continuity of `g ↦ U(g)ψ` on the whole group, which the GNS
construction of an invariant state with continuous matrix coefficients supplies, and is waiting
on a use that needs it.

**Restriction:** positive energy is assumed along lightlike directions too; the intended form
requires it only along future-timelike translations, with the lightlike case derived, and is
waiting on the strong-resolvent-limit argument for the generators.

Blueprint: def:covariant-vacuum-representation -/
structure IsCovariantVacuumRep (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H)) : Prop where
  /-- `U(1) = 1`. -/
  map_one : U 1 = LinearIsometryEquiv.refl ℂ H
  /-- `U(L'L) = U(L')U(L)`. -/
  map_mul : ∀ L L' : InhomogeneousLorentzGroup, U (L' * L) = (U L).trans (U L')
  /-- Strong continuity along every continuous one-parameter subgroup. -/
  continuous_apply : ∀ γ : ℝ → InhomogeneousLorentzGroup, IsContinuousOneParameterSubgroup γ →
    ∀ ψ : H, Continuous fun t => U (γ t) ψ
  /-- Operator-level covariance `U(g) π(a) U(g)⁻¹ = π(β_g a)`. -/
  covariant : ∀ (g : InhomogeneousLorentzGroup) (a : N.quasilocal.carrier) (x : H),
    U g (π a ((U g).symm x)) = π (N.action g a) x
  /-- Invariance of the vacuum vector. -/
  invariant : ∀ g : InhomogeneousLorentzGroup, U g Ω = Ω
  /-- Positive energy along every nonzero closed-forward-cone translation direction. -/
  positiveEnergy : ∀ n : SpacetimeModel, minkowskiForm n n ≤ 0 → 0 ≤ n 0 → n ≠ 0 →
    IsPositiveEnergy fun t : ℝ => U (translationFlow n t)
  /-- `Ω` is cyclic for `π(𝔘)`. -/
  cyclic : GNS.IsCyclicVector π Ω

variable {N : HaagKastlerNet} {π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
  {U : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H)}

/-- A covariant vacuum representation gives the vacuum hypotheses: `U(g)π(a)Ω = π(β_g a)Ω`, and
`t ↦ U(γ(t))` has positive energy for every future-timelike translation subgroup `γ`. With
`U(x) := U(translationSub x)` these are the hypotheses of the Reeh–Schlieder theorem.

Blueprint: lmm:covariant-vacuum-bridge -/
theorem IsCovariantVacuumRep.vacuum_hypotheses (h : N.IsCovariantVacuumRep π Ω U) :
    (∀ (g : InhomogeneousLorentzGroup) (a : N.quasilocal.carrier),
        U g (π a Ω) = π (N.action g a) Ω) ∧
      (∀ γ : ℝ → InhomogeneousLorentzGroup, IsFutureTimelikeTranslation γ →
        IsPositiveEnergy fun t => U (γ t)) ∧
      (∀ (x : StandardMinkowskiSpacetime.Carrier) (a : N.quasilocal.carrier),
        U (translationSub x) (π a Ω) = π (N.action (translationSub x) a) Ω) ∧
      ∀ n : StandardMinkowskiSpacetime.Carrier, (n : SpacetimeModel) ∈ minkowskiForwardCone 0 →
        IsPositiveEnergy fun t : ℝ => U (translationSub (t • n)) := by
  have hcov : ∀ (g : InhomogeneousLorentzGroup) (a : N.quasilocal.carrier),
      U g (π a Ω) = π (N.action g a) Ω := fun g a => by
    simpa [(U g).symm_apply_eq.2 (h.invariant g).symm] using h.covariant g a Ω
  have hpos : ∀ n : StandardMinkowskiSpacetime.Carrier,
      (n : SpacetimeModel) ∈ minkowskiForwardCone 0 →
        IsPositiveEnergy fun t : ℝ => U (translationSub (t • n)) := by
    have key : ∀ m : SpacetimeModel, m ∈ minkowskiForwardCone 0 →
        minkowskiForm m m ≤ 0 ∧ 0 ≤ m 0 ∧ m ≠ 0 := by
      rintro m ⟨h1, h2⟩
      simp only [WithLp.ofLp_zero, Pi.zero_apply, sub_zero] at h1 h2
      refine ⟨?_, h1.le, ?_⟩
      · rw [minkowskiForm_apply]; nlinarith
      · rintro rfl; simp at h1
    intro n hn
    obtain ⟨k1, k2, k3⟩ := key _ hn
    exact h.positiveEnergy _ k1 k2 k3
  exact ⟨hcov, fun γ ⟨n, hn, hγ⟩ => hγ ▸ hpos n hn, fun x a => hcov _ a, hpos⟩

/-- Reeh–Schlieder in a covariant vacuum representation: if `π` is weakly additive in the von
Neumann sense, then `Ω` is cyclic for `π(𝔘(B))` for every nonempty diamond `B`.

Blueprint: crllr:covariant-vacuum-reeh-schlieder -/
theorem IsCovariantVacuumRep.cyclic_localOperators (h : N.IsCovariantVacuumRep π Ω U)
    (hwa : N.IsWeaklyAdditiveVonNeumann π) {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B) (hne : B.Nonempty) :
    Dense ((fun T => T Ω) '' N.localOperators π hB) :=
  reeh_schlieder_cyclic_of_vonNeumann π Ω (fun x => U (translationSub x))
    h.vacuum_hypotheses.2.2.1 h.vacuum_hypotheses.2.2.2 hwa h.cyclic hB hne

/-- Covariance of the generating sets: `U(g) S(O) U(g)⁻¹ = S(g O)` for every `g` and `O`.

Blueprint: lmm:region-generating-set-covariance -/
theorem IsCovariantVacuumRep.conj_image_regionGeneratingSet (h : N.IsCovariantVacuumRep π Ω U)
    (g : InhomogeneousLorentzGroup) (O : Set StandardMinkowskiSpacetime.Carrier) :
    (fun a => conj[U g] a) '' N.regionGeneratingSet π O = N.regionGeneratingSet π (g • O) := by
  have hfun : (fun a => conj[U g] a) = Physicslib4.lieConj (U g) := by
    funext a; ext x; simp
  rw [hfun, ← N.regionGeneratingSet_smul π g O, regionGeneratingSet]
  simp only [Set.image_iUnion]
  refine Set.iUnion_congr fun B => Set.iUnion_congr fun hB => Set.iUnion_congr fun _ => ?_
  exact lieConj_image_localVonNeumann N π (U g) g hB (h.covariant g)

/-- Covariance of region algebras: `U(g) R(O) U(g)⁻¹ = R(g O)` for every `g` and `O`.

Blueprint: thrm:region-algebra-covariance -/
theorem IsCovariantVacuumRep.conj_image_regionVonNeumann (h : N.IsCovariantVacuumRep π Ω U)
    (g : InhomogeneousLorentzGroup) (O : Set StandardMinkowskiSpacetime.Carrier) :
    (fun a => conj[U g] a) '' N.regionVonNeumann π O = N.regionVonNeumann π (g • O) := by
  have hfun : (fun a => conj[U g] a) = Physicslib4.lieConj (U g) := by
    funext a; ext x; simp
  rw [regionVonNeumann, regionVonNeumann, ← h.conj_image_regionGeneratingSet g O, hfun,
    (Physicslib4.lieConj (U g)).image_centralizer_centralizer]

/-- The vacuum is cyclic for regions containing a nonempty diamond: if `π` is weakly additive in
the von Neumann sense and `O` contains a nonempty diamond, then `R(O)Ω` is dense.

Blueprint: lmm:region-algebra-cyclic -/
theorem IsCovariantVacuumRep.cyclic_regionVonNeumann (h : N.IsCovariantVacuumRep π Ω U)
    (hwa : N.IsWeaklyAdditiveVonNeumann π) {O : Set StandardMinkowskiSpacetime.Carrier}
    (hO : ∃ B : Set StandardMinkowskiSpacetime.Carrier,
      IsAlexandrovBasisSet B ∧ B.Nonempty ∧ B ⊆ O) :
    Dense ((fun T => T Ω) '' N.regionVonNeumann π O) := by
  sorry

end HaagKastlerNet

/-- Cyclic and separating from a cyclic subset of the commutant: if `𝒩 ⊆ M'` and `MΩ` and `𝒩Ω`
are dense, then `Ω` is cyclic and separating for `M`.

Blueprint: lmm:cyclic-separating-of-commutant -/
theorem isCyclicSeparatingVector_of_subset_centralizer {M 𝒩 : Set (H →L[ℂ] H)} {Ω : H}
    (h𝒩 : 𝒩 ⊆ Set.centralizer M)
    (hMΩ : Dense ((fun a => a Ω) '' M)) (h𝒩Ω : Dense ((fun b => b Ω) '' 𝒩)) :
    IsCyclicSeparatingVector M Ω :=
  ⟨hMΩ, h𝒩Ω.mono (Set.image_mono h𝒩)⟩

namespace HaagKastlerNet

variable {N : HaagKastlerNet} {π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
  {U : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H)}

/-- The vacuum is cyclic and separating for the wedge algebras: if `π` is weakly additive in the
von Neumann sense, then for every `g`, `Ω` is cyclic and separating for `R(g W_R)` and
`R(g W_L)`. In particular, for every wedge `W`, `R(W)` is a von Neumann algebra for which `Ω` is
cyclic and separating, so the modular objects of `(R(W), Ω)` are defined; they depend only on the
set `W` and on `Ω`.

Blueprint: thrm:wedge-cyclic-separating -/
theorem IsCovariantVacuumRep.wedge_isCyclicSeparatingVector (h : N.IsCovariantVacuumRep π Ω U)
    (hwa : N.IsWeaklyAdditiveVonNeumann π) :
    (∀ g : InhomogeneousLorentzGroup,
      IsCyclicSeparatingVector (N.regionVonNeumann π (g • rightWedge)) Ω ∧
        IsCyclicSeparatingVector (N.regionVonNeumann π (g • leftWedge)) Ω) ∧
      ∀ W : Set StandardMinkowskiSpacetime.Carrier, IsWedge W →
        IsVonNeumannSet (N.regionVonNeumann π W) ∧
          IsCyclicSeparatingVector (N.regionVonNeumann π W) Ω := by
  sorry

/-- Poincaré covariance of the wedge modular objects: for a wedge `W` and `h` in the
inhomogeneous Lorentz group, `h W` is a wedge, and, including domains,
`U(h) S_W U(h)⁻¹ = S_{hW}`, `U(h) Δ_W U(h)⁻¹ = Δ_{hW}`, `U(h) Δ_W^{it} U(h)⁻¹ = Δ_{hW}^{it}` and
`U(h) J_W U(h)⁻¹ = J_{hW}`.

The standardness of `(R(W), Ω)` and `(R(hW), Ω)` enters as the proofs `hΩ₁`, `hΩ₂` that name the
modular objects; under weak additivity they are supplied by
`IsCovariantVacuumRep.wedge_isCyclicSeparatingVector`. The reference conjugations `C₁`, `C₂` are
independent.

The binders are the ambient Hilbert space `H`, the representation data `N`, `π`, `Ω`, `U` with
the covariance hypothesis `h`, the wedge `W` with `hW` and the element `k`, the standardness proofs
`hΩ₁`, `hΩ₂`, and the reference conjugations `C₁`, `C₂` with their involution proofs, which the
modular API requires; the von Neumann property of the region algebras is supplied inline by
`regionVonNeumann_isVonNeumannSet`.

Blueprint: crllr:wedge-modular-covariance -/
theorem IsCovariantVacuumRep.wedge_modular_covariance (h : N.IsCovariantVacuumRep π Ω U)
    {W : Set StandardMinkowskiSpacetime.Carrier} (hW : IsWedge W) (k : InhomogeneousLorentzGroup)
    (hΩ₁ : IsCyclicSeparatingVector (N.regionVonNeumann π W) Ω)
    (hΩ₂ : IsCyclicSeparatingVector (N.regionVonNeumann π (k • W)) Ω)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x) :
    IsWedge (k • W) ∧
    ((∀ ψ : H, ψ ∈ (linearizedTomitaPre (N.regionVonNeumann π W) Ω C₁).closure.domain ↔
        U k ψ ∈ (linearizedTomitaPre (N.regionVonNeumann π (k • W)) Ω C₂).closure.domain) ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre (N.regionVonNeumann π W) Ω C₁).closure.domain)
        (h₂ : U k ψ ∈ (linearizedTomitaPre (N.regionVonNeumann π (k • W)) Ω C₂).closure.domain),
        tomitaOperator (N.regionVonNeumann π (k • W)) Ω C₂ ⟨U k ψ, h₂⟩ =
          U k (tomitaOperator (N.regionVonNeumann π W) Ω C₁ ⟨ψ, h₁⟩)) ∧
    (∀ ψ χ : H,
      (∃ h' : U k ψ ∈ (modularOperator (N.regionVonNeumann π (k • W)) Ω C₂).domain,
          modularOperator (N.regionVonNeumann π (k • W)) Ω C₂ ⟨U k ψ, h'⟩ = U k χ) ↔
        ∃ h' : ψ ∈ (modularOperator (N.regionVonNeumann π W) Ω C₁).domain,
          modularOperator (N.regionVonNeumann π W) Ω C₁ ⟨ψ, h'⟩ = χ) ∧
    (∀ (t : ℝ) (ψ : H),
      U k (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ₁ C₁ hC₁ t
          ((U k).symm ψ)) =
        modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π (k • W)).2 hΩ₂ C₂ hC₂ t ψ) ∧
    ∀ φ : H,
      U k (modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ₁ C₁ hC₁
          ((U k).symm φ)) =
        modularConjugation (N.regionVonNeumann_isVonNeumannSet π (k • W)).2 hΩ₂ C₂ hC₂ φ := by
  sorry

/-- The stabiliser of a wedge commutes with its modular objects: if `k W = W`, then `U(k)`
commutes with `Δ_W^{it}` for every `t` and with `J_W`. This applies to `k = b_g(s)` when
`W = g W_R`, and, for `W = W_R`, to `k = b(s)` and to the transverse translations
`k = translationSub a` with `a⁰ = a¹ = 0`.

The standardness of `(R(W), Ω)` enters as the proof `hΩ` that names the modular objects; under
weak additivity it is supplied by `IsCovariantVacuumRep.wedge_isCyclicSeparatingVector`.

The binders are the ambient Hilbert space `H`, the representation data `N`, `π`, `Ω`, `U` with
the covariance hypothesis `h`, the region `W`, the standardness proof `hΩ`, and the reference
conjugation `C` with its involution proof `hC`, which the modular API requires; the von Neumann
property of `R(W)` is supplied inline by `regionVonNeumann_isVonNeumannSet`.

Blueprint: crllr:wedge-stabiliser-commutes-modular -/
theorem IsCovariantVacuumRep.wedge_stabiliser_commute (h : N.IsCovariantVacuumRep π Ω U)
    {W : Set StandardMinkowskiSpacetime.Carrier}
    (hΩ : IsCyclicSeparatingVector (N.regionVonNeumann π W) Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) :
    (∀ k : InhomogeneousLorentzGroup, k • W = W →
      (∀ (t : ℝ) (ψ : H),
        U k
            (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC t ψ) =
          modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC t
            (U k ψ)) ∧
      ∀ ψ : H,
        U k
            (modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC ψ) =
          modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC (U k ψ)) ∧
    (∀ (g : InhomogeneousLorentzGroup) (s : ℝ), W = g • rightWedge →
      (∀ (t : ℝ) (ψ : H),
        U (wedgeBoostAlong g s)
            (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC t ψ) =
          modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC t
            (U (wedgeBoostAlong g s) ψ)) ∧
      ∀ ψ : H,
        U (wedgeBoostAlong g s)
            (modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC ψ) =
          modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC
            (U (wedgeBoostAlong g s) ψ)) ∧
    (W = rightWedge →
      (∀ s : ℝ,
        (∀ (t : ℝ) (ψ : H),
          U (wedgeBoost s)
              (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC t ψ) =
            modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC t
              (U (wedgeBoost s) ψ)) ∧
        ∀ ψ : H,
          U (wedgeBoost s)
              (modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC ψ) =
            modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC
              (U (wedgeBoost s) ψ)) ∧
      ∀ a : SpacetimeModel, a 0 = 0 → a 1 = 0 →
        (∀ (t : ℝ) (ψ : H),
          U (translationSub a)
              (modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC t ψ) =
            modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC t
              (U (translationSub a) ψ)) ∧
        ∀ ψ : H,
          U (translationSub a)
              (modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC ψ) =
            modularConjugation (N.regionVonNeumann_isVonNeumannSet π W).2 hΩ C hC
              (U (translationSub a) ψ)) := by
  sorry

end HaagKastlerNet

end HaagKastler
end AQFT
end Physicslib4
