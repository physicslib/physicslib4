/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.QuasilocalIntertwiner
import Physicslib4.Operators.Conjugation
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Vacuum states: the generator-parameterized scaffold

A *vacuum state* of a (Poincaré-)covariant quasilocal algebra is an invariant
state whose GNS representation additionally satisfies the **spectrum condition**:
the energy-momentum is positive. The physically faithful form is that, for every
future-pointing timelike direction `n`, the self-adjoint generator `P(n)` of the
one-parameter translation unitary group `t ↦ U(t·n)` is positive (`0 ≤ P(n)`).

Stating that faithfully needs Stone's theorem and the theory of unbounded
self-adjoint operators, neither of which Mathlib currently provides. This file
sets up the API so that the spectrum condition enters **as a hypothesis** and the
generator (and its positivity) is supplied data, deferring only the
construction/self-adjointness that Stone will provide:

* `IsPositiveEnergy V` — a one-parameter unitary group `V : ℝ → (H ≃ₗᵢ[ℂ] H)` has
  positive energy when its generator is a positive *bounded* operator `P` with
  `V t = exp(i t P)`. The bounded-generator form is a genuine restriction (physical
  generators are unbounded); it is the scaffold that compiles today, with the
  unbounded form to follow once Stone's theorem lands.
* `CovariantQuasilocalAlgebra.IsVacuumState ftl ω` — invariance plus, in the GNS
  representation, positive energy of every future-timelike translation subgroup.
  The future-timelike-translation predicate `ftl` is a parameter.
* `translationSub` / `translationFlow` / `IsFutureTimelikeTranslation` — the pure
  *translation* subgroup `n ↦ (id, n)` of the inhomogeneous Lorentz group, the
  one-parameter flow `t ↦ (id, t • n)`, and the concrete predicate picking out the
  flows in a future-pointing timelike direction `n` (i.e. `n` in the forward
  Minkowski cone). This wires in the translation subgroup and its causal structure,
  so `ftl` can be discharged with its intended value.
* `CovariantQuasilocalAlgebra.IsVacuumStateConcrete ω` — `IsVacuumState` with `ftl`
  fixed to `IsFutureTimelikeTranslation`; the vacuum definition then depends on no
  free predicate.

These are the *necessary* conditions for a vacuum; constructing/discharging the
spectrum condition for a concrete net is the Stone-gated next layer.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A continuous one-parameter subgroup of the inhomogeneous Lorentz group:
`γ 0 = 1` and `γ (s + t) = γ s * γ t`. The intended `γ` for the spectrum condition
are the future-timelike *translation* subgroups. -/
def IsOneParameterSubgroup (γ : ℝ → InhomogeneousLorentzGroup) : Prop :=
  γ 0 = 1 ∧ ∀ s t : ℝ, γ (s + t) = γ s * γ t

/-! ### The translation subgroup

The physically relevant one-parameter subgroups for the spectrum condition are the
pure *translations*. An element of `InhomogeneousLorentzGroup` is a pair
`(linear, translation)`; a pure translation has `linear = id`, so it embeds the
additive group of the spacetime carrier. This section wires that embedding in and
gives the concrete future-timelike-translation predicate, replacing the abstract
`ftl` parameter of `IsVacuumState` with its intended value. -/

/-- The pure-translation embedding of the spacetime carrier into the inhomogeneous
Lorentz group: `n ↦ (id, n)`, i.e. the affine map `x ↦ x + n`. -/
noncomputable def translationSub (n : StandardMinkowskiSpacetime.Carrier) :
    InhomogeneousLorentzGroup where
  linear := LinearEquiv.refl ℝ _
  translation := n
  isLorentz := isLorentz_refl
  isProper := isProper_refl
  isOrthochronous := isOrthochronous_refl

/-- The pure-translation embedding sends `0` to the identity. -/
@[simp] theorem translationSub_zero :
    translationSub (0 : StandardMinkowskiSpacetime.Carrier) = 1 :=
  InhomogeneousLorentzGroup.ext rfl rfl

/-- The pure-translation embedding is a homomorphism from the additive carrier:
`translationSub (n + m) = translationSub n * translationSub m` (the linear parts are
both the identity, and translations add). -/
theorem translationSub_mul (n m : StandardMinkowskiSpacetime.Carrier) :
    translationSub (n + m) = translationSub n * translationSub m := by
  refine InhomogeneousLorentzGroup.ext ?_ ?_
  · ext x; rfl
  · change n + m = n + (LinearEquiv.refl ℝ _) m
    simp

/-- The one-parameter translation subgroup in a direction `n`: `t ↦ (id, t • n)`. -/
noncomputable def translationFlow (n : StandardMinkowskiSpacetime.Carrier) :
    ℝ → InhomogeneousLorentzGroup :=
  fun t => translationSub (t • n)

/-- The translation flow in direction `n` is a one-parameter subgroup. -/
theorem isOneParameterSubgroup_translationFlow
    (n : StandardMinkowskiSpacetime.Carrier) :
    IsOneParameterSubgroup (translationFlow n) := by
  refine ⟨?_, ?_⟩
  · change translationSub ((0 : ℝ) • n) = 1
    rw [zero_smul, translationSub_zero]
  · intro s t
    change translationSub ((s + t) • n) = translationSub (s • n) * translationSub (t • n)
    rw [add_smul, translationSub_mul]

/-- **Concrete future-timelike-translation predicate.** A one-parameter subgroup `γ`
is a future-timelike translation when it is the translation flow `t ↦ (id, t • n)` in
a future-pointing timelike direction `n` — i.e. `n` lies in the forward Minkowski
cone at the origin. This is the value with which the abstract `ftl` parameter of
`IsVacuumState` is meant to be discharged. -/
def IsFutureTimelikeTranslation (γ : ℝ → InhomogeneousLorentzGroup) : Prop :=
  ∃ n : StandardMinkowskiSpacetime.Carrier,
    (n : SpacetimeModel) ∈ minkowskiForwardCone 0 ∧ γ = translationFlow n

/-- **Positive-energy condition (bounded-generator scaffold).** A one-parameter
unitary group `V : ℝ → (H ≃ₗᵢ[ℂ] H)` has *positive energy* when its generator is a
positive bounded operator: there is `P : H →L[ℂ] H` with `P.IsPositive` (hence
self-adjoint, with non-negative spectrum) such that `V t = exp(i t P)` for every
`t`.

The generator of a physical translation is unbounded, so requiring `P` bounded is a
restriction; the faithful unbounded form needs Stone's theorem and unbounded
self-adjoint operators, absent from Mathlib. The positivity `P.IsPositive` is the
energy-positivity that the spectrum condition asserts. -/
def IsPositiveEnergy (V : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∃ P : H →L[ℂ] H, P.IsPositive ∧
    ∀ (t : ℝ) (x : H), V t x = NormedSpace.exp (((t : ℂ) * Complex.I) • P) x

/-- The constant (trivial) unitary group `t ↦ id` has positive energy, with zero
generator `P = 0`: `exp(0) = 1 = id`, and `0` is a positive operator. -/
theorem isPositiveEnergy_const_refl :
    IsPositiveEnergy (fun _ : ℝ => LinearIsometryEquiv.refl ℂ H) := by
  refine ⟨0, ContinuousLinearMap.isPositive_zero, fun t x => ?_⟩
  simp [smul_zero, NormedSpace.exp_zero]

/-- **Uniqueness of the positive-energy generator.** If two bounded generators induce
the same one-parameter unitary group — `exp(i t P) = exp(i t Q)` for all `t` — they are
equal. Differentiating at `t = 0` gives `i \cdot P = i \cdot Q`, hence `P = Q`;
positivity is not needed. So the generator witnessing `IsPositiveEnergy` is unique. -/
theorem exp_generator_unique {P Q : H →L[ℂ] H}
    (h : ∀ (t : ℝ) (x : H),
      NormedSpace.exp (((t : ℂ) * Complex.I) • P) x
        = NormedSpace.exp (((t : ℂ) * Complex.I) • Q) x) :
    P = Q := by
  -- The two operator-valued exponential families coincide as functions.
  have hfun : (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • P))
      = (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • Q)) := by
    funext t; exact ContinuousLinearMap.ext (h t)
  -- Derivative at `0` of each exponential family is `i • generator`.  Working with a
  -- real scalar `u` and rewriting `((u:ℂ) * i) • R = u • (i • R)` avoids differentiating
  -- through the `ℝ → ℂ` coercion.
  have hderiv : ∀ R : H →L[ℂ] H,
      HasDerivAt (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • R))
        (Complex.I • R) 0 := by
    intro R
    have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • R) (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hc
    have hfeq : (fun u : ℝ => NormedSpace.exp (u • (Complex.I • R)))
        = (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • R)) := by
      funext u; rw [← Complex.coe_smul, smul_smul]
    rwa [hfeq] at hc
  have hP := hderiv P
  have hQ := hderiv Q
  rw [hfun] at hP
  have key : Complex.I • P = Complex.I • Q := hP.unique hQ
  exact smul_right_injective (H →L[ℂ] H) Complex.I_ne_zero key

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

/-- **Positive energy is a unitary invariant.** If a one-parameter unitary group `V`
has positive energy, so does its conjugate `t ↦ W ∘ V t ∘ W⁻¹` by a unitary `W`, with
generator `W P W⁻¹` (positive, being the unitary conjugate of the positive generator
`P`). Physically: the spectrum condition does not depend on the choice of unitary
frame. -/
theorem IsPositiveEnergy.conj (W : H ≃ₗᵢ[ℂ] H) {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) :
    IsPositiveEnergy (fun t => (W.symm.trans (V t)).trans W) := by
  obtain ⟨P, hPpos, hPexp⟩ := hV
  refine ⟨lieConj W P, ?_, fun t x => ?_⟩
  · -- `W P W⁻¹` is positive: symmetry and non-negativity transport through `W`'s
    -- isometry, using only `lieConj_apply` and `inner_map_map`.
    refine ContinuousLinearMap.isPositive_def.mpr ⟨fun a b => ?_, fun x => ?_⟩
    · simp only [ContinuousLinearMap.coe_coe, lieConj_apply]
      calc ⟪W (P (W.symm a)), b⟫_ℂ
          = ⟪W (P (W.symm a)), W (W.symm b)⟫_ℂ := by rw [W.apply_symm_apply]
        _ = ⟪P (W.symm a), W.symm b⟫_ℂ := W.inner_map_map _ _
        _ = ⟪W.symm a, P (W.symm b)⟫_ℂ := (ContinuousLinearMap.isPositive_def.mp hPpos).1 _ _
        _ = ⟪W (W.symm a), W (P (W.symm b))⟫_ℂ := (W.inner_map_map _ _).symm
        _ = ⟪a, W (P (W.symm b))⟫_ℂ := by rw [W.apply_symm_apply]
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply, lieConj_apply]
      have key : ⟪W (P (W.symm x)), x⟫_ℂ = ⟪P (W.symm x), W.symm x⟫_ℂ := by
        rw [← W.inner_map_map (P (W.symm x)) (W.symm x), W.apply_symm_apply]
      rw [key]
      have hpp := (ContinuousLinearMap.isPositive_def.mp hPpos).2 (W.symm x)
      rwa [ContinuousLinearMap.reApplyInnerSelf_apply] at hpp
  · -- `W ∘ exp(itP) ∘ W⁻¹ = exp(it · W P W⁻¹)` on cyclic vectors.
    change ((W.symm.trans (V t)).trans W) x
        = NormedSpace.exp (((t : ℂ) * Complex.I) • lieConj W P) x
    rw [← lieConj_smul, exp_lieConj, lieConj_apply,
      LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
      hPexp t (W.symm x)]

/-- **A positive-energy group is strongly continuous.** The bounded-generator scaffold
`V t = exp(i t P)` is automatically strongly continuous: `t ↦ V t x` is continuous for
every `x`, since `t ↦ (i t) • P` is continuous and the operator exponential is
continuous. This justifies describing a positive-energy group as a *strongly continuous*
one-parameter unitary group. -/
theorem IsPositiveEnergy.strongContinuous {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) (x : H) : Continuous (fun t : ℝ => V t x) := by
  obtain ⟨P, _, hPexp⟩ := hV
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  have hfun : (fun t : ℝ => V t x)
      = fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • P) x := by
    funext t; exact hPexp t x
  rw [hfun]
  have harg : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I) • P) :=
    (Complex.continuous_ofReal.mul continuous_const).smul continuous_const
  exact (NormedSpace.exp_continuous.comp harg).clm_apply continuous_const

/-- **Vacuum state (generator-parameterized scaffold).** A state `ω` on the
quasilocal algebra is a *vacuum state* (relative to the future-timelike-translation
predicate `ftl`) when:

1. it is invariant under the covariance action (`IsInvariantState`); and
2. in a GNS representation `(H, π, Ω)` reproducing `ω` and implementing the action
   by unitaries `U`, every future-timelike translation one-parameter subgroup `γ`
   has positive energy: `t ↦ U (γ t)` satisfies `IsPositiveEnergy`.

This packages the two *necessary* vacuum conditions — invariance and the spectrum
condition — with the spectrum condition entering as the positive-energy hypothesis
on the implementing unitaries. The future-timelike-translation predicate `ftl` is a
parameter (to be instantiated once the translation subgroup and its causal
structure are available); the positive-energy condition is the bounded-generator
scaffold of `IsPositiveEnergy`. -/
def CovariantQuasilocalAlgebra.IsVacuumState (C : CovariantQuasilocalAlgebra)
    (ftl : (ℝ → InhomogeneousLorentzGroup) → Prop)
    (ω : Physicslib4.GNS.State C.quasilocal.carrier) : Prop :=
  C.IsInvariantState ω ∧
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : C.quasilocal.carrier →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
      (U : InhomogeneousLorentzGroup → (K ≃ₗᵢ[ℂ] K)),
        (∀ a : C.quasilocal.carrier, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (L : InhomogeneousLorentzGroup) (a : C.quasilocal.carrier),
          U L (π a Ω) = π (C.action L a) Ω) ∧
        (∀ γ : ℝ → InhomogeneousLorentzGroup,
          IsOneParameterSubgroup γ → ftl γ → IsPositiveEnergy (fun t => U (γ t)))

/-- **A vacuum state is invariant.** Invariance is the first conjunct of the vacuum
conditions, so it is immediate - no spectrum condition / Stone's theorem needed. -/
theorem CovariantQuasilocalAlgebra.IsVacuumState.invariant
    {C : CovariantQuasilocalAlgebra}
    {ftl : (ℝ → InhomogeneousLorentzGroup) → Prop}
    {ω : Physicslib4.GNS.State C.quasilocal.carrier}
    (h : C.IsVacuumState ftl ω) : C.IsInvariantState ω :=
  h.1

/-- **A pure vacuum state yields an irreducible covariant representation.** Combining
invariance (`IsVacuumState.invariant`) with purity gives the irreducible, covariant GNS
representation of `IsInvariantState.exists_gns_irreducible_covariant`: a covariant GNS
triple with implementing unitaries `U(L)` (fixing `Ω`, with operator covariance) whose
representation is irreducible and generates all of `𝓑(H)`. This needs no spectrum
condition; it is the same no-Stone content, now packaged for a (pure) vacuum state. -/
theorem CovariantQuasilocalAlgebra.IsVacuumState.exists_gns_irreducible_covariant
    {C : CovariantQuasilocalAlgebra}
    {ftl : (ℝ → InhomogeneousLorentzGroup) → Prop}
    {ω : Physicslib4.GNS.State C.quasilocal.carrier}
    (h : C.IsVacuumState ftl ω) (hpure : Physicslib4.GNS.IsPure ω) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H)),
        Physicslib4.GNS.IsCyclicVector π Ω ∧
        (∀ a : C.quasilocal.carrier, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (L : InhomogeneousLorentzGroup) (a : C.quasilocal.carrier),
          U L (π a Ω) = π (C.action L a) Ω) ∧
        (∀ L : InhomogeneousLorentzGroup, U L Ω = Ω) ∧
        (∀ L L' : InhomogeneousLorentzGroup, U (L' * L) = (U L).trans (U L')) ∧
        U 1 = LinearIsometryEquiv.refl ℂ H ∧
        (∀ (L : InhomogeneousLorentzGroup) (a : C.quasilocal.carrier) (x : H),
          U L (π a ((U L).symm x)) = π (C.action L a) x) ∧
        Physicslib4.GNS.IsIrreducible π ∧
        Physicslib4.GNS.gnsVonNeumann π = Set.univ :=
  IsInvariantState.exists_gns_irreducible_covariant C h.invariant hpure

/-- **Vacuum state with the concrete spectrum condition.** Specializes
`IsVacuumState` to the concrete future-timelike-translation predicate
`IsFutureTimelikeTranslation`, so the spectrum condition is imposed on exactly the
one-parameter translation subgroups `t ↦ (id, t • n)` with `n` future-pointing
timelike. This discharges the abstract `ftl` parameter with its intended value, so a
concrete vacuum state no longer depends on a free predicate. -/
def CovariantQuasilocalAlgebra.IsVacuumStateConcrete (C : CovariantQuasilocalAlgebra)
    (ω : Physicslib4.GNS.State C.quasilocal.carrier) : Prop :=
  C.IsVacuumState IsFutureTimelikeTranslation ω

/-- A concrete vacuum state is invariant (unfolds to the parameterized form). -/
theorem CovariantQuasilocalAlgebra.IsVacuumStateConcrete.invariant
    {C : CovariantQuasilocalAlgebra}
    {ω : Physicslib4.GNS.State C.quasilocal.carrier}
    (h : C.IsVacuumStateConcrete ω) : C.IsInvariantState ω :=
  h.1

/-- A pure concrete vacuum state yields an irreducible covariant representation
(unfolds to the parameterized form). -/
theorem CovariantQuasilocalAlgebra.IsVacuumStateConcrete.exists_gns_irreducible_covariant
    {C : CovariantQuasilocalAlgebra}
    {ω : Physicslib4.GNS.State C.quasilocal.carrier}
    (h : C.IsVacuumStateConcrete ω) (hpure : Physicslib4.GNS.IsPure ω) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H)),
        Physicslib4.GNS.IsCyclicVector π Ω ∧
        (∀ a : C.quasilocal.carrier, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (L : InhomogeneousLorentzGroup) (a : C.quasilocal.carrier),
          U L (π a Ω) = π (C.action L a) Ω) ∧
        (∀ L : InhomogeneousLorentzGroup, U L Ω = Ω) ∧
        (∀ L L' : InhomogeneousLorentzGroup, U (L' * L) = (U L).trans (U L')) ∧
        U 1 = LinearIsometryEquiv.refl ℂ H ∧
        (∀ (L : InhomogeneousLorentzGroup) (a : C.quasilocal.carrier) (x : H),
          U L (π a ((U L).symm x)) = π (C.action L a) x) ∧
        Physicslib4.GNS.IsIrreducible π ∧
        Physicslib4.GNS.gnsVonNeumann π = Set.univ :=
  IsVacuumState.exists_gns_irreducible_covariant h hpure

end HaagKastler
end AQFT
end Physicslib4
