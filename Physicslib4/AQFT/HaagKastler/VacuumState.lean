/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.QuasilocalIntertwiner
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.InnerProductSpace.Positive

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
