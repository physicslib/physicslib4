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
  The future-timelike-translation predicate `ftl` is a parameter, to be supplied
  once the translation subgroup of the Lorentz group and its causal structure are
  wired in.

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

end HaagKastler
end AQFT
end Physicslib4
