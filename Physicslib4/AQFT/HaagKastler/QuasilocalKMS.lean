/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.QuasilocalIntertwiner
import Physicslib4.AQFT.KMS
import Physicslib4.AQFT.PositiveEnergy

/-!
# KMS states for the covariance action in Minkowski spacetime

This file connects the abstract KMS condition (`Physicslib4.AQFT.IsKMSState`) to
the Minkowski covariance action on the quasilocal algebra. A one-parameter
subgroup `t ↦ L_t` of the inhomogeneous Lorentz group - for instance the
time-translation subgroup whose modular/Hamiltonian flow defines time evolution -
induces, via the quasilocal lift `β_L`, a one-parameter group of
`*`-automorphisms of the global quasilocal algebra `𝔘`. One can then ask whether
a state on `𝔘` is KMS for that flow.

Unlike the curved-spacetime case, where the absence of a global quasilocal
algebra forces a restriction to the stabilizer subgroup `Stab(B)`, here the lift
`β_L` is a genuine automorphism of the single global algebra `𝔘` for *every*
`L`, so no stabilizer restriction is needed.

## Main definitions / results

* `HaagKastlerNet.flowAut`: the one-parameter automorphism family of
  `𝔘` induced by a one-parameter subgroup of the inhomogeneous Lorentz group.
* `HaagKastlerNet.isOneParameterAut_flowAut`: a one-parameter
  subgroup induces a one-parameter automorphism group.
* `HaagKastlerNet.IsKMSStateForFlow`: a state on `𝔘` is a KMS state
  for the covariance flow.
* `HaagKastlerNet.IsKMSStateForFlow.convexCombo`: the KMS state set
  for the covariance flow is convex.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

namespace HaagKastlerNet

variable (N : HaagKastlerNet)

/-- The one-parameter automorphism family of the quasilocal algebra `𝔘` induced by
a one-parameter subgroup `t ↦ L_t` of the inhomogeneous Lorentz group, via the
covariance action `β_L`. -/
noncomputable def flowAut (flow : ℝ → InhomogeneousLorentzGroup) (t : ℝ) :
    N.quasilocal.carrier ≃⋆ₐ[ℂ] N.quasilocal.carrier :=
  N.action (flow t)

/-- **A one-parameter subgroup of the Lorentz group induces a one-parameter
automorphism group.** If `flow` is a one-parameter subgroup (`flow 0 = 1`,
`flow (s+t) = flow s * flow t`), then the induced automorphisms of `𝔘` form a
one-parameter group. -/
theorem isOneParameterAut_flowAut (flow : ℝ → InhomogeneousLorentzGroup)
    (h0 : flow 0 = 1) (hadd : ∀ s t : ℝ, flow (s + t) = flow s * flow t) :
    AQFT.IsOneParameterAut (N.flowAut flow) := by
  refine ⟨fun a => ?_, fun s t a => ?_⟩
  · change N.action (flow 0) a = a
    rw [h0]; exact N.action_one_apply a
  · change N.action (flow (s + t)) a = N.action (flow s) (N.action (flow t) a)
    rw [hadd s t]; exact N.action_mul_apply (flow t) (flow s) a

/-- A state `ω` on the quasilocal algebra `𝔘` is a *KMS state for the covariance
flow* `flow` at inverse temperature `β` if it satisfies the KMS condition for the
induced one-parameter automorphism group `flowAut`. -/
def IsKMSStateForFlow (flow : ℝ → InhomogeneousLorentzGroup) (β : ℝ)
    (ω : Physicslib4.GNS.State N.quasilocal.carrier) : Prop :=
  AQFT.IsKMSState (N.flowAut flow) β ω

/-- **The covariance-flow KMS state set is convex.** A convex combination
`s·ω₁ + (1-s)·ω₂` (`0 ≤ s ≤ 1`) of two KMS states on `𝔘` for the same covariance
flow at the same inverse temperature `β` is again a KMS state for that flow. This
specializes the abstract KMS convexity (`AQFT.IsKMSState.convexCombo`) to the
induced one-parameter group `flowAut`. Physically the equilibrium states for a
one-parameter symmetry flow form a convex set. -/
theorem IsKMSStateForFlow.convexCombo (flow : ℝ → InhomogeneousLorentzGroup)
    {β : ℝ} {ω₁ ω₂ : Physicslib4.GNS.State N.quasilocal.carrier}
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h₁ : N.IsKMSStateForFlow flow β ω₁) (h₂ : N.IsKMSStateForFlow flow β ω₂) :
    N.IsKMSStateForFlow flow β (ω₁.convexCombo ω₂ s hs0 hs1) :=
  AQFT.IsKMSState.convexCombo s hs0 hs1 h₁ h₂

open scoped InnerProductSpace in
/-- **Ground state for a covariance flow (bounded-generator scaffold).** A state `ω` on
the quasilocal algebra `𝔘` is a *ground state* for a one-parameter subgroup `t ↦ L_t` of
the inhomogeneous Lorentz group (e.g. a translation or boost flow) when it is invariant
under the flow and, in a GNS representation `(K, π, Ω)` reproducing `ω` and implementing
the flow by unitaries `U` fixing `Ω`, the one-parameter unitary group `t ↦ U t` has
positive energy (`AQFT.IsPositiveEnergy`). This is the ground-state (`β → ∞`,
spectrum-condition) counterpart of `IsKMSStateForFlow`: the stationary state whose flow
generator (the Hamiltonian, for a timelike flow) is positive. The positive-energy
condition is the bounded-generator scaffold; the faithful unbounded form is Stone-gated. -/
def IsGroundStateForFlow (flow : ℝ → InhomogeneousLorentzGroup)
    (ω : Physicslib4.GNS.State N.quasilocal.carrier) : Prop :=
  (∀ (t : ℝ) (a : N.quasilocal.carrier), (ω (N.flowAut flow t a) : ℂ) = ω a) ∧
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : N.quasilocal.carrier →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
      (U : ℝ → (K ≃ₗᵢ[ℂ] K)),
        (∀ a : N.quasilocal.carrier, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (t : ℝ) (a : N.quasilocal.carrier), U t (π a Ω) = π (N.flowAut flow t a) Ω) ∧
        (∀ t : ℝ, U t Ω = Ω) ∧
        AQFT.IsPositiveEnergy U

/-- A covariance-flow ground state is invariant under the flow (the first conjunct); no
spectrum condition or Stone's theorem is needed. -/
theorem IsGroundStateForFlow.invariant (flow : ℝ → InhomogeneousLorentzGroup)
    {ω : Physicslib4.GNS.State N.quasilocal.carrier}
    (h : N.IsGroundStateForFlow flow ω) :
    ∀ (t : ℝ) (a : N.quasilocal.carrier), (ω (N.flowAut flow t a) : ℂ) = ω a :=
  h.1

open scoped InnerProductSpace in
/-- The implementing unitary group of a covariance-flow ground state is strongly
continuous, since it has positive energy (`AQFT.IsPositiveEnergy.strongContinuous`). This
needs no spectrum condition. -/
theorem IsGroundStateForFlow.exists_strongContinuous_unitary
    (flow : ℝ → InhomogeneousLorentzGroup)
    {ω : Physicslib4.GNS.State N.quasilocal.carrier}
    (h : N.IsGroundStateForFlow flow ω) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : N.quasilocal.carrier →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
      (U : ℝ → (K ≃ₗᵢ[ℂ] K)),
        (∀ a : N.quasilocal.carrier, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (t : ℝ) (a : N.quasilocal.carrier), U t (π a Ω) = π (N.flowAut flow t a) Ω) ∧
        (∀ t : ℝ, U t Ω = Ω) ∧
        ∀ ψ : K, Continuous fun t : ℝ => U t ψ := by
  obtain ⟨_, K, _, _, _, π, Ω, U, hrep, himpl, hfix, hpe⟩ := h
  exact ⟨K, ‹_›, ‹_›, ‹_›, π, Ω, U, hrep, himpl, hfix, fun ψ => hpe.strongContinuous ψ⟩

end HaagKastlerNet

end HaagKastler
end AQFT
end Physicslib4
