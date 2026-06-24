/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.StabilizerAction
import Physicslib4.AQFT.KMS
import Physicslib4.GNS.UnitaryRepresentation

/-!
# KMS states for a Killing flow in curved spacetime

This file connects the abstract KMS condition (`Physicslib4.AQFT.IsKMSState`) to
the curved-spacetime stabilizer action. A *Killing flow* fixing a region `B` is a
one-parameter subgroup `t ↦ φ_t` of the stabilizer `Stab(B) = {φ : φ·B = B}`. It
induces, via the stabilizer automorphism `stabAutHom`, a one-parameter group of
`*`-automorphisms of the single local algebra `𝔘(B)`, and one can then ask
whether a state on `𝔘(B)` is KMS for that flow.

This is the setting of the curved-spacetime thermal states discussed alongside
the stabilizer GNS unitary: the Hartle-Hawking state on a Schwarzschild exterior
(KMS for the stationary Killing flow at the Hawking temperature) and the
Bunch-Davies state restricted to a de Sitter static patch (KMS for the boost
Killing flow at the Gibbons-Hawking temperature).

## Main definitions / results

* `HaagKastlerNet.flowAut`: the one-parameter automorphism family of `𝔘(B)`
  induced by a flow into `Stab(B)`.
* `HaagKastlerNet.isOneParameterAut_flowAut`: if the flow is a one-parameter
  subgroup, the induced family is a one-parameter automorphism group.
* `HaagKastlerNet.IsKMSStateForFlow`: a state on `𝔘(B)` is a KMS state for the
  Killing flow.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

open scoped Pointwise InnerProductSpace

namespace HaagKastlerNet

variable {M : LorentzianSpacetime} (N : HaagKastlerNet M)

/-- The one-parameter automorphism family of the local algebra `𝔘(B)` induced by
a flow `t ↦ φ_t` into the stabilizer `Stab(B)`, via the stabilizer automorphism
`stabAutHom`. -/
noncomputable def flowAut (B : Set M.Carrier)
    (flow : ℝ → ↥(MulAction.stabilizer M.Isom B)) (t : ℝ) :
    N.algebra B ≃⋆ₐ[ℂ] N.algebra B :=
  N.stabAutHom B (flow t)

/-- **A Killing flow induces a one-parameter automorphism group.** If `flow` is a
one-parameter subgroup of `Stab(B)` (`flow 0 = 1`, `flow (s+t) = flow s * flow t`),
then the induced automorphisms of `𝔘(B)` form a one-parameter group. -/
theorem isOneParameterAut_flowAut (B : Set M.Carrier)
    (flow : ℝ → ↥(MulAction.stabilizer M.Isom B))
    (h0 : flow 0 = 1) (hadd : ∀ s t : ℝ, flow (s + t) = flow s * flow t) :
    AQFT.IsOneParameterAut (N.flowAut B flow) := by
  refine ⟨fun a => ?_, fun s t a => ?_⟩
  · change N.stabAutHom B (flow 0) a = a
    rw [h0]; exact N.stabAutHom_one B a
  · change N.stabAutHom B (flow (s + t)) a
        = N.stabAutHom B (flow s) (N.stabAutHom B (flow t) a)
    rw [hadd s t]; exact N.stabAutHom_mul B (flow t) (flow s) a

/-- A state `ω` on the local algebra `𝔘(B)` is a *KMS state for the Killing flow*
`flow` at inverse temperature `β` if it satisfies the KMS condition for the
induced one-parameter automorphism group `flowAut`. -/
def IsKMSStateForFlow (B : Set M.Carrier)
    (flow : ℝ → ↥(MulAction.stabilizer M.Isom B)) (β : ℝ)
    (ω : Physicslib4.GNS.State (N.algebra B)) : Prop :=
  AQFT.IsKMSState (N.flowAut B flow) β ω

/-- **The Killing-flow KMS thermal representation.** A KMS state `ω` on `𝔘(B)` for
a one-parameter Killing flow `t ↦ φ_t` into `Stab(B)`, at positive inverse
temperature `β`, yields a GNS triple `(H, π, Ω)` reproducing `ω` together with a
**strongly continuous** one-parameter unitary group `U : ℝ → (H ≃ₗᵢ[ℂ] H)`
implementing the flow:
`U t (π a Ω) = π (α_t a) Ω`, `U t Ω = Ω`, `U 0 = id`, `U (s+t) = U s ∘ U t`,
and `t ↦ U t ψ` is continuous for every `ψ`.

This is the curved-spacetime equilibrium (thermal) representation - the role played
by the vacuum representation in Minkowski spacetime - for states such as the
Hartle-Hawking and Gibbons-Hawking states. The hypotheses are: `flow` is a
one-parameter subgroup of `Stab(B)`, `0 < β`, the KMS condition, and weak
continuity of the matrix coefficients `t ↦ ω(a⋆ · α_t b)`. KMS at `β > 0` gives
`α`-invariance (`IsKMSState.invariant_of_pos`), which feeds the abstract
strongly-continuous GNS unitary construction. -/
theorem IsKMSStateForFlow.exists_gns_unitary_strongContinuous
    (B : Set M.Carrier) (flow : ℝ → ↥(MulAction.stabilizer M.Isom B))
    (h0 : flow 0 = 1) (hadd : ∀ s t : ℝ, flow (s + t) = flow s * flow t)
    {β : ℝ} (hβ : 0 < β) {ω : Physicslib4.GNS.State (N.algebra B)}
    (hkms : N.IsKMSStateForFlow B flow β ω)
    (hwc : ∀ a b : N.algebra B,
        Continuous fun t : ℝ => (ω (star a * N.flowAut B flow t b) : ℂ)) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : ℝ → (H ≃ₗᵢ[ℂ] H)),
        (∀ a : N.algebra B, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (t : ℝ) (a : N.algebra B), U t (π a Ω) = π (N.flowAut B flow t a) Ω) ∧
        (∀ t : ℝ, U t Ω = Ω) ∧
        (U 0 = LinearIsometryEquiv.refl ℂ H) ∧
        (∀ s t : ℝ, U (s + t) = (U t).trans (U s)) ∧
        (∀ ψ : H, Continuous fun t : ℝ => U t ψ) := by
  have hop : AQFT.IsOneParameterAut (N.flowAut B flow) :=
    N.isOneParameterAut_flowAut B flow h0 hadd
  obtain ⟨H, i1, i2, i3, π, Ω, U', hrepro, himpl, hfix, hmul', hone', hstrong, _hcov⟩ :=
    Physicslib4.GNS.exists_gns_unitary_of_invariant_strongContinuous
      (G := Multiplicative ℝ)
      (fun g => N.flowAut B flow (Multiplicative.toAdd g)) ω
      (fun g a => hkms.invariant_of_pos hop hβ a (Multiplicative.toAdd g))
      (fun g g' a => hop.2 (Multiplicative.toAdd g') (Multiplicative.toAdd g) a)
      (fun a => hop.1 a)
      (fun a b => hwc a b)
  refine ⟨H, i1, i2, i3, π, Ω, fun t => U' (Multiplicative.ofAdd t), hrepro,
    fun t a => himpl (Multiplicative.ofAdd t) a, fun t => hfix (Multiplicative.ofAdd t),
    hone', fun s t => ?_, fun ψ => hstrong ψ⟩
  exact hmul' (Multiplicative.ofAdd t) (Multiplicative.ofAdd s)

end HaagKastlerNet

end HaagKastlerCurved
end AQFT
end Physicslib4
