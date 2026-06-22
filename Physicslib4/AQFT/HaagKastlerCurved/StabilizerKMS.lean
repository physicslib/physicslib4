/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.StabilizerAction
import Physicslib4.AQFT.KMS

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

open scoped Pointwise

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

end HaagKastlerNet

end HaagKastlerCurved
end AQFT
end Physicslib4
