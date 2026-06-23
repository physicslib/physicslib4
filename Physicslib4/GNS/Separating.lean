/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Construction

/-!
# The GNS vector of a faithful state is separating

For a faithful state `ω` the cyclic GNS vector `Ω` is *separating* for the
representation: `π(a) Ω = 0` forces `a = 0`. The argument is the standard GNS
computation `‖π(a) Ω‖² = ⟪Ω, π(a⋆ a) Ω⟫ = ω(a⋆ a)`, so a null vector means
`ω(a⋆ a) = 0`, and faithfulness gives `a = 0`.

This is the companion to the injectivity clause of `gns_construction` and the
starting point for any modular (Tomita-Takesaki) development, where a cyclic and
separating vector is the basic datum.

## Main results

* `Physicslib4.GNS.separating_of_faithful`: in any representation reproducing a
  faithful state, the cyclic vector is separating; in particular the GNS vector
  of a faithful state is separating.
-/

namespace Physicslib4
namespace GNS

open scoped InnerProductSpace ComplexOrder

variable {A : Type*} [CStarAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A faithful state's GNS vector is separating.** If `π` is a `*`-representation
and `Ω` a vector reproducing a faithful state `ω` (i.e. `ω a = ⟪Ω, π a Ω⟫`), then
`π(a) Ω = 0` implies `a = 0`. -/
theorem separating_of_faithful {ω : State A} (hω : ω.IsFaithful)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {a : A} (ha : π a Ω = 0) : a = 0 := by
  by_contra hne
  have hpos : 0 < ω (star a * a) := hω a hne
  have hzero : ω (star a * a) = 0 := by
    rw [hrep (star a * a), map_mul, map_star]
    simp [ContinuousLinearMap.mul_apply, ha]
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

end GNS
end Physicslib4
