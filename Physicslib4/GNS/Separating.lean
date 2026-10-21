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
  faithful state, the cyclic vector is separating.
* `Physicslib4.GNS.exists_gns_separating`: the GNS specialization.
-/

namespace Physicslib4
namespace GNS

open scoped InnerProductSpace ComplexOrder

variable {A : Type*} [CStarAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
A vector reproducing a faithful state is separating: π(a)Ω = 0 forces a = 0.

Let π be a representation of A on H and Ω a vector with ω(a) = ⟨Ω, π(a)Ω⟩ for a faithful state
ω. If π(a)Ω = 0 then ω(a* a) = ‖π(a)Ω‖² = 0, and faithfulness gives a = 0. So distinct
observables act differently on Ω. A vector that is both cyclic and separating is the starting
datum of Tomita–Takesaki modular theory; in quantum field theory the Reeh–Schlieder theorem gives
the vacuum this property for the algebras of bounded regions.

Implementation note: "separating" is stated for the elements of A (π(a)Ω = 0 implies a = 0), not
for the generated von Neumann algebra π(A)''. The result holds in any representation reproducing
ω, not only the GNS one.

Blueprint: thrm:separating-faithful
-/
theorem separating_of_faithful {ω : State A} (hω : ω.IsFaithful)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {a : A} (ha : π a Ω = 0) : a = 0 := by
  by_contra hne
  have hpos : 0 < ω (star a * a) := hω a hne
  have hzero : ω (star a * a) = 0 := by
    rw [hrep (star a * a), map_mul, map_star]
    simp [mul_apply_eq_comp, ha]
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/--
The GNS vector of a faithful state is cyclic and separating.

For a faithful state ω there is a representation (H, π, Ω) of A with Ω cyclic,
ω(a) = ⟨Ω, π(a)Ω⟩ for all a, and π(a)Ω = 0 only for a = 0. It is the GNS triple of
`gns_construction` together with `separating_of_faithful`.

Implementation note: as in `gns_construction`, H lives in the universe of A.

Blueprint: thrm:separating-faithful
-/
theorem exists_gns_separating.{u} {A : Type u} [CStarAlgebra A]
    (ω : State A) (hω : ω.IsFaithful) :
    ∃ (H : Type u)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ a : A, π a Ω = 0 → a = 0) := by
  obtain ⟨H, i1, i2, i3, π, Ω, hcyc, hrep, _⟩ := gns_construction ω
  exact ⟨H, i1, i2, i3, π, Ω, hcyc, hrep,
    fun a ha => separating_of_faithful hω π Ω hrep ha⟩

end GNS
end Physicslib4
