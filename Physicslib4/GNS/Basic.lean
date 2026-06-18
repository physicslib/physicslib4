/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Dual

/-!
# Basic definitions for the GNS construction

This file formalises some basic notions used in the GNS construction, following
the AQFT-in-Lean blueprint, section 10.1.

## Main definitions

* `Physicslib4.GNS.State`: a state on an abstract C*-algebra, defined as a
  continuous linear functional that is positive (sends `star a * a` to a
  non-negative complex number) and normalised (operator norm equal to `1`).
  This corresponds to the blueprint label `def:state`.
* `Physicslib4.GNS.State.IsFaithful`: faithfulness of a state, asserting that
  `ω (star a * a) = 0` only when `a = 0`. Also part of `def:state`.
* `Physicslib4.GNS.IsCyclicVector`: a vector `Ω` of a Hilbert space `H` is
  cyclic for a representation `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)` of an algebra `A`
  when the set `{ π a Ω : a ∈ A }` is dense in `H`.
  This corresponds to the blueprint label `def:cyclic-vector`.

## Notes

Mathlib does not yet provide a packaged `State` type for C*-algebras, so we
introduce one here. The positivity condition is stated using the canonical
partial order on `ℂ` from Mathlib: `0 ≤ z` iff `z.re ≥ 0` and `z.im = 0`.

The blueprint statement of `def:cyclic-vector` only requires `A` to be an
algebra; here we keep the assumptions general enough to be reusable but
require the operator-algebra side `H →L[ℂ] H` to make sense, so `H` is a
complex Hilbert space.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable (A : Type*) [CStarAlgebra A]

/--
A *state* on a unital C*-algebra `A` is a continuous linear functional
`A →L[ℂ] ℂ` that is positive (sends every element of the form
`star a * a` to a non-negative complex number) and normalised (operator
norm equal to `1`).

Blueprint reference: `def:state`.
-/
structure State extends A →L[ℂ] ℂ where
  /-- Positivity: `ω (a* a) ≥ 0` for every `a ∈ A`. -/
  isPositive : ∀ a : A, 0 ≤ toContinuousLinearMap (star a * a)
  /-- Normalisation: the operator norm of `ω` equals `1`. -/
  isNormalized : ‖toContinuousLinearMap‖ = 1

namespace State

variable {A}

noncomputable instance : FunLike (State A) A ℂ where
  coe ω := ω.toContinuousLinearMap
  coe_injective' := by
    intro ω₁ ω₂ h
    cases ω₁
    cases ω₂
    simp only [mk.injEq]
    exact DFunLike.coe_injective h

/--
A state `ω` on a C*-algebra `A` is *faithful* if `ω (star a * a) = 0`
implies `a = 0`. Equivalently, `a ≠ 0` implies `0 < ω (star a * a)`.

Blueprint reference: `def:state` (faithfulness clause).
-/
def IsFaithful (ω : State A) : Prop :=
  ∀ a : A, a ≠ 0 → 0 < ω (star a * a)

end State

variable {A}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
A vector `Ω : H` is *cyclic* for a representation
`π : A →⋆ₐ[ℂ] (H →L[ℂ] H)` of `A` on the Hilbert space `H` when
the set `{ π a Ω : a ∈ A }` is dense in `H`.

Blueprint reference: `def:cyclic-vector`.
-/
def IsCyclicVector (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) : Prop :=
  Dense (Set.range fun a : A => π a Ω)

end GNS
end Physicslib4
