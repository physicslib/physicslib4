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

Mathlib has no packaged `State` type for C*-algebras, so one is introduced
here. The positivity condition is stated using the canonical
partial order on `ℂ` from Mathlib: `0 ≤ z` iff `z.re ≥ 0` and `z.im = 0`.

The blueprint statement of `def:cyclic-vector` only requires `A` to be an
algebra, but `IsCyclicVector` is declared under this file's ambient
`variable (A : Type*) [CStarAlgebra A]`, so in Lean `A` is a unital C*-algebra
(matching every call site in the project). The generality kept here is on the
`H` side: `H` is required only to be a complex Hilbert space, not fixed to the
GNS space of a particular state.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable (A : Type*) [CStarAlgebra A]

/--
A state on a unital C*-algebra A: a positive, normalised continuous linear functional ω : A → ℂ.

The number ω(a) is the expectation value of the observable a in the state ω. Positivity asks
that ω(a* a) ≥ 0 for every a ∈ A, that is, ω(a* a) is real and non-negative. Normalisation asks
that the operator norm ‖ω‖ is 1; for a positive functional on a nonzero algebra the norm is
Re ω(1) (`norm_eq_re_apply_one_of_positive`), so this is the familiar ω(1) = 1. A density matrix
ρ gives the state a ↦ tr(ρa) of the algebra of bounded operators on a Hilbert space, but the
definition needs no Hilbert space: the GNS construction (`gns_construction`) produces one from ω.

Implementation note: the structure extends `A →L[ℂ] ℂ`, and a `FunLike` instance lets one write
`ω a`. Positivity uses Mathlib's partial order on ℂ (`ComplexOrder`), in which 0 ≤ z means that
z is real and non-negative.

Blueprint: def:state
-/
structure State extends A →L[ℂ] ℂ where
  /-- Positivity: ω(a* a) is real and non-negative for every a ∈ A. -/
  isPositive : ∀ a : A, 0 ≤ toContinuousLinearMap (star a * a)
  /-- Normalisation: the operator norm ‖ω‖ equals 1. -/
  isNormalized : ‖toContinuousLinearMap‖ = 1

namespace State

variable {A}

noncomputable instance : FunLike (State A) A ℂ where
  coe ω := ω.toContinuousLinearMap
  coe_injective := by
    intro ω₁ ω₂ h
    cases ω₁
    cases ω₂
    simp only [mk.injEq]
    exact DFunLike.coe_injective h

/--
A faithful state: ω(a* a) > 0 for every nonzero a ∈ A.

Since ω(a* a) ≥ 0 always, this says that ω(a* a) = 0 only for a = 0: no nonzero observable has
vanishing expectation of a* a. A faithful state has an injective GNS representation
(`gns_construction`), and its cyclic vector is separating (`separating_of_faithful`). On a
matrix algebra the Gibbs state a ↦ tr(e^(−βH) a)/Z is faithful, while a vector state
a ↦ ⟨ψ, aψ⟩ is not: it vanishes on a* a whenever a annihilates the unit vector ψ.

Blueprint: def:state
-/
def IsFaithful (ω : State A) : Prop :=
  ∀ a : A, a ≠ 0 → 0 < ω (star a * a)

/-- Repackaging of a state as a Mathlib `PositiveLinearMap`, using the canonical
spectral order on the C*-algebra `A`, so that Mathlib's GNS infrastructure applies. -/
noncomputable def toPositiveLinearMap (ω : State A) [PartialOrder A] [StarOrderedRing A] :
    A →ₚ[ℂ] ℂ where
  toFun := ω.toContinuousLinearMap
  map_add' := by intro x y; exact map_add ω.toContinuousLinearMap x y
  map_smul' := by intro c x; exact map_smul ω.toContinuousLinearMap c x
  monotone' := by
    intro a b hab
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hba
    have h_pos : 0 ≤ ω.toContinuousLinearMap (b - a) := by
      rw [hy]; exact ω.isPositive y
    have hsub : ω.toContinuousLinearMap (b - a)
        = ω.toContinuousLinearMap b - ω.toContinuousLinearMap a := by
      simp [map_sub]
    rw [hsub] at h_pos
    exact sub_nonneg.mp h_pos

end State

variable {A}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
A cyclic vector Ω for a representation π of A on H: the vectors π(a)Ω, a ∈ A, are dense in H.

Every vector of H is then a limit of vectors obtained by acting on Ω with the represented
algebra, as every state of a Fock space is obtained from the vacuum by acting with creation
operators. The GNS representation of a state always has a cyclic vector (`gns_construction`),
and a cyclic representation reproducing a state is determined by the state up to unitary
equivalence (`gns_unique`).

Implementation note: a representation is a unital *-homomorphism π : A →⋆ₐ[ℂ] (H →L[ℂ] H) into
the bounded operators on a complex Hilbert space H. The blueprint allows any algebra A; here A is
a unital C*-algebra, the case used throughout the project.

Blueprint: def:cyclic-vector
-/
def IsCyclicVector (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) : Prop :=
  Dense (Set.range fun a : A => π a Ω)

end GNS
end Physicslib4
