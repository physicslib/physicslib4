/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Basic

/-!
# The null space of a state on a unital C*-algebra

This file formalises the statements of lemmas `lmm:lmm1` and `lmm:lmm2` from
section 9.1 of the AQFT-in-Lean blueprint.

Given a state `ω` on a unital C*-algebra `A`, the *null space* of `ω` is the
set
  `N(ω) := { n ∈ A : ω (n* n) = 0 }`,
and the *orthogonal set* is
  `N₁(ω) := { n ∈ A : ∀ b, ω (b* n) = 0 }`.

## Main statements

* `Physicslib4.GNS.nullSet`: the set `N(ω)`.
* `Physicslib4.GNS.orthSet`: the set `N₁(ω)`.
* `Physicslib4.GNS.lmm1`: `nullSet ω = orthSet ω` (blueprint `lmm:lmm1`).
* `Physicslib4.GNS.nullSubmodule`: the null space packaged as a
  `Submodule ℂ A` (carrier equal to `nullSet ω`), giving the
  linear-subspace content of `lmm:lmm2`.
* `Physicslib4.GNS.lmm2`: `nullSet ω` underlies a closed `Submodule ℂ A`
  (blueprint `lmm:lmm2`). The primary entry point is `lmm2`; the helper
  `nullSubmodule_isClosed` records closedness separately for convenience.

## Notes

The proofs are left as `sorry`. The linear-subspace data
(`add_mem'`, `zero_mem'`, `smul_mem'`) inside `nullSubmodule` are also
`sorry`s, since this file only formalises the *statements*.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

/--
The *null set* of a state `ω` on a unital C*-algebra `A`:
`N(ω) = { n ∈ A : ω (star n * n) = 0 }`.

Blueprint reference: the set `𝒩` in `lmm:lmm1` and `lmm:lmm2`.
-/
def nullSet (ω : State A) : Set A := { n | ω (star n * n) = 0 }

/--
The *orthogonal set* of a state `ω` on a unital C*-algebra `A`:
`N₁(ω) = { n ∈ A : ∀ b, ω (star b * n) = 0 }`.

Blueprint reference: the set `𝒩₁` in `lmm:lmm1`.
-/
def orthSet (ω : State A) : Set A := { n | ∀ b : A, ω (star b * n) = 0 }

/--
**Equality of the null set and the orthogonal set** (`lmm:lmm1`).

Let `ω` be a state over a unital C*-algebra `A`. Then
`nullSet ω = orthSet ω`, i.e.
`{ n : ω (n* n) = 0 } = { n : ∀ b, ω (b* n) = 0 }`.
-/
theorem lmm1 (ω : State A) : nullSet ω = orthSet ω := by
  sorry

/--
The null set of a state `ω`, packaged as a `Submodule ℂ A`.

The linear-subspace content of `lmm:lmm2`: the carrier equals `nullSet ω`,
and `nullSet ω` is closed under addition and under scalar multiplication
by complex numbers, and contains `0`.
-/
def nullSubmodule (ω : State A) : Submodule ℂ A where
  carrier := nullSet ω
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

@[simp]
lemma nullSubmodule_coe (ω : State A) : (nullSubmodule ω : Set A) = nullSet ω := rfl

/--
**The null space is a closed linear subspace** (`lmm:lmm2`, primary entry point).

Let `ω` be a state over a unital C*-algebra `A`. Then there exists a
`Submodule ℂ A` whose underlying set is `nullSet ω` and which is closed in
the topology of `A`. Concretely, `nullSubmodule ω` witnesses the
existential.
-/
theorem lmm2 (ω : State A) :
    ∃ S : Submodule ℂ A, (S : Set A) = nullSet ω ∧ IsClosed (S : Set A) := by
  sorry

/--
**Closedness of the null submodule** (`lmm:lmm2`, closedness part).

The underlying set of `nullSubmodule ω` is closed in `A`.
-/
theorem nullSubmodule_isClosed (ω : State A) :
    IsClosed (nullSubmodule ω : Set A) := by
  sorry

end GNS
end Physicslib4
