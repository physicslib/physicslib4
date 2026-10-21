/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Basic

/-!
# The null space of a state on a unital C*-algebra

This file formalises the statements of lemmas `lmm:lmm1` and `lmm:lmm2` from
section 10.1 of the AQFT-in-Lean blueprint.

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
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

/--
The null set N(ω) = { n ∈ A : ω(n* n) = 0 } of a state ω.

The GNS construction starts from the form ⟨a, b⟩ = ω(a* b) on A. It is positive semi-definite but
not an inner product when ω is not faithful, because ⟨n, n⟩ = 0 for every n ∈ N(ω). The set N(ω)
equals { n : ω(b* n) = 0 for all b } (`lmm1`), so it is a closed linear subspace (`lmm2`), and
the form descends to a genuine inner product on A/N(ω). The GNS Hilbert space is the completion
of A/N(ω). (The blueprint also uses that N(ω) is a left ideal, so that π(a)[b] = [ab] is well
defined; the library does not state this.) A faithful state has N(ω) = {0}.

Implementation note: `gns_construction` builds the GNS space with Mathlib's
`PositiveLinearMap.GNS`, the completion of A with the seminorm a ↦ ω(a* a)^(1/2); the quotient by
N(ω) happens inside that completion, so this file records the blueprint's lemmas about N(ω) and
is not used by the construction.

Blueprint: the set 𝒩 of lmm:lmm1 and lmm:lmm2
-/
def nullSet (ω : State A) : Set A := { n | ω (star n * n) = 0 }

/--
The set N₁(ω) = { n ∈ A : ω(b* n) = 0 for all b ∈ A } of a state ω.

These are the elements orthogonal to all of A for the form ⟨b, n⟩ = ω(b* n). By the
Cauchy–Schwarz inequality |ω(b* n)|² ≤ ω(b* b) ω(n* n), the set equals the null set N(ω)
(`lmm1`).

Blueprint: the set 𝒩₁ of lmm:lmm1
-/
def orthSet (ω : State A) : Set A := { n | ∀ b : A, ω (star b * n) = 0 }

/--
**Equality of the null set and the orthogonal set** (`lmm:lmm1`).

Let `ω` be a state over a unital C*-algebra `A`. Then
`nullSet ω = orthSet ω`, i.e.
`{ n : ω (n* n) = 0 } = { n : ∀ b, ω (b* n) = 0 }`.
-/
theorem lmm1 (ω : State A) : nullSet ω = orthSet ω := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  haveI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set f : A →ₚ[ℂ] ℂ := ω.toPositiveLinearMap with hf
  have hf_apply : ∀ a, f a = ω a := fun a => rfl
  apply Set.eq_of_subset_of_subset
  · -- nullSet ⊆ orthSet : Cauchy-Schwarz
    intro n hn b
    have CS := inner_mul_inner_self_le (𝕜 := ℂ)
      (f.toPreGNS b) (f.toPreGNS n)
    simp only [PositiveLinearMap.preGNS_inner_def,
               PositiveLinearMap.ofPreGNS_toPreGNS] at CS
    have hnn : f (star n * n) = 0 := hn
    rw [hnn] at CS
    simp only [map_zero, mul_zero] at CS
    have h_nonneg : 0 ≤ ‖f (star b * n)‖ * ‖f (star n * b)‖ := by positivity
    have h_eq : ‖f (star b * n)‖ * ‖f (star n * b)‖ = 0 := le_antisymm CS h_nonneg
    have h_norm_eq : ‖f (star b * n)‖ = ‖f (star n * b)‖ := by
      have hs := norm_inner_symm (𝕜 := ℂ) (f.toPreGNS b) (f.toPreGNS n)
      simp only [PositiveLinearMap.preGNS_inner_def,
                 PositiveLinearMap.ofPreGNS_toPreGNS] at hs
      exact hs
    rw [h_norm_eq] at h_eq
    have h_sq : ‖f (star n * b)‖ * ‖f (star n * b)‖ = 0 := h_eq
    have h_zero : ‖f (star n * b)‖ = 0 := by
      rcases mul_eq_zero.mp h_sq with h | h <;> exact h
    rw [← h_norm_eq] at h_zero
    exact norm_eq_zero.mp h_zero
  · -- orthSet ⊆ nullSet : take b = n
    intro n hn
    exact hn n

/--
The null set N(ω) of a state ω as a complex linear subspace of A.

Closure under sums and scalar multiples follows from N(ω) = N₁(ω) (`lmm1`), since N₁(ω) is
plainly linear. The subspace is closed (`nullSubmodule_isClosed`), so the quotient A/N(ω) is a
normed space.

Implementation note: the carrier is `nullSet ω` by definition (`nullSubmodule_coe`).

Blueprint: the subspace 𝒩 of lmm:lmm2
-/
def nullSubmodule (ω : State A) : Submodule ℂ A where
  carrier := nullSet ω
  add_mem' := by
    intro n m hn hm
    have h1 := lmm1 ω
    have hn' : n ∈ orthSet ω := h1 ▸ hn
    have hm' : m ∈ orthSet ω := h1 ▸ hm
    suffices h : n + m ∈ orthSet ω by
      rw [← h1] at h; exact h
    intro b
    have hadd : ω (star b * (n + m))
         = ω (star b * n) + ω (star b * m) := by
      rw [mul_add]
      exact map_add ω.toContinuousLinearMap (star b * n) (star b * m)
    rw [hadd, hn' b, hm' b]; ring
  zero_mem' := by
    change ω (star 0 * 0) = 0
    rw [star_zero, zero_mul]
    exact map_zero ω.toContinuousLinearMap
  smul_mem' := by
    intro c n hn
    have h1 := lmm1 ω
    have hn' : n ∈ orthSet ω := h1 ▸ hn
    suffices h : c • n ∈ orthSet ω by
      rw [← h1] at h; exact h
    intro b
    have hsmul : ω (star b * (c • n))
         = c * ω (star b * n) := by
      rw [Algebra.mul_smul_comm]
      exact map_smul ω.toContinuousLinearMap c (star b * n)
    rw [hsmul, hn' b]; ring

@[simp]
lemma nullSubmodule_coe (ω : State A) : (nullSubmodule ω : Set A) = nullSet ω := rfl

/--
**Closedness of the null submodule** (`lmm:lmm2`, closedness part).

The underlying set of `nullSubmodule ω` is closed in `A`.
-/
theorem nullSubmodule_isClosed (ω : State A) :
    IsClosed (nullSubmodule ω : Set A) := by
  rw [nullSubmodule_coe]
  have heq : nullSet ω = (fun x => ω (star x * x)) ⁻¹' {0} := by
    ext x
    simp [nullSet]
  rw [heq]
  apply IsClosed.preimage
  · have h1 : Continuous (fun x : A => star x * x) :=
      continuous_star.mul continuous_id
    exact (ω.toContinuousLinearMap.continuous).comp h1
  · exact isClosed_singleton

/--
**The null space is a closed linear subspace** (`lmm:lmm2`, primary entry point).

Let `ω` be a state over a unital C*-algebra `A`. Then there exists a
`Submodule ℂ A` whose underlying set is `nullSet ω` and which is closed in
the topology of `A`. Concretely, `nullSubmodule ω` witnesses the
existential.
-/
theorem lmm2 (ω : State A) :
    ∃ S : Submodule ℂ A, (S : Set A) = nullSet ω ∧ IsClosed (S : Set A) :=
  ⟨nullSubmodule ω, nullSubmodule_coe ω, nullSubmodule_isClosed ω⟩

end GNS
end Physicslib4
