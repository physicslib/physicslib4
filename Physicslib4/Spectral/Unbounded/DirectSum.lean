/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Physicslib4.Spectral.Unbounded.Spectrum

/-!
# Hilbert space direct sums and componentwise self-adjoint operators

The blueprint's external Hilbert space direct sum `⨁ⱼ Hⱼ` is Mathlib's `lp G 2`, and the
internal notion — a family of pairwise orthogonal closed subspaces of `H` summing to `H`
— is recorded here as `IsInternalOrthogonalDecomposition`, identified with the external
one through Mathlib's `IsHilbertSum`.

The payoff is the pair of propositions saying that an operator acting componentwise by a
family of *bounded* self-adjoint operators, defined at least on the finite direct sum, is
essentially self-adjoint with closure given by the same componentwise formula on the
maximal domain.

## Main definitions

* `Physicslib4.Spectral.Unbounded.IsInternalOrthogonalDecomposition`
* `Physicslib4.Spectral.Unbounded.IsDirectSumOperator`,
  `Physicslib4.Spectral.Unbounded.directSumDomain` (external form)
* `Physicslib4.Spectral.Unbounded.IsInternalDirectSumOperator`,
  `Physicslib4.Spectral.Unbounded.internalDomain` (internal form)

## Main statements

* `dense_setOf_finite_support` — the finite direct sum is dense.
* `isHilbertSum_of_isInternalOrthogonalDecomposition` — an internal decomposition is
  unitarily the external direct sum of its summands.
* `isEssentiallySelfAdjoint_of_isDirectSumOperator` and companions — the external form of
  the blueprint's Proposition 9.26.
* `isEssentiallySelfAdjoint_of_isInternalDirectSumOperator` and companions — its internal
  form.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### The external Hilbert space direct sum

The blueprint's `⨁ⱼ Hⱼ` — square-summable sequences with the componentwise inner product
— is Mathlib's `lp G 2` together with `lp.instInnerProductSpace`.
-/

section External

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
variable [∀ i, InnerProductSpace ℂ (G i)]

/--
The finite direct sum — the elements of `⨁ᵢ Gᵢ` with only finitely many non-zero entries
— is dense. (That it is a subspace is immediate, a linear combination of two
finitely-supported families again being finitely supported.)

Blueprint reference: `lmm:finite-direct-sum-dense`.
-/
theorem dense_setOf_finite_support :
    Dense {f : lp G 2 | {i : ι | f i ≠ 0}.Finite} := by
  sorry

end External

/-!
### Internal orthogonal decompositions
-/

/--
A sequence `K` of closed subspaces of `H` is an *internal orthogonal decomposition* of
`H` if the subspaces are pairwise orthogonal and every vector of `H` is the sum of a
norm-convergent series with `n`-th term in `K n`.

Blueprint reference: `def:internal-orthogonal-decomposition`.
-/
structure IsInternalOrthogonalDecomposition (K : ℕ → Submodule ℂ H) : Prop where
  /-- Each summand is closed. -/
  isClosed : ∀ n, IsClosed ((K n : Set H))
  /-- The summands are pairwise orthogonal. -/
  orthogonal : ∀ {n m : ℕ}, n ≠ m → ∀ η ∈ K n, ∀ ζ ∈ K m, ⟪η, ζ⟫_ℂ = 0
  /-- Every vector decomposes as a norm-convergent series with terms in the summands. -/
  exists_hasSum : ∀ ψ : H, ∃ f : ∀ n, K n, HasSum (fun n => (f n : H)) ψ

/--
The decomposition of a vector along an internal orthogonal decomposition is unique.

Blueprint reference: `lmm:internal-decomposition-unitary` (Part 1).
-/
theorem hasSum_injective_of_isInternalOrthogonalDecomposition {K : ℕ → Submodule ℂ H}
    (h : IsInternalOrthogonalDecomposition K) {ψ : H} {f g : ∀ n, K n}
    (hf : HasSum (fun n => (f n : H)) ψ) (hg : HasSum (fun n => (g n : H)) ψ) : f = g := by
  sorry

/--
Pythagoras for an internal orthogonal decomposition: `‖ψ‖² = ∑ₙ ‖ψₙ‖²`.

Blueprint reference: `lmm:internal-decomposition-unitary` (Part 2).
-/
theorem hasSum_norm_sq_of_isInternalOrthogonalDecomposition {K : ℕ → Submodule ℂ H}
    (h : IsInternalOrthogonalDecomposition K) {ψ : H} {f : ∀ n, K n}
    (hf : HasSum (fun n => (f n : H)) ψ) :
    HasSum (fun n => ‖(f n : H)‖ ^ 2) (‖ψ‖ ^ 2) := by
  sorry

/--
An internal orthogonal decomposition exhibits `H` as the external direct sum of its
summands; the identifying map `ψ ↦ (ψ₁, ψ₂, …)` is unitary. In Lean this is Mathlib's
`IsHilbertSum` for the inclusions `(K n).subtypeₗᵢ`, and the unitary map is
`IsHilbertSum.linearIsometryEquiv`.

The `CompleteSpace` instance on each summand, which the blueprint derives from closedness
of `K n` inside the complete space `H`, is carried here as an instance argument because
the statement of `IsHilbertSum` needs it at elaboration time.

Blueprint reference: `lmm:internal-decomposition-unitary` (Part 3).
-/
theorem isHilbertSum_of_isInternalOrthogonalDecomposition {K : ℕ → Submodule ℂ H}
    [∀ n, CompleteSpace (K n)] (h : IsInternalOrthogonalDecomposition K) :
    IsHilbertSum ℂ (fun n => (K n : Type _)) (fun n => (K n).subtypeₗᵢ) := by
  sorry

/-!
### Componentwise self-adjoint operators, external form
-/

section DirectSumOperator

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
variable [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

/--
The maximal domain `V` for the componentwise operator determined by a family `A` of
bounded operators: the vectors whose components and images have square-summable norms.

Blueprint reference: `prpstn:hall-9.26`.
-/
def directSumDomain (A : ∀ i, G i →L[ℂ] G i) : Set (lp G 2) :=
  {ψ | Summable fun i => ‖ψ i‖ ^ 2 + ‖A i (ψ i)‖ ^ 2}

/--
`T` is *the componentwise operator determined by the family `A`*: it is symmetric, its
domain contains the finite direct sum, and it acts by `A` componentwise there.

Blueprint reference: `prpstn:hall-9.26`.
-/
structure IsDirectSumOperator (A : ∀ i, G i →L[ℂ] G i) (T : lp G 2 →ₗ.[ℂ] lp G 2) :
    Prop where
  /-- `T` is symmetric. -/
  isSymmetric : IsSymmetric T
  /-- The finite direct sum lies in `Dom(T)`. -/
  memDomain : ∀ f : lp G 2, {i : ι | f i ≠ 0}.Finite → f ∈ T.domain
  /-- On the finite direct sum, `T` acts componentwise by `A`. -/
  apply_eq : ∀ (f : lp G 2) (hf : {i : ι | f i ≠ 0}.Finite) (i : ι),
    (T ⟨f, memDomain f hf⟩) i = A i (f i)

variable {A : ∀ i, G i →L[ℂ] G i} {T : lp G 2 →ₗ.[ℂ] lp G 2}

/--
A componentwise operator built from bounded self-adjoint pieces is essentially
self-adjoint.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem isEssentiallySelfAdjoint_of_isDirectSumOperator (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) : IsEssentiallySelfAdjoint T := by
  sorry

/--
The domain of the closure is the maximal domain `V`.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem domain_closure_eq_directSumDomain (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) :
    (T.closure.domain : Set (lp G 2)) = directSumDomain A := by
  sorry

/--
The domain of the adjoint is the maximal domain `V`.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem domain_adjoint_eq_directSumDomain (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) :
    ((T†).domain : Set (lp G 2)) = directSumDomain A := by
  sorry

/--
On `V`, the closure acts componentwise by `A`.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem closure_apply_eq_of_isDirectSumOperator (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) (ψ : T.closure.domain) (i : ι) :
    (T.closure ψ) i = A i ((ψ : lp G 2) i) := by
  sorry

/--
On `V`, the adjoint acts componentwise by `A`.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem adjoint_apply_eq_of_isDirectSumOperator (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) (ψ : (T†).domain) (i : ι) :
    (T† ψ) i = A i ((ψ : lp G 2) i) := by
  sorry

end DirectSumOperator

/-!
### Componentwise self-adjoint operators, internal form
-/

section InternalDirectSumOperator

variable {K : ℕ → Submodule ℂ H} [∀ n, CompleteSpace (K n)]

/--
The maximal domain for the internal componentwise operator determined by a family `A` of
bounded operators on the summands.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
def internalDomain (K : ℕ → Submodule ℂ H) (A : ∀ n, (K n) →L[ℂ] (K n)) : Set H :=
  {ψ | ∃ f : ∀ n, K n, HasSum (fun n => (f n : H)) ψ ∧
    Summable fun n => ‖(f n : H)‖ ^ 2 + ‖(A n (f n) : H)‖ ^ 2}

/--
`T` is the internal componentwise operator determined by `A`: symmetric, defined at least
on the algebraic span `W₀` of the summands, and acting there by `A` summandwise.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
structure IsInternalDirectSumOperator (A : ∀ n, (K n) →L[ℂ] (K n))
    (T : H →ₗ.[ℂ] H) : Prop where
  /-- `T` is symmetric. -/
  isSymmetric : IsSymmetric T
  /-- Every finite sum of elements of the summands lies in `Dom(T)`. -/
  memDomain : ∀ (N : ℕ) (η : ∀ n, K n), (∑ n ∈ Finset.range N, (η n : H)) ∈ T.domain
  /-- On such a finite sum, `T` acts summandwise by `A`. -/
  apply_eq : ∀ (N : ℕ) (η : ∀ n, K n),
    T ⟨∑ n ∈ Finset.range N, (η n : H), memDomain N η⟩ =
      ∑ n ∈ Finset.range N, (A n (η n) : H)

variable {A : ∀ n, (K n) →L[ℂ] (K n)} {T : H →ₗ.[ℂ] H}

/--
The internal form of `prpstn:hall-9.26`: essential self-adjointness.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem isEssentiallySelfAdjoint_of_isInternalDirectSumOperator
    (hK : IsInternalOrthogonalDecomposition K) (hA : ∀ n, IsSelfAdjoint (A n))
    (hT : IsInternalDirectSumOperator A T) : IsEssentiallySelfAdjoint T := by
  sorry

/--
The domain of the closure is the maximal internal domain.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem domain_closure_eq_internalDomain (hK : IsInternalOrthogonalDecomposition K)
    (hA : ∀ n, IsSelfAdjoint (A n)) (hT : IsInternalDirectSumOperator A T) :
    (T.closure.domain : Set H) = internalDomain K A := by
  sorry

/--
The domain of the adjoint is the maximal internal domain.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem domain_adjoint_eq_internalDomain (hK : IsInternalOrthogonalDecomposition K)
    (hA : ∀ n, IsSelfAdjoint (A n)) (hT : IsInternalDirectSumOperator A T) :
    ((T†).domain : Set H) = internalDomain K A := by
  sorry

/--
On the maximal internal domain, the closure is given by the norm-convergent sum
`∑ₙ Aₙ ψₙ`.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem hasSum_closure_apply_of_isInternalDirectSumOperator
    (hK : IsInternalOrthogonalDecomposition K) (hA : ∀ n, IsSelfAdjoint (A n))
    (hT : IsInternalDirectSumOperator A T) (ψ : T.closure.domain) {f : ∀ n, K n}
    (hf : HasSum (fun n => (f n : H)) (ψ : H)) :
    HasSum (fun n => (A n (f n) : H)) (T.closure ψ) := by
  sorry

/--
The same formula for the adjoint.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem hasSum_adjoint_apply_of_isInternalDirectSumOperator
    (hK : IsInternalOrthogonalDecomposition K) (hA : ∀ n, IsSelfAdjoint (A n))
    (hT : IsInternalDirectSumOperator A T) (ψ : (T†).domain) {f : ∀ n, K n}
    (hf : HasSum (fun n => (f n : H)) (ψ : H)) :
    HasSum (fun n => (A n (f n) : H)) (T† ψ) := by
  sorry

end InternalDirectSumOperator

end Unbounded
end Spectral
end Physicslib4
