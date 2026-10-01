/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Reducing subspaces

A closed subspace `K` of a complex Hilbert space that is invariant under an operator `T` and
under its adjoint *reduces* `T`: the orthogonal projection onto `K` commutes with `T`.

Blueprint reference: `lmm:reducing-subspace-projection-commutes`.
-/

namespace Physicslib4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **A reducing subspace commutes with the operator.** If `T` and its adjoint both map the
subspace `K` into itself, then the orthogonal projection onto `K` commutes with `T`.

Blueprint reference: `lmm:reducing-subspace-projection-commutes`. -/
theorem commute_starProjection_of_invariant (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (T : E →L[ℂ] E) (hT : ∀ x ∈ K, T x ∈ K)
    (hT' : ∀ x ∈ K, ContinuousLinearMap.adjoint T x ∈ K) :
    Commute T K.starProjection := by
  have hperp : ∀ z ∈ Kᗮ, T z ∈ Kᗮ := fun z hz k hk => by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact hz _ (hT' k hk)
  refine ContinuousLinearMap.ext fun x => ?_
  have h1 := K.starProjection_apply_mem x
  have h2 := K.sub_starProjection_mem_orthogonal x
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  change T (K.starProjection x) = K.starProjection (T x)
  conv_rhs => rw [hx]
  rw [map_add, map_add, (K.starProjection_eq_self_iff).2 (hT _ h1),
    (K.starProjection_apply_eq_zero_iff).2 (hperp _ h2), add_zero]

end Physicslib4
