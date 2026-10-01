/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Physicslib4.Operators.ReducingSubspace
import Physicslib4.Operators.LpDiagonal

/-!
# The von Neumann density theorem

For a unital `*`-algebra homomorphism `ρ : 𝔄 →⋆ₐ[ℂ] (E →L[ℂ] E)` on a complex Hilbert space `E`,
every element of the bicommutant `ρ(𝔄)''` is a strong limit of elements of `ρ(𝔄)`. This file
proves the one-vector case: for `T ∈ ρ(𝔄)''` and `ξ ∈ E`, `T ξ` lies in the closure of
`ρ(𝔄) ξ`. The commutant is `Set.centralizer`, as in
`Physicslib4/AQFT/HaagKastler/LocalVonNeumann.lean`.

Blueprint reference: `lmm:cyclic-subspace-reduces`, `lmm:bicommutant-single-vector`.
-/

namespace Physicslib4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {𝔄 : Type*} [Ring 𝔄] [StarRing 𝔄] [Algebra ℂ 𝔄]

/-- **The cyclic subspace of a vector reduces the representation.** The orthogonal projection onto
the closed subspace `closure (ρ(𝔄) ξ)` commutes with every `ρ a`.

Blueprint reference: `lmm:cyclic-subspace-reduces`. -/
theorem starProjection_cyclic_mem_centralizer (ρ : 𝔄 →⋆ₐ[ℂ] (E →L[ℂ] E)) (ξ : E) :
    (Submodule.span ℂ (Set.range fun a ↦ ρ a ξ)).topologicalClosure.starProjection ∈
      Set.centralizer (Set.range ρ) := by
  set S := Submodule.span ℂ (Set.range fun a ↦ ρ a ξ)
  have inv : ∀ a, ∀ x ∈ S.topologicalClosure, ρ a x ∈ S.topologicalClosure := by
    intro a
    have hS : S ≤ S.topologicalClosure.comap (ρ a).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact S.le_topologicalClosure (Submodule.subset_span ⟨a * b, by simp⟩)
    exact Submodule.topologicalClosure_minimal _ hS
      (S.isClosed_topologicalClosure.preimage (ρ a).continuous)
  rintro _ ⟨a, rfl⟩
  refine (commute_starProjection_of_invariant _ (ρ a) (inv a) ?_).eq
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  exact inv (star a)

/-- **The bicommutant moves a vector within its cyclic subspace.** For `T ∈ ρ(𝔄)''` and `ξ ∈ E`,
`T ξ` lies in the closure of `ρ(𝔄) ξ`; unitality of `ρ` puts `ξ` itself in that closure.

Blueprint reference: `lmm:bicommutant-single-vector`. -/
theorem apply_mem_closure_of_mem_bicommutant (ρ : 𝔄 →⋆ₐ[ℂ] (E →L[ℂ] E)) {T : E →L[ℂ] E}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range ρ))) (ξ : E) :
    T ξ ∈ closure (Set.range fun a ↦ ρ a ξ) := by
  set K := (Submodule.span ℂ (Set.range fun a ↦ ρ a ξ)).topologicalClosure
  have hP := starProjection_cyclic_mem_centralizer ρ ξ
  have hcomm : K.starProjection * T = T * K.starProjection :=
    Set.mem_centralizer_iff.mp hT _ hP
  have hξ : ξ ∈ K := Submodule.le_topologicalClosure _ <| Submodule.subset_span ⟨1, by simp⟩
  have hTξ : T ξ ∈ K := by
    rw [← (Submodule.starProjection_eq_self_iff).mpr hξ]
    rw [← (show K.starProjection (T ξ) = T (K.starProjection ξ) from congrArg (· ξ) hcomm)]
    exact Submodule.starProjection_apply_mem _ _
  let L : 𝔄 →ₗ[ℂ] E := (ContinuousLinearMap.apply ℂ E ξ).toLinearMap ∘ₗ ρ.toAlgHom.toLinearMap
  have hrange : (Set.range fun a ↦ ρ a ξ) = (LinearMap.range L : Set E) := by
    rw [LinearMap.coe_range]; rfl
  have hK : (K : Set E) = closure (Set.range fun a ↦ ρ a ξ) := by
    rw [Submodule.topologicalClosure_coe, hrange, Submodule.span_eq]
  rw [← hK]
  exact hTξ

/-! ### The amplification of a representation

For an index type `ι`, the amplification `ρ^ι` acts on `ℓ²(ι; E)` by the diagonal operator
`diag(ρ a, ρ a, …)`. Every copy is bounded by `‖ρ a‖`, so no norm on `𝔄` is needed (unlike
`Physicslib4.GNS.directSum`, which bounds different representations through a C*-norm). Finite
index types are used for the density theorem. -/

section Amplification

variable (ι : Type*)

omit [CompleteSpace E] in
/-- The **diagonal operator** `diag(T, T, …)` on `ℓ²(ι; E)`.

Blueprint reference: `def:finite-amplification`. -/
noncomputable def ampDiag (T : E →L[ℂ] E) : lp (fun _ : ι ↦ E) 2 →L[ℂ] lp (fun _ : ι ↦ E) 2 :=
  lpDiag (fun _ ↦ T) (norm_nonneg T) (fun _ ↦ le_rfl)

omit [CompleteSpace E] in
@[simp] theorem ampDiag_apply_coe (T : E →L[ℂ] E) (x : lp (fun _ : ι ↦ E) 2) (i : ι) :
    (ampDiag ι T x) i = T (x i) := rfl

/-- The **amplification** `ρ^ι` of a unital `*`-representation `ρ` on `ℓ²(ι; E)`:
`ρ^ι(a) = diag(ρ a, ρ a, …)`.

Blueprint reference: `def:finite-amplification`, `lmm:finite-amplification-star-hom`. -/
noncomputable def diagAmplification (ρ : 𝔄 →⋆ₐ[ℂ] (E →L[ℂ] E)) :
    𝔄 →⋆ₐ[ℂ] (lp (fun _ : ι ↦ E) 2 →L[ℂ] lp (fun _ : ι ↦ E) 2) where
  toFun a := ampDiag ι (ρ a)
  map_one' := by refine lpDiag_ext fun x i => ?_; simp [ampDiag, map_one]
  map_mul' a b := by
    refine lpDiag_ext fun x i => ?_; simp [ampDiag, map_mul, mul_apply_eq_comp]
  map_zero' := by
    refine lpDiag_ext fun x i => ?_
    change ρ 0 (x i) = (0 : lp (fun _ : ι ↦ E) 2) i
    rw [map_zero]; rfl
  map_add' a b := by
    refine lpDiag_ext fun x i => ?_
    change ρ (a + b) (x i) = ρ a (x i) + ρ b (x i)
    rw [map_add ρ a b]; rfl
  commutes' r := by
    refine lpDiag_ext fun x i => ?_
    simp [ampDiag, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, lp.coeFn_smul]
  map_star' a := by
    simp only [ampDiag]
    rw [lpDiag_star]
    refine lpDiag_ext fun x i => ?_
    change ρ (star a) (x i) = star (ρ a) (x i)
    rw [map_star ρ a]

@[simp] theorem diagAmplification_apply (ρ : 𝔄 →⋆ₐ[ℂ] (E →L[ℂ] E)) (a : 𝔄) :
    diagAmplification ι ρ a = ampDiag ι (ρ a) := rfl

variable {ι} [Finite ι]

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- A finite family of vectors as an element of `ℓ²(ι; E)`. -/
noncomputable def toLp2 (ξ : ι → E) : lp (fun _ : ι ↦ E) 2 := ⟨ξ, Memℓp.all ξ⟩

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
@[simp] theorem toLp2_apply (ξ : ι → E) (i : ι) : toLp2 ξ i = ξ i := rfl

end Amplification

end Physicslib4
