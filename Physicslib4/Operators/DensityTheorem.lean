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
proves the ingredients: the one-vector case (for `T ∈ ρ(𝔄)''` and `ξ ∈ E`, `T ξ` lies in the
closure of `ρ(𝔄) ξ`), the diagonal amplification `ρ^ι` on `ℓ²(ι; E)`, and the fact that
`diag(T) ∈ (ρ^ι(𝔄))''` for a finite index type `ι`. The commutant is `Set.centralizer`, as in
`Physicslib4/AQFT/HaagKastler/LocalVonNeumann.lean`.

Blueprint reference: `lmm:cyclic-subspace-reduces`, `lmm:bicommutant-single-vector`,
`def:finite-amplification`, `lmm:commutant-of-amplification-entries`,
`lmm:amplification-block-expansion`, `lmm:diagonal-in-amplified-bicommutant`.
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

/-! ### Block entries and the diagonal of the bicommutant -/

section Blocks

variable {ι : Type*} [DecidableEq ι]

omit [CompleteSpace E] in
/-- The **block entry** `S_{jk} = (coordinate j) ∘ S ∘ (inclusion k)` of an operator on
`ℓ²(ι; E)`.

Blueprint reference: `lmm:commutant-of-amplification-entries`. -/
noncomputable def blockEntry (S : lp (fun _ : ι ↦ E) 2 →L[ℂ] lp (fun _ : ι ↦ E) 2) (j k : ι) :
    E →L[ℂ] E :=
  lp.evalCLM ℂ (fun _ : ι ↦ E) 2 j ∘L S ∘L lp.singleContinuousLinearMap ℂ (fun _ : ι ↦ E) 2 k

omit [CompleteSpace E] in
theorem blockEntry_apply (S : lp (fun _ : ι ↦ E) 2 →L[ℂ] lp (fun _ : ι ↦ E) 2) (j k : ι)
    (v : E) : blockEntry S j k v = S (lp.single 2 k v) j := rfl

/-- **The block entries of an operator commuting with the amplification commute with `ρ`.**

Blueprint reference: `lmm:commutant-of-amplification-entries`. -/
theorem blockEntry_mem_centralizer (ρ : 𝔄 →⋆ₐ[ℂ] (E →L[ℂ] E))
    {S : lp (fun _ : ι ↦ E) 2 →L[ℂ] lp (fun _ : ι ↦ E) 2}
    (hS : S ∈ Set.centralizer (Set.range (diagAmplification ι ρ))) (j k : ι) :
    blockEntry S j k ∈ Set.centralizer (Set.range ρ) := by
  rintro _ ⟨a, rfl⟩
  have h := Set.mem_centralizer_iff.mp hS _ ⟨a, rfl⟩
  ext v
  have hs : ampDiag ι (ρ a) (lp.single 2 k v) = lp.single 2 k (ρ a v) := by
    ext i
    rw [ampDiag_apply_coe]
    rcases eq_or_ne i k with rfl | hik
    · rw [lp.single_apply_self, lp.single_apply_self]
    · rw [lp.single_apply_ne _ _ _ hik, lp.single_apply_ne _ _ _ hik, map_zero]
  calc (ρ a * blockEntry S j k) v = ((diagAmplification ι ρ a * S) (lp.single 2 k v)) j := rfl
    _ = ((S * diagAmplification ι ρ a) (lp.single 2 k v)) j := by rw [h]
    _ = (blockEntry S j k * ρ a) v := by
      change S (ampDiag ι (ρ a) (lp.single 2 k v)) j = _
      rw [hs]; rfl

omit [CompleteSpace E] in
/-- **Block expansion.** On a finite index type, `(S x)_j = ∑ₖ S_{jk} (x k)`.

Blueprint reference: `lmm:amplification-block-expansion`. -/
theorem apply_eq_sum_blockEntry [Fintype ι]
    (S : lp (fun _ : ι ↦ E) 2 →L[ℂ] lp (fun _ : ι ↦ E) 2) (x : lp (fun _ : ι ↦ E) 2) (j : ι) :
    S x j = ∑ k, blockEntry S j k (x k) := by
  have hx : x = ∑ k, lp.single 2 k (x k) :=
    (lp.hasSum_single (p := 2) (by norm_num) x).unique (hasSum_fintype _)
  conv_lhs => rw [hx]
  rw [map_sum, lp.coeFn_sum, Finset.sum_apply]
  rfl

omit [DecidableEq ι] in
/-- **The diagonal of a bicommutant element lies in the amplified bicommutant.** If
`T ∈ ρ(𝔄)''`, then `diag(T, …, T) ∈ (ρ^ι(𝔄))''` for a finite index type `ι`.

Blueprint reference: `lmm:diagonal-in-amplified-bicommutant`. -/
theorem ampDiag_mem_bicommutant [Finite ι] (ρ : 𝔄 →⋆ₐ[ℂ] (E →L[ℂ] E)) {T : E →L[ℂ] E}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range ρ))) :
    ampDiag ι T ∈ Set.centralizer (Set.centralizer (Set.range (diagAmplification ι ρ))) := by
  classical
  have := Fintype.ofFinite ι
  rw [Set.mem_centralizer_iff]
  intro S hS
  refine lpDiag_ext fun x j => ?_
  have hc k : blockEntry S j k * T = T * blockEntry S j k :=
    Set.mem_centralizer_iff.mp hT _ (blockEntry_mem_centralizer ρ hS j k)
  change S (ampDiag ι T x) j = T (S x j)
  rw [apply_eq_sum_blockEntry, apply_eq_sum_blockEntry, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ampDiag_apply_coe]
  exact congrArg (· (x k)) (hc k)

end Blocks

end Physicslib4
