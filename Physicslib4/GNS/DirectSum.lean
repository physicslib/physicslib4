/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.LpDiagonal
import Physicslib4.GNS.Superselection

/-!
# Direct sums of representations

Given a family of `*`-representations `π i : A →⋆ₐ[ℂ] (H i →L[ℂ] H i)` of a
C*-algebra `A` on Hilbert spaces `H i`, the **direct-sum representation**
`⊕ᵢ πᵢ` acts on the ℓ²-direct sum `lp H 2` by the diagonal operator of
`fun i ↦ π i a` (uniformly bounded by `‖a‖`, since a `*`-homomorphism of
C*-algebras is contractive).

This file builds `directSum π : A →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2)` and proves the two
basic structural facts:

* `intertwines_single` — each summand embeds as a **subrepresentation**: the
  isometric inclusion `H j ↪ lp H 2` intertwines `π j` with `directSum π`;
* `summandProj_mem_commutant` — the orthogonal **projection onto the `j`-th
  summand lies in the commutant** of `directSum π`, so a direct sum of two or more
  nonzero summands is reducible.
-/

namespace Physicslib4
namespace GNS

variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [DecidableEq ι] {H : ι → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
variable (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))

/-! ### Coordinate evaluation -/

/-- Coordinate evaluation `x ↦ x j` as a continuous linear map `lp H 2 →L H j`
(norm `≤ 1`). -/
noncomputable def lpEvalCLM (j : ι) : lp H 2 →L[ℂ] H j :=
  LinearMap.mkContinuous
    { toFun := fun x => x j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1
    (fun x => by simpa using lp.norm_apply_le_norm (p := 2) (by norm_num) x j)

omit [DecidableEq ι] [∀ (i : ι), CompleteSpace (H i)] in
@[simp] theorem lpEvalCLM_apply (j : ι) (x : lp H 2) : lpEvalCLM j x = x j := rfl

/-! ### The direct-sum representation -/

/-- The value of the direct-sum representation on `a`: the diagonal operator of the
family `fun i ↦ π i a`, uniformly bounded by `‖a‖`. -/
noncomputable def directSumFun (a : A) : lp H 2 →L[ℂ] lp H 2 :=
  lpDiag (fun i => π i a) (norm_nonneg a) (fun i => NonUnitalStarAlgHom.norm_apply_le (π i) a)

omit [DecidableEq ι] in
@[simp] theorem directSumFun_apply_coe (a : A) (x : lp H 2) (i : ι) :
    (directSumFun π a x) i = π i a (x i) := rfl

/-- The **direct-sum representation** `⊕ᵢ πᵢ` on the ℓ²-direct sum `lp H 2`. -/
noncomputable def directSum : A →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun := directSumFun π
  map_one' := by refine lpDiag_ext fun x i => ?_; simp [map_one]
  map_mul' a b := by
    refine lpDiag_ext fun x i => ?_; simp [map_mul, ContinuousLinearMap.mul_apply]
  map_zero' := by
    refine lpDiag_ext fun x i => ?_
    change π i 0 (x i) = (0 : lp H 2) i
    rw [map_zero]; rfl
  map_add' a b := by
    refine lpDiag_ext fun x i => ?_
    change π i (a + b) (x i) = π i a (x i) + π i b (x i)
    rw [map_add (π i) a b]; rfl
  commutes' r := by
    refine lpDiag_ext fun x i => ?_
    simp [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, lp.coeFn_smul]
  map_star' a := by
    simp only [directSumFun]
    rw [lpDiag_star]
    refine lpDiag_ext fun x i => ?_
    change π i (star a) (x i) = star (π i a) (x i)
    rw [map_star (π i) a]

omit [DecidableEq ι] in
@[simp] theorem directSum_apply (a : A) : directSum π a = directSumFun π a := rfl

/-! ### Subrepresentations and commutant projections -/

/-- Each summand is a **subrepresentation**: the isometric inclusion `H j ↪ lp H 2`
intertwines `π j` with the direct-sum representation. -/
theorem intertwines_single (j : ι) :
    Intertwines (π j) (directSum π) (lp.singleContinuousLinearMap ℂ H 2 j) := by
  intro a v
  apply lp.ext
  funext i
  simp only [lp.singleContinuousLinearMap_apply, directSum_apply, directSumFun_apply_coe,
    lp.single_apply]
  rcases eq_or_ne i j with h | h
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- The orthogonal projection onto the `j`-th summand, `x ↦ single j (x j)`. -/
noncomputable def summandProj (j : ι) : lp H 2 →L[ℂ] lp H 2 :=
  (lp.singleContinuousLinearMap ℂ H 2 j).comp (lpEvalCLM j)

omit [∀ (i : ι), CompleteSpace (H i)] in
@[simp] theorem summandProj_apply (j : ι) (x : lp H 2) :
    summandProj j x = lp.single 2 j (x j) := by
  simp [summandProj, lp.singleContinuousLinearMap_apply]

/-- The **projection onto the `j`-th summand commutes with the whole
representation**, hence lies in the commutant of `directSum π`. -/
theorem summandProj_mem_commutant (j : ι) :
    summandProj (H := H) j ∈ Set.centralizer (Set.range (directSum π)) := by
  rw [Set.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  refine lpDiag_ext fun x i => ?_
  simp only [ContinuousLinearMap.mul_apply, directSum_apply, directSumFun_apply_coe,
    summandProj_apply, lp.single_apply]
  rcases eq_or_ne i j with h | h
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

end GNS
end Physicslib4
