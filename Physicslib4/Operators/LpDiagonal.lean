/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The diagonal operator on an ℓ² direct sum

Given a family of Hilbert spaces `E i` and a uniformly bounded family of operators
`T i : E i →L[𝕜] E i`, the **diagonal operator** `lpDiag T` acts on the ℓ²-direct
sum `lp E 2` coordinatewise: `(lpDiag T x) i = T i (x i)`. It is built from
`Memℓp.mono'` (well-definedness) and `LinearMap.mkContinuous` (the operator-norm
bound `‖lpDiag T‖ ≤ K`).

This file records the `*`-algebra-hom laws of the diagonal operator, as a function
of the family:

* `lpDiag_apply_coe` — the coordinate action;
* `lpDiag_congr` — the operator is independent of the chosen bound;
* `lpDiag_one`, `lpDiag_mul`, `lpDiag_add`, `lpDiag_smul` — the unital, multiplicative,
  additive, and `𝕜`-linear laws;
* `lpDiag_star` — the adjoint of a diagonal is the diagonal of adjoints.

These are the pieces from which a direct-sum `*`-representation `⊕ᵢ πᵢ` is assembled
(the diagonal operator of `fun i ↦ πᵢ a`, uniformly bounded by `‖a‖`). The file is
spacetime/AQFT-agnostic.
-/

open scoped InnerProductSpace ENNReal

namespace Physicslib4

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]

/-- Coordinatewise bound: `‖T i (x i)‖ ≤ ‖((K : 𝕜) • x) i‖` for a uniformly bounded
family. -/
private theorem lpDiag_coord_bound (T : ∀ i, E i →L[𝕜] E i) {K : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (x : lp E 2) (i : ι) :
    ‖T i (x i)‖ ≤ ‖((K : 𝕜) • x) i‖ := by
  rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hK]
  exact (T i).le_of_opNorm_le (hTK i) _

/-- The **diagonal operator** on the ℓ²-direct sum `lp E 2` induced by a uniformly
bounded family `T i : E i →L[𝕜] E i`, acting coordinatewise. -/
noncomputable def lpDiag (T : ∀ i, E i →L[𝕜] E i) {K : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) : lp E 2 →L[𝕜] lp E 2 :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        ⟨fun i => T i (x i),
          (lp.memℓp ((K : 𝕜) • x)).mono' (lpDiag_coord_bound T hK hTK x)⟩
      map_add' := fun x y => by
        ext i
        change T i (x i + y i) = T i (x i) + T i (y i)
        exact map_add (T i) (x i) (y i)
      map_smul' := fun c x => by ext i; simp }
    K
    (fun x => by
      have h : ‖(⟨fun i => T i (x i),
          (lp.memℓp ((K : 𝕜) • x)).mono' (lpDiag_coord_bound T hK hTK x)⟩ : lp E 2)‖
          ≤ ‖(K : 𝕜) • x‖ :=
        lp.norm_mono (by norm_num) (lpDiag_coord_bound T hK hTK x)
      rwa [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hK] at h)

@[simp] theorem lpDiag_apply_coe (T : ∀ i, E i →L[𝕜] E i) {K : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (x : lp E 2) (i : ι) :
    (lpDiag T hK hTK x) i = T i (x i) := rfl

/-- The diagonal operator depends only on the family, not on the chosen bound. -/
theorem lpDiag_congr (T : ∀ i, E i →L[𝕜] E i) {K K' : ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hTK : ∀ i, ‖T i‖ ≤ K) (hTK' : ∀ i, ‖T i‖ ≤ K') :
    lpDiag T hK hTK = lpDiag T hK' hTK' :=
  ContinuousLinearMap.ext fun _ => lp.ext (funext fun _ => rfl)

/-- Coordinatewise extensionality for operators on `lp E 2`. -/
theorem lpDiag_ext {F G : lp E 2 →L[𝕜] lp E 2}
    (h : ∀ (x : lp E 2) (i : ι), (F x) i = (G x) i) : F = G :=
  ContinuousLinearMap.ext fun x => lp.ext (funext (h x))

/-- Diagonal of the identities is the identity. -/
theorem lpDiag_one :
    lpDiag (fun i => (1 : E i →L[𝕜] E i)) zero_le_one
      (fun _ => by rw [ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id_le)
      = (1 : lp E 2 →L[𝕜] lp E 2) := by
  refine lpDiag_ext fun x i => ?_
  simp

/-- The diagonal operator is multiplicative: the diagonal of the composites is the
composite of the diagonals. -/
theorem lpDiag_mul (S T : ∀ i, E i →L[𝕜] E i) {KS KT KST : ℝ}
    (hKS : 0 ≤ KS) (hKT : 0 ≤ KT) (hKST : 0 ≤ KST)
    (hSK : ∀ i, ‖S i‖ ≤ KS) (hTK : ∀ i, ‖T i‖ ≤ KT)
    (hSTK : ∀ i, ‖S i ∘L T i‖ ≤ KST) :
    lpDiag (fun i => S i ∘L T i) hKST hSTK = lpDiag S hKS hSK ∘L lpDiag T hKT hTK := by
  refine lpDiag_ext fun x i => ?_
  simp

/-- The diagonal operator is additive. -/
theorem lpDiag_add (S T : ∀ i, E i →L[𝕜] E i) {KS KT KST : ℝ}
    (hKS : 0 ≤ KS) (hKT : 0 ≤ KT) (hKST : 0 ≤ KST)
    (hSK : ∀ i, ‖S i‖ ≤ KS) (hTK : ∀ i, ‖T i‖ ≤ KT)
    (hSTK : ∀ i, ‖S i + T i‖ ≤ KST) :
    lpDiag (fun i => S i + T i) hKST hSTK = lpDiag S hKS hSK + lpDiag T hKT hTK := by
  refine lpDiag_ext fun x i => ?_
  change (S i + T i) (x i) = S i (x i) + T i (x i)
  exact ContinuousLinearMap.add_apply (S i) (T i) (x i)

/-- The diagonal operator is `𝕜`-linear in the family. -/
theorem lpDiag_smul (c : 𝕜) (T : ∀ i, E i →L[𝕜] E i) {K KcT : ℝ}
    (hK : 0 ≤ K) (hKcT : 0 ≤ KcT)
    (hTK : ∀ i, ‖T i‖ ≤ K) (hcTK : ∀ i, ‖c • T i‖ ≤ KcT) :
    lpDiag (fun i => c • T i) hKcT hcTK = c • lpDiag T hK hTK := by
  refine lpDiag_ext fun x i => ?_
  simp [lp.coeFn_smul]

variable [∀ i, CompleteSpace (E i)]

/-- The adjoint of a diagonal operator is the diagonal of the adjoints. -/
theorem lpDiag_star (T : ∀ i, E i →L[𝕜] E i) {K : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) :
    star (lpDiag T hK hTK)
      = lpDiag (fun i => star (T i)) hK (fun i => by rw [norm_star]; exact hTK i) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [lpDiag_apply_coe, lpDiag_apply_coe, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

end Physicslib4
