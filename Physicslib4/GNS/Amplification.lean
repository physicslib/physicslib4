/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.DirectSum

/-!
# Amplification and reducibility of direct sums

Two consequences of the direct-sum construction (`Physicslib4.GNS.DirectSum`):

* **Reducibility.** The summand projections lie in the commutant, so if the
  direct-sum representation is irreducible they must be scalars
  (`summandProj_isScalar_of_isIrreducible`); consequently a direct sum with two
  summands carrying nonzero vectors is reducible (`not_isIrreducible_directSum`).
* **Amplification.** The `ι`-fold amplification `ι · π := ⊕_{ι} π` of a single
  representation, in which `π` embeds as each summand (`amplification_intertwines_single`).

## The quasi-equivalence `π ~ ι · π`

The quasi-equivalence of a representation with its amplification (`QuasiEquiv π (ι · π)`)
is **not** proved here. It requires a `*`-isomorphism of the generated von Neumann
algebras `π(A)'' ≃⋆ₐ (ι·π)(A)''`. The natural map is `T ↦ lpDiag (fun _ ↦ T)`
(the diagonal), which is an injective `*`-homomorphism carrying `π a ↦ (ι·π) a`;
but *surjectivity* onto `(ι·π)(A)''` is exactly the amplification commutant theorem
`(π ⊗ 1)' = π' ⊗ B(K)` (equivalently `(π ⊗ 1)'' = π'' ⊗ ℂ1`), a genuine von Neumann
algebra result that Mathlib does not currently provide. It is recorded as deferred.
-/

namespace Physicslib4
namespace GNS

variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [DecidableEq ι] {H : ι → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
variable (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))

/-! ### Reducibility -/

/-- If the direct-sum representation is irreducible, each summand projection is a
scalar operator (irreducibility means the commutant is trivial). -/
theorem summandProj_isScalar_of_isIrreducible (hirr : IsIrreducible (directSum π)) (j : ι) :
    summandProj (H := H) j ∈ scalarOperators (lp H 2) :=
  isIrreducible_iff_centralizer.mp hirr ▸ summandProj_mem_commutant π j

set_option linter.unusedDecidableInType false in
/-- A direct sum with two summands carrying nonzero vectors is **reducible**: the
projection onto one summand is a non-scalar element of the commutant. -/
theorem not_isIrreducible_directSum {j k : ι} (hjk : j ≠ k)
    {v : H j} (hv : v ≠ 0) {w : H k} (hw : w ≠ 0) :
    ¬ IsIrreducible (directSum π) := by
  intro hirr
  obtain ⟨c, hc⟩ := summandProj_isScalar_of_isIrreducible π hirr j
  have hjv : lp.single 2 j v ≠ 0 := by
    rw [← norm_ne_zero_iff, lp.norm_single (by norm_num)]
    exact norm_ne_zero_iff.mpr hv
  have hkw : lp.single 2 k w ≠ 0 := by
    rw [← norm_ne_zero_iff, lp.norm_single (by norm_num)]
    exact norm_ne_zero_iff.mpr hw
  have e1 := DFunLike.congr_fun hc (lp.single 2 j v)
  have e2 := DFunLike.congr_fun hc (lp.single 2 k w)
  simp only [summandProj_apply, smul_apply, one_apply_eq_self,
    lp.single_apply_self] at e1
  simp only [summandProj_apply, lp.single_apply_ne 2 k w hjk, lp.single_zero,
    smul_apply, one_apply_eq_self] at e2
  have hc1 : c = 1 := by
    have h0 : (1 - c) • lp.single 2 j v = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hjv
  have hc0 : c = 0 := by
    rcases smul_eq_zero.mp e2.symm with h | h
    · exact h
    · exact absurd h hkw
  rw [hc1] at hc0
  exact one_ne_zero hc0

end GNS

/-! ### Amplification -/

namespace GNS

variable {A : Type*} [CStarAlgebra A]
variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
variable {ι : Type*} [DecidableEq ι]
variable (π : A →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀))

/-- The `ι`-fold **amplification** `ι · π := ⊕_{i : ι} π` of a representation, on the
ℓ²-direct sum of `ι` copies of `H₀`. -/
noncomputable def amplification :
    A →⋆ₐ[ℂ] (lp (fun _ : ι => H₀) 2 →L[ℂ] lp (fun _ : ι => H₀) 2) :=
  directSum (fun _ : ι => π)

/-- In the amplification, `π` embeds as each summand: the isometric inclusion of the
`j`-th copy `H₀ ↪ ℓ²(ι, H₀)` intertwines `π` with `ι · π`. -/
theorem amplification_intertwines_single (j : ι) :
    Intertwines π (amplification (ι := ι) π)
      (lp.singleContinuousLinearMap ℂ (fun _ : ι => H₀) 2 j) :=
  intertwines_single (fun _ : ι => π) j

end GNS
end Physicslib4
