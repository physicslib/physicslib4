/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Physicslib4.AQFT.HaagKastler.LocalVonNeumann
import Physicslib4.Operators.DensityTheorem

/-!
# The von Neumann density theorem for a unital `*`-representation

The bridge between physical observables and the local von Neumann algebras
`R(B) = π(𝔘(B))''` of `Physicslib4/AQFT/HaagKastler/LocalVonNeumann.lean` rests on the fact
that a bicommutant, though generally strictly larger than the image it is formed from, is
its *strong* closure: no measurement of finite precision can distinguish an element of the
bicommutant from a quasilocal observable close to it.

The strong operator topology is Mathlib's topology of pointwise convergence,
`PointwiseConvergenceCLM` (notation `H →Lₚₜ[ℂ] H`), and the commutant is
`Set.centralizer`, as in `LocalVonNeumann.lean`. What Mathlib does *not* have is the
density theorem itself (nor its Kaplansky strengthening); it is proved in
`Physicslib4/Operators/DensityTheorem.lean` together with this file.

## Main statements

* `Physicslib4.AQFT.HaagKastler.dense_range_in_bicommutant`
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {𝔄 : Type*} [Ring 𝔄] [StarRing 𝔄] [Algebra ℂ 𝔄]

omit [CompleteSpace H] in
/-- **Basic strong neighbourhoods of an operator.** In the strong operator topology (pointwise
convergence on finite sets), the neighbourhoods of `T` have as a basis the sets of `S` with
`‖S x - T x‖ < ε` for all `x` in a finite set.

Blueprint reference: `lmm:strong-neighbourhood-basis`. -/
theorem hasBasis_nhds_ofFun (T : H →L[ℂ] H) :
    (𝓝 (UniformConvergenceCLM.ofFun (σ := RingHom.id ℂ) (E := H) (F := H)
        {s : Set H | s.Finite} T)).HasBasis
      (fun sε : Set H × ℝ ↦ sε.1.Finite ∧ 0 < sε.2)
      (fun sε ↦ {S | ∀ x ∈ sε.1, ‖S x - T x‖ < sε.2}) := by
  have h0 := UniformConvergenceCLM.hasBasis_nhds_zero_of_basis (RingHom.id ℂ) H
    {s : Set H | s.Finite} ⟨∅, Set.finite_empty⟩
    (fun s hs t ht ↦ ⟨s ∪ t, hs.union ht, Set.subset_union_left, Set.subset_union_right⟩)
    (Metric.nhds_basis_ball (x := (0 : H)))
  rw [← nhds_translation_add_neg]
  refine (h0.comap _).congr (fun _ ↦ Iff.rfl) fun sε _ ↦ ?_
  ext S
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_ball_zero_iff, sub_eq_add_neg]
  exact Iff.rfl

/--
**The von Neumann density theorem**, in the form the observable bridge needs: the image of
a unital `*`-representation `π` of the quasilocal algebra `𝔘` on `H` is dense, in the
strong operator topology, in its bicommutant `π(𝔘)''`.

Unitality is the hypothesis that does the work — for the zero representation on a nonzero
`H` the image `{0}` is already strongly closed while the bicommutant is `ℂ · 1` — and it is
carried here by `StarAlgHom`, whose `map_one` field is exactly `π 1 = 1`.

The statement is phrased through the equivalence `UniformConvergenceCLM.ofFun`, which
re-topologizes `H →L[ℂ] H` as `H →Lₚₜ[ℂ] H`; both sets of operators are transported along
it so that the closure is taken in the strong topology.

This is Murphy's Lemma 4.1.4. It is **not** available in Mathlib: Mathlib has the double
commutant *property* of a bundled von Neumann algebra (`VonNeumannAlgebra.commutant_commutant`),
which is not a density result, and norm-topology closures of star subalgebras
(`StarSubalgebra.topologicalClosure`), which is the wrong topology. It is proved here from
the finitely-many-vectors approximation `exists_forall_norm_sub_lt_of_mem_bicommutant` of
`Physicslib4/Operators/DensityTheorem.lean` and the basic strong neighbourhoods
`hasBasis_nhds_ofFun`.

The self-adjoint strengthening — that every self-adjoint element of the bicommutant is a
strong limit of self-adjoint elements of the image — is the Kaplansky density theorem and
is deliberately *not* claimed: nothing in the bridge argument needs it.

Blueprint reference: `thrm:quasilocal-strongly-dense`.
-/
theorem dense_range_in_bicommutant (π : 𝔄 →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ⇑(UniformConvergenceCLM.ofFun (σ := RingHom.id ℂ) (E := H) (F := H)
        {s : Set H | s.Finite}) ''
      Set.centralizer (Set.centralizer (Set.range π)) ⊆
    closure (⇑(UniformConvergenceCLM.ofFun (σ := RingHom.id ℂ) (E := H) (F := H)
        {s : Set H | s.Finite}) '' Set.range π) := by
  rintro _ ⟨T, hT, rfl⟩
  rw [mem_closure_iff_nhds_basis' (hasBasis_nhds_ofFun T)]
  rintro ⟨s, ε⟩ ⟨hs, hε⟩
  obtain ⟨a, ha⟩ := exists_forall_norm_sub_lt_of_mem_bicommutant π hT hs hε
  exact ⟨_, fun x hx ↦ norm_sub_rev (T x) (π a x) ▸ ha x hx, π a, ⟨a, rfl⟩, rfl⟩

end HaagKastler
end AQFT
end Physicslib4
