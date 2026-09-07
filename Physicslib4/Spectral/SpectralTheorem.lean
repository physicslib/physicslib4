/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.BorelCalculus
import Physicslib4.Spectral.OperatorIntegral

/-!
# The spectral theorem for bounded self-adjoint operators

The projections `μ^A(E) ≡ 1_E(A)` of the bounded Borel functional calculus assemble
into a projection-valued measure on `σ(A)` which integrates the identity function to
`A`, and it is the unique projection-valued measure with that property.

## Main definitions

* `Physicslib4.Spectral.spectralMeasure` — the projection-valued measure `μ^A`.
* `Physicslib4.Spectral.functionalCalculus` — `f(A) = ∫ f dμ^A`.

## Main statements

* `Physicslib4.Spectral.spectralMeasure_integral_id` — `∫ λ dμ^A(λ) = A`.
* `Physicslib4.Spectral.borelCalculus_eq_integral` — the two constructions of `f(A)`
  agree.
* `Physicslib4.Spectral.existsUnique_spectralMeasure` — **the spectral theorem**,
  proved from `spectralMeasure_integral_id` and `pvm_eq_of_integral_id_eq`.

## Implementation notes

As in `Physicslib4/Spectral/ContinuousCalculus.lean`, the blueprint's `σ(A) ⊆ ℂ` is
represented by Mathlib's real spectrum `spectrum ℝ A`, which for self-adjoint `A` is
homeomorphic to it via `Complex.ofReal`; the blueprint's `∫ λ dμ^A(λ)` is therefore
the integral of `fun l => ((l : ℝ) : ℂ)`.
-/

namespace Physicslib4
namespace Spectral

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H}

/-!
### The projections `μ^A(E) = 1_E(A)`
-/

/--
Each `μ^A(E) = 1_E(A)` is a bounded orthogonal projection.

Blueprint reference: `prpstn:mua-projection`.
-/
theorem isStarProjection_borelCalculus_indicator (hA : IsSelfAdjoint A)
    {E : Set (spectrum ℝ A)} (hE : MeasurableSet E) :
    IsStarProjection (borelCalculus hA (E.indicator (1 : spectrum ℝ A → ℂ))) := by
  have hf : E.indicator (1 : spectrum ℝ A → ℂ) ∈ BddMeasurable (spectrum ℝ A) := by
    constructor
    · exact Measurable.indicator measurable_const hE
    · refine ⟨1, fun x => ?_⟩
      by_cases h : x ∈ E <;> simp [Set.indicator, h]
  refine ⟨?_, ?_⟩
  · change borelCalculus hA (E.indicator (1 : spectrum ℝ A → ℂ)) *
        borelCalculus hA (E.indicator (1 : spectrum ℝ A → ℂ)) =
        borelCalculus hA (E.indicator (1 : spectrum ℝ A → ℂ))
    rw [← borelCalculus_mul hA hf hf]
    congr 1
    funext x
    by_cases h : x ∈ E <;> simp [Set.indicator, h]
  · refine isSelfAdjoint_borelCalculus hA hf ?_
    intro l
    by_cases h : l ∈ E <;> simp [Set.indicator, h]

/--
`μ^A` is multiplicative: `μ^A(E₁) μ^A(E₂) = μ^A(E₁ ∩ E₂)`.

Blueprint reference: `prpstn:mua-multiplicative`.
-/
theorem borelCalculus_indicator_mul (hA : IsSelfAdjoint A) {E₁ E₂ : Set (spectrum ℝ A)}
    (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂) :
    borelCalculus hA (E₁.indicator (1 : spectrum ℝ A → ℂ)) *
        borelCalculus hA (E₂.indicator (1 : spectrum ℝ A → ℂ)) =
      borelCalculus hA ((E₁ ∩ E₂).indicator (1 : spectrum ℝ A → ℂ)) := by
  have hf₁ : E₁.indicator (1 : spectrum ℝ A → ℂ) ∈ BddMeasurable (spectrum ℝ A) := by
    constructor
    · exact Measurable.indicator measurable_const hE₁
    · refine ⟨1, fun x => ?_⟩
      by_cases h : x ∈ E₁ <;> simp [Set.indicator, h]
  have hf₂ : E₂.indicator (1 : spectrum ℝ A → ℂ) ∈ BddMeasurable (spectrum ℝ A) := by
    constructor
    · exact Measurable.indicator measurable_const hE₂
    · refine ⟨1, fun x => ?_⟩
      by_cases h : x ∈ E₂ <;> simp [Set.indicator, h]
  have hpoint :
      E₁.indicator (1 : spectrum ℝ A → ℂ) * E₂.indicator (1 : spectrum ℝ A → ℂ) =
        (E₁ ∩ E₂).indicator (1 : spectrum ℝ A → ℂ) := by
    funext x
    by_cases h₁ : x ∈ E₁ <;> by_cases h₂ : x ∈ E₂ <;>
      simp [Set.indicator, h₁, h₂, Set.mem_inter_iff]
  calc
    borelCalculus hA (E₁.indicator (1 : spectrum ℝ A → ℂ)) *
        borelCalculus hA (E₂.indicator (1 : spectrum ℝ A → ℂ))
        = borelCalculus hA (E₁.indicator (1 : spectrum ℝ A → ℂ) *
            E₂.indicator (1 : spectrum ℝ A → ℂ)) :=
          (borelCalculus_mul hA hf₁ hf₂).symm
    _ = borelCalculus hA ((E₁ ∩ E₂).indicator (1 : spectrum ℝ A → ℂ)) :=
          congrArg (borelCalculus hA) hpoint

/--
`μ^A(∅) = 0`.

Blueprint reference: `prpstn:mua-empty-and-whole` (first part).
-/
theorem borelCalculus_indicator_empty (hA : IsSelfAdjoint A) :
    borelCalculus hA ((∅ : Set (spectrum ℝ A)).indicator (1 : spectrum ℝ A → ℂ)) = 0 := by
  rw [Set.indicator_empty]
  have h0 : (0 : spectrum ℝ A → ℂ) ∈ BddMeasurable (spectrum ℝ A) := by
    constructor
    · exact measurable_const
    · exact ⟨0, by simp⟩
  let hQ : IsBoundedQuadraticForm (borelForm hA 0) := isBoundedQuadraticForm_borelForm hA h0
  have hC : ∀ ψ : H, borelForm hA 0 ψ = ⟪ψ, (0 : H →L[ℂ] H) ψ⟫_ℂ := by
    intro ψ
    simp [borelForm]
  calc
    borelCalculus hA 0 = hQ.toOperator :=
      hQ.eq_toOperator (fun ψ => (inner_borelCalculus hA h0 ψ).symm)
    _ = (0 : H →L[ℂ] H) := (hQ.eq_toOperator hC).symm

/--
`μ^A(σ(A)) = 1`.

Blueprint reference: `prpstn:mua-empty-and-whole` (second part).
-/
theorem borelCalculus_indicator_univ (hA : IsSelfAdjoint A) :
    borelCalculus hA ((Set.univ : Set (spectrum ℝ A)).indicator (1 : spectrum ℝ A → ℂ)) = 1 := by
  rw [Set.indicator_univ]
  have h1 : (1 : spectrum ℝ A → ℂ) ∈ BddMeasurable (spectrum ℝ A) := by
    constructor
    · exact measurable_const
    · exact ⟨1, by intro x; simp⟩
  let hQ : IsBoundedQuadraticForm (borelForm hA 1) := isBoundedQuadraticForm_borelForm hA h1
  have hC : ∀ ψ : H, borelForm hA 1 ψ = ⟪ψ, ψ⟫_ℂ := by
    intro ψ
    calc
      borelForm hA 1 ψ = ((assocMeasure hA ψ) Set.univ).toReal := by
        simp [borelForm, Measure.real]
      _ = ‖ψ‖ ^ 2 := by
        rw [assocMeasure_univ hA ψ]
        exact_mod_cast ENNReal.toReal_ofReal (sq_nonneg ‖ψ‖)
      _ = ⟪ψ, ψ⟫_ℂ := by
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
  calc
    borelCalculus hA 1 = hQ.toOperator :=
      hQ.eq_toOperator (fun ψ => (inner_borelCalculus hA h1 ψ).symm)
    _ = (1 : H →L[ℂ] H) := (hQ.eq_toOperator hC).symm

/--
`μ^A` is countably additive in the norm topology of `H`.

Blueprint reference: `prpstn:mua-countably-additive`.
-/
theorem hasSum_borelCalculus_indicator (hA : IsSelfAdjoint A) (E : ℕ → Set (spectrum ℝ A))
    (hE : ∀ j, MeasurableSet (E j)) (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (ψ : H) :
    HasSum (fun j => borelCalculus hA ((E j).indicator (1 : spectrum ℝ A → ℂ)) ψ)
      (borelCalculus hA ((⋃ j, E j).indicator (1 : spectrum ℝ A → ℂ)) ψ) := by
  classical
  let P : ℕ → H →L[ℂ] H := fun i =>
    borelCalculus hA ((E i).indicator (1 : spectrum ℝ A → ℂ))
  let Q : H →L[ℂ] H := borelCalculus hA ((⋃ j, E j).indicator (1 : spectrum ℝ A → ℂ))
  refine hasSum_of_isStarProjection_orthogonal (P := P) ?_ ?_ Q ?_ ψ
  · intro i
    exact isStarProjection_borelCalculus_indicator hA (hE i)
  · intro i j hij
    calc
      P i * P j = borelCalculus hA ((E i ∩ E j).indicator (1 : spectrum ℝ A → ℂ)) := by
        simpa [P] using borelCalculus_indicator_mul hA (hE i) (hE j)
      _ = 0 := by
        have hInt : (E i ∩ E j).indicator (1 : spectrum ℝ A → ℂ) =
            (∅ : Set (spectrum ℝ A)).indicator (1 : spectrum ℝ A → ℂ) := by
          congr 1
          exact Set.disjoint_iff_inter_eq_empty.mp (hdisj hij)
        rw [hInt]
        exact borelCalculus_indicator_empty hA
  · -- convergence of the partial sums to the full-union indicator
    intro φ
    let R : ℕ → H →L[ℂ] H := fun n =>
      borelCalculus hA ((⋃ i ∈ Finset.range n, E i).indicator (1 : spectrum ℝ A → ℂ))
    have hBdd : ∀ {S : Set (spectrum ℝ A)}, MeasurableSet S →
        S.indicator (1 : spectrum ℝ A → ℂ) ∈ BddMeasurable (spectrum ℝ A) := by
      intro S hS
      constructor
      · exact Measurable.indicator measurable_const hS
      · refine ⟨1, fun x => ?_⟩
        by_cases h : x ∈ S <;> simp [Set.indicator, h]
    have hmeasS : ∀ n : ℕ, MeasurableSet (⋃ i ∈ Finset.range n, E i) :=
      fun n => Finset.measurableSet_biUnion (Finset.range n) (fun i _ => hE i)
    have hSmeas : ∀ n, (⋃ i ∈ Finset.range n, E i).indicator (1 : spectrum ℝ A → ℂ) ∈
        BddMeasurable (spectrum ℝ A) := fun n => hBdd (hmeasS n)
    have hPmeas : ∀ i, (E i).indicator (1 : spectrum ℝ A → ℂ) ∈
        BddMeasurable (spectrum ℝ A) := fun i => hBdd (hE i)
    have hUnmeas : MeasurableSet (⋃ j, E j) := MeasurableSet.iUnion hE
    have hUmeas : (⋃ j, E j).indicator (1 : spectrum ℝ A → ℂ) ∈
        BddMeasurable (spectrum ℝ A) := hBdd hUnmeas
    have hRproj : ∀ n : ℕ, IsStarProjection (R n) :=
      fun n => isStarProjection_borelCalculus_indicator hA (hmeasS n)
    have hQproj : IsStarProjection Q :=
      isStarProjection_borelCalculus_indicator hA hUnmeas
    have hfin_le : ∀ n : ℕ, (⋃ i ∈ Finset.range n, E i) ⊆ (⋃ j, E j) := by
      intro n l hl
      rcases Set.mem_iUnion₂.mp hl with ⟨i, _hi, hli⟩
      exact Set.mem_iUnion.mpr ⟨i, hli⟩
    have hRQ : ∀ n : ℕ, R n * Q = R n := by
      intro n
      calc
        R n * Q = borelCalculus hA (((⋃ i ∈ Finset.range n, E i) ∩ (⋃ j, E j)).indicator
            (1 : spectrum ℝ A → ℂ)) := by
          simpa [R, Q] using borelCalculus_indicator_mul hA (hmeasS n) hUnmeas
        _ = R n := by
          have hInt : (((⋃ i ∈ Finset.range n, E i) ∩ (⋃ j, E j)).indicator
              (1 : spectrum ℝ A → ℂ)) =
              (⋃ i ∈ Finset.range n, E i).indicator (1 : spectrum ℝ A → ℂ) := by
            congr 1
            exact Set.inter_eq_self_of_subset_left (hfin_le n)
          rw [hInt]
    have hQR : ∀ n : ℕ, Q * R n = R n := by
      intro n
      have hQs : star Q = Q := hQproj.isSelfAdjoint
      have hRs : star (R n) = R n := (hRproj n).isSelfAdjoint
      calc
        Q * R n = star Q * star (R n) := by
          rw [hQs, hRs]
        _ = star (R n * Q) := by
          rw [star_mul]
        _ = star (R n) := congrArg star (hRQ n)
        _ = R n := hRs
    have hsum_op : ∀ n : ℕ, (∑ i ∈ Finset.range n, P i) = R n := by
      intro n
      induction n with
      | zero =>
          calc
            (∑ i ∈ Finset.range 0, P i) = 0 := by simp [P]
            _ = R 0 := by
              have hU : (⋃ i ∈ Finset.range 0, E i) = (∅ : Set (spectrum ℝ A)) := by
                ext l
                simp [Finset.range_zero]
              change (0 : H →L[ℂ] H) =
                borelCalculus hA ((⋃ i ∈ Finset.range 0, E i).indicator
                  (1 : spectrum ℝ A → ℂ))
              rw [hU]
              exact (borelCalculus_indicator_empty hA).symm
      | succ n ih =>
          calc
            (∑ i ∈ Finset.range (n + 1), P i)
                = (∑ i ∈ Finset.range n, P i) + P n := by
                    rw [Finset.sum_range_succ]
            _ = R n + P n := by rw [ih]
            _ = borelCalculus hA ((⋃ i ∈ Finset.range n, E i).indicator
                  (1 : spectrum ℝ A → ℂ)) +
                borelCalculus hA ((E n).indicator (1 : spectrum ℝ A → ℂ)) := by
                    rfl
            _ = borelCalculus hA ((⋃ i ∈ Finset.range n, E i).indicator
                  (1 : spectrum ℝ A → ℂ) + (E n).indicator (1 : spectrum ℝ A → ℂ)) := by
                    exact (borelCalculus_add hA (hSmeas n) (hPmeas n)).symm
            _ = borelCalculus hA (((⋃ i ∈ Finset.range n, E i) ∪ E n).indicator
                  (1 : spectrum ℝ A → ℂ)) := by
                    have hSn : Disjoint (⋃ i ∈ Finset.range n, E i) (E n) := by
                      rw [Set.disjoint_iUnion₂_left]
                      intro i hi
                      exact hdisj (ne_of_lt (Finset.mem_range.mp hi))
                    exact congrArg (borelCalculus hA)
                      (Set.indicator_union_of_disjoint hSn (1 : spectrum ℝ A → ℂ)).symm
            _ = borelCalculus hA ((⋃ i ∈ Finset.range (n + 1), E i).indicator
                  (1 : spectrum ℝ A → ℂ)) := by
                    have hUn : (⋃ i ∈ Finset.range (n + 1), E i) =
                        (⋃ i ∈ Finset.range n, E i) ∪ E n := by
                      rw [Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
                    rw [hUn]
            _ = R (n + 1) := rfl
    -- the squared norm of the difference is the difference of the inner products
    have hnormSqC : ∀ n : ℕ, (‖Q φ - R n φ‖ : ℂ) ^ 2 = ⟪φ, Q φ⟫_ℂ - ⟪φ, R n φ⟫_ℂ := by
      intro n
      have hQstar : star Q = Q := hQproj.isSelfAdjoint
      have hQadj : Q.adjoint = Q := by
        rw [← ContinuousLinearMap.star_eq_adjoint Q]
        exact hQstar
      have hQidem : Q * Q = Q := hQproj.isIdempotentElem
      have hRstar : star (R n) = R n := (hRproj n).isSelfAdjoint
      have hRadj : (R n).adjoint = R n := by
        rw [← ContinuousLinearMap.star_eq_adjoint (R n)]
        exact hRstar
      have hRidem : R n * R n = R n := (hRproj n).isIdempotentElem
      have ha : ⟪Q φ, Q φ⟫_ℂ = ⟪φ, Q φ⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right Q φ (Q φ)]
        rw [hQadj]
        change ⟪φ, (Q * Q) φ⟫_ℂ = ⟪φ, Q φ⟫_ℂ
        rw [hQidem]
      have hb : ⟪Q φ, R n φ⟫_ℂ = ⟪φ, R n φ⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right Q φ (R n φ)]
        rw [hQadj]
        change ⟪φ, (Q * R n) φ⟫_ℂ = ⟪φ, R n φ⟫_ℂ
        rw [hQR n]
      have hc : ⟪R n φ, Q φ⟫_ℂ = ⟪φ, R n φ⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right (R n) φ (Q φ)]
        rw [hRadj]
        change ⟪φ, (R n * Q) φ⟫_ℂ = ⟪φ, R n φ⟫_ℂ
        rw [hRQ n]
      have hd : ⟪R n φ, R n φ⟫_ℂ = ⟪φ, R n φ⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right (R n) φ (R n φ)]
        rw [hRadj]
        change ⟪φ, (R n * R n) φ⟫_ℂ = ⟪φ, R n φ⟫_ℂ
        rw [hRidem]
      calc
        (‖Q φ - R n φ‖ : ℂ) ^ 2 = ⟪Q φ - R n φ, Q φ - R n φ⟫_ℂ :=
          (inner_self_eq_norm_sq_to_K (Q φ - R n φ)).symm
        _ = (⟪Q φ, Q φ⟫_ℂ - ⟪Q φ, R n φ⟫_ℂ) -
            (⟪R n φ, Q φ⟫_ℂ - ⟪R n φ, R n φ⟫_ℂ) := by
          rw [inner_sub_left]
          rw [inner_sub_right (x := Q φ) (y := Q φ) (z := R n φ)]
          rw [inner_sub_right (x := R n φ) (y := Q φ) (z := R n φ)]
        _ = ⟪Q φ, Q φ⟫_ℂ - ⟪Q φ, R n φ⟫_ℂ - ⟪R n φ, Q φ⟫_ℂ + ⟪R n φ, R n φ⟫_ℂ := by
          ring
        _ = ⟪φ, Q φ⟫_ℂ - ⟪φ, R n φ⟫_ℂ := by
          rw [ha, hb, hc, hd]
          ring
    -- the inner products converge because the indicators converge pointwise
    have hinner : Tendsto (fun n : ℕ => ⟪φ, R n φ⟫_ℂ) atTop (𝓝 (⟪φ, Q φ⟫_ℂ)) := by
      let f : ℕ → spectrum ℝ A → ℂ := fun n =>
        (⋃ i ∈ Finset.range n, E i).indicator (1 : spectrum ℝ A → ℂ)
      let g : spectrum ℝ A → ℂ := (⋃ j, E j).indicator (1 : spectrum ℝ A → ℂ)
      have hmeas : ∀ n, Measurable (f n) := by
        intro n
        exact Measurable.indicator measurable_const (hmeasS n)
      have hlim : BoundedPointwiseLimit f g (fun _ : spectrum ℝ A => 1) := by
        constructor
        · intro n x
          change ‖(⋃ i ∈ Finset.range n, E i).indicator (1 : spectrum ℝ A → ℂ) x‖ ≤ 1
          rw [Set.indicator_apply]
          split <;> simp
        · intro x
          by_cases hx : x ∈ ⋃ j, E j
          · have he : (fun _ : ℕ => (1 : ℂ)) =ᶠ[atTop] fun n => f n x := by
              rcases Set.mem_iUnion.mp hx with ⟨j₀, hj₀⟩
              filter_upwards [Filter.eventually_gt_atTop j₀] with n hn
              have hx2 : x ∈ ⋃ i ∈ Finset.range n, E i :=
                Set.mem_iUnion₂.mpr ⟨j₀, Finset.mem_range.mpr hn, hj₀⟩
              change (1 : ℂ) =
                (⋃ i ∈ Finset.range n, E i).indicator (1 : spectrum ℝ A → ℂ) x
              exact (Set.indicator_of_mem hx2 (1 : spectrum ℝ A → ℂ)).symm
            have hgx : g x = 1 := Set.indicator_of_mem hx (1 : spectrum ℝ A → ℂ)
            rw [hgx]
            exact Filter.Tendsto.congr' he tendsto_const_nhds
          · have h0 : (fun _ : ℕ => (0 : ℂ)) =ᶠ[atTop] fun n => f n x := by
              refine Filter.Eventually.of_forall fun n => ?_
              have hn' : x ∉ ⋃ i ∈ Finset.range n, E i := fun h => hx (hfin_le n h)
              change (0 : ℂ) =
                (⋃ i ∈ Finset.range n, E i).indicator (1 : spectrum ℝ A → ℂ) x
              exact (Set.indicator_of_notMem hn' (1 : spectrum ℝ A → ℂ)).symm
            have hgx : g x = 0 := Set.indicator_of_notMem hx (1 : spectrum ℝ A → ℂ)
            rw [hgx]
            exact Filter.Tendsto.congr' h0 tendsto_const_nhds
      have hBC : Tendsto (fun n => borelForm hA (f n) φ) atTop (𝓝 (borelForm hA g φ)) :=
        tendsto_borelForm hA hmeas hlim φ
      have hinnerR : (fun n => ⟪φ, R n φ⟫_ℂ) = fun n => borelForm hA (f n) φ := by
        funext n
        dsimp [R, f]
        exact inner_borelCalculus hA (hSmeas n) φ
      have hinnerQ : ⟪φ, Q φ⟫_ℂ = borelForm hA g φ := by
        dsimp [Q, g]
        exact inner_borelCalculus hA hUmeas φ
      simpa [← hinnerR, ← hinnerQ] using hBC
    -- hence the squared distance to the limit tends to zero
    have hnsqC : Tendsto (fun n : ℕ => (‖Q φ - R n φ‖ : ℂ) ^ 2) atTop (𝓝 (0 : ℂ)) := by
      have hsub : Tendsto (fun n : ℕ => ⟪φ, Q φ⟫_ℂ - ⟪φ, R n φ⟫_ℂ) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := ⟪φ, Q φ⟫_ℂ)).sub hinner
      simpa [← hnormSqC] using hsub
    have hnsq : Tendsto (fun n : ℕ => (‖Q φ - R n φ‖ : ℝ) ^ 2) atTop (𝓝 (0 : ℝ)) := by
      have hc : Tendsto (fun n => Complex.re ((‖Q φ - R n φ‖ : ℂ) ^ 2)) atTop
          (𝓝 (Complex.re 0)) := (Complex.continuous_re.tendsto (0 : ℂ)).comp hnsqC
      convert hc using 1
      · ext n
        simp [← Complex.ofReal_pow]
      · rfl
    have hnorm : Tendsto (fun n : ℕ => ‖Q φ - R n φ‖) atTop (𝓝 (0 : ℝ)) := by
      have hsqrt : Tendsto (fun n => Real.sqrt ((‖Q φ - R n φ‖ : ℝ) ^ 2)) atTop (𝓝 0) := by
        simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hnsq
      refine hsqrt.congr fun n => ?_
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (Q φ - R n φ))]
    have hconvR : Tendsto (fun n : ℕ => R n φ) atTop (𝓝 (Q φ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine hnorm.congr fun n => ?_
      rw [← norm_neg (R n φ - Q φ), neg_sub]
    have hseq : (fun n => ∑ i ∈ Finset.range n, P i φ) = fun n => R n φ := by
      funext n
      calc
        ∑ i ∈ Finset.range n, P i φ = (∑ i ∈ Finset.range n, P i) φ := by
          rw [← sum_apply]
        _ = R n φ := by rw [hsum_op n]
    simpa [← hseq] using hconvR

/-!
### The spectral measure
-/

open Classical in
/--
The projection-valued measure `μ^A` of a self-adjoint operator `A`, built directly
out of `μ^A(E) = 1_E(A)`: its four defining properties are the four `prpstn:mua-*`
statements above.
-/
noncomputable def spectralMeasure (hA : IsSelfAdjoint A) :
    ProjectionValuedMeasure (spectrum ℝ A) H where
  toFun E :=
    if MeasurableSet E then borelCalculus hA (E.indicator (1 : spectrum ℝ A → ℂ)) else 0
  isStarProjection' E := by
    by_cases hE : MeasurableSet E
    · simpa [hE] using isStarProjection_borelCalculus_indicator hA hE
    · simp [hE]
  notMeasurable' _E hE := if_neg hE
  univ' := by simpa using borelCalculus_indicator_univ hA
  hasSum' E hE hdisj v := by
    simpa [hE, MeasurableSet.iUnion hE] using hasSum_borelCalculus_indicator hA E hE hdisj v
  inter' E F hE hF := by
    simpa [hE, hF, hE.inter hF] using (borelCalculus_indicator_mul hA hE hF).symm

theorem spectralMeasure_apply (hA : IsSelfAdjoint A) {E : Set (spectrum ℝ A)}
    (hE : MeasurableSet E) :
    spectralMeasure hA E = borelCalculus hA (E.indicator (1 : spectrum ℝ A → ℂ)) := by
  classical
  simp only [spectralMeasure, ProjectionValuedMeasure.coe_mk, if_pos hE]

/--
The integral of an indicator against `μ^A` recovers `μ^A(E)`.

This is `ProjectionValuedMeasure.integral_indicator` specialised to `μ^A`.

Blueprint reference: `prpstn:mua-indicator-integral`.
-/
theorem spectralMeasure_integral_indicator (hA : IsSelfAdjoint A) {E : Set (spectrum ℝ A)}
    (hE : MeasurableSet E) :
    (spectralMeasure hA).integral (E.indicator (1 : spectrum ℝ A → ℂ)) =
      spectralMeasure hA E :=
  (spectralMeasure hA).integral_indicator hE

/-- The measure `μ_ψ` of the continuous calculus agrees with the measure
associated with the spectral measure by `ProjectionValuedMeasure.assoc`. -/
private theorem assocMeasure_eq_spectralMeasure_assoc (hA : IsSelfAdjoint A) (ψ : H) :
    assocMeasure hA ψ = (spectralMeasure hA).assoc ψ := by
  apply MeasureTheory.Measure.ext
  intro E hE
  have hg : E.indicator (1 : spectrum ℝ A → ℂ) ∈ BddMeasurable (spectrum ℝ A) := by
    constructor
    · exact Measurable.indicator measurable_const hE
    · refine ⟨1, fun x => ?_⟩
      by_cases h : x ∈ E <;> simp [Set.indicator, h]
  have htoReal : (((spectralMeasure hA).assoc ψ) E).toReal = ((assocMeasure hA ψ) E).toReal := by
    calc
      (((spectralMeasure hA).assoc ψ) E).toReal
          = (⟪ψ, (spectralMeasure hA) E ψ⟫_ℂ).re :=
              ProjectionValuedMeasure.assoc_apply (spectralMeasure hA) ψ hE
      _ = (⟪ψ, borelCalculus hA (E.indicator (1 : spectrum ℝ A → ℂ)) ψ⟫_ℂ).re := by
              rw [spectralMeasure_apply hA hE]
      _ = (borelForm hA (E.indicator (1 : spectrum ℝ A → ℂ)) ψ).re := by
              rw [inner_borelCalculus hA hg ψ]
      _ = (∫ l, E.indicator (1 : spectrum ℝ A → ℂ) l ∂(assocMeasure hA ψ)).re := rfl
      _ = ((assocMeasure hA ψ) E).toReal := by
              change (∫ l, E.indicator (fun _ : spectrum ℝ A => (1 : ℂ)) l
                ∂(assocMeasure hA ψ)).re = ((assocMeasure hA ψ) E).toReal
              rw [integral_indicator_const (1 : ℂ) hE, Measure.real_def]
              simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top (assocMeasure hA ψ) E)]
  rw [← ENNReal.ofReal_toReal (measure_ne_top ((spectralMeasure hA).assoc ψ) E)]
  exact (congrArg ENNReal.ofReal htoReal).symm

/--
The two constructions of `f(A)` — from the quadratic form `Q_f`, and as the
projection-valued integral of `f` against `μ^A` — agree.

Blueprint reference: `prpstn:mua-bounded-calculus-agrees`.
-/
theorem borelCalculus_eq_integral (hA : IsSelfAdjoint A) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) :
    borelCalculus hA f = (spectralMeasure hA).integral f := by
  have hQ : IsBoundedQuadraticForm (borelForm hA f) := isBoundedQuadraticForm_borelForm hA hf
  have hrep : ∀ ψ : H, borelForm hA f ψ = ⟪ψ, (spectralMeasure hA).integral f ψ⟫_ℂ := by
    intro ψ
    calc
      borelForm hA f ψ = ∫ l, f l ∂(assocMeasure hA ψ) := rfl
      _ = ∫ l, f l ∂((spectralMeasure hA).assoc ψ) := by
        rw [assocMeasure_eq_spectralMeasure_assoc hA ψ]
      _ = ⟪ψ, (spectralMeasure hA).integral f ψ⟫_ℂ := by
        rw [← ProjectionValuedMeasure.inner_integral (spectralMeasure hA) hf ψ]
  calc
    borelCalculus hA f = hQ.toOperator := by
      exact hQ.eq_toOperator (fun ψ => (inner_borelCalculus hA hf ψ).symm)
    _ = (spectralMeasure hA).integral f := (hQ.eq_toOperator (fun ψ => hrep ψ)).symm

/-- The Borel calculus of the continuous real-valued function `g` agrees with the
real calculus `g(A)`. -/
private theorem borelCalculus_eq_realCalculus (hA : IsSelfAdjoint A)
    (g : C(spectrum ℝ A, ℝ)) :
    borelCalculus hA (fun l => ((g l : ℝ) : ℂ)) = realCalculus hA g := by
  let gc : spectrum ℝ A → ℂ := fun l => ((g l : ℝ) : ℂ)
  have hgc : gc ∈ BddMeasurable (spectrum ℝ A) := by
    change (fun l => ((g l : ℝ) : ℂ)) ∈ BddMeasurable (spectrum ℝ A)
    exact (continuous_mem_FClass hA g).1
  let hQ : IsBoundedQuadraticForm (borelForm hA gc) :=
    isBoundedQuadraticForm_borelForm hA hgc
  have h1 : borelCalculus hA gc = hQ.toOperator := by
    exact hQ.eq_toOperator (fun ψ => (inner_borelCalculus hA hgc ψ).symm)
  have h2 : realCalculus hA g = hQ.toOperator := by
    refine hQ.eq_toOperator ?_
    intro ψ
    change borelForm hA (fun l => ((g l : ℝ) : ℂ)) ψ = ⟪ψ, realCalculus hA g ψ⟫_ℂ
    rw [borelForm]
    norm_cast
    exact (integral_assocMeasure hA ψ g).symm
  exact h1.trans h2.symm

/--
`∫ λ dμ^A(λ) = A`.

Blueprint reference: `prpstn:mua-integrates-to-A`.
-/
theorem spectralMeasure_integral_id (hA : IsSelfAdjoint A) :
    (spectralMeasure hA).integral (fun l => ((l : ℝ) : ℂ)) = A := by
  let g : C(spectrum ℝ A, ℝ) := ⟨fun l => (l : ℝ), continuous_subtype_val⟩
  have hf : (fun l : spectrum ℝ A => ((l : ℝ) : ℂ)) ∈ BddMeasurable (spectrum ℝ A) := by
    exact (continuous_mem_FClass hA g).1
  calc
    (spectralMeasure hA).integral (fun l => ((l : ℝ) : ℂ))
        = borelCalculus hA (fun l => ((l : ℝ) : ℂ)) :=
          (borelCalculus_eq_integral hA hf).symm
    _ = realCalculus hA g := borelCalculus_eq_realCalculus hA g
    _ = realCalculus hA (polyOn A (Polynomial.X : Polynomial ℝ)) := by
          congr 1
          ext l
          simp [g, polyOn, Polynomial.eval_X]
    _ = Polynomial.aeval A (Polynomial.X : Polynomial ℝ) :=
          realCalculus_polyOn hA (Polynomial.X : Polynomial ℝ)
    _ = A := by
          exact Polynomial.aeval_X (R := ℝ) (x := A)

/--
The projections `μ^A(E) = 1_E(A)` form a projection-valued measure on `σ(A)` which
integrates the identity function to `A`.

Both halves have already been established — the first by the construction of
`spectralMeasure`, the second by `spectralMeasure_integral_id` — so this blueprint
node is proved rather than restated.

Blueprint reference: `thrm:hall-8.10`.
-/
theorem exists_spectralMeasure (hA : IsSelfAdjoint A) :
    ∃ μ : ProjectionValuedMeasure (spectrum ℝ A) H,
      (∀ E : Set (spectrum ℝ A), MeasurableSet E →
          μ E = borelCalculus hA (E.indicator (1 : spectrum ℝ A → ℂ))) ∧
        μ.integral (fun l => ((l : ℝ) : ℂ)) = A :=
  ⟨spectralMeasure hA, fun _E hE => spectralMeasure_apply hA hE,
    spectralMeasure_integral_id hA⟩

/-!
### Uniqueness
-/

/--
Two projection-valued measures on `σ(A)` integrating the identity to `A` agree on
polynomials.

Blueprint reference: `prpstn:pvm-agree-on-polynomials`.
-/
theorem pvm_integral_polynomial_eq (hA : IsSelfAdjoint A)
    (μ ν : ProjectionValuedMeasure (spectrum ℝ A) H)
    (hμ : μ.integral (fun l => ((l : ℝ) : ℂ)) = A)
    (hν : ν.integral (fun l => ((l : ℝ) : ℂ)) = A) (p : Polynomial ℂ) :
    μ.integral (fun l => p.eval ((l : ℝ) : ℂ)) =
      ν.integral (fun l => p.eval ((l : ℝ) : ℂ)) := by
  -- The self-adjointness of `A` is not needed for this argument: it holds for
  -- any compact spectrum, so `hA` only records the setting.
  have _hA : IsSelfAdjoint A := hA
  let F : Polynomial ℂ → spectrum ℝ A → ℂ := fun r l => r.eval ((l : ℝ) : ℂ)
  let idF : spectrum ℝ A → ℂ := fun l => ((l : ℝ) : ℂ)
  -- A polynomial in the coordinate is continuous on the compact `spectrum ℝ A`,
  -- hence bounded and measurable; `idF` and `1` are particular cases.
  have hpoly_mem : ∀ p : Polynomial ℂ, F p ∈ BddMeasurable (spectrum ℝ A) := by
    intro p
    have hcont : Continuous (F p) :=
      p.continuous.comp (Complex.continuous_ofReal.comp continuous_subtype_val)
    rw [mem_bddMeasurable]
    refine ⟨hcont.measurable, ?_⟩
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (f := F p) hcont.continuousOn
    exact ⟨C, fun x => hC x trivial⟩
  have hid_mem : idF ∈ BddMeasurable (spectrum ℝ A) := by
    have hcont : Continuous idF :=
      Complex.continuous_ofReal.comp continuous_subtype_val
    rw [mem_bddMeasurable]
    refine ⟨hcont.measurable, ?_⟩
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (f := idF) hcont.continuousOn
    exact ⟨C, fun x => hC x trivial⟩
  have hone_mem : (1 : spectrum ℝ A → ℂ) ∈ BddMeasurable (spectrum ℝ A) := by
    rw [mem_bddMeasurable]
    exact ⟨measurable_const, ⟨1, by intro x; simp⟩⟩
  -- constants
  have hconst (a : ℂ) : μ.integral (F (Polynomial.C a)) = ν.integral (F (Polynomial.C a)) := by
    have hμa : μ.integral (F (Polynomial.C a)) = a • (1 : H →L[ℂ] H) := by
      calc
        μ.integral (F (Polynomial.C a)) = μ.integral (fun _ : spectrum ℝ A => a) := by
          congr 1
          funext l
          simp [F, Polynomial.eval_C]
        _ = μ.integral (a • (1 : spectrum ℝ A → ℂ)) := by
          congr 1
          funext l
          simp
        _ = a • μ.integral (1 : spectrum ℝ A → ℂ) :=
          ProjectionValuedMeasure.integral_smul μ a hone_mem
        _ = a • (1 : H →L[ℂ] H) := by rw [ProjectionValuedMeasure.integral_one μ]
    have hνa : ν.integral (F (Polynomial.C a)) = a • (1 : H →L[ℂ] H) := by
      calc
        ν.integral (F (Polynomial.C a)) = ν.integral (fun _ : spectrum ℝ A => a) := by
          congr 1
          funext l
          simp [F, Polynomial.eval_C]
        _ = ν.integral (a • (1 : spectrum ℝ A → ℂ)) := by
          congr 1
          funext l
          simp
        _ = a • ν.integral (1 : spectrum ℝ A → ℂ) :=
          ProjectionValuedMeasure.integral_smul ν a hone_mem
        _ = a • (1 : H →L[ℂ] H) := by rw [ProjectionValuedMeasure.integral_one ν]
    exact hμa.trans hνa.symm
  -- sums
  have hadd (r s : Polynomial ℂ) :
      (μ.integral (F r) = ν.integral (F r)) →
      (μ.integral (F s) = ν.integral (F s)) →
      μ.integral (F (r + s)) = ν.integral (F (r + s)) := by
    intro hr hs
    have hF_add : F (r + s) = F r + F s := by
      funext l
      simp [F, Polynomial.eval_add]
    calc
      μ.integral (F (r + s)) = μ.integral (F r + F s) := by rw [hF_add]
      _ = μ.integral (F r) + μ.integral (F s) :=
        ProjectionValuedMeasure.integral_add μ (hpoly_mem r) (hpoly_mem s)
      _ = ν.integral (F r) + ν.integral (F s) := by rw [hr, hs]
      _ = ν.integral (F r + F s) :=
        (ProjectionValuedMeasure.integral_add ν (hpoly_mem r) (hpoly_mem s)).symm
      _ = ν.integral (F (r + s)) := by rw [← hF_add]
  -- monomial step: `C a * X ^ n` ↦ `C a * X ^ (n + 1)`
  have hmono (n : ℕ) (a : ℂ) :
      (μ.integral (F (Polynomial.C a * Polynomial.X ^ n)) =
        ν.integral (F (Polynomial.C a * Polynomial.X ^ n))) →
      μ.integral (F (Polynomial.C a * Polynomial.X ^ (n + 1))) =
        ν.integral (F (Polynomial.C a * Polynomial.X ^ (n + 1))) := by
    intro ih
    have hid_eq : μ.integral idF = ν.integral idF := hμ.trans hν.symm
    have hF_mon : F (Polynomial.C a * Polynomial.X ^ (n + 1)) =
        F (Polynomial.C a * Polynomial.X ^ n) * idF := by
      funext l
      simp [F, idF, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow,
        pow_succ, mul_assoc]
    calc
      μ.integral (F (Polynomial.C a * Polynomial.X ^ (n + 1)))
          = μ.integral (F (Polynomial.C a * Polynomial.X ^ n) * idF) := by rw [hF_mon]
      _ = μ.integral (F (Polynomial.C a * Polynomial.X ^ n)) * μ.integral idF :=
          ProjectionValuedMeasure.integral_mul μ
            (hpoly_mem (Polynomial.C a * Polynomial.X ^ n)) hid_mem
      _ = μ.integral (F (Polynomial.C a * Polynomial.X ^ n)) * ν.integral idF := by rw [hid_eq]
      _ = ν.integral (F (Polynomial.C a * Polynomial.X ^ n)) * ν.integral idF := by rw [ih]
      _ = ν.integral (F (Polynomial.C a * Polynomial.X ^ n) * idF) :=
          (ProjectionValuedMeasure.integral_mul ν
            (hpoly_mem (Polynomial.C a * Polynomial.X ^ n)) hid_mem).symm
      _ = ν.integral (F (Polynomial.C a * Polynomial.X ^ (n + 1))) := by rw [← hF_mon]
  exact Polynomial.induction_on (motive := fun q => μ.integral (F q) = ν.integral (F q))
    p hconst hadd hmono

/--
Two projection-valued measures on `σ(A)` integrating the identity to `A` agree on
continuous functions.

Blueprint reference: `prpstn:pvm-agree-on-continuous`.
-/
theorem pvm_integral_continuous_eq (hA : IsSelfAdjoint A)
    (μ ν : ProjectionValuedMeasure (spectrum ℝ A) H)
    (hμ : μ.integral (fun l => ((l : ℝ) : ℂ)) = A)
    (hν : ν.integral (fun l => ((l : ℝ) : ℂ)) = A) (g : C(spectrum ℝ A, ℂ)) :
    μ.integral (fun l => g l) = ν.integral (fun l => g l) := by
  classical
  -- The complex polynomials on `σ(A)` are dense in `C(σ(A), ℂ)` for the sup norm.
  have hdense : Dense {f : C(spectrum ℝ A, ℂ) |
      ∃ p : Polynomial ℂ, ∀ l : spectrum ℝ A, f l = p.eval ((l : ℝ) : ℂ)} :=
    dense_polynomial_spectrum A
  -- The map `f ↦ μ.integral (fun x => f x)` is 1-Lipschitz, hence continuous.
  have hcont : ∀ μ : ProjectionValuedMeasure (spectrum ℝ A) H,
      Continuous (fun f : C(spectrum ℝ A, ℂ) => μ.integral (fun x => f x)) := by
    intro μ
    refine (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
    intro f f'
    -- membership of continuous maps in `BddMeasurable`
    have hf : (fun x : spectrum ℝ A => f x) ∈ BddMeasurable (spectrum ℝ A) := by
      rw [mem_bddMeasurable]
      refine ⟨f.continuous.measurable, ‖f‖, fun x => ?_⟩
      simpa using ContinuousMap.norm_coe_le_norm (f := f) x
    have hf' : (fun x : spectrum ℝ A => f' x) ∈ BddMeasurable (spectrum ℝ A) := by
      rw [mem_bddMeasurable]
      refine ⟨f'.continuous.measurable, ‖f'‖, fun x => ?_⟩
      simpa using ContinuousMap.norm_coe_le_norm (f := f') x
    have hΔ : (fun x : spectrum ℝ A => f x - f' x) ∈ BddMeasurable (spectrum ℝ A) :=
      (BddMeasurable (spectrum ℝ A)).sub_mem hf hf'
    -- linearity of the integral applied to the difference `f - f'`
    have hlin : μ.integral (fun x => f x) - μ.integral (fun x => f' x) =
        μ.integral (fun x => f x - f' x) := by
      have hf'neg : (fun x : spectrum ℝ A => -f' x) ∈ BddMeasurable (spectrum ℝ A) :=
        (BddMeasurable (spectrum ℝ A)).neg_mem hf'
      have hneg : μ.integral (fun x => -f' x) = -(μ.integral (fun x => f' x)) := by
        have hsmul : μ.integral ((-1 : ℂ) • (fun x : spectrum ℝ A => f' x)) =
            (-1 : ℂ) • μ.integral (fun x => f' x) :=
          ProjectionValuedMeasure.integral_smul μ (-1) hf'
        calc
          μ.integral (fun x => -f' x) = μ.integral ((-1 : ℂ) • (fun x : spectrum ℝ A => f' x)) := by
            congr 1
            funext x
            simp
          _ = (-1 : ℂ) • μ.integral (fun x => f' x) := hsmul
          _ = -(μ.integral (fun x => f' x)) := by simp
      calc
        μ.integral (fun x => f x) - μ.integral (fun x => f' x)
            = μ.integral (fun x => f x) + μ.integral (fun x => -f' x) := by
              rw [sub_eq_add_neg, ← hneg]
        _ = μ.integral ((fun x : spectrum ℝ A => f x) + (fun x : spectrum ℝ A => -f' x)) :=
              (ProjectionValuedMeasure.integral_add μ hf hf'neg).symm
        _ = μ.integral (fun x => f x - f' x) := rfl
    -- the difference integral is bounded by the sup norm of `f - f'`
    have hbnd : dist (μ.integral (fun x => f x)) (μ.integral (fun x => f' x)) ≤ dist f f' := by
      calc
        dist (μ.integral (fun x => f x)) (μ.integral (fun x => f' x))
            = ‖μ.integral (fun x => f x) - μ.integral (fun x => f' x)‖ := by
              rw [dist_eq_norm]
        _ = ‖μ.integral (fun x => f x - f' x)‖ := by rw [hlin]
        _ ≤ ⨆ x, ‖f x - f' x‖ := ProjectionValuedMeasure.norm_integral_le μ hΔ
        _ ≤ ‖f - f'‖ := Real.iSup_le
              (fun x => by simpa using ContinuousMap.norm_coe_le_norm (f := f - f') x)
              (norm_nonneg (f - f'))
        _ = dist f f' := by simp [dist_eq_norm]
    simpa using hbnd
  -- `μ.integral` and `ν.integral` agree on the polynomials
  have hagree : ∀ f : C(spectrum ℝ A, ℂ),
      f ∈ {f : C(spectrum ℝ A, ℂ) |
        ∃ p : Polynomial ℂ, ∀ l : spectrum ℝ A, f l = p.eval ((l : ℝ) : ℂ)} →
        μ.integral (fun x => f x) = ν.integral (fun x => f x) := by
    rintro f ⟨p, hp⟩
    calc
      μ.integral (fun x => f x) = μ.integral (fun x => p.eval ((x : ℝ) : ℂ)) := by
        congr 1
        funext x
        exact hp x
      _ = ν.integral (fun x => p.eval ((x : ℝ) : ℂ)) :=
            pvm_integral_polynomial_eq hA μ ν hμ hν p
      _ = ν.integral (fun x => f x) := by
        congr 1
        funext x
        exact (hp x).symm
  exact congrFun (Continuous.ext_on hdense (hcont μ) (hcont ν) hagree) g

/--
Two projection-valued measures on `σ(A)` integrating the identity to `A` agree on
all bounded Borel functions.

Blueprint reference: `prpstn:pvm-agree-on-measurable`.
-/
theorem pvm_integral_bddMeasurable_eq (hA : IsSelfAdjoint A)
    (μ ν : ProjectionValuedMeasure (spectrum ℝ A) H)
    (hμ : μ.integral (fun l => ((l : ℝ) : ℂ)) = A)
    (hν : ν.integral (fun l => ((l : ℝ) : ℂ)) = A) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) :
    μ.integral f = ν.integral f := by
  classical
  let 𝒢 : Set (spectrum ℝ A → ℂ) :=
    {g | g ∈ BddMeasurable (spectrum ℝ A) ∧ μ.integral g = ν.integral g}
  have h𝒢 : IsBorelGenerating 𝒢 := by
    refine { bddMeasurable := ?_, smul_add_mem := ?_, continuous_mem := ?_, tendsto_mem := ?_ }
    · intro g hg
      exact hg.1
    · intro α β g k hg hk
      have hαg : α • g ∈ BddMeasurable (spectrum ℝ A) :=
        (BddMeasurable (spectrum ℝ A)).smul_mem α hg.1
      have hβk : β • k ∈ BddMeasurable (spectrum ℝ A) :=
        (BddMeasurable (spectrum ℝ A)).smul_mem β hk.1
      refine ⟨(BddMeasurable (spectrum ℝ A)).add_mem hαg hβk, ?_⟩
      calc
        μ.integral (α • g + β • k)
            = μ.integral (α • g) + μ.integral (β • k) :=
              ProjectionValuedMeasure.integral_add μ hαg hβk
        _ = α • μ.integral g + β • μ.integral k := by
              rw [ProjectionValuedMeasure.integral_smul μ α hg.1,
                ProjectionValuedMeasure.integral_smul μ β hk.1]
        _ = α • ν.integral g + β • ν.integral k := by
              rw [hg.2, hk.2]
        _ = ν.integral (α • g) + ν.integral (β • k) := by
              rw [← ProjectionValuedMeasure.integral_smul ν α hg.1,
                ← ProjectionValuedMeasure.integral_smul ν β hk.1]
        _ = ν.integral (α • g + β • k) :=
              (ProjectionValuedMeasure.integral_add ν hαg hβk).symm
    · intro g
      refine ⟨(continuous_mem_FClass hA g).1, ?_⟩
      let gc : C(spectrum ℝ A, ℂ) :=
        ⟨fun l => ((g l : ℝ) : ℂ), (Complex.continuous_ofReal.comp g.continuous)⟩
      exact pvm_integral_continuous_eq hA μ ν hμ hν gc
    · intro f g M hf hlim
      have hgB : g ∈ BddMeasurable (spectrum ℝ A) :=
        ⟨measurable_of_tendsto_pointwise (fun n => (hf n).1.1) hlim.tendsto,
          ⟨M, fun x => norm_le_of_tendsto hlim x⟩⟩
      refine ⟨hgB, ?_⟩
      have hlimit : ∀ ψ : H, ⟪ψ, μ.integral g ψ⟫_ℂ = ⟪ψ, ν.integral g ψ⟫_ℂ := by
        intro ψ
        have hconvμ : Tendsto (fun n => ⟪ψ, μ.integral (f n) ψ⟫_ℂ) atTop
            (𝓝 (⟪ψ, μ.integral g ψ⟫_ℂ)) := by
          have hBCT : Tendsto (fun n => ∫ x, f n x ∂(μ.assoc ψ)) atTop
              (𝓝 (∫ x, g x ∂(μ.assoc ψ))) :=
            tendsto_integral_of_boundedPointwiseLimit (μ := μ.assoc ψ)
              (hmeas := fun n => (hf n).1.1) hlim
          rw [← ProjectionValuedMeasure.inner_integral μ hgB ψ] at hBCT
          have hseq : (fun n => ⟪ψ, μ.integral (f n) ψ⟫_ℂ) =
              fun n => ∫ x, f n x ∂(μ.assoc ψ) := by
            funext n
            exact ProjectionValuedMeasure.inner_integral μ (hf n).1 ψ
          rw [← hseq] at hBCT
          exact hBCT
        have hconvν : Tendsto (fun n => ⟪ψ, ν.integral (f n) ψ⟫_ℂ) atTop
            (𝓝 (⟪ψ, ν.integral g ψ⟫_ℂ)) := by
          have hBCT : Tendsto (fun n => ∫ x, f n x ∂(ν.assoc ψ)) atTop
              (𝓝 (∫ x, g x ∂(ν.assoc ψ))) :=
            tendsto_integral_of_boundedPointwiseLimit (μ := ν.assoc ψ)
              (hmeas := fun n => (hf n).1.1) hlim
          rw [← ProjectionValuedMeasure.inner_integral ν hgB ψ] at hBCT
          have hseq : (fun n => ⟪ψ, ν.integral (f n) ψ⟫_ℂ) =
              fun n => ∫ x, f n x ∂(ν.assoc ψ) := by
            funext n
            exact ProjectionValuedMeasure.inner_integral ν (hf n).1 ψ
          rw [← hseq] at hBCT
          exact hBCT
        have hseq : (fun n => ⟪ψ, μ.integral (f n) ψ⟫_ℂ) =
            fun n => ⟪ψ, ν.integral (f n) ψ⟫_ℂ := by
          funext n
          exact congrArg (fun T : H →L[ℂ] H => ⟪ψ, T ψ⟫_ℂ) (hf n).2
        rw [hseq] at hconvμ
        exact tendsto_nhds_unique hconvμ hconvν
      let L : H →L[ℂ] H := μ.integral g - ν.integral g
      have hself : ∀ ψ : H, ⟪ψ, L ψ⟫_ℂ = 0 := by
        intro ψ
        rw [sub_apply, inner_sub_right]
        rw [hlimit ψ]
        simp
      have hself' : ∀ ψ : H, ⟪(L : H →ₗ[ℂ] H) ψ, ψ⟫_ℂ = 0 := by
        intro ψ
        rw [← inner_conj_symm]
        simp [hself ψ]
      have hL₀ : (L : H →ₗ[ℂ] H) = 0 :=
        (inner_map_self_eq_zero (L : H →ₗ[ℂ] H)).mp hself'
      have hL : L = 0 := by
        ext ψ
        simpa using congrFun (congrArg DFunLike.coe hL₀) ψ
      exact sub_eq_zero.mp hL
  have h𝒢_eq : 𝒢 = (BddMeasurable (spectrum ℝ A) : Set (spectrum ℝ A → ℂ)) :=
    h𝒢.eq_bddMeasurable
  have hf𝒢 : f ∈ 𝒢 := by
    rw [h𝒢_eq]
    exact hf
  exact hf𝒢.2

/--
A projection-valued measure on `σ(A)` integrating the identity to `A` is unique.

Blueprint reference: `thrm:hall-prblm-8.3.4`.
-/
theorem pvm_eq_of_integral_id_eq (hA : IsSelfAdjoint A)
    (μ ν : ProjectionValuedMeasure (spectrum ℝ A) H)
    (hμ : μ.integral (fun l => ((l : ℝ) : ℂ)) = A)
    (hν : ν.integral (fun l => ((l : ℝ) : ℂ)) = A) :
    ∀ E : Set (spectrum ℝ A), MeasurableSet E → μ E = ν E := by
  intro E hE
  have hf : E.indicator (1 : spectrum ℝ A → ℂ) ∈ BddMeasurable (spectrum ℝ A) := by
    constructor
    · exact Measurable.indicator measurable_const hE
    · refine ⟨1, fun x => ?_⟩
      by_cases h : x ∈ E <;> simp [Set.indicator, h]
  calc
    μ E = μ.integral (E.indicator (1 : spectrum ℝ A → ℂ)) := by
      rw [← μ.integral_indicator hE]
    _ = ν.integral (E.indicator (1 : spectrum ℝ A → ℂ)) := by
      exact pvm_integral_bddMeasurable_eq hA μ ν hμ hν hf
    _ = ν E := by
      rw [ν.integral_indicator hE]

/--
**The spectral theorem for bounded self-adjoint operators.** A self-adjoint
`A ∈ 𝓑(H)` admits a unique projection-valued measure on the Borel `σ`-algebra of
`σ(A)` with `∫ λ dμ^A(λ) = A`.

Existence is `spectralMeasure_integral_id` and uniqueness is
`pvm_eq_of_integral_id_eq`, so this node is proved from its parts.

Blueprint reference: `thrm:spectral-theorem-for-bounded-operators`.
-/
theorem existsUnique_spectralMeasure (hA : IsSelfAdjoint A) :
    ∃! μ : ProjectionValuedMeasure (spectrum ℝ A) H,
      μ.integral (fun l => ((l : ℝ) : ℂ)) = A := by
  refine ⟨spectralMeasure hA, spectralMeasure_integral_id hA, fun ν hν => ?_⟩
  refine ProjectionValuedMeasure.ext fun E => ?_
  by_cases hE : MeasurableSet E
  · exact pvm_eq_of_integral_id_eq hA ν (spectralMeasure hA) hν
      (spectralMeasure_integral_id hA) E hE
  · rw [ν.apply_of_not_measurableSet hE, (spectralMeasure hA).apply_of_not_measurableSet hE]

/--
**Functional calculus.** For a bounded Borel `f` on `σ(A)`, the operator
`f(A) = ∫ f dμ^A`. By `borelCalculus_eq_integral` this agrees with the operator
obtained from the quadratic form `Q_f` in `Physicslib4/Spectral/BorelCalculus.lean`,
so the notation `f(A)` is unambiguous.

Blueprint reference: `def:functional-calculus`.
-/
noncomputable def functionalCalculus (hA : IsSelfAdjoint A) (f : spectrum ℝ A → ℂ) :
    H →L[ℂ] H :=
  (spectralMeasure hA).integral f

end Spectral
end Physicslib4
