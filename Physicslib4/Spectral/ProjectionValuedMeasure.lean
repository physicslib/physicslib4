/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Forms

/-!
# Projection-valued measures

A *projection-valued measure* on a measurable space `X` with values in the bounded
operators of a complex Hilbert space `H` is the object the spectral theorem
produces: a countably additive, multiplicative assignment of orthogonal
projections to measurable subsets of `X`.

## Main definitions

* `Physicslib4.Spectral.ProjectionValuedMeasure` — the blueprint's
  `μ : Ω(X) → 𝓑(H)`.
* `Physicslib4.Spectral.ProjectionValuedMeasure.assoc` — the positive finite
  scalar measure `μ_ψ : E ↦ ⟪ψ, μ E ψ⟫`.

## Main statements

* `Physicslib4.Spectral.ProjectionValuedMeasure.existsUnique_assoc` — `μ_ψ` is a
  well-defined positive, finite, real-valued measure.
* `Physicslib4.Spectral.ProjectionValuedMeasure.inner_eq_zero_of_disjoint`,
  `Physicslib4.Spectral.ProjectionValuedMeasure.norm_sq_eq_sum_of_partition` — the
  vectors `μ(Eᵢ)ψ` of a finite measurable partition are pairwise orthogonal and
  their squared norms add up to `‖ψ‖²`.
* `Physicslib4.Spectral.exists_isStarProjection_tendsto_partialSum` — a family of
  mutually annihilating projections sums to the projection onto the closed span of
  their ranges.

## Implementation notes

Following Mathlib's `MeasureTheory.VectorMeasure`, a `ProjectionValuedMeasure` is
a *total* function `Set X → H →L[ℂ] H` which is required to vanish on
non-measurable sets; this makes the object canonical and avoids carrying
measurability side conditions in the coercion.

The blueprint's countable additivity is stated as `HasSum`, Mathlib's unordered
summability. For a family of pairwise orthogonal projections this is equivalent to
convergence of the partial sums, which is the blueprint's formulation.

Two projection-valued measures are *equivalent* in the blueprint's sense exactly
when they are equal as functions on `Set X`, so no separate relation is introduced.
-/

namespace Physicslib4
namespace Spectral

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap MeasureTheory

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
A *projection-valued measure* on the measurable space `X` with values in `𝓑(H)`:
each set is sent to a bounded orthogonal projection, non-measurable sets to `0`,
all of `X` to the identity, the map is countably additive on pairwise disjoint
measurable families, and it is multiplicative on intersections.

The blueprint's `μ(∅) = 0` is not a field: it follows from `hasSum'` applied to the
constant family `E j = ∅`, so requiring it would put a derivable obligation on every
constructor.

Blueprint reference: `def:projection-valued-measure`.
-/
structure ProjectionValuedMeasure (X : Type*) [MeasurableSpace X] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The underlying assignment of operators to sets. -/
  toFun : Set X → H →L[ℂ] H
  /-- Every value is a bounded orthogonal projection. -/
  isStarProjection' : ∀ E : Set X, IsStarProjection (toFun E)
  /-- Non-measurable sets are sent to `0`, making the assignment canonical. -/
  notMeasurable' : ∀ E : Set X, ¬MeasurableSet E → toFun E = 0
  /-- All of `X` is sent to the identity operator. -/
  univ' : toFun Set.univ = 1
  /-- Countable additivity, in the norm topology of `H`. -/
  hasSum' : ∀ E : ℕ → Set X, (∀ j, MeasurableSet (E j)) →
    Pairwise (fun i j => Disjoint (E i) (E j)) →
    ∀ v : H, HasSum (fun j => toFun (E j) v) (toFun (⋃ j, E j) v)
  /-- Multiplicativity on intersections. -/
  inter' : ∀ E F : Set X, MeasurableSet E → MeasurableSet F →
    toFun (E ∩ F) = toFun E * toFun F

namespace ProjectionValuedMeasure

instance instFunLike : FunLike (ProjectionValuedMeasure X H) (Set X) (H →L[ℂ] H) where
  coe := ProjectionValuedMeasure.toFun
  coe_injective μ ν h := by cases μ; cases ν; congr

@[simp]
theorem coe_mk (f : Set X → H →L[ℂ] H) (h₁ h₂ h₃ h₄ h₅) :
    ⇑(ProjectionValuedMeasure.mk f h₁ h₂ h₃ h₄ h₅ : ProjectionValuedMeasure X H) = f := rfl

/-- Two projection-valued measures agreeing as functions on `Set X` are equal. -/
@[ext]
theorem ext {μ ν : ProjectionValuedMeasure X H} (h : ∀ E : Set X, μ E = ν E) : μ = ν :=
  DFunLike.ext _ _ h

/-! The five structure fields, restated through the `FunLike` coercion. -/

theorem isStarProjection_apply (μ : ProjectionValuedMeasure X H) (E : Set X) :
    IsStarProjection (μ E) := μ.isStarProjection' E

theorem apply_of_not_measurableSet (μ : ProjectionValuedMeasure X H) {E : Set X}
    (hE : ¬MeasurableSet E) : μ E = 0 := μ.notMeasurable' E hE

@[simp]
theorem apply_univ (μ : ProjectionValuedMeasure X H) : μ Set.univ = 1 := μ.univ'

theorem hasSum_apply (μ : ProjectionValuedMeasure X H) (E : ℕ → Set X)
    (hE : ∀ j, MeasurableSet (E j)) (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) (v : H) :
    HasSum (fun j => μ (E j) v) (μ (⋃ j, E j) v) := μ.hasSum' E hE hdisj v

theorem apply_inter (μ : ProjectionValuedMeasure X H) {E F : Set X} (hE : MeasurableSet E)
    (hF : MeasurableSet F) : μ (E ∩ F) = μ E * μ F := μ.inter' E F hE hF

/--
For every `ψ ∈ H` there is a unique positive finite measure `μ_ψ` on `X` whose
value on a measurable set `E` is `⟪ψ, μ(E) ψ⟫`.

Blueprint reference: `thrm:projection-valued-measures-associated-measure`.
-/
theorem existsUnique_assoc (μ : ProjectionValuedMeasure X H) (ψ : H) :
    ∃! ν : Measure X, IsFiniteMeasure ν ∧
      ∀ E : Set X, MeasurableSet E → (ν E).toReal = (⟪ψ, μ E ψ⟫_ℂ).re := by
  -- `μ(∅) = 0` follows from countable additivity applied to the constant empty family.
  have hempty : μ (∅ : Set X) = 0 := by
    ext v
    have hsum : Summable (fun _ : ℕ => μ (∅ : Set X) v) :=
      (μ.hasSum_apply (fun _ : ℕ => (∅ : Set X)) (by intro _; exact MeasurableSet.empty)
        (by intro k e; simp) v).summable
    exact (summable_const_iff (a := μ (∅ : Set X) v)).mp hsum
  -- The value `⟪ψ, μ E ψ⟫` is real and non-negative for every measurable `E`:
  -- `μ E` is an orthogonal projection, so `⟪ψ, μ E ψ⟫ = ⟪μ E ψ, μ E ψ⟫ ≥ 0`.
  have hreal_nonneg : ∀ E : Set X, MeasurableSet E → 0 ≤ (⟪ψ, μ E ψ⟫_ℂ).re := by
    intro E hE
    have hstar : star (μ E) = μ E := (μ.isStarProjection_apply E).isSelfAdjoint
    have hadj : (μ E).adjoint = μ E := by
      rw [← ContinuousLinearMap.star_eq_adjoint (μ E)]
      exact hstar
    have hidem : μ E * μ E = μ E := (μ.isStarProjection_apply E).isIdempotentElem
    have hsq : ⟪ψ, μ E ψ⟫_ℂ = ⟪μ E ψ, μ E ψ⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right (μ E) ψ (μ E ψ)]
      rw [hadj]
      rw [show μ E (μ E ψ) = μ E ψ by
        simpa using congrArg (fun T : H →L[ℂ] H => T ψ) hidem]
    rw [hsq]
    simpa using inner_self_nonneg (𝕜 := ℂ) (x := μ E ψ)
  -- The candidate measure: `ν E = ofReal ((⟪ψ, μ E ψ⟫_ℂ).re)` on measurable sets.
  let m : ∀ E : Set X, MeasurableSet E → ENNReal :=
    fun E _ => ENNReal.ofReal ((⟪ψ, μ E ψ⟫_ℂ).re)
  have hm0 : m ∅ MeasurableSet.empty = 0 := by
    simp [m, hempty]
  have hmU : ∀ ⦃f : ℕ → Set X⦄ (h : ∀ i, MeasurableSet (f i)),
      Pairwise (fun i j => Disjoint (f i) (f j)) →
        m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i) := by
    intro f hf hdisj
    have hsum' : HasSum (fun j => ⟪ψ, μ (f j) ψ⟫_ℂ) (⟪ψ, μ (⋃ j, f j) ψ⟫_ℂ) := by
      simpa using ContinuousLinearMap.hasSum (innerSL ℂ ψ) (μ.hasSum_apply f hf hdisj ψ)
    have hsum : HasSum (fun j : ℕ => (⟪ψ, μ (f j) ψ⟫_ℂ).re) ((⟪ψ, μ (⋃ j, f j) ψ⟫_ℂ).re) :=
      Complex.hasSum_re hsum'
    have hnonneg : ∀ j : ℕ, 0 ≤ (⟪ψ, μ (f j) ψ⟫_ℂ).re := fun j => hreal_nonneg (f j) (hf j)
    simp only [m]
    rw [← hsum.tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg hnonneg hsum.summable
  let ν : Measure X := Measure.ofMeasurable m hm0 hmU
  have hν_apply : ∀ (E : Set X), MeasurableSet E → ν E = ENNReal.ofReal ((⟪ψ, μ E ψ⟫_ℂ).re) := by
    intro E hE
    rw [show ν = Measure.ofMeasurable m hm0 hmU by rfl]
    exact Measure.ofMeasurable_apply (s := E) (hs := hE)
  have hν_fin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν_apply Set.univ MeasurableSet.univ]
    exact ENNReal.ofReal_lt_top
  have hν_prop : ∀ E : Set X, MeasurableSet E → (ν E).toReal = (⟪ψ, μ E ψ⟫_ℂ).re := by
    intro E hE
    rw [hν_apply E hE]
    exact ENNReal.toReal_ofReal (hreal_nonneg E hE)
  refine ⟨ν, ⟨hν_fin, hν_prop⟩, ?_⟩
  intro ν' hν'
  haveI : IsFiniteMeasure ν' := hν'.1
  apply Measure.ext
  intro E hE
  have hν'E_ne_top : ν' E ≠ ⊤ := MeasureTheory.measure_ne_top ν' E
  calc
    ν' E = ENNReal.ofReal (ν' E).toReal := (ENNReal.ofReal_toReal hν'E_ne_top).symm
    _ = ENNReal.ofReal ((⟪ψ, μ E ψ⟫_ℂ).re) := by rw [hν'.2 E hE]
    _ = ν E := (hν_apply E hE).symm

/--
The positive finite measure `μ_ψ : E ↦ ⟪ψ, μ(E) ψ⟫` associated with a
projection-valued measure `μ` and a vector `ψ`.
-/
noncomputable def assoc (μ : ProjectionValuedMeasure X H) (ψ : H) : Measure X :=
  (existsUnique_assoc μ ψ).choose

instance (μ : ProjectionValuedMeasure X H) (ψ : H) : IsFiniteMeasure (μ.assoc ψ) :=
  (existsUnique_assoc μ ψ).choose_spec.1.1

theorem assoc_apply (μ : ProjectionValuedMeasure X H) (ψ : H) {E : Set X}
    (hE : MeasurableSet E) : ((μ.assoc ψ) E).toReal = (⟪ψ, μ E ψ⟫_ℂ).re :=
  (existsUnique_assoc μ ψ).choose_spec.1.2 E hE

/--
For a finite pairwise disjoint measurable family `E₁, …, Eₙ`, the vectors `μ(Eᵢ)ψ`
are pairwise orthogonal.

The blueprint additionally assumes that the `Eᵢ` cover `X`; that hypothesis is used
only for the norm identity `norm_sq_eq_sum_of_partition`, not here, so it is omitted.

Blueprint reference: `lmm:lemma2-of-operator-valued-integration` (part 1).
-/
theorem inner_eq_zero_of_disjoint (μ : ProjectionValuedMeasure X H) {n : ℕ} (E : Fin n → Set X)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (ψ : H) {i j : Fin n} (hij : i ≠ j) : ⟪μ (E i) ψ, μ (E j) ψ⟫_ℂ = 0 := by
  have hempty : μ (∅ : Set X) = 0 := by
    ext v
    have hsum : Summable (fun _ : ℕ => μ (∅ : Set X) v) :=
      (μ.hasSum_apply (fun _ : ℕ => (∅ : Set X)) (by intro _; exact MeasurableSet.empty)
        (by intro k e; simp) v).summable
    exact (summable_const_iff (a := μ (∅ : Set X) v)).mp hsum
  have hdisji : E i ∩ E j = ∅ := by
    simpa [Set.disjoint_iff_inter_eq_empty] using hdisj hij
  have hstar : star (μ (E i)) = μ (E i) :=
    (μ.isStarProjection_apply (E i)).isSelfAdjoint
  have hadj : (μ (E i)).adjoint = μ (E i) := by
    rw [← ContinuousLinearMap.star_eq_adjoint (μ (E i))]
    exact hstar
  rw [← ContinuousLinearMap.adjoint_inner_right (μ (E i)) ψ (μ (E j) ψ)]
  rw [hadj]
  have hcomp : μ (E i) (μ (E j) ψ) = (μ (E i) * μ (E j)) ψ := by rfl
  rw [hcomp]
  rw [← μ.apply_inter (hE i) (hE j)]
  rw [hdisji]
  simp [hempty]

/--
For a finite measurable partition `E₁, …, Eₙ` of `X`, `‖ψ‖² = ∑ᵢ ‖μ(Eᵢ)ψ‖²`.

Blueprint reference: `lmm:lemma2-of-operator-valued-integration` (part 2).
-/
theorem norm_sq_eq_sum_of_partition (μ : ProjectionValuedMeasure X H) {n : ℕ} (E : Fin n → Set X)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : (⋃ i, E i) = Set.univ) (ψ : H) :
    ‖ψ‖ ^ 2 = ∑ i, ‖μ (E i) ψ‖ ^ 2 := by
  have hempty2 : μ (∅ : Set X) = 0 := by
    ext v
    have hsum : Summable (fun _ : ℕ => μ (∅ : Set X) v) :=
      (μ.hasSum_apply (fun _ : ℕ => (∅ : Set X)) (by intro _; exact MeasurableSet.empty)
        (by intro k e; simp) v).summable
    exact (summable_const_iff (a := μ (∅ : Set X) v)).mp hsum
  let E' : ℕ → Set X := fun k => if hk : k < n then E ⟨k, hk⟩ else ∅
  have hE'meas : ∀ k : ℕ, MeasurableSet (E' k) := by
    intro k
    by_cases hk : k < n
    · simpa [E', hk] using hE ⟨k, hk⟩
    · simpa [E', hk] using MeasurableSet.empty
  have hE'disj : Pairwise (fun k l => Disjoint (E' k) (E' l)) := by
    intro k l hkl
    by_cases hk : k < n
    · by_cases hl : l < n
      · have hne : (⟨k, hk⟩ : Fin n) ≠ (⟨l, hl⟩ : Fin n) := by
          intro h
          exact hkl (congrArg Fin.val h)
        simpa [E', hk, hl] using
          (hdisj (i := (⟨k, hk⟩ : Fin n)) (j := (⟨l, hl⟩ : Fin n)) hne)
      · simpa [E', hl] using Set.disjoint_empty (E' k)
    · simpa [E', hk] using Set.empty_disjoint (E' l)
  have hunion : (⋃ k : ℕ, E' k) = ⋃ i, E i := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨k, hx⟩
      by_cases hklt : k < n
      · rw [Set.mem_iUnion]
        exact ⟨⟨k, hklt⟩, by simpa [E', hklt] using hx⟩
      · exact False.elim (by simpa [E', hklt] using hx)
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hx⟩
      rw [Set.mem_iUnion]
      exact ⟨i.1, by simpa [E', i.isLt] using hx⟩
  have hfinite : ∀ k : ℕ, n ≤ k → μ (E' k) ψ = 0 := by
    intro k hk
    have hnot : ¬ k < n := not_lt_of_ge hk
    have hEq : E' k = (∅ : Set X) := by
      simp [E', hnot]
    simp [hEq, hempty2]
  have htsum : (∑ k ∈ Finset.range n, μ (E' k) ψ) = μ (⋃ k : ℕ, E' k) ψ := by
    have hts : (∑' k, μ (E' k) ψ) = μ (⋃ k, E' k) ψ :=
      (μ.hasSum_apply E' hE'meas hE'disj ψ).tsum_eq
    have hfin : (∑' k, μ (E' k) ψ) = ∑ k ∈ Finset.range n, μ (E' k) ψ := by
      exact tsum_eq_sum (s := Finset.range n) (f := fun k => μ (E' k) ψ) (by
        intro k hk
        exact hfinite k (Nat.ge_of_not_lt (by simpa using hk)))
    rw [← hfin, hts]
  have hbrid : (∑ i : Fin n, μ (E i) ψ) = ∑ k ∈ Finset.range n, μ (E' k) ψ := by
    let f0 : ℕ → H := fun k => if hk : k < n then μ (E ⟨k, hk⟩) ψ else 0
    calc
      (∑ i : Fin n, μ (E i) ψ) = ∑ i : Fin n, f0 i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [f0, i.2]
      _ = ∑ k ∈ Finset.range n, f0 k := by
        simpa using (Fin.sum_univ_eq_sum_range f0 n)
      _ = ∑ k ∈ Finset.range n, μ (E' k) ψ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        simp [f0, E', hklt]
  have hsumFin : (∑ i : Fin n, μ (E i) ψ) = ψ := by
    calc
      (∑ i : Fin n, μ (E i) ψ) = ∑ k ∈ Finset.range n, μ (E' k) ψ := hbrid
      _ = μ (⋃ k : ℕ, E' k) ψ := htsum
      _ = ψ := by
        rw [hunion, hcover]
        simp
  let a : Fin n → H := fun i => μ (E i) ψ
  have hsumA : (∑ i : Fin n, a i) = ψ := by simpa [a] using hsumFin
  have horth : ∀ i j : Fin n, i ≠ j → ⟪a i, a j⟫_ℂ = 0 := by
    intro i j hij
    simpa [a] using inner_eq_zero_of_disjoint μ E hE hdisj ψ hij
  have hExp : (⟪∑ i : Fin n, a i, ∑ j : Fin n, a j⟫_ℂ : ℂ) = ∑ i : Fin n, ⟪a i, a i⟫_ℂ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      ⟪a i, ∑ j : Fin n, a j⟫_ℂ = ∑ j : Fin n, ⟪a i, a j⟫_ℂ := by
        exact inner_sum (Finset.univ : Finset (Fin n)) a (a i)
      _ = ⟪a i, a i⟫_ℂ := by
        exact Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n => ⟪a i, a j⟫_ℂ) i
          (by intro j hj hji; exact horth i j (Ne.symm hji))
          (by intro h; exact (h (Finset.mem_univ i)).elim)
  have hc : (‖ψ‖ : ℂ) ^ 2 = ∑ i : Fin n, (‖a i‖ : ℂ) ^ 2 := by
    calc
      (‖ψ‖ : ℂ) ^ 2 = ⟪ψ, ψ⟫_ℂ := (inner_self_eq_norm_sq_to_K ψ).symm
      _ = ⟪∑ i : Fin n, a i, ∑ j : Fin n, a j⟫_ℂ := by rw [← hsumA]
      _ = ∑ i : Fin n, ⟪a i, a i⟫_ℂ := hExp
      _ = ∑ i : Fin n, (‖a i‖ : ℂ) ^ 2 := by simp [inner_self_eq_norm_sq_to_K]
  have hreal : ‖ψ‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
    exact_mod_cast hc
  simpa [a] using hreal

end ProjectionValuedMeasure

/-!
### Sums of mutually annihilating projections
-/

/--
The partial sums `∑_{i<n} Pᵢ ψ` of a family of mutually annihilating orthogonal
projections converge in `H`.

Blueprint reference: `prpstn:orthogonal-sum-converges`.
-/
theorem exists_tendsto_partialSum_of_isStarProjection {P : ℕ → H →L[ℂ] H}
    (hP : ∀ i, IsStarProjection (P i)) (horth : ∀ i j, i ≠ j → P i * P j = 0) (ψ : H) :
    ∃ l : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P i ψ) atTop (𝓝 l) := by
  let S : ℕ → H →L[ℂ] H := fun n => ∑ i ∈ Finset.range n, P i
  let s : ℕ → H := fun n => ∑ i ∈ Finset.range n, P i ψ
  let a : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, ‖P i ψ‖ ^ 2
  have happly : ∀ n : ℕ, (S n) ψ = s n := by
    intro n
    simp [S, s]
  -- Each partial-sum operator `S n` is itself a star projection.
  have hSstar : ∀ i : ℕ, star (P i) = P i := fun i => (hP i).isSelfAdjoint
  have hSproj : ∀ n : ℕ, IsStarProjection (S n) := by
    intro n
    refine ⟨?_, ?_⟩
    · change S n * S n = S n
      calc
        S n * S n = (∑ i ∈ Finset.range n, P i) * (∑ j ∈ Finset.range n, P j) := by simp [S]
        _ = ∑ i ∈ Finset.range n, P i * (∑ j ∈ Finset.range n, P j) := by
          rw [Finset.sum_mul]
        _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (P i) * (P j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = ∑ i ∈ Finset.range n, (P i) * (P i) := by
          apply Finset.sum_congr rfl
          intro i hi
          refine Finset.sum_eq_single (s := Finset.range n)
            (f := fun j => (P i) * (P j)) i ?_ ?_
          · intro j hj hji
            simpa using horth i j (Ne.symm hji)
          · intro h
            exact False.elim (h hi)
        _ = ∑ i ∈ Finset.range n, P i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hP i).isIdempotentElem
        _ = S n := by simp [S]
    · change star (S n) = S n
      calc
        star (S n) = star (∑ i ∈ Finset.range n, P i) := by rfl
        _ = ∑ i ∈ Finset.range n, star (P i) := by simp [star_sum]
        _ = ∑ i ∈ Finset.range n, P i := by simp [hSstar]
        _ = S n := by simp [S]
  -- The vectors `P i ψ` are pairwise orthogonal.
  have horthVec : ∀ {i j : ℕ}, i ≠ j → ⟪P i ψ, P j ψ⟫_ℂ = 0 := by
    intro i j hij
    have hadj : (P i).adjoint = P i := by
      rw [← ContinuousLinearMap.star_eq_adjoint (P i)]
      exact hSstar i
    calc
      ⟪P i ψ, P j ψ⟫_ℂ = ⟪ψ, (P i).adjoint (P j ψ)⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right (P i) ψ (P j ψ)]
      _ = ⟪ψ, P i (P j ψ)⟫_ℂ := by rw [hadj]
      _ = ⟪ψ, (P i * P j) ψ⟫_ℂ := rfl
      _ = 0 := by
        rw [horth i j hij]
        simp
  -- Pythagoras on every finite set.
  have hnorm2 : ∀ t : Finset ℕ, (∑ i ∈ t, ‖P i ψ‖ ^ 2) = ‖∑ i ∈ t, P i ψ‖ ^ 2 := by
    intro t
    have hc : (‖∑ i ∈ t, P i ψ‖ : ℂ) ^ 2 = ∑ i ∈ t, (‖P i ψ‖ : ℂ) ^ 2 := by
      calc
        (‖∑ i ∈ t, P i ψ‖ : ℂ) ^ 2 = ⟪∑ i ∈ t, P i ψ, ∑ j ∈ t, P j ψ⟫_ℂ := by
          exact (inner_self_eq_norm_sq_to_K (∑ i ∈ t, P i ψ)).symm
        _ = ∑ i ∈ t, ⟪P i ψ, P i ψ⟫_ℂ := by
          calc
            ⟪∑ i ∈ t, P i ψ, ∑ j ∈ t, P j ψ⟫_ℂ = ∑ i ∈ t, ⟪P i ψ, ∑ j ∈ t, P j ψ⟫_ℂ := by
              rw [sum_inner]
            _ = ∑ i ∈ t, ∑ j ∈ t, ⟪P i ψ, P j ψ⟫_ℂ := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [inner_sum]
            _ = ∑ i ∈ t, ⟪P i ψ, P i ψ⟫_ℂ := by
              apply Finset.sum_congr rfl
              intro i hi
              refine Finset.sum_eq_single (s := t)
                (f := fun j => ⟪P i ψ, P j ψ⟫_ℂ) i ?_ ?_
              · intro j hj hji
                exact horthVec (Ne.symm hji)
              · intro h
                exact False.elim (h hi)
        _ = ∑ i ∈ t, (‖P i ψ‖ : ℂ) ^ 2 := by
          simp [inner_self_eq_norm_sq_to_K]
    exact_mod_cast hc.symm
  have hsq : ∀ n : ℕ, ‖s n‖ ^ 2 = a n := by
    intro n
    calc
      ‖s n‖ ^ 2 = ‖∑ i ∈ Finset.range n, P i ψ‖ ^ 2 := by simp [s]
      _ = ∑ i ∈ Finset.range n, ‖P i ψ‖ ^ 2 := (hnorm2 (Finset.range n)).symm
      _ = a n := by simp [a]
  -- `a n` is bounded by the projection bound on `S n`.
  have hbdd : ∀ n : ℕ, a n ≤ ‖ψ‖ ^ 2 := by
    intro n
    calc
      a n = ‖s n‖ ^ 2 := (hsq n).symm
      _ ≤ ‖ψ‖ ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg (s n))
          (by simpa [happly] using norm_apply_le_of_isStarProjection (hSproj n) ψ) 2
  -- `a` is monotone and bounded, so it converges; in particular its
  -- differences are arbitrarily small.
  have hmono : Monotone a := by
    intro n m hnm
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by simpa using Finset.range_mono hnm)
      (fun i hi hmem => sq_nonneg (‖P i ψ‖))
  have hbddA : BddAbove (Set.range a) := by
    refine ⟨‖ψ‖ ^ 2, ?_⟩
    rintro y ⟨j, rfl⟩
    exact hbdd j
  have hlim : Tendsto a atTop (𝓝 (⨆ i, a i)) :=
    tendsto_atTop_ciSup (f := a) hmono hbddA
  have htailR : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dist (a n) (a m) < ε := by
    intro ε hε
    rcases (Metric.tendsto_atTop.mp hlim) (ε / 2) (by positivity) with ⟨N, hN⟩
    refine ⟨N, fun n hn m hm => ?_⟩
    have hn' : dist (a n) (⨆ j, a j) < ε / 2 := hN n hn
    have hm' : dist (a m) (⨆ j, a j) < ε / 2 := hN m hm
    have htr : dist (a n) (a m) ≤ dist (a n) (⨆ j, a j) + dist (⨆ j, a j) (a m) :=
      dist_triangle (a n) (⨆ j, a j) (a m)
    have h2 : dist (⨆ j, a j) (a m) < ε / 2 := by simpa [dist_comm] using hm'
    have hsum : dist (a n) (⨆ j, a j) + dist (⨆ j, a j) (a m) < ε / 2 + ε / 2 :=
      add_lt_add hn' h2
    exact lt_of_le_of_lt htr (by linarith)
  -- Tail estimate for `s`: `‖s m - s n‖² = a m - a n` when `n ≤ m`.
  have htail : ∀ {n m : ℕ}, n ≤ m → ‖s m - s n‖ ^ 2 = a m - a n := by
    intro n m hnm
    have htl : s m - s n = ∑ i ∈ Finset.Ico n m, P i ψ := by
      have hx : (∑ i ∈ Finset.Ico n m, P i ψ) =
          (∑ i ∈ Finset.range m, P i ψ) - (∑ i ∈ Finset.range n, P i ψ) :=
        Finset.sum_Ico_eq_sub (fun i => P i ψ) (h := hnm)
      simpa [s] using hx.symm
    calc
      ‖s m - s n‖ ^ 2 = ‖∑ i ∈ Finset.Ico n m, P i ψ‖ ^ 2 := by rw [htl]
      _ = ∑ i ∈ Finset.Ico n m, ‖P i ψ‖ ^ 2 := (hnorm2 (Finset.Ico n m)).symm
      _ = a m - a n := by
        rw [Finset.sum_Ico_eq_sub (fun i => ‖P i ψ‖ ^ 2) (h := hnm)]
  have hnormAbs : ∀ {n m : ℕ}, ‖s n - s m‖ ^ 2 = |a n - a m| := by
    intro n m
    rcases le_total n m with hnm | hnm
    · calc
        ‖s n - s m‖ ^ 2 = ‖s m - s n‖ ^ 2 := by rw [norm_sub_rev]
        _ = a m - a n := htail hnm
        _ = |a m - a n| := by
          rw [abs_of_nonneg (sub_nonneg.mpr (hmono hnm))]
        _ = |a n - a m| := by
          rw [abs_sub_comm]
    · calc
        ‖s n - s m‖ ^ 2 = a n - a m := htail hnm
        _ = |a n - a m| := by
          rw [abs_of_nonneg (sub_nonneg.mpr (hmono hnm))]
  -- The partial sums are Cauchy, hence converge by completeness.
  have hcauchy_s : CauchySeq s := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    rcases htailR (ε ^ 2) hε2 with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    have hd : |a m - a n| < ε ^ 2 := hN m hm n hn
    rw [dist_eq_norm]
    have hsqe : ‖s m - s n‖ ^ 2 < ε ^ 2 := by
      calc
        ‖s m - s n‖ ^ 2 = |a m - a n| := hnormAbs (n := m) (m := n)
        _ < ε ^ 2 := hd
    have hlt : ‖s m - s n‖ < ε := by
      have := (sq_lt_sq).mp hsqe
      rw [abs_of_nonneg (norm_nonneg (s m - s n))] at this
      rwa [abs_of_pos hε] at this
    exact hlt
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy_s
  refine ⟨l, ?_⟩
  simpa [s] using hl

/--
The pointwise limit of the partial sums of a family of mutually annihilating
orthogonal projections is again a bounded orthogonal projection.

Blueprint reference: `prpstn:orthogonal-sum-is-projection`.
-/
theorem exists_isStarProjection_tendsto_partialSum' {P : ℕ → H →L[ℂ] H}
    (hP : ∀ i, IsStarProjection (P i)) (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    ∃ Q : H →L[ℂ] H, IsStarProjection Q ∧
      ∀ ψ : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P i ψ) atTop (𝓝 (Q ψ)) := by
  let S : ℕ → H →L[ℂ] H := fun n => ∑ i ∈ Finset.range n, P i
  -- The product of two partial sums collapses to the smaller one:
  -- `S n * S m = S n` whenever `n ≤ m`.
  have hSSle : ∀ {m n : ℕ}, n ≤ m → S n * S m = S n := by
    intro m n h
    calc
      S n * S m = (∑ i ∈ Finset.range n, P i) * (∑ j ∈ Finset.range m, P j) := by
        simp [S]
      _ = ∑ i ∈ Finset.range n, P i * (∑ j ∈ Finset.range m, P j) := by
        rw [Finset.sum_mul]
      _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, P i * P j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range n, P i := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          (∑ j ∈ Finset.range m, P i * P j) = P i * P i := by
            refine Finset.sum_eq_single (s := Finset.range m)
              (f := fun j : ℕ => P i * P j) i ?_ ?_
            · intro j hj hji
              exact horth i j (Ne.symm hji)
            · intro hni
              exact False.elim (hni (Finset.mem_range.mpr
                (lt_of_lt_of_le (Finset.mem_range.mp hi) h)))
          _ = P i := (hP i).isIdempotentElem
      _ = S n := by simp [S]
  -- Each partial sum is again a bounded orthogonal projection.
  have hS_proj : ∀ n : ℕ, IsStarProjection (S n) := by
    intro n
    constructor
    · exact hSSle (m := n) (n := n) le_rfl
    · change star (S n) = S n
      have hstar_sum : ∀ m : ℕ,
          star (∑ i ∈ Finset.range m, P i) = ∑ i ∈ Finset.range m, star (P i) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
            rw [star_add, ih]
      calc
        star (S n) = star (∑ i ∈ Finset.range n, P i) := by simp [S]
        _ = ∑ i ∈ Finset.range n, star (P i) := hstar_sum n
        _ = ∑ i ∈ Finset.range n, P i := by
          apply Finset.sum_congr rfl
          intro i _
          exact (hP i).isSelfAdjoint
        _ = S n := by simp [S]
  -- The partial sums are norm-decreasing.
  have hb_norm : ∀ n : ℕ, ∀ ψ : H, ‖S n ψ‖ ≤ ‖ψ‖ := by
    intro n ψ
    exact norm_apply_le_of_isStarProjection (hS_proj n) ψ
  -- The pointwise limit of the partial sums, as a raw function `f`.
  let f : H → H := fun ψ =>
    Classical.choose (exists_tendsto_partialSum_of_isStarProjection hP horth ψ)
  have hf : ∀ ψ : H, Tendsto (fun n : ℕ => S n ψ) atTop (𝓝 (f ψ)) := by
    intro ψ
    simpa [S] using
      (Classical.choose_spec (exists_tendsto_partialSum_of_isStarProjection hP horth ψ))
  -- The limit is linear and norm-decreasing.
  have hf_add : ∀ φ ψ : H, f (φ + ψ) = f φ + f ψ := by
    intro φ ψ
    refine tendsto_nhds_unique (hf (φ + ψ)) ?_
    exact Tendsto.congr (fun n => (map_add (S n) φ ψ).symm) ((hf φ).add (hf ψ))
  have hf_smul : ∀ (c : ℂ) (ψ : H), f (c • ψ) = c • f ψ := by
    intro c ψ
    refine tendsto_nhds_unique (hf (c • ψ)) ?_
    exact Tendsto.congr (fun n => (map_smul (S n) c ψ).symm) (tendsto_const_nhds.smul (hf ψ))
  have hf_bound : ∀ ψ : H, ‖f ψ‖ ≤ ‖ψ‖ := by
    intro ψ
    exact le_of_tendsto ((hf ψ).norm)
      (Eventually.of_forall fun n => hb_norm n ψ)
  -- Package the pointwise limit as a bounded operator `Q`.
  let A : H →ₗ[ℂ] H := { toFun := f, map_add' := hf_add, map_smul' := hf_smul }
  let Q : H →L[ℂ] H := LinearMap.mkContinuous A 1 (fun x : H => by
    simpa [A] using hf_bound x)
  have hQapply : ∀ ψ : H, Q ψ = f ψ := by
    intro ψ
    simp [Q, LinearMap.mkContinuous_apply, A]
  have hQlim : ∀ ψ : H, Tendsto (fun n : ℕ => S n ψ) atTop (𝓝 (Q ψ)) := by
    intro ψ
    simpa [hQapply ψ] using hf ψ
  -- `S k` acts as the identity on the pieces of `Q ψ`:
  -- `S k (Q ψ) = S k ψ`.
  have happly : ∀ (k : ℕ) (ψ : H), S k (Q ψ) = S k ψ := by
    intro k ψ
    have h1 : Tendsto (fun m : ℕ => S k (S m ψ)) atTop (𝓝 (S k (Q ψ))) :=
      ((S k).continuous.tendsto (Q ψ)).comp (hQlim ψ)
    have h2 : Tendsto (fun m : ℕ => S k (S m ψ)) atTop (𝓝 (S k ψ)) := by
      have hEv : (fun m : ℕ => S k (S m ψ)) =ᶠ[atTop] (fun _ : ℕ => S k ψ) := by
        exact Filter.eventually_atTop.mpr ⟨k, fun m hk => by
          calc
            S k (S m ψ) = (S k * S m) ψ := by rw [← mul_apply_eq_comp]
            _ = S k ψ := by rw [hSSle hk]⟩
      exact Tendsto.congr' hEv.symm (tendsto_const_nhds (x := S k ψ))
    exact tendsto_nhds_unique h1 h2
  -- `Q` is idempotent.
  have hQQ : Q * Q = Q := by
    ext ψ
    rw [mul_apply_eq_comp]
    refine tendsto_nhds_unique (hQlim (Q ψ)) ?_
    exact Tendsto.congr (fun k : ℕ => (happly k ψ).symm) (hQlim ψ)
  -- `Q` is self-adjoint: the inner products of the partial sums already agree.
  have hpair : ∀ (φ ψ : H) (k : ℕ), ⟪S k φ, ψ⟫_ℂ = ⟪φ, S k ψ⟫_ℂ := by
    intro φ ψ k
    calc
      ⟪S k φ, ψ⟫_ℂ = ⟪∑ i ∈ Finset.range k, P i φ, ψ⟫_ℂ := by
        rw [show (S k) φ = ∑ i ∈ Finset.range k, P i φ by simp [S]]
      _ = ∑ i ∈ Finset.range k, ⟪P i φ, ψ⟫_ℂ :=
        sum_inner (Finset.range k) (fun i => P i φ) ψ
      _ = ∑ i ∈ Finset.range k, ⟪φ, P i ψ⟫_ℂ := by
        apply Finset.sum_congr rfl
        intro i _
        have hadj : adjoint (P i) = P i := by
          rw [← ContinuousLinearMap.star_eq_adjoint (P i)]
          exact (hP i).isSelfAdjoint
        calc
          ⟪P i φ, ψ⟫_ℂ = ⟪φ, adjoint (P i) ψ⟫_ℂ := (adjoint_inner_right (P i) φ ψ).symm
          _ = ⟪φ, P i ψ⟫_ℂ := by rw [hadj]
      _ = ⟪φ, S k ψ⟫_ℂ := by
        rw [show (S k) ψ = ∑ i ∈ Finset.range k, P i ψ by simp [S]]
        exact (inner_sum (Finset.range k) (fun i => P i ψ) φ).symm
  have hSym : (Q : H →ₗ[ℂ] H).IsSymmetric := by
    intro φ ψ
    have hnet1 : Tendsto (fun k : ℕ => ⟪S k φ, ψ⟫_ℂ) atTop (𝓝 (⟪Q φ, ψ⟫_ℂ)) :=
      (hQlim φ).inner (tendsto_const_nhds (x := ψ))
    have hnet2 : Tendsto (fun k : ℕ => ⟪S k φ, ψ⟫_ℂ) atTop (𝓝 (⟪φ, Q ψ⟫_ℂ)) :=
      Tendsto.congr (fun k : ℕ => (hpair φ ψ k).symm)
        ((tendsto_const_nhds (x := φ)).inner (hQlim ψ))
    exact tendsto_nhds_unique hnet1 hnet2
  have hSAdj : IsSelfAdjoint Q :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := Q)).mpr hSym
  exact ⟨Q, ⟨hQQ, hSAdj⟩, fun ψ => by simpa [S] using hQlim ψ⟩

/--
The range of the limit projection is the smallest closed subspace containing the
ranges of the `Pᵢ`.

Blueprint reference: `prpstn:orthogonal-sum-range`.
-/
theorem range_eq_topologicalClosure_iSup_of_tendsto_partialSum {P : ℕ → H →L[ℂ] H}
    (hP : ∀ i, IsStarProjection (P i)) (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (Q : H →L[ℂ] H) (hQ : ∀ ψ : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P i ψ) atTop (𝓝 (Q ψ))) :
    LinearMap.range (Q : H →ₗ[ℂ] H) =
      (⨆ i, LinearMap.range ((P i : H →L[ℂ] H) : H →ₗ[ℂ] H)).topologicalClosure := by
  let R : ℕ → Submodule ℂ H := fun i => LinearMap.range ((P i : H →L[ℂ] H) : H →ₗ[ℂ] H)
  let V : Submodule ℂ H := ⨆ i, R i
  -- Part 1: the range of `Q` is contained in `V.topologicalClosure`.
  have hPart1 : LinearMap.range (Q : H →ₗ[ℂ] H) ≤ V.topologicalClosure := by
    intro x hx
    rcases LinearMap.mem_range.mp hx with ⟨y, hy⟩
    rw [← hy]
    have hS : ∀ n : ℕ, (∑ i ∈ Finset.range n, P i y) ∈ V := by
      intro n
      refine V.sum_mem ?_
      intro i hi
      exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range.mpr ⟨y, rfl⟩)
    exact mem_closure_of_tendsto (hQ y) (Eventually.of_forall hS)
  -- Part 2: the closure of `V` lies in the range of `Q`.
  obtain ⟨Q', hQ'proj, hQ'lim⟩ := exists_isStarProjection_tendsto_partialSum' hP horth
  have hQe : Q = Q' := by
    ext x
    exact tendsto_nhds_unique (hQ x) (hQ'lim x)
  have hQidem : Q * Q = Q := by
    calc
      Q * Q = Q' * Q' := by rw [hQe]
      _ = Q' := (hQ'proj).isIdempotentElem
      _ = Q := hQe.symm
  have hQclosed : IsClosed ((LinearMap.range (Q : H →ₗ[ℂ] H)) : Set H) := by
    exact ContinuousLinearMap.IsIdempotentElem.isClosed_range hQidem
  -- Every `P i` vector is fixed by the limit projection `Q`.
  have hFix : ∀ i : ℕ, ∀ x : H, Q (P i x) = P i x := by
    intro i x
    have hev : (fun n : ℕ => ∑ j ∈ Finset.range n, P j (P i x)) =ᶠ[atTop]
        (fun _ : ℕ => P i x) := by
      filter_upwards [eventually_gt_atTop i] with n hin
      calc
        (∑ j ∈ Finset.range n, P j (P i x)) = P i (P i x) := by
          refine Finset.sum_eq_single i ?h0 ?h1
          · intro b hb hbi
            have hz : (P b * P i) x = 0 := by
              simpa using congrArg (fun T : H →L[ℂ] H => T x) (horth b i hbi)
            rw [show (P b * P i) x = P b (P i x) by simp] at hz
            exact hz
          · intro hnot
            exact (hnot (Finset.mem_range.mpr hin)).elim
        _ = P i x := by
          have hid : P i * P i = P i := (show P i * P i = P i from (hP i).isIdempotentElem)
          simpa using congrArg (fun T : H →L[ℂ] H => T x) hid
    have hlim : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, P j (P i x)) atTop (𝓝 (Q (P i x))) :=
      hQ (P i x)
    have hconst : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, P j (P i x)) atTop (𝓝 (P i x)) :=
      Filter.Tendsto.congr' hev.symm (tendsto_const_nhds (x := P i x))
    exact tendsto_nhds_unique hlim hconst
  have hVQ : V ≤ LinearMap.range (Q : H →ₗ[ℂ] H) := by
    dsimp [V]
    apply iSup_le
    intro i x hx
    rcases LinearMap.mem_range.mp hx with ⟨z, hz⟩
    exact LinearMap.mem_range.mpr ⟨P i z, by rw [← hz]; exact hFix i z⟩
  exact le_antisymm hPart1 (Submodule.topologicalClosure_minimal V hVQ hQclosed)

/--
A family of mutually annihilating orthogonal projections sums pointwise to the
orthogonal projection onto the smallest closed subspace containing all their
ranges.

This blueprint node is exactly the conjunction of
`exists_isStarProjection_tendsto_partialSum'` and
`range_eq_topologicalClosure_iSup_of_tendsto_partialSum`, so it is proved from them
rather than restated.

Blueprint reference: `lmm:lemma-4`.
-/
theorem exists_isStarProjection_tendsto_partialSum {P : ℕ → H →L[ℂ] H}
    (hP : ∀ i, IsStarProjection (P i)) (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    ∃ Q : H →L[ℂ] H, IsStarProjection Q ∧
      (∀ ψ : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P i ψ) atTop (𝓝 (Q ψ))) ∧
        LinearMap.range (Q : H →ₗ[ℂ] H) =
          (⨆ i, LinearMap.range ((P i : H →L[ℂ] H) : H →ₗ[ℂ] H)).topologicalClosure := by
  obtain ⟨Q, hQproj, hQlim⟩ := exists_isStarProjection_tendsto_partialSum' hP horth
  exact ⟨Q, hQproj, hQlim,
    range_eq_topologicalClosure_iSup_of_tendsto_partialSum hP horth Q hQlim⟩

/--
A family of mutually annihilating orthogonal projections is unconditionally
summable, and the (`HasSum`) value is the pointwise limit of the partial sums
over `Finset.range`.

Blueprint reference: `prpstn:mua-countably-additive`.
-/
theorem hasSum_of_isStarProjection_orthogonal {P : ℕ → H →L[ℂ] H}
    (hP : ∀ i, IsStarProjection (P i)) (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (Q : H →L[ℂ] H)
    (hQ : ∀ ψ : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P i ψ) atTop (𝓝 (Q ψ)))
    (ψ : H) : HasSum (fun i => P i ψ) (Q ψ) := by
  let S : ℕ → H →L[ℂ] H := fun n => ∑ i ∈ Finset.range n, P i
  -- Each `P i` is self-adjoint.
  have hstar : ∀ i, star (P i) = P i := fun i => (hP i).isSelfAdjoint
  -- The vectors `P i ψ` are pairwise orthogonal.
  have horthVec : ∀ {i j : ℕ}, i ≠ j → ⟪P i ψ, P j ψ⟫_ℂ = 0 := by
    intro i j hij
    have hadj : (P i).adjoint = P i := by
      rw [← ContinuousLinearMap.star_eq_adjoint (P i)]
      exact hstar i
    calc
      ⟪P i ψ, P j ψ⟫_ℂ = ⟪ψ, (P i).adjoint (P j ψ)⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right (P i) ψ (P j ψ)]
      _ = ⟪ψ, P i (P j ψ)⟫_ℂ := by rw [hadj]
      _ = ⟪ψ, (P i * P j) ψ⟫_ℂ := rfl
      _ = 0 := by
        rw [horth i j hij]
        simp
  -- Each partial-sum operator `S n` is itself a star projection.
  have hSproj : ∀ n : ℕ, IsStarProjection (S n) := by
    intro n
    refine ⟨?_, ?_⟩
    · change S n * S n = S n
      calc
        S n * S n = (∑ i ∈ Finset.range n, P i) * (∑ j ∈ Finset.range n, P j) := by simp [S]
        _ = ∑ i ∈ Finset.range n, P i * (∑ j ∈ Finset.range n, P j) := by
          rw [Finset.sum_mul]
        _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (P i) * (P j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = ∑ i ∈ Finset.range n, (P i) * (P i) := by
          apply Finset.sum_congr rfl
          intro i hi
          refine Finset.sum_eq_single (s := Finset.range n)
            (f := fun j => (P i) * (P j)) i ?_ ?_
          · intro j hj hji
            simpa using horth i j (Ne.symm hji)
          · intro h
            exact False.elim (h hi)
        _ = ∑ i ∈ Finset.range n, P i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hP i).isIdempotentElem
        _ = S n := by simp [S]
    · change star (S n) = S n
      calc
        star (S n) = star (∑ i ∈ Finset.range n, P i) := by rfl
        _ = ∑ i ∈ Finset.range n, star (P i) := by simp [star_sum]
        _ = ∑ i ∈ Finset.range n, P i := by simp [hstar]
        _ = S n := by simp [S]
  -- Pythagoras on every finite set.
  have hnorm2 : ∀ t : Finset ℕ, (∑ i ∈ t, ‖P i ψ‖ ^ 2) = ‖∑ i ∈ t, P i ψ‖ ^ 2 := by
    intro t
    have hc : (‖∑ i ∈ t, P i ψ‖ : ℂ) ^ 2 = ∑ i ∈ t, (‖P i ψ‖ : ℂ) ^ 2 := by
      calc
        (‖∑ i ∈ t, P i ψ‖ : ℂ) ^ 2 = ⟪∑ i ∈ t, P i ψ, ∑ j ∈ t, P j ψ⟫_ℂ := by
          exact (inner_self_eq_norm_sq_to_K (∑ i ∈ t, P i ψ)).symm
        _ = ∑ i ∈ t, ⟪P i ψ, P i ψ⟫_ℂ := by
          calc
            ⟪∑ i ∈ t, P i ψ, ∑ j ∈ t, P j ψ⟫_ℂ = ∑ i ∈ t, ⟪P i ψ, ∑ j ∈ t, P j ψ⟫_ℂ := by
              rw [sum_inner]
            _ = ∑ i ∈ t, ∑ j ∈ t, ⟪P i ψ, P j ψ⟫_ℂ := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [inner_sum]
            _ = ∑ i ∈ t, ⟪P i ψ, P i ψ⟫_ℂ := by
              apply Finset.sum_congr rfl
              intro i hi
              refine Finset.sum_eq_single (s := t)
                (f := fun j => ⟪P i ψ, P j ψ⟫_ℂ) i ?_ ?_
              · intro j hj hji
                exact horthVec (Ne.symm hji)
              · intro h
                exact False.elim (h hi)
        _ = ∑ i ∈ t, (‖P i ψ‖ : ℂ) ^ 2 := by
          simp [inner_self_eq_norm_sq_to_K]
    exact_mod_cast hc.symm
  -- The Bessel bound: `∑_{i < n} ‖P i ψ‖² ≤ ‖ψ‖²`.
  have hbdd_range : ∀ n : ℕ, (∑ i ∈ Finset.range n, ‖P i ψ‖ ^ 2) ≤ ‖ψ‖ ^ 2 := by
    intro n
    calc
      (∑ i ∈ Finset.range n, ‖P i ψ‖ ^ 2) = ‖∑ i ∈ Finset.range n, P i ψ‖ ^ 2 :=
        hnorm2 (Finset.range n)
      _ ≤ ‖ψ‖ ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg (∑ i ∈ Finset.range n, P i ψ))
          (by simpa [S] using norm_apply_le_of_isStarProjection (hSproj n) ψ) 2
  -- Hence the squared norms are summable, with the vanishing-tail property.
  have hsummable_sq : Summable (fun i : ℕ => ‖P i ψ‖ ^ 2) :=
    summable_of_sum_range_le (fun i => sq_nonneg _) hbdd_range
  have hvan : ∀ ε : ℝ, 0 < ε → ∃ u : Finset ℕ, ∀ t : Finset ℕ,
      Disjoint t u → ‖∑ i ∈ t, ‖P i ψ‖ ^ 2‖ < ε := by
    intro ε hε
    exact (summable_iff_vanishing_norm.mp hsummable_sq) ε hε
  -- Hence the vectors `P i ψ` are unconditionally summable.
  have hsumm_vec : Summable (fun i : ℕ => P i ψ) := by
    rw [summable_iff_vanishing_norm]
    intro ε hε
    rcases (summable_iff_vanishing_norm.mp hsummable_sq) (ε ^ 2) (sq_pos_of_pos hε) with
      ⟨u, hu⟩
    refine ⟨u, ?_⟩
    intro t htu
    have hn : 0 ≤ ∑ i ∈ t, ‖P i ψ‖ ^ 2 :=
      Finset.sum_nonneg (fun i hi => sq_nonneg (‖P i ψ‖))
    have hltSq : ‖∑ i ∈ t, P i ψ‖ ^ 2 < ε ^ 2 := by
      rw [← hnorm2 t]
      simpa [abs_of_nonneg hn] using hu t htu
    have hltAbs : |‖∑ i ∈ t, P i ψ‖| < |ε| := (sq_lt_sq).mp hltSq
    simpa [abs_of_nonneg (norm_nonneg (∑ i ∈ t, P i ψ)), abs_of_pos hε] using hltAbs
  -- `Q ψ` is the value of the unconditional sum.
  have hhas : HasSum (fun i : ℕ => P i ψ) (∑' i : ℕ, P i ψ) := hsumm_vec.hasSum
  have hEq : (∑' i : ℕ, P i ψ) = Q ψ :=
    tendsto_nhds_unique (hhas.tendsto_sum_nat) (hQ ψ)
  rw [← hEq]
  exact hhas

end Spectral
end Physicslib4
