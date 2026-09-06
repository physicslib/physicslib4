/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.ProjectionValuedMeasure

/-!
# Integration of bounded measurable functions against a projection-valued measure

Given a projection-valued measure `μ` on a measurable space `X` with values in
`𝓑(H)`, every bounded measurable `f : X → ℂ` has an operator-valued integral
`∫ f dμ ∈ 𝓑(H)`, characterised by
`⟪ψ, (∫ f dμ) ψ⟫ = ∫ f dμ_ψ` for every `ψ ∈ H`.

## Main definitions

* `Physicslib4.Spectral.ProjectionValuedMeasure.integral` — the operator-valued
  integral `f ↦ ∫ f dμ`, extended by `0` to arbitrary functions.

The class of admissible integrands is `Physicslib4.Spectral.BddMeasurable`, defined
in `Physicslib4/Spectral/Basic.lean`; every statement below takes
`f ∈ BddMeasurable X` rather than a `Measurable f`/bounded hypothesis pair.

## Main statements

* `Physicslib4.Spectral.ProjectionValuedMeasure.existsUnique_integral` — existence
  and uniqueness of the operator-valued integral as a linear map.
* `Physicslib4.Spectral.ProjectionValuedMeasure.integral_add`,
  `Physicslib4.Spectral.ProjectionValuedMeasure.integral_smul` — linearity of
  `f ↦ ∫ f dμ`.
* `Physicslib4.Spectral.ProjectionValuedMeasure.integral_indicator` — the integral
  of an indicator is the corresponding projection.
* `Physicslib4.Spectral.ProjectionValuedMeasure.norm_integral_le` — the integral is
  bounded by the supremum norm of the integrand.
* `Physicslib4.Spectral.ProjectionValuedMeasure.integral_mul` — multiplicativity.
* `Physicslib4.Spectral.ProjectionValuedMeasure.integral_conj` — compatibility with
  conjugation and the adjoint.
-/

namespace Physicslib4
namespace Spectral

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap MeasureTheory

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProjectionValuedMeasure

/-!
### The quadratic forms behind the construction
-/

/--
For an indicator function `Q_{1_E}` is a bounded quadratic form.

Blueprint reference: `prpstn:Q-indicator-bounded-form` (first part).
-/
theorem isBoundedQuadraticForm_integral_indicator (μ : ProjectionValuedMeasure X H) {E : Set X}
    (hE : MeasurableSet E) :
    IsBoundedQuadraticForm (fun ψ : H => ∫ x, E.indicator (1 : X → ℂ) x ∂(μ.assoc ψ)) := by
  have hint : (fun ψ : H => ∫ x, E.indicator (1 : X → ℂ) x ∂(μ.assoc ψ)) =
      (fun ψ : H => ⟪ψ, μ E ψ⟫_ℂ) := by
    funext ψ
    have him : (⟪ψ, μ E ψ⟫_ℂ).im = 0 := by
      have hAdj : (μ E).adjoint = μ E := by
        rw [← ContinuousLinearMap.star_eq_adjoint (μ E)]
        exact (μ.isStarProjection_apply E).isSelfAdjoint
      have hSym : ∀ x y : H, ⟪(μ E) x, y⟫_ℂ = ⟪x, (μ E) y⟫_ℂ := by
        exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAdj)
      apply (Complex.conj_eq_iff_im.mp)
      calc
        (starRingEnd ℂ) (⟪ψ, (μ E) ψ⟫_ℂ) = ⟪(μ E) ψ, ψ⟫_ℂ := inner_conj_symm ((μ E) ψ) ψ
        _ = ⟪ψ, (μ E) ψ⟫_ℂ := hSym ψ ψ
    have htoReal : (((μ.assoc ψ) E).toReal : ℂ) = (⟪ψ, μ E ψ⟫_ℂ).re := by
      exact_mod_cast (μ.assoc_apply ψ hE)
    have hre : (⟪ψ, μ E ψ⟫_ℂ).re = ⟪ψ, μ E ψ⟫_ℂ := by
      refine Complex.ext ?_ ?_
      · simp
      · simp [him]
    calc
      (∫ x, E.indicator (fun _ : X => (1 : ℂ)) x ∂(μ.assoc ψ))
          = (((μ.assoc ψ) E).toReal : ℂ) := by
            rw [integral_indicator_const (1 : ℂ) hE]
            rw [Measure.real_def]
            simp
      _ = (⟪ψ, μ E ψ⟫_ℂ).re := htoReal
      _ = ⟪ψ, μ E ψ⟫_ℂ := hre
  rw [hint]
  exact isBoundedQuadraticForm_inner (μ E)

/--
For an indicator function `Q_{1_E}` is bounded with constant `1`.

Blueprint reference: `prpstn:Q-indicator-bounded-form` (second part).
-/
theorem norm_integral_indicator_le (μ : ProjectionValuedMeasure X H) {E : Set X}
    (hE : MeasurableSet E) (ψ : H) :
    ‖∫ x, E.indicator (1 : X → ℂ) x ∂(μ.assoc ψ)‖ ≤ ‖ψ‖ ^ 2 := by
  have hint : (∫ x, E.indicator (1 : X → ℂ) x ∂(μ.assoc ψ)) = ⟪ψ, μ E ψ⟫_ℂ := by
    have him : (⟪ψ, μ E ψ⟫_ℂ).im = 0 := by
      have hAdj : (μ E).adjoint = μ E := by
        rw [← ContinuousLinearMap.star_eq_adjoint (μ E)]
        exact (μ.isStarProjection_apply E).isSelfAdjoint
      have hSym : ∀ x y : H, ⟪(μ E) x, y⟫_ℂ = ⟪x, (μ E) y⟫_ℂ := by
        exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAdj)
      apply (Complex.conj_eq_iff_im.mp)
      calc
        (starRingEnd ℂ) (⟪ψ, (μ E) ψ⟫_ℂ) = ⟪(μ E) ψ, ψ⟫_ℂ := inner_conj_symm ((μ E) ψ) ψ
        _ = ⟪ψ, (μ E) ψ⟫_ℂ := hSym ψ ψ
    have htoReal : (((μ.assoc ψ) E).toReal : ℂ) = (⟪ψ, μ E ψ⟫_ℂ).re := by
      exact_mod_cast (μ.assoc_apply ψ hE)
    have hre : (⟪ψ, μ E ψ⟫_ℂ).re = ⟪ψ, μ E ψ⟫_ℂ := by
      refine Complex.ext ?_ ?_
      · simp
      · simp [him]
    calc
      (∫ x, E.indicator (fun _ : X => (1 : ℂ)) x ∂(μ.assoc ψ))
          = (((μ.assoc ψ) E).toReal : ℂ) := by
            rw [integral_indicator_const (1 : ℂ) hE]
            rw [Measure.real_def]
            simp
      _ = (⟪ψ, μ E ψ⟫_ℂ).re := htoReal
      _ = ⟪ψ, μ E ψ⟫_ℂ := hre
  rw [hint]
  calc
    ‖⟪ψ, μ E ψ⟫_ℂ‖ ≤ ‖ψ‖ * ‖μ E ψ‖ := norm_inner_le_norm ψ (μ E ψ)
    _ ≤ ‖ψ‖ * ‖ψ‖ := by
      have hproj : ‖μ E ψ‖ ≤ ‖ψ‖ :=
        norm_apply_le_of_isStarProjection (μ.isStarProjection_apply E) ψ
      exact mul_le_mul_of_nonneg_left hproj (norm_nonneg ψ)
    _ = ‖ψ‖ ^ 2 := by ring

/--
For a simple function the quadratic form `Q_s` is a bounded quadratic form.

Blueprint reference: `prpstn:Q-simple-bounded-form`.
-/
theorem isBoundedQuadraticForm_integral_simpleFunc (μ : ProjectionValuedMeasure X H)
    (s : SimpleFunc X ℂ) :
    IsBoundedQuadraticForm (fun ψ : H => ∫ x, s x ∂(μ.assoc ψ)) := by
  classical
  -- `s` is the finite linear combination of the indicators of its fibres
  -- `s = ∑ c ∈ s.range, c * 1_{s ⁻¹' {c}}`.
  have hdecomp : ∀ x : X,
      (∑ c ∈ s.range, c * (s ⁻¹' {c}).indicator (fun _ : X => (1 : ℂ)) x) = s x := by
    intro x
    calc
      (∑ c ∈ s.range, c * (s ⁻¹' {c}).indicator (fun _ : X => (1 : ℂ)) x)
          = (s x) * (s ⁻¹' {s x}).indicator (fun _ : X => (1 : ℂ)) x := by
            refine Finset.sum_eq_single (s x) ?_ ?_
            · intro c hc hcne
              have hne : s x ≠ c := hcne.symm
              have hx : x ∉ s ⁻¹' {c} := by
                simp [Set.mem_preimage, hne]
              simp [hx]
            · intro hx
              exact (hx (SimpleFunc.mem_range_self s x)).elim
      _ = s x := by
            simp [Set.mem_preimage]
  -- `Qg c ψ` is the quadratic form of the indicator of the fibre `s ⁻¹' {c}`.
  let Qg : ℂ → H → ℂ := fun c ψ =>
    ∫ x, (s ⁻¹' {c}).indicator (fun _ : X => (1 : ℂ)) x ∂(μ.assoc ψ)
  have hQ : IsBoundedQuadraticForm (fun ψ : H => ∑ c ∈ s.range, c * Qg c ψ) := by
    refine IsBoundedQuadraticForm.sum s.range ?_ (fun c : ℂ => c)
    intro c hc
    dsimp [Qg]
    exact isBoundedQuadraticForm_integral_indicator μ (s.measurableSet_fiber c)
  -- the sum of the fibre integrals equals the integral of `s`
  have hsum : (fun ψ : H => ∑ c ∈ s.range, c * Qg c ψ) =
      (fun ψ : H => ∫ x, s x ∂(μ.assoc ψ)) := by
    funext ψ
    have hInt : ∀ c ∈ s.range, Integrable
        (fun x : X => c * (s ⁻¹' {c}).indicator (fun _ : X => (1 : ℂ)) x) (μ.assoc ψ) := by
      intro c hc
      refine Integrable.of_bound ?_ ‖c‖ ?_
      · refine StronglyMeasurable.aestronglyMeasurable ?_
        refine StronglyMeasurable.const_mul
          (StronglyMeasurable.indicator (stronglyMeasurable_const :
            StronglyMeasurable (fun _ : X => (1 : ℂ))) (s.measurableSet_fiber c)) c
      · refine ae_of_all (μ.assoc ψ) ?_
        intro x
        by_cases hx : x ∈ s ⁻¹' {c}
        · simp [hx]
        · simp [hx]
    calc
      (∑ c ∈ s.range, c * Qg c ψ)
          = (∑ c ∈ s.range,
              ∫ x, c * (s ⁻¹' {c}).indicator (fun _ : X => (1 : ℂ)) x ∂(μ.assoc ψ)) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            simp [Qg, integral_const_mul]
      _ = (∫ x, (∑ c ∈ s.range,
            c * (s ⁻¹' {c}).indicator (fun _ : X => (1 : ℂ)) x) ∂(μ.assoc ψ)) := by
            rw [integral_finsetSum s.range hInt]
      _ = (∫ x, s x ∂(μ.assoc ψ)) := by
            exact integral_congr_ae (ae_of_all (μ.assoc ψ) hdecomp)
  rw [← hsum]
  exact hQ

/--
For a bounded measurable `f` the quadratic form `Q_f` is a bounded quadratic form.

This is the third and last stage of the argument summarised by
`isBoundedQuadraticForm_integral`: it is obtained from
`isBoundedQuadraticForm_integral_simpleFunc` by uniform approximation.

Blueprint reference: `prpstn:Q-measurable-bounded-form`.
-/
theorem isBoundedQuadraticForm_integral_bddMeasurable (μ : ProjectionValuedMeasure X H)
    {f : X → ℂ} (hf : f ∈ BddMeasurable X) :
    IsBoundedQuadraticForm (fun ψ : H => ∫ x, f x ∂(μ.assoc ψ)) := by
  classical
  obtain ⟨s, hs⟩ := exists_simpleFunc_tendstoUniformly hf
  let Q : ℕ → H → ℂ := fun n ψ => ∫ x, s n x ∂(μ.assoc ψ)
  let Q₀ : H → ℂ := fun ψ => ∫ x, f x ∂(μ.assoc ψ)
  have hQn : ∀ n, IsBoundedQuadraticForm (Q n) := by
    intro n
    exact isBoundedQuadraticForm_integral_simpleFunc μ (s n)
  -- `f` is bounded by `Cf`, and the simple functions converge uniformly to `f`.
  rcases hf with ⟨_, Cf, hCf⟩
  have hN : ∃ N : ℕ, ∀ n ≥ N, ∀ x : X, ‖s n x - f x‖ ≤ 1 := by
    have hs1 : ∀ᶠ n in atTop, ∀ x : X, dist (f x) (s n x) < 1 :=
      Metric.tendstoUniformly_iff.mp hs 1 zero_lt_one
    rcases (Filter.eventually_atTop.mp hs1) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn x
    have hx : dist (f x) (s n x) < 1 := hN n hn x
    rw [dist_eq_norm] at hx
    rw [norm_sub_rev] at hx
    exact le_of_lt hx
  rcases hN with ⟨N, hN⟩
  -- A uniform bound on the approximating simple functions: the finitely many
  -- initial terms are bounded by their (finite) ranges, the tail by `1 + Cf`.
  let Cnn : ℕ → NNReal := fun n =>
    ⟨max (Classical.choose ((s n).exists_forall_norm_le)) 0, le_max_right _ _⟩
  have hCnn : ∀ n x, ‖s n x‖ ≤ (Cnn n : ℝ) := by
    intro n x
    exact le_trans (Classical.choose_spec ((s n).exists_forall_norm_le) x) (le_max_left _ 0)
  let C : ℝ := max (1 + Cf) ((Finset.sup (Finset.range N) Cnn : NNReal) : ℝ)
  have hC : ∀ n x, ‖s n x‖ ≤ C := by
    intro n x
    by_cases hn : n < N
    · calc
        ‖s n x‖ ≤ (Cnn n : ℝ) := hCnn n x
        _ ≤ ((Finset.sup (Finset.range N) Cnn : NNReal) : ℝ) := by
          exact Finset.le_sup (f := Cnn) (Finset.mem_range.mpr hn)
        _ ≤ C := by
          dsimp [C]
          exact le_max_right _ _
    · have hnN : N ≤ n := le_of_not_gt hn
      calc
        ‖s n x‖ = ‖(s n x - f x) + f x‖ := by rw [sub_add_cancel]
        _ ≤ ‖s n x - f x‖ + ‖f x‖ := norm_add_le _ _
        _ ≤ 1 + Cf := add_le_add (hN n hnN x) (hCf x)
        _ ≤ C := by
          dsimp [C]
          exact le_max_left _ _
  -- the total mass of `μ_φ` is `‖φ‖²`
  have h_total : ∀ φ : H, ((μ.assoc φ) Set.univ).toReal = ‖φ‖ ^ 2 := by
    intro φ
    calc
      ((μ.assoc φ) Set.univ).toReal = (⟪φ, μ Set.univ φ⟫_ℂ).re := μ.assoc_apply φ MeasurableSet.univ
      _ = (⟪φ, φ⟫_ℂ).re := by simp
      _ = ‖φ‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]
        rw [← map_pow]
        exact Complex.ofReal_re _
  -- pointwise convergence of the integrals, by dominated convergence
  have hptconv : ∀ x : X, Tendsto (fun n => s n x) atTop (𝓝 (f x)) := by
    intro x
    exact TendstoUniformlyOnFilter.tendsto_at (p' := ⊤) hs.tendstoUniformlyOnFilter le_top
  have hpt : ∀ φ : H, Tendsto (fun n => Q n φ) atTop (𝓝 (Q₀ φ)) := by
    intro φ
    dsimp [Q, Q₀]
    refine tendsto_integral_of_dominated_convergence (μ := μ.assoc φ)
      (F := fun n x => s n x) (f := f) (bound := fun _ : X => C) ?_ ?_ ?_ ?_
    · intro n
      exact (s n).stronglyMeasurable.aestronglyMeasurable
    · exact (integrable_const_iff (μ := μ.assoc φ) (c := C)).2 (Or.inr inferInstance)
    · intro n
      exact ae_of_all (μ.assoc φ) (hC n)
    · exact ae_of_all (μ.assoc φ) hptconv
  -- the uniform bound on the quadratic forms `Q n`
  have hnorm_le : ∀ n φ, ‖Q n φ‖ ≤ C * ‖φ‖ ^ 2 := by
    intro n φ
    have hInt : Integrable (fun x => ‖s n x‖) (μ.assoc φ) := by
      refine Integrable.of_bound ?_ C ?_
      · exact (s n).stronglyMeasurable.norm.aestronglyMeasurable
      · refine ae_of_all (μ.assoc φ) ?_
        intro x
        simpa using hC n x
    have hIntC : Integrable (fun _ : X => C) (μ.assoc φ) :=
      (integrable_const_iff (μ := μ.assoc φ) (c := C)).2 (Or.inr inferInstance)
    calc
      ‖Q n φ‖ = ‖∫ x, s n x ∂(μ.assoc φ)‖ := rfl
      _ ≤ ∫ x, ‖s n x‖ ∂(μ.assoc φ) := norm_integral_le_integral_norm _
      _ ≤ ∫ x, C ∂(μ.assoc φ) := by
        refine integral_mono_ae hInt hIntC ?_
        exact ae_of_all (μ.assoc φ) (hC n)
      _ = C * ((μ.assoc φ) Set.univ).toReal := by
        rw [integral_const, measureReal_def]
        simp [mul_comm]
      _ = C * ‖φ‖ ^ 2 := by rw [h_total φ]
  simpa [Q₀] using isBoundedQuadraticForm_of_tendsto (Q := Q) (Q₀ := Q₀) (C := C)
    (fun n => (hQn n).isQuadratic) ⟨hnorm_le, hpt⟩

/--
For a bounded measurable `f`, the map `Q_f : ψ ↦ ∫ f dμ_ψ` is a bounded quadratic
form on `H`.

This is the summary statement of the three-stage argument: indicator functions in
`isBoundedQuadraticForm_integral_indicator`, simple functions in
`isBoundedQuadraticForm_integral_simpleFunc`, and general bounded measurable
functions in `isBoundedQuadraticForm_integral_bddMeasurable`, which is the stage
that carries the whole statement and so discharges this node.

Blueprint reference: `lmm:lemma1-of-operator-valued-integration`.
-/
theorem isBoundedQuadraticForm_integral (μ : ProjectionValuedMeasure X H) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) :
    IsBoundedQuadraticForm (fun ψ : H => ∫ x, f x ∂(μ.assoc ψ)) :=
  isBoundedQuadraticForm_integral_bddMeasurable μ hf

/--
**Operator-valued integration.** There is a unique linear map from the space of
bounded measurable complex-valued functions on `X` into `𝓑(H)`, written
`f ↦ ∫ f dμ`, such that `⟪ψ, (∫ f dμ) ψ⟫ = ∫ f dμ_ψ` for every `f` and every
`ψ ∈ H`.

Blueprint reference: `thrm:operator-valued-integration`.
-/
theorem existsUnique_integral (μ : ProjectionValuedMeasure X H) :
    ∃! T : BddMeasurable X →ₗ[ℂ] (H →L[ℂ] H),
      ∀ (f : BddMeasurable X) (ψ : H),
        ⟪ψ, T f ψ⟫_ℂ = ∫ x, (f : X → ℂ) x ∂(μ.assoc ψ) := by
  classical
  let P : BddMeasurable X → H → ℂ := fun f : BddMeasurable X => fun ψ : H =>
    ∫ x, (f : X → ℂ) x ∂(μ.assoc ψ)
  have hQ : ∀ f : BddMeasurable X, IsBoundedQuadraticForm (P f) := by
    intro f
    exact isBoundedQuadraticForm_integral_bddMeasurable μ f.property
  have hInt : ∀ (f : BddMeasurable X) (ψ : H),
      Integrable (fun x : X => (f : X → ℂ) x) (μ.assoc ψ) := by
    intro f ψ
    rcases f.property with ⟨hfmeas, C, hC⟩
    exact Integrable.of_bound (μ := μ.assoc ψ) hfmeas.aestronglyMeasurable C (ae_of_all _ hC)
  let T : BddMeasurable X →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := fun f => (hQ f).toOperator
      map_add' := by
        intro f g
        exact (IsBoundedQuadraticForm.eq_toOperator (hQ (f + g))
          (A := (hQ f).toOperator + (hQ g).toOperator) (by
            intro ψ
            have hco : (fun x : X => ((f + g : BddMeasurable X) : X → ℂ) x) =
                fun x : X => (f : X → ℂ) x + (g : X → ℂ) x := rfl
            have hrep_f : (∫ x : X, (f : X → ℂ) x ∂(μ.assoc ψ)) =
                ⟪ψ, (hQ f).toOperator ψ⟫_ℂ := by
              exact IsBoundedQuadraticForm.inner_toOperator (hQ f) ψ
            have hrep_g : (∫ x : X, (g : X → ℂ) x ∂(μ.assoc ψ)) =
                ⟪ψ, (hQ g).toOperator ψ⟫_ℂ := by
              exact IsBoundedQuadraticForm.inner_toOperator (hQ g) ψ
            calc
              ∫ x, ((f + g : BddMeasurable X) : X → ℂ) x ∂(μ.assoc ψ)
                  = ∫ x, ((f : X → ℂ) x + (g : X → ℂ) x) ∂(μ.assoc ψ) := by
                    rw [hco]
              _ = (∫ x, (f : X → ℂ) x ∂(μ.assoc ψ)) +
                  (∫ x, (g : X → ℂ) x ∂(μ.assoc ψ)) := by
                    rw [integral_add (hInt f ψ) (hInt g ψ)]
              _ = ⟪ψ, (hQ f).toOperator ψ⟫_ℂ + ⟪ψ, (hQ g).toOperator ψ⟫_ℂ := by
                    rw [hrep_f, hrep_g]
              _ = ⟪ψ, ((hQ f).toOperator + (hQ g).toOperator) ψ⟫_ℂ := by
                    simp [inner_add_right]
          )).symm
      map_smul' := by
        intro c f
        exact (IsBoundedQuadraticForm.eq_toOperator (hQ (c • f))
          (A := c • (hQ f).toOperator) (by
            intro ψ
            have hco : (fun x : X => ((c • f : BddMeasurable X) : X → ℂ) x) =
                fun x : X => c • (f : X → ℂ) x := rfl
            have hrep : (∫ x : X, (f : X → ℂ) x ∂(μ.assoc ψ)) =
                ⟪ψ, (hQ f).toOperator ψ⟫_ℂ := by
              exact IsBoundedQuadraticForm.inner_toOperator (hQ f) ψ
            calc
              ∫ x, ((c • f : BddMeasurable X) : X → ℂ) x ∂(μ.assoc ψ)
                  = ∫ x, c • (f : X → ℂ) x ∂(μ.assoc ψ) := by
                    rw [hco]
              _ = c • (∫ x, (f : X → ℂ) x ∂(μ.assoc ψ)) := by
                    rw [integral_smul]
              _ = ⟪ψ, (c • (hQ f).toOperator) ψ⟫_ℂ := by
                    rw [hrep]
                    simp [inner_smul_right]
          )).symm }
  refine ⟨T, ?_identity, ?_unique⟩
  · intro f ψ
    exact (IsBoundedQuadraticForm.inner_toOperator (hQ f) ψ).symm
  · intro T' hT'
    apply LinearMap.ext
    intro f
    have hzero : ∀ ψ : H,
        ⟪((T' f - T f : H →L[ℂ] H) : H →ₗ[ℂ] H) ψ, ψ⟫_ℂ = 0 := by
      intro ψ
      have hb : ⟪ψ, (T' f - T f : H →L[ℂ] H) ψ⟫_ℂ = 0 := by
        rw [sub_apply, inner_sub_right, hT' f ψ, sub_eq_zero]
        exact IsBoundedQuadraticForm.inner_toOperator (hQ f) ψ
      rw [← inner_conj_symm]
      simpa using congrArg (starRingEnd ℂ) hb
    have h0 : ((T' f - T f : H →L[ℂ] H) : H →ₗ[ℂ] H) = 0 :=
      (inner_map_self_eq_zero ((T' f - T f : H →L[ℂ] H) : H →ₗ[ℂ] H)).mp hzero
    ext ψ
    exact sub_eq_zero.mp (congrFun (congrArg DFunLike.coe h0) ψ)

open Classical in
/--
The operator-valued integral `∫ f dμ`, defined to be `0` on functions that are not
bounded and measurable.
-/
noncomputable def integral (μ : ProjectionValuedMeasure X H) (f : X → ℂ) : H →L[ℂ] H :=
  if h : f ∈ BddMeasurable X then (existsUnique_integral μ).choose ⟨f, h⟩ else 0

theorem inner_integral (μ : ProjectionValuedMeasure X H) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) (ψ : H) :
    ⟪ψ, μ.integral f ψ⟫_ℂ = ∫ x, f x ∂(μ.assoc ψ) := by
  classical
  simp only [integral, dif_pos hf]
  exact (existsUnique_integral μ).choose_spec.1 ⟨f, hf⟩ ψ

/-!
### Linearity of the integral

`integral` is defined through `Exists.choose` applied to `existsUnique_integral`, so
its linearity in the integrand is not definitional. The two computation rules below
recover it, and are what the vector-space arguments elsewhere in the directory
consume.
-/

/-- Additivity of the operator-valued integral. -/
theorem integral_add (μ : ProjectionValuedMeasure X H) {f g : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hg : g ∈ BddMeasurable X) :
    μ.integral (f + g) = μ.integral f + μ.integral g := by
  classical
  have hfg : f + g ∈ BddMeasurable X := (BddMeasurable X).add_mem hf hg
  simp only [integral, dif_pos hf, dif_pos hg, dif_pos hfg]
  exact map_add (existsUnique_integral μ).choose ⟨f, hf⟩ ⟨g, hg⟩

/-- Homogeneity of the operator-valued integral. -/
theorem integral_smul (μ : ProjectionValuedMeasure X H) (α : ℂ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) : μ.integral (α • f) = α • μ.integral f := by
  classical
  have hαf : α • f ∈ BddMeasurable X := (BddMeasurable X).smul_mem α hf
  simp only [integral, dif_pos hf, dif_pos hαf]
  exact map_smul (existsUnique_integral μ).choose α ⟨f, hf⟩

/-!
### Basic properties of the operator-valued integral
-/

/--
The integral of an indicator function is the corresponding projection.

Blueprint reference: `prpstn:integral-of-indicator` (first part).
-/
theorem integral_indicator (μ : ProjectionValuedMeasure X H) {E : Set X}
    (hE : MeasurableSet E) :
    μ.integral (E.indicator (1 : X → ℂ)) = μ E := by
  classical
  let Q : H → ℂ := fun ψ => ∫ x, E.indicator (1 : X → ℂ) x ∂(μ.assoc ψ)
  have hQ : IsBoundedQuadraticForm Q := isBoundedQuadraticForm_integral_indicator μ hE
  have hf : E.indicator (1 : X → ℂ) ∈ BddMeasurable X := by
    rw [mem_bddMeasurable]
    refine ⟨measurable_const.indicator hE, ⟨1, ?_⟩⟩
    intro x
    by_cases hx : x ∈ E
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hA : ∀ ψ : H, Q ψ = ⟪ψ, μ E ψ⟫_ℂ := by
    intro ψ
    have him : (⟪ψ, μ E ψ⟫_ℂ).im = 0 := by
      have hAdj : (μ E).adjoint = μ E := by
        rw [← ContinuousLinearMap.star_eq_adjoint (μ E)]
        exact (μ.isStarProjection_apply E).isSelfAdjoint
      have hSym : ∀ x y : H, ⟪(μ E) x, y⟫_ℂ = ⟪x, (μ E) y⟫_ℂ := by
        exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAdj)
      apply (Complex.conj_eq_iff_im.mp)
      calc
        (starRingEnd ℂ) (⟪ψ, (μ E) ψ⟫_ℂ) = ⟪(μ E) ψ, ψ⟫_ℂ := inner_conj_symm ((μ E) ψ) ψ
        _ = ⟪ψ, (μ E) ψ⟫_ℂ := hSym ψ ψ
    have htoReal : (((μ.assoc ψ) E).toReal : ℂ) = (⟪ψ, μ E ψ⟫_ℂ).re := by
      exact_mod_cast (μ.assoc_apply ψ hE)
    have hre : (⟪ψ, μ E ψ⟫_ℂ).re = ⟪ψ, μ E ψ⟫_ℂ := by
      refine Complex.ext ?_ ?_
      · simp
      · simp [him]
    calc
      Q ψ = (∫ x, E.indicator (fun _ : X => (1 : ℂ)) x ∂(μ.assoc ψ)) := rfl
      _ = (((μ.assoc ψ) E).toReal : ℂ) := by
        rw [integral_indicator_const (1 : ℂ) hE]
        rw [Measure.real_def]
        simp
      _ = (⟪ψ, μ E ψ⟫_ℂ).re := htoReal
      _ = ⟪ψ, μ E ψ⟫_ℂ := hre
  have hB : ∀ ψ : H, Q ψ = ⟪ψ, μ.integral (E.indicator (1 : X → ℂ)) ψ⟫_ℂ := by
    intro ψ
    simpa [Q] using (inner_integral μ hf ψ).symm
  calc
    μ.integral (E.indicator (1 : X → ℂ)) = hQ.toOperator :=
      IsBoundedQuadraticForm.eq_toOperator hQ hB
    _ = μ E := (IsBoundedQuadraticForm.eq_toOperator hQ hA).symm

/--
The integral of the constant function `1` is the identity operator.

This is `integral_indicator` at `E = Set.univ`, together with the field `univ'` of
`ProjectionValuedMeasure`.

Blueprint reference: `prpstn:integral-of-indicator` (second part).
-/
theorem integral_one (μ : ProjectionValuedMeasure X H) : μ.integral (1 : X → ℂ) = 1 := by
  have h := μ.integral_indicator MeasurableSet.univ
  rw [Set.indicator_univ] at h
  exact h.trans μ.univ'

/--
`μ E` is an orthogonal projection, so its matrix element is symmetric:
`inner phi (μ E psi) = inner (μ E phi) (μ E psi)`.
-/
private lemma inner_pvm_apply (μ : ProjectionValuedMeasure X H) (E : Set X) (phi psi : H) :
    inner ℂ phi (μ E psi) = inner ℂ (μ E phi) (μ E psi) := by
  classical
  have hP : IsStarProjection (μ E) := μ.isStarProjection_apply E
  have hAdj : (μ E).adjoint = μ E := by
    rw [← ContinuousLinearMap.star_eq_adjoint (μ E)]
    exact hP.isSelfAdjoint
  have hSym : ∀ x y : H, inner ℂ ((μ E) x) y = inner ℂ x ((μ E) y) := by
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAdj)
  have hid : μ E (μ E psi) = μ E psi := by
    have hidp : μ E * μ E = μ E := hP.isIdempotentElem
    calc
      μ E (μ E psi) = ((μ E) * (μ E)) psi := by
        rw [ContinuousLinearMap.mul_apply]
      _ = μ E psi := by rw [hidp]
  calc
    inner ℂ phi (μ E psi) = inner ℂ phi (μ E (μ E psi)) := by
          conv_lhs => rw [← hid]
    _ = inner ℂ (μ E phi) (μ E psi) := by
          exact (hSym phi (μ E psi)).symm

/--
For a simple function `s`, the squared norms of the projections of `ψ` onto the
fibres `s ⁻¹' {c}` sum to `‖ψ‖²`.

This is the `s.range`-indexed reformulation of
`norm_sq_eq_sum_of_partition`.
-/
private lemma norm_sq_eq_sum_of_fibers (μ : ProjectionValuedMeasure X H) (s : SimpleFunc X ℂ)
    (ψ : H) : ∑ c ∈ s.range, ‖μ (s ⁻¹' {c}) ψ‖ ^ 2 = ‖ψ‖ ^ 2 :=by
  classical
  let n : ℕ := s.range.card
  let e : s.range ≃ Fin n := Finset.equivFin s.range
  let E : Fin (s.range.card) → Set X := fun i => s ⁻¹' {↑(e.symm i)}
  have hEm : ∀ i : Fin n, MeasurableSet (E i) :=by
    intro i
    exact s.measurableSet_fiber ↑(e.symm i)
  have hEd : Pairwise (fun i j : Fin (s.range.card) => Disjoint (E i) (E j)) :=by
    intro i j hij
    have hne : (↑(e.symm i) : ℂ) ≠ (↑(e.symm j) : ℂ) :=by
      intro hval
      apply hij
      calc
        i = e (e.symm i) := (Equiv.apply_symm_apply e i).symm
        _ = e (e.symm j) := congrArg e (Subtype.ext hval)
        _ = j := Equiv.apply_symm_apply e j
    have hInt : E i ∩ E j = (∅ : Set X) :=by
      ext x
      constructor
      · intro hx
        have hxi : s x = (↑(e.symm i) : ℂ) :=by
          simpa [E, Set.mem_preimage] using hx.1
        have hxj : s x = (↑(e.symm j) : ℂ) :=by
          simpa [E, Set.mem_preimage] using hx.2
        exact (hne (hxi.symm.trans hxj)).elim
      · intro hx
        exact hx.elim
    exact (Set.disjoint_iff_inter_eq_empty.mpr hInt)
  have hEc : (⋃ i : Fin n, E i) = Set.univ :=by
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      rw [Set.mem_iUnion]
      refine ⟨e ⟨s x, s.mem_range_self x⟩, ?_⟩
      simpa [E, Set.mem_preimage, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  calc
    (∑ c ∈ s.range, ‖μ (s ⁻¹' {c}) ψ‖ ^ 2)
        = ∑ c : s.range, ‖μ (s ⁻¹' {↑c}) ψ‖ ^ 2 :=by
          rw [← Finset.sum_coe_sort]
    _ = ∑ i : Fin n, ‖μ (E i) ψ‖ ^ 2 :=by
          simpa [E] using (Equiv.sum_comp e.symm (fun c : s.range => ‖μ (s ⁻¹' {↑c}) ψ‖ ^ 2)).symm
    _ = ‖ψ‖ ^ 2 :=(μ.norm_sq_eq_sum_of_partition E hEm hEd hEc ψ).symm

/--
The norm bound for the integral of a simple function.

This is the special case of `norm_integral_le` for a simple integrand; it is kept
as a separate declaration only because the blueprint proves the general bound by
reducing to it.

The blueprint spells the integrand as `∑ᵢ cᵢ 1_{Eᵢ}` for a finite measurable family
`E` that is pairwise disjoint and covers `X`. Here it is a
`MeasureTheory.SimpleFunc X ℂ`, matching the sibling statements
`isBoundedQuadraticForm_integral_simpleFunc` and `integral_simpleFunc_mul`: a simple
function is canonically of that form, over the pairwise disjoint fibres `s ⁻¹' {c}`,
which cover `X`. So no generality is gained or lost.

Blueprint reference: `prpstn:integral-norm-bound-simple`.
-/
theorem norm_integral_simple_le (μ : ProjectionValuedMeasure X H) (s : SimpleFunc X ℂ) :
    ‖μ.integral (fun x => s x)‖ ≤ ⨆ x, ‖s x‖ := by
  classical
  let E : ℂ → Set X := fun c => s ⁻¹' {c}
  have hE : ∀ c : ℂ, MeasurableSet (E c) := by
    intro c
    simpa [E] using s.measurableSet_fiber c
  have hind : ∀ c : ℂ, (E c).indicator (fun _ : X => (1 : ℂ)) ∈ BddMeasurable X := by
    intro c
    rw [mem_bddMeasurable]
    refine ⟨measurable_const.indicator (hE c), ⟨1, ?_⟩⟩
    intro x
    by_cases hx : x ∈ E c
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hzero : μ.integral (fun _ : X => 0) = 0 := by
    have h0 : (fun _ : X => (0 : ℂ)) ∈ BddMeasurable X := (BddMeasurable X).zero_mem
    rw [integral, dif_pos h0]
    exact map_zero (existsUnique_integral μ).choose
  -- The integral is additive over finite pointwise sums of bounded measurable functions.
  have hlin : ∀ (t : Finset ℂ) (g : ℂ → X → ℂ),
      (∀ c ∈ t, g c ∈ BddMeasurable X) →
      μ.integral (fun x : X => t.sum (fun c : ℂ => g c x)) = t.sum (fun c : ℂ => μ.integral (g c)) := by
    intro t g hg
    induction t using Finset.induction with
    | empty =>
        simpa using hzero
    | insert c rest hrest ih =>
        have hgc : g c ∈ BddMeasurable X := hg c (Finset.mem_insert_self c rest)
        have hgrest : ∀ c' ∈ rest, g c' ∈ BddMeasurable X := fun c' hc' => hg c' (Finset.mem_insert_of_mem hc')
        have hsum_mem : rest.sum (fun c' : ℂ => g c') ∈ BddMeasurable X :=
          (BddMeasurable X).sum_mem (t := rest) hgrest
        calc
          μ.integral (fun x : X => (insert c rest).sum (fun c' : ℂ => g c' x))
              = μ.integral (fun x : X => g c x + rest.sum (fun c' : ℂ => g c' x)) := by
                congr 1
                funext x
                rw [Finset.sum_insert hrest]
          _ = μ.integral (g c) + μ.integral (fun x : X => rest.sum (fun c' : ℂ => g c' x)) := by
                have hcont : μ.integral (fun x : X => rest.sum (fun c' : ℂ => g c' x)) =
                    μ.integral (rest.sum (fun c' : ℂ => g c')) := by
                  congr 1
                  funext x
                  rw [Finset.sum_apply]
                have hInt1 : μ.integral (fun x : X => g c x + rest.sum (fun c' : ℂ => g c' x)) =
                    μ.integral (g c) + μ.integral (rest.sum (fun c' : ℂ => g c')) := by
                  have hPeq : (fun x : X => g c x + rest.sum (fun c' : ℂ => g c' x)) =
                      g c + rest.sum (fun c' : ℂ => g c') := by
                    funext x
                    simp [Finset.sum_apply]
                  rw [hPeq]
                  exact integral_add μ hgc hsum_mem
                rw [hcont, ← hInt1]
          _ = (insert c rest).sum (fun c' : ℂ => μ.integral (g c')) := by
                rw [ih hgrest]
                rw [Finset.sum_insert hrest]
  -- Pointwise decomposition of `s` over its fibres.
  have hdecomp : ∀ x : X,
      s.range.sum (fun c : ℂ => c • (E c).indicator (fun _ : X => (1 : ℂ)) x) = s x := by
    intro x
    calc
      s.range.sum (fun c : ℂ => c • (E c).indicator (fun _ : X => (1 : ℂ)) x)
          = (s x) • (E (s x)).indicator (fun _ : X => (1 : ℂ)) x := by
            refine Finset.sum_eq_single (s x) ?_ ?_
            · intro c hc hcne
              have hx : x ∉ E c := by
                simp [E, Set.mem_preimage, hcne.symm]
              simp [hx]
            · intro hx
              exact (hx (SimpleFunc.mem_range_self s x)).elim
      _ = s x := by
            simp [E, Set.mem_preimage]
  -- The integral of `s` is the corresponding sum of spectral projections.
  have hSsum : μ.integral (fun x => s x) = s.range.sum (fun c : ℂ => c • μ (E c)) := by
    calc
      μ.integral (fun x => s x)
          = μ.integral (fun x => s.range.sum (fun c : ℂ => c • (E c).indicator (fun _ : X => (1 : ℂ)) x)) := by
            congr 1
            funext x
            exact (hdecomp x).symm
      _ = s.range.sum (fun c : ℂ => μ.integral (fun x : X => c • (E c).indicator (fun _ : X => (1 : ℂ)) x)) := by
            exact hlin s.range (fun c : ℂ => fun x : X => c • (E c).indicator (fun _ : X => (1 : ℂ)) x)
              (fun c _ => (BddMeasurable X).smul_mem c (hind c))
      _ = s.range.sum (fun c : ℂ => c • μ (E c)) := by
            apply Finset.sum_congr rfl
            intro c hc
            calc
              μ.integral (fun x : X => c • (E c).indicator (fun _ : X => (1 : ℂ)) x)
                  = μ.integral (c • (E c).indicator (fun _ : X => (1 : ℂ))) := rfl
              _ = c • μ.integral ((E c).indicator (fun _ : X => (1 : ℂ))) :=
                    μ.integral_smul c (hind c)
              _ = c • μ (E c) := by
                    rw [← μ.integral_indicator (hE c)]
                    rfl
  let S : H →L[ℂ] H := μ.integral (fun x => s x)
  have hSψ : ∀ ψ : H, S ψ = s.range.sum (fun c : ℂ => c • μ (E c) ψ) := by
    intro ψ
    change (μ.integral (fun x => s x)) ψ = s.range.sum (fun c : ℂ => c • μ (E c) ψ)
    -- t
    calc
      (μ.integral (fun x => s x)) ψ = (s.range.sum (fun c : ℂ => c • μ (E c))) ψ := by rw [hSsum]
      _ = s.range.sum (fun c : ℂ => (c • μ (E c)) ψ) := by simp
      _ = s.range.sum (fun c : ℂ => c • (μ (E c) ψ)) := by simp
  let M : ℝ := ⨆ x : X, ‖s x‖
  have hM0 : 0 ≤ M :=by
    dsimp [M]
    exact Real.iSup_nonneg (fun x : X => norm_nonneg (s x))
  have himg : (fun z : ℂ => ‖z‖) '' Set.range ⇑s = Set.range (fun y : X => ‖s y‖) :=by
    ext r
    constructor
    · rintro ⟨c, hc, rfl⟩
      rcases hc with ⟨y, hy⟩
      exact ⟨y, by rw [← hy]⟩
    · rintro ⟨y, rfl⟩
      refine ⟨s y, ⟨y, rfl⟩, rfl⟩
  have hBdd : BddAbove (Set.range (fun y : X => ‖s y‖)) :=by
    rw [← himg]
    exact (s.finite_range.image (fun z : ℂ => ‖z‖)).bddAbove
  have hM : ∀ c : ℂ, c ∈ s.range → ‖c‖ ≤ M :=by
    intro c hc
    rcases(SimpleFunc.mem_range.mp hc)with ⟨x, hx⟩
    rw [← hx]
    dsimp [M]
    exact le_ciSup (α := ℝ) (f := fun y : X => ‖s y‖) hBdd x
  -- the matrix element of `S` is the sum over the fibres
  have hmat : ∀ phi psi : H,
      inner ℂ phi (S psi) =
        ∑ c ∈ s.range, c * inner ℂ (μ (E c) phi) (μ (E c) psi) := by
    intro phi psi
    calc
      inner ℂ phi (S psi) = inner ℂ phi (∑ c ∈ s.range, c • (μ (E c) psi)) := by
            rw [hSψ]
      _ = ∑ c ∈ s.range, inner ℂ phi (c • (μ (E c) psi)) := by
            rw [inner_sum]
      _ = ∑ c ∈ s.range, c * inner ℂ phi (μ (E c) psi) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            rw [inner_smul_right]
      _ = ∑ c ∈ s.range, c * inner ℂ (μ (E c) phi) (μ (E c) psi) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            rw [inner_pvm_apply μ (E c) phi psi]
  have hsesq : ∀ phi psi : H, ‖inner ℂ phi (S psi)‖ ≤ M * ‖phi‖ * ‖psi‖ := by
    intro phi psi
    let a : ℂ → ℝ := fun c : ℂ => ‖μ (E c) phi‖
    let b : ℂ → ℝ := fun c : ℂ => ‖μ (E c) psi‖
    have hA : ‖inner ℂ phi (S psi)‖ ≤ ∑ c ∈ s.range, ‖c‖ * (a c * b c) := by
      calc
        ‖inner ℂ phi (S psi)‖ = ‖∑ c ∈ s.range, c * inner ℂ (μ (E c) phi) (μ (E c) psi)‖ := by
              rw [hmat]
        _ ≤ ∑ c ∈ s.range, ‖c * inner ℂ (μ (E c) phi) (μ (E c) psi)‖ := by
              exact norm_sum_le _ _
        _ = ∑ c ∈ s.range, ‖c‖ * ‖inner ℂ (μ (E c) phi) (μ (E c) psi)‖ := by
              refine Finset.sum_congr rfl ?_
              intro c hc
              rw [norm_mul]
        _ ≤ ∑ c ∈ s.range, ‖c‖ * (a c * b c) := by
              refine Finset.sum_le_sum ?_
              intro c hc
              exact mul_le_mul_of_nonneg_left
                (norm_inner_le_norm (μ (E c) phi) (μ (E c) psi)) (norm_nonneg (c : ℂ))
    have hB : (∑ c ∈ s.range, ‖c‖ * (a c * b c)) ≤ ∑ c ∈ s.range, M * (a c * b c) := by
      refine Finset.sum_le_sum ?_
      intro c hc
      have ha : 0 ≤ a c := by
        dsimp [a]
        positivity
      have hb : 0 ≤ b c := by
        dsimp [b]
        positivity
      exact mul_le_mul_of_nonneg_right (hM c hc) (mul_nonneg ha hb)
    have hC : (∑ c ∈ s.range, M * (a c * b c)) = M * ∑ c ∈ s.range, a c * b c := by
      rw [Finset.mul_sum]
    have hD : M * (∑ c ∈ s.range, a c * b c) ≤
        M * (√(∑ c ∈ s.range, a c ^ 2) * √(∑ c ∈ s.range, b c ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt s.range a b) hM0
    have hsqp : √(∑ c ∈ s.range, a c ^ 2) = ‖phi‖ := by
      have hsum : (∑ c ∈ s.range, a c ^ 2) = ‖phi‖ ^ 2 := by
        simpa [a, E] using (norm_sq_eq_sum_of_fibers μ s phi)
      rw [hsum]
      exact Real.sqrt_sq (norm_nonneg phi)
    have hsqb : √(∑ c ∈ s.range, b c ^ 2) = ‖psi‖ := by
      have hsum : (∑ c ∈ s.range, b c ^ 2) = ‖psi‖ ^ 2 := by
        simpa [b, E] using (norm_sq_eq_sum_of_fibers μ s psi)
      rw [hsum]
      exact Real.sqrt_sq (norm_nonneg psi)
    calc
      ‖inner ℂ phi (S psi)‖ ≤ ∑ c ∈ s.range, ‖c‖ * (a c * b c) := hA
      _ ≤ ∑ c ∈ s.range, M * (a c * b c) := hB
      _ = M * ∑ c ∈ s.range, a c * b c := hC
      _ ≤ M * (√(∑ c ∈ s.range, a c ^ 2) * √(∑ c ∈ s.range, b c ^ 2)) := hD
      _ = M * (‖phi‖ * ‖psi‖) := by
            rw [hsqp, hsqb]
      _ = M * ‖phi‖ * ‖psi‖ := by ring
  have hnorm : ∀ psi : H, ‖S psi‖ ≤ M * ‖psi‖ := by
    intro psi
    by_cases hpsi : S psi = 0
    · rw [hpsi]
      simpa using (mul_nonneg hM0 (norm_nonneg psi))
    · have hsq : ‖S psi‖ ^ 2 ≤ M * ‖S psi‖ * ‖psi‖ := by
        calc
          ‖S psi‖ ^ 2 = ‖inner ℂ (S psi) (S psi)‖ := by
                rw [inner_self_eq_norm_sq_to_K]
                rw [norm_pow]
                simpa using (Complex.norm_of_nonneg (norm_nonneg (S psi)))
          _ ≤ M * ‖S psi‖ * ‖psi‖ := hsesq (S psi) psi
      have hfac : ‖S psi‖ * ‖S psi‖ ≤ (M * ‖psi‖) * ‖S psi‖ := by
        nlinarith [hsq]
      have hpos : 0 < ‖S psi‖ := (norm_pos_iff.mpr hpsi)
      exact le_of_mul_le_mul_right hfac hpos
  exact ContinuousLinearMap.opNorm_le_bound S hM0 hnorm

/--
The operator norm of `∫ f dμ` is bounded by the supremum norm of `f`.

Blueprint reference: `prpstn:integral-norm-bound`.
-/
theorem norm_integral_le (μ : ProjectionValuedMeasure X H) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) : ‖μ.integral f‖ ≤ ⨆ x, ‖f x‖ := by
  classical
  -- the supremum norm of a bounded function
  let snorm : (X → ℂ) → ℝ := fun g => ⨆ x, ‖g x‖
  have hset_nonneg (g : X → ℂ) : 0 ≤ snorm g := by
    dsimp [snorm]
    exact Real.iSup_nonneg (fun x => norm_nonneg (g x))
  have hset_le (g : X → ℂ) (hg : g ∈ BddMeasurable X) (x : X) : ‖g x‖ ≤ snorm g := by
    dsimp [snorm]
    rcases exists_bound_of_mem_bddMeasurable hg with ⟨M, hM⟩
    have hBdd : BddAbove (Set.range fun y : X => ‖g y‖) :=
      ⟨M, by rintro r ⟨y, rfl⟩; exact hM y⟩
    exact le_ciSup (f := fun y : X => ‖g y‖) hBdd x
  -- the total mass of the measure associated with a vector is its squared norm
  have h_total : ∀ v : H, ((μ.assoc v) Set.univ).toReal = ‖v‖ ^ 2 := by
    intro v
    calc
      ((μ.assoc v) Set.univ).toReal = (⟪v, μ Set.univ v⟫_ℂ).re := μ.assoc_apply v MeasurableSet.univ
      _ = (⟪v, v⟫_ℂ).re := by simp
      _ = ‖v‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]
        rw [← map_pow]
        exact Complex.ofReal_re _
  -- (I) a preliminary bound for arbitrary bounded `g`: ‖∫ g dμ‖ ≤ 6 ‖g‖∞.
  have hSix (g : X → ℂ) (hg : g ∈ BddMeasurable X) : ‖μ.integral g‖ ≤ 6 * snorm g := by
    let Q : H → ℂ := fun v => ∫ x, g x ∂(μ.assoc v)
    have hQ : IsBoundedQuadraticForm Q := isBoundedQuadraticForm_integral_bddMeasurable μ hg
    have hT : μ.integral g = hQ.toOperator := by
      exact IsBoundedQuadraticForm.eq_toOperator hQ
        (fun v => by simpa [Q] using (inner_integral μ hg v).symm)
    have hQb (v : H) : ‖Q v‖ ≤ snorm g * ‖v‖ ^ 2 := by
      dsimp [Q]
      have hb : ‖∫ x, g x ∂(μ.assoc v)‖ ≤ snorm g * ((μ.assoc v) Set.univ).toReal := by
        simpa [measureReal_def] using
          (norm_integral_le_of_norm_le_const (μ := μ.assoc v) (f := g) (C := snorm g)
            (ae_of_all (μ.assoc v) (fun x => hset_le g hg x)))
      exact hb.trans (by rw [h_total v])
    -- ‖⟪χ, T ψ⟫‖ = ‖polarization Q χ ψ‖ for T = hQ.toOperator
    have hPolar (χ ψ : H) : ‖⟪χ, hQ.toOperator ψ⟫_ℂ‖ = ‖polarization Q χ ψ‖ := by
      have hsub : (fun ζ : H => ⟪ζ, hQ.toOperator ζ⟫_ℂ) = Q := by
        funext ζ
        exact (hQ.inner_toOperator ζ).symm
      calc
        ‖⟪χ, hQ.toOperator ψ⟫_ℂ‖ = ‖polarization (fun ζ : H => ⟪ζ, hQ.toOperator ζ⟫_ℂ) χ ψ‖ := by
          rw [polarization_inner]
        _ = ‖polarization Q χ ψ‖ := by
          exact congrArg (fun F : H → ℂ => ‖polarization F χ ψ‖) hsub
    have htriple (a b c : ℂ) : ‖a - b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
      calc
        ‖a - b - c‖ ≤ ‖a - b‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := add_le_add (norm_sub_le a b) le_rfl
    -- the polarization estimate on unit vectors
    have hpol : ∀ {χ ψ : H}, ‖χ‖ = 1 → ‖ψ‖ = 1 → ‖polarization Q χ ψ‖ ≤ 6 * snorm g := by
      intro χ ψ hχ hψ
      have hgt : 0 ≤ snorm g := hset_nonneg g
      have hsum1 : (‖χ + ψ‖ : ℝ) ^ 2 ≤ 4 := by
        have h2 : ‖χ + ψ‖ ≤ 2 := by
          nlinarith [norm_add_le χ ψ, hχ, hψ]
        have h2' : (‖χ + ψ‖ : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg (χ + ψ)) h2 2
        nlinarith
      have hI : ‖Complex.I • ψ‖ = 1 := by
        rw [norm_smul, hψ]
        norm_num
      have hsum2 : (‖χ + Complex.I • ψ‖ : ℝ) ^ 2 ≤ 4 := by
        have h3 : ‖χ + Complex.I • ψ‖ ≤ 2 := by
          nlinarith [norm_add_le χ (Complex.I • ψ), hχ, hI]
        have h3' : (‖χ + Complex.I • ψ‖ : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
        nlinarith
      have hpow : (‖ψ‖ : ℝ) ^ 2 = 1 := by rw [hψ]; norm_num
      have hpowχ : (‖χ‖ : ℝ) ^ 2 = 1 := by rw [hχ]; norm_num
      have hblk1 : ‖Q (χ + ψ) - Q χ - Q ψ‖ ≤ 6 * snorm g := by
        calc
          ‖Q (χ + ψ) - Q χ - Q ψ‖ ≤ ‖Q (χ + ψ)‖ + ‖Q χ‖ + ‖Q ψ‖ := htriple _ _ _
          _ ≤ snorm g * (‖χ + ψ‖ ^ 2 + ‖χ‖ ^ 2 + ‖ψ‖ ^ 2) := by
                have hL : ‖Q (χ + ψ)‖ + ‖Q χ‖ + ‖Q ψ‖ ≤
                    snorm g * ‖χ + ψ‖ ^ 2 + snorm g * ‖χ‖ ^ 2 + snorm g * ‖ψ‖ ^ 2 :=
                  add_le_add (add_le_add (hQb (χ + ψ)) (hQb χ)) (hQb ψ)
                exact hL.trans_eq (by ring)
          _ ≤ snorm g * (4 + 1 + 1) := by
            exact mul_le_mul_of_nonneg_left (by nlinarith [hsum1, hpowχ, hpow]) hgt
          _ = 6 * snorm g := by ring
      have hblk2 : ‖Q (χ + Complex.I • ψ) - Q χ - Q (Complex.I • ψ)‖ ≤ 6 * snorm g := by
        calc
          ‖Q (χ + Complex.I • ψ) - Q χ - Q (Complex.I • ψ)‖
              ≤ ‖Q (χ + Complex.I • ψ)‖ + ‖Q χ‖ + ‖Q (Complex.I • ψ)‖ :=
                htriple _ _ _
          _ ≤ snorm g * (‖χ + Complex.I • ψ‖ ^ 2 + ‖χ‖ ^ 2 + ‖Complex.I • ψ‖ ^ 2) := by
                have hL : ‖Q (χ + Complex.I • ψ)‖ + ‖Q χ‖ + ‖Q (Complex.I • ψ)‖ ≤
                    snorm g * ‖χ + Complex.I • ψ‖ ^ 2 + snorm g * ‖χ‖ ^ 2 +
                      snorm g * ‖Complex.I • ψ‖ ^ 2 :=
                  add_le_add (add_le_add (hQb (χ + Complex.I • ψ)) (hQb χ))
                    (hQb (Complex.I • ψ))
                exact hL.trans_eq (by ring)
          _ ≤ snorm g * (4 + 1 + 1) := by
            have hpowI : (‖Complex.I • ψ‖ : ℝ) ^ 2 = 1 := by rw [hI]; norm_num
            exact mul_le_mul_of_nonneg_left (by nlinarith [hsum2, hpowχ, hpow, hpowI]) hgt
          _ = 6 * snorm g := by ring
      calc
        ‖polarization Q χ ψ‖
            = ‖(1 / 2 : ℂ) * (Q (χ + ψ) - Q χ - Q ψ) -
                (Complex.I / 2) * (Q (χ + Complex.I • ψ) - Q χ - Q (Complex.I • ψ))‖ := by rfl
        _ ≤ ‖(1 / 2 : ℂ) * (Q (χ + ψ) - Q χ - Q ψ)‖ +
            ‖(Complex.I / 2) * (Q (χ + Complex.I • ψ) - Q χ - Q (Complex.I • ψ))‖ :=
              norm_sub_le _ _
        _ = (1 / 2 : ℝ) * ‖Q (χ + ψ) - Q χ - Q ψ‖ +
            (1 / 2 : ℝ) * ‖Q (χ + Complex.I • ψ) - Q χ - Q (Complex.I • ψ)‖ := by
              have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
              have hhalfI : ‖(Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
              rw [norm_mul, norm_mul, hhalf, hhalfI]
        _ ≤ (1 / 2) * (6 * snorm g) + (1 / 2) * (6 * snorm g) := by
              exact add_le_add (mul_le_mul_of_nonneg_left hblk1 (by norm_num))
                (mul_le_mul_of_nonneg_left hblk2 (by norm_num))
        _ = 6 * snorm g := by ring
    have hmat : ∀ χ ψ : H, ‖χ‖ = 1 → ‖ψ‖ = 1 →
        ‖⟪χ, hQ.toOperator ψ⟫_ℂ‖ ≤ 6 * snorm g := by
      intro χ ψ hχ hψ
      rw [hPolar]
      exact hpol hχ hψ
    rw [hT, opNorm_eq_sSup_inner]
    exact Real.sSup_le (by
      rintro r ⟨χ, ψ, hχ, hψ, rfl⟩
      exact hmat χ ψ hχ hψ) (by nlinarith [hset_nonneg g])
  -- (II) the sharp bound for simple functions: ‖∫ s dμ‖ ≤ ‖s‖∞, cited as the
  -- black-box declaration `norm_integral_simple_le` (proved by another prover in
  -- the real file).
  have hsimple : ∀ (s : SimpleFunc X ℂ), ‖μ.integral (fun x => s x)‖ ≤ snorm (fun x => s x) := by
    intro s
    exact le_trans (norm_integral_simple_le μ s) (by
      dsimp [snorm]
      exact le_rfl)
  -- (III) uniform approximation and passing to the limit
  rcases exists_simpleFunc_tendstoUniformly hf with ⟨s, hs⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε7 : 0 < ε / (7 : ℝ) := by nlinarith
  have hlt_base : ∀ᶠ n in atTop, ∀ x : X, dist (s n x) (f x) < ε / (7 : ℝ) := by
    simpa [dist_comm] using (Metric.tendstoUniformly_iff.mp hs) (ε / (7 : ℝ)) hε7
  rcases (eventually_atTop.mp hlt_base) with ⟨N, hN⟩
  have hbig : ‖μ.integral f‖ ≤ (⨆ x, ‖f x‖) + ε := by
    have hsn : (fun x : X => s N x) ∈ BddMeasurable X := by
      rw [mem_bddMeasurable]
      exact ⟨(s N).measurable, (s N).exists_forall_norm_le⟩
    have hΔ : (fun x : X => s N x - f x) ∈ BddMeasurable X :=
      (BddMeasurable X).sub_mem hsn hf
    have hlt (x : X) : ‖s N x - f x‖ < ε / (7 : ℝ) := by
      have hd : ‖s N x - f x‖ < ε / (7 : ℝ) := by
        simpa [dist_eq_norm] using hN N le_rfl x
      exact hd
    have hsnorm : snorm (fun x : X => s N x - f x) ≤ ε / (7 : ℝ) := by
      exact Real.iSup_le (fun x : X => le_of_lt (hlt x)) (le_of_lt hε7)
    have hdiff : ‖μ.integral (fun x => s N x - f x)‖ ≤ 6 * (ε / (7 : ℝ)) := by
      exact le_trans (hSix (fun x => s N x - f x) hΔ)
        (by nlinarith [hsnorm])
    have hlin : μ.integral (fun x => s N x) - μ.integral f =
        μ.integral (fun x => s N x - f x) := by
      have hfneg : (fun x : X => -f x) ∈ BddMeasurable X := by
        rw [mem_bddMeasurable]
        rcases hf with ⟨hfmeas, Cf, hC⟩
        exact ⟨hfmeas.neg, ⟨Cf, fun x => by simpa using hC x⟩⟩
      have hneg : μ.integral (fun x => -f x) = -(μ.integral f) := by
        have hsmul : μ.integral ((-1 : ℂ) • f) = (-1 : ℂ) • μ.integral f := integral_smul μ (-1) hf
        calc
          μ.integral (fun x => -f x) = μ.integral ((-1 : ℂ) • f) := by
            congr 1
            funext x
            simp
          _ = (-1 : ℂ) • μ.integral f := hsmul
          _ = -(μ.integral f) := by simp
      calc
        μ.integral (fun x => s N x) - μ.integral f
            = μ.integral (fun x => s N x) + μ.integral (fun x => -f x) := by
              rw [sub_eq_add_neg, ← hneg]
        _ = μ.integral ((fun x : X => s N x) + (fun x : X => -f x)) :=
            (integral_add μ hsn hfneg).symm
        _ = μ.integral (fun x => s N x - f x) := rfl
    have hfdiff : ‖μ.integral (fun x => s N x) - μ.integral f‖ ≤ 6 * (ε / (7 : ℝ)) := by
      rw [hlin]
      exact hdiff
    have htri : ‖μ.integral f‖
        ≤ ‖μ.integral (fun x => s N x)‖ + ‖μ.integral (fun x => s N x) - μ.integral f‖ := by
      calc
        ‖μ.integral f‖
            = ‖μ.integral (fun x => s N x) - (μ.integral (fun x => s N x) - μ.integral f)‖ := by
              congr 1
              abel
        _ ≤ ‖μ.integral (fun x => s N x)‖ + ‖μ.integral (fun x => s N x) - μ.integral f‖ :=
            norm_sub_le _ _
    have hmain : ‖μ.integral f‖ ≤ ‖μ.integral (fun x => s N x)‖ + 6 * (ε / (7 : ℝ)) := by
      exact le_trans htri (add_le_add_right hfdiff (‖μ.integral (fun x => s N x)‖))
    have hpt (x : X) : ‖s N x‖ ≤ (⨆ x, ‖f x‖) + ε / (7 : ℝ) := by
      calc
        ‖s N x‖ = ‖(s N x - f x) + f x‖ := by
          congr 1
          abel
        _ ≤ ‖s N x - f x‖ + ‖f x‖ := norm_add_le _ _
        _ ≤ ε / (7 : ℝ) + (⨆ x, ‖f x‖) := by
          exact add_le_add (le_of_lt (hlt x)) (hset_le f hf x)
        _ = (⨆ x, ‖f x‖) + ε / (7 : ℝ) := by ring
    have hsupf : 0 ≤ (⨆ x, ‖f x‖) := by
      exact hset_nonneg f
    have hsups : snorm (fun x => s N x) ≤ (⨆ x, ‖f x‖) + ε / (7 : ℝ) := by
      exact Real.iSup_le hpt (add_nonneg hsupf (le_of_lt hε7))
    have hsimpN : ‖μ.integral (fun x => s N x)‖ ≤ snorm (fun x => s N x) := hsimple (s N)
    have hup : ‖μ.integral (fun x => s N x)‖ ≤ (⨆ x, ‖f x‖) + ε / (7 : ℝ) :=
      le_trans hsimpN hsups
    calc
      ‖μ.integral f‖ ≤ ‖μ.integral (fun x => s N x)‖ + 6 * (ε / (7 : ℝ)) := hmain
      _ ≤ ((⨆ x, ‖f x‖) + ε / (7 : ℝ)) + 6 * (ε / (7 : ℝ)) := by
        exact add_le_add_left hup (6 * (ε / (7 : ℝ)))
      _ = (⨆ x, ‖f x‖) + ε := by ring
  exact hbig

/--
If simple functions `sᵢ` converge uniformly to a bounded measurable `f`, then the
operators `∫ sᵢ dμ` converge in operator norm to `∫ f dμ`.

The blueprint also asserts that `∫ sᵢ dμ` is a Cauchy sequence; that is
`Filter.Tendsto.cauchySeq` applied to the conclusion below, so it is not restated.

Blueprint reference: `prpstn:integral-as-limit-of-simple`.
-/
theorem tendsto_integral_of_tendstoUniformly (μ : ProjectionValuedMeasure X H) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) {s : ℕ → SimpleFunc X ℂ}
    (hs : TendstoUniformly (fun n x => s n x) f atTop) :
    Tendsto (fun n => μ.integral (fun x => s n x)) atTop (𝓝 (μ.integral f)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- uniform convergence of `s n` to `f` gives a pointwise bound on `‖s n x - f x‖`
  have hsε : ∀ᶠ n in atTop, ∀ x : X, dist (s n x) (f x) < ε / 2 := by
    simpa [dist_comm] using (Metric.tendstoUniformly_iff.mp hs) (ε / 2) (half_pos hε)
  rcases (Filter.eventually_atTop.mp hsε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hlt : ∀ x : X, ‖s n x - f x‖ < ε / 2 := fun x =>
    by simpa [dist_eq_norm] using hN n hn x
  -- each `s n` is bounded measurable
  have hsn : (fun x : X => s n x) ∈ BddMeasurable X := by
    rw [mem_bddMeasurable]
    exact ⟨(s n).measurable, (s n).exists_forall_norm_le⟩
  -- linearity: `∫ sₙ dμ - ∫ f dμ = ∫ (sₙ - f) dμ`
  have hlin : μ.integral (fun x => s n x) - μ.integral f =
      μ.integral (fun x => s n x - f x) := by
    have hfneg : (fun x : X => -f x) ∈ BddMeasurable X := by
      rw [mem_bddMeasurable]
      rcases hf with ⟨hfmeas, Cf, hC⟩
      exact ⟨hfmeas.neg, ⟨Cf, fun x => by simpa using hC x⟩⟩
    have hneg : μ.integral (fun x => -f x) = -(μ.integral f) := by
      have hsmul : μ.integral ((-1 : ℂ) • f) = (-1 : ℂ) • μ.integral f := integral_smul μ (-1) hf
      calc
        μ.integral (fun x => -f x) = μ.integral ((-1 : ℂ) • f) := by
          congr 1
          funext x
          simp
        _ = (-1 : ℂ) • μ.integral f := hsmul
        _ = -(μ.integral f) := by simp
    calc
      μ.integral (fun x => s n x) - μ.integral f
          = μ.integral (fun x => s n x) + μ.integral (fun x => -f x) := by
            rw [sub_eq_add_neg, ← hneg]
      _ = μ.integral ((fun x : X => s n x) + (fun x : X => -f x)) :=
            (integral_add μ hsn hfneg).symm
      _ = μ.integral (fun x => s n x - f x) := rfl
  -- the difference-integral is bounded by `ε / 2` (via `norm_integral_le`, by name)
  have hnorm : ‖μ.integral (fun x => s n x - f x)‖ ≤ ε / 2 := by
    have hΔ : (fun x : X => s n x - f x) ∈ BddMeasurable X := (BddMeasurable X).sub_mem hsn hf
    have hsup : (⨆ x, ‖s n x - f x‖) ≤ ε / 2 := by
      exact Real.iSup_le (fun x : X => le_of_lt (hlt x)) (le_of_lt (half_pos hε))
    exact le_trans (norm_integral_le μ hΔ) hsup
  calc
    dist (μ.integral (fun x => s n x)) (μ.integral f)
        = ‖μ.integral (fun x => s n x) - μ.integral f‖ := by rw [dist_eq_norm]
    _ = ‖μ.integral (fun x => s n x - f x)‖ := by rw [hlin]
    _ ≤ ε / 2 := hnorm
    _ < ε := by linarith

/--
Multiplicativity of the integral on indicator functions.

Blueprint reference: `prpstn:integral-mult-indicator`.
-/
theorem integral_indicator_mul (μ : ProjectionValuedMeasure X H) {E F : Set X}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    μ.integral (E.indicator (1 : X → ℂ) * F.indicator (1 : X → ℂ)) =
      μ.integral (E.indicator (1 : X → ℂ)) * μ.integral (F.indicator (1 : X → ℂ)) := by
  calc
    μ.integral (E.indicator (1 : X → ℂ) * F.indicator (1 : X → ℂ))
        = μ.integral ((E ∩ F).indicator (1 : X → ℂ)) := by
          rw [← Set.inter_indicator_one]
    _ = μ (E ∩ F) := μ.integral_indicator (hE.inter hF)
    _ = μ E * μ F := μ.apply_inter hE hF
    _ = μ.integral (E.indicator (1 : X → ℂ)) * μ.integral (F.indicator (1 : X → ℂ)) := by
          rw [μ.integral_indicator hE, μ.integral_indicator hF]

/--
Multiplicativity of the integral on simple functions.

Blueprint reference: `prpstn:integral-mult-simple`.
-/
theorem integral_simpleFunc_mul (μ : ProjectionValuedMeasure X H) (s r : SimpleFunc X ℂ) :
    μ.integral (fun x => s x * r x) =
      μ.integral (fun x => s x) * μ.integral (fun x => r x) := by
  classical
  -- `i c` and `j d` are the indicators of the fibres `s ⁻¹' {c}` and `r ⁻¹' {d}`.
  let i : ℂ → X → ℂ := fun c => (s ⁻¹' {c}).indicator (1 : X → ℂ)
  let j : ℂ → X → ℂ := fun d => (r ⁻¹' {d}).indicator (1 : X → ℂ)
  have hi : ∀ c, i c ∈ BddMeasurable X := by
    intro c
    rw [mem_bddMeasurable]
    refine ⟨measurable_const.indicator (s.measurableSet_fiber c), ⟨1, ?_⟩⟩
    intro x
    by_cases hx : x ∈ s ⁻¹' {c}
    · simp [i, hx]
    · simp [i, hx]
  have hj : ∀ d, j d ∈ BddMeasurable X := by
    intro d
    rw [mem_bddMeasurable]
    refine ⟨measurable_const.indicator (r.measurableSet_fiber d), ⟨1, ?_⟩⟩
    intro x
    by_cases hx : x ∈ r ⁻¹' {d}
    · simp [j, hx]
    · simp [j, hx]
  have hij_mem : ∀ c d, i c * j d ∈ BddMeasurable X := by
    intro c d
    rw [mem_bddMeasurable]
    refine ⟨(measurable_of_mem_bddMeasurable (hi c)).mul (measurable_of_mem_bddMeasurable (hj d)),
      ⟨1, ?_⟩⟩
    intro x
    by_cases hx : x ∈ s ⁻¹' {c}
    · by_cases hy : x ∈ r ⁻¹' {d}
      · simp [i, j, hx, hy]
      · simp [i, j, hx, hy]
    · simp [i, j, hx]
  have hzero : μ.integral (0 : X → ℂ) = 0 := by
    have hone : (1 : X → ℂ) ∈ BddMeasurable X := by
      rw [mem_bddMeasurable]
      exact ⟨measurable_const, ⟨1, by intro x; simp⟩⟩
    simpa using (integral_smul μ (0 : ℂ) (f := (1 : X → ℂ)) hone)
  -- the integral is linear over finite sums of bounded measurable functions
  have hsum : ∀ (u : Finset ℂ) (a : ℂ → X → ℂ),
      (∀ c ∈ u, a c ∈ BddMeasurable X) →
      μ.integral (fun x => ∑ c ∈ u, a c x) = ∑ c ∈ u, μ.integral (a c) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        intro a ha
        change μ.integral (0 : X → ℂ) = 0
        exact hzero
    | insert c t hct ih =>
        intro a ha
        have hg : (fun x : X => ∑ d ∈ t, a d x) ∈ BddMeasurable X := by
          have hsumfun : (fun x : X => ∑ d ∈ t, a d x) = (∑ d ∈ t, a d) := by
            funext x
            rw [Finset.sum_apply]
          rw [hsumfun]
          exact (BddMeasurable X).sum_mem (fun d hd => ha d (Finset.mem_insert_of_mem hd))
        simp_rw [Finset.sum_insert hct]
        change μ.integral (a c + fun x : X => ∑ d ∈ t, a d x) =
          μ.integral (a c) + ∑ d ∈ t, μ.integral (a d)
        rw [integral_add μ (ha c (Finset.mem_insert_self c t)) hg]
        rw [ih a (fun d hd => ha d (Finset.mem_insert_of_mem hd))]
  -- pointwise decompositions `s = ∑ c, c • i c` and `r = ∑ d, d • j d`
  have hs : ∀ x, s x = ∑ c ∈ s.range, (c • i c) x := by
    intro x
    have hdecomp : (∑ c ∈ s.range, (c • i c) x) = (s x • i (s x)) x := by
      refine Finset.sum_eq_single (s x) ?_ ?_
      · intro c hc hcne
        have hx : x ∉ s ⁻¹' {c} := by
          simp [Set.mem_preimage, hcne.symm]
        simp [i, hx]
      · intro hx
        exact (hx (SimpleFunc.mem_range_self s x)).elim
    calc
      s x = (s x • i (s x)) x := by
        simp [i, Set.mem_preimage]
      _ = ∑ c ∈ s.range, (c • i c) x := hdecomp.symm
  have hr : ∀ x, r x = ∑ d ∈ r.range, (d • j d) x := by
    intro x
    have hdecomp : (∑ d ∈ r.range, (d • j d) x) = (r x • j (r x)) x := by
      refine Finset.sum_eq_single (r x) ?_ ?_
      · intro d hd hdne
        have hx : x ∉ r ⁻¹' {d} := by
          simp [Set.mem_preimage, hdne.symm]
        simp [j, hx]
      · intro h
        exact (h (SimpleFunc.mem_range_self r x)).elim
    calc
      r x = (r x • j (r x)) x := by
        simp [j, Set.mem_preimage]
      _ = ∑ d ∈ r.range, (d • j d) x := hdecomp.symm
  -- the integral of a product of fibre indicators is the product of the integrals
  have hij_mul : ∀ c d,
      μ.integral (i c * j d) = μ.integral (i c) * μ.integral (j d) := by
    intro c d
    rw [show i c = (s ⁻¹' {c}).indicator (1 : X → ℂ) by rfl]
    rw [show j d = (r ⁻¹' {d}).indicator (1 : X → ℂ) by rfl]
    exact integral_indicator_mul μ (s.measurableSet_fiber c) (r.measurableSet_fiber d)
  -- pointwise pairing of the two fibre sums
  have hscalar : ∀ c d x, (c • i c) x * (d • j d) x = ((c * d) • (i c * j d)) x := by
    intro c d x
    simp
    ring
  -- the fibre indicators are bounded by `1`
  have hi_bound : ∀ c x, ‖i c x‖ ≤ 1 := by
    intro c x
    by_cases hx : x ∈ s ⁻¹' {c}
    · simp [i, hx]
    · simp [i, hx]
  have hj_bound : ∀ d x, ‖j d x‖ ≤ 1 := by
    intro d x
    by_cases hx : x ∈ r ⁻¹' {d}
    · simp [j, hx]
    · simp [j, hx]
  have hnorm_of : ∀ (a : ℂ) (u : X → ℂ), (∀ x, ‖u x‖ ≤ 1) → ∀ x, ‖(a • u) x‖ ≤ ‖a‖ := by
    intro a u hu x
    calc
      ‖(a • u) x‖ = ‖a‖ * ‖u x‖ := by simp
      _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left (hu x) (norm_nonneg a)
      _ = ‖a‖ := by simp
  -- `r` itself is a bounded measurable function
  have hr_mem : (fun x : X => r x) ∈ BddMeasurable X := by
    rw [mem_bddMeasurable]
    refine ⟨r.measurable, ?_⟩
    exact SimpleFunc.exists_forall_norm_le r
  -- products of a fibre term with `r` are bounded measurable
  have hcr_mem : ∀ c, (fun x : X => (c • i c) x * r x) ∈ BddMeasurable X := by
    intro c
    rcases SimpleFunc.exists_forall_norm_le r with ⟨C, hC⟩
    rw [mem_bddMeasurable]
    refine ⟨(measurable_of_mem_bddMeasurable ((BddMeasurable X).smul_mem c (hi c))).mul
      r.measurable, ⟨‖c‖ * C, ?_⟩⟩
    intro x
    calc
      ‖(c • i c) x * r x‖ = ‖(c • i c) x‖ * ‖r x‖ := by rw [norm_mul]
      _ ≤ ‖c‖ * C := by
        exact mul_le_mul (hnorm_of c (i c) (hi_bound c) x) (hC x) (norm_nonneg _) (norm_nonneg _)
  -- products of two simple terms are bounded measurable
  have hcd_mem : ∀ c d, (fun x : X => (c • i c) x * (d • j d) x) ∈ BddMeasurable X := by
    intro c d
    rw [mem_bddMeasurable]
    refine ⟨(measurable_of_mem_bddMeasurable ((BddMeasurable X).smul_mem c (hi c))).mul
      (measurable_of_mem_bddMeasurable ((BddMeasurable X).smul_mem d (hj d))),
      ⟨‖c‖ * ‖d‖, ?_⟩⟩
    intro x
    calc
      ‖(c • i c) x * (d • j d) x‖ = ‖(c • i c) x‖ * ‖(d • j d) x‖ := by rw [norm_mul]
      _ ≤ ‖c‖ * ‖d‖ := by
        exact mul_le_mul (hnorm_of c (i c) (hi_bound c) x) (hnorm_of d (j d) (hj_bound d) x)
          (norm_nonneg _) (norm_nonneg _)
  -- multiplication by scalars is bilinear in the algebra of bounded operators
  have hsmul_mul : ∀ (a b : ℂ) (A B : H →L[ℂ] H), (a • A) * (b • B) = (a * b) • (A * B) := by
    intro a b A B
    ext x
    simp [smul_smul, mul_comm]
  -- the integral of `s` is the sum over its range
  have hleft : μ.integral (fun x => s x) = ∑ c ∈ s.range, c • μ.integral (i c) := by
    calc
      μ.integral (fun x => s x) = μ.integral (fun x => ∑ c ∈ s.range, (c • i c) x) := by
        congr 1
        funext x
        exact hs x
      _ = ∑ c ∈ s.range, μ.integral (c • i c) := by
        rw [hsum s.range (fun c => c • i c) ?_]
        intro c hc
        exact (BddMeasurable X).smul_mem c (hi c)
      _ = ∑ c ∈ s.range, c • μ.integral (i c) := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        exact integral_smul μ c (hi c)
  have hright : μ.integral (fun x => r x) = ∑ d ∈ r.range, d • μ.integral (j d) := by
    calc
      μ.integral (fun x => r x) = μ.integral (fun x => ∑ d ∈ r.range, (d • j d) x) := by
        congr 1
        funext x
        exact hr x
      _ = ∑ d ∈ r.range, μ.integral (d • j d) := by
        rw [hsum r.range (fun d => d • j d) ?_]
        intro d hd
        exact (BddMeasurable X).smul_mem d (hj d)
      _ = ∑ d ∈ r.range, d • μ.integral (j d) := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        exact integral_smul μ d (hj d)
  calc
    μ.integral (fun x => s x * r x)
        = μ.integral (fun x => (∑ c ∈ s.range, (c • i c) x) * r x) := by
          congr 1
          funext x
          rw [hs x]
    _ = μ.integral (fun x => ∑ c ∈ s.range, (c • i c) x * r x) := by
          congr 1
          funext x
          rw [Finset.sum_mul]
    _ = ∑ c ∈ s.range, μ.integral (fun x => (c • i c) x * r x) := by
          rw [hsum s.range (fun c => fun x => (c • i c) x * r x) ?_]
          intro c hc
          exact hcr_mem c
    _ = ∑ c ∈ s.range, μ.integral (fun x => (c • i c) x * (∑ d ∈ r.range, (d • j d) x)) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          congr 1
          funext x
          rw [hr x]
    _ = ∑ c ∈ s.range, μ.integral (fun x => ∑ d ∈ r.range, (c • i c) x * (d • j d) x) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          congr 1
          funext x
          rw [Finset.mul_sum]
    _ = ∑ c ∈ s.range, ∑ d ∈ r.range, μ.integral (fun x => (c • i c) x * (d • j d) x) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          rw [hsum r.range (fun d => fun x => (c • i c) x * (d • j d) x) ?_]
          intro d hd
          exact hcd_mem c d
    _ = ∑ c ∈ s.range, ∑ d ∈ r.range, (c * d) • μ.integral (i c * j d) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          refine Finset.sum_congr rfl ?_
          intro d hd
          calc
            μ.integral (fun x => (c • i c) x * (d • j d) x)
                = μ.integral (fun x => ((c * d) • (i c * j d)) x) := by
                  congr 1
                  funext x
                  exact hscalar c d x
            _ = (c * d) • μ.integral (i c * j d) := by
                  change μ.integral ((c * d) • (i c * j d)) = (c * d) • μ.integral (i c * j d)
                  exact integral_smul μ (c * d) (hij_mem c d)
    _ = ∑ c ∈ s.range, ∑ d ∈ r.range, (c * d) • (μ.integral (i c) * μ.integral (j d)) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          refine Finset.sum_congr rfl ?_
          intro d hd
          rw [hij_mul c d]
    _ = (∑ c ∈ s.range, c • μ.integral (i c)) * (∑ d ∈ r.range, d • μ.integral (j d)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro c hc
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro d hd
          exact (hsmul_mul c d (μ.integral (i c)) (μ.integral (j d))).symm
    _ = μ.integral (fun x => s x) * μ.integral (fun x => r x) := by
          rw [hleft, hright]

/--
Multiplicativity of the integral on bounded measurable functions.

This is the third and last stage of the argument summarised by `integral_mul`: it is
obtained from `integral_simpleFunc_mul` by uniform approximation, using
`tendstoUniformly_mul_of_bounded` and `tendsto_integral_of_tendstoUniformly`.

Blueprint reference: `prpstn:integral-mult-measurable`.
-/
theorem integral_bddMeasurable_mul (μ : ProjectionValuedMeasure X H) {f g : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hg : g ∈ BddMeasurable X) :
    μ.integral (f * g) = μ.integral f * μ.integral g := by
  classical
  -- approximate `f` and `g` uniformly by simple functions
  obtain ⟨s, hs⟩ := exists_simpleFunc_tendstoUniformly hf
  obtain ⟨r, hr⟩ := exists_simpleFunc_tendstoUniformly hg
  have hfg : f * g ∈ BddMeasurable X := by
    rw [mem_bddMeasurable]
    rcases hf with ⟨hfmeas, Cf, hCf⟩
    rcases hg with ⟨hgmeas, Cg, hCg⟩
    refine ⟨hfmeas.mul hgmeas, ⟨Cf * Cg, ?_⟩⟩
    intro x
    calc
      ‖(f * g) x‖ = ‖f x * g x‖ := rfl
      _ ≤ ‖f x‖ * ‖g x‖ := norm_mul_le _ _
      _ ≤ Cf * Cg := mul_le_mul (hCf x) (hCg x) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hCf x))
  -- `sᵢ rᵢ → f g` uniformly along the diagonal: the diagonal case of
  -- `tendstoUniformly_mul_of_bounded` (which lives below this declaration and so
  -- cannot be cited here), proved with the blueprint's ε/2-splitting.
  have hdiag : TendstoUniformly (fun n x => s n x * r n x) (f * g) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    rcases exists_bound_of_mem_bddMeasurable hf with ⟨Mf, hMf⟩
    rcases exists_bound_of_mem_bddMeasurable hg with ⟨Mg, hMg⟩
    let Mf' : ℝ := max Mf 0
    let Mg' : ℝ := max Mg 0
    have hMf' : 0 ≤ Mf' := le_max_right Mf 0
    have hMg' : 0 ≤ Mg' := le_max_right Mg 0
    have hMf'1 : 0 < Mf' + 1 := by linarith
    have hMg'1 : 0 < Mg' + 1 := by linarith
    have hMf0 : ∀ x, ‖f x‖ ≤ Mf' := fun x => le_trans (hMf x) (le_max_left Mf 0)
    have hMg0 : ∀ x, ‖g x‖ ≤ Mg' := fun x => le_trans (hMg x) (le_max_left Mg 0)
    have hs' : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, dist (f x) (s n x) < ε :=
      Metric.tendstoUniformly_iff.mp hs
    have hr' : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, dist (g x) (r n x) < ε :=
      Metric.tendstoUniformly_iff.mp hr
    have hsε : ∀ᶠ n in atTop, ∀ x, dist (f x) (s n x) < ε / (2 * (Mg' + 1)) :=
      hs' (ε / (2 * (Mg' + 1))) (by positivity)
    have hrε : ∀ᶠ n in atTop, ∀ x, dist (g x) (r n x) < ε / (2 * (Mf' + 1)) :=
      hr' (ε / (2 * (Mf' + 1))) (by positivity)
    have hr1 : ∀ᶠ n in atTop, ∀ x, dist (g x) (r n x) < 1 := hr' 1 zero_lt_one
    filter_upwards [hsε, hrε, hr1] with n hsn hrn hr1n x
    calc
      dist ((f * g) x) (s n x * r n x) = ‖f x * g x - s n x * r n x‖ := by
        simp [dist_eq_norm]
      _ ≤ ‖(f x - s n x) * r n x‖ + ‖f x * (g x - r n x)‖ := by
        rw [show f x * g x - s n x * r n x = (f x - s n x) * r n x + f x * (g x - r n x) by ring]
        exact norm_add_le _ _
      _ ≤ ‖f x - s n x‖ * ‖r n x‖ + ‖f x‖ * ‖g x - r n x‖ := by
        exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖f x - s n x‖ * (Mg' + 1) + Mf' * ‖g x - r n x‖ := by
        have hrx : ‖r n x‖ ≤ Mg' + 1 := by
          have hd : ‖g x - r n x‖ < 1 := by simpa [dist_eq_norm] using hr1n x
          have hd' : ‖r n x - g x‖ ≤ 1 := by
            simpa [norm_sub_rev] using le_of_lt hd
          calc
            ‖r n x‖ = ‖(r n x - g x) + g x‖ := by
              congr 1
              ring
            _ ≤ ‖r n x - g x‖ + ‖g x‖ := norm_add_le _ _
            _ ≤ Mg' + 1 := by
              nlinarith [hd', hMg0 x]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hrx (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hMf0 x) (norm_nonneg _))
      _ < ε := by
        have h1 : ‖f x - s n x‖ * (Mg' + 1) < ε / 2 := by
          have hd : ‖f x - s n x‖ < ε / (2 * (Mg' + 1)) := by
            simpa [dist_eq_norm] using hsn x
          have heq : (ε / (2 * (Mg' + 1))) * (Mg' + 1) = ε / 2 := by
            field_simp [hMg'1.ne']
          exact lt_of_lt_of_eq (mul_lt_mul_of_pos_right hd hMg'1) heq
        have h2 : Mf' * ‖g x - r n x‖ < ε / 2 := by
          have hd : ‖g x - r n x‖ < ε / (2 * (Mf' + 1)) := by
            simpa [dist_eq_norm] using hrn x
          have hle : Mf' * ‖g x - r n x‖ ≤ Mf' * (ε / (2 * (Mf' + 1))) :=
            mul_le_mul_of_nonneg_left (le_of_lt hd) hMf'
          have hlt : Mf' * (ε / (2 * (Mf' + 1))) < ε / 2 := by
            calc
              Mf' * (ε / (2 * (Mf' + 1))) < (Mf' + 1) * (ε / (2 * (Mf' + 1))) :=
                mul_lt_mul_of_pos_right (lt_add_of_pos_right Mf' one_pos)
                  (by positivity)
              _ = ε / 2 := by
                field_simp [hMf'1.ne']
          exact lt_of_le_of_lt hle hlt
        nlinarith
  -- `∫ sᵢrᵢ dμ → ∫ fg dμ`
  have hlim1 : Tendsto (fun n => μ.integral (fun x => s n x * r n x)) atTop
      (𝓝 (μ.integral (f * g))) := by
    exact tendsto_integral_of_tendstoUniformly μ hfg (s := fun n => s n * r n)
      (by simpa only [SimpleFunc.mul_apply] using hdiag)
  -- `∫ sᵢ dμ → ∫ f dμ` and `∫ rᵢ dμ → ∫ g dμ`, so the products converge too
  have hlimS : Tendsto (fun n => μ.integral (fun x => s n x)) atTop (𝓝 (μ.integral f)) :=
    tendsto_integral_of_tendstoUniformly μ hf (s := s) hs
  have hlimR : Tendsto (fun n => μ.integral (fun x => r n x)) atTop (𝓝 (μ.integral g)) :=
    tendsto_integral_of_tendstoUniformly μ hg (s := r) hr
  have hlim2 : Tendsto (fun n => μ.integral (fun x => s n x) * μ.integral (fun x => r n x))
      atTop (𝓝 (μ.integral f * μ.integral g)) :=
    Tendsto.mul hlimS hlimR
  -- the same sequence converges to both limits, which must therefore agree
  have hlim1' : Tendsto (fun n => μ.integral (fun x => s n x) * μ.integral (fun x => r n x))
      atTop (𝓝 (μ.integral (f * g))) := by
    simpa [integral_simpleFunc_mul] using hlim1
  exact (tendsto_nhds_unique hlim2 hlim1').symm

/--
Multiplicativity of the operator-valued integral.

This is the summary statement of the three-stage argument: indicator functions in
`integral_indicator_mul`, simple functions in `integral_simpleFunc_mul`, and general
bounded measurable functions in `integral_bddMeasurable_mul`, which is the stage that
carries the whole statement and so discharges this node.

Blueprint reference: `prpstn:integral-multiplicative`.
-/
theorem integral_mul (μ : ProjectionValuedMeasure X H) {f g : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hg : g ∈ BddMeasurable X) :
    μ.integral (f * g) = μ.integral f * μ.integral g :=
  integral_bddMeasurable_mul μ hf hg

/--
The integral of the complex conjugate of `f` is the adjoint of the integral of `f`.

Blueprint reference: `prpstn:integral-conjugation` (first part).
-/
theorem integral_conj (μ : ProjectionValuedMeasure X H) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) :
    μ.integral (fun x => (starRingEnd ℂ) (f x)) = adjoint (μ.integral f) := by
  classical
  have hfconj : (fun x => (starRingEnd ℂ) (f x)) ∈ BddMeasurable X := by
    rw [mem_bddMeasurable]
    rcases hf with ⟨hfmeas, C, hC⟩
    refine ⟨?_, ⟨C, ?_⟩⟩
    · simpa [Function.comp_def] using (Complex.continuous_conj.measurable.comp hfmeas)
    · intro x
      simpa using hC x
  let Q : H → ℂ := fun ψ => ∫ x, (starRingEnd ℂ) (f x) ∂(μ.assoc ψ)
  have hQ : IsBoundedQuadraticForm Q := isBoundedQuadraticForm_integral_bddMeasurable μ hfconj
  have hL : ∀ ψ : H, Q ψ = ⟪ψ, μ.integral (fun x => (starRingEnd ℂ) (f x)) ψ⟫_ℂ := by
    intro ψ
    simpa [Q] using (inner_integral μ hfconj ψ).symm
  have hR : ∀ ψ : H, Q ψ = ⟪ψ, adjoint (μ.integral f) ψ⟫_ℂ := by
    intro ψ
    calc
      Q ψ = (∫ x, (starRingEnd ℂ) (f x) ∂(μ.assoc ψ)) := rfl
      _ = (starRingEnd ℂ) (∫ x, f x ∂(μ.assoc ψ)) := by
        simpa using (_root_.integral_conj (μ := μ.assoc ψ) (f := f))
      _ = (starRingEnd ℂ) (⟪ψ, μ.integral f ψ⟫_ℂ) := by rw [inner_integral μ hf ψ]
      _ = ⟪ψ, adjoint (μ.integral f) ψ⟫_ℂ := by
        calc
          (starRingEnd ℂ) (⟪ψ, μ.integral f ψ⟫_ℂ) = ⟪μ.integral f ψ, ψ⟫_ℂ :=
            inner_conj_symm (μ.integral f ψ) ψ
          _ = ⟪ψ, adjoint (μ.integral f) ψ⟫_ℂ := by
            rw [adjoint_inner_right (μ.integral f) ψ ψ]
  calc
    μ.integral (fun x => (starRingEnd ℂ) (f x)) = hQ.toOperator :=
      IsBoundedQuadraticForm.eq_toOperator hQ hL
    _ = adjoint (μ.integral f) := (IsBoundedQuadraticForm.eq_toOperator hQ hR).symm

/--
The integral of a real-valued function is self-adjoint.

Blueprint reference: `prpstn:integral-conjugation` (second part).
-/
theorem isSelfAdjoint_integral_of_real (μ : ProjectionValuedMeasure X H) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hreal : ∀ x, (f x).im = 0) :
    IsSelfAdjoint (μ.integral f) := by
  classical
  exact isSelfAdjoint_of_inner_self_real (A := μ.integral f) (fun ψ => by
    rw [inner_integral μ hf ψ]
    apply Complex.conj_eq_iff_im.mp
    calc
      (starRingEnd ℂ) (∫ x, f x ∂(μ.assoc ψ))
          = ∫ x, (starRingEnd ℂ) (f x) ∂(μ.assoc ψ) := by
            simpa using (_root_.integral_conj (μ := μ.assoc ψ) (f := f)).symm
      _ = ∫ x, f x ∂(μ.assoc ψ) := by
        refine integral_congr_ae (ae_of_all (μ.assoc ψ) ?_)
        intro x
        exact (Complex.conj_eq_iff_im.mpr (hreal x)))

end ProjectionValuedMeasure

/--
Uniform convergence is preserved by products of uniformly bounded sequences: if
`sᵢ → f` and `rⱼ → g` uniformly with each `rⱼ` bounded, then `sᵢ rⱼ → f g`
uniformly as `i, j → ∞`.

The blueprint's boundedness assumption on `g` is not stated: it follows from `hr`
together with `hrb`.

Blueprint reference: `prpstn:products-converge-uniformly`.
-/
theorem tendstoUniformly_mul_of_bounded {Y : Type*} {f g : Y → ℂ}
    (hf : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) {s r : ℕ → Y → ℂ}
    (hs : TendstoUniformly s f atTop) (hr : TendstoUniformly r g atTop)
    (hrb : ∀ j, ∃ C : ℝ, ∀ x, ‖r j x‖ ≤ C) :
    TendstoUniformly (fun p : ℕ × ℕ => fun x => s p.1 x * r p.2 x) (f * g)
      (atTop ×ˢ atTop) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  -- A positive uniform bound on `‖f‖`.
  rcases hf with ⟨C_f, hCf⟩
  let M_f : ℝ := max C_f 0 + 1
  have hMf_pos : 0 < M_f := by
    dsimp [M_f]
    linarith [le_max_right C_f 0]
  have hMf : ∀ x, ‖f x‖ ≤ M_f := by
    intro x
    dsimp [M_f]
    calc
      ‖f x‖ ≤ C_f := hCf x
      _ ≤ max C_f 0 := le_max_left C_f 0
      _ ≤ max C_f 0 + 1 := by linarith
  -- A positive uniform bound on `‖g‖`, obtained from `hr` and `hrb`.
  have hg_bounded : ∃ C_g : ℝ, 0 < C_g ∧ ∀ x, ‖g x‖ ≤ C_g := by
    rcases (Metric.tendstoUniformly_iff.mp hr 1 zero_lt_one).exists with ⟨j₀, hj₀⟩
    rcases hrb j₀ with ⟨C, hC⟩
    refine ⟨max (1 + C) 0 + 1, ?_, ?_⟩
    · linarith [le_max_right (1 + C) 0]
    · intro x
      have hdist : ‖g x - r j₀ x‖ < 1 := by
        simpa [dist_eq_norm] using hj₀ x
      calc
        ‖g x‖ ≤ ‖g x - r j₀ x‖ + ‖r j₀ x‖ := by
          calc
            ‖g x‖ = ‖(g x - r j₀ x) + r j₀ x‖ := by rw [sub_add_cancel]
            _ ≤ ‖g x - r j₀ x‖ + ‖r j₀ x‖ := norm_add_le _ _
        _ ≤ 1 + C := by
          exact le_of_lt (add_lt_add_of_lt_of_le hdist (hC x))
        _ ≤ max (1 + C) 0 + 1 := by linarith [le_max_left (1 + C) 0]
  rcases hg_bounded with ⟨C_g, hCg_pos, hCg⟩
  -- A uniform bound on `r j` that holds for all `j` eventually.
  let M_r : ℝ := C_g + 1
  have hMr_pos : 0 < M_r := by
    dsimp [M_r]
    linarith
  have hr_bound : ∀ᶠ j in atTop, ∀ x, ‖r j x‖ ≤ M_r := by
    filter_upwards [Metric.tendstoUniformly_iff.mp hr 1 zero_lt_one] with j hj
    intro x
    have hdist : ‖r j x - g x‖ < 1 := by
      simpa [dist_eq_norm, norm_sub_rev] using hj x
    have hle : ‖r j x‖ ≤ ‖r j x - g x‖ + ‖g x‖ := by
      calc
        ‖r j x‖ = ‖(r j x - g x) + g x‖ := by rw [sub_add_cancel]
        _ ≤ ‖r j x - g x‖ + ‖g x‖ := norm_add_le _ _
    calc
      ‖r j x‖ ≤ ‖r j x - g x‖ + ‖g x‖ := hle
      _ ≤ 1 + C_g := by
        exact le_of_lt (add_lt_add_of_lt_of_le hdist (hCg x))
      _ = M_r := by
        dsimp [M_r]
        ring
  -- The two convergence rates.
  have hε1_pos : 0 < ε / (2 * M_r) := by positivity
  have hε2_pos : 0 < ε / (2 * M_f) := by positivity
  have hs' : ∀ᶠ i in atTop, ∀ x, ‖f x - s i x‖ < ε / (2 * M_r) := by
    simpa [dist_eq_norm] using (Metric.tendstoUniformly_iff.mp hs) (ε / (2 * M_r)) hε1_pos
  have hr' : ∀ᶠ j in atTop, ∀ x, ‖g x - r j x‖ < ε / (2 * M_f) := by
    simpa [dist_eq_norm] using (Metric.tendstoUniformly_iff.mp hr) (ε / (2 * M_f)) hε2_pos
  -- Combine the eventualities on the product filter.
  rw [Filter.eventually_prod_iff]
  refine ⟨fun i : ℕ => ∀ x, ‖f x - s i x‖ < ε / (2 * M_r), hs', ?_⟩
  refine ⟨fun j : ℕ => (∀ x, ‖g x - r j x‖ < ε / (2 * M_f)) ∧ ∀ x, ‖r j x‖ ≤ M_r, ?_, ?_⟩
  · exact hr'.and hr_bound
  · intro i hi j hj x
    have h1 : ‖f x - s i x‖ < ε / (2 * M_r) := hi x
    have h2 : ‖g x - r j x‖ < ε / (2 * M_f) := hj.1 x
    have h3 : ‖r j x‖ ≤ M_r := hj.2 x
    have hMf_ne : M_f ≠ 0 := by linarith
    have hMr_ne : M_r ≠ 0 := by linarith
    have hterm1 : ‖f x‖ * ‖g x - r j x‖ < ε / 2 := by
      calc
        ‖f x‖ * ‖g x - r j x‖ ≤ M_f * ‖g x - r j x‖ :=
          mul_le_mul_of_nonneg_right (hMf x) (norm_nonneg _)
        _ < M_f * (ε / (2 * M_f)) := mul_lt_mul_of_pos_left h2 hMf_pos
        _ = ε / 2 := by
          field_simp [hMf_ne]
    have hterm2 : ‖f x - s i x‖ * ‖r j x‖ < ε / 2 := by
      calc
        ‖f x - s i x‖ * ‖r j x‖ ≤ ‖f x - s i x‖ * M_r :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ < (ε / (2 * M_r)) * M_r := mul_lt_mul_of_pos_right h1 hMr_pos
        _ = ε / 2 := by
          field_simp [hMr_ne]
    have hnorm : ‖(f * g) x - s i x * r j x‖ ≤
        ‖f x‖ * ‖g x - r j x‖ + ‖f x - s i x‖ * ‖r j x‖ := by
      calc
        ‖(f * g) x - s i x * r j x‖ = ‖f x * g x - s i x * r j x‖ := by rfl
        _ = ‖f x * (g x - r j x) + (f x - s i x) * r j x‖ := by
          congr 1
          ring
        _ ≤ ‖f x * (g x - r j x)‖ + ‖(f x - s i x) * r j x‖ := norm_add_le _ _
        _ ≤ ‖f x‖ * ‖g x - r j x‖ + ‖f x - s i x‖ * ‖r j x‖ := by
          exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    have hsum : ‖f x‖ * ‖g x - r j x‖ + ‖f x - s i x‖ * ‖r j x‖ < ε := by
      linarith
    simpa [dist_eq_norm] using lt_of_le_of_lt hnorm hsum

end Spectral
end Physicslib4
