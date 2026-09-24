/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.BorelClasses
import Physicslib4.Spectral.ContinuousCalculus
import Physicslib4.Spectral.Forms

/-!
# The bounded Borel functional calculus

For a self-adjoint `A ∈ 𝓑(H)` and a bounded Borel function `f` on `σ(A)`, the map
`Q_f : ψ ↦ ∫ f dμ_ψ` is a bounded quadratic form, hence of the form
`ψ ↦ ⟪ψ, f(A) ψ⟫` for a unique `f(A) ∈ 𝓑(H)`. This is the blueprint's second
functional calculus, `def:hall-8.8`, and it is multiplicative.

## Main definitions

* `Physicslib4.Spectral.borelForm` — the blueprint's `Q_f`.
* `Physicslib4.Spectral.FClass` — the blueprint's `𝓕`.
* `Physicslib4.Spectral.borelCalculus` — the blueprint's `f ↦ f(A)`.
* `Physicslib4.Spectral.F1Class`, `Physicslib4.Spectral.F2Class` — the blueprint's
  `𝓕₁` and `𝓕₂`.

## Main statements

* `Physicslib4.Spectral.isBoundedQuadraticForm_borelForm` — `Q_f` is a bounded
  quadratic form.
* `Physicslib4.Spectral.existsUnique_borelCalculus` — the operator `f(A)`.
* `Physicslib4.Spectral.borelCalculus_add`, `Physicslib4.Spectral.borelCalculus_smul`
  — linearity of `f ↦ f(A)`.
* `Physicslib4.Spectral.borelCalculus_mul` — multiplicativity of the calculus.
* `Physicslib4.Spectral.isBorelGenerating_F1Class`,
  `Physicslib4.Spectral.isBorelGenerating_F2Class` — `𝓕₁` and `𝓕₂` satisfy the
  hypotheses of the monotone-class bootstrap of
  `Physicslib4/Spectral/BorelClasses.lean`, from which `𝓕₁ = 𝓕₂ = {bounded Borel}`
  follows.

## Implementation notes

"Bounded Borel function on `σ(A)`" is spelled `f ∈ BddMeasurable (spectrum ℝ A)`
throughout, using the submodule defined in `Physicslib4/Spectral/Basic.lean`, rather
than a `Measurable f`/bounded hypothesis pair.
-/

namespace Physicslib4
namespace Spectral

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H}

/-!
### The quadratic forms `Q_f`
-/

/--
The blueprint's `Q_f`: for a bounded Borel function `f` on `σ(A)` and `ψ ∈ H`,
`Q_f(ψ) = ∫_{σ(A)} f dμ_ψ`.

Blueprint reference: `def:hall-8.6`.
-/
noncomputable def borelForm (hA : IsSelfAdjoint A) (f : spectrum ℝ A → ℂ) (ψ : H) : ℂ :=
  ∫ l, f l ∂(assocMeasure hA ψ)

/--
The blueprint's class `𝓕`: the bounded Borel functions `f` on `σ(A)` for which `Q_f`
is a bounded quadratic form.

Blueprint reference: `def:F-class`.
-/
def FClass (hA : IsSelfAdjoint A) : Set (spectrum ℝ A → ℂ) :=
  {f | f ∈ BddMeasurable (spectrum ℝ A) ∧ IsBoundedQuadraticForm (borelForm hA f)}

/--
`f ↦ Q_f` is additive in `f`.

Blueprint reference: `prpstn:Q-is-linear` (additivity).
-/
theorem borelForm_add (hA : IsSelfAdjoint A) {f g : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) (hg : g ∈ BddMeasurable (spectrum ℝ A)) (ψ : H) :
    borelForm hA (f + g) ψ = borelForm hA f ψ + borelForm hA g ψ := by
  have hint (h : spectrum ℝ A → ℂ) (hh : h ∈ BddMeasurable (spectrum ℝ A)) :
      MeasureTheory.Integrable h (assocMeasure hA ψ) := by
    rcases hh with ⟨hmeas, C, hC⟩
    exact MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable C
      (Eventually.of_forall hC)
  simpa [borelForm, Pi.add_apply] using
    (MeasureTheory.integral_add (hint f hf) (hint g hg))

/--
`f ↦ Q_f` is homogeneous in `f`.

Blueprint reference: `prpstn:Q-is-linear` (homogeneity).
-/
theorem borelForm_smul (hA : IsSelfAdjoint A) (α : ℂ) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) (ψ : H) :
    borelForm hA (α • f) ψ = α * borelForm hA f ψ := by
  have hint (h : spectrum ℝ A → ℂ) (hh : h ∈ BddMeasurable (spectrum ℝ A)) :
      MeasureTheory.Integrable h (assocMeasure hA ψ) := by
    rcases hh with ⟨hmeas, C, hC⟩
    exact MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable C
      (Eventually.of_forall hC)
  simpa [borelForm, Pi.smul_apply, smul_eq_mul] using
    (MeasureTheory.Integrable.integral_smul α (hint f hf))

/--
The quadratic form of a linear combination of members of `𝓕` is `|λ|²`-homogeneous.

Blueprint reference: `prpstn:F-homogeneous`.
-/
theorem borelForm_smul_of_mem_FClass (hA : IsSelfAdjoint A) {f g : spectrum ℝ A → ℂ}
    (hf : f ∈ FClass hA) (hg : g ∈ FClass hA) (α β : ℂ) (l : ℂ) (ψ : H) :
    borelForm hA (α • f + β • g) (l • ψ) =
      (‖l‖ : ℂ) ^ 2 * borelForm hA (α • f + β • g) ψ := by
  have hαf : α • f ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).smul_mem α hf.1
  have hβg : β • g ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).smul_mem β hg.1
  calc
    borelForm hA (α • f + β • g) (l • ψ)
        = borelForm hA (α • f) (l • ψ) + borelForm hA (β • g) (l • ψ) := by
            rw [borelForm_add hA hαf hβg (l • ψ)]
    _ = α * borelForm hA f (l • ψ) + β * borelForm hA g (l • ψ) := by
            rw [borelForm_smul hA α hf.1 (l • ψ), borelForm_smul hA β hg.1 (l • ψ)]
    _ = α * ((‖l‖ : ℂ) ^ 2 * borelForm hA f ψ) +
        β * ((‖l‖ : ℂ) ^ 2 * borelForm hA g ψ) := by
            rw [hf.2.isQuadratic.smul l ψ, hg.2.isQuadratic.smul l ψ]
    _ = (‖l‖ : ℂ) ^ 2 * (α * borelForm hA f ψ + β * borelForm hA g ψ) := by
            ring
    _ = (‖l‖ : ℂ) ^ 2 * borelForm hA (α • f + β • g) ψ := by
            rw [borelForm_add hA hαf hβg ψ, borelForm_smul hA α hf.1 ψ,
              borelForm_smul hA β hg.1 ψ]

/--
The polarization of the quadratic form of a linear combination of members of `𝓕` is
sesquilinear.

Blueprint reference: `prpstn:F-sesquilinear`.
-/
theorem isSesquilinearForm_polarization_borelForm (hA : IsSelfAdjoint A)
    {f g : spectrum ℝ A → ℂ} (hf : f ∈ FClass hA) (hg : g ∈ FClass hA) (α β : ℂ) :
    ∃ L : SesquilinearForm H, ∀ φ ψ : H,
      L φ ψ = polarization (borelForm hA (α • f + β • g)) φ ψ := by
  let Lf : SesquilinearForm H := hf.2.isQuadratic.isSesquilinear.choose
  let Lg : SesquilinearForm H := hg.2.isQuadratic.isSesquilinear.choose
  have hLf : ∀ φ ψ : H, Lf φ ψ = polarization (borelForm hA f) φ ψ :=
    fun φ ψ => hf.2.isQuadratic.isSesquilinear.choose_spec φ ψ
  have hLg : ∀ φ ψ : H, Lg φ ψ = polarization (borelForm hA g) φ ψ :=
    fun φ ψ => hg.2.isQuadratic.isSesquilinear.choose_spec φ ψ
  have hαf : α • f ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).smul_mem α hf.1
  have hβg : β • g ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).smul_mem β hg.1
  have hadd : ∀ ψ : H, borelForm hA (α • f + β • g) ψ =
      α * borelForm hA f ψ + β * borelForm hA g ψ := by
    intro ψ
    rw [borelForm_add hA hαf hβg ψ]
    rw [borelForm_smul hA α hf.1 ψ]
    rw [borelForm_smul hA β hg.1 ψ]
  have hpol : ∀ φ ψ : H,
      polarization (borelForm hA (α • f + β • g)) φ ψ =
        α * polarization (borelForm hA f) φ ψ + β * polarization (borelForm hA g) φ ψ := by
    intro φ ψ
    simp only [polarization, hadd]
    ring
  refine ⟨α • Lf + β • Lg, ?_⟩
  intro φ ψ
  calc
    (α • Lf + β • Lg) φ ψ = α * Lf φ ψ + β * Lg φ ψ := by
      simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    _ = α * polarization (borelForm hA f) φ ψ +
        β * polarization (borelForm hA g) φ ψ := by
      rw [hLf φ ψ, hLg φ ψ]
    _ = polarization (borelForm hA (α • f + β • g)) φ ψ := by
      rw [hpol φ ψ]

/--
The quadratic form of a linear combination of members of `𝓕` is bounded.

Blueprint reference: `prpstn:F-bounded` (the closure property).
-/
theorem bounded_borelForm_of_mem_FClass (hA : IsSelfAdjoint A) {f g : spectrum ℝ A → ℂ}
    (hf : f ∈ FClass hA) (hg : g ∈ FClass hA) (α β : ℂ) :
    ∃ C : ℝ, ∀ φ : H, ‖borelForm hA (α • f + β • g) φ‖ ≤ C * ‖φ‖ ^ 2 := by
  rcases hf.2.bounded with ⟨Cf, hCf⟩
  rcases hg.2.bounded with ⟨Cg, hCg⟩
  have hαf : α • f ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).smul_mem α hf.1
  have hβg : β • g ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).smul_mem β hg.1
  refine ⟨‖α‖ * |Cf| + ‖β‖ * |Cg|, ?_⟩
  intro φ
  have hCf' : ‖borelForm hA f φ‖ ≤ |Cf| * ‖φ‖ ^ 2 :=
    le_trans (hCf φ) (mul_le_mul_of_nonneg_right (le_abs_self Cf) (sq_nonneg ‖φ‖))
  have hCg' : ‖borelForm hA g φ‖ ≤ |Cg| * ‖φ‖ ^ 2 :=
    le_trans (hCg φ) (mul_le_mul_of_nonneg_right (le_abs_self Cg) (sq_nonneg ‖φ‖))
  calc
    ‖borelForm hA (α • f + β • g) φ‖
        = ‖borelForm hA (α • f) φ + borelForm hA (β • g) φ‖ := by
          rw [borelForm_add hA hαf hβg φ]
    _ ≤ ‖borelForm hA (α • f) φ‖ + ‖borelForm hA (β • g) φ‖ :=
          norm_add_le _ _
    _ = ‖α * borelForm hA f φ‖ + ‖β * borelForm hA g φ‖ := by
          rw [borelForm_smul hA α hf.1 φ, borelForm_smul hA β hg.1 φ]
    _ = ‖α‖ * ‖borelForm hA f φ‖ + ‖β‖ * ‖borelForm hA g φ‖ := by
          rw [norm_mul, norm_mul]
    _ ≤ ‖α‖ * (|Cf| * ‖φ‖ ^ 2) + ‖β‖ * (|Cg| * ‖φ‖ ^ 2) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hCf' (norm_nonneg α))
            (mul_le_mul_of_nonneg_left hCg' (norm_nonneg β))
    _ = (‖α‖ * |Cf| + ‖β‖ * |Cg|) * ‖φ‖ ^ 2 := by
          ring

/--
`𝓕` is a complex vector space.

This is the blueprint's "consequently" half of `prpstn:F-bounded`; it assembles
`borelForm_smul_of_mem_FClass`, `isSesquilinearForm_polarization_borelForm` and
`bounded_borelForm_of_mem_FClass`.

Blueprint reference: `prpstn:F-bounded` (the global consequence).
-/
theorem smul_add_mem_FClass (hA : IsSelfAdjoint A) {f g : spectrum ℝ A → ℂ}
    (hf : f ∈ FClass hA) (hg : g ∈ FClass hA) (α β : ℂ) :
    α • f + β • g ∈ FClass hA := by
  have hαf : α • f ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).smul_mem α hf.1
  have hβg : β • g ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).smul_mem β hg.1
  have hmem : α • f + β • g ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).add_mem hαf hβg
  have hbqf : IsBoundedQuadraticForm (borelForm hA (α • f + β • g)) :=
    ⟨⟨borelForm_smul_of_mem_FClass hA hf hg α β,
        isSesquilinearForm_polarization_borelForm hA hf hg α β⟩,
      bounded_borelForm_of_mem_FClass hA hf hg α β⟩
  change α • f + β • g ∈ BddMeasurable (spectrum ℝ A) ∧
    IsBoundedQuadraticForm (borelForm hA (α • f + β • g))
  exact ⟨hmem, hbqf⟩

/--
`𝓕` contains the continuous real-valued functions on `σ(A)`.

Blueprint reference: `prpstn:F-contains-continuous`.
-/
theorem continuous_mem_FClass (hA : IsSelfAdjoint A) (f : C(spectrum ℝ A, ℝ)) :
    (fun l => ((f l : ℝ) : ℂ)) ∈ FClass hA := by
  rw [FClass, Set.mem_setOf_eq]
  constructor
  · rw [mem_bddMeasurable]
    constructor
    · exact (Complex.continuous_ofReal.comp f.continuous).measurable
    · obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
        (f := fun l : spectrum ℝ A => ((f l : ℝ) : ℂ))
        (by intro x hx; exact (Complex.continuous_ofReal.comp f.continuous).continuousOn x hx)
      exact ⟨C, fun x => hC x trivial⟩
  · have hform : borelForm hA (fun l => ((f l : ℝ) : ℂ)) =
        fun ψ : H => ⟪ψ, realCalculus hA f ψ⟫_ℂ := by
      funext ψ
      rw [borelForm]
      norm_cast
      exact (integral_assocMeasure hA ψ f).symm
    rw [hform]
    exact isBoundedQuadraticForm_inner (realCalculus hA f)

/--
`𝓕` is closed under pointwise limits of uniformly bounded sequences.

Blueprint reference: `prpstn:F-closed-under-limits`.
-/
theorem mem_FClass_of_tendsto (hA : IsSelfAdjoint A) {f : ℕ → spectrum ℝ A → ℂ}
    {g : spectrum ℝ A → ℂ} {M : ℝ} (hf : ∀ n, f n ∈ FClass hA)
    (hlim : BoundedPointwiseLimit f g (fun _ => M)) : g ∈ FClass hA := by
  refine ⟨?_, ?_⟩
  · refine ⟨measurable_of_tendsto_pointwise (fun n => (hf n).1.1) hlim.tendsto,
      ⟨M, fun x => norm_le_of_tendsto hlim x⟩⟩
  · refine isBoundedQuadraticForm_of_tendsto (C := M)
      (Q := fun n => borelForm hA (f n)) (Q₀ := borelForm hA g)
      (hQ := fun n => (hf n).2.isQuadratic) ?_
    refine { norm_le := ?_, tendsto := ?_ }
    · intro n φ
      unfold borelForm
      calc
        ‖∫ l, f n l ∂(assocMeasure hA φ)‖ ≤ M * (assocMeasure hA φ).real Set.univ := by
          exact MeasureTheory.norm_integral_le_of_norm_le_const (μ := assocMeasure hA φ)
            (C := M) (by
              filter_upwards with x
              exact hlim.norm_le n x)
        _ = M * ‖φ‖ ^ 2 := by
          congr 1
          rw [Measure.real, assocMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg ‖φ‖)]
    · intro φ
      unfold borelForm
      exact tendsto_integral_of_boundedPointwiseLimit (μ := assocMeasure hA φ)
        (hmeas := fun n => (hf n).1.1) hlim

/--
For every bounded Borel function `f` on `σ(A)`, the map `Q_f` is a bounded quadratic
form on `H`.

Blueprint reference: `prpstn:hall-8.7`.
-/
theorem isBoundedQuadraticForm_borelForm (hA : IsSelfAdjoint A) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) :
    IsBoundedQuadraticForm (borelForm hA f) := by
  have hgen : IsBorelGenerating (FClass hA) :=
    { bddMeasurable := fun g hg => hg.1
      smul_add_mem := fun α β g k hg hk => smul_add_mem_FClass hA hg hk α β
      continuous_mem := fun g => continuous_mem_FClass hA g
      tendsto_mem := fun g h M hg hlim => mem_FClass_of_tendsto hA hg hlim }
  have hF : FClass hA = (BddMeasurable (spectrum ℝ A) : Set (spectrum ℝ A → ℂ)) :=
    hgen.eq_bddMeasurable
  have hfF : f ∈ FClass hA := by
    rw [hF]
    exact hf
  exact hfF.2

/-!
### The operators `f(A)`
-/

/--
**The bounded Borel functional calculus.** For a bounded Borel function `f` on
`σ(A)` there is a unique `f(A) ∈ 𝓑(H)` with `⟪ψ, f(A) ψ⟫ = Q_f(ψ)` for all `ψ`.

Blueprint reference: `def:hall-8.8`.
-/
theorem existsUnique_borelCalculus (hA : IsSelfAdjoint A) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) :
    ∃! B : H →L[ℂ] H, ∀ ψ : H, ⟪ψ, B ψ⟫_ℂ = borelForm hA f ψ := by
  have hQ : IsBoundedQuadraticForm (borelForm hA f) := isBoundedQuadraticForm_borelForm hA hf
  refine ⟨hQ.toOperator, ?_, ?_⟩
  · intro ψ
    exact (hQ.inner_toOperator ψ).symm
  · intro B hB
    exact hQ.eq_toOperator (fun ψ => (hB ψ).symm)

open Classical in
/--
The operator `f(A)` associated with a bounded Borel function `f` on `σ(A)`, extended
by `0` to functions that are not bounded and measurable.
-/
noncomputable def borelCalculus (hA : IsSelfAdjoint A) (f : spectrum ℝ A → ℂ) : H →L[ℂ] H :=
  if h : f ∈ BddMeasurable (spectrum ℝ A) then (existsUnique_borelCalculus hA h).choose else 0

theorem inner_borelCalculus (hA : IsSelfAdjoint A) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) (ψ : H) :
    ⟪ψ, borelCalculus hA f ψ⟫_ℂ = borelForm hA f ψ := by
  classical
  simp only [borelCalculus, dif_pos hf]
  exact (existsUnique_borelCalculus hA hf).choose_spec.1 ψ

theorem borelCalculus_of_notMem (hA : IsSelfAdjoint A) {f : spectrum ℝ A → ℂ}
    (hf : f ∉ BddMeasurable (spectrum ℝ A)) : borelCalculus hA f = 0 := by
  classical
  simp only [borelCalculus, dif_neg hf]

/-!
### Linearity of the calculus

`borelCalculus` is defined through `Exists.choose`, so its linearity in `f` is not
definitional. The two computation rules below are what the vector-space fields of
`isBorelGenerating_F1Class` and `isBorelGenerating_F2Class` consume; together they
say that `f ↦ f(A)` restricts to a `ℂ`-linear map on `BddMeasurable (spectrum ℝ A)`.
-/

/--
Additivity of the bounded Borel functional calculus.

Blueprint reference: `def:hall-8.8` (linearity of `f ↦ f(A)`).
-/
theorem borelCalculus_add (hA : IsSelfAdjoint A) {f g : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) (hg : g ∈ BddMeasurable (spectrum ℝ A)) :
    borelCalculus hA (f + g) = borelCalculus hA f + borelCalculus hA g := by
  have hfg : f + g ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).add_mem hf hg
  let hQ : IsBoundedQuadraticForm (borelForm hA (f + g)) :=
    isBoundedQuadraticForm_borelForm hA hfg
  have hC : ∀ ψ : H, borelForm hA (f + g) ψ =
      ⟪ψ, (borelCalculus hA f + borelCalculus hA g) ψ⟫_ℂ := by
    intro ψ
    calc
      borelForm hA (f + g) ψ = borelForm hA f ψ + borelForm hA g ψ := by
        rw [borelForm_add hA hf hg ψ]
      _ = ⟪ψ, borelCalculus hA f ψ⟫_ℂ + ⟪ψ, borelCalculus hA g ψ⟫_ℂ := by
        rw [← inner_borelCalculus hA hf ψ, ← inner_borelCalculus hA hg ψ]
      _ = ⟪ψ, (borelCalculus hA f + borelCalculus hA g) ψ⟫_ℂ := by
        simp [inner_add_right]
  calc
    borelCalculus hA (f + g) = hQ.toOperator :=
      hQ.eq_toOperator (fun ψ => (inner_borelCalculus hA hfg ψ).symm)
    _ = borelCalculus hA f + borelCalculus hA g := (hQ.eq_toOperator hC).symm

/--
Homogeneity of the bounded Borel functional calculus.

Blueprint reference: `def:hall-8.8` (linearity of `f ↦ f(A)`).
-/
theorem borelCalculus_smul (hA : IsSelfAdjoint A) (α : ℂ) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) :
    borelCalculus hA (α • f) = α • borelCalculus hA f := by
  have hαf : α • f ∈ BddMeasurable (spectrum ℝ A) :=
    (BddMeasurable (spectrum ℝ A)).smul_mem α hf
  let hQ : IsBoundedQuadraticForm (borelForm hA (α • f)) :=
    isBoundedQuadraticForm_borelForm hA hαf
  have hC : ∀ ψ : H, borelForm hA (α • f) ψ =
      ⟪ψ, (α • borelCalculus hA f) ψ⟫_ℂ := by
    intro ψ
    calc
      borelForm hA (α • f) ψ = α * borelForm hA f ψ := by
        rw [borelForm_smul hA α hf ψ]
      _ = α * ⟪ψ, borelCalculus hA f ψ⟫_ℂ := by
        rw [← inner_borelCalculus hA hf ψ]
      _ = ⟪ψ, (α • borelCalculus hA f) ψ⟫_ℂ := by
        simp [inner_smul_right]
  calc
    borelCalculus hA (α • f) = hQ.toOperator :=
      hQ.eq_toOperator (fun ψ => (inner_borelCalculus hA hαf ψ).symm)
    _ = α • borelCalculus hA f := (hQ.eq_toOperator hC).symm

/--
If `f` is real-valued then `f(A)` is self-adjoint.

Blueprint reference: `lmm:lemma-3`.
-/
theorem isSelfAdjoint_borelCalculus (hA : IsSelfAdjoint A) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) (hreal : ∀ l, (f l).im = 0) :
    IsSelfAdjoint (borelCalculus hA f) := by
  apply isSelfAdjoint_of_inner_self_real
  intro ψ
  rw [inner_borelCalculus hA hf]
  rw [borelForm]
  have hf_int : MeasureTheory.Integrable f (assocMeasure hA ψ) := by
    rcases hf with ⟨hmeas, C, hC⟩
    exact MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable C
      (Eventually.of_forall hC)
  change Complex.imCLM (∫ l, f l ∂(assocMeasure hA ψ)) = 0
  rw [← ContinuousLinearMap.integral_comp_comm Complex.imCLM hf_int]
  simp [hreal]


/-!
### The classes `𝓕₁` and `𝓕₂`
-/

/--
The blueprint's class `𝓕₁`: the bounded Borel functions `f` on `σ(A)` for which
`(fg)(A) = f(A) g(A)` for every *continuous* real `g`.

Blueprint reference: `def:F1-F2-classes` (first class).
-/
def F1Class (hA : IsSelfAdjoint A) : Set (spectrum ℝ A → ℂ) :=
  {f | f ∈ BddMeasurable (spectrum ℝ A) ∧
    ∀ g : C(spectrum ℝ A, ℝ),
      borelCalculus hA (fun l => f l * ((g l : ℝ) : ℂ)) =
        borelCalculus hA f * borelCalculus hA (fun l => ((g l : ℝ) : ℂ))}

/--
The blueprint's class `𝓕₂`: the bounded Borel functions `g` on `σ(A)` for which
`(fg)(A) = f(A) g(A)` for every *bounded Borel* `f`.

Blueprint reference: `def:F1-F2-classes` (second class).
-/
def F2Class (hA : IsSelfAdjoint A) : Set (spectrum ℝ A → ℂ) :=
  {g | g ∈ BddMeasurable (spectrum ℝ A) ∧
    ∀ f ∈ BddMeasurable (spectrum ℝ A),
      borelCalculus hA (fun l => f l * g l) = borelCalculus hA f * borelCalculus hA g}

/-- `Q_f` is continuous under uniformly bounded pointwise limits of the integrand.
Private auxiliary copy used by `isBorelGenerating_F1Class` before `tendsto_borelForm`
is declared (same statement as the public theorem below). -/
private theorem tendsto_borelForm_F1Aux (hA : IsSelfAdjoint A) {f : ℕ → spectrum ℝ A → ℂ}
    {g : spectrum ℝ A → ℂ} {M : ℝ} (hmeas : ∀ n, Measurable (f n))
    (hlim : BoundedPointwiseLimit f g (fun _ => M)) (ψ : H) :
    Tendsto (fun n => borelForm hA (f n) ψ) atTop (𝓝 (borelForm hA g ψ)) := by
  unfold borelForm
  exact tendsto_integral_of_boundedPointwiseLimit (μ := assocMeasure hA ψ)
    (hmeas := hmeas) hlim

/-- The polarization of `Q_f` is continuous under uniformly bounded pointwise limits of
the integrand. Private auxiliary copy used by `isBorelGenerating_F1Class` before
`tendsto_polarization_borelForm` is declared (same statement as the public theorem below). -/
private theorem tendsto_polarization_borelForm_F1Aux (hA : IsSelfAdjoint A)
    {f : ℕ → spectrum ℝ A → ℂ} {g : spectrum ℝ A → ℂ} {M : ℝ}
    (hmeas : ∀ n, Measurable (f n)) (hlim : BoundedPointwiseLimit f g (fun _ => M))
    (φ ψ : H) :
    Tendsto (fun n => polarization (borelForm hA (f n)) φ ψ) atTop
      (𝓝 (polarization (borelForm hA g) φ ψ)) := by
  have hB : ∀ v : H, Tendsto (fun n => borelForm hA (f n) v) atTop (𝓝 (borelForm hA g v)) :=
    fun v => tendsto_borelForm_F1Aux hA hmeas hlim v
  have hsum1 : Tendsto
      (fun n => (borelForm hA (f n) (φ + ψ) - borelForm hA (f n) φ) - borelForm hA (f n) ψ)
      atTop (𝓝 ((borelForm hA g (φ + ψ) - borelForm hA g φ) - borelForm hA g ψ)) :=
    ((hB (φ + ψ)).sub (hB φ)).sub (hB ψ)
  have hsum2 : Tendsto
      (fun n => (borelForm hA (f n) (φ + Complex.I • ψ) - borelForm hA (f n) φ) -
        borelForm hA (f n) (Complex.I • ψ)) atTop
      (𝓝 ((borelForm hA g (φ + Complex.I • ψ) - borelForm hA g φ) -
        borelForm hA g (Complex.I • ψ))) :=
    ((hB (φ + Complex.I • ψ)).sub (hB φ)).sub (hB (Complex.I • ψ))
  have hterm1 : Tendsto
      (fun n => (1 / 2 : ℂ) *
        ((borelForm hA (f n) (φ + ψ) - borelForm hA (f n) φ) - borelForm hA (f n) ψ)) atTop
      (𝓝 ((1 / 2 : ℂ) *
        ((borelForm hA g (φ + ψ) - borelForm hA g φ) - borelForm hA g ψ))) :=
    tendsto_const_nhds.mul hsum1
  have hterm2 : Tendsto
      (fun n => (Complex.I / 2 : ℂ) *
        ((borelForm hA (f n) (φ + Complex.I • ψ) - borelForm hA (f n) φ) -
          borelForm hA (f n) (Complex.I • ψ))) atTop
      (𝓝 ((Complex.I / 2 : ℂ) *
        ((borelForm hA g (φ + Complex.I • ψ) - borelForm hA g φ) -
          borelForm hA g (Complex.I • ψ)))) :=
    tendsto_const_nhds.mul hsum2
  simpa [polarization] using hterm1.sub hterm2

/--
`𝓕₁` satisfies the blueprint's bootstrap hypotheses: it consists of bounded Borel
functions, is a complex subspace, contains the continuous real-valued functions on
`σ(A)`, and is closed under uniformly bounded pointwise limits.

The first three of these are `prpstn:F1-vector-space`, the last is
`prpstn:F1-closed-under-limits`; they are packaged as `IsBorelGenerating` because
that is exactly what the monotone-class bootstrap of
`Physicslib4/Spectral/BorelClasses.lean` consumes.

Blueprint reference: `prpstn:F1-vector-space`.
-/
theorem isBorelGenerating_F1Class (hA : IsSelfAdjoint A) :
    IsBorelGenerating (F1Class hA) := by
  -- pointwise multiplication preserves `BddMeasurable`
  have hmul_mem : ∀ {u v : spectrum ℝ A → ℂ},
      u ∈ BddMeasurable (spectrum ℝ A) → v ∈ BddMeasurable (spectrum ℝ A) →
      (fun l => u l * v l) ∈ BddMeasurable (spectrum ℝ A) := by
    intro u v hu hv
    rcases hu with ⟨hu_meas, Cu, hCu⟩
    rcases hv with ⟨hv_meas, Cv, hCv⟩
    refine ⟨hu_meas.mul hv_meas, max Cu 0 * max Cv 0, fun l => ?_⟩
    calc
      ‖u l * v l‖ ≤ ‖u l‖ * ‖v l‖ := norm_mul_le (u l) (v l)
      _ ≤ max Cu 0 * max Cv 0 := by
        exact mul_le_mul (le_trans (hCu l) (le_max_left Cu 0))
          (le_trans (hCv l) (le_max_left Cv 0)) (norm_nonneg (v l)) (le_max_right Cu 0)
  -- the polarization of `Q_f` is the inner product with `f(A)` off the diagonal
  have hpol_inner : ∀ (h : spectrum ℝ A → ℂ) (hh : h ∈ BddMeasurable (spectrum ℝ A))
      (φ ψ : H), polarization (borelForm hA h) φ ψ = ⟪φ, borelCalculus hA h ψ⟫_ℂ := by
    intro h hh φ ψ
    let hQ : IsBoundedQuadraticForm (borelForm hA h) := isBoundedQuadraticForm_borelForm hA hh
    have hcalc : borelCalculus hA h = hQ.toOperator := by
      exact hQ.eq_toOperator (fun ζ => (inner_borelCalculus hA hh ζ).symm)
    calc
      polarization (borelForm hA h) φ ψ = hQ.toSesq φ ψ := by simp
      _ = ⟪φ, hQ.toOperator ψ⟫_ℂ := by
        rw [IsBoundedQuadraticForm.toOperator, ContinuousLinearMap.adjoint_inner_right,
          InnerProductSpace.continuousLinearMapOfBilin_apply]
      _ = ⟪φ, borelCalculus hA h ψ⟫_ℂ := by rw [hcalc]
  -- the Borel calculus agrees with the real calculus on continuous functions
  have bridge : ∀ f : C(spectrum ℝ A, ℝ),
      borelCalculus hA (fun l => ((f l : ℝ) : ℂ)) = realCalculus hA f := by
    intro f
    let fc : spectrum ℝ A → ℂ := fun l => ((f l : ℝ) : ℂ)
    have hfc : fc ∈ BddMeasurable (spectrum ℝ A) := by
      simpa [fc] using (continuous_mem_FClass hA f).1
    let hQ : IsBoundedQuadraticForm (borelForm hA fc) := isBoundedQuadraticForm_borelForm hA hfc
    have h1 : borelCalculus hA fc = hQ.toOperator := by
      exact hQ.eq_toOperator (fun ψ => (inner_borelCalculus hA hfc ψ).symm)
    have h2 : realCalculus hA f = hQ.toOperator := by
      refine hQ.eq_toOperator ?_
      intro ψ
      change borelForm hA (fun l => ((f l : ℝ) : ℂ)) ψ = ⟪ψ, realCalculus hA f ψ⟫_ℂ
      rw [borelForm]
      norm_cast
      exact (integral_assocMeasure hA ψ f).symm
    exact h1.trans h2.symm
  refine { bddMeasurable := ?_, smul_add_mem := ?_, continuous_mem := ?_, tendsto_mem := ?_ }
  · intro f hf
    exact hf.1
  · intro α β f g hf hg
    have hαf : α • f ∈ BddMeasurable (spectrum ℝ A) :=
      (BddMeasurable (spectrum ℝ A)).smul_mem α hf.1
    have hβg : β • g ∈ BddMeasurable (spectrum ℝ A) :=
      (BddMeasurable (spectrum ℝ A)).smul_mem β hg.1
    refine ⟨?_, ?_⟩
    · exact (BddMeasurable (spectrum ℝ A)).add_mem hαf hβg
    · intro k
      let kc : spectrum ℝ A → ℂ := fun l => ((k l : ℝ) : ℂ)
      change borelCalculus hA (fun l => (α • f + β • g) l * kc l) =
        borelCalculus hA (α • f + β • g) * borelCalculus hA kc
      have hkc : kc ∈ BddMeasurable (spectrum ℝ A) := by
        simpa [kc] using (continuous_mem_FClass hA k).1
      have hfk : (fun l => f l * kc l) ∈ BddMeasurable (spectrum ℝ A) := hmul_mem hf.1 hkc
      have hgk : (fun l => g l * kc l) ∈ BddMeasurable (spectrum ℝ A) := hmul_mem hg.1 hkc
      have hαfk : α • (fun l => f l * kc l) ∈ BddMeasurable (spectrum ℝ A) :=
        (BddMeasurable (spectrum ℝ A)).smul_mem α hfk
      have hβgk : β • (fun l => g l * kc l) ∈ BddMeasurable (spectrum ℝ A) :=
        (BddMeasurable (spectrum ℝ A)).smul_mem β hgk
      have hdist : (fun l => (α • f + β • g) l * kc l) =
          α • (fun l => f l * kc l) + β • (fun l => g l * kc l) := by
        funext l
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      calc
        borelCalculus hA (fun l => (α • f + β • g) l * kc l)
            = borelCalculus hA (α • (fun l => f l * kc l) + β • (fun l => g l * kc l)) := by
                rw [hdist]
        _ = α • borelCalculus hA (fun l => f l * kc l) +
              β • borelCalculus hA (fun l => g l * kc l) := by
                rw [borelCalculus_add hA hαfk hβgk, borelCalculus_smul hA α hfk,
                  borelCalculus_smul hA β hgk]
        _ = α • (borelCalculus hA f * borelCalculus hA kc) +
              β • (borelCalculus hA g * borelCalculus hA kc) := by
                rw [hf.2 k, hg.2 k]
        _ = (α • borelCalculus hA f + β • borelCalculus hA g) * borelCalculus hA kc := by
                ext x
                simp
        _ = borelCalculus hA (α • f + β • g) * borelCalculus hA kc := by
                rw [borelCalculus_add hA hαf hβg, borelCalculus_smul hA α hf.1,
                  borelCalculus_smul hA β hg.1]
  · intro f
    refine ⟨?_, ?_⟩
    · exact (continuous_mem_FClass hA f).1
    · intro g
      calc
        borelCalculus hA (fun l => ((f l : ℝ) : ℂ) * ((g l : ℝ) : ℂ))
            = borelCalculus hA (fun l => (((f * g : C(spectrum ℝ A, ℝ)) l : ℝ) : ℂ)) := by
                congr 1
                funext l
                norm_cast
        _ = realCalculus hA (f * g) := bridge (f * g)
        _ = realCalculus hA f * realCalculus hA g := realCalculus_mul hA f g
        _ = borelCalculus hA (fun l => ((f l : ℝ) : ℂ)) *
              borelCalculus hA (fun l => ((g l : ℝ) : ℂ)) := by
                rw [← bridge f, ← bridge g]
  · intro f g M hf hlim
    have hg : g ∈ BddMeasurable (spectrum ℝ A) :=
      ⟨measurable_of_tendsto_pointwise (fun n => (hf n).1.1) hlim.tendsto,
        ⟨M, fun x => norm_le_of_tendsto hlim x⟩⟩
    refine ⟨hg, ?_⟩
    intro k
    let kc : spectrum ℝ A → ℂ := fun l => ((k l : ℝ) : ℂ)
    change borelCalculus hA (fun l => g l * kc l) = borelCalculus hA g * borelCalculus hA kc
    have hkc : kc ∈ BddMeasurable (spectrum ℝ A) := by
      simpa [kc] using (continuous_mem_FClass hA k).1
    have hnorm_k : ∀ l : spectrum ℝ A, ‖kc l‖ ≤ ‖k‖ := by
      intro l
      have hmain : ‖k l‖ ≤ ‖k‖ := ContinuousMap.norm_coe_le_norm (f := k) l
      simpa [kc] using hmain
    have hmeas_kc : Measurable kc := by
      dsimp [kc]
      exact (Complex.continuous_ofReal.comp k.continuous).measurable
    have hprod_norm : ∀ n l, ‖f n l * kc l‖ ≤ M * ‖k‖ := by
      intro n l
      calc
        ‖f n l * kc l‖ ≤ ‖f n l‖ * ‖kc l‖ := norm_mul_le (f n l) (kc l)
        _ ≤ M * ‖k‖ := by
          exact mul_le_mul (hlim.norm_le n l) (hnorm_k l) (norm_nonneg (kc l))
            (le_trans (norm_nonneg (f n l)) (hlim.norm_le n l))
    have hprod_tendsto : ∀ l, Tendsto (fun n => f n l * kc l) atTop (𝓝 (g l * kc l)) := by
      intro l
      exact (hlim.tendsto l).mul (tendsto_const_nhds (x := kc l))
    have hprod_lim : BoundedPointwiseLimit (fun n l => f n l * kc l)
        (fun l => g l * kc l) (fun _ => M * ‖k‖) :=
      ⟨hprod_norm, hprod_tendsto⟩
    have hconv1_raw : ∀ ψ : H, Tendsto (fun n => borelForm hA (fun l => f n l * kc l) ψ) atTop
        (𝓝 (borelForm hA (fun l => g l * kc l) ψ)) := fun ψ =>
      tendsto_borelForm_F1Aux hA (fun n => ((hf n).1.1).mul hmeas_kc) hprod_lim ψ
    have hgkc_mem : (fun l => g l * kc l) ∈ BddMeasurable (spectrum ℝ A) := hmul_mem hg hkc
    have hrep : ∀ ψ : H, borelForm hA (fun l => g l * kc l) ψ =
        ⟪ψ, (borelCalculus hA g * borelCalculus hA kc) ψ⟫_ℂ := by
      intro ψ
      let η : H := borelCalculus hA kc ψ
      have hconv1 : Tendsto (fun n => ⟪ψ, (borelCalculus hA (f n) * borelCalculus hA kc) ψ⟫_ℂ)
          atTop (𝓝 (borelForm hA (fun l => g l * kc l) ψ)) := by
        refine (hconv1_raw ψ).congr' (Eventually.of_forall fun n => ?_)
        calc
          borelForm hA (fun l => f n l * kc l) ψ = ⟪ψ, borelCalculus hA (fun l => f n l * kc l) ψ⟫_ℂ :=
            (inner_borelCalculus hA (hmul_mem (hf n).1 hkc) ψ).symm
          _ = ⟪ψ, (borelCalculus hA (f n) * borelCalculus hA kc) ψ⟫_ℂ := by
            dsimp [kc]
            rw [← (hf n).2 k]
      have hpol_g : polarization (borelForm hA g) ψ η =
          ⟪ψ, (borelCalculus hA g * borelCalculus hA kc) ψ⟫_ℂ := by
        calc
          polarization (borelForm hA g) ψ η = ⟪ψ, borelCalculus hA g η⟫_ℂ :=
            hpol_inner g hg ψ η
          _ = ⟪ψ, (borelCalculus hA g * borelCalculus hA kc) ψ⟫_ℂ := by
            simp [η, ContinuousLinearMap.mul_apply]
      have hpol' : Tendsto (fun n => polarization (borelForm hA (f n)) ψ η) atTop
          (𝓝 ⟪ψ, (borelCalculus hA g * borelCalculus hA kc) ψ⟫_ℂ) := by
        simpa [hpol_g] using
          (tendsto_polarization_borelForm_F1Aux hA (fun n => (hf n).1.1) hlim ψ η)
      have hconv2 : Tendsto (fun n => ⟪ψ, (borelCalculus hA (f n) * borelCalculus hA kc) ψ⟫_ℂ)
          atTop (𝓝 ⟪ψ, (borelCalculus hA g * borelCalculus hA kc) ψ⟫_ℂ) := by
        refine (hpol'.congr' (Eventually.of_forall fun n => ?_))
        rw [hpol_inner (f n) (hf n).1 ψ η]
        simp [η, ContinuousLinearMap.mul_apply]
      exact tendsto_nhds_unique hconv1 hconv2
    let hQ : IsBoundedQuadraticForm (borelForm hA (fun l => g l * kc l)) :=
      isBoundedQuadraticForm_borelForm hA hgkc_mem
    have hcalc1 : borelCalculus hA (fun l => g l * kc l) = hQ.toOperator :=
      hQ.eq_toOperator (fun ψ => (inner_borelCalculus hA hgkc_mem ψ).symm)
    have hcalc2 : borelCalculus hA g * borelCalculus hA kc = hQ.toOperator :=
      hQ.eq_toOperator (fun ψ => hrep ψ)
    exact hcalc1.trans hcalc2.symm

/--
`Q_f` is continuous under uniformly bounded pointwise limits of the integrand.

Blueprint reference: `prpstn:Q-continuous-under-limits` (first part).
-/
theorem tendsto_borelForm (hA : IsSelfAdjoint A) {f : ℕ → spectrum ℝ A → ℂ}
    {g : spectrum ℝ A → ℂ} {M : ℝ} (hmeas : ∀ n, Measurable (f n))
    (hlim : BoundedPointwiseLimit f g (fun _ => M)) (ψ : H) :
    Tendsto (fun n => borelForm hA (f n) ψ) atTop (𝓝 (borelForm hA g ψ)) := by
  unfold borelForm
  exact tendsto_integral_of_boundedPointwiseLimit (μ := assocMeasure hA ψ)
    (hmeas := hmeas) hlim

/--
The polarization of `Q_f` is continuous under uniformly bounded pointwise limits of
the integrand.

Blueprint reference: `prpstn:Q-continuous-under-limits` (second part).
-/
theorem tendsto_polarization_borelForm (hA : IsSelfAdjoint A) {f : ℕ → spectrum ℝ A → ℂ}
    {g : spectrum ℝ A → ℂ} {M : ℝ} (hmeas : ∀ n, Measurable (f n))
    (hlim : BoundedPointwiseLimit f g (fun _ => M)) (φ ψ : H) :
    Tendsto (fun n => polarization (borelForm hA (f n)) φ ψ) atTop
      (𝓝 (polarization (borelForm hA g) φ ψ)) := by
  have hB : ∀ v : H, Tendsto (fun n => borelForm hA (f n) v) atTop (𝓝 (borelForm hA g v)) :=
    fun v => tendsto_borelForm hA hmeas hlim v
  have hsum1 : Tendsto
      (fun n => (borelForm hA (f n) (φ + ψ) - borelForm hA (f n) φ) - borelForm hA (f n) ψ)
      atTop (𝓝 ((borelForm hA g (φ + ψ) - borelForm hA g φ) - borelForm hA g ψ)) :=
    ((hB (φ + ψ)).sub (hB φ)).sub (hB ψ)
  have hsum2 : Tendsto
      (fun n => (borelForm hA (f n) (φ + Complex.I • ψ) - borelForm hA (f n) φ) -
        borelForm hA (f n) (Complex.I • ψ)) atTop
      (𝓝 ((borelForm hA g (φ + Complex.I • ψ) - borelForm hA g φ) -
        borelForm hA g (Complex.I • ψ))) :=
    ((hB (φ + Complex.I • ψ)).sub (hB φ)).sub (hB (Complex.I • ψ))
  have hterm1 : Tendsto
      (fun n => (1 / 2 : ℂ) *
        ((borelForm hA (f n) (φ + ψ) - borelForm hA (f n) φ) - borelForm hA (f n) ψ)) atTop
      (𝓝 ((1 / 2 : ℂ) *
        ((borelForm hA g (φ + ψ) - borelForm hA g φ) - borelForm hA g ψ))) :=
    tendsto_const_nhds.mul hsum1
  have hterm2 : Tendsto
      (fun n => (Complex.I / 2 : ℂ) *
        ((borelForm hA (f n) (φ + Complex.I • ψ) - borelForm hA (f n) φ) -
          borelForm hA (f n) (Complex.I • ψ))) atTop
      (𝓝 ((Complex.I / 2 : ℂ) *
        ((borelForm hA g (φ + Complex.I • ψ) - borelForm hA g φ) -
          borelForm hA g (Complex.I • ψ)))) :=
    tendsto_const_nhds.mul hsum2
  simpa [polarization] using hterm1.sub hterm2

/--
`𝓕₁` is closed under uniformly bounded pointwise limits.

Blueprint reference: `prpstn:F1-closed-under-limits` (the closure property).
-/
theorem mem_F1Class_of_tendsto (hA : IsSelfAdjoint A) {f : ℕ → spectrum ℝ A → ℂ}
    {g : spectrum ℝ A → ℂ} {M : ℝ} (hf : ∀ n, f n ∈ F1Class hA)
    (hlim : BoundedPointwiseLimit f g (fun _ => M)) :
    g ∈ F1Class hA :=
  (isBorelGenerating_F1Class hA).tendsto_mem f g M hf hlim

/--
`𝓕₁` is the set of *all* bounded Borel functions on `σ(A)`.

This is the blueprint's "consequently" half of `prpstn:F1-closed-under-limits`; it
has no hypotheses beyond self-adjointness of `A` and follows from the bootstrap
lemma `IsBorelGenerating.eq_bddMeasurable`.

Blueprint reference: `prpstn:F1-closed-under-limits` (the global consequence).
-/
theorem F1Class_eq_bddMeasurable (hA : IsSelfAdjoint A) :
    F1Class hA = (BddMeasurable (spectrum ℝ A) : Set (spectrum ℝ A → ℂ)) :=
  (isBorelGenerating_F1Class hA).eq_bddMeasurable

/--
`𝓕₂` satisfies the blueprint's bootstrap hypotheses: it consists of bounded Borel
functions, is a complex subspace, contains the continuous real-valued functions on
`σ(A)`, and is closed under uniformly bounded pointwise limits.

Blueprint reference: `prpstn:F2-is-everything` (hypotheses (1)–(3)).
-/
theorem isBorelGenerating_F2Class (hA : IsSelfAdjoint A) :
    IsBorelGenerating (F2Class hA) := by
  -- pointwise multiplication preserves `BddMeasurable`
  have hmul_mem : ∀ {u v : spectrum ℝ A → ℂ},
      u ∈ BddMeasurable (spectrum ℝ A) → v ∈ BddMeasurable (spectrum ℝ A) →
      (fun l => u l * v l) ∈ BddMeasurable (spectrum ℝ A) := by
    intro u v hu hv
    rcases hu with ⟨hu_meas, Cu, hCu⟩
    rcases hv with ⟨hv_meas, Cv, hCv⟩
    refine ⟨hu_meas.mul hv_meas, max Cu 0 * max Cv 0, fun l => ?_⟩
    calc
      ‖u l * v l‖ ≤ ‖u l‖ * ‖v l‖ := norm_mul_le (u l) (v l)
      _ ≤ max Cu 0 * max Cv 0 := by
        exact mul_le_mul (le_trans (hCu l) (le_max_left Cu 0))
          (le_trans (hCv l) (le_max_left Cv 0)) (norm_nonneg (v l)) (le_max_right Cu 0)
  -- the polarization of `Q_f` is the inner product with `f(A)` off the diagonal
  have hpol_inner : ∀ (h : spectrum ℝ A → ℂ) (hh : h ∈ BddMeasurable (spectrum ℝ A))
      (φ ψ : H), polarization (borelForm hA h) φ ψ = ⟪φ, borelCalculus hA h ψ⟫_ℂ := by
    intro h hh φ ψ
    let hQ : IsBoundedQuadraticForm (borelForm hA h) := isBoundedQuadraticForm_borelForm hA hh
    have hcalc : borelCalculus hA h = hQ.toOperator := by
      exact hQ.eq_toOperator (fun ζ => (inner_borelCalculus hA hh ζ).symm)
    calc
      polarization (borelForm hA h) φ ψ = hQ.toSesq φ ψ := by simp
      _ = ⟪φ, hQ.toOperator ψ⟫_ℂ := by
        rw [IsBoundedQuadraticForm.toOperator, ContinuousLinearMap.adjoint_inner_right,
          InnerProductSpace.continuousLinearMapOfBilin_apply]
      _ = ⟪φ, borelCalculus hA h ψ⟫_ℂ := by rw [hcalc]
  refine { bddMeasurable := ?_, smul_add_mem := ?_, continuous_mem := ?_, tendsto_mem := ?_ }
  · intro g hg
    exact hg.1
  · intro α β g₁ g₂ hg₁ hg₂
    refine ⟨?_, ?_⟩
    · exact (BddMeasurable (spectrum ℝ A)).add_mem
        ((BddMeasurable (spectrum ℝ A)).smul_mem α hg₁.1)
        ((BddMeasurable (spectrum ℝ A)).smul_mem β hg₂.1)
    · intro s hs
      have hα₁ : (fun l => s l * g₁ l) ∈ BddMeasurable (spectrum ℝ A) := hmul_mem hs hg₁.1
      have hα₂ : (fun l => s l * g₂ l) ∈ BddMeasurable (spectrum ℝ A) := hmul_mem hs hg₂.1
      have hα₁' : α • (fun l => s l * g₁ l) ∈ BddMeasurable (spectrum ℝ A) :=
        (BddMeasurable (spectrum ℝ A)).smul_mem α hα₁
      have hα₂' : β • (fun l => s l * g₂ l) ∈ BddMeasurable (spectrum ℝ A) :=
        (BddMeasurable (spectrum ℝ A)).smul_mem β hα₂
      have hαg₁ : α • g₁ ∈ BddMeasurable (spectrum ℝ A) :=
        (BddMeasurable (spectrum ℝ A)).smul_mem α hg₁.1
      have hβg₂ : β • g₂ ∈ BddMeasurable (spectrum ℝ A) :=
        (BddMeasurable (spectrum ℝ A)).smul_mem β hg₂.1
      have hfunc : (fun l => s l * (α • g₁ + β • g₂) l) =
          α • (fun l => s l * g₁ l) + β • (fun l => s l * g₂ l) := by
        funext l
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hfunc]
      calc
        borelCalculus hA (α • (fun l => s l * g₁ l) + β • (fun l => s l * g₂ l))
            = borelCalculus hA (α • (fun l => s l * g₁ l)) +
                borelCalculus hA (β • (fun l => s l * g₂ l)) := by
                  rw [borelCalculus_add hA hα₁' hα₂']
        _ = α • borelCalculus hA (fun l => s l * g₁ l) +
                β • borelCalculus hA (fun l => s l * g₂ l) := by
                  rw [borelCalculus_smul hA α hα₁, borelCalculus_smul hA β hα₂]
        _ = α • (borelCalculus hA s * borelCalculus hA g₁) +
                β • (borelCalculus hA s * borelCalculus hA g₂) := by
                  rw [hg₁.2 s hs, hg₂.2 s hs]
        _ = borelCalculus hA s * (α • borelCalculus hA g₁ +
                β • borelCalculus hA g₂) := by
                  ext x
                  simp [map_add, map_smul]
        _ = borelCalculus hA s * borelCalculus hA (α • g₁ + β • g₂) := by
                  rw [borelCalculus_add hA hαg₁ hβg₂, borelCalculus_smul hA α hg₁.1,
                    borelCalculus_smul hA β hg₂.1]
  · intro g
    refine ⟨?_, ?_⟩
    · exact (continuous_mem_FClass hA g).1
    · intro s hs
      have hsF1 : s ∈ F1Class hA := by
        rw [F1Class_eq_bddMeasurable hA]
        exact hs
      exact (hsF1.2 g)
  · intro p q M hp hlim
    have hq : q ∈ BddMeasurable (spectrum ℝ A) :=
      ⟨measurable_of_tendsto_pointwise (fun n => (hp n).1.1) hlim.tendsto,
        ⟨M, fun x => norm_le_of_tendsto hlim x⟩⟩
    refine ⟨hq, ?_⟩
    intro s hs
    obtain ⟨Ck, hCk⟩ := hs.2
    have hMea : ∀ n, Measurable (fun l => s l * p n l) := fun n => hs.1.mul (hp n).1.1
    have hBnd : ∀ n l, ‖s l * p n l‖ ≤ |Ck| * |M| := by
      intro n l
      calc
        ‖s l * p n l‖ ≤ ‖s l‖ * ‖p n l‖ := norm_mul_le (s l) (p n l)
        _ ≤ ‖s l‖ * |M| := mul_le_mul_of_nonneg_left
          (le_trans (hlim.norm_le n l) (le_abs_self M)) (norm_nonneg _)
        _ ≤ |Ck| * |M| := mul_le_mul_of_nonneg_right
          (le_trans (hCk l) (le_abs_self Ck)) (abs_nonneg M)
    have hTend : ∀ l, Tendsto (fun n => s l * p n l) atTop (𝓝 (s l * q l)) := by
      intro l
      exact (tendsto_const_nhds (x := s l)).mul (hlim.tendsto l)
    have hSp : BoundedPointwiseLimit (fun n l => s l * p n l) (fun l => s l * q l)
        (fun _ => |Ck| * |M|) := ⟨hBnd, hTend⟩
    have hsq_bdd : (fun l => s l * q l) ∈ BddMeasurable (spectrum ℝ A) := hmul_mem hs hq
    have hQlim : ∀ χ : H,
        Tendsto (fun n => borelForm hA (fun l => s l * p n l) χ) atTop
          (𝓝 (borelForm hA (fun l => s l * q l) χ)) := by
      intro χ
      exact tendsto_borelForm hA (hmeas := hMea) (hlim := hSp) χ
    have hFt : ∀ (n : ℕ) (χ : H),
        borelForm hA (fun l => s l * p n l) χ =
          ⟪χ, (borelCalculus hA s * borelCalculus hA (p n)) χ⟫_ℂ := by
      intro n χ
      have hsp : (fun l => s l * p n l) ∈ BddMeasurable (spectrum ℝ A) := hmul_mem hs (hp n).1
      calc
        borelForm hA (fun l => s l * p n l) χ =
            ⟪χ, borelCalculus hA (fun l => s l * p n l) χ⟫_ℂ := by
              rw [← inner_borelCalculus hA hsp χ]
        _ = ⟪χ, (borelCalculus hA s * borelCalculus hA (p n)) χ⟫_ℂ := by
              rw [(hp n).2 s hs]
    have hTB : ∀ χ : H,
        Tendsto (fun n => ⟪χ, (borelCalculus hA s * borelCalculus hA (p n)) χ⟫_ℂ) atTop
          (𝓝 ⟪χ, (borelCalculus hA s * borelCalculus hA q) χ⟫_ℂ) := by
      intro χ
      have hTpolar : Tendsto (fun n => polarization (borelForm hA (p n))
            ((adjoint (borelCalculus hA s)) χ) χ) atTop
          (𝓝 (polarization (borelForm hA q) ((adjoint (borelCalculus hA s)) χ) χ)) :=
        tendsto_polarization_borelForm hA (hmeas := fun n => (hp n).1.1) hlim
          ((adjoint (borelCalculus hA s)) χ) χ
      have hTinner : Tendsto (fun n =>
          ⟪χ, (borelCalculus hA s * borelCalculus hA (p n)) χ⟫_ℂ) atTop
          (𝓝 (polarization (borelForm hA q) ((adjoint (borelCalculus hA s)) χ) χ)) := by
        refine Tendsto.congr ?_ hTpolar
        intro n
        calc
          polarization (borelForm hA (p n)) ((adjoint (borelCalculus hA s)) χ) χ =
              ⟪(adjoint (borelCalculus hA s)) χ, borelCalculus hA (p n) χ⟫_ℂ := by
                rw [hpol_inner (p n) (hp n).1]
          _ = ⟪χ, (borelCalculus hA s * borelCalculus hA (p n)) χ⟫_ℂ := by
                rw [ContinuousLinearMap.adjoint_inner_left (borelCalculus hA s)
                  (borelCalculus hA (p n) χ) χ]
                simp
      have htail : polarization (borelForm hA q) ((adjoint (borelCalculus hA s)) χ) χ =
          ⟪χ, (borelCalculus hA s * borelCalculus hA q) χ⟫_ℂ := by
        calc
          polarization (borelForm hA q) ((adjoint (borelCalculus hA s)) χ) χ =
              ⟪(adjoint (borelCalculus hA s)) χ, borelCalculus hA q χ⟫_ℂ := by
                rw [hpol_inner q hq]
          _ = ⟪χ, (borelCalculus hA s * borelCalculus hA q) χ⟫_ℂ := by
                rw [ContinuousLinearMap.adjoint_inner_left (borelCalculus hA s)
                  (borelCalculus hA q χ) χ]
                simp
      simpa [htail] using hTinner
    have hmain : ∀ χ : H,
        borelForm hA (fun l => s l * q l) χ =
          ⟪χ, (borelCalculus hA s * borelCalculus hA q) χ⟫_ℂ := by
      intro χ
      have h1 : Tendsto (fun n => borelForm hA (fun l => s l * p n l) χ) atTop
          (𝓝 ⟪χ, (borelCalculus hA s * borelCalculus hA q) χ⟫_ℂ) := by
        simpa [hFt] using hTB χ
      exact tendsto_nhds_unique (hQlim χ) h1
    have hQ : IsBoundedQuadraticForm (borelForm hA (fun l => s l * q l)) :=
      isBoundedQuadraticForm_borelForm hA hsq_bdd
    have hQrep : borelCalculus hA (fun l => s l * q l) = hQ.toOperator := by
      exact hQ.eq_toOperator (fun χ => (inner_borelCalculus hA hsq_bdd χ).symm)
    have hQrep' : borelCalculus hA s * borelCalculus hA q = hQ.toOperator := by
      exact hQ.eq_toOperator (fun χ => hmain χ)
    calc
      borelCalculus hA (fun l => s l * q l) = hQ.toOperator := hQrep
      _ = borelCalculus hA s * borelCalculus hA q := hQrep'.symm

/--
`𝓕₂` is the set of *all* bounded Borel functions on `σ(A)`.

Blueprint reference: `prpstn:F2-is-everything`.
-/
theorem F2Class_eq_bddMeasurable (hA : IsSelfAdjoint A) :
    F2Class hA = (BddMeasurable (spectrum ℝ A) : Set (spectrum ℝ A → ℂ)) :=
  (isBorelGenerating_F2Class hA).eq_bddMeasurable

/--
Multiplicativity of the bounded Borel functional calculus.

Blueprint reference: `prpstn:hall-8.9`.
-/
theorem borelCalculus_mul (hA : IsSelfAdjoint A) {f g : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) (hg : g ∈ BddMeasurable (spectrum ℝ A)) :
    borelCalculus hA (fun l => f l * g l) =
      borelCalculus hA f * borelCalculus hA g := by
  have hgF : g ∈ F2Class hA := by
    rw [F2Class_eq_bddMeasurable hA]
    exact hg
  exact hgF.2 f hf

end Spectral
end Physicslib4
