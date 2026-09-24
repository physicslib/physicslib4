/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.BorelClasses
import Physicslib4.Spectral.Unbounded.Normal
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# From a continuous functional calculus to a projection-valued measure

This file carries out, abstractly, the second stage of the spectral theorem: the input is
a compact metric space `X` and an isometric `*`-homomorphism `Φ : C(X, ℂ) → 𝓑(H)`, with no
operator in sight, and the output is a projection-valued measure `abstractPVM` on `X`
integrating to `Φ`. The bounded self-adjoint case of
`Physicslib4/Spectral/SpectralTheorem.lean` and the bounded normal case below are then two
instances of the one statement.

## Main definitions

* `IsAbstractCalculus` — the five properties of `def:abstract-continuous-functional-calculus`.
* `abstractMeasure` — the measure `μ_ψ` supplied by Riesz representation.
* `abstractForm`, `extendedCalculus` — the quadratic form `Q_f` and the operator `Φ̃(f)`
  for bounded measurable `f`.
* `abstractPVM` — the resulting projection-valued measure.

## Main statements

* `isSelfAdjoint_of_real`, `inner_nonneg_of_nonneg` — an abstract calculus is non-negative.
* `abstractMeasure_univ` — the associated measures are finite of mass `‖ψ‖²`.
* `isBoundedQuadraticForm_abstractForm`, `norm_abstractForm_le` — the extended forms are
  bounded quadratic forms, with bound `‖f‖_∞ ‖ψ‖²`.
* `extendedCalculus_add`, `extendedCalculus_smul`, `inner_extendedCalculus`,
  `tendsto_inner_extendedCalculus`, `isSelfAdjoint_extendedCalculus_of_real`,
  `extendedCalculus_mul`, `extendedCalculus_conj`.
* `abstractPVM_integral`, `abstractPVM_integral_continuous` — the projection-valued
  measure integrates to `Φ̃`, and to `Φ` on continuous functions.
* `norm_extendedCalculus_le` — the extended calculus is norm-bounded.
* `existsUnique_spectralMeasure_normal`, `eq_of_integral_id_eq_ambient` — the spectral
  theorem for bounded normal operators, with its ambient uniqueness form.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A real-valued continuous function, viewed as a complex-valued one. -/
noncomputable def ofRealCM (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

/--
An *abstract continuous functional calculus* on a compact metric space `X`: a map
`C(X, ℂ) → 𝓑(H)` that is linear, multiplicative, intertwines conjugation with the adjoint,
is isometric, and sends the constant function `1` to `1`.

By `thrm:continuous-functional-calculus-normal` a bounded normal operator supplies one on
`X = σ(A)`.

Blueprint reference: `def:abstract-continuous-functional-calculus`.
-/
structure IsAbstractCalculus (Φ : C(X, ℂ) → H →L[ℂ] H) : Prop where
  /-- `Φ` is `ℂ`-linear. -/
  map_smul_add : ∀ (α β : ℂ) (f g : C(X, ℂ)), Φ (α • f + β • g) = α • Φ f + β • Φ g
  /-- `Φ` is multiplicative. -/
  map_mul : ∀ f g : C(X, ℂ), Φ (f * g) = Φ f * Φ g
  /-- `Φ` intertwines complex conjugation with the adjoint. -/
  map_star : ∀ f : C(X, ℂ), Φ (star f) = ContinuousLinearMap.adjoint (Φ f)
  /-- `Φ` is isometric for the supremum norm. -/
  norm_map : ∀ f : C(X, ℂ), ‖Φ f‖ = ‖f‖
  /-- `Φ` is unital. -/
  map_one : Φ 1 = 1

variable {Φ : C(X, ℂ) → H →L[ℂ] H}

omit [MeasurableSpace X] [BorelSpace X] in
/--
A real-valued continuous function gives a self-adjoint operator, and hence a real
expectation value.

Blueprint reference: `lmm:abstract-calculus-non-negative` (Part 1).
-/
theorem isSelfAdjoint_of_real (hΦ : IsAbstractCalculus Φ) (f : C(X, ℝ)) :
    IsSelfAdjoint (Φ (ofRealCM f)) ∧ ∀ ψ : H, (⟪ψ, Φ (ofRealCM f) ψ⟫_ℂ).im = 0 := by
  have hs : star (ofRealCM f) = ofRealCM f := by ext x; simp [ofRealCM]
  have hsa : IsSelfAdjoint (Φ (ofRealCM f)) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', ← hΦ.map_star, hs]
  refine ⟨hsa, fun ψ => Complex.conj_eq_iff_im.mp ?_⟩
  rw [inner_conj_symm]
  exact hsa.isSymmetric ψ ψ

omit [MeasurableSpace X] [BorelSpace X] in
/--
A non-negative continuous function gives a non-negative expectation value.

Blueprint reference: `lmm:abstract-calculus-non-negative` (Part 2).
-/
theorem inner_nonneg_of_nonneg (hΦ : IsAbstractCalculus Φ) {f : C(X, ℝ)} (hf : ∀ x, 0 ≤ f x)
    (ψ : H) : 0 ≤ (⟪ψ, Φ (ofRealCM f) ψ⟫_ℂ).re := by
  let g : C(X, ℝ) := ⟨fun x => Real.sqrt (f x), Real.continuous_sqrt.comp f.continuous⟩
  have hg : ofRealCM f = star (ofRealCM g) * ofRealCM g := by
    ext x
    simp [ofRealCM, g, ← Complex.ofReal_mul, Real.mul_self_sqrt (hf x)]
  rw [hg, hΦ.map_mul, hΦ.map_star]
  change 0 ≤ (⟪ψ, adjoint (Φ (ofRealCM g)) (Φ (ofRealCM g) ψ)⟫_ℂ).re
  rw [adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ)

/--
Riesz representation applied to the positive linear functional `f ↦ ⟪ψ, Φ(f) ψ⟫` supplies
a unique finite positive Borel measure `μ_ψ` on `X`.

Blueprint reference: `def:abstract-associated-measures`.
-/
theorem existsUnique_abstractMeasure (hΦ : IsAbstractCalculus Φ) (ψ : H) :
    ∃! ν : Measure X, IsFiniteMeasure ν ∧
      ∀ f : C(X, ℝ), ∫ x, f x ∂ν = (⟪ψ, Φ (ofRealCM f) ψ⟫_ℂ).re := by
  have hlin : ∀ (a b : ℝ) (g g' : C(X, ℝ)), (⟪ψ, Φ (ofRealCM (a • g + b • g')) ψ⟫_ℂ).re =
      a * (⟪ψ, Φ (ofRealCM g) ψ⟫_ℂ).re + b * (⟪ψ, Φ (ofRealCM g') ψ⟫_ℂ).re := by
    intro a b g g'
    have : ofRealCM (a • g + b • g') = (a : ℂ) • ofRealCM g + (b : ℂ) • ofRealCM g' := by
      ext x; simp [ofRealCM]
    rw [this, hΦ.map_smul_add, _root_.add_apply, _root_.smul_apply, _root_.smul_apply,
      inner_add_right, inner_smul_right, inner_smul_right]
    simp
  let Λ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ :=
  { toFun g := (⟪ψ, Φ (ofRealCM g.toContinuousMap) ψ⟫_ℂ).re
    map_add' g g' := by
      have h := hlin 1 1 g.toContinuousMap g'.toContinuousMap
      simp only [one_smul, one_mul] at h
      exact h
    map_smul' c g := by
      have h := hlin c 0 g.toContinuousMap 0
      simp only [zero_smul, add_zero, zero_mul] at h
      exact h
    monotone' g g' hgg' := by
      have h := hlin 1 1 g.toContinuousMap (g'.toContinuousMap - g.toContinuousMap)
      have h0 := inner_nonneg_of_nonneg hΦ
        (f := g'.toContinuousMap - g.toContinuousMap) (fun x => sub_nonneg.2 (hgg' x)) ψ
      simp only [one_smul, add_sub_cancel, one_mul] at h
      simp only
      linarith }
  refine ⟨RealRMK.rieszMeasure Λ, ⟨inferInstance, fun f => ?_⟩, ?_⟩
  · exact RealRMK.integral_rieszMeasure Λ (CompactlySupportedContinuousMap.continuousMapEquiv f)
  · rintro ν ⟨hν, hνf⟩
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
    exact (hνf f.toContinuousMap).trans (RealRMK.integral_rieszMeasure Λ f).symm

/--
The measure `μ_ψ` associated to `ψ` by an abstract continuous functional calculus.

Blueprint reference: `def:abstract-associated-measures`.
-/
noncomputable def abstractMeasure (hΦ : IsAbstractCalculus Φ) (ψ : H) : Measure X :=
  (existsUnique_abstractMeasure hΦ ψ).choose

instance (hΦ : IsAbstractCalculus Φ) (ψ : H) : IsFiniteMeasure (abstractMeasure hΦ ψ) :=
  (existsUnique_abstractMeasure hΦ ψ).choose_spec.1.1

/--
The defining property of `abstractMeasure`.

Blueprint reference: `def:abstract-associated-measures`.
-/
theorem integral_abstractMeasure (hΦ : IsAbstractCalculus Φ) (ψ : H) (f : C(X, ℝ)) :
    ∫ x, f x ∂(abstractMeasure hΦ ψ) = (⟪ψ, Φ (ofRealCM f) ψ⟫_ℂ).re :=
  (existsUnique_abstractMeasure hΦ ψ).choose_spec.1.2 f

/--
The associated measures are finite, with total mass `‖ψ‖²`.

Blueprint reference: `lmm:abstract-associated-measures-finite`.
-/
theorem abstractMeasure_univ (hΦ : IsAbstractCalculus Φ) (ψ : H) :
    (abstractMeasure hΦ ψ) Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  have h := integral_abstractMeasure hΦ ψ 1
  have h1 : ofRealCM (1 : C(X, ℝ)) = 1 := by ext x; simp [ofRealCM]
  rw [h1, hΦ.map_one] at h
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one,
    one_apply_eq_self, inner_self_eq_norm_sq_to_K] at h
  rw [← ofReal_measureReal (measure_ne_top _ _), h]
  norm_cast

/--
The extended quadratic form `Q_f (ψ) = ∫ f dμ_ψ`, defined for bounded measurable `f`.

Blueprint reference: `prpstn:abstract-extended-forms-are-bounded`.
-/
noncomputable def abstractForm (hΦ : IsAbstractCalculus Φ) (f : X → ℂ) (ψ : H) : ℂ :=
  ∫ x, f x ∂(abstractMeasure hΦ ψ)

/--
For continuous `f`, the extended form is the quadratic form of `Φ(f)`: split `f` into real
and imaginary parts and apply `integral_abstractMeasure` to each. Stated publicly as
`abstractForm_continuous`, after the boundedness results that use it.
-/
private theorem abstractForm_continuous_aux (hΦ : IsAbstractCalculus Φ) (f : C(X, ℂ))
    (ψ : H) : abstractForm hΦ (fun x => f x) ψ = ⟪ψ, Φ f ψ⟫_ℂ := by
  let u : C(X, ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
  let v : C(X, ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
  have hf : f = (1 : ℂ) • ofRealCM u + Complex.I • ofRealCM v := by
    ext x
    simp [ofRealCM, u, v, mul_comm Complex.I]
  have hreal : ∀ g : C(X, ℝ), ((⟪ψ, Φ (ofRealCM g) ψ⟫_ℂ).re : ℂ) = ⟪ψ, Φ (ofRealCM g) ψ⟫_ℂ :=
    fun g => Complex.ext (by simp) (by simp [(isSelfAdjoint_of_real hΦ g).2 ψ])
  have hint : ∀ g : C(X, ℝ), Integrable (fun x => ((g x : ℝ) : ℂ)) (abstractMeasure hΦ ψ) :=
    fun g => (g.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).ofReal
  have e : abstractForm hΦ (fun x => f x) ψ =
      ((∫ x, u x ∂(abstractMeasure hΦ ψ) : ℝ) : ℂ) +
        Complex.I * ((∫ x, v x ∂(abstractMeasure hΦ ψ) : ℝ) : ℂ) := by
    rw [abstractForm, ← integral_complex_ofReal, ← integral_complex_ofReal,
      ← integral_const_mul, ← integral_add (hint u) ((hint v).const_mul _)]
    congr 1
    funext x
    simp [u, v, mul_comm Complex.I]
  rw [e, integral_abstractMeasure, integral_abstractMeasure, hreal, hreal]
  conv_rhs => rw [hf, hΦ.map_smul_add]
  simp [inner_add_right, inner_smul_right]

/--
`Q_f` is a bounded quadratic form, with `|Q_f(ψ)| ≤ ‖f‖_∞ ‖ψ‖²`.

Blueprint reference: `prpstn:abstract-extended-forms-are-bounded`.
-/
theorem isBoundedQuadraticForm_abstractForm (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) : IsBoundedQuadraticForm (abstractForm hΦ f) := by
  let 𝒞 : Set (X → ℂ) :=
    {g | g ∈ BddMeasurable X ∧ IsBoundedQuadraticForm (abstractForm hΦ g)}
  have hint : ∀ ψ, ∀ g ∈ BddMeasurable X, Integrable g (abstractMeasure hΦ ψ) :=
    fun ψ g ⟨hmeas, C, hC⟩ =>
      Integrable.of_bound hmeas.aestronglyMeasurable C (Eventually.of_forall hC)
  have hgen : IsBorelGenerating 𝒞 :=
    { bddMeasurable := fun g hg => hg.1
      smul_add_mem := fun α β g k hg hk => by
        refine ⟨(BddMeasurable X).add_mem ((BddMeasurable X).smul_mem α hg.1)
          ((BddMeasurable X).smul_mem β hk.1), ?_⟩
        have e : abstractForm hΦ (α • g + β • k) =
            α • abstractForm hΦ g + β • abstractForm hΦ k := by
          funext ψ
          simp only [abstractForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [integral_add ((hint ψ g hg.1).const_mul α) ((hint ψ k hk.1).const_mul β),
            integral_const_mul, integral_const_mul]
        rw [e]
        exact (hg.2.smul α).add (hk.2.smul β)
      continuous_mem := fun g => by
        refine ⟨⟨(Complex.continuous_ofReal.comp g.continuous).measurable, ?_⟩, ?_⟩
        · exact ⟨‖ofRealCM g‖, (ofRealCM g).norm_coe_le_norm⟩
        · have e : abstractForm hΦ (fun x => ((g x : ℝ) : ℂ)) =
              fun ψ : H => ⟪ψ, Φ (ofRealCM g) ψ⟫_ℂ :=
            funext fun ψ => abstractForm_continuous_aux hΦ (ofRealCM g) ψ
          rw [e]
          exact isBoundedQuadraticForm_inner _
      tendsto_mem := fun g g₀ M hg hlim => by
        refine ⟨⟨measurable_of_tendsto_pointwise (fun n => (hg n).1.1) hlim.tendsto,
          ⟨M, fun x => norm_le_of_tendsto hlim x⟩⟩, ?_⟩
        refine isBoundedQuadraticForm_of_tendsto (C := M)
          (Q := fun n => abstractForm hΦ (g n)) (hQ := fun n => (hg n).2.isQuadratic)
          ⟨fun n φ => ?_, fun φ => ?_⟩
        · calc ‖abstractForm hΦ (g n) φ‖ ≤ M * (abstractMeasure hΦ φ).real Set.univ :=
                norm_integral_le_of_norm_le_const (Eventually.of_forall (hlim.norm_le n))
            _ = M * ‖φ‖ ^ 2 := by
                rw [Measure.real, abstractMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
        · exact tendsto_integral_of_boundedPointwiseLimit (fun n => (hg n).1.1) hlim }
  have hf' : f ∈ 𝒞 := by
    rw [hgen.eq_bddMeasurable]
    exact hf
  exact hf'.2

/--
The explicit bound `|Q_f(ψ)| ≤ ‖f‖_∞ ‖ψ‖²`, with `‖f‖_∞ = ⨆ x, ‖f x‖` as in
`ProjectionValuedMeasure.norm_integral_le`.

Blueprint reference: `prpstn:abstract-extended-forms-are-bounded` (explicit bound).
-/
theorem norm_abstractForm_le (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) (ψ : H) :
    ‖abstractForm hΦ f ψ‖ ≤ (⨆ x, ‖f x‖) * ‖ψ‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hf.2
  have hbdd : BddAbove (Set.range fun x => ‖f x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  calc ‖abstractForm hΦ f ψ‖ ≤ (⨆ x, ‖f x‖) * (abstractMeasure hΦ ψ).real Set.univ :=
        norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => le_ciSup hbdd x)
    _ = (⨆ x, ‖f x‖) * ‖ψ‖ ^ 2 := by
        rw [Measure.real, abstractMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]

/--
For continuous `f`, the extended form is the quadratic form of `Φ(f)`.

Blueprint reference: `prpstn:abstract-extended-forms-are-bounded` (final claim).
-/
theorem abstractForm_continuous (hΦ : IsAbstractCalculus Φ) (f : C(X, ℂ)) (ψ : H) :
    abstractForm hΦ (fun x => f x) ψ = ⟪ψ, Φ f ψ⟫_ℂ :=
  abstractForm_continuous_aux hΦ f ψ

open Classical in
/--
The extended calculus `Φ̃(f)`: the unique bounded operator whose quadratic form is `Q_f`,
extended by `0` to functions that are not bounded and measurable.

Blueprint reference: `def:abstract-extended-calculus`.
-/
noncomputable def extendedCalculus (hΦ : IsAbstractCalculus Φ) (f : X → ℂ) : H →L[ℂ] H :=
  if h : f ∈ BddMeasurable X then
    (isBoundedQuadraticForm_abstractForm hΦ h).toOperator
  else 0

/--
The defining property of the extended calculus.

Blueprint reference: `def:abstract-extended-calculus`.
-/
theorem inner_extendedCalculus (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) (ψ : H) :
    ⟪ψ, extendedCalculus hΦ f ψ⟫_ℂ = abstractForm hΦ f ψ := by
  rw [extendedCalculus, dif_pos hf]
  exact ((isBoundedQuadraticForm_abstractForm hΦ hf).inner_toOperator ψ).symm

/--
The extended calculus agrees with `Φ` on continuous functions.

Blueprint reference: `def:abstract-extended-calculus` (final clause).
-/
theorem extendedCalculus_continuous (hΦ : IsAbstractCalculus Φ) (f : C(X, ℂ)) :
    extendedCalculus hΦ (fun x => f x) = Φ f := by
  have hf : (fun x => f x) ∈ BddMeasurable X :=
    ⟨f.continuous.measurable, ‖f‖, fun x => f.norm_coe_le_norm x⟩
  rw [extendedCalculus, dif_pos hf]
  exact ((isBoundedQuadraticForm_abstractForm hΦ hf).eq_toOperator
    (abstractForm_continuous hΦ f)).symm

/--
The extended calculus is linear.

Blueprint reference: `lmm:abstract-extended-linear`.
-/
theorem extendedCalculus_smul_add (hΦ : IsAbstractCalculus Φ) (α β : ℂ) {f g : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hg : g ∈ BddMeasurable X) :
    extendedCalculus hΦ (fun x => α * f x + β * g x) =
      α • extendedCalculus hΦ f + β • extendedCalculus hΦ g := by
  have hfg : (fun x => α * f x + β * g x) ∈ BddMeasurable X :=
    Submodule.add_mem _ (Submodule.smul_mem _ α hf) (Submodule.smul_mem _ β hg)
  have hint : ∀ {h : X → ℂ}, h ∈ BddMeasurable X → ∀ ψ : H,
      Integrable h (abstractMeasure hΦ ψ) := fun ⟨hm, C, hC⟩ _ =>
    Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
  rw [extendedCalculus, dif_pos hfg]
  refine ((isBoundedQuadraticForm_abstractForm hΦ hfg).eq_toOperator fun ψ => ?_).symm
  rw [add_apply, smul_apply, smul_apply, inner_add_right, inner_smul_right, inner_smul_right,
    inner_extendedCalculus hΦ hf, inner_extendedCalculus hΦ hg, abstractForm, abstractForm,
    abstractForm, integral_add ((hint hf ψ).const_mul α) ((hint hg ψ).const_mul β),
    integral_const_mul, integral_const_mul]

/--
The off-diagonal formula: the sesquilinear form associated to `Q_h` is
`(φ, ψ) ↦ ⟪φ, Φ̃(h) ψ⟫`.

Blueprint reference: `lmm:abstract-extended-convergence` (Part 1).
-/
theorem polarization_abstractForm (hΦ : IsAbstractCalculus Φ) {h : X → ℂ}
    (hh : h ∈ BddMeasurable X) (φ ψ : H) :
    polarization (abstractForm hΦ h) φ ψ = ⟪φ, extendedCalculus hΦ h ψ⟫_ℂ := by
  rw [show abstractForm hΦ h = fun χ => ⟪χ, extendedCalculus hΦ h χ⟫_ℂ from
    funext fun χ => (inner_extendedCalculus hΦ hh χ).symm]
  exact polarization_inner _ φ ψ

/--
The convergence principle: uniformly bounded pointwise limits of the integrand pass to the
weak limit of the operators.

Blueprint reference: `lmm:abstract-extended-convergence` (Part 2).
-/
theorem tendsto_inner_extendedCalculus (hΦ : IsAbstractCalculus Φ) {h : ℕ → X → ℂ}
    {h₀ : X → ℂ} {M : ℝ} (hh : ∀ i, h i ∈ BddMeasurable X) (hh₀ : h₀ ∈ BddMeasurable X)
    (hbdd : ∀ i x, ‖h i x‖ ≤ M) (hlim : ∀ x, Tendsto (fun i => h i x) atTop (𝓝 (h₀ x)))
    (φ ψ : H) :
    Tendsto (fun i => ⟪φ, extendedCalculus hΦ (h i) ψ⟫_ℂ) atTop
      (𝓝 ⟪φ, extendedCalculus hΦ h₀ ψ⟫_ℂ) := by
  have hQ : ∀ ξ : H, Tendsto (fun i => abstractForm hΦ (h i) ξ) atTop
      (𝓝 (abstractForm hΦ h₀ ξ)) := fun ξ =>
    tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun i => (hh i).1.aestronglyMeasurable) (integrable_const M)
      (fun i => Eventually.of_forall (hbdd i)) (Eventually.of_forall hlim)
  simp_rw [← polarization_abstractForm hΦ (hh _), ← polarization_abstractForm hΦ hh₀,
    polarization]
  exact (tendsto_const_nhds.mul (((hQ _).sub (hQ _)).sub (hQ _))).sub
    (tendsto_const_nhds.mul (((hQ _).sub (hQ _)).sub (hQ _)))

/--
A real-valued bounded measurable function gives a self-adjoint operator.

Blueprint reference: `lmm:abstract-extended-real-self-adjoint`.
-/
theorem isSelfAdjoint_extendedCalculus_of_real (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hreal : ∀ x, (f x).im = 0) :
    IsSelfAdjoint (extendedCalculus hΦ f) := by
  rw [extendedCalculus, dif_pos hf]
  refine (isBoundedQuadraticForm_abstractForm hΦ hf).isSelfAdjoint_toOperator fun ψ => ?_
  have hre : f = fun x => ((f x).re : ℂ) := funext fun x => Complex.ext rfl (by simp [hreal x])
  rw [abstractForm, hre]
  beta_reduce
  rw [integral_complex_ofReal, Complex.ofReal_im]

/--
The extended calculus is multiplicative.

Blueprint reference: `prpstn:abstract-extended-multiplicative`.
-/
theorem extendedCalculus_mul (hΦ : IsAbstractCalculus Φ) {f g : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hg : g ∈ BddMeasurable X) :
    extendedCalculus hΦ (fun x => f x * g x) =
      extendedCalculus hΦ f * extendedCalculus hΦ g := by
  have hmulmem : ∀ {u v : X → ℂ}, u ∈ BddMeasurable X → v ∈ BddMeasurable X →
      (fun x => u x * v x) ∈ BddMeasurable X := by
    rintro u v ⟨hu, Cu, hCu⟩ ⟨hv, Cv, hCv⟩
    exact ⟨hu.mul hv, Cu * Cv, fun x => by
      rw [norm_mul]
      exact mul_le_mul (hCu x) (hCv x) (norm_nonneg _) ((norm_nonneg _).trans (hCu x))⟩
  have hcontmem : ∀ g : C(X, ℂ), (fun x => g x) ∈ BddMeasurable X := fun g =>
    ⟨g.continuous.measurable, ‖g‖, fun x => g.norm_coe_le_norm x⟩
  have hext : ∀ A B : H →L[ℂ] H, (∀ φ ψ, ⟪φ, A ψ⟫_ℂ = ⟪φ, B ψ⟫_ℂ) → A = B := fun A B h =>
    ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => h φ ψ
  have hlim : ∀ (p : ℕ → X → ℂ) (q : X → ℂ) (M : ℝ), (∀ n, p n ∈ BddMeasurable X) →
      BoundedPointwiseLimit p q (fun _ => M) → q ∈ BddMeasurable X := fun p q M hp hpq =>
    ⟨measurable_of_tendsto_metrizable (fun n => (hp n).1) (tendsto_pi_nhds.2 hpq.tendsto),
      M, fun x => le_of_tendsto' (hpq.tendsto x).norm fun n => hpq.norm_le n x⟩
  have hsa : ∀ (α β : ℂ) {u₁ u₂ : X → ℂ}, u₁ ∈ BddMeasurable X → u₂ ∈ BddMeasurable X →
      α • u₁ + β • u₂ ∈ BddMeasurable X := fun α β _ _ h₁ h₂ =>
    (BddMeasurable X).add_mem ((BddMeasurable X).smul_mem α h₁) ((BddMeasurable X).smul_mem β h₂)
  -- Pass 1: the right factor continuous.
  let C₁ : Set (X → ℂ) := {u | u ∈ BddMeasurable X ∧ ∀ g : C(X, ℂ),
    extendedCalculus hΦ (fun x => u x * g x) = extendedCalculus hΦ u * Φ g}
  have hC₁ : IsBorelGenerating C₁ := by
    refine ⟨fun u hu => hu.1, ?_, ?_, ?_⟩
    · rintro α β u₁ u₂ ⟨hu₁, h₁⟩ ⟨hu₂, h₂⟩
      refine ⟨hsa α β hu₁ hu₂, fun g => ?_⟩
      have e1 : (fun x => (α • u₁ + β • u₂) x * g x) =
          fun x => α * (u₁ x * g x) + β * (u₂ x * g x) := by
        funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      have e2 : (α • u₁ + β • u₂) = fun x => α * u₁ x + β * u₂ x := rfl
      rw [e1, extendedCalculus_smul_add hΦ α β (hmulmem hu₁ (hcontmem g))
        (hmulmem hu₂ (hcontmem g)), h₁, h₂, e2, extendedCalculus_smul_add hΦ α β hu₁ hu₂,
        add_mul, smul_mul_assoc, smul_mul_assoc]
    · intro f
      refine ⟨hcontmem (ofRealCM f), fun g => ?_⟩
      have h1 := extendedCalculus_continuous hΦ (ofRealCM f * g)
      simp only [ContinuousMap.mul_apply] at h1
      change extendedCalculus hΦ (fun x => ofRealCM f x * g x) =
        extendedCalculus hΦ (fun x => ofRealCM f x) * Φ g
      rw [h1, extendedCalculus_continuous, hΦ.map_mul]
    · rintro p q M hp hpq
      have hq := hlim p q M (fun n => (hp n).1) hpq
      refine ⟨hq, fun g => hext _ _ fun φ ψ => ?_⟩
      have t1 := tendsto_inner_extendedCalculus hΦ (h := fun n x => p n x * g x)
        (h₀ := fun x => q x * g x) (M := M * ‖g‖)
        (fun n => hmulmem (hp n).1 (hcontmem g)) (hmulmem hq (hcontmem g))
        (fun n x => by
          rw [norm_mul]
          exact mul_le_mul (hpq.norm_le n x) (g.norm_coe_le_norm x) (norm_nonneg _)
            ((norm_nonneg _).trans (hpq.norm_le n x)))
        (fun x => (hpq.tendsto x).mul tendsto_const_nhds) φ ψ
      have t2 := tendsto_inner_extendedCalculus hΦ (fun n => (hp n).1) hq hpq.norm_le
        hpq.tendsto φ (Φ g ψ)
      refine tendsto_nhds_unique (t1.congr fun n => ?_) t2
      rw [(hp n).2 g]
      rfl
  have hC₁eq := hC₁.eq_bddMeasurable
  -- Pass 2: the right factor bounded measurable.
  let C₂ : Set (X → ℂ) := {v | v ∈ BddMeasurable X ∧ ∀ u ∈ BddMeasurable X,
    extendedCalculus hΦ (fun x => u x * v x) = extendedCalculus hΦ u * extendedCalculus hΦ v}
  have hC₂ : IsBorelGenerating C₂ := by
    refine ⟨fun v hv => hv.1, ?_, ?_, ?_⟩
    · rintro α β v₁ v₂ ⟨hv₁, h₁⟩ ⟨hv₂, h₂⟩
      refine ⟨hsa α β hv₁ hv₂, fun u hu => ?_⟩
      have e1 : (fun x => u x * (α • v₁ + β • v₂) x) =
          fun x => α * (u x * v₁ x) + β * (u x * v₂ x) := by
        funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      have e2 : (α • v₁ + β • v₂) = fun x => α * v₁ x + β * v₂ x := rfl
      rw [e1, extendedCalculus_smul_add hΦ α β (hmulmem hu hv₁) (hmulmem hu hv₂), h₁ u hu,
        h₂ u hu, e2, extendedCalculus_smul_add hΦ α β hv₁ hv₂, mul_add, mul_smul_comm,
        mul_smul_comm]
    · intro g
      refine ⟨hcontmem (ofRealCM g), fun u hu => ?_⟩
      have hu1 : u ∈ C₁ := by rw [hC₁eq]; exact hu
      change extendedCalculus hΦ (fun x => u x * ofRealCM g x) =
        extendedCalculus hΦ u * extendedCalculus hΦ (fun x => ofRealCM g x)
      rw [hu1.2, extendedCalculus_continuous]
    · rintro p q M hp hpq
      have hq := hlim p q M (fun n => (hp n).1) hpq
      refine ⟨hq, fun u hu => hext _ _ fun φ ψ => ?_⟩
      obtain ⟨Cu, hCu⟩ := hu.2
      have t1 := tendsto_inner_extendedCalculus hΦ (h := fun n x => u x * p n x)
        (h₀ := fun x => u x * q x) (M := Cu * M)
        (fun n => hmulmem hu (hp n).1) (hmulmem hu hq)
        (fun n x => by
          rw [norm_mul]
          exact mul_le_mul (hCu x) (hpq.norm_le n x) (norm_nonneg _)
            ((norm_nonneg _).trans (hCu x)))
        (fun x => tendsto_const_nhds.mul (hpq.tendsto x)) φ ψ
      have t2 := tendsto_inner_extendedCalculus hΦ (fun n => (hp n).1) hq hpq.norm_le
        hpq.tendsto (ContinuousLinearMap.adjoint (extendedCalculus hΦ u) φ) ψ
      simp only [ContinuousLinearMap.adjoint_inner_left] at t2
      refine tendsto_nhds_unique (t1.congr fun n => ?_) t2
      rw [(hp n).2 u hu]
      rfl
  have hgC : g ∈ C₂ := by rw [hC₂.eq_bddMeasurable]; exact hg
  exact hgC.2 f hf

/--
The extended calculus intertwines conjugation with the adjoint.

Blueprint reference: `lmm:abstract-extended-conjugation`.
-/
theorem extendedCalculus_conj (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) :
    extendedCalculus hΦ (fun x => starRingEnd ℂ (f x)) =
      ContinuousLinearMap.adjoint (extendedCalculus hΦ f) := by
  obtain ⟨hfm, C, hC⟩ := hf
  have hu : (fun x => ((f x).re : ℂ)) ∈ BddMeasurable X :=
    ⟨Complex.measurable_ofReal.comp (Complex.measurable_re.comp hfm), C, fun x => by
      simpa using (Complex.abs_re_le_norm (f x)).trans (hC x)⟩
  have hv : (fun x => ((f x).im : ℂ)) ∈ BddMeasurable X :=
    ⟨Complex.measurable_ofReal.comp (Complex.measurable_im.comp hfm), C, fun x => by
      simpa using (Complex.abs_im_le_norm (f x)).trans (hC x)⟩
  have hsu := isSelfAdjoint_extendedCalculus_of_real hΦ hu (fun x => by simp)
  have hsv := isSelfAdjoint_extendedCalculus_of_real hΦ hv (fun x => by simp)
  have e1 : (fun x => starRingEnd ℂ (f x)) =
      fun x => 1 * ((f x).re : ℂ) + (-Complex.I) * ((f x).im : ℂ) := by
    funext x; apply Complex.ext <;> simp
  have e2 : f = fun x => 1 * ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ) := by
    funext x; apply Complex.ext <;> simp
  conv_rhs => rw [e2]
  rw [e1, extendedCalculus_smul_add hΦ _ _ hu hv, extendedCalculus_smul_add hΦ _ _ hu hv,
    map_add, map_smulₛₗ, map_smulₛₗ, hsu.adjoint_eq, hsv.adjoint_eq]
  simp

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
/-- The indicator `1_E` is bounded and measurable exactly when `E` is measurable. -/
theorem indicator_one_mem_bddMeasurable_iff {E : Set X} :
    E.indicator (1 : X → ℂ) ∈ BddMeasurable X ↔ MeasurableSet E :=
  ⟨fun h => (measurable_indicator_const_iff (1 : ℂ)).1 h.1, indicator_one_mem_bddMeasurable⟩

/-- `Φ̃(0) = 0`. -/
theorem extendedCalculus_zero (hΦ : IsAbstractCalculus Φ) :
    extendedCalculus hΦ (0 : X → ℂ) = 0 := by
  have h := extendedCalculus_smul_add hΦ 0 0 (zero_mem (BddMeasurable X))
    (zero_mem (BddMeasurable X))
  simp only [zero_mul, add_zero, zero_smul] at h
  exact h

/-- `Φ̃(1_{E ∩ F}) = Φ̃(1_E) Φ̃(1_F)`. -/
theorem extendedCalculus_indicator_inter (hΦ : IsAbstractCalculus Φ) {E F : Set X}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    extendedCalculus hΦ ((E ∩ F).indicator (1 : X → ℂ)) =
      extendedCalculus hΦ (E.indicator 1) * extendedCalculus hΦ (F.indicator 1) := by
  rw [← extendedCalculus_mul hΦ (indicator_one_mem_bddMeasurable hE)
    (indicator_one_mem_bddMeasurable hF), Set.inter_indicator_one]
  rfl

/-- `Φ̃(1_{E ∪ F}) = Φ̃(1_E) + Φ̃(1_F)` for disjoint `E`, `F`. -/
theorem extendedCalculus_indicator_union (hΦ : IsAbstractCalculus Φ) {E F : Set X}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hEF : Disjoint E F) :
    extendedCalculus hΦ ((E ∪ F).indicator (1 : X → ℂ)) =
      extendedCalculus hΦ (E.indicator 1) + extendedCalculus hΦ (F.indicator 1) := by
  have h := extendedCalculus_smul_add hΦ 1 1 (indicator_one_mem_bddMeasurable hE)
    (indicator_one_mem_bddMeasurable hF)
  simp only [one_mul, one_smul] at h
  rw [← h, Set.indicator_union_of_disjoint hEF]

/-- Each `Φ̃(1_E)` is an orthogonal projection. -/
theorem isStarProjection_extendedCalculus_indicator (hΦ : IsAbstractCalculus Φ)
    (E : Set X) : IsStarProjection (extendedCalculus hΦ (E.indicator (1 : X → ℂ))) := by
  by_cases hE : MeasurableSet E
  · refine ⟨?_, isSelfAdjoint_extendedCalculus_of_real hΦ
      (indicator_one_mem_bddMeasurable hE) fun x => ?_⟩
    · rw [IsIdempotentElem, ← extendedCalculus_indicator_inter hΦ hE hE, Set.inter_self]
    · by_cases hx : x ∈ E <;> simp [hx]
  · rw [extendedCalculus, dif_neg (mt indicator_one_mem_bddMeasurable_iff.1 hE)]
    exact IsStarProjection.zero _

/-- For an orthogonal projection `P`, `‖P ψ‖² = Re ⟪ψ, P ψ⟫`. -/
theorem norm_sq_apply_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) (ψ : H) :
    ‖P ψ‖ ^ 2 = (⟪ψ, P ψ⟫_ℂ).re := by
  rw [apply_norm_sq_eq_inner_adjoint_right, ← star_eq_adjoint, hP.isSelfAdjoint.star_eq]
  exact congrArg (fun T : H →L[ℂ] H => (⟪ψ, T ψ⟫_ℂ).re) hP.isIdempotentElem

/-- Countable additivity of `E ↦ Φ̃(1_E)`, in the norm topology of `H`. -/
theorem hasSum_extendedCalculus_indicator (hΦ : IsAbstractCalculus Φ) (E : ℕ → Set X)
    (hE : ∀ j, MeasurableSet (E j)) (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (v : H) :
    HasSum (fun j => extendedCalculus hΦ ((E j).indicator (1 : X → ℂ)) v)
      (extendedCalculus hΦ ((⋃ j, E j).indicator (1 : X → ℂ)) v) := by
  let P : Set X → H →L[ℂ] H := fun S => extendedCalculus hΦ (S.indicator (1 : X → ℂ))
  let F : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, E i
  have hF : ∀ n, MeasurableSet (F n) := fun n =>
    Finset.measurableSet_biUnion _ fun i _ => hE i
  have hU : MeasurableSet (⋃ j, E j) := MeasurableSet.iUnion hE
  -- the partial sums are `Φ̃(1_{F n})`, and the tails are `Φ̃(1_{U \ F n})`
  have hsum : ∀ n, ∑ i ∈ Finset.range n, P (E i) = P (F n) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, P, F, Finset.notMem_empty,
        Set.iUnion_of_empty, Set.iUnion_empty, Set.indicator_empty]
      exact (extendedCalculus_zero hΦ).symm
    | succ n ih =>
      have hFn : F (n + 1) = F n ∪ E n := by
        simp only [F, Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
      rw [Finset.sum_range_succ, ih, hFn]
      exact (extendedCalculus_indicator_union hΦ (hF n) (hE n)
        (Set.disjoint_iUnion₂_left.2 fun i hi => hdisj (Finset.mem_range.1 hi).ne)).symm
  have htail : ∀ n, P (⋃ j, E j) - P (F n) = P ((⋃ j, E j) \ F n) := by
    intro n
    have hsub : F n ⊆ ⋃ j, E j := Set.iUnion₂_subset fun i _ => Set.subset_iUnion E i
    rw [sub_eq_iff_eq_add', ← extendedCalculus_indicator_union hΦ (hF n) (hU.diff (hF n))
      Set.disjoint_sdiff_right, Set.union_sdiff_cancel hsub]
  refine hasSum_of_isStarProjection_orthogonal (P := fun j => P (E j))
    (fun i => isStarProjection_extendedCalculus_indicator hΦ _) (fun i j hij => ?_)
    (P (⋃ j, E j)) (fun ψ => ?_) v
  · rw [← extendedCalculus_indicator_inter hΦ (hE i) (hE j), (hdisj hij).inter_eq,
      Set.indicator_empty]
    exact extendedCalculus_zero hΦ
  · -- `‖Φ̃(1_{U \ F n}) ψ‖² = Re ⟪ψ, Φ̃(1_{U \ F n}) ψ⟫ → 0` by the convergence principle
    have hlim : ∀ x, Tendsto (fun n => ((⋃ j, E j) \ F n).indicator (1 : X → ℂ) x) atTop
        (𝓝 ((0 : X → ℂ) x)) := by
      intro x
      refine tendsto_const_nhds.congr' ?_
      by_cases hx : x ∈ ⋃ j, E j
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
        filter_upwards [eventually_gt_atTop j] with n hn
        have : x ∈ F n := Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hn, hj⟩
        simp [this]
      · exact Eventually.of_forall fun n => by simp [hx]
    have hconv := tendsto_inner_extendedCalculus hΦ (M := 1)
      (fun n => indicator_one_mem_bddMeasurable (hU.diff (hF n)))
      (zero_mem (BddMeasurable X))
      (fun n x => by by_cases hx : x ∈ (⋃ j, E j) \ F n <;> simp [hx]) hlim ψ ψ
    rw [extendedCalculus_zero, zero_apply, inner_zero_right] at hconv
    have hre := (Complex.continuous_re.tendsto 0).comp hconv
    rw [Complex.zero_re] at hre
    have hsq : Tendsto (fun n => ‖P (F n) ψ - P (⋃ j, E j) ψ‖ ^ 2) atTop (𝓝 0) := by
      refine hre.congr fun n => ?_
      rw [Function.comp_apply, ← norm_neg, neg_sub, ← sub_apply, htail,
        norm_sq_apply_of_isStarProjection (isStarProjection_extendedCalculus_indicator hΦ _)]
    simp_rw [← sum_apply, hsum]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt

/--
The projection-valued measure manufactured from an abstract continuous functional
calculus: `μ^Φ(E) = Φ̃(1_E)`.

Blueprint reference: `thrm:abstract-calculus-yields-pvm`.
-/
noncomputable def abstractPVM (hΦ : IsAbstractCalculus Φ) : ProjectionValuedMeasure X H where
  toFun E := extendedCalculus hΦ (E.indicator (1 : X → ℂ))
  isStarProjection' := isStarProjection_extendedCalculus_indicator hΦ
  notMeasurable' E hE := by
    rw [extendedCalculus, dif_neg (mt indicator_one_mem_bddMeasurable_iff.1 hE)]
  univ' := by
    rw [Set.indicator_univ, ← hΦ.map_one, ← extendedCalculus_continuous hΦ 1]
    rfl
  hasSum' := hasSum_extendedCalculus_indicator hΦ
  inter' E F hE hF := extendedCalculus_indicator_inter hΦ hE hF

@[simp]
theorem abstractPVM_apply (hΦ : IsAbstractCalculus Φ) (E : Set X) :
    abstractPVM hΦ E = extendedCalculus hΦ (E.indicator (1 : X → ℂ)) := rfl

/-- The measures associated with `μ^Φ` are the measures `μ_ψ` of the calculus. -/
theorem abstractPVM_assoc (hΦ : IsAbstractCalculus Φ) (ψ : H) :
    (abstractPVM hΦ).assoc ψ = abstractMeasure hΦ ψ := by
  refine Measure.ext fun E hE => ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ E),
    ← ENNReal.ofReal_toReal (measure_ne_top (abstractMeasure hΦ ψ) E),
    ProjectionValuedMeasure.assoc_apply _ ψ hE, abstractPVM_apply,
    inner_extendedCalculus hΦ (indicator_one_mem_bddMeasurable hE), abstractForm]
  change ENNReal.ofReal (∫ x, E.indicator (fun _ => (1 : ℂ)) x ∂abstractMeasure hΦ ψ).re = _
  rw [integral_indicator_const _ hE, Measure.real_def]
  simp

/--
The projection-valued measure integrates to the extended calculus; in particular to `Φ`
on continuous functions.

Blueprint reference: `thrm:abstract-calculus-yields-pvm`.
-/
theorem abstractPVM_integral (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) :
    (abstractPVM hΦ).integral f = extendedCalculus hΦ f := by
  have hQ := isBoundedQuadraticForm_abstractForm hΦ hf
  refine (hQ.eq_toOperator fun ψ => ?_).trans
    (hQ.eq_toOperator fun ψ => (inner_extendedCalculus hΦ hf ψ).symm).symm
  rw [ProjectionValuedMeasure.inner_integral _ hf, abstractPVM_assoc]
  rfl

/--
On continuous functions the projection-valued measure integrates to `Φ` itself.

Blueprint reference: `thrm:abstract-calculus-yields-pvm` (final clause).
-/
theorem abstractPVM_integral_continuous (hΦ : IsAbstractCalculus Φ) (f : C(X, ℂ)) :
    (abstractPVM hΦ).integral (fun x => f x) = Φ f :=
  (abstractPVM_integral hΦ ⟨f.continuous.measurable, ‖f‖, f.norm_coe_le_norm⟩).trans
    (extendedCalculus_continuous hΦ f)

/--
The extended calculus is bounded by the supremum norm `‖f‖_∞ = ⨆ x, ‖f x‖` of the
integrand (the same form as `ProjectionValuedMeasure.norm_integral_le`; the supremum is
`0` when `X` is empty).

Blueprint reference: `crllr:abstract-extended-norm-bound`.
-/
theorem norm_extendedCalculus_le (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) :
    ‖extendedCalculus hΦ f‖ ≤ ⨆ x, ‖f x‖ :=
  abstractPVM_integral hΦ hf ▸ (abstractPVM hΦ).norm_integral_le hf

/-!
### The spectral theorem for bounded normal operators
-/

/--
The inclusion of `σ(A)` into a compact ambient set `Y ⊆ ℂ` containing it.
-/
def inclSpectrum {A : H →L[ℂ] H} {Y : Set ℂ} (hsub : spectrum ℂ A ⊆ Y) :
    spectrum ℂ A → Y := fun lam => ⟨(lam : ℂ), hsub lam.2⟩

omit [CompleteSpace H] in
/-- `inclSpectrum` is continuous. -/
theorem continuous_inclSpectrum {A : H →L[ℂ] H} {Y : Set ℂ} (hsub : spectrum ℂ A ⊆ Y) :
    Continuous (inclSpectrum hsub) :=
  continuous_subtype_val.subtype_mk _

/-- A continuous function on a compact space is a bounded measurable integrand. -/
theorem continuousMap_mem_bddMeasurable {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] (f : C(Z, ℂ)) :
    (fun z => f z) ∈ BddMeasurable Z :=
  ⟨f.continuous.measurable, ‖f‖, f.norm_coe_le_norm⟩

/-- On a compact space, `f ↦ ∫ f dμ` is continuous (indeed `1`-Lipschitz) for the sup
norm on `C(Z, ℂ)`. -/
theorem continuous_integral_continuousMap {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] (μ : ProjectionValuedMeasure Z H) :
    Continuous fun f : C(Z, ℂ) => μ.integral (fun z => f z) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
  have hsub : μ.integral (fun z => f z) - μ.integral (fun z => g z) =
      μ.integral (fun z => (f - g) z) := by
    have h := μ.integral_add (continuousMap_mem_bddMeasurable f)
      ((BddMeasurable Z).smul_mem (-1) (continuousMap_mem_bddMeasurable g))
    rw [μ.integral_smul _ (continuousMap_mem_bddMeasurable g)] at h
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (μ.integral _), ← h]
    congr 1; ext z; simp [sub_eq_add_neg]
  rw [dist_eq_norm, dist_eq_norm, hsub, NNReal.coe_one, one_mul]
  exact (μ.norm_integral_le (continuousMap_mem_bddMeasurable _)).trans
    (Real.iSup_le (fun z => ContinuousMap.norm_coe_le_norm _ z) (norm_nonneg _))

/-- The integral of a constant `c` is `c • 1`. -/
theorem integral_const_eq_smul_one {Z : Type*} [MeasurableSpace Z]
    (μ : ProjectionValuedMeasure Z H) (c : ℂ) : μ.integral (fun _ => c) = c • 1 := by
  rw [show (fun _ => c) = c • (1 : Z → ℂ) by ext; simp,
    μ.integral_smul c (f := 1) ⟨measurable_const, 1, fun _ => by simp⟩, μ.integral_one]

/-- If PVMs on `Y ⊇ σ(A)` and on `σ(A)` both integrate the identity to `A`, then they
agree on every continuous `g` on `Y` (restricted to `σ(A)` on the right): both sides are
`*`-homomorphisms in `g` agreeing on `λ`, and Stone–Weierstrass gives density. -/
theorem integral_continuousMap_eq_comp_inclSpectrum {A : H →L[ℂ] H} {Y : Set ℂ}
    [CompactSpace Y] (hsub : spectrum ℂ A ⊆ Y) {μA : ProjectionValuedMeasure (spectrum ℂ A) H}
    (hμA : μA.integral (fun lam => (lam : ℂ)) = A)
    {ν : ProjectionValuedMeasure Y H} (hν : ν.integral (fun y => (y : ℂ)) = A) (g : C(Y, ℂ)) :
    ν.integral (fun y => g y) = μA.integral (fun lam => g (inclSpectrum hsub lam)) := by
  let inc : C(spectrum ℂ A, Y) := ⟨inclSpectrum hsub, continuous_inclSpectrum hsub⟩
  have hB := continuousMap_mem_bddMeasurable (Z := Y)
  have hB' := continuousMap_mem_bddMeasurable (Z := spectrum ℂ A)
  let S : StarSubalgebra ℂ C(Y, ℂ) :=
    { carrier := {g | ν.integral (fun y => g y) = μA.integral (fun lam => g.comp inc lam)}
      mul_mem' := fun {f g} hf hg => by
        change ν.integral ((fun y => f y) * fun y => g y) =
          μA.integral ((fun lam => f.comp inc lam) * fun lam => g.comp inc lam)
        rw [ν.integral_mul (hB f) (hB g), μA.integral_mul (hB' _) (hB' _)]
        exact congrArg₂ _ hf hg
      add_mem' := fun {f g} hf hg => by
        change ν.integral ((fun y => f y) + fun y => g y) =
          μA.integral ((fun lam => f.comp inc lam) + fun lam => g.comp inc lam)
        rw [ν.integral_add (hB f) (hB g), μA.integral_add (hB' _) (hB' _)]
        exact congrArg₂ _ hf hg
      algebraMap_mem' := fun c => by
        change ν.integral (fun _ => algebraMap ℂ ℂ c) =
          μA.integral (fun _ => algebraMap ℂ ℂ c)
        rw [integral_const_eq_smul_one, integral_const_eq_smul_one]
      star_mem' := fun {g} hg => by
        change ν.integral (fun y => starRingEnd ℂ (g y)) =
          μA.integral (fun lam => starRingEnd ℂ (g.comp inc lam))
        rw [ν.integral_conj (hB g), μA.integral_conj (hB' _)]
        exact congrArg _ hg }
  have hι : ContinuousMap.restrict Y (.id ℂ) ∈ S := by
    change ν.integral (fun y => (y : ℂ)) = μA.integral (fun lam => (lam : ℂ))
    rw [hν, hμA]
  have hadj : StarAlgebra.adjoin ℂ {ContinuousMap.restrict Y (.id ℂ)} ≤ S :=
    StarAlgebra.adjoin_le (Set.singleton_subset_iff.mpr hι)
  have hclos : closure (StarAlgebra.adjoin ℂ {ContinuousMap.restrict Y (.id ℂ)} :
      Set C(Y, ℂ)) = Set.univ := by
    have := ContinuousMap.elemental_id_eq_top Y
    rw [StarAlgebra.elemental] at this
    rw [← StarSubalgebra.topologicalClosure_coe, this, StarSubalgebra.coe_top]
  exact Set.EqOn.closure (fun f hf => hadj hf) (continuous_integral_continuousMap ν)
    ((continuous_integral_continuousMap μA).comp (ContinuousMap.continuous_precomp inc))
    (hclos ▸ Set.mem_univ g)

/-- Under the hypotheses of `integral_continuousMap_eq_comp_inclSpectrum`, the measure
`ν_ψ` on `Y` is the push-forward of `(μA)_ψ` along `inclSpectrum`. -/
theorem assoc_eq_map_inclSpectrum {A : H →L[ℂ] H} {Y : Set ℂ} [CompactSpace Y]
    (hsub : spectrum ℂ A ⊆ Y) {μA : ProjectionValuedMeasure (spectrum ℂ A) H}
    (hμA : μA.integral (fun lam => (lam : ℂ)) = A)
    {ν : ProjectionValuedMeasure Y H} (hν : ν.integral (fun y => (y : ℂ)) = A) (ψ : H) :
    ν.assoc ψ = (μA.assoc ψ).map (inclSpectrum hsub) := by
  have hm := (continuous_inclSpectrum hsub).measurable
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  let g : C(Y, ℂ) := ⟨fun y => (f y : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  let inc : C(spectrum ℂ A, Y) := ⟨inclSpectrum hsub, continuous_inclSpectrum hsub⟩
  have h := congrArg (fun T : H →L[ℂ] H => ⟪ψ, T ψ⟫_ℂ)
    (integral_continuousMap_eq_comp_inclSpectrum hsub hμA hν g)
  rw [ν.inner_integral (continuousMap_mem_bddMeasurable g),
    μA.inner_integral (f := fun lam => g (inclSpectrum hsub lam))
      (continuousMap_mem_bddMeasurable (g.comp inc))] at h
  change ∫ x, ((f x : ℝ) : ℂ) ∂_ = ∫ x, ((f (inclSpectrum hsub x) : ℝ) : ℂ) ∂_ at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  rw [integral_map hm.aemeasurable f.continuous.aestronglyMeasurable]
  exact_mod_cast h

/-- The ambient uniqueness statement, for a compact `Y ⊇ σ(A)` (normality of `A` is not
needed): `ν(E) = μA(E ∩ σ(A))`, compared through the associated measures. -/
theorem apply_eq_apply_preimage_inclSpectrum {A : H →L[ℂ] H} {Y : Set ℂ} [CompactSpace Y]
    (hsub : spectrum ℂ A ⊆ Y) {μA : ProjectionValuedMeasure (spectrum ℂ A) H}
    (hμA : μA.integral (fun lam => (lam : ℂ)) = A)
    {ν : ProjectionValuedMeasure Y H} (hν : ν.integral (fun y => (y : ℂ)) = A)
    {E : Set Y} (hE : MeasurableSet E) :
    ν E = μA (inclSpectrum hsub ⁻¹' E) := by
  have hm := (continuous_inclSpectrum hsub).measurable
  have hE' : MeasurableSet (inclSpectrum hsub ⁻¹' E) := hm hE
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun ψ => ?_)
  change ⟪ν E ψ, ψ⟫_ℂ = ⟪μA (inclSpectrum hsub ⁻¹' E) ψ, ψ⟫_ℂ
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  congr 1
  rw [← ν.integral_indicator hE, ν.inner_integral (indicator_one_mem_bddMeasurable hE),
    assoc_eq_map_inclSpectrum hsub hμA hν,
    integral_map hm.aemeasurable (indicator_one_mem_bddMeasurable hE).1.aestronglyMeasurable,
    ← μA.integral_indicator hE', μA.inner_integral (indicator_one_mem_bddMeasurable hE')]
  rfl

/--
**Spectral theorem for bounded normal operators.** A bounded normal operator on a nonzero
Hilbert space is the integral of the identity function against a unique projection-valued
measure on `σ(A)`.

Blueprint reference: `thrm:hall-10.20`.
-/
theorem existsUnique_spectralMeasure_normal {A : H →L[ℂ] H}
    (hA : IsStarNormal A) :
    ∃! μ : ProjectionValuedMeasure (spectrum ℂ A) H,
      μ.integral (fun lam => (lam : ℂ)) = A := by
  have hΦ : IsAbstractCalculus (H := H) (normalCalculus hA) :=
    { map_smul_add := fun α β f g => by simp only [map_add, map_smul]
      map_mul := normalCalculus_mul hA
      map_star := fun f => by rw [normalCalculus_star, star_eq_adjoint]
      norm_map := norm_normalCalculus hA
      map_one := (normalCalculus_one_and_id hA).1 }
  have hμ : (abstractPVM hΦ).integral (fun lam => (lam : ℂ)) = A :=
    (abstractPVM_integral_continuous hΦ ⟨fun lam => (lam : ℂ), continuous_subtype_val⟩).trans
      (normalCalculus_one_and_id hA).2
  refine ⟨abstractPVM hΦ, hμ, fun ν hν => ProjectionValuedMeasure.ext fun E => ?_⟩
  by_cases hE : MeasurableSet E
  · exact apply_eq_apply_preimage_inclSpectrum subset_rfl hμ hν hE
  · rw [ν.apply_of_not_measurableSet hE, (abstractPVM hΦ).apply_of_not_measurableSet hE]

/--
The ambient form of uniqueness: a projection-valued measure on a larger compact set `Y`
integrating to `A` assigns no mass off `σ(A)` and agrees with `μ^A` there.

Blueprint reference: `thrm:hall-10.20`.
-/
theorem eq_of_integral_id_eq_ambient {A : H →L[ℂ] H} (_hA : IsStarNormal A)
    {Y : Set ℂ} (hY : IsCompact Y) (hsub : spectrum ℂ A ⊆ Y)
    {μA : ProjectionValuedMeasure (spectrum ℂ A) H}
    (hμA : μA.integral (fun lam => (lam : ℂ)) = A)
    {ν : ProjectionValuedMeasure Y H} (hν : ν.integral (fun y => (y : ℂ)) = A)
    {E : Set Y} (hE : MeasurableSet E) :
    ν E = μA (inclSpectrum hsub ⁻¹' E) :=
  haveI := isCompact_iff_compactSpace.mp hY
  apply_eq_apply_preimage_inclSpectrum hsub hμA hν hE

end Unbounded
end Spectral
end Physicslib4
