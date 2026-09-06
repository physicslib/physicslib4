/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.BorelClasses
import Physicslib4.Spectral.Unbounded.Normal

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
* `isBoundedQuadraticForm_abstractForm` — the extended forms are bounded quadratic forms.
* `extendedCalculus_add`, `extendedCalculus_smul`, `inner_extendedCalculus`,
  `tendsto_inner_extendedCalculus`, `isSelfAdjoint_extendedCalculus_of_real`,
  `extendedCalculus_mul`, `extendedCalculus_conj`.
* `abstractPVM_integral` — the projection-valued measure integrates to `Φ̃`.
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

/--
A real-valued continuous function gives a self-adjoint operator, and hence a real
expectation value.

Blueprint reference: `lmm:abstract-calculus-non-negative` (Part 1).
-/
theorem isSelfAdjoint_of_real (hΦ : IsAbstractCalculus Φ) (f : C(X, ℝ)) :
    IsSelfAdjoint (Φ (ofRealCM f)) ∧ ∀ ψ : H, (⟪ψ, Φ (ofRealCM f) ψ⟫_ℂ).im = 0 := by
  sorry

/--
A non-negative continuous function gives a non-negative expectation value.

Blueprint reference: `lmm:abstract-calculus-non-negative` (Part 2).
-/
theorem inner_nonneg_of_nonneg (hΦ : IsAbstractCalculus Φ) {f : C(X, ℝ)} (hf : ∀ x, 0 ≤ f x)
    (ψ : H) : 0 ≤ (⟪ψ, Φ (ofRealCM f) ψ⟫_ℂ).re := by
  sorry

/--
Riesz representation applied to the positive linear functional `f ↦ ⟪ψ, Φ(f) ψ⟫` supplies
a unique finite positive Borel measure `μ_ψ` on `X`.

Blueprint reference: `def:abstract-associated-measures`.
-/
theorem existsUnique_abstractMeasure (hΦ : IsAbstractCalculus Φ) (ψ : H) :
    ∃! ν : Measure X, IsFiniteMeasure ν ∧
      ∀ f : C(X, ℝ), ∫ x, f x ∂ν = (⟪ψ, Φ (ofRealCM f) ψ⟫_ℂ).re := by
  sorry

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
  sorry

/--
The extended quadratic form `Q_f (ψ) = ∫ f dμ_ψ`, defined for bounded measurable `f`.

Blueprint reference: `prpstn:abstract-extended-forms-are-bounded`.
-/
noncomputable def abstractForm (hΦ : IsAbstractCalculus Φ) (f : X → ℂ) (ψ : H) : ℂ :=
  ∫ x, f x ∂(abstractMeasure hΦ ψ)

/--
`Q_f` is a bounded quadratic form, with `|Q_f(ψ)| ≤ ‖f‖_∞ ‖ψ‖²`.

Blueprint reference: `prpstn:abstract-extended-forms-are-bounded`.
-/
theorem isBoundedQuadraticForm_abstractForm (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) : IsBoundedQuadraticForm (abstractForm hΦ f) := by
  sorry

/--
For continuous `f`, the extended form is the quadratic form of `Φ(f)`.

Blueprint reference: `prpstn:abstract-extended-forms-are-bounded` (final claim).
-/
theorem abstractForm_continuous (hΦ : IsAbstractCalculus Φ) (f : C(X, ℂ)) (ψ : H) :
    abstractForm hΦ (fun x => f x) ψ = ⟪ψ, Φ f ψ⟫_ℂ := by
  sorry

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
  sorry

/--
The extended calculus agrees with `Φ` on continuous functions.

Blueprint reference: `def:abstract-extended-calculus` (final clause).
-/
theorem extendedCalculus_continuous (hΦ : IsAbstractCalculus Φ) (f : C(X, ℂ)) :
    extendedCalculus hΦ (fun x => f x) = Φ f := by
  sorry

/--
The extended calculus is linear.

Blueprint reference: `lmm:abstract-extended-linear`.
-/
theorem extendedCalculus_smul_add (hΦ : IsAbstractCalculus Φ) (α β : ℂ) {f g : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hg : g ∈ BddMeasurable X) :
    extendedCalculus hΦ (fun x => α * f x + β * g x) =
      α • extendedCalculus hΦ f + β • extendedCalculus hΦ g := by
  sorry

/--
The off-diagonal formula: the sesquilinear form associated to `Q_h` is
`(φ, ψ) ↦ ⟪φ, Φ̃(h) ψ⟫`.

Blueprint reference: `lmm:abstract-extended-convergence` (Part 1).
-/
theorem polarization_abstractForm (hΦ : IsAbstractCalculus Φ) {h : X → ℂ}
    (hh : h ∈ BddMeasurable X) (φ ψ : H) :
    polarization (abstractForm hΦ h) φ ψ = ⟪φ, extendedCalculus hΦ h ψ⟫_ℂ := by
  sorry

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
  sorry

/--
A real-valued bounded measurable function gives a self-adjoint operator.

Blueprint reference: `lmm:abstract-extended-real-self-adjoint`.
-/
theorem isSelfAdjoint_extendedCalculus_of_real (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hreal : ∀ x, (f x).im = 0) :
    IsSelfAdjoint (extendedCalculus hΦ f) := by
  sorry

/--
The extended calculus is multiplicative.

Blueprint reference: `prpstn:abstract-extended-multiplicative`.
-/
theorem extendedCalculus_mul (hΦ : IsAbstractCalculus Φ) {f g : X → ℂ}
    (hf : f ∈ BddMeasurable X) (hg : g ∈ BddMeasurable X) :
    extendedCalculus hΦ (fun x => f x * g x) =
      extendedCalculus hΦ f * extendedCalculus hΦ g := by
  sorry

/--
The extended calculus intertwines conjugation with the adjoint.

Blueprint reference: `lmm:abstract-extended-conjugation`.
-/
theorem extendedCalculus_conj (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) :
    extendedCalculus hΦ (fun x => starRingEnd ℂ (f x)) =
      ContinuousLinearMap.adjoint (extendedCalculus hΦ f) := by
  sorry

/--
The projection-valued measure manufactured from an abstract continuous functional
calculus: `μ^Φ(E) = Φ̃(1_E)`.

Blueprint reference: `thrm:abstract-calculus-yields-pvm`.
-/
noncomputable def abstractPVM (hΦ : IsAbstractCalculus Φ) : ProjectionValuedMeasure X H where
  toFun E := extendedCalculus hΦ (E.indicator (1 : X → ℂ))
  isStarProjection' := by sorry
  notMeasurable' := by sorry
  univ' := by sorry
  hasSum' := by sorry
  inter' := by sorry

@[simp]
theorem abstractPVM_apply (hΦ : IsAbstractCalculus Φ) (E : Set X) :
    abstractPVM hΦ E = extendedCalculus hΦ (E.indicator (1 : X → ℂ)) := rfl

/--
The projection-valued measure integrates to the extended calculus; in particular to `Φ`
on continuous functions.

Blueprint reference: `thrm:abstract-calculus-yields-pvm`.
-/
theorem abstractPVM_integral (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) :
    (abstractPVM hΦ).integral f = extendedCalculus hΦ f := by
  sorry

/--
The extended calculus is bounded by the supremum norm of the integrand.

Blueprint reference: `crllr:abstract-extended-norm-bound`.
-/
theorem norm_extendedCalculus_le (hΦ : IsAbstractCalculus Φ) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖extendedCalculus hΦ f‖ ≤ C := by
  sorry

/-!
### The spectral theorem for bounded normal operators
-/

/--
The inclusion of `σ(A)` into a compact ambient set `Y ⊆ ℂ` containing it.
-/
def inclSpectrum {A : H →L[ℂ] H} {Y : Set ℂ} (hsub : spectrum ℂ A ⊆ Y) :
    spectrum ℂ A → Y := fun lam => ⟨(lam : ℂ), hsub lam.2⟩

/--
**Spectral theorem for bounded normal operators.** A bounded normal operator on a nonzero
Hilbert space is the integral of the identity function against a unique projection-valued
measure on `σ(A)`.

Blueprint reference: `thrm:hall-10.20`.
-/
theorem existsUnique_spectralMeasure_normal [Nontrivial H] {A : H →L[ℂ] H}
    (hA : IsStarNormal A) :
    ∃! μ : ProjectionValuedMeasure (spectrum ℂ A) H,
      μ.integral (fun lam => (lam : ℂ)) = A := by
  sorry

/--
The ambient form of uniqueness: a projection-valued measure on a larger compact set `Y`
integrating to `A` assigns no mass off `σ(A)` and agrees with `μ^A` there.

Blueprint reference: `thrm:hall-10.20`.
-/
theorem eq_of_integral_id_eq_ambient [Nontrivial H] {A : H →L[ℂ] H} (hA : IsStarNormal A)
    {Y : Set ℂ} (hY : IsCompact Y) (hsub : spectrum ℂ A ⊆ Y)
    {μA : ProjectionValuedMeasure (spectrum ℂ A) H}
    (hμA : μA.integral (fun lam => (lam : ℂ)) = A)
    {ν : ProjectionValuedMeasure Y H} (hν : ν.integral (fun y => (y : ℂ)) = A)
    {E : Set Y} (hE : MeasurableSet E) :
    ν E = μA (inclSpectrum hsub ⁻¹' E) := by
  sorry

end Unbounded
end Spectral
end Physicslib4
