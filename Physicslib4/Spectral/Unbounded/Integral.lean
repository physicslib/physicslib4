/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.OperatorIntegral
import Physicslib4.Spectral.Unbounded.DirectSum

/-!
# Integration of an unbounded function against a projection-valued measure

`Physicslib4/Spectral/OperatorIntegral.lean` defines `μ.integral f : H →L[ℂ] H` for a
*bounded* measurable `f`. Here the integrand is allowed to be unbounded, so the resulting
operator `pmapIntegral μ f` is an unbounded operator — a `LinearPMap` — with domain

`W_f = {ψ | ∫ |f|² dμ_ψ < ∞}`,

which is `integralDomain μ f`, spelled with Mathlib's `MemLp f 2 (μ.assoc ψ)`.

Along the way we need quadratic and sesquilinear forms defined on a subspace `D ⊆ H`
rather than on all of `H`, since `W_f` (and, in the proof of `prpstn:hall-10.3`, a
spectral subspace) is not all of `H`. These mirror `Physicslib4/Spectral/Forms.lean`.

## Main definitions

* `IsSesquilinearFormOn`, `polarizationOn`, `IsQuadraticFormOn`,
  `IsBoundedQuadraticFormOn` — forms on a subspace.
* `integralDomain`, `integralForm` — `W_f` and `Q_f`.
* `pmapIntegral` — `∫ f dμ` as an unbounded operator.

## Main statements

* `assoc_univ_eq`, `norm_sq_integral_apply` — total mass of `μ_ψ` and the norm identity
  for the bounded integral.
* `dense_integralDomain`, `isQuadraticFormOn_integralForm`,
  `norm_polarizationOn_integralForm_le`, `existsUnique_repr_integralForm` — the blueprint's
  Proposition 10.2.
* `inner_pmapIntegral`, `inner_self_pmapIntegral`, `norm_sq_pmapIntegral`,
  `eq_pmapIntegral_of_inner_self` — the blueprint's Proposition 10.1.
* `pmapIntegral_of_bddMeasurable` — agreement with the bounded integral.
* `pmapIntegral_congr_of_null`, `tendsto_integral_truncation`, `assoc_integral_apply`,
  `mapsTo_pmapIntegral_range` — the further facts needed for the Cayley transform.
* `isSelfAdjoint_pmapIntegral_of_real` — the integral of a real-valued function is
  self-adjoint.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap ENNReal NNReal
open Filter Topology ContinuousLinearMap MeasureTheory

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### Quadratic and sesquilinear forms on a subspace
-/

section Forms

variable {D D' : Submodule ℂ H}

/--
A *sesquilinear form on a subspace* `D` of `H`: conjugate linear in the first slot, linear
in the second. Taking `D = ⊤` recovers `Physicslib4.Spectral.SesquilinearForm`.

Blueprint reference: `def:hall-sesquilinear-form-on-a-subspace`.
-/
abbrev SesquilinearFormOn (D : Submodule ℂ H) := D →ₗ⋆[ℂ] D →ₗ[ℂ] ℂ

/--
The polarization formula for a form defined on a subspace.

Blueprint reference: `def:hall-quadratic-form-on-a-subspace` (point 2).
-/
noncomputable def polarizationOn {D : Submodule ℂ H} (Q : D → ℂ) : D → D → ℂ := fun φ ψ =>
  (1 / 2 : ℂ) * (Q (φ + ψ) - Q φ - Q ψ) -
    (Complex.I / 2) * (Q (φ + Complex.I • ψ) - Q φ - Q (Complex.I • ψ))

/--
A *quadratic form on the subspace* `D`: `|λ|²`-homogeneous, with sesquilinear
polarization.

Blueprint reference: `def:hall-quadratic-form-on-a-subspace`.
-/
structure IsQuadraticFormOn {D : Submodule ℂ H} (Q : D → ℂ) : Prop where
  /-- `Q (λ • ψ) = |λ|² Q ψ`. -/
  smul : ∀ (l : ℂ) (ψ : D), Q (l • ψ) = (‖l‖ : ℂ) ^ 2 * Q ψ
  /-- The polarization of `Q` is a sesquilinear form on `D`. -/
  isSesquilinear : ∃ L : SesquilinearFormOn D, ∀ φ ψ : D, L φ ψ = polarizationOn Q φ ψ

/--
A *bounded* quadratic form on the subspace `D`.

Blueprint reference: `def:hall-quadratic-form-on-a-subspace` (final paragraph).
-/
structure IsBoundedQuadraticFormOn {D : Submodule ℂ H} (Q : D → ℂ) : Prop where
  /-- The underlying form is quadratic. -/
  isQuadratic : IsQuadraticFormOn Q
  /-- `|Q ψ| ≤ C ‖ψ‖²` for some real `C`. -/
  bounded : ∃ C : ℝ, ∀ ψ : D, ‖Q ψ‖ ≤ C * ‖(ψ : H)‖ ^ 2

/--
If a quadratic form on `D` is induced on the diagonal by a linear map `T : D → H`, then
its polarization is the off-diagonal form `(φ, ψ) ↦ ⟪φ, T ψ⟫`.

Blueprint reference: `prpstn:quadratic-forms-on-a-subspace-properties` (Part 1).
-/
theorem polarizationOn_eq_inner {Q : D → ℂ} (hQ : IsQuadraticFormOn Q) (T : D →ₗ[ℂ] H)
    (hT : ∀ ψ : D, Q ψ = ⟪(ψ : H), T ψ⟫_ℂ) (φ ψ : D) :
    polarizationOn Q φ ψ = ⟪(φ : H), T ψ⟫_ℂ := by
  sorry

/--
A real-valued quadratic form on `D` has conjugate-symmetric polarization.

Blueprint reference: `prpstn:quadratic-forms-on-a-subspace-properties` (Part 2).
-/
theorem polarizationOn_conj_symm {Q : D → ℂ} (hQ : IsQuadraticFormOn Q)
    (hreal : ∀ ψ : D, (Q ψ).im = 0) (φ ψ : D) :
    polarizationOn Q φ ψ = starRingEnd ℂ (polarizationOn Q ψ φ) := by
  sorry

/--
The restriction of a quadratic form to a smaller subspace is again a quadratic form.

Blueprint reference: `lmm:restriction-of-quadratic-form`.
-/
theorem isQuadraticFormOn_restrict (h : D' ≤ D) {Q : D → ℂ} (hQ : IsQuadraticFormOn Q) :
    IsQuadraticFormOn (fun ψ : D' => Q ⟨(ψ : H), h ψ.2⟩) := by
  sorry

/--
Its associated sesquilinear form is the restriction of the original one.

Blueprint reference: `lmm:restriction-of-quadratic-form`.
-/
theorem polarizationOn_restrict (h : D' ≤ D) {Q : D → ℂ} (φ ψ : D') :
    polarizationOn (fun ξ : D' => Q ⟨(ξ : H), h ξ.2⟩) φ ψ =
      polarizationOn Q ⟨(φ : H), h φ.2⟩ ⟨(ψ : H), h ψ.2⟩ := by
  sorry

end Forms

/-!
### Preliminaries on the associated measures
-/

variable (μ : ProjectionValuedMeasure X H)

/--
The associated measure `μ_ψ` has total mass `‖ψ‖²`; in particular it is finite.

Blueprint reference: `lmm:associated-measure-total-mass`.
-/
theorem assoc_univ_eq (ψ : H) : (μ.assoc ψ) Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  sorry

/--
Consequently `μ_ψ(E) ≤ ‖ψ‖²` for every `E`.

Blueprint reference: `lmm:associated-measure-total-mass`.
-/
theorem assoc_le_norm_sq (ψ : H) (E : Set X) :
    (μ.assoc ψ) E ≤ ENNReal.ofReal (‖ψ‖ ^ 2) := by
  sorry

/--
The norm identity for the bounded integral:
`‖(∫ f dμ) ψ‖² = ∫ |f|² dμ_ψ` for bounded measurable `f`.

Blueprint reference: `lmm:norm-identity-bounded-integral`.
-/
theorem norm_sq_integral_apply {f : X → ℂ} (hf : f ∈ BddMeasurable X) (ψ : H) :
    ‖μ.integral f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(μ.assoc ψ) := by
  sorry

/--
If `η` lies in the range of the projection `μ E`, then `μ_η` is concentrated on `E`.

Blueprint reference: `lmm:range-membership-concentrates-measure`.
-/
theorem assoc_compl_eq_zero {E : Set X} (hE : MeasurableSet E) {η : H}
    (hη : η ∈ Set.range (μ E)) : (μ.assoc η) Eᶜ = 0 := by
  sorry

/--
Hence integrals against `μ_η` may be computed over `E` alone.

Blueprint reference: `lmm:range-membership-concentrates-measure`.
-/
theorem lintegral_assoc_eq_setLIntegral {E : Set X} (hE : MeasurableSet E) {η : H}
    (hη : η ∈ Set.range (μ E)) (g : X → ℝ≥0∞) :
    ∫⁻ x, g x ∂(μ.assoc η) = ∫⁻ x in E, g x ∂(μ.assoc η) := by
  sorry

/--
Over a countable measurable partition of `X`, every vector is the norm-convergent sum of
its pieces.

Blueprint reference: `lmm:norm-convergent-decomposition` (Part 1).
-/
theorem hasSum_apply_of_partition (F : ℕ → Set X) (hF : ∀ n, MeasurableSet (F n))
    (hdisj : Pairwise fun i j => Disjoint (F i) (F j)) (hcover : (⋃ n, F n) = Set.univ)
    (ψ : H) : HasSum (fun n => μ (F n) ψ) ψ := by
  sorry

/--
The `N`-th partial sum of that series is `μ (⋃_{n<N} Fₙ) ψ`.

Blueprint reference: `lmm:norm-convergent-decomposition` (Part 2).
-/
theorem apply_biUnion_eq_sum (F : ℕ → Set X) (hF : ∀ n, MeasurableSet (F n))
    (hdisj : Pairwise fun i j => Disjoint (F i) (F j)) (N : ℕ) (ψ : H) :
    μ (⋃ n ∈ Finset.range N, F n) ψ = ∑ n ∈ Finset.range N, μ (F n) ψ := by
  sorry

/-!
### Projections: range, kernel, closedness
-/

/--
The range of an orthogonal projection is the kernel of `1 - P`.

Blueprint reference: `lmm:range-of-projection-is-kernel`.
-/
theorem range_eq_ker_one_sub {P : H →L[ℂ] H} (hP : IsStarProjection P) :
    LinearMap.range (P : H →ₗ[ℂ] H) = LinearMap.ker ((1 - P : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  sorry

/--
A vector lies in the range of an orthogonal projection exactly when it is fixed by it.

Blueprint reference: `lmm:range-of-projection-is-kernel`.
-/
theorem mem_range_iff_apply_eq {P : H →L[ℂ] H} (hP : IsStarProjection P) (η : H) :
    η ∈ Set.range P ↔ P η = η := by
  sorry

/--
The range of an orthogonal projection is closed.

Blueprint reference: `lmm:range-of-projection-is-kernel`.
-/
theorem isClosed_range_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) :
    IsClosed (Set.range P) := by
  sorry

/-!
### Measure-theoretic facts not already in Mathlib
-/

/--
Two measures agreeing on all measurable subsets of `E` give the same integral over `E`.

Blueprint reference: `prpstn:integrals-agree-when-measures-agree`.
-/
theorem setLIntegral_congr_measure {ν ν' : Measure X} {E : Set X} (hE : MeasurableSet E)
    (h : ∀ S, MeasurableSet S → S ⊆ E → ν S = ν' S) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in E, g x ∂ν = ∫⁻ x in E, g x ∂ν' := by
  sorry

/-!
### The unbounded integral
-/

/--
The domain `W_f = {ψ | ∫ |f|² dμ_ψ < ∞}` of the integral of a possibly unbounded
measurable `f`.

Blueprint reference: `prpstn:hall-10.2`.
-/
def integralDomain (f : X → ℂ) : Submodule ℂ H where
  carrier := {ψ : H | MemLp f 2 (μ.assoc ψ)}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

@[simp]
theorem mem_integralDomain {f : X → ℂ} {ψ : H} :
    ψ ∈ integralDomain μ f ↔ MemLp f 2 (μ.assoc ψ) := Iff.rfl

/--
The quadratic form `Q_f (ψ) = ∫ f dμ_ψ` on `W_f`.

Blueprint reference: `prpstn:hall-10.2` (Part 1).
-/
noncomputable def integralForm (f : X → ℂ) (ψ : integralDomain μ f) : ℂ :=
  ∫ x, f x ∂(μ.assoc (ψ : H))

/--
`W_f` is dense in `H`.

Blueprint reference: `prpstn:hall-10.2` (Part 1).
-/
theorem dense_integralDomain {f : X → ℂ} (hf : Measurable f) :
    Dense ((integralDomain μ f : Submodule ℂ H) : Set H) := by
  sorry

/--
`Q_f` is a quadratic form on `W_f`.

Blueprint reference: `prpstn:hall-10.2` (Part 1).
-/
theorem isQuadraticFormOn_integralForm {f : X → ℂ} (hf : Measurable f) :
    IsQuadraticFormOn (integralForm μ f) := by
  sorry

/--
The associated sesquilinear form `L_f` obeys `|L_f(φ, ψ)| ≤ ‖φ‖ ‖f‖_{L²(μ_ψ)}`.

Blueprint reference: `prpstn:hall-10.2` (Part 2).
-/
theorem norm_polarizationOn_integralForm_le {f : X → ℂ} (hf : Measurable f)
    (φ ψ : integralDomain μ f) :
    ‖polarizationOn (integralForm μ f) φ ψ‖ ≤
      ‖(φ : H)‖ * Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(μ.assoc (ψ : H))) := by
  sorry

/--
For each `ψ ∈ W_f` there is a unique `χ ∈ H` representing `φ ↦ L_f(φ, ψ)`.

Blueprint reference: `prpstn:hall-10.2` (Part 3).
-/
theorem existsUnique_repr_integralForm {f : X → ℂ} (hf : Measurable f)
    (ψ : integralDomain μ f) :
    ∃! χ : H, ∀ φ : integralDomain μ f,
      polarizationOn (integralForm μ f) φ ψ = ⟪(φ : H), χ⟫_ℂ := by
  sorry

open Classical in
/--
The vector representing `φ ↦ L_f(φ, ψ)`, extended by `0` when no such vector exists.
-/
noncomputable def integralApply (f : X → ℂ) (ψ : integralDomain μ f) : H :=
  if h : ∃! χ : H, ∀ φ : integralDomain μ f,
      polarizationOn (integralForm μ f) φ ψ = ⟪(φ : H), χ⟫_ℂ then h.choose else 0

/--
The integral `∫ f dμ` of a possibly unbounded measurable `f`, as an unbounded operator
with domain `W_f`.

Blueprint reference: `prpstn:hall-10.1`.
-/
noncomputable def pmapIntegral (f : X → ℂ) : H →ₗ.[ℂ] H where
  domain := integralDomain μ f
  toFun :=
    { toFun := integralApply μ f
      map_add' := by sorry
      map_smul' := by sorry }

@[simp]
theorem pmapIntegral_domain (f : X → ℂ) :
    (pmapIntegral μ f).domain = integralDomain μ f := rfl

/--
The defining off-diagonal identity `⟪φ, (∫ f dμ) ψ⟫ = L_f(φ, ψ)`.

Blueprint reference: `prpstn:hall-10.1`.
-/
theorem inner_pmapIntegral {f : X → ℂ} (hf : Measurable f) (φ ψ : integralDomain μ f) :
    ⟪(φ : H), pmapIntegral μ f ψ⟫_ℂ = polarizationOn (integralForm μ f) φ ψ := by
  sorry

/--
The diagonal identity `⟪ψ, (∫ f dμ) ψ⟫ = ∫ f dμ_ψ`.

Blueprint reference: `prpstn:hall-10.1`.
-/
theorem inner_self_pmapIntegral {f : X → ℂ} (hf : Measurable f) (ψ : integralDomain μ f) :
    ⟪(ψ : H), pmapIntegral μ f ψ⟫_ℂ = ∫ x, f x ∂(μ.assoc (ψ : H)) := by
  sorry

/--
The norm formula `‖(∫ f dμ) ψ‖² = ∫ |f|² dμ_ψ`.

Blueprint reference: `prpstn:hall-10.1`.
-/
theorem norm_sq_pmapIntegral {f : X → ℂ} (hf : Measurable f) (ψ : integralDomain μ f) :
    ‖pmapIntegral μ f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(μ.assoc (ψ : H)) := by
  sorry

/--
Strengthened uniqueness: any unbounded operator with domain `W_f` satisfying merely the
diagonal identity equals `∫ f dμ`.

Blueprint reference: `prpstn:hall-10.1`.
-/
theorem eq_pmapIntegral_of_inner_self {f : X → ℂ} (hf : Measurable f) (A : H →ₗ.[ℂ] H)
    (hdom : A.domain = integralDomain μ f)
    (h : ∀ ψ : A.domain, ⟪(ψ : H), A ψ⟫_ℂ = ∫ x, f x ∂(μ.assoc (ψ : H))) :
    A = pmapIntegral μ f := by
  sorry

/--
For bounded measurable `f`, `W_f = H` and the unbounded integral is the bounded one.

Blueprint reference: `prpstn:coincidence-with-the-bounded-integral`.
-/
theorem pmapIntegral_of_bddMeasurable {f : X → ℂ} (hf : f ∈ BddMeasurable X) :
    integralDomain μ f = ⊤ ∧
      pmapIntegral μ f = ((μ.integral f : H →ₗ[ℂ] H).toPMap ⊤) := by
  sorry

/--
If `f` and `g` agree off a set annihilated by `μ`, they have the same domain and the same
integral.

Blueprint reference: `lmm:integral-ignores-null-sets`.
-/
theorem pmapIntegral_congr_of_null {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    {N : Set X} (hN : MeasurableSet N) (hμN : μ N = 0) (hfg : ∀ x ∉ N, f x = g x) :
    integralDomain μ f = integralDomain μ g ∧ pmapIntegral μ f = pmapIntegral μ g := by
  sorry

/--
If `|f| ≤ c` on `E`, then the range of `μ E` lies in `W_f`.

Blueprint reference: `lmm:bounded-on-set-range-in-domain`.
-/
theorem range_subset_integralDomain {f : X → ℂ} (hf : Measurable f) {E : Set X}
    (hE : MeasurableSet E) {c : ℝ} (hc : ∀ x ∈ E, ‖f x‖ ≤ c) :
    Set.range (μ E) ⊆ ((integralDomain μ f : Submodule ℂ H) : Set H) := by
  sorry

/--
The quantitative half of `lmm:bounded-on-set-range-in-domain`.

Blueprint reference: `lmm:bounded-on-set-range-in-domain`.
-/
theorem integral_norm_sq_le_of_mem_range {f : X → ℂ} (hf : Measurable f) {E : Set X}
    (hE : MeasurableSet E) {c : ℝ} (hc : ∀ x ∈ E, ‖f x‖ ≤ c) {η : H}
    (hη : η ∈ Set.range (μ E)) :
    ∫ x, ‖f x‖ ^ 2 ∂(μ.assoc η) ≤ c ^ 2 * ‖η‖ ^ 2 := by
  sorry

/--
The bounded truncations `f · 1_{|f| < n}` converge to `∫ f dμ` pointwise in `H`.

Blueprint reference: `lmm:truncations-converge`.
-/
theorem tendsto_integral_truncation {f : X → ℂ} (hf : Measurable f)
    (ψ : integralDomain μ f) :
    Tendsto (fun n : ℕ => μ.integral ({x | ‖f x‖ < n}.indicator f) (ψ : H)) atTop
      (𝓝 (pmapIntegral μ f ψ)) := by
  sorry

/--
For bounded measurable `h` and `T = ∫ h dμ`, the associated measure of `T ψ` has density
`|h|²` with respect to `μ_ψ`.

Blueprint reference: `lmm:associated-measure-of-image`.
-/
theorem assoc_integral_apply {h : X → ℂ} (hh : h ∈ BddMeasurable X) (ψ : H) {E : Set X}
    (hE : MeasurableSet E) :
    (μ.assoc (μ.integral h ψ)) E = ∫⁻ x in E, (‖h x‖₊ : ℝ≥0∞) ^ 2 ∂(μ.assoc ψ) := by
  sorry

/--
Consequently integrals against `μ_{Tψ}` are integrals against `μ_ψ` weighted by `|h|²`.

Blueprint reference: `lmm:associated-measure-of-image`.
-/
theorem lintegral_assoc_integral_apply {h : X → ℂ} (hh : h ∈ BddMeasurable X) (ψ : H)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(μ.assoc (μ.integral h ψ)) =
      ∫⁻ x, g x * (‖h x‖₊ : ℝ≥0∞) ^ 2 ∂(μ.assoc ψ) := by
  sorry

/--
If `f` is bounded on `E`, then `∫ f dμ` preserves the spectral subspace
`V_E = Range(μ E)` (which lies in `W_f` by `range_subset_integralDomain`).

Blueprint reference: `lmm:integral-preserves-spectral-subspaces`.
-/
theorem mapsTo_pmapIntegral_range {f : X → ℂ} (hf : Measurable f) {E : Set X}
    (hE : MeasurableSet E) {c : ℝ} (hc : ∀ x ∈ E, ‖f x‖ ≤ c)
    (ψ : integralDomain μ f) (hψ : (ψ : H) ∈ Set.range (μ E)) :
    pmapIntegral μ f ψ ∈ Set.range (μ E) := by
  sorry

/--
The integral of a real-valued measurable function is a self-adjoint unbounded operator on
`W_f`.

Blueprint reference: `prpstn:hall-10.3`.
-/
theorem isSelfAdjoint_pmapIntegral_of_real {f : X → ℂ} (hf : Measurable f)
    (hreal : ∀ x, (f x).im = 0) : IsSelfAdjoint (pmapIntegral μ f) := by
  sorry

end Unbounded
end Spectral
end Physicslib4
