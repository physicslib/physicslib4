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
* `integralDomain_eq_top_of_bddMeasurable`, `pmapIntegral_of_bddMeasurable` — agreement
  with the bounded integral.
* `integralDomain_congr_of_null`, `pmapIntegral_congr_of_null`,
  `tendsto_integral_truncation`, `assoc_integral_apply`,
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

omit [CompleteSpace H] in
/--
If a quadratic form on `D` is induced on the diagonal by a linear map `T : D → H`, then
its polarization is the off-diagonal form `(φ, ψ) ↦ ⟪φ, T ψ⟫`.

Blueprint reference: `prpstn:quadratic-forms-on-a-subspace-properties` (Part 1).
-/
theorem polarizationOn_eq_inner {Q : D → ℂ} (T : D →ₗ[ℂ] H)
    (hT : ∀ ψ : D, Q ψ = ⟪(ψ : H), T ψ⟫_ℂ) (φ ψ : D) :
    polarizationOn Q φ ψ = ⟪(φ : H), T ψ⟫_ℂ := by
  simp only [polarizationOn, hT, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

omit [CompleteSpace H] in
/--
A real-valued quadratic form on `D` has conjugate-symmetric polarization.

Blueprint reference: `prpstn:quadratic-forms-on-a-subspace-properties` (Part 2).
-/
theorem polarizationOn_conj_symm {Q : D → ℂ} (hQ : IsQuadraticFormOn Q)
    (hreal : ∀ ψ : D, (Q ψ).im = 0) (φ ψ : D) :
    polarizationOn Q φ ψ = starRingEnd ℂ (polarizationOn Q ψ φ) := by
  obtain ⟨L, hL⟩ := hQ.isSesquilinear
  have hdiag : ∀ a : D, L a a = Q a := by
    intro a
    rw [hL, polarizationOn]
    have h2 : a + a = (2 : ℂ) • a := by rw [two_smul]
    have h1i : a + Complex.I • a = ((1 : ℂ) + Complex.I) • a := by rw [add_smul, one_smul]
    have hn : (‖((1 : ℂ) + Complex.I)‖ : ℂ) ^ 2 = 2 := by
      have : ‖((1 : ℂ) + Complex.I)‖ ^ 2 = (2 : ℝ) := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; norm_num
      exact_mod_cast this
    rw [h2, h1i, hQ.smul, hQ.smul, hQ.smul, hn]
    simp
    ring
  have hreal' : ∀ a : D, (L a a).im = 0 := fun a => (hdiag a) ▸ hreal a
  have e1 := hreal' (φ + ψ)
  have e2 := hreal' (φ + Complex.I • ψ)
  have e3 := hreal' φ
  have e4 := hreal' ψ
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, RingHom.id_apply,
    Complex.conj_I, smul_eq_mul, Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.add_re,
    Complex.mul_re, Complex.neg_im, Complex.I_re, Complex.I_im, e3, e4] at e1 e2
  rw [← hL, ← hL]
  apply Complex.ext <;> simp <;> nlinarith [e1, e2]

omit [CompleteSpace H] in
/--
The restriction of a quadratic form to a smaller subspace is again a quadratic form.

Blueprint reference: `lmm:restriction-of-quadratic-form`.
-/
theorem isQuadraticFormOn_restrict (h : D' ≤ D) {Q : D → ℂ} (hQ : IsQuadraticFormOn Q) :
    IsQuadraticFormOn (fun ψ : D' => Q ⟨(ψ : H), h ψ.2⟩) := by
  obtain ⟨L, hL⟩ := hQ.isSesquilinear
  refine ⟨fun l ψ => hQ.smul l ⟨(ψ : H), h ψ.2⟩, ?_⟩
  refine ⟨(L.compl₂ (Submodule.inclusion h)).comp (Submodule.inclusion h), fun φ ψ => ?_⟩
  exact hL _ _

omit [CompleteSpace H] in
/--
Its associated sesquilinear form is the restriction of the original one.

Blueprint reference: `lmm:restriction-of-quadratic-form`.
-/
theorem polarizationOn_restrict (h : D' ≤ D) {Q : D → ℂ} (φ ψ : D') :
    polarizationOn (fun ξ : D' => Q ⟨(ξ : H), h ξ.2⟩) φ ψ =
      polarizationOn Q ⟨(φ : H), h φ.2⟩ ⟨(ψ : H), h ψ.2⟩ :=
  rfl

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
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), μ.assoc_apply ψ MeasurableSet.univ,
    μ.apply_univ, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

/--
Consequently `μ_ψ(E) ≤ ‖ψ‖²` for every `E`.

Blueprint reference: `lmm:associated-measure-total-mass`.
-/
theorem assoc_le_norm_sq (ψ : H) (E : Set X) :
    (μ.assoc ψ) E ≤ ENNReal.ofReal (‖ψ‖ ^ 2) :=
  assoc_univ_eq μ ψ ▸ measure_mono (Set.subset_univ E)

omit [CompleteSpace H] in
/-- Bounded measurable functions are closed under products. -/
private lemma mul_mem_bddMeasurable {u v : X → ℂ} (hu : u ∈ BddMeasurable X)
    (hv : v ∈ BddMeasurable X) : u * v ∈ BddMeasurable X :=
  let ⟨hu, Cu, hCu⟩ := hu
  let ⟨hv, Cv, hCv⟩ := hv
  ⟨hu.mul hv, Cu * Cv, fun x => by
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hCu x) (hCv x) (norm_nonneg _) ((norm_nonneg _).trans (hCu x))⟩

omit [CompleteSpace H] in
/-- Bounded measurable functions are closed under complex conjugation. -/
private lemma conj_mem_bddMeasurable {u : X → ℂ} (hu : u ∈ BddMeasurable X) :
    (fun x => (starRingEnd ℂ) (u x)) ∈ BddMeasurable X :=
  ⟨Complex.continuous_conj.measurable.comp hu.1, hu.2.choose, fun x => by
    simpa using hu.2.choose_spec x⟩

omit [CompleteSpace H] in
/-- The indicator function of a measurable set is bounded and measurable. -/
private lemma indicator_one_mem_bddMeasurable {E : Set X} (hE : MeasurableSet E) :
    E.indicator (1 : X → ℂ) ∈ BddMeasurable X :=
  ⟨measurable_const.indicator hE, 1, fun x => by by_cases hx : x ∈ E <;> simp [hx]⟩

/--
The norm identity for the bounded integral:
`‖(∫ f dμ) ψ‖² = ∫ |f|² dμ_ψ` for bounded measurable `f`.

Blueprint reference: `lmm:norm-identity-bounded-integral`.
-/
theorem norm_sq_integral_apply {f : X → ℂ} (hf : f ∈ BddMeasurable X) (ψ : H) :
    ‖μ.integral f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(μ.assoc ψ) := by
  have hfc := conj_mem_bddMeasurable hf
  have key : ⟪μ.integral f ψ, μ.integral f ψ⟫_ℂ =
      ((∫ x, ‖f x‖ ^ 2 ∂(μ.assoc ψ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.mul_def, ← μ.integral_conj hf, ← μ.integral_mul hfc hf,
      μ.inner_integral (mul_mem_bddMeasurable hfc hf)]
    exact integral_congr_ae (ae_of_all _ fun x => by simp [Complex.conj_mul'])
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), key]
  rfl

/--
If `η` lies in the range of the projection `μ E`, then `μ_η` is concentrated on `E`.

Blueprint reference: `lmm:range-membership-concentrates-measure`.
-/
theorem assoc_compl_eq_zero {E : Set X} (hE : MeasurableSet E) {η : H}
    (hη : η ∈ Set.range (μ E)) : (μ.assoc η) Eᶜ = 0 := by
  obtain ⟨x, rfl⟩ := hη
  have hempty : μ (∅ : Set X) = 0 := by
    ext v
    exact (summable_const_iff (a := μ (∅ : Set X) v)).mp
      (μ.hasSum_apply (fun _ : ℕ => (∅ : Set X)) (fun _ => MeasurableSet.empty)
        (by intro k e; simp) v).summable
  have hzero : μ Eᶜ (μ E x) = 0 := by
    change (μ Eᶜ * μ E) x = 0
    rw [← μ.apply_inter hE.compl hE, Set.compl_inter_self, hempty, zero_apply]
  have h := μ.assoc_apply (μ E x) hE.compl
  rw [hzero, inner_zero_right, Complex.zero_re, ENNReal.toReal_eq_zero_iff] at h
  exact h.resolve_right (measure_ne_top _ _)

/--
Hence integrals against `μ_η` may be computed over `E` alone.

Blueprint reference: `lmm:range-membership-concentrates-measure`.
-/
theorem lintegral_assoc_eq_setLIntegral {E : Set X} (hE : MeasurableSet E) {η : H}
    (hη : η ∈ Set.range (μ E)) (g : X → ℝ≥0∞) :
    ∫⁻ x, g x ∂(μ.assoc η) = ∫⁻ x in E, g x ∂(μ.assoc η) := by
  rw [Measure.restrict_eq_self_of_ae_mem]
  exact (ae_iff (p := fun x => x ∈ E)).mpr (assoc_compl_eq_zero μ hE hη)

/--
Over a countable measurable partition of `X`, every vector is the norm-convergent sum of
its pieces.

Blueprint reference: `lmm:norm-convergent-decomposition` (Part 1).
-/
theorem hasSum_apply_of_partition (F : ℕ → Set X) (hF : ∀ n, MeasurableSet (F n))
    (hdisj : Pairwise fun i j => Disjoint (F i) (F j)) (hcover : (⋃ n, F n) = Set.univ)
    (ψ : H) : HasSum (fun n => μ (F n) ψ) ψ := by
  simpa [hcover, μ.apply_univ] using μ.hasSum_apply F hF hdisj ψ

/--
The `N`-th partial sum of that series is `μ (⋃_{n<N} Fₙ) ψ`.

Blueprint reference: `lmm:norm-convergent-decomposition` (Part 2).
-/
theorem apply_biUnion_eq_sum (F : ℕ → Set X) (hF : ∀ n, MeasurableSet (F n))
    (hdisj : Pairwise fun i j => Disjoint (F i) (F j)) (N : ℕ) (ψ : H) :
    μ (⋃ n ∈ Finset.range N, F n) ψ = ∑ n ∈ Finset.range N, μ (F n) ψ := by
  have hempty : μ (∅ : Set X) ψ = 0 :=
    (summable_const_iff _).mp (μ.hasSum_apply (fun _ : ℕ => (∅ : Set X))
      (fun _ => MeasurableSet.empty) (fun _ _ _ => by simp) ψ).summable
  let E : ℕ → Set X := fun n => if n < N then F n else ∅
  have hE : ∀ n, MeasurableSet (E n) := fun n => by
    by_cases h : n < N <;> simp [E, h, hF n]
  have hEdisj : Pairwise fun i j => Disjoint (E i) (E j) := fun i j hij => by
    by_cases hi : i < N <;> by_cases hj : j < N <;> simp [E, hi, hj, hdisj hij]
  have hU : (⋃ n, E n) = ⋃ n ∈ Finset.range N, F n := by
    ext x; simp [E]
  have hs := μ.hasSum_apply E hE hEdisj ψ
  rw [hU] at hs
  refine hs.unique (hasSum_sum_of_ne_finset_zero fun n hn => ?_) |>.trans
    (Finset.sum_congr rfl fun n hn => ?_)
  · simp only [Finset.mem_range, not_lt] at hn
    simp [E, not_lt.mpr hn, hempty]
  · simp [E, Finset.mem_range.mp hn]

/-!
### Projections: range, kernel, closedness
-/

/--
The range of an orthogonal projection is the kernel of `1 - P`.

Blueprint reference: `lmm:range-of-projection-is-kernel`.
-/
theorem range_eq_ker_one_sub {P : H →L[ℂ] H} (hP : IsStarProjection P) :
    LinearMap.range (P : H →ₗ[ℂ] H) = LinearMap.ker ((1 - P : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  ext η
  have hPP : ∀ x, P (P x) = P x := fun x => by
    simpa using congrArg (fun T : H →L[ℂ] H => T x) hP.isIdempotentElem.eq
  simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, one_apply_eq_self, sub_eq_zero]
  exact ⟨fun ⟨x, hx⟩ => hx ▸ (hPP x).symm, fun h => ⟨η, h.symm⟩⟩

/--
A vector lies in the range of an orthogonal projection exactly when it is fixed by it.

Blueprint reference: `lmm:range-of-projection-is-kernel`.
-/
theorem mem_range_iff_apply_eq {P : H →L[ℂ] H} (hP : IsStarProjection P) (η : H) :
    η ∈ Set.range P ↔ P η = η := by
  have hPP : ∀ x, P (P x) = P x := fun x => by
    simpa using congrArg (fun T : H →L[ℂ] H => T x) hP.isIdempotentElem.eq
  exact ⟨fun ⟨x, hx⟩ => hx ▸ hPP x, fun h => ⟨η, h⟩⟩

/--
The range of an orthogonal projection is closed.

Blueprint reference: `lmm:range-of-projection-is-kernel`.
-/
theorem isClosed_range_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) :
    IsClosed (Set.range P) := by
  rw [show Set.range P = {η | P η = η} from Set.ext (mem_range_iff_apply_eq hP)]
  exact isClosed_eq P.continuous continuous_id

/--
A closed subspace of a separable Hilbert space is again a separable Hilbert space: it is
complete, and separable. The separability hypothesis on `H` is the blueprint's standing
assumption; the rest of this file does not need it.

Blueprint reference: `lmm:closed-subspace-is-hilbert`.
-/
theorem completeSpace_and_separableSpace_of_isClosed [TopologicalSpace.SeparableSpace H]
    {K : Submodule ℂ H} (hK : IsClosed (K : Set H)) :
    CompleteSpace K ∧ TopologicalSpace.SeparableSpace K :=
  ⟨hK.completeSpace_coe,
    (TopologicalSpace.IsSeparable.of_separableSpace (K : Set H)).separableSpace⟩

/-!
### Measure-theoretic facts not already in Mathlib
-/

/--
Two measures agreeing on all measurable subsets of `E` give the same integral over `E`.

Blueprint reference: `prpstn:integrals-agree-when-measures-agree`.
-/
theorem setLIntegral_congr_measure {ν ν' : Measure X} {E : Set X} (hE : MeasurableSet E)
    (h : ∀ S, MeasurableSet S → S ⊆ E → ν S = ν' S) (g : X → ℝ≥0∞) :
    ∫⁻ x in E, g x ∂ν = ∫⁻ x in E, g x ∂ν' := by
  congr 1
  ext S hS
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
  exact h _ (hS.inter hE) Set.inter_subset_right

/-!
### The unbounded integral
-/

/-- On a measurable set `E`, the associated measure is `μ_ψ(E) = ‖μ(E) ψ‖²`. -/
theorem assoc_apply_eq_norm_sq (ψ : H) {E : Set X} (hE : MeasurableSet E) :
    (μ.assoc ψ) E = ENNReal.ofReal (‖μ E ψ‖ ^ 2) := by
  have hP := μ.isStarProjection_apply E
  have hadj : (μ E).adjoint = μ E := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hP.isSelfAdjoint
  have hPP : μ E (μ E ψ) = μ E ψ := by
    simpa using congrArg (fun T : H →L[ℂ] H => T ψ) hP.isIdempotentElem.eq
  have key : ⟪ψ, μ E ψ⟫_ℂ = ⟪μ E ψ, μ E ψ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hadj, hPP]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), μ.assoc_apply ψ hE, key]
  exact congrArg ENNReal.ofReal (inner_self_eq_norm_sq (𝕜 := ℂ) _)

/-- The associated measure of a sum: `μ_{φ+ψ} ≤ 2 (μ_φ + μ_ψ)`. -/
theorem assoc_add_le (φ ψ : H) :
    μ.assoc (φ + ψ) ≤ (2 : ℝ≥0∞) • (μ.assoc φ + μ.assoc ψ) := by
  rw [Measure.le_iff]
  intro E hE
  rw [Measure.smul_apply, Measure.add_apply, assoc_apply_eq_norm_sq μ _ hE,
    assoc_apply_eq_norm_sq μ _ hE, assoc_apply_eq_norm_sq μ _ hE, map_add, smul_eq_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (μ E φ) (μ E ψ)) 2
  norm_num
  nlinarith [sq_nonneg (‖μ E φ‖ - ‖μ E ψ‖)]

/-- The associated measure of a multiple: `μ_{cψ} = |c|² μ_ψ`. -/
theorem assoc_smul (c : ℂ) (ψ : H) :
    μ.assoc (c • ψ) = ENNReal.ofReal (‖c‖ ^ 2) • μ.assoc ψ := by
  ext E hE
  rw [Measure.smul_apply, assoc_apply_eq_norm_sq μ _ hE, assoc_apply_eq_norm_sq μ _ hE,
    map_smul, norm_smul, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity), mul_pow]

/-- The associated measure of the zero vector is zero. -/
theorem assoc_zero : μ.assoc (0 : H) = 0 := by
  ext E hE
  simp [assoc_apply_eq_norm_sq μ _ hE]

/--
The domain `W_f = {ψ | ∫ |f|² dμ_ψ < ∞}` of the integral of a possibly unbounded
measurable `f`.

Blueprint reference: `prpstn:hall-10.2`.
-/
def integralDomain (f : X → ℂ) : Submodule ℂ H where
  carrier := {ψ : H | MemLp f 2 (μ.assoc ψ)}
  add_mem' := by
    intro φ ψ hφ hψ
    simp only [Set.mem_setOf_eq] at *
    have hsum : MemLp f 2 (μ.assoc φ + μ.assoc ψ) := by
      refine ⟨hφ.1.add_measure hψ.1, ?_⟩
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top,
        lintegral_add_measure]
      exact ENNReal.add_lt_top.2
        ⟨lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hφ.2,
          lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hψ.2⟩
    exact hsum.of_measure_le_smul (by norm_num) (assoc_add_le μ φ ψ)
  zero_mem' := by simp [assoc_zero]
  smul_mem' := by
    intro c ψ hψ
    simp only [Set.mem_setOf_eq] at *
    rw [assoc_smul]
    exact hψ.smul_measure ENNReal.ofReal_ne_top

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
  set F : ℕ → Set X := fun n => {x | ‖f x‖ < n}
  have hFm : ∀ n, MeasurableSet (F n) := fun n => measurableSet_lt hf.norm measurable_const
  have hFmono : Monotone F := fun m n hmn x hx => by
    simp only [F, Set.mem_setOf_eq] at hx ⊢
    exact hx.trans_le (by exact_mod_cast hmn)
  have hFU : (⋃ n, F n) = Set.univ := by
    ext x
    simp only [F, Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_nat_gt _
  -- `μ(Fₙ) ψ ∈ W_f`: its associated measure is `μ_ψ` restricted to `Fₙ`, where `|f| < n`.
  have hmem : ∀ n ψ, μ (F n) ψ ∈ integralDomain μ f := by
    intro n ψ
    have hres : μ.assoc (μ (F n) ψ) = (μ.assoc ψ).restrict (F n) := by
      ext E hE
      rw [Measure.restrict_apply hE, assoc_apply_eq_norm_sq μ _ hE,
        assoc_apply_eq_norm_sq μ _ (hE.inter (hFm n)), μ.apply_inter hE (hFm n),
        mul_apply_eq_comp]
    rw [mem_integralDomain, hres]
    exact MemLp.of_bound hf.aestronglyMeasurable.restrict (n : ℝ)
      ((ae_restrict_iff' (hFm n)).2 (Eventually.of_forall fun x hx => le_of_lt hx))
  intro ψ
  -- `‖ψ - μ(Fₙ) ψ‖² = μ_ψ(X) - μ_ψ(Fₙ)`.
  have hnorm : ∀ n, ‖μ (F n) ψ - ψ‖ =
      Real.sqrt (((μ.assoc ψ) Set.univ).toReal - ((μ.assoc ψ) (F n)).toReal) := by
    intro n
    have hP := μ.isStarProjection_apply (F n)
    have hadj : (μ (F n)).adjoint = μ (F n) := by
      rw [← ContinuousLinearMap.star_eq_adjoint]; exact hP.isSelfAdjoint
    have hPP : μ (F n) (μ (F n) ψ) = μ (F n) ψ := by
      simpa using congrArg (fun T : H →L[ℂ] H => T ψ) hP.isIdempotentElem.eq
    have horth : ⟪μ (F n) ψ, ψ - μ (F n) ψ⟫_ℂ = 0 := by
      rw [← hadj, ContinuousLinearMap.adjoint_inner_left, hadj, map_sub, hPP, sub_self,
        inner_zero_right]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    rw [add_sub_cancel] at hpy
    rw [assoc_apply_eq_norm_sq μ _ MeasurableSet.univ, assoc_apply_eq_norm_sq μ _ (hFm n),
      μ.apply_univ, one_apply_eq_self, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity), norm_sub_rev]
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by nlinarith) (norm_nonneg _)]
    rw [sq, sq] at *
    linarith
  have htend : Tendsto (fun n => μ (F n) ψ) atTop (𝓝 ψ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp_rw [hnorm]
    have hm : Tendsto (fun n => ((μ.assoc ψ) (F n)).toReal) atTop
        (𝓝 ((μ.assoc ψ) Set.univ).toReal) := by
      have := tendsto_measure_iUnion_atTop (μ := μ.assoc ψ) hFmono
      rw [hFU] at this
      exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
    have := ((tendsto_const_nhds (x := ((μ.assoc ψ) Set.univ).toReal)).sub hm).sqrt
    simpa using this
  exact mem_closure_of_tendsto htend (Eventually.of_forall fun n => hmem n ψ)

/-- The truncation `f · 1_{|f| < n}` of a measurable `f` is bounded and measurable. -/
theorem indicator_lt_mem_bddMeasurable {f : X → ℂ} (hf : Measurable f) (n : ℕ) :
    {x | ‖f x‖ < n}.indicator f ∈ BddMeasurable X :=
  ⟨hf.indicator (measurableSet_lt hf.norm measurable_const), n, fun x => by
    by_cases hx : x ∈ {x | ‖f x‖ < n}
    · rw [Set.indicator_of_mem hx]; exact le_of_lt hx
    · rw [Set.indicator_of_notMem hx, norm_zero]; positivity⟩

omit [CompleteSpace H] in
/-- For integrable `g`, the integrals of `g` over the sublevel sets `{|f| < n}` of a
measurable `f` converge to `∫ g` (dominated convergence). -/
private lemma tendsto_integral_indicator_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → ℂ} (hf : Measurable f) {ν : Measure X} {g : X → E}
    (hg : Integrable g ν) :
    Tendsto (fun n : ℕ => ∫ x, {x | ‖f x‖ < n}.indicator g x ∂ν) atTop (𝓝 (∫ x, g x ∂ν)) :=
  tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    (fun n => (hg.indicator (measurableSet_lt hf.norm measurable_const)).1) hg.norm
    (fun n => ae_of_all _ fun x => norm_indicator_le_norm_self g x)
    (ae_of_all _ fun x => tendsto_const_nhds.congr' <| by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖f x‖] with n hn
      exact (Set.indicator_of_mem (s := {x | ‖f x‖ < n}) hn g).symm)

omit [CompleteSpace H] in
/-- For integrable `g`, the tail integrals of `g` over `{|f| ≥ n}` tend to `0`. -/
private lemma tendsto_integral_indicator_compl_lt {f : X → ℂ} (hf : Measurable f)
    {ν : Measure X} {g : X → ℝ} (hg : Integrable g ν) :
    Tendsto (fun n : ℕ => ∫ x, {x | ‖f x‖ < n}ᶜ.indicator g x ∂ν) atTop (𝓝 0) := by
  have := (tendsto_integral_indicator_lt hf hg).const_sub (∫ x, g x ∂ν)
  rw [sub_self] at this
  refine this.congr fun n => ?_
  rw [Set.indicator_compl, integral_sub' hg
    (hg.indicator (measurableSet_lt hf.norm measurable_const))]

/-- For `ψ ∈ W_f`, `∫ f · 1_{|f| < n} dμ_ψ → ∫ f dμ_ψ` (dominated convergence). -/
theorem tendsto_integral_trunc_assoc {f : X → ℂ} (hf : Measurable f) {ψ : H}
    (hψ : ψ ∈ integralDomain μ f) :
    Tendsto (fun n : ℕ => ∫ x, {x | ‖f x‖ < n}.indicator f x ∂(μ.assoc ψ)) atTop
      (𝓝 (∫ x, f x ∂(μ.assoc ψ))) :=
  tendsto_integral_indicator_lt hf (hψ.integrable one_le_two)

/--
For `ψ ∈ W_f`, the vectors `(∫ f · 1_{|f| < n} dμ) ψ` converge in `H`: their differences
are controlled by the tails `∫_{|f| ≥ N} |f|² dμ_ψ → 0`.

Blueprint reference: `prpstn:hall-10.2` (Part 3).
-/
theorem tendsto_integral_trunc_apply {f : X → ℂ} (hf : Measurable f) {ψ : H}
    (hψ : ψ ∈ integralDomain μ f) :
    ∃ χ : H, Tendsto (fun n : ℕ => μ.integral ({x | ‖f x‖ < n}.indicator f) ψ) atTop
      (𝓝 χ) := by
  set F : ℕ → X → ℂ := fun n => {x | ‖f x‖ < n}.indicator f
  have hF := indicator_lt_mem_bddMeasurable hf
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (μ.assoc ψ) := hψ.integrable_norm_pow two_ne_zero
  refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0 _
    (fun n m N hn hm => ?_) (by simpa using (tendsto_integral_indicator_compl_lt hf hint).sqrt))
  have hsub : μ.integral (F n) ψ - μ.integral (F m) ψ = μ.integral (F n - F m) ψ := by
    rw [← sub_add_cancel (F n) (F m), μ.integral_add ((BddMeasurable X).sub_mem (hF n) (hF m))
      (hF m), sub_add_cancel, add_apply, add_sub_cancel_right]
  rw [dist_eq_norm, hsub, Real.le_sqrt (norm_nonneg _)
      (integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => by positivity) x),
    norm_sq_integral_apply μ ((BddMeasurable X).sub_mem (hF n) (hF m))]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
    (hint.indicator (measurableSet_lt hf.norm measurable_const).compl) (ae_of_all _ fun x => ?_)
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  by_cases h : ‖f x‖ < N
  · simp [Set.indicator, h, h.trans_le hn', h.trans_le hm']
  · by_cases h1 : ‖f x‖ < n <;> by_cases h2 : ‖f x‖ < m <;> simp [Set.indicator, h, h1, h2]

/--
There is a linear map `T : W_f → H`, the pointwise limit of the truncated integrals, which
induces `Q_f` on the diagonal: `Q_f(ψ) = ⟪ψ, T ψ⟫`.

Blueprint reference: `prpstn:hall-10.2` (Parts 1 and 3).
-/
theorem exists_linearMap_integralForm_eq_inner {f : X → ℂ} (hf : Measurable f) :
    ∃ T : integralDomain μ f →ₗ[ℂ] H,
      (∀ ψ : integralDomain μ f, Tendsto (fun n : ℕ =>
        μ.integral ({x | ‖f x‖ < n}.indicator f) (ψ : H)) atTop (𝓝 (T ψ))) ∧
      ∀ ψ : integralDomain μ f, integralForm μ f ψ = ⟪(ψ : H), T ψ⟫_ℂ := by
  choose χ hχ using fun ψ : integralDomain μ f => tendsto_integral_trunc_apply μ hf ψ.2
  let T : integralDomain μ f →ₗ[ℂ] H :=
    { toFun := χ
      map_add' := fun a b =>
        tendsto_nhds_unique (hχ (a + b)) (by simpa using (hχ a).add (hχ b))
      map_smul' := fun c a =>
        tendsto_nhds_unique (hχ (c • a)) (by simpa using (hχ a).const_smul c) }
  refine ⟨T, hχ, fun ψ => ?_⟩
  refine tendsto_nhds_unique (tendsto_integral_trunc_assoc μ hf ψ.2) ?_
  simpa [T, μ.inner_integral (indicator_lt_mem_bddMeasurable hf _)] using
    (tendsto_const_nhds (x := (ψ : H))).inner (𝕜 := ℂ) (hχ ψ)

/--
`Q_f` is a quadratic form on `W_f`.

Blueprint reference: `prpstn:hall-10.2` (Part 1).
-/
theorem isQuadraticFormOn_integralForm {f : X → ℂ} (hf : Measurable f) :
    IsQuadraticFormOn (integralForm μ f) := by
  obtain ⟨T, -, hT⟩ := exists_linearMap_integralForm_eq_inner μ hf
  refine ⟨fun l ψ => ?_, ⟨((innerₛₗ ℂ).comp (integralDomain μ f).subtype).compl₂ T,
    fun φ ψ => (polarizationOn_eq_inner T hT φ ψ).symm⟩⟩
  rw [hT, hT, map_smul, Submodule.coe_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul']

/--
The associated sesquilinear form `L_f` obeys `|L_f(φ, ψ)| ≤ ‖φ‖ ‖f‖_{L²(μ_ψ)}`.

Blueprint reference: `prpstn:hall-10.2` (Part 2).
-/
theorem norm_polarizationOn_integralForm_le {f : X → ℂ} (hf : Measurable f)
    (φ ψ : integralDomain μ f) :
    ‖polarizationOn (integralForm μ f) φ ψ‖ ≤
      ‖(φ : H)‖ * Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(μ.assoc (ψ : H))) := by
  obtain ⟨T, hlim, hT⟩ := exists_linearMap_integralForm_eq_inner μ hf
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (μ.assoc (ψ : H)) := by
    simpa using ((mem_integralDomain μ).1 ψ.2).integrable_norm_pow (p := 2) two_ne_zero
  rw [polarizationOn_eq_inner T hT]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine le_of_tendsto (hlim ψ).norm (Eventually.of_forall fun n => ?_)
  rw [Real.le_sqrt (norm_nonneg _) (integral_nonneg fun x => by positivity),
    norm_sq_integral_apply μ (indicator_lt_mem_bddMeasurable hf n)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hint
    (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ {x | ‖f x‖ < n} <;> simp [Set.indicator, hx]

/--
For each `ψ ∈ W_f` there is a unique `χ ∈ H` representing `φ ↦ L_f(φ, ψ)`.

Blueprint reference: `prpstn:hall-10.2` (Part 3).
-/
theorem existsUnique_repr_integralForm {f : X → ℂ} (hf : Measurable f)
    (ψ : integralDomain μ f) :
    ∃! χ : H, ∀ φ : integralDomain μ f,
      polarizationOn (integralForm μ f) φ ψ = ⟪(φ : H), χ⟫_ℂ := by
  obtain ⟨T, -, hT⟩ := exists_linearMap_integralForm_eq_inner μ hf
  refine ⟨T ψ, fun φ => polarizationOn_eq_inner T hT φ ψ, fun χ hχ => ?_⟩
  refine (dense_integralDomain μ hf).eq_of_inner_right ℂ fun v hv => ?_
  rw [← hχ ⟨v, hv⟩, polarizationOn_eq_inner T hT]

open Classical in
/--
The vector representing `φ ↦ L_f(φ, ψ)`, extended by `0` when `f` is not measurable or no
such vector exists. The measurability guard makes `pmapIntegral` linear by a direct
argument; every result about `pmapIntegral` assumes `f` measurable anyway.
-/
noncomputable def integralApply (f : X → ℂ) (ψ : integralDomain μ f) : H :=
  if h : Measurable f ∧ ∃! χ : H, ∀ φ : integralDomain μ f,
      polarizationOn (integralForm μ f) φ ψ = ⟪(φ : H), χ⟫_ℂ then h.2.choose else 0

/-- For measurable `f`, `integralApply` agrees with any linear `T` inducing `Q_f`. -/
private theorem integralApply_eq {f : X → ℂ} (hf : Measurable f)
    (T : integralDomain μ f →ₗ[ℂ] H)
    (hT : ∀ ψ : integralDomain μ f, integralForm μ f ψ = ⟪(ψ : H), T ψ⟫_ℂ)
    (ψ : integralDomain μ f) : integralApply μ f ψ = T ψ := by
  have h := existsUnique_repr_integralForm μ hf ψ
  rw [integralApply, dif_pos ⟨hf, h⟩]
  exact h.unique h.choose_spec.1 (fun φ => polarizationOn_eq_inner T hT φ ψ)

private theorem integralApply_add (f : X → ℂ) (φ ψ : integralDomain μ f) :
    integralApply μ f (φ + ψ) = integralApply μ f φ + integralApply μ f ψ := by
  by_cases hf : Measurable f
  · obtain ⟨T, -, hT⟩ := exists_linearMap_integralForm_eq_inner μ hf
    simp only [integralApply_eq μ hf T hT, map_add]
  · simp [integralApply, hf]

private theorem integralApply_smul (f : X → ℂ) (c : ℂ) (ψ : integralDomain μ f) :
    integralApply μ f (c • ψ) = c • integralApply μ f ψ := by
  by_cases hf : Measurable f
  · obtain ⟨T, -, hT⟩ := exists_linearMap_integralForm_eq_inner μ hf
    simp only [integralApply_eq μ hf T hT, map_smul]
  · simp [integralApply, hf]

/--
The integral `∫ f dμ` of a possibly unbounded measurable `f`, as an unbounded operator
with domain `W_f`.

Blueprint reference: `prpstn:hall-10.1`.
-/
noncomputable def pmapIntegral (f : X → ℂ) : H →ₗ.[ℂ] H where
  domain := integralDomain μ f
  toFun :=
    { toFun := integralApply μ f
      map_add' := integralApply_add μ f
      map_smul' := integralApply_smul μ f }

@[simp]
theorem pmapIntegral_domain (f : X → ℂ) :
    (pmapIntegral μ f).domain = integralDomain μ f := rfl

/--
The defining off-diagonal identity `⟪φ, (∫ f dμ) ψ⟫ = L_f(φ, ψ)`.

Blueprint reference: `prpstn:hall-10.1`.
-/
theorem inner_pmapIntegral {f : X → ℂ} (hf : Measurable f) (φ ψ : integralDomain μ f) :
    ⟪(φ : H), pmapIntegral μ f ψ⟫_ℂ = polarizationOn (integralForm μ f) φ ψ := by
  have h := existsUnique_repr_integralForm μ hf ψ
  change ⟪(φ : H), integralApply μ f ψ⟫_ℂ = _
  rw [integralApply, dif_pos ⟨hf, h⟩]
  exact (h.choose_spec.1 φ).symm

/--
The diagonal identity `⟪ψ, (∫ f dμ) ψ⟫ = ∫ f dμ_ψ`.

Blueprint reference: `prpstn:hall-10.1`.
-/
theorem inner_self_pmapIntegral {f : X → ℂ} (hf : Measurable f) (ψ : integralDomain μ f) :
    ⟪(ψ : H), pmapIntegral μ f ψ⟫_ℂ = ∫ x, f x ∂(μ.assoc (ψ : H)) := by
  have hQ := isQuadraticFormOn_integralForm μ hf
  rw [inner_pmapIntegral μ hf, polarizationOn]
  have h2 : ψ + ψ = (2 : ℂ) • ψ := by rw [two_smul]
  have h1i : ψ + Complex.I • ψ = ((1 : ℂ) + Complex.I) • ψ := by rw [add_smul, one_smul]
  have hn : (‖((1 : ℂ) + Complex.I)‖ : ℂ) ^ 2 = 2 := by
    have : ‖((1 : ℂ) + Complex.I)‖ ^ 2 = (2 : ℝ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; norm_num
    exact_mod_cast this
  rw [h2, h1i, hQ.smul, hQ.smul, hQ.smul, hn]
  simp only [Complex.norm_ofNat, Complex.norm_I]
  rw [integralForm]
  push_cast
  ring

/--
The bounded truncations `f · 1_{|f| < n}` converge to `∫ f dμ` pointwise in `H`.

Blueprint reference: `lmm:truncations-converge`.
-/
theorem tendsto_integral_truncation {f : X → ℂ} (hf : Measurable f)
    (ψ : integralDomain μ f) :
    Tendsto (fun n : ℕ => μ.integral ({x | ‖f x‖ < n}.indicator f) (ψ : H)) atTop
      (𝓝 (pmapIntegral μ f ψ)) := by
  obtain ⟨T, hlim, hT⟩ := exists_linearMap_integralForm_eq_inner μ hf
  exact (show pmapIntegral μ f ψ = T ψ from integralApply_eq μ hf T hT ψ) ▸ hlim ψ

/--
The norm formula `‖(∫ f dμ) ψ‖² = ∫ |f|² dμ_ψ`.

Blueprint reference: `prpstn:hall-10.1`.
-/
theorem norm_sq_pmapIntegral {f : X → ℂ} (hf : Measurable f) (ψ : integralDomain μ f) :
    ‖pmapIntegral μ f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(μ.assoc (ψ : H)) := by
  refine tendsto_nhds_unique ((tendsto_integral_truncation μ hf ψ).norm.pow 2) ?_
  refine (tendsto_integral_indicator_lt hf (ψ.2.integrable_norm_pow two_ne_zero)).congr
    fun n => ?_
  rw [norm_sq_integral_apply μ (indicator_lt_mem_bddMeasurable hf n)]
  simp [Set.indicator_apply, apply_ite]

/--
Strengthened uniqueness: any unbounded operator with domain `W_f` satisfying merely the
diagonal identity equals `∫ f dμ`.

Blueprint reference: `prpstn:hall-10.1`.
-/
theorem eq_pmapIntegral_of_inner_self {f : X → ℂ} (hf : Measurable f) (A : H →ₗ.[ℂ] H)
    (hdom : A.domain = integralDomain μ f)
    (h : ∀ ψ : A.domain, ⟪(ψ : H), A ψ⟫_ℂ = ∫ x, f x ∂(μ.assoc (ψ : H))) :
    A = pmapIntegral μ f := by
  let T : integralDomain μ f →ₗ[ℂ] H := A.toFun.comp (Submodule.inclusion hdom.symm.le)
  have hT : ∀ ψ : integralDomain μ f, integralForm μ f ψ = ⟪(ψ : H), T ψ⟫_ℂ :=
    fun ψ => (h (Submodule.inclusion hdom.symm.le ψ)).symm
  have key : ∀ ψ : integralDomain μ f, T ψ = pmapIntegral μ f ψ := fun ψ =>
    (dense_integralDomain μ hf).eq_of_inner_right ℂ fun v hv => by
      rw [← polarizationOn_eq_inner T hT ⟨v, hv⟩ ψ, inner_pmapIntegral μ hf ⟨v, hv⟩ ψ]
  exact LinearPMap.ext hdom fun x hx hy => key ⟨x, hy⟩

/--
For bounded measurable `f`, `W_f = H`.

Blueprint reference: `prpstn:coincidence-with-the-bounded-integral`.
-/
theorem integralDomain_eq_top_of_bddMeasurable {f : X → ℂ} (hf : f ∈ BddMeasurable X) :
    integralDomain μ f = ⊤ := by
  obtain ⟨hmeas, C, hC⟩ := hf
  refine eq_top_iff.2 fun ψ _ => ?_
  haveI : IsFiniteMeasure (μ.assoc ψ) :=
    ⟨by rw [assoc_univ_eq]; exact ENNReal.ofReal_lt_top⟩
  exact MemLp.of_bound hmeas.aestronglyMeasurable C (Eventually.of_forall hC)

/--
For bounded measurable `f`, the unbounded integral is the bounded one.

Blueprint reference: `prpstn:coincidence-with-the-bounded-integral`.
-/
theorem pmapIntegral_of_bddMeasurable {f : X → ℂ} (hf : f ∈ BddMeasurable X) :
    pmapIntegral μ f = ((μ.integral f : H →ₗ[ℂ] H).toPMap ⊤) := by
  have hdom := integralDomain_eq_top_of_bddMeasurable μ hf
  have hall : ∀ h : H, h ∈ integralDomain μ f := fun h => hdom ▸ Submodule.mem_top
  have hrep : ∀ ψ φ : integralDomain μ f,
      polarizationOn (integralForm μ f) φ ψ = ⟪(φ : H), μ.integral f ψ⟫_ℂ := fun ψ φ =>
    polarizationOn_eq_inner ((μ.integral f : H →ₗ[ℂ] H).comp (integralDomain μ f).subtype)
      (fun ψ => (μ.inner_integral hf ψ).symm) φ ψ
  have hval : ∀ ψ : integralDomain μ f, integralApply μ f ψ = μ.integral f ψ := by
    intro ψ
    have hex : ∃! χ : H, ∀ φ : integralDomain μ f,
        polarizationOn (integralForm μ f) φ ψ = ⟪(φ : H), χ⟫_ℂ := by
      refine ⟨μ.integral f ψ, hrep ψ, fun χ hχ => ?_⟩
      have h := (hχ ⟨χ - μ.integral f ψ, hall _⟩).symm.trans (hrep ψ _)
      rw [← sub_eq_zero, ← inner_sub_right] at h
      exact sub_eq_zero.1 (inner_self_eq_zero.1 h)
    rw [integralApply, dif_pos ⟨measurable_of_mem_bddMeasurable hf, hex⟩]
    exact hex.unique hex.choose_spec.1 (hrep ψ)
  refine LinearPMap.ext (by rw [pmapIntegral_domain, hdom, LinearMap.toPMap_domain])
    fun x hx _ => ?_
  rw [LinearMap.toPMap_apply]
  exact hval ⟨x, hx⟩

/--
If `f` and `g` agree off a set annihilated by `μ`, they have the same domain.

Blueprint reference: `lmm:integral-ignores-null-sets`.
-/
theorem integralDomain_congr_of_null {f g : X → ℂ} {N : Set X} (hN : MeasurableSet N)
    (hμN : μ N = 0) (hfg : ∀ x ∉ N, f x = g x) : integralDomain μ f = integralDomain μ g := by
  have hae : ∀ ψ : H, f =ᵐ[μ.assoc ψ] g := fun ψ =>
    ae_iff.2 (measure_mono_null (fun x hx => by_contra fun h => hx (hfg x h))
      (by simp [assoc_apply_eq_norm_sq μ ψ hN, hμN]))
  ext ψ
  exact memLp_congr_ae (hae ψ)

/--
If `f` and `g` agree off a set annihilated by `μ`, they have the same integral.

Blueprint reference: `lmm:integral-ignores-null-sets`.
-/
theorem pmapIntegral_congr_of_null {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    {N : Set X} (hN : MeasurableSet N) (hμN : μ N = 0) (hfg : ∀ x ∉ N, f x = g x) :
    pmapIntegral μ f = pmapIntegral μ g := by
  have hae : ∀ ψ : H, f =ᵐ[μ.assoc ψ] g := fun ψ =>
    ae_iff.2 (measure_mono_null (fun x hx => by_contra fun h => hx (hfg x h))
      (by simp [assoc_apply_eq_norm_sq μ ψ hN, hμN]))
  have hdom := integralDomain_congr_of_null μ hN hμN hfg
  -- the quadratic forms agree on vectors with the same underlying value
  have hQ : ∀ (a : integralDomain μ f) (b : integralDomain μ g), (a : H) = b →
      integralForm μ f a = integralForm μ g b := fun a b hab => by
    simp only [integralForm, hab]
    exact integral_congr_ae (hae _)
  have hP : ∀ (φ ψ : integralDomain μ f) (φ' ψ' : integralDomain μ g), (φ : H) = φ' →
      (ψ : H) = ψ' → polarizationOn (integralForm μ f) φ ψ =
        polarizationOn (integralForm μ g) φ' ψ' := fun φ ψ φ' ψ' h1 h2 => by
    simp only [polarizationOn]
    rw [hQ _ (φ' + ψ') (by simp [h1, h2]), hQ _ φ' h1, hQ _ ψ' h2,
      hQ _ (φ' + Complex.I • ψ') (by simp [h1, h2]), hQ _ (Complex.I • ψ') (by simp [h2])]
  refine LinearPMap.ext hdom fun x hx hy => ?_
  change integralApply μ f ⟨x, hx⟩ = integralApply μ g ⟨x, hy⟩
  have hiff : ∀ χ : H, (∀ φ : integralDomain μ f,
      polarizationOn (integralForm μ f) φ ⟨x, hx⟩ = ⟪(φ : H), χ⟫_ℂ) ↔
      ∀ φ : integralDomain μ g,
      polarizationOn (integralForm μ g) φ ⟨x, hy⟩ = ⟪(φ : H), χ⟫_ℂ := fun χ =>
    ⟨fun h φ => by
      rw [← hP ⟨φ, hdom.symm ▸ φ.2⟩ ⟨x, hx⟩ φ ⟨x, hy⟩ rfl rfl]; exact h _,
    fun h φ => by
      rw [hP φ ⟨x, hx⟩ ⟨φ, hdom ▸ φ.2⟩ ⟨x, hy⟩ rfl rfl]; exact h _⟩
  unfold integralApply
  by_cases h : ∃! χ : H, ∀ φ : integralDomain μ f,
      polarizationOn (integralForm μ f) φ ⟨x, hx⟩ = ⟪(φ : H), χ⟫_ℂ
  · have h' : ∃! χ : H, ∀ φ : integralDomain μ g,
        polarizationOn (integralForm μ g) φ ⟨x, hy⟩ = ⟪(φ : H), χ⟫_ℂ := by
      simpa only [hiff] using h
    rw [dif_pos ⟨hf, h⟩, dif_pos ⟨hg, h'⟩]
    exact h'.unique ((hiff _).1 h.choose_spec.1) h'.choose_spec.1
  · have h' : ¬ ∃! χ : H, ∀ φ : integralDomain μ g,
        polarizationOn (integralForm μ g) φ ⟨x, hy⟩ = ⟪(φ : H), χ⟫_ℂ := by
      simpa only [hiff] using h
    rw [dif_neg (fun hh => h hh.2), dif_neg (fun hh => h' hh.2)]

/--
If `|f| ≤ c` on `E`, then the range of `μ E` lies in `W_f`.

Blueprint reference: `lmm:bounded-on-set-range-in-domain`.
-/
theorem range_subset_integralDomain {f : X → ℂ} (hf : Measurable f) {E : Set X}
    (hE : MeasurableSet E) {c : ℝ} (hc : ∀ x ∈ E, ‖f x‖ ≤ c) :
    Set.range (μ E) ⊆ ((integralDomain μ f : Submodule ℂ H) : Set H) := by
  intro η hη
  have hae : ∀ᵐ x ∂(μ.assoc η), ‖f x‖ ≤ c := by
    filter_upwards [(ae_iff (p := fun x => x ∈ E)).mpr (assoc_compl_eq_zero μ hE hη)]
      with x hx using hc x hx
  exact MemLp.of_bound hf.aestronglyMeasurable c hae

/--
The quantitative half of `lmm:bounded-on-set-range-in-domain`.

Blueprint reference: `lmm:bounded-on-set-range-in-domain`.
-/
theorem integral_norm_sq_le_of_mem_range {f : X → ℂ} (hf : Measurable f) {E : Set X}
    (hE : MeasurableSet E) {c : ℝ} (hc : ∀ x ∈ E, ‖f x‖ ≤ c) {η : H}
    (hη : η ∈ Set.range (μ E)) :
    ∫ x, ‖f x‖ ^ 2 ∂(μ.assoc η) ≤ c ^ 2 * ‖η‖ ^ 2 := by
  have hae : ∀ᵐ x ∂(μ.assoc η), ‖f x‖ ^ 2 ≤ c ^ 2 := by
    filter_upwards [(ae_iff (p := fun x => x ∈ E)).mpr (assoc_compl_eq_zero μ hE hη)]
      with x hx using pow_le_pow_left₀ (norm_nonneg _) (hc x hx) 2
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (μ.assoc η) :=
    (range_subset_integralDomain μ hf hE hc hη).integrable_norm_pow two_ne_zero
  calc ∫ x, ‖f x‖ ^ 2 ∂(μ.assoc η) ≤ ∫ _, c ^ 2 ∂(μ.assoc η) :=
        integral_mono_ae hint (integrable_const _) hae
    _ = c ^ 2 * ‖η‖ ^ 2 := by
        rw [integral_const, smul_eq_mul, measureReal_def, assoc_univ_eq,
          ENNReal.toReal_ofReal (by positivity), mul_comm]

/--
For bounded measurable `h` and `T = ∫ h dμ`, the associated measure of `T ψ` has density
`|h|²` with respect to `μ_ψ`.

Blueprint reference: `lmm:associated-measure-of-image`.
-/
theorem assoc_integral_apply {h : X → ℂ} (hh : h ∈ BddMeasurable X) (ψ : H) {E : Set X}
    (hE : MeasurableSet E) :
    (μ.assoc (μ.integral h ψ)) E = ∫⁻ x in E, (‖h x‖₊ : ℝ≥0∞) ^ 2 ∂(μ.assoc ψ) := by
  have hconj := conj_mem_bddMeasurable hh
  have hind := indicator_one_mem_bddMeasurable hE
  have hci := mul_mem_bddMeasurable hconj hind
  obtain ⟨hmeas, C, hC⟩ := id hh
  let G : X → ℂ := fun x => ((E.indicator (fun y => ‖h y‖ ^ 2) x : ℝ) : ℂ)
  have hG : (fun x => (starRingEnd ℂ) (h x)) * E.indicator (1 : X → ℂ) * h = G := by
    funext x
    by_cases hx : x ∈ E <;> simp [G, hx, Complex.conj_mul']
  have hGm : G ∈ BddMeasurable X := hG ▸ mul_mem_bddMeasurable hci hh
  have hop : adjoint (μ.integral h) * μ E * μ.integral h = μ.integral G := by
    rw [← hG, μ.integral_mul hci hh, μ.integral_mul hconj hind, μ.integral_conj hh,
      μ.integral_indicator hE]
  have hint : Integrable (E.indicator (fun y => ‖h y‖ ^ 2)) (μ.assoc ψ) :=
    (Integrable.of_bound (C := C ^ 2) (hmeas.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hC x) 2)).indicator hE
  have hreal : ((μ.assoc (μ.integral h ψ)) E).toReal =
      ∫ x, E.indicator (fun y => ‖h y‖ ^ 2) x ∂(μ.assoc ψ) := by
    have : ⟪μ.integral h ψ, μ E (μ.integral h ψ)⟫_ℂ =
        ⟪ψ, (adjoint (μ.integral h) * μ E * μ.integral h) ψ⟫_ℂ :=
      (adjoint_inner_right _ _ _).symm
    rw [μ.assoc_apply _ hE, this, hop, μ.inner_integral hGm]
    exact congrArg Complex.re (integral_ofReal (𝕜 := ℂ)) |>.trans (Complex.ofReal_re _)
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), hreal,
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => by positivity) x),
    ← lintegral_indicator hE]
  congr 1
  funext x
  by_cases hx : x ∈ E <;> simp [hx, enorm_eq_nnnorm]

/--
Consequently integrals against `μ_{Tψ}` are integrals against `μ_ψ` weighted by `|h|²`.

Blueprint reference: `lmm:associated-measure-of-image`.
-/
theorem lintegral_assoc_integral_apply {h : X → ℂ} (hh : h ∈ BddMeasurable X) (ψ : H)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(μ.assoc (μ.integral h ψ)) =
      ∫⁻ x, g x * (‖h x‖₊ : ℝ≥0∞) ^ 2 ∂(μ.assoc ψ) := by
  have hd : Measurable fun x => (‖h x‖₊ : ℝ≥0∞) ^ 2 :=
    (measurable_of_mem_bddMeasurable hh).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hmeas : μ.assoc (μ.integral h ψ) =
      (μ.assoc ψ).withDensity fun x => (‖h x‖₊ : ℝ≥0∞) ^ 2 :=
    Measure.ext fun E hE => by rw [withDensity_apply _ hE, assoc_integral_apply μ hh ψ hE]
  rw [hmeas, lintegral_withDensity_eq_lintegral_mul _ hd hg]
  simp only [Pi.mul_apply, mul_comm]

/--
If `f` is bounded on `E`, then `∫ f dμ` preserves the spectral subspace
`V_E = Range(μ E)` (which lies in `W_f` by `range_subset_integralDomain`).

Blueprint reference: `lmm:integral-preserves-spectral-subspaces`.
-/
theorem mapsTo_pmapIntegral_range {f : X → ℂ} (hf : Measurable f) {E : Set X}
    (hE : MeasurableSet E) {c : ℝ} (_hc : ∀ x ∈ E, ‖f x‖ ≤ c)
    (ψ : integralDomain μ f) (hψ : (ψ : H) ∈ Set.range (μ E)) :
    pmapIntegral μ f ψ ∈ Set.range (μ E) := by
  have hP := μ.isStarProjection_apply E
  have hψE : μ E ψ = ψ := (mem_range_iff_apply_eq hP _).1 hψ
  have hind := indicator_one_mem_bddMeasurable hE
  refine (isClosed_range_of_isStarProjection hP).mem_of_tendsto
    (tendsto_integral_truncation μ hf ψ) (Eventually.of_forall fun n => ?_)
  have hg := indicator_lt_mem_bddMeasurable hf n
  have hcomm : μ E * μ.integral ({x | ‖f x‖ < (n : ℝ)}.indicator f) =
      μ.integral ({x | ‖f x‖ < (n : ℝ)}.indicator f) * μ E := by
    rw [← μ.integral_indicator hE, ← μ.integral_mul hind hg, ← μ.integral_mul hg hind, mul_comm]
  rw [mem_range_iff_apply_eq hP, ← mul_apply_eq_comp, hcomm, mul_apply_eq_comp, hψE]

/--
For real-valued measurable `f`, the integral `∫ f dμ` is symmetric on `W_f`.

Blueprint reference: `prpstn:hall-10.3`.
-/
theorem isSymmetric_pmapIntegral_of_real {f : X → ℂ} (hf : Measurable f)
    (hreal : ∀ x, (f x).im = 0) : IsSymmetric (pmapIntegral μ f) := by
  have hQ : ∀ ψ : integralDomain μ f, (integralForm μ f ψ).im = 0 := fun ψ => by
    rw [integralForm, integral_congr_ae (ae_of_all _ fun x =>
      (Complex.ext (by simp) (by simp [hreal x]) : f x = (((f x).re : ℝ) : ℂ))),
      integral_complex_ofReal, Complex.ofReal_im]
  intro φ ψ
  rw [inner_pmapIntegral μ hf φ ψ,
    polarizationOn_conj_symm (isQuadraticFormOn_integralForm μ hf) hQ,
    ← inner_pmapIntegral μ hf ψ φ, inner_conj_symm]

/--
For real measurable `f` and non-real `c`, the bounded operator `∫ (f - c)⁻¹ dμ` is a right
inverse of `∫ f dμ - c 1`: it maps into `W_f` and `(∫ f dμ - c)(∫ (f - c)⁻¹ dμ) η = η`.

Blueprint reference: `prpstn:hall-10.3`; also Step 1 of the uniqueness proof of `thrm:hall-10.4`.
-/
theorem pmapIntegral_sub_smul_integral_inv {f : X → ℂ} (hf : Measurable f)
    (hreal : ∀ x, (f x).im = 0) {c : ℂ} (hc : c.im ≠ 0) (η : H) :
    ∃ hψ : μ.integral (fun x => (f x - c)⁻¹) η ∈ integralDomain μ f,
      pmapIntegral μ f ⟨_, hψ⟩ - c • μ.integral (fun x => (f x - c)⁻¹) η = η := by
  have hne : ∀ x, f x - c ≠ 0 := fun x h => hc (by simpa [hreal x] using congrArg Complex.im h)
  have hlow : ∀ x, |c.im| ≤ ‖f x - c‖ := fun x => by
    simpa [hreal x] using Complex.abs_im_le_norm (f x - c)
  have hpos : 0 < |c.im| := abs_pos.mpr hc
  set g : X → ℂ := fun x => (f x - c)⁻¹
  have hgb : ∀ x, ‖g x‖ ≤ |c.im|⁻¹ := fun x => by
    simp only [g, norm_inv]; exact inv_anti₀ hpos (hlow x)
  have hg : g ∈ BddMeasurable X := ⟨(hf.sub_const c).inv, |c.im|⁻¹, hgb⟩
  set K : ℝ := 1 + ‖c‖ * |c.im|⁻¹
  have hfg : ∀ x, f x * g x = 1 + c * g x := fun x => by
    simp only [g]; field_simp [hne x]; ring
  have hfgb : ∀ x, ‖f x * g x‖ ≤ K := fun x => by
    rw [hfg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (hgb x) (norm_nonneg c)) 1
  set ψ := μ.integral g η
  have hψ : ψ ∈ integralDomain μ f := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top,
      lintegral_assoc_integral_apply μ hg η (hf.enorm.pow_const _)]
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_ :
      _ ≤ ∫⁻ _, ENNReal.ofReal (K ^ 2) ∂(μ.assoc η)) ?_
    · rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [ENNReal.toReal_ofNat, Real.rpow_two, ← mul_pow, ← norm_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (hfgb x) 2
    · rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  refine ⟨hψ, ?_⟩
  set F : ℕ → X → ℂ := fun n => {x | ‖f x‖ < n}.indicator f
  have hF : ∀ n, F n ∈ BddMeasurable X := indicator_lt_mem_bddMeasurable hf
  set h : ℕ → X → ℂ := fun n x => (F n x - f x) * g x
  have hdecomp : ∀ n, h n = F n * g + (-c) • g + (-1 : ℂ) • (1 : X → ℂ) := fun n => by
    funext x
    have := hfg x
    simp only [h, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
    linear_combination -this
  have hone : (1 : X → ℂ) ∈ BddMeasurable X := ⟨measurable_const, 1, fun x => by simp⟩
  have hkey : ∀ n, μ.integral (F n) ψ - c • ψ - η = μ.integral (h n) η := fun n => by
    rw [hdecomp, μ.integral_add ((BddMeasurable X).add_mem (mul_mem_bddMeasurable (hF n) hg)
        ((BddMeasurable X).smul_mem _ hg)) ((BddMeasurable X).smul_mem _ hone),
      μ.integral_add (mul_mem_bddMeasurable (hF n) hg) ((BddMeasurable X).smul_mem _ hg),
      μ.integral_mul (hF n) hg, μ.integral_smul _ hg, μ.integral_smul _ hone, μ.integral_one]
    simp only [add_apply, smul_apply, mul_apply_eq_comp, one_apply_eq_self, ψ]
    rw [neg_smul, neg_smul, one_smul]
    abel
  have hhb : ∀ n, h n ∈ BddMeasurable X := fun n => by
    rw [hdecomp]
    exact (BddMeasurable X).add_mem ((BddMeasurable X).add_mem (mul_mem_bddMeasurable (hF n) hg)
      ((BddMeasurable X).smul_mem _ hg)) ((BddMeasurable X).smul_mem _ hone)
  have hhle : ∀ n x, ‖h n x‖ ≤ K := fun n x => by
    refine le_trans ?_ (hfgb x)
    simp only [h, F, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    by_cases hx : ‖f x‖ < n <;> simp [Set.indicator, hx]
  have hsq : Tendsto (fun n => ∫ x, ‖h n x‖ ^ 2 ∂(μ.assoc η)) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ.assoc η)
      (F := fun n x => ‖h n x‖ ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => K ^ 2)
      (fun n => ((hhb n).1.norm.pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hhle n x) 2)
      (Eventually.of_forall fun x => by
        obtain ⟨N, hN⟩ := exists_nat_gt ‖f x‖
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have : ‖f x‖ < n := hN.trans_le (by exact_mod_cast hn)
        simp [h, F, this])
    simpa using this
  have hlim : Tendsto (fun n => μ.integral (F n) ψ - c • ψ - η) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : ∀ n, ‖μ.integral (F n) ψ - c • ψ - η‖ =
        Real.sqrt (∫ x, ‖h n x‖ ^ 2 ∂(μ.assoc η)) := fun n => by
      rw [hkey, ← norm_sq_integral_apply μ (hhb n), Real.sqrt_sq (norm_nonneg _)]
    simp_rw [hn]
    simpa using hsq.sqrt
  have h1 := ((tendsto_integral_truncation μ hf ⟨ψ, hψ⟩).sub_const (c • ψ)).sub_const η
  exact sub_eq_zero.mp (tendsto_nhds_unique h1 hlim)

/--
For real-valued measurable `f` and non-real `c`, the operator `∫ f dμ - c 1` maps `W_f`
onto `H`: a preimage of `η` is `(∫ (f - c)⁻¹ dμ) η`.

Blueprint reference: `prpstn:hall-10.3`.
-/
theorem range_subSmul_pmapIntegral_eq_top {f : X → ℂ} (hf : Measurable f)
    (hreal : ∀ x, (f x).im = 0) {c : ℂ} (hc : c.im ≠ 0) :
    range (subSmul (pmapIntegral μ f) c) = ⊤ := by
  refine eq_top_iff.2 fun η _ => ?_
  obtain ⟨hψ, he⟩ := pmapIntegral_sub_smul_integral_inv μ hf hreal hc η
  exact mem_range.2 ⟨⟨_, hψ⟩, he⟩

/--
The integral of a real-valued measurable function is a self-adjoint unbounded operator on
`W_f`.

Blueprint reference: `prpstn:hall-10.3`.
-/
theorem isSelfAdjoint_pmapIntegral_of_real {f : X → ℂ} (hf : Measurable f)
    (hreal : ∀ x, (f x).im = 0) : IsSelfAdjoint (pmapIntegral μ f) := by
  have hT : HasDenseDomain (pmapIntegral μ f) := dense_integralDomain μ hf
  have hle := (isSymmetric_iff_le_adjoint hT).mp (isSymmetric_pmapIntegral_of_real μ hf hreal)
  have hk : ker (subSmul ((pmapIntegral μ f)†) (-Complex.I)) = ⊥ := by
    rw [← Complex.conj_I, ← orthogonal_range_subSmul hT,
      range_subSmul_pmapIntegral_eq_top μ hf hreal (by simp), Submodule.top_orthogonal_eq_bot]
  exact LinearPMap.isSelfAdjoint_def.mpr (adjoint_eq_of_range_eq_top hle
    (range_subSmul_pmapIntegral_eq_top μ hf hreal (by simp)) hk)

end Unbounded
end Spectral
end Physicslib4
