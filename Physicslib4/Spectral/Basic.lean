/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bounded operators on a Hilbert space: basic spectral prerequisites

This file collects the facts about a complex Hilbert space `H` and the algebra
`H →L[ℂ] H` of bounded operators on it that the blueprint's section on spectral
theorems (`sctn:spectral-theorems`) uses as prerequisites and which are *not*
already available in Mathlib. Prerequisites that Mathlib does supply are recorded in
the dictionary below rather than restated as local theorems.

Throughout, `H` is a complex Hilbert space, so that `H →L[ℂ] H` is the blueprint's
`𝓑(H)`.

## Main definitions

* `Physicslib4.Spectral.BddMeasurable` — the complex vector space of bounded
  measurable complex-valued functions on a measurable space. This is the single
  spelling of "bounded Borel function" used throughout the `Spectral` directory,
  in place of a repeated `Measurable f ∧ ∃ K, ∀ x, ‖f x‖ ≤ K` hypothesis pair.
* `Physicslib4.Spectral.BoundedPointwiseLimit` — "the sequence `f` is uniformly
  bounded by `M` and converges pointwise to `g`", the hypothesis package shared by
  every bounded-convergence and monotone-class argument in this directory.

## Main statements

* `Physicslib4.Spectral.mem_span_orthogonal_iff` — the orthogonal complement of an
  arbitrary *subset* of `H`.
* `Physicslib4.Spectral.completeSpace_boundedOp` — `𝓑(H)` is a Banach space.
* `Physicslib4.Spectral.completeSpace_dual` — the dual of a normed space is a Banach
  space.
* `Physicslib4.Spectral.mem_resolventSet_iff_isUnit_sub_smul`,
  `Physicslib4.Spectral.spectrum_eq_compl_resolventSet`,
  `Physicslib4.Spectral.mul_resolvent_of_mem_resolventSet` — the resolvent set, the
  spectrum, and the resolvent, in the blueprint's sign convention.
* `Physicslib4.Spectral.riesz_representation` — the Riesz representation theorem.
* `Physicslib4.Spectral.norm_adjoint`,
  `Physicslib4.Spectral.norm_adjoint_mul_self` — the C⋆-identities.
* `Physicslib4.Spectral.adjoint_add`, `Physicslib4.Spectral.adjoint_smul`,
  `Physicslib4.Spectral.adjoint_mul`, `Physicslib4.Spectral.adjoint_pow`,
  `Physicslib4.Spectral.adjoint_one` — the `*`-algebra identities for the adjoint.
* `Physicslib4.Spectral.tendsto_adjoint` — continuity of the adjoint.
* `Physicslib4.Spectral.norm_apply_le_of_isStarProjection` — projections are norm
  decreasing.
* `Physicslib4.Spectral.opNorm_eq_sSup_inner` — the operator norm as a supremum of
  matrix elements over pairs of unit vectors.
* `Physicslib4.Spectral.continuous_iff_exists_bound` — bounded ↔ continuous for
  linear maps between normed spaces.
* `Physicslib4.Spectral.exists_simpleFunc_tendstoUniformly` — a bounded measurable
  complex function is a uniform limit of simple functions.
* `Physicslib4.Spectral.tendsto_iff_isBounded_of_monotone`,
  `Physicslib4.Spectral.tendsto_iff_isBounded_of_antitone` — the monotone
  convergence theorem for real sequences.
* `Physicslib4.Spectral.measurable_of_tendsto_pointwise`,
  `Physicslib4.Spectral.norm_le_of_tendsto` — pointwise limits of uniformly bounded
  measurable functions.
* `Physicslib4.Spectral.tendsto_integral_of_boundedPointwiseLimit` — the bounded
  convergence theorem on a finite measure space.
* `Physicslib4.Spectral.exists_unique_laurentSeries` — Laurent's theorem.

## Implementation notes

Mathlib's `ContinuousLinearMap.adjoint` supplies the blueprint's `A ↦ A⋆`, and
`IsStarProjection` supplies the blueprint's bounded orthogonal projections; the
blueprint's `ρ(A)`, `σ(A)` are Mathlib's `resolventSet ℂ A`, `spectrum ℂ A`, noting
that Mathlib uses `λ • 1 - A` where the blueprint uses `A - λ • 1`, which describes
the same set (`mem_resolventSet_iff_isUnit_sub_smul`).

The blueprint's standing convention `H ≠ {0}`, stated in the section preamble
alongside `def:bounded-operator-notation`, is localised, as the blueprint itself
prescribes: it appears as a `Nontrivial H` hypothesis on exactly those declarations
that use it. No declaration in this file needs it. The blueprint's other standing
convention, separability of `H`
(`def:bounded-operator-notation`), is *never* needed in this directory: the only
place one might expect it — the convergence of the partial sums
`∑_{i<n} Pᵢψ` of a family of mutually annihilating projections in
`Physicslib4/Spectral/ProjectionValuedMeasure.lean` — follows from
`‖∑_{i<n} Pᵢψ‖² = ∑_{i<n} ‖Pᵢψ‖² ≤ ‖ψ‖²` and completeness alone. Accordingly no
declaration in the `Spectral` directory carries a `SeparableSpace H` hypothesis, and
its absence is deliberate.

### Blueprint conventions that are literally Mathlib declarations

The blueprint opens with a block of notational conventions and a proposition
collecting standard facts. Each is exactly a Mathlib declaration, so it is cited
rather than restated here; the blueprint nodes carry those Mathlib names.

* `def:inner-product` — Mathlib's `InnerProductSpace ℂ H` has precisely the
  blueprint's axioms, and conjugates the *first* argument, which is the blueprint's
  (physics) convention: `inner_conj_symm`, `inner_self_im`, `inner_self_nonneg`,
  `inner_self_eq_zero`, `inner_smul_left`, `inner_smul_right`, `inner_add_left`,
  `inner_add_right`.
* `def:induced-norm` — `norm_eq_sqrt_re_inner`.
* `def:bounded-operator-notation` — `ContinuousLinearMap.le_opNorm` and
  `ContinuousLinearMap.opNorm_le_bound` (the operator norm is the least bound);
  `𝓑(H)` is `H →L[ℂ] H`.
* `def:identity-operator` — `ContinuousLinearMap.norm_id`, `ContinuousLinearMap.one_def`
  and `ContinuousLinearMap.id_apply`.
* `def:indicator-function` — `Set.indicator`, `Set.indicator_apply`,
  `Set.indicator_of_mem`, `Set.indicator_of_notMem`, `Set.indicator_mul`,
  `Set.indicator_union_of_disjoint`.
* `def:identity-and-indicator` — carried by
  `Physicslib4.Spectral.one_apply_and_indicator_apply` below, which asserts both halves
  of the compound anchor together and also records the convention that `ℕ` includes `0`.
* `prpstn:basic-integral-properties` — `MeasureTheory.integral_indicator`,
  `MeasureTheory.integral_add`, `MeasureTheory.integral_smul`,
  `MeasureTheory.lintegral_mono`, `norm_integral_le_integral_norm`.
* `prpstn:hall-a.43` (Cauchy–Schwarz) — `norm_inner_le_norm` and, in the squared
  form the blueprint states first, `inner_mul_inner_self_le`.
* `prpstn:reverse-triangle-inequality` — `abs_norm_sub_norm_le`.
* `def:bounded-inverse` — `isUnit_iff_exists`.
* `def:adjoint-bounded` — `ContinuousLinearMap.eq_adjoint_iff` (existence *and*
  uniqueness of the adjoint), `ContinuousLinearMap.adjoint_inner_left`,
  `ContinuousLinearMap.star_eq_adjoint`,
  `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`.
* `prpstn:hall-7.3` — `ContinuousLinearMap.orthogonal_range`. This is an equality of
  `Submodule`s, `(T : E →ₗ F).rangeᗮ = (T⋆).ker`, rather than the blueprint's equality
  of subsets of `H`; the two are interchangeable through `SetLike.ext_iff`.
* `prpstn:continuity-of-norm-and-inner-product` — `Filter.Tendsto.norm` and
  `Filter.Tendsto.inner`.

The same holds of the analysis prerequisites the spectral section quotes from a
functional-analysis course. Where the Mathlib spelling is not a literal transcription
of the blueprint, the divergence is recorded.

* `lmm:lemma-2` — `norm_mul_le`, applied through the `NormedRing (H →L[ℂ] H)`
  instance, in which `A * B` is composition. (`ContinuousLinearMap.opNorm_comp_le` is
  the same inequality written with `∘L`.)
* `prpstn:hall-a.34` — `Summable.of_norm`, whose ambient `[CompleteSpace E]` is exactly
  the blueprint's hypothesis that `V` is Banach; the comparison-test form used in
  practice is `Summable.of_norm_bounded`. Caveat: Mathlib's `Summable` is
  *unconditional* summability over the index type, which for a series indexed by `ℕ` in
  a Banach space is strictly stronger than convergence of the partial sums. This is
  harmless here, because the hypothesis `∑ ‖ψᵢ‖ < ∞` is absolute convergence, under
  which the two notions agree.
* `lmm:nth-term-test` — `Summable.tendsto_atTop_zero`, i.e. the blueprint's
  contrapositive form `∑ aᵢ` converges `⇒ ‖aᵢ‖ → 0`. Caveat: as above, the Lean
  hypothesis is unconditional `Summable f`, not mere convergence of the partial sums
  `∑_{i<n} aᵢ`, so the Lean statement is formally weaker than the blueprint's; it is
  what every use in this section needs, since the series involved are all absolutely
  convergent.
* `thrm:analytic-equivalence-theorem` — `Complex.analyticOnNhd_iff_differentiableOn`
  (`Complex.analyticOn_iff_differentiableOn` for the `AnalyticOn` variant). Stated for
  Banach-space-valued `f : ℂ → E`, which covers the blueprint's scalar case.
* `thrm:maximum-modulus-principle` — `Complex.exists_mem_frontier_isMaxOn_norm` is the
  blueprint's statement itself (`|f|` attains its maximum at a point of the frontier),
  and `Complex.norm_le_of_forall_mem_frontier_norm_le` is the corollary form actually
  used downstream (a bound on the frontier propagates to the closure). Caveats:
  Mathlib's `DiffContOnCl ℂ f U` is the blueprint's "continuous on `B̄`, holomorphic on
  `B`"; and Mathlib drops the blueprint's hypothesis that `B` be connected, which is
  superfluous — the maximum modulus principle in this form holds on any bounded
  non-empty open set.
* `thrm:hall-a.40` — `banach_steinhaus`, the principle of uniform boundedness;
  `banach_steinhaus_iSup_nnnorm` is the `ℝ≥0∞`-supremum variant.
-/

namespace Physicslib4
namespace Spectral

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### Notation anchors
-/

omit [CompleteSpace H] in
/--
The compound anchor for the two notational conventions fixed together in the
blueprint: the identity operator `1` acts as the identity on every vector, and
the indicator function `1_E` takes the value `1` on `E` and `0` off it.

This node also fixes a third convention with no propositional content, that
`ℕ = {0, 1, 2, ...}` includes `0`, matching Lean and Mathlib. Section 10.3 cites
this anchor for that convention as well as for the two notations.

Blueprint reference: `def:identity-and-indicator`.
-/
theorem one_apply_and_indicator_apply {X : Type*} (E : Set X) (x : X)
    [Decidable (x ∈ E)] :
    (∀ ψ : H, (1 : H →L[ℂ] H) ψ = ψ) ∧
      E.indicator (1 : X → ℂ) x = if x ∈ E then 1 else 0 :=
  ⟨fun _ => rfl, by simp [Set.indicator_apply]⟩

/-!
### Orthogonal complements of subsets
-/

omit [CompleteSpace H] in
/--
The orthogonal complement of an arbitrary subset `V ⊆ H` is the orthogonal
complement `(Submodule.span ℂ V)ᗮ` of the submodule it spans: a vector `ψ` lies in
it exactly when `⟪ψ, v⟫ = 0` for every `v ∈ V`.

Blueprint reference: `def:orthogonal-complement`.
-/
theorem mem_span_orthogonal_iff {V : Set H} {ψ : H} :
    ψ ∈ (Submodule.span ℂ V)ᗮ ↔ ∀ v ∈ V, ⟪ψ, v⟫_ℂ = 0 := by
  rw [Submodule.mem_orthogonal']
  refine ⟨fun h v hv => h v (Submodule.subset_span hv), fun h u hu => ?_⟩
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul c x _ hx => simp [inner_smul_right, hx]

/-!
### Bounded measurable functions

The blueprint's "bounded Borel function on `X`" is used as a hypothesis on roughly
thirty declarations in this directory. We package it once, as a `Submodule` (the
class is a complex vector space, which is how the blueprint uses it), rather than
threading a `Measurable f ∧ ∃ K, ∀ x, ‖f x‖ ≤ K` pair through every signature.
-/

/--
The complex vector space of bounded, measurable, complex-valued functions on a
measurable space `X`.
-/
def BddMeasurable (X : Type*) [MeasurableSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C}
  zero_mem' := ⟨measurable_const, 0, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, Cf, hCf⟩ ⟨hg, Cg, hCg⟩
    exact ⟨hf.add hg, Cf + Cg, fun x =>
      (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))⟩
  smul_mem' := by
    rintro c f ⟨hf, Cf, hCf⟩
    refine ⟨hf.const_smul c, ‖c‖ * Cf, fun x => ?_⟩
    simpa [norm_smul] using mul_le_mul_of_nonneg_left (hCf x) (norm_nonneg c)

@[simp]
theorem mem_bddMeasurable {X : Type*} [MeasurableSpace X] {f : X → ℂ} :
    f ∈ BddMeasurable X ↔ Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := Iff.rfl

theorem measurable_of_mem_bddMeasurable {X : Type*} [MeasurableSpace X] {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) : Measurable f := hf.1

theorem exists_bound_of_mem_bddMeasurable {X : Type*} [MeasurableSpace X] {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := hf.2

/-!
### `𝓑(H)` as a Banach space
-/

/--
`𝓑(H)` is a Banach space: it is a normed `ℂ`-algebra (the `NormedRing` and
`NormedAlgebra` instances on `H →L[ℂ] H`) and it is complete in the operator norm.
Only completeness has propositional content, so it is what is stated here.

Blueprint reference: `lmm:bounded-operators-form-a-banach-space`.
-/
theorem completeSpace_boundedOp : CompleteSpace (H →L[ℂ] H) := inferInstance

/--
The dual of a normed space is a Banach space: `V →L[ℂ] ℂ` is complete in the
operator norm.

In Mathlib this is the instance `ContinuousLinearMap.instCompleteSpace` rather than a
theorem, so — following `completeSpace_boundedOp` above — it is restated here as the
proposition the blueprint asserts. Note that the blueprint assumes `V` itself is a
Banach space; that hypothesis is not needed, since completeness of `V →L[ℂ] ℂ` comes
from completeness of the *target* `ℂ`. It is therefore omitted rather than carried as
an unused binder.

Blueprint reference: `thrm:theorem-on-completeness-of-the-dual`.
-/
theorem completeSpace_dual (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] :
    CompleteSpace (V →L[ℂ] ℂ) := inferInstance

/-!
### The resolvent set, the spectrum and the resolvent

Mathlib's `resolventSet ℂ A` is defined through `λ𝟙 - A`, whereas the blueprint uses
`A - λ𝟙`; since `-1` is a unit these describe the same set, which is the content of
`mem_resolventSet_iff_isUnit_sub_smul`.

Blueprint reference: `def:bounded-operator-resolvent-and-spectrum`.
-/

omit [CompleteSpace H] in
/--
`λ` lies in the resolvent set of `A` exactly when `A - λ𝟙` has a bounded inverse,
which is the blueprint's definition.
-/
theorem mem_resolventSet_iff_isUnit_sub_smul (A : H →L[ℂ] H) (lam : ℂ) :
    lam ∈ resolventSet ℂ A ↔ IsUnit (A - lam • (1 : H →L[ℂ] H)) := by
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, ← IsUnit.neg_iff, neg_sub]

omit [CompleteSpace H] in
/-- The spectrum is the complement of the resolvent set. -/
theorem spectrum_eq_compl_resolventSet (A : H →L[ℂ] H) :
    spectrum ℂ A = (resolventSet ℂ A)ᶜ := rfl

omit [CompleteSpace H] in
/-- For `λ` in the resolvent set, `resolvent A λ` inverts `λ𝟙 - A`. -/
theorem mul_resolvent_of_mem_resolventSet (A : H →L[ℂ] H) {lam : ℂ}
    (h : lam ∈ resolventSet ℂ A) :
    (lam • (1 : H →L[ℂ] H) - A) * resolvent A lam = 1 := by
  have h' : IsUnit ((algebraMap ℂ (H →L[ℂ] H)) lam - A) := h
  simpa [resolvent, Algebra.algebraMap_eq_smul_one] using Ring.mul_inverse_cancel _ h'

/-!
### The Riesz representation theorem
-/

/--
The Riesz representation theorem: every bounded linear functional on `H` is
`ψ ↦ ⟪χ, ψ⟫` for a unique `χ ∈ H`, whose norm is the operator norm of the
functional. Mathlib packages this as the conjugate-linear isometric equivalence
`InnerProductSpace.toDual`.

Blueprint reference: `thrm:hall-a.52`.
-/
theorem riesz_representation (ξ : H →L[ℂ] ℂ) :
    ∃! χ : H, (∀ ψ : H, ξ ψ = ⟪χ, ψ⟫_ℂ) ∧ ‖χ‖ = ‖ξ‖ := by
  refine ⟨(InnerProductSpace.toDual ℂ H).symm ξ,
    ⟨fun ψ => (InnerProductSpace.toDual_symm_apply (x := ψ) (y := ξ)).symm,
      (InnerProductSpace.toDual ℂ H).symm.norm_map ξ⟩, ?_⟩
  rintro χ ⟨hχ, -⟩
  refine ext_inner_right ℂ fun ψ => ?_
  rw [← hχ ψ, InnerProductSpace.toDual_symm_apply]

/-!
### The adjoint

The defining property of the adjoint and its uniqueness are Mathlib's
`ContinuousLinearMap.eq_adjoint_iff` (blueprint `def:adjoint-bounded`). What is
recorded here are the facts Mathlib does not state in this form: the two
C⋆-identities, the `*`-algebra identities, and continuity.
-/

/--
The adjoint is norm preserving; in particular `A⋆` is again a bounded operator, and
`‖A⋆‖ ≤ ‖A‖`.

Blueprint references: `prpstn:adjoint-is-bounded` and the first half of
`prpstn:hall-7.2`.
-/
theorem norm_adjoint (A : H →L[ℂ] H) : ‖adjoint A‖ = ‖A‖ :=
  (adjoint (𝕜 := ℂ) (E := H) (F := H)).norm_map A

/--
The C⋆-identity `‖A⋆A‖ = ‖A‖²` on `𝓑(H)`.

Blueprint reference: `prpstn:hall-7.2` (second half).
-/
theorem norm_adjoint_mul_self (A : H →L[ℂ] H) : ‖adjoint A * A‖ = ‖A‖ ^ 2 := by
  rw [← star_eq_adjoint, CStarRing.norm_star_mul_self, sq]

/--
The adjoint is additive.

Blueprint reference: `lmm:adjoint-algebra`.
-/
theorem adjoint_add (A B : H →L[ℂ] H) : adjoint (A + B) = adjoint A + adjoint B := by
  simp [← star_eq_adjoint, star_add]

/--
The adjoint is conjugate homogeneous.

Blueprint reference: `lmm:adjoint-algebra`.
-/
theorem adjoint_smul (c : ℂ) (A : H →L[ℂ] H) :
    adjoint (c • A) = (starRingEnd ℂ) c • adjoint A := by
  simp [← star_eq_adjoint, star_smul]

/--
The adjoint is anti-multiplicative.

Blueprint reference: `lmm:adjoint-algebra`.
-/
theorem adjoint_mul (A B : H →L[ℂ] H) : adjoint (A * B) = adjoint B * adjoint A := by
  simp [← star_eq_adjoint, star_mul]

/--
The adjoint is compatible with powers.

Blueprint reference: `lmm:adjoint-algebra`.
-/
theorem adjoint_pow (A : H →L[ℂ] H) (k : ℕ) : adjoint (A ^ k) = adjoint A ^ k := by
  simp [← star_eq_adjoint, star_pow]

/--
The adjoint fixes the identity operator. (Involutivity of the adjoint is Mathlib's
`ContinuousLinearMap.adjoint_adjoint`.)

Blueprint reference: `lmm:adjoint-algebra`.
-/
theorem adjoint_one : adjoint (1 : H →L[ℂ] H) = 1 := by
  simp

/--
Convergence in the operator norm is preserved by taking adjoints.

Blueprint reference: `prpstn:continuity-of-the-adjoint`.
-/
theorem tendsto_adjoint {B : ℕ → H →L[ℂ] H} {B₀ : H →L[ℂ] H}
    (h : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun n => adjoint (B n)) atTop (𝓝 (adjoint B₀)) :=
  (((adjoint (𝕜 := ℂ) (E := H) (F := H)).continuous).tendsto B₀).comp h

/-!
### Orthogonal projections
-/

/--
A bounded orthogonal projection is norm decreasing.

Blueprint reference: `lmm:projection-norm-decreasing`.
-/
theorem norm_apply_le_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) (ψ : H) :
    ‖P ψ‖ ≤ ‖ψ‖ := by
  obtain ⟨inst, hPeq⟩ := isStarProjection_iff_eq_starProjection_range.mp hP
  haveI := inst
  rw [hPeq]
  exact Submodule.norm_starProjection_apply_le _ ψ

/-!
### The operator norm
-/

/--
The operator norm of `A` is the supremum of the moduli of its matrix elements
`⟪χ, A ψ⟫` over pairs of unit vectors.

Blueprint reference: `lmm:lemma-1`.
-/
theorem opNorm_eq_sSup_inner (A : H →L[ℂ] H) :
    ‖A‖ = sSup {r : ℝ | ∃ χ ψ : H, ‖χ‖ = 1 ∧ ‖ψ‖ = 1 ∧ r = ‖⟪χ, A ψ⟫_ℂ‖} := by
  let S : Set ℝ := {r : ℝ | ∃ χ ψ : H, ‖χ‖ = 1 ∧ ‖ψ‖ = 1 ∧ r = ‖⟪χ, A ψ⟫_ℂ‖}
  -- The norm of a vector is the supremum of the moduli of its inner products
  -- against all unit vectors (the sharp Cauchy-Schwarz bound, via Riesz).
  have hnorm (y : H) :
      ‖y‖ = sSup {r : ℝ | ∃ x : H, ‖x‖ = 1 ∧ r = ‖⟪x, y⟫_ℂ‖} := by
    let L : H →L[ℂ] ℂ := InnerProductSpace.toDual ℂ H y
    have hL : ‖L‖ = ‖y‖ := (InnerProductSpace.toDual ℂ H).norm_map y
    have hset : (fun x : H => ‖L x‖) '' Metric.sphere (0 : H) 1 =
        {r : ℝ | ∃ x : H, ‖x‖ = 1 ∧ r = ‖⟪x, y⟫_ℂ‖} := by
      apply Set.ext
      intro r
      constructor
      · rintro ⟨x, hx, heq⟩
        refine ⟨x, ?_, ?_⟩
        · simpa [Metric.sphere] using hx
        · have heq0 : ‖⟪y, x⟫_ℂ‖ = r := by
            rw [← heq]
            simp [L]
          exact heq0.symm.trans (norm_inner_symm y x)
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x, ?_, ?_⟩
        · simpa [Metric.sphere] using hx
        · simpa [L] using norm_inner_symm y x
    calc
      ‖y‖ = sSup ((fun x : H => ‖L x‖) '' Metric.sphere (0 : H) 1) := by
        rw [L.sSup_sphere_eq_norm]
        exact hL.symm
      _ = sSup {r : ℝ | ∃ x : H, ‖x‖ = 1 ∧ r = ‖⟪x, y⟫_ℂ‖} := by rw [hset]
  -- Every matrix element in `S` is bounded above by `‖A‖` (Cauchy-Schwarz).
  have hS_le : ∀ r ∈ S, r ≤ ‖A‖ := by
    rintro r ⟨χ, ψ, hχ, hψ, rfl⟩
    calc
      ‖⟪χ, A ψ⟫_ℂ‖ ≤ ‖χ‖ * ‖A ψ‖ := norm_inner_le_norm χ (A ψ)
      _ = ‖A ψ‖ := by rw [hχ]; ring
      _ ≤ ‖A‖ * ‖ψ‖ := A.le_opNorm ψ
      _ = ‖A‖ := by rw [hψ]; ring
  have hS_bdd : BddAbove S := ⟨‖A‖, hS_le⟩
  have h0 : 0 ≤ sSup S := by
    rcases S.eq_empty_or_nonempty with hsmpty | hne
    · rw [hsmpty, Real.sSup_empty]
    · rcases hne with ⟨r, hr⟩
      exact le_trans (by rcases hr with ⟨χ, ψ, hχ, hψ, rfl⟩; exact norm_nonneg ⟪χ, A ψ⟫_ℂ)
        (le_csSup hS_bdd hr)
  -- Upper bound: `sSup S` is the least upper bound, and `‖A‖` bounds it.
  have hsSup_le : sSup S ≤ ‖A‖ := Real.sSup_le hS_le (norm_nonneg A)
  -- Lower bound: ‖A‖ = sSup {‖A ψ‖ | ‖ψ‖ = 1}, and each ‖A ψ‖ is a member's sSup.
  have hT : ‖A‖ = sSup ((fun x : H => ‖A x‖) '' Metric.sphere (0 : H) 1) :=
    A.sSup_sphere_eq_norm.symm
  have hleT : sSup ((fun x : H => ‖A x‖) '' Metric.sphere (0 : H) 1) ≤ sSup S := by
    apply Real.sSup_le
    · rintro r ⟨ψ, hψ, rfl⟩
      let U : Set ℝ := {r : ℝ | ∃ χ : H, ‖χ‖ = 1 ∧ r = ‖⟪χ, A ψ⟫_ℂ‖}
      have hU : ‖A ψ‖ = sSup U := by
        simpa [U] using hnorm (A ψ)
      have hU_le : sSup U ≤ sSup S := by
        apply Real.sSup_le
        · rintro r' ⟨χ, hχ, rfl⟩
          exact le_csSup hS_bdd ⟨χ, ψ, hχ, (by simpa [Metric.sphere] using hψ), rfl⟩
        · exact h0
      calc
        ‖A ψ‖ = sSup U := hU
        _ ≤ sSup S := hU_le
    · exact h0
  have hle : ‖A‖ ≤ sSup S := by
    calc
      ‖A‖ = sSup ((fun x : H => ‖A x‖) '' Metric.sphere (0 : H) 1) := hT
      _ ≤ sSup S := hleT
  change ‖A‖ = sSup S
  exact le_antisymm hle hsSup_le

/--
A linear map between normed spaces is bounded if and only if it is continuous.

Blueprint reference: `prpstn:bounded-operators-are-continuous`.
-/
theorem continuous_iff_exists_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℂ E] [NormedSpace ℂ F] (T : E →ₗ[ℂ] F) :
    Continuous T ↔ ∃ C : ℝ, ∀ x : E, ‖T x‖ ≤ C * ‖x‖ := by
  refine ⟨fun h => ?_, fun ⟨C, hC⟩ => AddMonoidHomClass.continuous_of_bound T C hC⟩
  exact ⟨‖(⟨T, h⟩ : E →L[ℂ] F)‖, fun x => (⟨T, h⟩ : E →L[ℂ] F).le_opNorm x⟩

/-!
### Approximation and convergence prerequisites
-/

/-- The grid point of a real coordinate `a` at level `m`: `⌊a * m⌋`. -/
private noncomputable def gridIndex (m : ℕ) (a : ℝ) : ℤ :=
  Int.floor (a * (m : ℝ))

/-- A symmetric bound for `gridIndex m a` when `|a| ≤ C`. -/
private noncomputable def gridBound (m : ℕ) (C : ℝ) : ℤ :=
  Int.ceil (C * (m : ℝ)) + 1

/-- The complex grid point with integer coordinates `i`, `j` at level `m`. -/
private noncomputable def gridVal (m : ℕ) (i j : ℤ) : ℂ :=
  Complex.mk ((i : ℝ) / (m : ℝ)) ((j : ℝ) / (m : ℝ))

private lemma gridIndex_mem_Icc {C : ℝ} (hC : 0 ≤ C) {a : ℝ} (ha : |a| ≤ C) {m : ℕ}
    (hm : 0 < (m : ℝ)) :
    gridIndex m a ∈ Finset.Icc (-gridBound m C) (gridBound m C) := by
  rw [Finset.mem_Icc]
  constructor
  · -- lower bound: -gridBound m C ≤ gridIndex m a
    have hz : -(gridBound m C : ℝ) < (gridIndex m a : ℝ) := by
      have h1 : -(gridBound m C : ℝ) ≤ -(C * (m : ℝ)) - 1 := by
        have h4a : C * (m : ℝ) ≤ (Int.ceil (C * (m : ℝ)) : ℝ) := Int.le_ceil (C * (m : ℝ))
        rw [show -(gridBound m C : ℝ) = -(Int.ceil (C * (m : ℝ)) : ℝ) - 1 by
          unfold gridBound
          norm_num [Int.cast_add]
          ring]
        nlinarith
      have h2 : -(C * (m : ℝ)) - 1 ≤ a * (m : ℝ) - 1 := by
        have hnega : -C ≤ a := (abs_le.mp ha).1
        nlinarith
      have h3 : a * (m : ℝ) - 1 < (gridIndex m a : ℝ) := by
        have hh : a * (m : ℝ) < (Int.floor (a * (m : ℝ)) : ℝ) + 1 :=
          Int.lt_floor_add_one (a * (m : ℝ))
        unfold gridIndex
        nlinarith
      calc
        -(gridBound m C : ℝ) ≤ -(C * (m : ℝ)) - 1 := h1
        _ ≤ a * (m : ℝ) - 1 := h2
        _ < (gridIndex m a : ℝ) := h3
    exact_mod_cast (le_of_lt hz)
  · -- upper bound: gridIndex m a ≤ gridBound m C
    have hz : (gridIndex m a : ℝ) < (gridBound m C : ℝ) := by
      have h1 : (gridIndex m a : ℝ) ≤ a * (m : ℝ) := by
        unfold gridIndex
        exact Int.floor_le (a * (m : ℝ))
      have h2 : a * (m : ℝ) ≤ |a| * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self a) (le_of_lt hm)
      have h3 : |a| * (m : ℝ) ≤ C * (m : ℝ) :=
        mul_le_mul_of_nonneg_right ha (le_of_lt hm)
      have h4 : C * (m : ℝ) < (Int.ceil (C * (m : ℝ)) : ℝ) + 1 := by
        have h4a : C * (m : ℝ) ≤ (Int.ceil (C * (m : ℝ)) : ℝ) := Int.le_ceil (C * (m : ℝ))
        nlinarith
      calc
        (gridIndex m a : ℝ) ≤ a * (m : ℝ) := h1
        _ ≤ |a| * (m : ℝ) := h2
        _ ≤ C * (m : ℝ) := h3
        _ < (Int.ceil (C * (m : ℝ)) : ℝ) + 1 := h4
        _ = (gridBound m C : ℝ) := by
          unfold gridBound
          norm_num [Int.cast_add]
    exact_mod_cast (le_of_lt hz)

private lemma gridIndex_sub_lt {m : ℕ} {a : ℝ} (hm : 0 < (m : ℝ)) :
    |gridIndex m a / (m : ℝ) - a| < 1 / (m : ℝ) := by
  have hle : (Int.floor (a * (m : ℝ)) : ℝ) ≤ a * (m : ℝ) := Int.floor_le (a * (m : ℝ))
  have hlt : a * (m : ℝ) < (Int.floor (a * (m : ℝ)) : ℝ) + 1 :=
    Int.lt_floor_add_one (a * (m : ℝ))
  have hnon : 0 ≤ a * (m : ℝ) - (Int.floor (a * (m : ℝ)) : ℝ) := sub_nonneg.mpr hle
  have hlt1 : a * (m : ℝ) - (Int.floor (a * (m : ℝ)) : ℝ) < 1 := by linarith
  have habs : |(Int.floor (a * (m : ℝ)) : ℝ) - a * (m : ℝ)| < 1 := by
    rw [abs_sub_comm, abs_of_nonneg hnon]
    exact hlt1
  -- |⌊a*m⌋/m − a| = |⌊a*m⌋ − a*m| / m
  have hre : |(gridIndex m a : ℝ) / (m : ℝ) - a| =
      |(Int.floor (a * (m : ℝ)) : ℝ) - a * (m : ℝ)| / (m : ℝ) := by
    unfold gridIndex
    have h : (Int.floor (a * (m : ℝ)) : ℝ) / (m : ℝ) - a =
        ((Int.floor (a * (m : ℝ)) : ℝ) - a * (m : ℝ)) / (m : ℝ) := by
      field_simp [ne_of_gt hm]
    simp [h, abs_div, abs_of_pos hm]
  rw [hre]
  -- |x| / m < 1 / m from |x| < 1 and 0 < m
  apply (lt_div_iff₀ hm).mpr
  rw [div_mul_cancel₀ _ (ne_of_gt hm)]
  exact habs

/--
The complex-valued simple approximation theorem: a bounded measurable
complex-valued function on a measurable space is the uniform limit of a sequence of
simple functions.

Mathlib's `MeasureTheory.StronglyMeasurable.approxBounded` gives an almost
everywhere *pointwise* approximation by bounded simple functions; the uniform
statement below is genuinely stronger and is proved by slicing the (bounded) range
of `f` into finitely many pieces of diameter `< 1/n`.

Blueprint reference: `thrm:complex-valued-simple-approximation-theorem`.
-/
theorem exists_simpleFunc_tendstoUniformly {X : Type*} [MeasurableSpace X] {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) :
    ∃ s : ℕ → MeasureTheory.SimpleFunc X ℂ,
      TendstoUniformly (fun n x => s n x) f atTop := by
  rcases hf with ⟨hmeas, C, hC⟩
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right C 0
  have hC0' : ∀ x, ‖f x‖ ≤ C0 := fun x => le_trans (hC x) (le_max_left C 0)
  let s : ℕ → MeasureTheory.SimpleFunc X ℂ := fun n => by
    let m : ℕ := n + 1
    have hm : 0 < (m : ℝ) := by
      simp [m]
      exact_mod_cast (Nat.succ_pos n)
    refine MeasureTheory.SimpleFunc.mk (fun x : X => gridVal m (gridIndex m ((f x).re)) (gridIndex m ((f x).im))) ?fiber ?finite
    · -- measurable fibres: the pair of grid indices is measurable into the
      -- discrete space ℤ × ℤ, and the grid-value map is measurable from it
      intro y
      have hp : Measurable (fun x : X => (gridIndex m ((f x).re), gridIndex m ((f x).im))) := by
        refine Measurable.prod ?h1 ?h2
        · have hre : Measurable (fun x : X => (f x).re) := Complex.measurable_re.comp hmeas
          exact Int.measurable_floor.comp (hre.mul_const (m : ℝ))
        · have him : Measurable (fun x : X => (f x).im) := Complex.measurable_im.comp hmeas
          exact Int.measurable_floor.comp (him.mul_const (m : ℝ))
      change MeasurableSet
        ((fun t : ℤ × ℤ => gridVal m t.1 t.2) ∘
          (fun x : X => (gridIndex m ((f x).re), gridIndex m ((f x).im))) ⁻¹' {y})
      rw [Set.preimage_comp]
      exact hp (by measurability)
    · -- finite range: indices lie in the box, which is finite
      let K : ℤ := gridBound m C0
      let I : Finset (ℤ × ℤ) := (Finset.Icc (-K) K).product (Finset.Icc (-K) K)
      have hbox : ∀ x : X,
          (gridIndex m ((f x).re), gridIndex m ((f x).im)) ∈ I := by
        intro x
        have hx1 : |(f x).re| ≤ C0 := le_trans (Complex.abs_re_le_norm (f x)) (hC0' x)
        have hx2 : |(f x).im| ≤ C0 := le_trans (Complex.abs_im_le_norm (f x)) (hC0' x)
        exact Finset.mem_product.mpr ⟨by simpa [K] using gridIndex_mem_Icc hC0 hx1 hm,
          by simpa [K] using gridIndex_mem_Icc hC0 hx2 hm⟩
      have hIm : Set.range (fun x : X =>
          gridVal m (gridIndex m ((f x).re)) (gridIndex m ((f x).im))) ⊆
          (fun t : ℤ × ℤ => gridVal m t.1 t.2) '' (I : Set (ℤ × ℤ)) := by
        rintro z ⟨x, rfl⟩
        exact ⟨(gridIndex m ((f x).re), gridIndex m ((f x).im)), hbox x, rfl⟩
      exact (Set.Finite.image (fun t : ℤ × ℤ => gridVal m t.1 t.2)
        (Finset.finite_toSet I)).subset hIm
  refine ⟨s, ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  -- uniform bound: ‖s n x - f x‖ < 2 / (n + 1)
  have hbnd : ∀ n x, ‖s n x - f x‖ < (2 : ℝ) / ((n : ℝ) + 1) := by
    intro n x
    let m : ℕ := n + 1
    have hm : 0 < (m : ℝ) := by
      simp [m]
      exact_mod_cast (Nat.succ_pos n)
    let e : ℂ := s n x - f x
    have hre : |e.re| < 1 / (m : ℝ) := by
      have h1 := gridIndex_sub_lt (m := m) (a := (f x).re) hm
      simpa [e, s, m, gridVal, gridIndex, Complex.sub_re] using h1
    have him : |e.im| < 1 / (m : ℝ) := by
      have h2 := gridIndex_sub_lt (m := m) (a := (f x).im) hm
      simpa [e, s, m, gridVal, gridIndex, Complex.sub_im] using h2
    calc
      ‖s n x - f x‖ ≤ |e.re| + |e.im| := by
        simpa [e] using Complex.norm_le_abs_re_add_abs_im (s n x - f x)
      _ < 1 / (m : ℝ) + 1 / (m : ℝ) := add_lt_add hre him
      _ = (2 : ℝ) / ((n : ℝ) + 1) := by
        simp [m]
        ring
  -- 2 / (n+1) → 0
  have hcv : Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [one_div, div_eq_mul_inv] using h1.const_mul (2 : ℝ)
  -- eventually 2 / (n+1) < ε
  have hεev : ∀ᶠ n : ℕ in atTop, (2 : ℝ) / ((n : ℝ) + 1) < ε := by
    rw [Metric.tendsto_atTop] at hcv
    rcases hcv ε hε with ⟨N, hN⟩
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hlt : dist ((2 : ℝ) / ((n : ℝ) + 1)) 0 < ε := hN n hn
    have hn1 : 0 < ((n : ℝ) + 1) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      linarith
    have hpos : 0 ≤ (2 : ℝ) / ((n : ℝ) + 1) := div_nonneg (by norm_num) (le_of_lt hn1)
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_div, abs_of_nonneg hpos, abs_of_pos hn1] using hlt
  filter_upwards [hεev] with n hn
  intro x
  calc
    dist (f x) (s n x) = ‖s n x - f x‖ := by rw [dist_comm, dist_eq_norm]
    _ < (2 : ℝ) / ((n : ℝ) + 1) := hbnd n x
    _ < ε := hn

/--
The monotone convergence theorem for real sequences: a monotone sequence of reals
has a finite limit if and only if it is bounded.

Blueprint reference: `thrm:monotone-convergence-theorem`.
-/
theorem tendsto_iff_isBounded_of_monotone {a : ℕ → ℝ} (ha : Monotone a) :
    (∃ L : ℝ, Tendsto a atTop (𝓝 L)) ↔ Bornology.IsBounded (Set.range a) :=
  ⟨fun ⟨_, hL⟩ => Metric.isBounded_range_of_tendsto a hL,
    fun hb => ⟨⨆ i, a i, tendsto_atTop_ciSup ha hb.bddAbove⟩⟩

/--
The monotone convergence theorem for real sequences, decreasing case.

Blueprint reference: `thrm:monotone-convergence-theorem`.
-/
theorem tendsto_iff_isBounded_of_antitone {a : ℕ → ℝ} (ha : Antitone a) :
    (∃ L : ℝ, Tendsto a atTop (𝓝 L)) ↔ Bornology.IsBounded (Set.range a) :=
  ⟨fun ⟨_, hL⟩ => Metric.isBounded_range_of_tendsto a hL,
    fun hb => ⟨⨅ i, a i, tendsto_atTop_ciInf ha hb.bddBelow⟩⟩

/-!
### Uniformly bounded pointwise limits

Almost every convergence argument in this directory — the extension of the
functional calculus from continuous to bounded Borel functions, the monotone-class
bootstrap, and the bounded convergence theorem for the measures `μ_ψ` — feeds on
the same package of hypotheses on a sequence `f : ℕ → α → ℂ`: a single bound `M`
valid for all indices and all points, plus pointwise convergence to a limit `g`.
It is named once here and reused, rather than respelled as a pair of binders in
each signature.
-/

/--
`BoundedPointwiseLimit f g b` says that the sequence of complex-valued functions
`f : ℕ → α → ℂ` is dominated by `b` **uniformly in the index** and converges to `g`
**pointwise** (not uniformly: the rate of convergence may depend on the point).

The dominating function `b` is almost always a constant `fun _ => M`; it is allowed
to vary so that the same structure covers the quadratic bound
`fun φ => C * ‖φ‖ ^ 2` used for families of quadratic forms in
`Physicslib4/Spectral/Forms.lean`.
-/
structure BoundedPointwiseLimit {α : Type*} (f : ℕ → α → ℂ) (g : α → ℂ) (b : α → ℝ) : Prop where
  /-- The sequence is dominated by `b`, uniformly in the index. -/
  norm_le : ∀ n x, ‖f n x‖ ≤ b x
  /-- The sequence converges to `g` pointwise. -/
  tendsto : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))

/--
A pointwise limit of measurable complex-valued functions is measurable.

Blueprint reference: `lmm:pointwise-limits-of-borel-measurable-functions` (first
half).
-/
theorem measurable_of_tendsto_pointwise {X : Type*} [MeasurableSpace X] {f : ℕ → X → ℂ}
    {g : X → ℂ} (hmeas : ∀ i, Measurable (f i))
    (hlim : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (g x))) : Measurable g :=
  measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr hlim)

/--
A pointwise limit of a uniformly bounded sequence of functions obeys the same bound.

Blueprint reference: `lmm:pointwise-limits-of-borel-measurable-functions` (second
half).
-/
theorem norm_le_of_tendsto {α : Type*} {f : ℕ → α → ℂ} {g : α → ℂ} {b : α → ℝ}
    (h : BoundedPointwiseLimit f g b) (x : α) : ‖g x‖ ≤ b x :=
  le_of_tendsto ((h.tendsto x).norm) (Eventually.of_forall fun n => h.norm_le n x)

/--
The bounded convergence theorem: on a space of finite measure, the integrals of a
uniformly bounded sequence of measurable complex-valued functions converge to the
integral of its pointwise limit.

This is the constant-dominating-function case of Mathlib's
`MeasureTheory.tendsto_integral_of_dominated_convergence`; the constant is
integrable precisely because `μ` is finite, which is the blueprint's hypothesis
`μ(X) < ∞`. Measurability of each `f i` is carried explicitly: the blueprint leaves
it implicit in writing `∫_X f_i dμ`, but the integral is only defined with it.

Blueprint reference: `thrm:bounded-convergence-theorem`.
-/
theorem tendsto_integral_of_boundedPointwiseLimit {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsFiniteMeasure μ] {f : ℕ → X → ℂ} {g : X → ℂ}
    {M : ℝ} (hmeas : ∀ i, Measurable (f i)) (h : BoundedPointwiseLimit f g fun _ => M) :
    Tendsto (fun i => ∫ x, f i x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ : X => M)
  · exact fun i => (hmeas i).aestronglyMeasurable
  · exact MeasureTheory.integrable_const M
  · intro i
    filter_upwards with x
    exact h.norm_le i x
  · filter_upwards with x
    exact h.tendsto x

/-!
### Complex analysis prerequisites
-/

/--
Laurent's theorem: a function holomorphic on an open annulus admits a unique
expansion there as a Laurent series.

Blueprint reference: `thrm:laurents-theorem`.
-/
theorem exists_unique_laurentSeries {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z : ℂ | r < ‖z - c‖ ∧ ‖z - c‖ < R}) :
    ∃! a : ℤ → ℂ, ∀ z : ℂ, r < ‖z - c‖ → ‖z - c‖ < R →
      HasSum (fun n : ℤ => a n * (z - c) ^ n) (f z) := by
  sorry

end Spectral
end Physicslib4
