/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Physicslib4.Spectral.SpectralTheorem
import Physicslib4.Spectral.Unbounded.Integral

/-!
# Bounded normal operators

The Cayley transform turns an unbounded self-adjoint operator into a bounded operator
that is normal but not self-adjoint, so the spectral theorem is needed for bounded
*normal* operators. This file carries out the first stage: the continuous functional
calculus for a bounded normal operator, built through a two-variable spectral mapping
theorem for polynomials in `A` and `A*`.

A normal operator is Mathlib's `IsStarNormal`. A polynomial in two variables is an
`MvPolynomial (Fin 2) ℂ`; substituting `A` for the first variable and `A*` for the second
is `mvApply`, defined coefficientwise (so no commutativity of the target algebra is
required), and the corresponding scalar function `λ ↦ p(λ, conj λ)` is `mvEvalConj`.

## Main definitions

* `mvApply`, `mvEvalConj`, `mvPolyOn` — polynomials in `A` and `A*`.
* `spectralSubspace` — the range of a spectral projection.
* `IsAlmostEigenvector` — the blueprint's `ε`-almost eigenvector.
* `normalCalculus` — the continuous functional calculus of a normal operator.

## Main statements

* `norm_eq_sSup_dual` — the norm via the dual pairing.
* `tendsto_norm_pow_div_atTop`, `spectralRadius_mul_le_of_commute` — power growth and the
  spectral radius of a commuting product.
* `mapsTo_pvmOperator_spectralSubspace`, `norm_sub_smul_le_of_mem_spectralSubspace`,
  `spectralSubspace_ne_bot` — properties of spectral subspaces.
* `commute_borelCalculus`, `mapsTo_spectralSubspace_of_commute` — commuting operators
  preserve spectral subspaces.
* `norm_adjoint_sub_smul_apply`, `isAlmostEigenvector_adjoint`,
  `mem_spectrum_iff_forall_isAlmostEigenvector` — almost eigenvectors.
* `spectrum_mvApply` — the two-variable spectral mapping theorem.
* `norm_mvApply` — the norm of a polynomial in `A` and `A*`.
* `existsUnique_normalCalculus` and the property lemmas — the continuous functional
  calculus for a normal operator.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### Polynomials in `A` and `A*`
-/

/--
Substitution of `A` for `λ` and `A*` for `conj λ` in a two-variable polynomial. It is
defined coefficientwise, so it needs no commutativity in `𝓑(H)`; the point of normality
is that this assignment is then multiplicative, which is
`normalCalculus_mul` below.

Blueprint reference: the substitution `p ↦ p(A, A*)` of `lmm:polynomials-in-normal-are-normal`.
-/
noncomputable def mvApply (A : H →L[ℂ] H) (p : MvPolynomial (Fin 2) ℂ) : H →L[ℂ] H :=
  ∑ d ∈ p.support, MvPolynomial.coeff d p • (A ^ d 0 * (ContinuousLinearMap.adjoint A) ^ d 1)

/--
The scalar function `λ ↦ p(λ, conj λ)` attached to a two-variable polynomial.
-/
noncomputable def mvEvalConj (p : MvPolynomial (Fin 2) ℂ) (lam : ℂ) : ℂ :=
  ∑ d ∈ p.support, MvPolynomial.coeff d p * lam ^ d 0 * (starRingEnd ℂ lam) ^ d 1

/-!
### Norm and spectral radius
-/

/--
The norm of a vector is recovered by pairing it with the unit ball of the dual space:
`‖x‖ = sup {|ξ x| : ξ ∈ V*, ‖ξ‖ ≤ 1}`.

Mathlib has the two halves (`NormedSpace.norm_le_dual_bound` and the Hahn–Banach
`exists_dual_vector''`) but not the supremum form.

Blueprint reference: `thrm:norm-via-dual-pairing`.
-/
theorem norm_eq_sSup_dual {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (x : V) :
    ‖x‖ = sSup ((fun ξ : StrongDual 𝕜 V => ‖ξ x‖) '' Metric.closedBall 0 1) := by
  have hle : ∀ y ∈ (fun ξ : StrongDual 𝕜 V => ‖ξ x‖) '' Metric.closedBall 0 1, y ≤ ‖x‖ := by
    rintro _ ⟨ξ, hξ, rfl⟩
    rw [mem_closedBall_zero_iff] at hξ
    exact (ξ.le_opNorm x).trans (by nlinarith [norm_nonneg x])
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' 𝕜 x
  refine le_antisymm (le_csSup ⟨‖x‖, hle⟩ ⟨g, mem_closedBall_zero_iff.2 hg, ?_⟩)
    (csSup_le ⟨_, 0, Metric.mem_closedBall_self zero_le_one, rfl⟩ hle)
  simp [hgx]

/--
Powers of a bounded operator grow no faster than the spectral radius allows: if
`R(A) < T` then `‖Aᵐ‖ / Tᵐ → 0`.

The blueprint's standing hypothesis `H ≠ {0}`, needed there for `σ(A)` to be non-empty and
hence `R(A)` to be a supremum over a non-empty set, is `Nontrivial H`.

Blueprint reference: `lmm:power-growth-controlled-by-spectral-radius`.
-/
theorem tendsto_norm_pow_div_atTop (A : H →L[ℂ] H) {T : ℝ} (hT : 0 < T)
    (hRT : spectralRadius ℂ A < ENNReal.ofReal T) :
    Tendsto (fun m : ℕ => ‖A ^ m‖ / T ^ m) atTop (𝓝 0) := by
  have hr : ENNReal.ofReal (spectralRadius ℂ A).toReal = spectralRadius ℂ A :=
    ENNReal.ofReal_toReal hRT.ne_top
  have hrT : (spectralRadius ℂ A).toReal < T := by
    rw [← hr] at hRT; exact (ENNReal.ofReal_lt_ofReal_iff hT).1 hRT
  obtain ⟨S, hS0, hrS, hST⟩ : ∃ S : ℝ, 0 < S ∧ (spectralRadius ℂ A).toReal < S ∧ S < T :=
    ⟨((spectralRadius ℂ A).toReal + T) / 2,
      by linarith [ENNReal.toReal_nonneg (a := spectralRadius ℂ A)], by linarith, by linarith⟩
  have hS : spectralRadius ℂ A < ENNReal.ofReal S := by
    rw [← hr]; exact (ENNReal.ofReal_lt_ofReal_iff hS0).2 hrS
  have hev :=
    (tendsto_order.1 (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A)).2 _ hS
  refine squeeze_zero' (Eventually.of_forall fun m => by positivity) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hT).2 hST))
  filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
  rw [div_pow, div_le_div_iff_of_pos_right (by positivity)]
  have h1 := ((ENNReal.ofReal_lt_ofReal_iff' ).1 hm).1
  calc ‖A ^ m‖ = (‖A ^ m‖ ^ (1 / m : ℝ)) ^ m := by
        rw [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) (by omega)]
    _ ≤ S ^ m := pow_le_pow_left₀ (by positivity) h1.le m

/--
The spectral radius is submultiplicative on commuting operators.

Blueprint reference: `lmm:hall-10.22`.
-/
theorem spectralRadius_mul_le_of_commute [Nontrivial H] {A B : H →L[ℂ] H} (h : Commute A B) :
    spectralRadius ℂ (A * B) ≤ spectralRadius ℂ A * spectralRadius ℂ B := by
  have hfin : ∀ C : H →L[ℂ] H, spectralRadius ℂ C ≠ ⊤ := fun C =>
    ((spectrum.spectralRadius_le_nnnorm C).trans_lt ENNReal.coe_lt_top).ne
  refine le_of_tendsto_of_tendsto' (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius _)
    (ENNReal.Tendsto.mul (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A)
      (Or.inr (hfin B)) (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius B)
      (Or.inr (hfin A))) fun m => ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    h.mul_pow]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (norm_nonneg _) (norm_mul_le _ _) (by positivity))

/-!
### Spectral subspaces
-/

section SpectralSubspace

variable {X : Type*} [MeasurableSpace X]

/--
The spectral subspace attached to a measurable set `E` by a projection-valued measure: the
range of the projection `μ E`. It is a closed subspace of `H`
(`isClosed_range_of_isStarProjection`), hence itself a Hilbert space.

Blueprint reference: `def:hall-7.14`.
-/
def spectralSubspace (μ : ProjectionValuedMeasure X H) (E : Set X) : Submodule ℂ H :=
  LinearMap.range ((μ E : H →L[ℂ] H) : H →ₗ[ℂ] H)

end SpectralSubspace

/--
The bounded operator `∫ ι dμ` attached to a projection-valued measure on a compact subset
`Y ⊆ ℂ`, where `ι` is the inclusion `Y ↪ ℂ`.

Blueprint reference: `prpstn:hall-7.15`.
-/
noncomputable def pvmOperator {Y : Set ℂ} (μ : ProjectionValuedMeasure Y H) : H →L[ℂ] H :=
  μ.integral fun y : Y => (y : ℂ)

/-- The inclusion `Y ↪ ℂ` of a compact set is bounded and measurable. -/
theorem coe_mem_bddMeasurable {Y : Set ℂ} (hY : IsCompact Y) :
    (fun y : Y => (y : ℂ)) ∈ BddMeasurable Y := by
  obtain ⟨C, hC⟩ := hY.isBounded.exists_norm_le
  exact ⟨measurable_subtype_coe, C, fun y => hC y y.2⟩

/-- The indicator function of a measurable set is bounded and measurable. -/
theorem indicator_one_mem_bddMeasurable {X : Type*} [MeasurableSpace X] {E : Set X}
    (hE : MeasurableSet E) : E.indicator (1 : X → ℂ) ∈ BddMeasurable X := by
  refine ⟨measurable_const.indicator hE, 1, fun x => ?_⟩
  by_cases hx : x ∈ E <;> simp [hx]

/-- Bounded measurable functions are closed under products. -/
private theorem bddMeasurable_mul {X : Type*} [MeasurableSpace X] {u v : X → ℂ}
    (hu : u ∈ BddMeasurable X) (hv : v ∈ BddMeasurable X) : u * v ∈ BddMeasurable X :=
  let ⟨hu, Cu, hCu⟩ := hu
  let ⟨hv, Cv, hCv⟩ := hv
  ⟨hu.mul hv, Cu * Cv, fun x => by
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hCu x) (hCv x) (norm_nonneg _) ((norm_nonneg _).trans (hCu x))⟩

/-- `∫ (ι - λ₀) dμ = ∫ ι dμ - λ₀ 1`. -/
theorem integral_coe_sub_const {Y : Set ℂ} (hY : IsCompact Y)
    (μ : ProjectionValuedMeasure Y H) (lam₀ : ℂ) :
    μ.integral (fun y : Y => (y : ℂ) - lam₀) = pvmOperator μ - lam₀ • (1 : H →L[ℂ] H) := by
  have h1 : (1 : Y → ℂ) ∈ BddMeasurable Y := ⟨measurable_const, 1, fun _ => by simp⟩
  have h : (fun y : Y => (y : ℂ) - lam₀) = (fun y : Y => (y : ℂ)) + (-lam₀) • (1 : Y → ℂ) := by
    ext y; simp [sub_eq_add_neg]
  rw [h, μ.integral_add (coe_mem_bddMeasurable hY) ((BddMeasurable Y).smul_mem _ h1),
    μ.integral_smul _ h1, μ.integral_one, pvmOperator, neg_smul, ← sub_eq_add_neg]

/--
Each spectral subspace is invariant under `∫ ι dμ`.

Blueprint reference: `prpstn:hall-7.15` (Part 1).
-/
theorem mapsTo_pvmOperator_spectralSubspace {Y : Set ℂ} (hY : IsCompact Y)
    (μ : ProjectionValuedMeasure Y H) (E : Set Y) (ψ : H) (hψ : ψ ∈ spectralSubspace μ E) :
    pvmOperator μ ψ ∈ spectralSubspace μ E := by
  obtain ⟨φ, rfl⟩ := hψ
  by_cases hE : MeasurableSet E
  · have hcomm : pvmOperator μ * μ E = μ E * pvmOperator μ := by
      rw [pvmOperator, ← μ.integral_indicator hE, ← μ.integral_mul (coe_mem_bddMeasurable hY)
        (indicator_one_mem_bddMeasurable hE), ← μ.integral_mul
        (indicator_one_mem_bddMeasurable hE) (coe_mem_bddMeasurable hY), mul_comm]
    exact ⟨pvmOperator μ φ, by simpa using (congrArg (· φ) hcomm).symm⟩
  · simp [μ.apply_of_not_measurableSet hE]

/--
If `E` sits in the closed `ε`-disc about `λ₀`, then `‖(A - λ₀ 1) ψ‖ ≤ ε ‖ψ‖` on the
corresponding spectral subspace.

Blueprint reference: `prpstn:hall-7.15` (Part 2).
-/
theorem norm_sub_smul_le_of_mem_spectralSubspace {Y : Set ℂ} (hY : IsCompact Y)
    (μ : ProjectionValuedMeasure Y H) {E : Set Y} {lam₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hE : ∀ y ∈ E, ‖(y : ℂ) - lam₀‖ ≤ ε) {ψ : H} (hψ : ψ ∈ spectralSubspace μ E) :
    ‖(pvmOperator μ - lam₀ • (1 : H →L[ℂ] H)) ψ‖ ≤ ε * ‖ψ‖ := by
  obtain ⟨φ, rfl⟩ := hψ
  by_cases hEm : MeasurableSet E
  · have hf : (fun y : Y => (y : ℂ) - lam₀) ∈ BddMeasurable Y :=
      (BddMeasurable Y).sub_mem (coe_mem_bddMeasurable hY)
        (⟨measurable_const, ‖lam₀‖, fun _ => le_rfl⟩ : (fun _ : Y => lam₀) ∈ BddMeasurable Y)
    have hidem : μ E (μ E φ) = μ E φ := by
      simpa using congrArg (· φ) (μ.isStarProjection_apply E).isIdempotentElem.eq
    have key : (pvmOperator μ - lam₀ • (1 : H →L[ℂ] H)) (μ E φ) =
        μ.integral ((fun y : Y => (y : ℂ) - lam₀) * E.indicator 1) (μ E φ) := by
      rw [μ.integral_mul hf (indicator_one_mem_bddMeasurable hEm), μ.integral_indicator hEm,
        integral_coe_sub_const hY, mul_def, comp_apply, hidem]
    change ‖(pvmOperator μ - lam₀ • (1 : H →L[ℂ] H)) (μ E φ)‖ ≤ ε * ‖μ E φ‖
    rw [key]
    refine (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (μ.norm_integral_le (bddMeasurable_mul hf (indicator_one_mem_bddMeasurable hEm))).trans
      (Real.iSup_le (fun y => ?_) hε.le)
    by_cases hy : y ∈ E
    · simpa [hy] using hE y hy
    · simp [hy, hε.le]
  · simp [μ.apply_of_not_measurableSet hEm]

/--
Spectral subspaces attached to neighbourhoods of a spectral point are non-trivial.

Blueprint reference: `prpstn:hall-7.15` (Part 3).
-/
theorem spectralSubspace_ne_bot {Y : Set ℂ} (hY : IsCompact Y)
    (μ : ProjectionValuedMeasure Y H) {lam₀ : ℂ} (hlam : lam₀ ∈ spectrum ℂ (pvmOperator μ))
    {U : Set ℂ} (hU : IsOpen U) (hlamU : lam₀ ∈ U) :
    spectralSubspace μ {y : Y | (y : ℂ) ∈ U} ≠ ⊥ := by
  classical
  intro hbot
  set U' : Set Y := {y : Y | (y : ℂ) ∈ U}
  have hU' : MeasurableSet U' := measurable_subtype_coe hU.measurableSet
  have hμ : μ U' = 0 := by
    ext ψ
    have hmem : μ U' ψ ∈ spectralSubspace μ U' := ⟨ψ, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU lam₀ hlamU
  let f : Y → ℂ := fun y => (y : ℂ) - lam₀
  let g : Y → ℂ := fun y => if (y : ℂ) ∈ U then 0 else ((y : ℂ) - lam₀)⁻¹
  have hf : f ∈ BddMeasurable Y :=
    (BddMeasurable Y).sub_mem (coe_mem_bddMeasurable hY)
      (⟨measurable_const, ‖lam₀‖, fun _ => le_rfl⟩ : (fun _ : Y => lam₀) ∈ BddMeasurable Y)
  have hg : g ∈ BddMeasurable Y := by
    refine ⟨Measurable.ite hU' measurable_const
      ((measurable_subtype_coe.sub_const _).inv), ε⁻¹, fun y => ?_⟩
    by_cases hy : (y : ℂ) ∈ U
    · simp [g, hy, hε.le]
    · have hd : ε ≤ ‖(y : ℂ) - lam₀‖ := by
        by_contra hlt
        exact hy (hball (by rw [Metric.mem_ball, dist_eq_norm]; linarith))
      simp only [g, hy, if_false, norm_inv]
      exact inv_anti₀ hε hd
  have hfun : f * g + U'.indicator 1 = 1 := by
    ext y
    by_cases hy : (y : ℂ) ∈ U
    · simp [g, U', hy]
    · have hne : (y : ℂ) - lam₀ ≠ 0 := by
        intro h0
        exact hy (by rw [sub_eq_zero.mp h0]; exact hlamU)
      simp [f, g, U', hy, hne]
  have hfg : μ.integral f * μ.integral g = 1 := by
    have hsum := congrArg μ.integral hfun
    rw [μ.integral_add (bddMeasurable_mul hf hg) (indicator_one_mem_bddMeasurable hU'),
      μ.integral_indicator hU', hμ, add_zero, μ.integral_one, μ.integral_mul hf hg] at hsum
    exact hsum
  have hgf : μ.integral g * μ.integral f = 1 := by
    rw [← μ.integral_mul hg hf, mul_comm, μ.integral_mul hf hg, hfg]
  have hT : IsUnit (pvmOperator μ - lam₀ • (1 : H →L[ℂ] H)) := by
    rw [← integral_coe_sub_const hY]
    exact isUnit_iff_exists.mpr ⟨μ.integral g, hfg, hgf⟩
  apply spectrum.mem_iff.mp hlam
  have hneg : algebraMap ℂ (H →L[ℂ] H) lam₀ - pvmOperator μ =
      -(pvmOperator μ - lam₀ • (1 : H →L[ℂ] H)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  rw [hneg]
  exact hT.neg

/--
An operator commuting with a bounded self-adjoint `A` commutes with the whole bounded
Borel functional calculus of `A`.

Blueprint reference: `prpstn:hall-7.16` (Part 1).
-/
theorem commute_borelCalculus {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    {B : H →L[ℂ] H} (hB : Commute A B) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) : Commute (borelCalculus hA f) B := by
  -- off the diagonal, the polarization of `Q_h` is the matrix element of `h(A)`
  have hpol_inner : ∀ (h : spectrum ℝ A → ℂ) (hh : h ∈ BddMeasurable (spectrum ℝ A))
      (φ ψ : H), polarization (borelForm hA h) φ ψ = ⟪φ, borelCalculus hA h ψ⟫_ℂ := by
    intro h hh φ ψ
    let hQ : IsBoundedQuadraticForm (borelForm hA h) := isBoundedQuadraticForm_borelForm hA hh
    have hcalc : borelCalculus hA h = hQ.toOperator :=
      hQ.eq_toOperator (fun ζ => (inner_borelCalculus hA hh ζ).symm)
    calc
      polarization (borelForm hA h) φ ψ = hQ.toSesq φ ψ := by simp
      _ = ⟪φ, hQ.toOperator ψ⟫_ℂ := by
        rw [IsBoundedQuadraticForm.toOperator, ContinuousLinearMap.adjoint_inner_right,
          InnerProductSpace.continuousLinearMapOfBilin_apply]
      _ = ⟪φ, borelCalculus hA h ψ⟫_ℂ := by rw [hcalc]
  -- on continuous real functions the Borel calculus is the continuous calculus
  have bridge : ∀ g : C(spectrum ℝ A, ℝ),
      borelCalculus hA (fun l => ((g l : ℝ) : ℂ)) = realCalculus hA g := by
    intro g
    have hgc := (continuous_mem_FClass hA g).1
    let hQ := isBoundedQuadraticForm_borelForm hA hgc
    refine (hQ.eq_toOperator (fun ψ => (inner_borelCalculus hA hgc ψ).symm)).trans
      (hQ.eq_toOperator fun ψ => ?_).symm
    rw [borelForm]
    norm_cast
    exact (integral_assocMeasure hA ψ g).symm
  have hgen : IsBorelGenerating
      {h : spectrum ℝ A → ℂ | h ∈ BddMeasurable (spectrum ℝ A) ∧
        Commute (borelCalculus hA h) B} :=
    { bddMeasurable := fun h hh => hh.1
      smul_add_mem := by
        rintro α β g k ⟨hg, hgB⟩ ⟨hk, hkB⟩
        have hαg := (BddMeasurable (spectrum ℝ A)).smul_mem α hg
        have hβk := (BddMeasurable (spectrum ℝ A)).smul_mem β hk
        refine ⟨(BddMeasurable (spectrum ℝ A)).add_mem hαg hβk, ?_⟩
        rw [borelCalculus_add hA hαg hβk, borelCalculus_smul hA α hg,
          borelCalculus_smul hA β hk]
        exact (hgB.smul_left α).add_left (hkB.smul_left β)
      continuous_mem := fun g => ⟨(continuous_mem_FClass hA g).1, by
        rw [bridge g]
        exact IsSelfAdjoint.commute_cfcHom hA hA hB g⟩
      tendsto_mem := by
        intro fs g M hfs hlim
        have hg : g ∈ BddMeasurable (spectrum ℝ A) :=
          ⟨measurable_of_tendsto_pointwise (fun n => (hfs n).1.1) hlim.tendsto,
            ⟨M, fun x => norm_le_of_tendsto hlim x⟩⟩
        refine ⟨hg, ?_⟩
        have hlimit : ∀ φ ψ : H, Tendsto (fun n => ⟪φ, borelCalculus hA (fs n) ψ⟫_ℂ) atTop
            (𝓝 ⟪φ, borelCalculus hA g ψ⟫_ℂ) := by
          intro φ ψ
          rw [← hpol_inner g hg]
          exact (tendsto_polarization_borelForm hA (fun n => (hfs n).1.1) hlim φ ψ).congr
            fun n => hpol_inner (fs n) (hfs n).1 φ ψ
        refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
        have h1 := hlimit φ (B ψ)
        have h2 := hlimit (ContinuousLinearMap.adjoint B φ) ψ
        simp only [ContinuousLinearMap.adjoint_inner_left] at h2
        change ⟪φ, borelCalculus hA g (B ψ)⟫_ℂ = ⟪φ, B (borelCalculus hA g ψ)⟫_ℂ
        exact tendsto_nhds_unique h1 (h2.congr fun n =>
          congrArg (fun T : H →L[ℂ] H => ⟪φ, T ψ⟫_ℂ) (hfs n).2.eq.symm) }
  have hmem : f ∈ {h : spectrum ℝ A → ℂ | h ∈ BddMeasurable (spectrum ℝ A) ∧
      Commute (borelCalculus hA h) B} := by
    rw [hgen.eq_bddMeasurable]
    exact hf
  exact hmem.2

/--
Consequently every spectral subspace of `A` is invariant under `B`.

Blueprint reference: `prpstn:hall-7.16` (Part 2).
-/
theorem mapsTo_spectralSubspace_of_commute {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) {B : H →L[ℂ] H} (hB : Commute A B) (E : Set (spectrum ℝ A))
    (ψ : H) (hψ : ψ ∈ spectralSubspace (spectralMeasure hA) E) :
    B ψ ∈ spectralSubspace (spectralMeasure hA) E := by
  have hcomm : Commute (spectralMeasure hA E) B := by
    by_cases hE : MeasurableSet E
    · rw [spectralMeasure_apply hA hE]
      refine commute_borelCalculus hA hB ⟨?_, 1, fun l => ?_⟩
      · exact measurable_const.indicator hE
      · by_cases hl : l ∈ E <;> simp [hl]
    · rw [(spectralMeasure hA).apply_of_not_measurableSet hE]
      exact Commute.zero_left B
  obtain ⟨x, rfl⟩ := hψ
  exact ⟨B x, by simpa using congrArg (· x) hcomm.eq⟩

/-!
### Almost eigenvectors
-/

/--
For a normal `A`, the operators `A - λ 1` and `A* - conj λ 1` have the same action on
norms.

Blueprint reference: `lmm:normality-balances-norms`.
-/
theorem norm_adjoint_sub_smul_apply {A : H →L[ℂ] H} [IsStarNormal A] (lam : ℂ) (ψ : H) :
    ‖(ContinuousLinearMap.adjoint A - (starRingEnd ℂ lam) • (1 : H →L[ℂ] H)) ψ‖ =
      ‖(A - lam • (1 : H →L[ℂ] H)) ψ‖ := by
  have hadj : ContinuousLinearMap.adjoint (A - lam • (1 : H →L[ℂ] H)) =
      ContinuousLinearMap.adjoint A - (starRingEnd ℂ lam) • (1 : H →L[ℂ] H) := by
    rw [← star_eq_adjoint, ← star_eq_adjoint, star_sub, star_smul, star_one]; rfl
  have hN : IsStarNormal (A - lam • (1 : H →L[ℂ] H)) := by
    rw [isStarNormal_iff, star_eq_adjoint, hadj]
    have := (IsStarNormal.star_comm_self (x := A))
    rw [star_eq_adjoint] at this
    simp only [Commute, SemiconjBy] at this ⊢
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, this, smul_sub,
      smul_smul, mul_comm (starRingEnd ℂ lam) lam]
    abel
  rw [← hadj, ← isStarNormal_iff_norm_eq_adjoint.mp hN]

/--
An `ε`-almost eigenvector for `A` with eigenvalue `λ`: a nonzero `ψ` with
`‖(A - λ 1) ψ‖ < ε ‖ψ‖`.

Blueprint reference: `def:hall-10.24`.
-/
structure IsAlmostEigenvector (A : H →L[ℂ] H) (lam : ℂ) (ε : ℝ) (ψ : H) : Prop where
  /-- Almost eigenvectors are nonzero. -/
  ne_zero : ψ ≠ 0
  /-- The defining strict inequality. -/
  norm_lt : ‖(A - lam • (1 : H →L[ℂ] H)) ψ‖ < ε * ‖ψ‖

/--
An almost eigenvector of a normal `A` with eigenvalue `λ` is one for `A*` with eigenvalue
`conj λ`.

Blueprint reference: `lmm:hall-10.25` (Part 1).
-/
theorem isAlmostEigenvector_adjoint {A : H →L[ℂ] H} [IsStarNormal A] {lam : ℂ} {ε : ℝ}
    {ψ : H} (h : IsAlmostEigenvector A lam ε ψ) :
    IsAlmostEigenvector (ContinuousLinearMap.adjoint A) (starRingEnd ℂ lam) ε ψ :=
  ⟨h.ne_zero, (norm_adjoint_sub_smul_apply lam ψ).trans_lt h.norm_lt⟩

/--
For a normal operator, the spectrum is exactly the set of `λ` admitting `ε`-almost
eigenvectors for every `ε > 0`.

Blueprint reference: `lmm:hall-10.25` (Part 2).
-/
theorem mem_spectrum_iff_forall_isAlmostEigenvector {A : H →L[ℂ] H} [IsStarNormal A]
    (lam : ℂ) :
    lam ∈ spectrum ℂ A ↔ ∀ ε : ℝ, 0 < ε → ∃ ψ : H, IsAlmostEigenvector A lam ε ψ := by
  set N := A - lam • (1 : H →L[ℂ] H) with hNdef
  have hunit : lam ∈ spectrum ℂ A ↔ ¬IsUnit N := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub, IsUnit.neg_iff]
  rw [hunit]
  constructor
  · intro hN
    by_contra hcon
    push Not at hcon
    obtain ⟨ε, hε, hno⟩ := hcon
    have hbd : ∀ ψ : H, ε * ‖ψ‖ ≤ ‖N ψ‖ := fun ψ => by
      by_cases hψ : ψ = 0
      · simp [hψ]
      · by_contra hlt
        exact hno ψ ⟨hψ, lt_of_not_ge hlt⟩
    have hbd' : ∀ ψ : H, ε * ‖ψ‖ ≤ ‖(ContinuousLinearMap.adjoint N) ψ‖ := fun ψ => by
      have hadj : ContinuousLinearMap.adjoint N =
          ContinuousLinearMap.adjoint A - (starRingEnd ℂ lam) • (1 : H →L[ℂ] H) := by
        rw [hNdef, ← star_eq_adjoint, ← star_eq_adjoint, star_sub, star_smul, star_one]; rfl
      rw [hadj, norm_adjoint_sub_smul_apply]
      exact hbd ψ
    apply hN
    rw [ContinuousLinearMap.isUnit_iff_bijective, bijective_iff_dense_range_and_antilipschitz]
    refine ⟨?_, ⟨Real.toNNReal ε⁻¹, N.antilipschitz_of_bound fun ψ => ?_⟩⟩
    · rw [Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range,
        Submodule.eq_bot_iff]
      intro ψ hψ
      have := hbd' ψ
      have h0 : ContinuousLinearMap.adjoint N ψ = 0 := hψ
      rw [h0, norm_zero] at this
      exact norm_le_zero_iff.mp (nonpos_of_mul_nonpos_right this hε)
    · rw [Real.coe_toNNReal _ (inv_nonneg.mpr hε.le), inv_mul_eq_div, le_div_iff₀ hε, mul_comm]
      exact hbd ψ
  · intro h hN
    obtain ⟨S, hS⟩ := hN.exists_left_inv
    obtain ⟨ψ, hψ0, hψ⟩ := h (‖S‖ + 1)⁻¹ (by positivity)
    have h1 : ‖ψ‖ ≤ ‖S‖ * ‖N ψ‖ := by
      calc ‖ψ‖ = ‖S (N ψ)‖ := by simpa using congrArg (fun T : H →L[ℂ] H => ‖T ψ‖) hS.symm
        _ ≤ ‖S‖ * ‖N ψ‖ := S.le_opNorm _
    have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ0
    have h2 : ‖S‖ * ‖N ψ‖ ≤ ‖S‖ * ((‖S‖ + 1)⁻¹ * ‖ψ‖) :=
      mul_le_mul_of_nonneg_left hψ.le (norm_nonneg _)
    have h3 : ‖S‖ * ((‖S‖ + 1)⁻¹ * ‖ψ‖) < ‖ψ‖ := by
      rw [← mul_assoc, ← div_eq_mul_inv]
      have : ‖S‖ / (‖S‖ + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      nlinarith
    linarith

/--
Polynomials in `A` and `A*` turn `ε`-almost eigenvectors into `(C ε)`-almost eigenvectors,
with `C` independent of `ε` and `ψ`.

Blueprint reference: `lmm:hall-10.26`.
-/
theorem exists_const_isAlmostEigenvector_mvApply {A : H →L[ℂ] H} [IsStarNormal A]
    (p : MvPolynomial (Fin 2) ℂ) (lam : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (ψ : H), IsAlmostEigenvector A lam ε ψ →
      IsAlmostEigenvector (mvApply A p) (mvEvalConj p lam) (C * ε) ψ := by
  set N := A - lam • (1 : H →L[ℂ] H) with hNdef
  -- one more factor `X` (with `‖(X - ν) ψ‖ ≤ ‖N ψ‖`) on the right of a controlled `T`
  have step : ∀ (T X : H →L[ℂ] H) (μ ν : ℂ) (c : ℝ), 0 ≤ c →
      (∀ ψ, ‖(T - μ • (1 : H →L[ℂ] H)) ψ‖ ≤ c * ‖N ψ‖) →
      (∀ ψ, ‖(X - ν • (1 : H →L[ℂ] H)) ψ‖ ≤ ‖N ψ‖) →
      ∃ c' : ℝ, 0 ≤ c' ∧ ∀ ψ, ‖(T * X - (μ * ν) • (1 : H →L[ℂ] H)) ψ‖ ≤ c' * ‖N ψ‖ := by
    intro T X μ ν c hc hT hX
    refine ⟨‖T‖ + ‖ν‖ * c, by positivity, fun ψ => ?_⟩
    have hid : (T * X - (μ * ν) • (1 : H →L[ℂ] H)) ψ =
        T ((X - ν • (1 : H →L[ℂ] H)) ψ) + ν • (T - μ • (1 : H →L[ℂ] H)) ψ := by
      simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul, smul_sub,
        smul_smul, mul_comm ν μ]
      abel_nf
      exact add_comm _ _
    rw [hid]
    calc _ ≤ ‖T ((X - ν • (1 : H →L[ℂ] H)) ψ)‖ + ‖ν • (T - μ • (1 : H →L[ℂ] H)) ψ‖ :=
          norm_add_le _ _
      _ ≤ ‖T‖ * ‖N ψ‖ + ‖ν‖ * (c * ‖N ψ‖) := by
          rw [norm_smul]
          gcongr
          exacts [(T.le_opNorm _).trans (by gcongr; exact hX ψ), hT ψ]
      _ = _ := by ring
  have hA : ∀ ψ, ‖(A - lam • (1 : H →L[ℂ] H)) ψ‖ ≤ ‖N ψ‖ := fun ψ => le_rfl
  have hA' : ∀ ψ, ‖(ContinuousLinearMap.adjoint A - (starRingEnd ℂ lam) • (1 : H →L[ℂ] H)) ψ‖ ≤
      ‖N ψ‖ := fun ψ => (norm_adjoint_sub_smul_apply lam ψ).le
  have mono : ∀ a b : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ ψ,
      ‖(A ^ a * (ContinuousLinearMap.adjoint A) ^ b -
        (lam ^ a * (starRingEnd ℂ lam) ^ b) • (1 : H →L[ℂ] H)) ψ‖ ≤ c * ‖N ψ‖ := by
    intro a b
    induction b with
    | zero =>
      simp only [pow_zero, mul_one]
      induction a with
      | zero => exact ⟨0, le_rfl, fun ψ => by simp⟩
      | succ a ih =>
        obtain ⟨c, hc, h⟩ := ih
        simpa only [pow_succ] using step _ _ _ _ c hc h hA
    | succ b ih =>
      obtain ⟨c, hc, h⟩ := ih
      simpa only [pow_succ, ← mul_assoc] using step _ _ _ _ c hc h hA'
  have total : ∀ s : Finset (Fin 2 →₀ ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ ψ,
      ‖(∑ d ∈ s, MvPolynomial.coeff d p • (A ^ d 0 * (ContinuousLinearMap.adjoint A) ^ d 1) -
        (∑ d ∈ s, MvPolynomial.coeff d p * lam ^ d 0 * (starRingEnd ℂ lam) ^ d 1) •
          (1 : H →L[ℂ] H)) ψ‖ ≤ c * ‖N ψ‖ := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨0, le_rfl, fun ψ => by simp⟩
    | insert d s hd ih =>
      obtain ⟨c, hc, h⟩ := ih
      obtain ⟨c₁, hc₁, h₁⟩ := mono (d 0) (d 1)
      refine ⟨‖MvPolynomial.coeff d p‖ * c₁ + c, by positivity, fun ψ => ?_⟩
      rw [Finset.sum_insert hd, Finset.sum_insert hd]
      have hid : ((MvPolynomial.coeff d p • (A ^ d 0 * (ContinuousLinearMap.adjoint A) ^ d 1) +
            ∑ d ∈ s, MvPolynomial.coeff d p • (A ^ d 0 * (ContinuousLinearMap.adjoint A) ^ d 1)) -
          (MvPolynomial.coeff d p * lam ^ d 0 * (starRingEnd ℂ lam) ^ d 1 +
            ∑ d ∈ s, MvPolynomial.coeff d p * lam ^ d 0 * (starRingEnd ℂ lam) ^ d 1) •
              (1 : H →L[ℂ] H)) ψ =
          MvPolynomial.coeff d p • (A ^ d 0 * (ContinuousLinearMap.adjoint A) ^ d 1 -
            (lam ^ d 0 * (starRingEnd ℂ lam) ^ d 1) • (1 : H →L[ℂ] H)) ψ +
          (∑ d ∈ s, MvPolynomial.coeff d p • (A ^ d 0 * (ContinuousLinearMap.adjoint A) ^ d 1) -
            (∑ d ∈ s, MvPolynomial.coeff d p * lam ^ d 0 * (starRingEnd ℂ lam) ^ d 1) •
              (1 : H →L[ℂ] H)) ψ := by
        simp only [sub_apply, add_apply, smul_apply, add_smul, smul_sub, smul_smul, mul_assoc]
        abel
      rw [hid]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ ‖MvPolynomial.coeff d p‖ * (c₁ * ‖N ψ‖) + c * ‖N ψ‖ := by
          rw [norm_smul]
          gcongr
          exacts [h₁ ψ, h ψ]
        _ = _ := by ring
  obtain ⟨c, hc, h⟩ := total p.support
  refine ⟨c + 1, by positivity, fun ε ψ hψ => ⟨hψ.ne_zero, ?_⟩⟩
  have hlt := hψ.norm_lt
  have hpos : 0 < ε * ‖ψ‖ := (norm_nonneg _).trans_lt hlt
  calc ‖(mvApply A p - mvEvalConj p lam • (1 : H →L[ℂ] H)) ψ‖ ≤ c * ‖N ψ‖ := h ψ
    _ ≤ c * (ε * ‖ψ‖) := by gcongr
    _ < (c + 1) * ε * ‖ψ‖ := by nlinarith

/--
The adjoint of `p(A, A*)` is obtained by conjugating the coefficients and swapping the two
exponents.

Blueprint reference: `lmm:polynomials-in-normal-are-normal`.
-/
theorem adjoint_mvApply {A : H →L[ℂ] H} (p : MvPolynomial (Fin 2) ℂ) :
    ContinuousLinearMap.adjoint (mvApply A p) =
      ∑ d ∈ p.support, (starRingEnd ℂ (MvPolynomial.coeff d p)) •
        (A ^ d 1 * (ContinuousLinearMap.adjoint A) ^ d 0) := by
  simp only [mvApply, ← star_eq_adjoint, star_sum, star_smul, star_mul, star_pow, star_star,
    Complex.star_def]

/--
`p(A, A*)` is again normal.

Blueprint reference: `lmm:polynomials-in-normal-are-normal`.
-/
theorem isStarNormal_mvApply {A : H →L[ℂ] H} [IsStarNormal A] (p : MvPolynomial (Fin 2) ℂ) :
    IsStarNormal (mvApply A p) := by
  have hA : Commute (star A) A := IsStarNormal.star_comm_self
  have key : ∀ (c : (Fin 2 →₀ ℕ) → ℂ) (e f : (Fin 2 →₀ ℕ) → ℕ) (B : H →L[ℂ] H),
      Commute A B → Commute (star A) B →
        Commute (∑ d ∈ p.support, c d • (A ^ e d * star A ^ f d)) B :=
    fun c e f B h h' => Commute.sum_left _ _ _ fun d _ =>
      ((h.pow_left _).mul_left (h'.pow_left _)).smul_left _
  refine ⟨?_⟩
  rw [star_eq_adjoint, adjoint_mvApply, ← star_eq_adjoint]
  refine key _ _ _ _ ?_ ?_
  · exact (key _ _ _ _ (Commute.refl A) hA).symm
  · exact (key _ _ _ _ hA.symm (Commute.refl _)).symm

/--
`p(A, A*)` and its adjoint commute with `A` and with `A*`.

Blueprint reference: `lmm:polynomials-in-normal-are-normal`.
-/
theorem commute_mvApply {A : H →L[ℂ] H} [IsStarNormal A] (p : MvPolynomial (Fin 2) ℂ) :
    Commute (mvApply A p) A ∧ Commute (mvApply A p) (ContinuousLinearMap.adjoint A) ∧
      Commute (ContinuousLinearMap.adjoint (mvApply A p)) A ∧
      Commute (ContinuousLinearMap.adjoint (mvApply A p)) (ContinuousLinearMap.adjoint A) := by
  have hA : Commute (star A) A := IsStarNormal.star_comm_self
  have key : ∀ (c : (Fin 2 →₀ ℕ) → ℂ) (e f : (Fin 2 →₀ ℕ) → ℕ) (B : H →L[ℂ] H),
      Commute A B → Commute (star A) B →
        Commute (∑ d ∈ p.support, c d • (A ^ e d * star A ^ f d)) B :=
    fun c e f B h h' => Commute.sum_left _ _ _ fun d _ =>
      ((h.pow_left _).mul_left (h'.pow_left _)).smul_left _
  rw [adjoint_mvApply, mvApply, ← star_eq_adjoint]
  exact ⟨key _ _ _ _ (Commute.refl A) hA, key _ _ _ _ hA.symm (Commute.refl _),
    key _ _ _ _ (Commute.refl A) hA, key _ _ _ _ hA.symm (Commute.refl _)⟩

/--
A normal operator restricted to a nonzero closed subspace invariant under both `A` and
`A*` is again normal, with adjoint the restriction of `A*` and norm at most `‖A‖`.

Blueprint reference: `lmm:restriction-of-normal-operator`.
-/
theorem exists_restrict_isStarNormal {A : H →L[ℂ] H} [IsStarNormal A] {W : Submodule ℂ H}
    (_hW : IsClosed (W : Set H)) [CompleteSpace W] (_hne : W ≠ ⊥)
    (hAW : ∀ ψ ∈ W, A ψ ∈ W)
    (hA'W : ∀ ψ ∈ W, ContinuousLinearMap.adjoint A ψ ∈ W) :
    ∃ B : W →L[ℂ] W, (∀ ψ : W, ((B ψ : W) : H) = A (ψ : H)) ∧ IsStarNormal B ∧
      (∀ ψ : W, ((ContinuousLinearMap.adjoint B ψ : W) : H) =
        ContinuousLinearMap.adjoint A (ψ : H)) ∧ ‖B‖ ≤ ‖A‖ := by
  set B : W →L[ℂ] W := (A.comp W.subtypeL).codRestrict W fun x => hAW _ x.2
  set B' : W →L[ℂ] W :=
    ((ContinuousLinearMap.adjoint A).comp W.subtypeL).codRestrict W fun x => hA'W _ x.2
  have hadj : ContinuousLinearMap.adjoint B = B' := by
    refine ((ContinuousLinearMap.eq_adjoint_iff B' B).2 fun x y => ?_).symm
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact ContinuousLinearMap.adjoint_inner_left A (y : H) (x : H)
  refine ⟨B, fun ψ => rfl, ?_, fun ψ => by rw [hadj]; rfl, ?_⟩
  · refine ⟨?_⟩
    have hA := (isStarNormal_iff A).1 inferInstance
    ext ψ
    change ((ContinuousLinearMap.adjoint B * B) ψ : H) = ((B * ContinuousLinearMap.adjoint B) ψ : H)
    rw [hadj]
    exact congrArg (fun T : H →L[ℂ] H => T (ψ : H)) hA
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ => ?_
    exact A.le_opNorm (ψ : H)

/--
For `ν` in the spectrum of `p(A, A*)` there is, for every `ε > 0`, a nonzero closed
subspace invariant under `A` and `A*` all of whose nonzero vectors are `ε`-almost
eigenvectors for `p(A, A*)` with eigenvalue `ν`.

Blueprint reference: `lmm:hall-10.27`.
-/
theorem exists_subspace_isAlmostEigenvector {A : H →L[ℂ] H} [IsStarNormal A]
    (p : MvPolynomial (Fin 2) ℂ) {ν : ℂ} (hν : ν ∈ spectrum ℂ (mvApply A p)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ W : Submodule ℂ H, W ≠ ⊥ ∧ IsClosed (W : Set H) ∧
      (∀ ψ ∈ W, A ψ ∈ W) ∧ (∀ ψ ∈ W, ContinuousLinearMap.adjoint A ψ ∈ W) ∧
      ∀ ψ ∈ W, ψ ≠ 0 → IsAlmostEigenvector (mvApply A p) ν ε ψ := by
  set N := mvApply A p
  set B : H →L[ℂ] H := N - ν • (1 : H →L[ℂ] H) with hBdef
  set T : H →L[ℂ] H := star B * B
  set δ : ℝ := ε ^ 2 / 4
  have hδ : 0 < δ := by positivity
  have hT : IsSelfAdjoint T := IsSelfAdjoint.star_mul_self B
  obtain ⟨hNA, hNA', hN'A, hN'A'⟩ := commute_mvApply (A := A) p
  have hsN : star N = ContinuousLinearMap.adjoint N := ContinuousLinearMap.star_eq_adjoint N
  have hsB : star B = star N - star (ν • (1 : H →L[ℂ] H)) := star_sub _ _
  have hs1 : star (ν • (1 : H →L[ℂ] H)) = (starRingEnd ℂ ν) • (1 : H →L[ℂ] H) := by
    rw [star_smul, star_one]; rfl
  -- commutation of `T = B* B` with `A` and `A*`
  have hcomm : ∀ C : H →L[ℂ] H, Commute N C → Commute (star N) C → Commute T C := by
    intro C h1 h2
    have hB : Commute B C := h1.sub_left ((Commute.one_left C).smul_left ν)
    have hB' : Commute (star B) C := by
      rw [hsB, hs1]; exact h2.sub_left ((Commute.one_left C).smul_left _)
    exact hB'.mul_left hB
  have hTA : Commute T A := hcomm A hNA (hsN ▸ hN'A)
  have hTA' : Commute T (ContinuousLinearMap.adjoint A) :=
    hcomm _ hNA' (hsN ▸ hN'A')
  -- Step 1: `0 ∈ σ(B* B)`
  have hN : Commute (star N) N := (isStarNormal_iff N).1 (isStarNormal_mvApply p)
  have hBn : Commute (star B) B := by
    have h1 : Commute (star N) B := hN.sub_right ((Commute.one_right _).smul_right ν)
    have h2 : Commute (star (ν • (1 : H →L[ℂ] H))) B := by
      rw [hs1]; exact (Commute.one_left B).smul_left _
    rw [hsB]; exact h1.sub_left h2
  have h0 : (0 : ℝ) ∈ spectrum ℝ T := by
    rw [spectrum.zero_mem_iff]
    intro hu
    have hBu : IsUnit B := ((Commute.isUnit_mul_iff hBn).1 hu).2
    apply (spectrum.mem_iff.1 hν)
    have : algebraMap ℂ (H →L[ℂ] H) ν - N = -B := by
      rw [Algebra.algebraMap_eq_smul_one, hBdef, neg_sub]
    rw [this]; exact hBu.neg
  -- Step 2: the spectral subspace of `T` for `[-δ, δ]`, realised as `ker f(T)` where
  -- `f` vanishes exactly on `[-δ, δ]`; `k` is a bump at `0` witnessing non-triviality
  set g : ℝ → ℝ := fun t => max (min t δ) (-δ)
  set f : ℝ → ℝ := fun t => t - g t
  set k : ℝ → ℝ := fun t => max (δ - |t|) 0
  have hg : Continuous g := by fun_prop
  have hf : Continuous f := by fun_prop
  have hk : Continuous k := by fun_prop
  have hfk : cfc f T * cfc k T = 0 := by
    rw [← cfc_mul f k T hf.continuousOn hk.continuousOn]
    have : (fun x => f x * k x) = fun _ => (0 : ℝ) := by
      funext x
      by_cases hx : |x| < δ
      · have hgx : g x = x := by
          obtain ⟨h1, h2⟩ := abs_lt.1 hx
          simp only [g]
          rw [min_eq_left h2.le, max_eq_left h1.le]
        simp [f, hgx]
      · have : k x = 0 := max_eq_right (by linarith [not_lt.1 hx])
        simp [this]
    rw [this, cfc_const_zero]
  have hk0 : cfc k T ≠ 0 := by
    intro h
    rw [← cfc_zero ℝ T] at h
    have h' := eqOn_of_cfc_eq_cfc h hk.continuousOn continuous_zero.continuousOn hT h0
    simp only [k, abs_zero, sub_zero, Pi.zero_apply] at h'
    linarith [le_max_left δ 0]
  have hdec : T = cfc f T + cfc g T := by
    rw [← cfc_add T f g hf.continuousOn hg.continuousOn]
    simp only [f, sub_add_cancel]
    exact (cfc_id' ℝ T hT).symm
  have hgnorm : ‖cfc g T‖ ≤ δ := by
    refine norm_cfc_le hδ.le fun x _ => ?_
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩
  refine ⟨LinearMap.ker ((cfc f T : H →L[ℂ] H) : H →ₗ[ℂ] H), ?_,
    ContinuousLinearMap.isClosed_ker (cfc f T : H →L[ℂ] H), ?_, ?_, ?_⟩
  · obtain ⟨φ, hφ⟩ : ∃ φ, cfc k T φ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hk0 (ContinuousLinearMap.ext hc)
    refine (Submodule.ne_bot_iff _).2 ⟨cfc k T φ, ?_, hφ⟩
    rw [LinearMap.mem_ker]
    change (cfc f T * cfc k T) φ = 0
    rw [hfk]; rfl
  -- Step 4: invariance under `A` and `A*`
  · intro ψ hψ
    replace hψ : cfc f T ψ = 0 := hψ
    change (cfc f T * A) ψ = 0
    rw [(Commute.cfc_real hTA f).eq]
    change A (cfc f T ψ) = 0
    rw [hψ, map_zero]
  · intro ψ hψ
    replace hψ : cfc f T ψ = 0 := hψ
    change (cfc f T * ContinuousLinearMap.adjoint A) ψ = 0
    rw [(Commute.cfc_real hTA' f).eq]
    change ContinuousLinearMap.adjoint A (cfc f T ψ) = 0
    rw [hψ, map_zero]
  -- Step 3: `‖B ψ‖² = ⟪B* B ψ, ψ⟫ ≤ δ ‖ψ‖²`
  · intro ψ hψ hne
    replace hψ : cfc f T ψ = 0 := hψ
    refine ⟨hne, ?_⟩
    have hTψ : T ψ = cfc g T ψ := by
      conv_lhs => rw [hdec]
      rw [add_apply, hψ, zero_add]
    have hTle : ‖T ψ‖ ≤ δ * ‖ψ‖ := by
      rw [hTψ]
      exact ((cfc g T).le_opNorm ψ).trans (mul_le_mul_of_nonneg_right hgnorm (norm_nonneg _))
    have hsq : ‖B ψ‖ ^ 2 ≤ δ * ‖ψ‖ ^ 2 := by
      have h1 : ‖B ψ‖ ^ 2 = RCLike.re ⟪T ψ, ψ⟫_ℂ := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
        change _ = RCLike.re ⟪star B (B ψ), ψ⟫_ℂ
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      rw [h1]
      calc RCLike.re ⟪T ψ, ψ⟫_ℂ ≤ ‖T ψ‖ * ‖ψ‖ := re_inner_le_norm _ _
        _ ≤ δ * ‖ψ‖ * ‖ψ‖ := mul_le_mul_of_nonneg_right hTle (norm_nonneg _)
        _ = δ * ‖ψ‖ ^ 2 := by ring
    have hpos : 0 < ‖ψ‖ := norm_pos_iff.2 hne
    have hle : ‖B ψ‖ ≤ ε / 2 * ‖ψ‖ := by
      have : δ * ‖ψ‖ ^ 2 = (ε / 2 * ‖ψ‖) ^ 2 := by simp only [δ]; ring
      rw [this] at hsq
      exact pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero |>.1 hsq
    change ‖B ψ‖ < ε * ‖ψ‖
    nlinarith

/-!
### The two-variable spectral mapping theorem
-/

/-- For normal `A`, `p(A, A*)` is Mathlib's `cfc` of `λ ↦ p(λ, conj λ)`. -/
private theorem mvApply_eq_cfc {A : H →L[ℂ] H} [IsStarNormal A]
    (p : MvPolynomial (Fin 2) ℂ) : mvApply A p = cfc (mvEvalConj p) A := by
  have h : mvEvalConj p =
      ∑ d ∈ p.support, fun lam : ℂ => MvPolynomial.coeff d p * (lam ^ d 0 * star lam ^ d 1) := by
    ext lam; simp [mvEvalConj, Finset.sum_apply, mul_assoc]
  rw [h, cfc_sum _ A _ fun d _ => by fun_prop]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [cfc_const_mul _ _ A (by fun_prop), cfc_mul _ _ A (by fun_prop) (by fun_prop),
    cfc_pow_id A (d 0), cfc_pow (star ·) (d 1) A (by fun_prop), cfc_star_id (a := A),
    star_eq_adjoint]

private theorem continuous_mvEvalConj (p : MvPolynomial (Fin 2) ℂ) :
    Continuous (mvEvalConj p) := by
  unfold mvEvalConj; fun_prop

/--
**Spectral mapping for polynomials in `A` and `A*`.**

Blueprint reference: `thrm:hall-10.23`.
-/
theorem spectrum_mvApply {A : H →L[ℂ] H} [IsStarNormal A]
    (p : MvPolynomial (Fin 2) ℂ) :
    spectrum ℂ (mvApply A p) = mvEvalConj p '' spectrum ℂ A := by
  rw [mvApply_eq_cfc, cfc_map_spectrum (a := A) (hf := (continuous_mvEvalConj p).continuousOn)]

/--
The norm of a polynomial in `A` and `A*` is the supremum of `|p(λ, conj λ)|` over the
spectrum.

Blueprint reference: `crllr:norm-of-polynomial-in-a-astar`.
-/
theorem norm_mvApply [Nontrivial H] {A : H →L[ℂ] H} [IsStarNormal A]
    (p : MvPolynomial (Fin 2) ℂ) :
    ‖mvApply A p‖ = sSup ((fun lam => ‖mvEvalConj p lam‖) '' spectrum ℂ A) := by
  rw [mvApply_eq_cfc,
    (IsGreatest.norm_cfc (mvEvalConj p) A (continuous_mvEvalConj p).continuousOn).csSup_eq]

/-!
### The continuous functional calculus for a normal operator
-/

/--
A two-variable polynomial restricted to `σ(A)`, as a continuous complex-valued function.
-/
noncomputable def mvPolyOn (A : H →L[ℂ] H) (p : MvPolynomial (Fin 2) ℂ) :
    C(spectrum ℂ A, ℂ) :=
  ⟨fun lam => mvEvalConj p (lam : ℂ), by unfold mvEvalConj; fun_prop⟩

/--
The continuous functional calculus `f ↦ f(A)` of a bounded normal operator: Mathlib's
`cfcHom` for the predicate `IsStarNormal`, available because
`Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap` makes `H →L[ℂ] H` a C⋆-algebra.

Blueprint reference: `thrm:continuous-functional-calculus-normal`.
-/
noncomputable def normalCalculus {A : H →L[ℂ] H} (hA : IsStarNormal A) :
    C(spectrum ℂ A, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  cfcHom hA

/--
`normalCalculus` extends `p ↦ p(A, A*)`.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (the defining property).
-/
theorem normalCalculus_mvPolyOn {A : H →L[ℂ] H} (hA : IsStarNormal A)
    (p : MvPolynomial (Fin 2) ℂ) : normalCalculus hA (mvPolyOn A p) = mvApply A p := by
  set ι : C(spectrum ℂ A, ℂ) := ⟨fun lam => (lam : ℂ), continuous_subtype_val⟩
  have h : mvPolyOn A p = ∑ d ∈ p.support, MvPolynomial.coeff d p • (ι ^ d 0 * star ι ^ d 1) := by
    ext lam
    simp [mvPolyOn, mvEvalConj, ι, mul_assoc]
  have hι : normalCalculus hA ι = A := cfcHom_id hA
  rw [h, map_sum]
  simp only [map_smul, map_mul, map_pow, map_star, hι,
    ContinuousLinearMap.star_eq_adjoint, mvApply, ι]

/--
**The continuous functional calculus for a normal operator.** There is a unique bounded
`ℂ`-linear map `C⁰(σ(A); ℂ) → 𝓑(H)` sending `p` to `p(A, A*)`.

Blueprint reference: `thrm:continuous-functional-calculus-normal`.
-/
theorem existsUnique_normalCalculus {A : H →L[ℂ] H} (hA : IsStarNormal A) :
    ∃! T : C(spectrum ℂ A, ℂ) →L[ℂ] (H →L[ℂ] H),
      ∀ p : MvPolynomial (Fin 2) ℂ, T (mvPolyOn A p) = mvApply A p := by
  set ι : C(spectrum ℂ A, ℂ) := ContinuousMap.restrict (spectrum ℂ A) (.id ℂ)
  let Φ : C(spectrum ℂ A, ℂ) →L[ℂ] (H →L[ℂ] H) :=
    (normalCalculus hA).toLinearMap.mkContinuous 1 fun f => by
      simp [normalCalculus, norm_cfcHom A f hA]
  refine ⟨Φ, normalCalculus_mvPolyOn hA, fun T hT => ?_⟩
  have haeval : ∀ p : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.aeval ![ι, star ι] p = mvPolyOn A p := by
    intro p
    ext lam
    simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Fin.prod_univ_two, mvPolyOn,
      mvEvalConj, ι, ContinuousMap.sum_apply, mul_assoc]
  have hadj : ∀ f ∈ StarAlgebra.adjoin ℂ {ι}, T f = Φ f := by
    intro f hf
    have hle : Algebra.adjoin ℂ ({ι} ∪ star {ι}) ≤ (MvPolynomial.aeval ![ι, star ι]).range := by
      refine Algebra.adjoin_le ?_
      rintro g (rfl | hg)
      · exact ⟨MvPolynomial.X 0, by simp⟩
      · rw [Set.star_singleton, Set.mem_singleton_iff] at hg
        exact ⟨MvPolynomial.X 1, by simp [hg]⟩
    obtain ⟨p, hp⟩ := hle hf
    rw [show f = mvPolyOn A p from hp.symm.trans (haeval p), hT]
    exact (normalCalculus_mvPolyOn hA p).symm
  have hclos : closure (StarAlgebra.adjoin ℂ {ι} : Set C(spectrum ℂ A, ℂ)) = Set.univ := by
    have := ContinuousMap.elemental_id_eq_top (spectrum ℂ A)
    rw [StarAlgebra.elemental] at this
    rw [← StarSubalgebra.topologicalClosure_coe, this, StarSubalgebra.coe_top]
  ext1 f
  exact (Set.EqOn.closure hadj T.continuous Φ.continuous) (hclos ▸ Set.mem_univ f)

/--
Multiplicativity of the normal functional calculus.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (Property 2).
-/
theorem normalCalculus_mul {A : H →L[ℂ] H} (hA : IsStarNormal A)
    (f g : C(spectrum ℂ A, ℂ)) :
    normalCalculus hA (f * g) = normalCalculus hA f * normalCalculus hA g :=
  map_mul (normalCalculus hA) f g

/--
The calculus intertwines complex conjugation with the adjoint.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (Property 3).
-/
theorem normalCalculus_star {A : H →L[ℂ] H} (hA : IsStarNormal A) (f : C(spectrum ℂ A, ℂ)) :
    normalCalculus hA (star f) = star (normalCalculus hA f) :=
  map_star (normalCalculus hA) f

/--
The calculus is isometric.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (Property 4).
-/
theorem norm_normalCalculus {A : H →L[ℂ] H} (hA : IsStarNormal A) (f : C(spectrum ℂ A, ℂ)) :
    ‖normalCalculus hA f‖ = ‖f‖ :=
  norm_cfcHom A f hA

/--
The calculus sends the constant `1` to `1` and the identity function to `A`.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (Property 5).
-/
theorem normalCalculus_one_and_id {A : H →L[ℂ] H} (hA : IsStarNormal A) :
    normalCalculus hA 1 = 1 ∧
      normalCalculus hA ⟨fun lam => (lam : ℂ), continuous_subtype_val⟩ = A :=
  ⟨map_one _, cfcHom_id hA⟩

/--
A real-valued `f` gives a self-adjoint operator, and every `f` gives a normal one.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (final paragraph).
-/
theorem isSelfAdjoint_normalCalculus_of_real {A : H →L[ℂ] H} (hA : IsStarNormal A)
    {f : C(spectrum ℂ A, ℂ)} (hf : ∀ lam, (f lam).im = 0) :
    IsSelfAdjoint (normalCalculus hA f) := by
  have : star f = f := by
    ext lam
    exact Complex.conj_eq_iff_im.mpr (hf lam)
  exact (show IsSelfAdjoint f from this).map (normalCalculus hA)

/--
Every value of the calculus is normal.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (final paragraph).
-/
theorem isStarNormal_normalCalculus {A : H →L[ℂ] H} (hA : IsStarNormal A)
    (f : C(spectrum ℂ A, ℂ)) : IsStarNormal (normalCalculus hA f) :=
  ⟨by rw [← map_star, commute_iff_eq, ← map_mul, ← map_mul, mul_comm]⟩

end Unbounded
end Spectral
end Physicslib4
