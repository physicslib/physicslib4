/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Physicslib4.Spectral.Basic

/-!
# The spectrum of a bounded operator

The blueprint's resolvent set `ρ(A)` and spectrum `σ(A)` are Mathlib's
`resolventSet ℂ A` and `spectrum ℂ A`; Mathlib's resolvent operator
`resolvent A z` is `(z • 1 - A)⁻¹`, the *negative* of the blueprint's
`(A - λ 1)⁻¹`, which flips the sign in the Neumann expansion below but describes
the same resolvent set and spectrum.

## Main statements

* `Physicslib4.Spectral.isUnit_one_sub`,
  `Physicslib4.Spectral.hasSum_geometric_inverse_one_sub` — invertibility of `1 - X`
  and the Neumann series for `(1 - X)⁻¹` when `‖X‖ < 1`.
* `Physicslib4.Spectral.isCompact_spectrum`, `Physicslib4.Spectral.spectrum_nonempty`
  — `σ(A)` is compact, and (for `H ≠ {0}`) non-empty.
* `Physicslib4.Spectral.mem_resolventSet_of_norm_lt` — `|λ| > ‖A‖` puts `λ` in the
  resolvent set.
* `Physicslib4.Spectral.isOpen_resolventSet`,
  `Physicslib4.Spectral.exists_hasSum_resolvent`,
  `Physicslib4.Spectral.hasSum_resolvent_of_norm_lt` — the resolvent set is open,
  the resolvent is locally given by a power series, and the Neumann expansion holds
  outside the disc of radius `‖A‖`.
* `Physicslib4.Spectral.sq_norm_sub_smul_apply_le` — the `b²` inequality for a
  self-adjoint operator.
* `Physicslib4.Spectral.spectrum_subset_real` — a self-adjoint operator has real
  spectrum.
* `Physicslib4.Spectral.not_isUnit_mul_of_commute` — a commuting multiple of a
  non-invertible operator is non-invertible.
* `Physicslib4.Spectral.isSelfAdjoint_aeval_real` — real polynomials of a
  self-adjoint operator are self-adjoint.

## Blueprint nodes that are literally Mathlib declarations

The spectral-radius block of the blueprint is Mathlib verbatim, so those nodes are
cited rather than restated here. Where the Mathlib spelling is not a literal
transcription of the blueprint, the divergence is recorded.

* `thrm:heine-borel-theorem` — `Metric.isCompact_iff_isClosed_bounded`, together with
  the one-directional `Metric.isCompact_of_isClosed_isBounded` used for `σ(A)`. The
  blueprint states it for `ℂⁿ` with `n ≥ 1`; Mathlib has no dimension hypothesis,
  because what the proof uses is that the space is proper and Hausdorff, which `ℂⁿ`
  is.
* `def:spectral-radius` — `spectralRadius`. Caveat: `spectralRadius ℂ A` is
  `ℝ≥0∞`-valued, being `⨆ z ∈ spectrum ℂ A, ‖z‖₊`, whereas the blueprint's `R(A)` is a
  real number. The identification is `R(A) = (spectralRadius ℂ A).toReal`. It is
  faithful because for `H ≠ {0}` the supremum is attained
  (`spectrum.exists_nnnorm_eq_spectralRadius`), hence finite, which is the blueprint's
  own remark that `R(A)` is a finite real; note also that Mathlib's `⨆` over the empty
  set is `0`, so on the zero space the two sides read `0` rather than `-∞`.
* `crllr:crllr-1` — `spectrum.spectralRadius_le_nnnorm`. Two caveats. It is the
  `ℝ≥0∞` inequality `spectralRadius ℂ A ≤ ‖A‖₊`, which is the blueprint's
  `R(A) ≤ ‖A‖` under the `toReal` identification above. And it carries a
  `NormOneClass` hypothesis, which for `𝓑(H)` amounts to `‖1‖ = 1`, i.e. to the
  blueprint's standing `H ≠ {0}` (`Nontrivial H`); the blueprint's inequality does
  still hold on the zero space, where `σ(A) = ∅` and both sides are `0`, but not by
  this lemma.
* `lmm:hall-8.1` — `IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm`, the
  real-valued form `(spectralRadius ℂ A).toReal = ‖A‖` matching the blueprint's
  real-valued `R(A)`; the `ℝ≥0∞` form is `IsSelfAdjoint.spectralRadius_eq_nnnorm`. It
  is stated for an arbitrary `CStarAlgebra`, and `CStarAlgebra (H →L[ℂ] H)` is an
  instance. The blueprint derives it from Laurent's theorem
  (`thrm:laurents-theorem`); Mathlib derives it from the Gelfand formula instead, so
  `Physicslib4.Spectral.exists_unique_laurentSeries` is *not* needed for it and may
  stay unproved without blocking this node.
-/

namespace Physicslib4
namespace Spectral

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
If `‖X‖ < 1` then `1 - X` has a bounded inverse in `𝓑(H)`.

Blueprint reference: `lmm:hall-7.6` (first half).
-/
theorem isUnit_one_sub {X : H →L[ℂ] H} (hX : ‖X‖ < 1) : IsUnit (1 - X) :=
  ⟨Units.oneSub X hX, Units.val_oneSub X hX⟩

/--
If `‖X‖ < 1` then `(1 - X)⁻¹` is given by the operator-norm convergent Neumann
series `∑ Xⁿ`.

Blueprint reference: `lmm:hall-7.6` (second half).
-/
theorem hasSum_geometric_inverse_one_sub {X : H →L[ℂ] H} (hX : ‖X‖ < 1) :
    HasSum (fun n : ℕ => X ^ n) (Ring.inverse (1 - X)) :=
  hasSum_geom_series_inverse X hX

/--
The spectrum of a bounded operator is a compact subset of `ℂ`. Closedness and
boundedness (parts (1) and (2) of `prpstn:hall-7.5`) are `IsCompact.isClosed` and
`IsCompact.isBounded` applied to this.

Parts (3) and (4) of the blueprint statement — that `σ(A)` is a metric space under
the metric inherited from `ℂ`, and a measurable space for its Borel `σ`-algebra —
are supplied in Lean by the subtype instances `Subtype.instMetricSpace`,
`Subtype.instMeasurableSpace` and `Subtype.borelSpace`, so they carry no
propositional content here.

Blueprint reference: `lmm:spectrum-is-compact-metric-measurable`.
-/
theorem isCompact_spectrum (A : H →L[ℂ] H) : IsCompact (spectrum ℂ A) :=
  spectrum.isCompact A

/--
For a non-zero Hilbert space, the spectrum of any bounded operator is non-empty.
This is the one half of `lmm:spectrum-is-compact-metric-measurable` that uses the
blueprint's standing convention `H ≠ {0}`, stated in the section preamble alongside
`def:bounded-operator-notation`.

Blueprint reference: `lmm:spectrum-is-compact-metric-measurable`.
-/
theorem spectrum_nonempty [Nontrivial H] (A : H →L[ℂ] H) : (spectrum ℂ A).Nonempty :=
  spectrum.nonempty A

/--
Every `λ` with `‖A‖ < |λ|` lies in the resolvent set of `A`; equivalently, `σ(A)` is
contained in the closed disc of radius `‖A‖`.

This is the only part of `prpstn:hall-7.5` that is not already `isCompact_spectrum`
or `spectrum_nonempty`.

`Nontrivial H` is carried because the bound `‖z‖ ≤ ‖A‖` on `σ(A)` is stated in
Mathlib for a `NormOneClass` ring, and `‖1‖ = 1` in `𝓑(H)` needs `H ≠ {0}`. (On the
zero space `𝓑(H)` is the zero ring, so `resolventSet ℂ A = ℂ` and the conclusion
holds vacuously; the hypothesis is an artefact of the proof, not of the statement.)

Blueprint reference: `prpstn:hall-7.5`.
-/
theorem mem_resolventSet_of_norm_lt [Nontrivial H] (A : H →L[ℂ] H) {z : ℂ}
    (hz : ‖A‖ < ‖z‖) : z ∈ resolventSet ℂ A := by
  have h : z ∉ spectrum ℂ A := fun hmem =>
    absurd (spectrum.norm_le_norm_of_mem hmem) (not_le.mpr hz)
  simpa [spectrum, Set.mem_compl_iff] using h

/--
The resolvent set of a bounded operator is open.

Blueprint reference: `prpstn:resolvent-holomorphy-and-neumann-series` (part 1,
openness).
-/
theorem isOpen_resolventSet (A : H →L[ℂ] H) : IsOpen (resolventSet ℂ A) :=
  spectrum.isOpen_resolventSet A

/--
Near every point of the resolvent set, the resolvent is given by an operator-norm
convergent power series in `z - z₀` with coefficients in `𝓑(H)`.

Blueprint reference: `prpstn:resolvent-holomorphy-and-neumann-series` (part 1,
local power series).
-/
theorem exists_hasSum_resolvent (A : H →L[ℂ] H) {z₀ : ℂ} (hz₀ : z₀ ∈ resolventSet ℂ A) :
    ∃ (c : ℕ → H →L[ℂ] H) (r : ℝ), 0 < r ∧
      ∀ z : ℂ, ‖z - z₀‖ < r → HasSum (fun n : ℕ => (z - z₀) ^ n • c n) (resolvent A z) := by
  let R₀ : H →L[ℂ] H := resolvent A z₀
  let r : ℝ := (1 + ‖R₀‖)⁻¹
  refine ⟨fun n : ℕ => (-1 : ℂ) ^ n • R₀ ^ (n + 1), r, ?_, ?_⟩
  · dsimp only [r]
    exact inv_pos.mpr (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg R₀))
  · intro z hz
    let t : ℂ := z - z₀
    let X : H →L[ℂ] H := -(t • R₀)
    have hrpos : 0 < (1 + ‖R₀‖ : ℝ) := add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg R₀)
    have ht_norm : ‖t‖ * (1 + ‖R₀‖ : ℝ) < 1 := by
      have hmain : ‖t‖ < (1 + ‖R₀‖ : ℝ)⁻¹ := by
        simpa [t, r] using hz
      have h : ‖t‖ * (1 + ‖R₀‖) < (1 + ‖R₀‖)⁻¹ * (1 + ‖R₀‖) :=
        mul_lt_mul_of_pos_right hmain hrpos
      rwa [inv_mul_cancel₀ (ne_of_gt hrpos)] at h
    have htR : ‖t • R₀‖ < 1 := by
      calc
        ‖t • R₀‖ = ‖t‖ * ‖R₀‖ := norm_smul t R₀
        _ ≤ ‖t‖ * (1 + ‖R₀‖) := by
          gcongr
          linarith [norm_nonneg R₀]
        _ < 1 := ht_norm
    have hX : ‖X‖ < 1 := by
      simpa [X, norm_neg] using htR
    have hmX : IsUnit (1 - X) := isUnit_one_sub hX
    have hgeo : HasSum (fun n : ℕ => X ^ n) (Ring.inverse (1 - X)) :=
      hasSum_geometric_inverse_one_sub (X := X) hX
    let S₀ : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z₀ - A
    have hS₀R₀ : S₀ * R₀ = 1 := by
      change S₀ * Ring.inverse S₀ = 1
      exact Ring.mul_inverse_cancel S₀ (by simpa [S₀, resolventSet] using hz₀)
    have hfac : algebraMap ℂ (H →L[ℂ] H) z - A = S₀ * (1 - X) := by
      have hz₀t : z₀ + t = z := by
        dsimp [t]
        ring
      calc
        algebraMap ℂ (H →L[ℂ] H) z - A = algebraMap ℂ (H →L[ℂ] H) (z₀ + t) - A := by
          rw [← hz₀t]
        _ = (algebraMap ℂ (H →L[ℂ] H) z₀ + t • (1 : H →L[ℂ] H)) - A := by
          rw [map_add]
          simp [Algebra.algebraMap_eq_smul_one]
        _ = S₀ + t • (1 : H →L[ℂ] H) := by
          simp [S₀]
          abel
        _ = S₀ * (1 + t • R₀) := by
          calc
            S₀ + t • (1 : H →L[ℂ] H) = S₀ * 1 + t • (1 : H →L[ℂ] H) := by simp
            _ = S₀ * 1 + t • (S₀ * R₀) := by rw [← hS₀R₀]
            _ = S₀ * 1 + S₀ * (t • R₀) := by
              rw [← Algebra.mul_smul_comm]
            _ = S₀ * (1 + t • R₀) := by rw [← mul_add]
        _ = S₀ * (1 - X) := by
          simp [X]
    have hval : Ring.inverse (1 - X) * R₀ = resolvent A z := by
      calc
        Ring.inverse (1 - X) * R₀ = Ring.inverse (1 - X) * Ring.inverse S₀ := by
          simp [R₀, resolvent, S₀]
        _ = Ring.inverse (S₀ * (1 - X)) := by
          rw [Ring.inverse_mul (Or.inr hmX)]
        _ = Ring.inverse (algebraMap ℂ (H →L[ℂ] H) z - A) := by rw [hfac]
        _ = resolvent A z := by rfl
    have hgeo' : HasSum (fun n : ℕ => X ^ n * R₀) (Ring.inverse (1 - X) * R₀) :=
      hgeo.mul_right R₀
    have hsummand : ∀ n : ℕ, t ^ n • ((-1 : ℂ) ^ n • R₀ ^ (n + 1)) = X ^ n * R₀ := by
      intro n
      calc
        t ^ n • ((-1 : ℂ) ^ n • R₀ ^ (n + 1)) = (t ^ n * (-1 : ℂ) ^ n) • R₀ ^ (n + 1) := by
          rw [smul_smul]
        _ = (-t) ^ n • R₀ ^ (n + 1) := by
          rw [mul_comm, ← mul_pow, neg_one_mul]
        _ = ((-t) • R₀) ^ n * R₀ := by
          calc
            (-t) ^ n • R₀ ^ (n + 1) = (-t) ^ n • (R₀ ^ n * R₀) := by rw [pow_succ]
            _ = ((-t) ^ n • R₀ ^ n) * R₀ := by rw [← Algebra.smul_mul_assoc]
            _ = ((-t) • R₀) ^ n * R₀ := by rw [← smul_pow]
        _ = X ^ n * R₀ := by
          simp [X, neg_smul]
    have hsummand' : ∀ n : ℕ, (z - z₀) ^ n • ((-1 : ℂ) ^ n • R₀ ^ (n + 1)) = X ^ n * R₀ := by
      intro n
      simpa [t] using hsummand n
    simpa [hsummand', hval] using hgeo'

/--
Outside the closed disc of radius `‖A‖` the resolvent is given by the Neumann
expansion `∑ Aᵐ / z^{m+1}`.

Note that Mathlib's `resolvent A z = (z • 1 - A)⁻¹` is the negative of the
blueprint's `(A - z 1)⁻¹`, which accounts for the sign of the series relative to the
blueprint.

Blueprint reference: `prpstn:resolvent-holomorphy-and-neumann-series` (part 2).
-/
theorem hasSum_resolvent_of_norm_lt (A : H →L[ℂ] H) {z : ℂ} (hz : ‖A‖ < ‖z‖) :
    HasSum (fun m : ℕ => (z ^ (m + 1))⁻¹ • A ^ m) (resolvent A z) := by
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (norm_nonneg A) hz
  have hzne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hzpos)
  have hX : ‖z⁻¹ • A‖ < 1 := by
    rw [norm_smul, norm_inv, mul_comm, ← div_eq_mul_inv]
    exact (div_lt_one hzpos).2 hz
  have hgeo : HasSum (fun n : ℕ => (z⁻¹ • A) ^ n) (Ring.inverse (1 - z⁻¹ • A)) :=
    hasSum_geometric_inverse_one_sub (X := z⁻¹ • A) hX
  have hsmul :
      (Units.mk0 z hzne : ℂˣ) • resolvent A z = Ring.inverse (1 - z⁻¹ • A) := by
    calc
      (Units.mk0 z hzne : ℂˣ) • resolvent A z =
          resolvent ((Units.mk0 z hzne : ℂˣ)⁻¹ • A) (1 : ℂ) :=
        spectrum.units_smul_resolvent_self (r := Units.mk0 z hzne) (a := A)
      _ = Ring.inverse (1 - z⁻¹ • A) := by
        rw [resolvent]
        congr 1
        simp [Units.smul_def]
  have hR : resolvent A z = (z⁻¹ : ℂ) • Ring.inverse (1 - z⁻¹ • A) := by
    calc
      resolvent A z = (z⁻¹ : ℂ) • ((Units.mk0 z hzne : ℂˣ) • resolvent A z) := by
        rw [Units.smul_def, Units.val_mk0, smul_smul, inv_mul_cancel₀ hzne, one_smul]
      _ = (z⁻¹ : ℂ) • Ring.inverse (1 - z⁻¹ • A) := by
        rw [← hsmul]
  have hsummand : ∀ n : ℕ, (z⁻¹ : ℂ) • (z⁻¹ • A) ^ n = (z ^ (n + 1))⁻¹ • A ^ n := by
    intro n
    rw [smul_pow, smul_smul, ← pow_succ', inv_pow]
  simpa [hsummand, hR] using hgeo.const_smul (z⁻¹ : ℂ)

/--
For a self-adjoint `A` and `λ = a + i b` with `a, b` real,
`b² ‖ψ‖² ≤ ‖(A - λ 1) ψ‖²` for every `ψ`.

Blueprint reference: `lmm:hall-7.8`.
-/
theorem sq_norm_sub_smul_apply_le {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (a b : ℝ) (ψ : H) :
    b ^ 2 * ‖ψ‖ ^ 2 ≤
      ‖(A - ((a : ℂ) + (b : ℂ) * Complex.I) • (1 : H →L[ℂ] H)) ψ‖ ^ 2 := by
  let B : H →L[ℂ] H := A - (a : ℂ) • (1 : H →L[ℂ] H)
  have hB : IsSelfAdjoint B := by
    dsimp [B]
    rw [isSelfAdjoint_iff, star_sub, hA]
    rw [StarModule.star_smul]
    simpa [star_eq_adjoint, adjoint_one, Complex.conj_ofReal]
  have hBconj : star ⟪B ψ, ψ⟫_ℂ = ⟪B ψ, ψ⟫_ℂ := by
    exact (IsSelfAdjoint.isSymmetric hB).conj_inner_sym ψ ψ
  rcases (Complex.conj_eq_iff_real.mp hBconj) with ⟨r, hr⟩
  have hcross : (⟪B ψ, ((b : ℂ) * Complex.I) • ψ⟫_ℂ).re = 0 := by
    rw [inner_smul_right, hr]
    have hprod : ((b : ℂ) * Complex.I) * (r : ℂ) =
        ((b * r : ℝ) : ℂ) * Complex.I := by
      calc
        ((b : ℂ) * Complex.I) * (r : ℂ) = (b : ℂ) * (r : ℂ) * Complex.I := by ring
        _ = ((b * r : ℝ) : ℂ) * Complex.I := by rw [Complex.ofReal_mul]
    rw [hprod, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  have hre_defeq : RCLike.re ⟪B ψ, ((b : ℂ) * Complex.I) • ψ⟫_ℂ =
      (⟪B ψ, ((b : ℂ) * Complex.I) • ψ⟫_ℂ).re := by
    rfl
  have hsmul_norm_sq : ‖((b : ℂ) * Complex.I) • ψ‖ ^ 2 = b ^ 2 * ‖ψ‖ ^ 2 := by
    rw [norm_smul, mul_pow]
    congr 1
    rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    simpa using sq_abs b
  have hlambda : (A - (((a : ℂ) + (b : ℂ) * Complex.I) • (1 : H →L[ℂ] H))) ψ =
      B ψ - ((b : ℂ) * Complex.I) • ψ := by
    simp [B, sub_apply, smul_apply, add_apply, add_smul]
    abel
  calc
    b ^ 2 * ‖ψ‖ ^ 2 = ‖((b : ℂ) * Complex.I) • ψ‖ ^ 2 := by
      exact hsmul_norm_sq.symm
    _ ≤ ‖B ψ‖ ^ 2 + ‖((b : ℂ) * Complex.I) • ψ‖ ^ 2 := by
      exact le_add_of_nonneg_left (sq_nonneg ‖B ψ‖)
    _ = ‖B ψ - ((b : ℂ) * Complex.I) • ψ‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := ℂ)]
      rw [hre_defeq, hcross]
      ring
    _ = ‖(A - (((a : ℂ) + (b : ℂ) * Complex.I) • (1 : H →L[ℂ] H))) ψ‖ ^ 2 := by
      rw [hlambda]

/--
The spectrum of a self-adjoint bounded operator is contained in the reals.

Blueprint reference: `prpstn:hall-7.7`.
-/
theorem spectrum_subset_real {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    spectrum ℂ A ⊆ {z : ℂ | z.im = 0} := by
  intro z hz
  have h : ((z.re : ℝ) : ℂ) = z := IsSelfAdjoint.spectrumRestricts hA |>.rightInvOn hz
  simpa using congrArg Complex.im h.symm

omit [CompleteSpace H] in
/--
If `A` and `B` commute and `A` is not invertible, then `A * B` is not invertible.

Blueprint reference: `lmm:hall-ex-8.3.1`.
-/
theorem not_isUnit_mul_of_commute {A B : H →L[ℂ] H} (h : Commute A B) (hA : ¬IsUnit A) :
    ¬IsUnit (A * B) := fun hu => hA (h.isUnit_mul_iff.mp hu).1

/--
A polynomial with real coefficients evaluated at a self-adjoint operator is
self-adjoint.

Blueprint reference: `lmm:real-polynomial-self-adjoint`.
-/
theorem isSelfAdjoint_aeval_real {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (p : Polynomial ℝ) :
    IsSelfAdjoint (Polynomial.aeval A p) := by
  refine Polynomial.induction_on' (motive := fun q => IsSelfAdjoint (Polynomial.aeval A q)) p ?_ ?_
  · intro p q hp hq
    simpa [map_add] using hp.add hq
  · intro n a
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
    exact IsSelfAdjoint.smul (r := a) (by simp [isSelfAdjoint_iff]) (hA.pow n)

end Spectral
end Physicslib4
