/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Construction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Irreducibility of representations and Schur's lemma

A `*`-representation `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)` is *irreducible* when its
commutant is trivial: the only bounded operators commuting with every `π a` are
the scalar multiples of the identity. This is the von Neumann (commutant) form of
irreducibility, the operator-algebra counterpart of "no nontrivial closed
invariant subspace".

The central analytic fact is the **topological Schur lemma** for a cyclic
representation: if `T` commutes with all `π a` and its diagonal GNS coefficient
`a ↦ ⟪Ω, T (π a Ω)⟫` is proportional to `a ↦ ⟪Ω, π a Ω⟫`, then `T` is the
corresponding scalar. The proof is pure Hilbert-space analysis: the off-diagonal
coefficients `⟪π b Ω, (T - c) (π a Ω)⟫` all vanish (using the `*`-representation
property and the commutation relation), so `(T - c)` annihilates the dense cyclic
orbit and is therefore zero.

This is the bridge between the commutant and the GNS state: a commutant operator
is a scalar exactly when its GNS coefficient is proportional to the state.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A `*`-representation `π` of `A` on `H` is **irreducible** when its commutant is
trivial: every bounded operator `T` commuting with all `π a` is a scalar multiple
of the identity. -/
def IsIrreducible (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ T : H →L[ℂ] H, (∀ a : A, π a * T = T * π a) → ∃ c : ℂ, T = c • 1

/-- **Topological Schur lemma (proportional coefficient ⟹ scalar).** Let `Ω` be a
cyclic vector for `π`. If `T` commutes with every `π a` and the diagonal GNS
coefficient `a ↦ ⟪Ω, T (π a Ω)⟫` equals `c` times `a ↦ ⟪Ω, π a Ω⟫`, then
`T = c • 1`. The key step is that all off-diagonal coefficients
`⟪π b Ω, (T - c) (π a Ω)⟫` vanish, so `(T - c)` kills the dense cyclic orbit. -/
theorem eq_smul_one_of_commute_of_cyclic
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H} (hcyc : IsCyclicVector π Ω)
    {T : H →L[ℂ] H} (hT : ∀ a : A, π a * T = T * π a)
    {c : ℂ} (hprop : ∀ a : A, ⟪Ω, T (π a Ω)⟫_ℂ = c * ⟪Ω, π a Ω⟫_ℂ) :
    T = c • 1 := by
  have hcycdense : DenseRange (fun a : A => π a Ω) := hcyc
  -- The adjoint of `π b` is `π (star b)` (since `π` is a `*`-homomorphism).
  have hop : ∀ b : A, ContinuousLinearMap.adjoint (π b) = π (star b) := fun b => by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_star]
  -- Move `π b` to the other slot of the inner product via the adjoint.
  have hadj : ∀ (b : A) (w : H), ⟪(π b) Ω, w⟫_ℂ = ⟪Ω, π (star b) w⟫_ℂ := fun b w => by
    rw [← hop b, ContinuousLinearMap.adjoint_inner_right]
  -- `T` agrees with `c • ·` on the cyclic orbit.
  have hkey : ∀ a : A, T (π a Ω) = c • (π a Ω) := by
    intro a
    have hzero : ∀ b : A, ⟪π b Ω, T (π a Ω) - c • (π a Ω)⟫_ℂ = 0 := by
      intro b
      rw [inner_sub_right, inner_smul_right]
      have e1 : ⟪(π b) Ω, T (π a Ω)⟫_ℂ = ⟪Ω, T (π (star b * a) Ω)⟫_ℂ := by
        rw [hadj b (T (π a Ω))]
        congr 1
        have h1 : (π (star b)) (T (π a Ω)) = T ((π (star b)) (π a Ω)) :=
          calc (π (star b)) (T (π a Ω))
              = (π (star b) * T) (π a Ω) := by rw [ContinuousLinearMap.mul_apply]
            _ = (T * π (star b)) (π a Ω) := by rw [hT (star b)]
            _ = T ((π (star b)) (π a Ω)) := by rw [ContinuousLinearMap.mul_apply]
        rw [h1]
        congr 1
        rw [← ContinuousLinearMap.mul_apply, ← map_mul]
      have e2 : ⟪(π b) Ω, π a Ω⟫_ℂ = ⟪Ω, π (star b * a) Ω⟫_ℂ := by
        rw [hadj b (π a Ω)]
        congr 1
        rw [← ContinuousLinearMap.mul_apply, ← map_mul]
      rw [e1, e2, hprop (star b * a)]
      ring
    have hw0 : T (π a Ω) - c • (π a Ω) = 0 := by
      have hcont : Continuous (fun y : H => ⟪y, T (π a Ω) - c • (π a Ω)⟫_ℂ) :=
        continuous_id.inner continuous_const
      have heqon : Set.EqOn (fun y : H => ⟪y, T (π a Ω) - c • (π a Ω)⟫_ℂ)
          (fun _ => (0 : ℂ)) (Set.range fun a' : A => π a' Ω) := by
        rintro _ ⟨b, rfl⟩; exact hzero b
      have hzeroall := congrFun
        (Continuous.ext_on hcycdense hcont continuous_const heqon)
        (T (π a Ω) - c • (π a Ω))
      exact inner_self_eq_zero.mp hzeroall
    exact sub_eq_zero.mp hw0
  -- Density + continuity upgrade the agreement to all of `H`.
  have hall : (fun x => T x) = (fun x : H => c • x) :=
    Continuous.ext_on hcycdense T.continuous (continuous_const.smul continuous_id)
      (by rintro _ ⟨a, rfl⟩; exact hkey a)
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  exact congrFun hall x

/-- **A commutant operator is a scalar iff its GNS coefficient is proportional to
the state.** In a cyclic representation reproducing `ω`, an operator `T` commuting
with all `π a` is a scalar multiple of the identity exactly when its diagonal
coefficient `a ↦ ⟪Ω, T (π a Ω)⟫` is a scalar multiple of `ω`. This is the precise
operator-theoretic bridge between irreducibility and purity: it is the forward
(easy) direction together with the topological Schur lemma. -/
theorem isScalar_iff_coeff_proportional
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H} (hcyc : IsCyclicVector π Ω)
    {ω : State A} (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {T : H →L[ℂ] H} (hT : ∀ a : A, π a * T = T * π a) :
    (∃ c : ℂ, T = c • 1) ↔ ∃ t : ℂ, ∀ a : A, ⟪Ω, T (π a Ω)⟫_ℂ = t * (ω a : ℂ) := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, fun a => ?_⟩
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right,
      ← hrep a]
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    apply eq_smul_one_of_commute_of_cyclic hcyc hT
    intro a
    rw [ht a, hrep a]

/-- A state `ω` is **pure** if every positive linear functional `ψ` dominated by
`ω` (i.e. `0 ≤ ψ(a* a) ≤ ω(a* a)`) is a scalar multiple of `ω`. This is the
order-theoretic characterization of purity (extreme point of the state space),
phrased so that no convex-combination/normalization bookkeeping is needed. -/
def IsPure (ω : State A) : Prop :=
  ∀ ψ : A →L[ℂ] ℂ, (∀ a : A, 0 ≤ ψ (star a * a)) →
    (∀ a : A, ψ (star a * a) ≤ ω (star a * a)) →
      ∃ t : ℂ, ∀ a : A, ψ a = t * (ω a : ℂ)

/-- The **GNS coefficient functional** `a ↦ ⟪Ω, T (π a Ω)⟫` of an operator `T`,
bundled as a continuous linear functional. -/
noncomputable def coeffFunctional (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (T : H →L[ℂ] H) :
    A →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟪Ω, T (π a Ω)⟫_ℂ
      map_add' := fun a b => by
        simp [map_add, ContinuousLinearMap.add_apply, inner_add_right]
      map_smul' := fun c a => by
        simp [map_smul, ContinuousLinearMap.smul_apply, inner_smul_right] }
    (‖Ω‖ * ‖T‖ * ‖Ω‖)
    (fun a => by
      have hT' : ‖T (π a Ω)‖ ≤ ‖T‖ * (‖a‖ * ‖Ω‖) :=
        calc ‖T (π a Ω)‖ ≤ ‖T‖ * ‖π a Ω‖ := T.le_opNorm _
          _ ≤ ‖T‖ * (‖π a‖ * ‖Ω‖) := by gcongr; exact (π a).le_opNorm _
          _ ≤ ‖T‖ * (‖a‖ * ‖Ω‖) := by
              gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
      calc ‖⟪Ω, T (π a Ω)⟫_ℂ‖ ≤ ‖Ω‖ * ‖T (π a Ω)‖ := norm_inner_le_norm Ω _
        _ ≤ ‖Ω‖ * (‖T‖ * (‖a‖ * ‖Ω‖)) := by gcongr
        _ = ‖Ω‖ * ‖T‖ * ‖Ω‖ * ‖a‖ := by ring)

@[simp] theorem coeffFunctional_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (T : H →L[ℂ] H) (a : A) :
    coeffFunctional π Ω T a = ⟪Ω, T (π a Ω)⟫_ℂ := rfl

/-- On an element `star a * a`, the coefficient functional of a commutant operator
`T` evaluates to `⟪π a Ω, T (π a Ω)⟫`. -/
theorem coeffFunctional_star_mul {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H} {T : H →L[ℂ] H}
    (hT : ∀ a : A, π a * T = T * π a) (a : A) :
    coeffFunctional π Ω T (star a * a) = ⟪π a Ω, T (π a Ω)⟫_ℂ := by
  rw [coeffFunctional_apply]
  have hsplit : π (star a * a) Ω = π (star a) (π a Ω) := by
    rw [map_mul, ContinuousLinearMap.mul_apply]
  rw [hsplit]
  have hcomm : T (π (star a) (π a Ω)) = π (star a) (T (π a Ω)) := by
    rw [← ContinuousLinearMap.mul_apply, ← hT (star a), ContinuousLinearMap.mul_apply]
  rw [hcomm]
  have hadjeq : ContinuousLinearMap.adjoint (π a) = π (star a) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_star]
  rw [← hadjeq, ContinuousLinearMap.adjoint_inner_right]

omit [CompleteSpace H] in
/-- For a positive operator `S`, the diagonal inner product `⟪v, S v⟫` is a
non-negative complex number (its real part is `≥ 0` and its imaginary part
vanishes by self-adjointness). -/
theorem isPositive_inner_nonneg {S : H →L[ℂ] H} (hS : S.IsPositive) (v : H) :
    (0 : ℂ) ≤ ⟪v, S v⟫_ℂ := by
  rw [Complex.le_def]
  refine ⟨?_, ?_⟩
  · simpa using hS.re_inner_nonneg_right v
  · have hreal : (starRingEnd ℂ) ⟪v, S v⟫_ℂ = ⟪v, S v⟫_ℂ :=
      (inner_conj_symm (S v) v).trans (hS.1 v v)
    simp [Complex.conj_eq_iff_im.mp hreal]

/-- **Pure ⟹ irreducible, self-adjoint case.** If `ω` is pure (in its cyclic GNS
representation reproducing `ω`) and `S` is a self-adjoint operator commuting with
all `π a`, then `S` is a scalar multiple of the identity. The proof scales `S`
into a positive operator `T = r·S + ½·1` with `0 ≤ T ≤ 1`, whose coefficient
functional is positive and dominated by `ω`; purity forces it proportional to
`ω`, so Schur's lemma makes `T` (hence `S`) a scalar. -/
theorem scalar_of_isSelfAdjoint_of_isPure
    {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    (hpure : IsPure ω) {S : H →L[ℂ] H} (hSsa : IsSelfAdjoint S)
    (hScomm : ∀ a : A, π a * S = S * π a) :
    ∃ c : ℂ, S = c • 1 := by
  set r : ℝ := (2 * (‖S‖ + 1))⁻¹ with hr_def
  have hNnn : (0 : ℝ) ≤ ‖S‖ := norm_nonneg S
  have hrpos : 0 < r := by rw [hr_def]; positivity
  have hrS : r * ‖S‖ ≤ 1 / 2 := by
    rw [hr_def, inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith [hNnn]
  -- the scaled operator
  set T : H →L[ℂ] H := (r : ℂ) • S + (2⁻¹ : ℂ) • (1 : H →L[ℂ] H) with hT_def
  have h1SA : IsSelfAdjoint (1 : H →L[ℂ] H) := by simp [IsSelfAdjoint]
  have hrSA : IsSelfAdjoint ((r : ℂ)) := Complex.conj_ofReal r
  have hhSA : IsSelfAdjoint ((2⁻¹ : ℂ)) := by
    rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num]; exact Complex.conj_ofReal _
  have hTsa : IsSelfAdjoint T :=
    (hrSA.smul hSsa).add (hhSA.smul h1SA)
  have hTsymm : T.IsSymmetric := hTsa.isSymmetric
  -- coefficient expansion of `re ⟪T v, v⟫`
  have hTexp : ∀ v : H,
      Complex.re ⟪T v, v⟫_ℂ = r * Complex.re ⟪S v, v⟫_ℂ + 2⁻¹ * ‖v‖ ^ 2 := by
    intro v
    have hTv : T v = (r : ℂ) • S v + (2⁻¹ : ℂ) • v := by
      simp [hT_def, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [hTv, inner_add_left, inner_smul_left, inner_smul_left,
      Complex.add_re, Complex.conj_ofReal, Complex.re_ofReal_mul]
    have h2 : (starRingEnd ℂ) (2⁻¹ : ℂ) = (2⁻¹ : ℂ) := by
      rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num]; exact Complex.conj_ofReal _
    rw [h2]
    have hhalf : Complex.re ((2⁻¹ : ℂ) * ⟪v, v⟫_ℂ) = 2⁻¹ * Complex.re ⟪v, v⟫_ℂ := by
      rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    have hvv : Complex.re ⟪v, v⟫_ℂ = ‖v‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [hhalf, hvv]
  -- bound: |re ⟪S v, v⟫| ≤ ‖S‖ ‖v‖²
  have hb : ∀ v : H, |Complex.re ⟪S v, v⟫_ℂ| ≤ ‖S‖ * ‖v‖ ^ 2 := by
    intro v
    calc |Complex.re ⟪S v, v⟫_ℂ| ≤ ‖⟪S v, v⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖S v‖ * ‖v‖ := norm_inner_le_norm _ _
      _ ≤ (‖S‖ * ‖v‖) * ‖v‖ := by gcongr; exact S.le_opNorm v
      _ = ‖S‖ * ‖v‖ ^ 2 := by ring
  -- `T` and `1 - T` are positive
  have hTpos : T.IsPositive := by
    refine (ContinuousLinearMap.isPositive_def).mpr ⟨hTsymm, fun v => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    change (0 : ℝ) ≤ Complex.re ⟪T v, v⟫_ℂ
    rw [hTexp v]
    have hbv := (abs_le.mp (hb v)).1
    nlinarith [mul_le_mul_of_nonneg_left hbv hrpos.le,
      mul_le_mul_of_nonneg_right hrS (sq_nonneg ‖v‖), sq_nonneg ‖v‖]
  have hTle : (1 - T).IsPositive := by
    refine (ContinuousLinearMap.isPositive_def).mpr ⟨(h1SA.sub hTsa).isSymmetric, fun v => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    change (0 : ℝ) ≤ Complex.re ⟪(1 - T) v, v⟫_ℂ
    have hsub : ((1 : H →L[ℂ] H) - T) v = v - T v := by
      simp [ContinuousLinearMap.sub_apply]
    have hvv : Complex.re ⟪v, v⟫_ℂ = ‖v‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [hsub, inner_sub_left, Complex.sub_re, hTexp v, hvv]
    have hbv := (abs_le.mp (hb v)).2
    nlinarith [mul_le_mul_of_nonneg_left hbv hrpos.le,
      mul_le_mul_of_nonneg_right hrS (sq_nonneg ‖v‖), sq_nonneg ‖v‖]
  -- the coefficient functional is a dominated positive functional
  have hTcomm : ∀ a : A, π a * T = T * π a := by
    intro a
    rw [hT_def, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hScomm a,
      mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hψpos : ∀ a : A, 0 ≤ coeffFunctional π Ω T (star a * a) := by
    intro a
    rw [coeffFunctional_star_mul hTcomm a]
    exact isPositive_inner_nonneg hTpos _
  have hψdom : ∀ a : A,
      coeffFunctional π Ω T (star a * a) ≤ ω (star a * a) := by
    intro a
    rw [coeffFunctional_star_mul hTcomm a, hrep (star a * a)]
    have hsplit : π (star a * a) Ω = π (star a) (π a Ω) := by
      rw [map_mul, ContinuousLinearMap.mul_apply]
    have hadjeq : ContinuousLinearMap.adjoint (π a) = π (star a) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, map_star]
    have hω : ⟪Ω, π (star a * a) Ω⟫_ℂ = ⟪π a Ω, π a Ω⟫_ℂ := by
      rw [hsplit, ← hadjeq, ContinuousLinearMap.adjoint_inner_right]
    rw [hω]
    have hpd := isPositive_inner_nonneg hTle (π a Ω)
    have hsub : ((1 : H →L[ℂ] H) - T) (π a Ω) = π a Ω - T (π a Ω) := by
      simp [ContinuousLinearMap.sub_apply]
    rw [hsub, inner_sub_right] at hpd
    exact sub_nonneg.mp hpd
  -- purity forces `T` to be a scalar
  obtain ⟨t, ht⟩ := hpure (coeffFunctional π Ω T) hψpos hψdom
  have hTscalar : T = t • 1 := by
    apply eq_smul_one_of_commute_of_cyclic hcyc hTcomm
    intro a
    have hta := ht a
    rw [coeffFunctional_apply] at hta
    rw [hta, hrep a]
  -- deduce `S` is a scalar
  refine ⟨(r : ℂ)⁻¹ * (t - 2⁻¹), ?_⟩
  have hrne : (r : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hrpos
  have hSeq : (r : ℂ) • S = (t - 2⁻¹) • (1 : H →L[ℂ] H) := by
    have hrw : (r : ℂ) • S = T - (2⁻¹ : ℂ) • 1 := by rw [hT_def]; abel
    rw [hrw, hTscalar, sub_smul]
  calc S = (r : ℂ)⁻¹ • ((r : ℂ) • S) := by rw [smul_smul, inv_mul_cancel₀ hrne, one_smul]
    _ = (r : ℂ)⁻¹ • ((t - 2⁻¹) • (1 : H →L[ℂ] H)) := by rw [hSeq]
    _ = ((r : ℂ)⁻¹ * (t - 2⁻¹)) • 1 := by rw [smul_smul]

/-- **Pure ⟹ irreducible.** If a state `ω` is pure, then any cyclic representation
reproducing `ω` (in particular its GNS representation) is irreducible: the only
operators commuting with all `π a` are scalars. The proof decomposes a commuting
operator into its self-adjoint real and imaginary parts (the commutant is
`*`-closed), each of which is a scalar by `scalar_of_isSelfAdjoint_of_isPure`. -/
theorem isIrreducible_of_isPure
    {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    (hpure : IsPure ω) : IsIrreducible π := by
  intro T hTcomm
  -- the commutant is `*`-closed: `star T` also commutes
  have hstarcomm : ∀ a : A, π a * star T = star T * π a := by
    intro a
    have h := congrArg star (hTcomm (star a))
    simp only [star_mul, ← map_star, star_star] at h
    exact h.symm
  -- self-adjoint real and imaginary parts
  have hPSA : IsSelfAdjoint (T + star T) := by
    change star (T + star T) = T + star T
    rw [star_add, star_star, add_comm]
  have hPcomm : ∀ a : A, π a * (T + star T) = (T + star T) * π a := by
    intro a; rw [mul_add, add_mul, hTcomm a, hstarcomm a]
  have hQSA : IsSelfAdjoint (Complex.I • (star T - T)) := by
    change star (Complex.I • (star T - T)) = Complex.I • (star T - T)
    rw [star_smul, star_sub, star_star, RCLike.star_def, Complex.conj_I,
      neg_smul, ← smul_neg, neg_sub]
  have hQcomm : ∀ a : A,
      π a * (Complex.I • (star T - T)) = (Complex.I • (star T - T)) * π a := by
    intro a
    rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hstarcomm a, hTcomm a]
  -- each part is a scalar
  obtain ⟨p, hp⟩ :=
    scalar_of_isSelfAdjoint_of_isPure hcyc hrep hpure hPSA hPcomm
  obtain ⟨q, hq⟩ :=
    scalar_of_isSelfAdjoint_of_isPure hcyc hrep hpure hQSA hQcomm
  -- reconstruct `T` as a scalar
  refine ⟨2⁻¹ * (p + Complex.I * q), ?_⟩
  have h2T : (2 : ℂ) • T = (T + star T) + Complex.I • (Complex.I • (star T - T)) := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, two_smul]; abel
  have hval : (2 : ℂ) • T = (p + Complex.I * q) • (1 : H →L[ℂ] H) := by
    rw [h2T, hp, hq, smul_smul, ← add_smul]
  calc T = (2⁻¹ : ℂ) • ((2 : ℂ) • T) := by
            rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
    _ = (2⁻¹ : ℂ) • ((p + Complex.I * q) • (1 : H →L[ℂ] H)) := by rw [hval]
    _ = (2⁻¹ * (p + Complex.I * q)) • 1 := by rw [smul_smul]

end GNS
end Physicslib4
