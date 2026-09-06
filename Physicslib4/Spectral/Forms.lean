/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Basic

/-!
# Sesquilinear and quadratic forms on a Hilbert space

The blueprint constructs operators out of quadratic forms: an operator-valued
integral against a projection-valued measure, and the bounded Borel functional
calculus of a self-adjoint operator, are both obtained by exhibiting a bounded
quadratic form and invoking `existsUnique_operator_of_isBoundedQuadraticForm`
(the blueprint's Proposition A.63).

## Main definitions

* `Physicslib4.Spectral.SesquilinearForm` — `H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ`, conjugate linear
  in the first slot and linear in the second (the *physics* convention, and the
  shape of Mathlib's `innerSL`).
* `Physicslib4.Spectral.BoundedSesquilinearForm` — `H →L⋆[ℂ] H →L[ℂ] ℂ`.
* `Physicslib4.Spectral.polarization` — the sesquilinear form associated with a
  quadratic form.
* `Physicslib4.Spectral.IsQuadraticForm`, `Physicslib4.Spectral.IsBoundedQuadraticForm`.
* `Physicslib4.Spectral.IsBoundedQuadraticForm.toOperator` — the bounded operator
  representing a bounded quadratic form.

## Main statements

* `Physicslib4.Spectral.sesquilinear_polarization` — a sesquilinear form is
  determined by its diagonal.
* `Physicslib4.Spectral.polarization_diag`,
  `Physicslib4.Spectral.exists_bound_polarization`,
  `Physicslib4.Spectral.polarization_conj_symm` — the three properties of the
  polarization of a quadratic form asserted by the blueprint's Proposition A.61.
* `Physicslib4.Spectral.existsUnique_operator_of_isBoundedQuadraticForm` — a
  bounded quadratic form is `ψ ↦ ⟪ψ, A ψ⟫` for a unique `A ∈ 𝓑(H)`, and
  `Physicslib4.Spectral.IsBoundedQuadraticForm.isSelfAdjoint_toOperator` — that
  operator is self-adjoint when the form is real-valued.

## Implementation notes

Sesquilinearity and bounded sesquilinearity are *not* recorded as predicates on raw
functions `H → H → ℂ`: Mathlib bundles them as the semilinear map spaces
`H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ` and `H →L⋆[ℂ] H →L[ℂ] ℂ`. A raw function `F : H → H → ℂ` is
therefore asserted to be sesquilinear in the form `∃ L : SesquilinearForm H, ∀ φ ψ,
L φ ψ = F φ ψ`, which is the spelling used by `IsQuadraticForm.isSesquilinear`,
`exists_sesquilinearForm_sum` (`lmm:sesquilinear-linear-combination`) and
`exists_sesquilinearForm_of_tendsto` (`lmm:sesquilinear-pointwise-limit`).

Note that `H →L⋆[ℂ] H →L[ℂ] ℂ` is exactly the blueprint's notion of a *bounded*
sesquilinear form: continuity of the outer map says `‖L φ‖ ≤ C ‖φ‖` in the operator
norm, i.e. `|L φ ψ| ≤ C ‖φ‖ ‖ψ‖`.
-/

namespace Physicslib4
namespace Spectral

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### Sesquilinear forms
-/

/--
A *sesquilinear form* on a complex Hilbert space `H`: conjugate linear in the first
factor, linear in the second. This is Mathlib's semilinear map space
`H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ`, the shape of `innerSL`.

Blueprint reference: `def:bounded-sesquilinear-form` (first paragraph).
-/
abbrev SesquilinearForm (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ

/--
A *bounded sesquilinear form*: a sesquilinear form which is in addition continuous
in each slot, equivalently satisfies `|L φ ψ| ≤ C ‖φ‖ ‖ψ‖`.

Blueprint reference: `def:bounded-sesquilinear-form`.
-/
abbrev BoundedSesquilinearForm (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] :=
  H →L⋆[ℂ] H →L[ℂ] ℂ

omit [CompleteSpace H] in
/--
A sesquilinear form is determined by its values on the diagonal, through the
polarization identity.

Blueprint reference: `prpstn:hall-a.59`.
-/
theorem sesquilinear_polarization (L : SesquilinearForm H) (φ ψ : H) :
    L φ ψ =
      (1 / 2 : ℂ) * (L (φ + ψ) (φ + ψ) - L φ φ - L ψ ψ) -
        (Complex.I / 2) *
          (L (φ + Complex.I • ψ) (φ + Complex.I • ψ) - L φ φ -
            L (Complex.I • ψ) (Complex.I • ψ)) := by
  have h1 : L (φ + ψ) (φ + ψ) - L φ φ - L ψ ψ = L φ ψ + L ψ φ := by
    simp [map_add]
    ring
  have h2 : L (φ + Complex.I • ψ) (φ + Complex.I • ψ) - L φ φ -
      L (Complex.I • ψ) (Complex.I • ψ) = Complex.I * L φ ψ - Complex.I * L ψ φ := by
    simp [map_add, map_smul, map_smulₛₗ, smul_eq_mul]
    ring
  rw [h1, h2]
  field_simp
  simp
  ring

omit [CompleteSpace H] in
/--
A finite linear combination `∑ k ∈ s, α k • L k` of sesquilinear forms is a
sesquilinear form. With sesquilinearity bundled into the type `SesquilinearForm H`
this is the module structure on that space; what the blueprint asserts is that the
raw function `fun φ ψ => ∑ k ∈ s, α k * L k φ ψ` is the value function of a
sesquilinear form.

Blueprint reference: `lmm:sesquilinear-linear-combination`.
-/
theorem exists_sesquilinearForm_sum {ι : Type*} (s : Finset ι) (L : ι → SesquilinearForm H)
    (α : ι → ℂ) :
    ∃ L₀ : SesquilinearForm H, ∀ φ ψ : H, L₀ φ ψ = ∑ k ∈ s, α k * L k φ ψ :=
  ⟨∑ k ∈ s, α k • L k, by intro φ ψ; simp⟩

omit [CompleteSpace H] in
/--
A pointwise limit of sesquilinear forms is sesquilinear.

Blueprint reference: `lmm:sesquilinear-pointwise-limit`.
-/
theorem exists_sesquilinearForm_of_tendsto {L : ℕ → SesquilinearForm H} {F : H → H → ℂ}
    (h : ∀ φ ψ : H, Tendsto (fun i => L i φ ψ) atTop (𝓝 (F φ ψ))) :
    ∃ L₀ : SesquilinearForm H, ∀ φ ψ : H, L₀ φ ψ = F φ ψ := by
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F ?h1 ?h2 ?h3 ?h4, ?val⟩
  · intro φ₁ φ₂ ψ
    have hlim : Tendsto (fun i => L i φ₁ ψ + L i φ₂ ψ) atTop (𝓝 (F (φ₁ + φ₂) ψ)) := by
      simpa using h (φ₁ + φ₂) ψ
    exact (tendsto_nhds_unique ((h φ₁ ψ).add (h φ₂ ψ)) hlim).symm
  · intro c φ ψ
    have hlim : Tendsto (fun i => starRingEnd ℂ c * L i φ ψ) atTop (𝓝 (F (c • φ) ψ)) := by
      have hp : (fun i : ℕ => starRingEnd ℂ c * L i φ ψ) = fun i : ℕ => L i (c • φ) ψ := by
        ext i
        simp [map_smulₛₗ]
      simpa [hp] using h (c • φ) ψ
    have hmul : Tendsto (fun i : ℕ => starRingEnd ℂ c * L i φ ψ) atTop
        (𝓝 (starRingEnd ℂ c * F φ ψ)) :=
      Tendsto.const_mul (starRingEnd ℂ c) (h φ ψ)
    simpa [smul_eq_mul] using (tendsto_nhds_unique hmul hlim).symm
  · intro φ ψ₁ ψ₂
    have hlim : Tendsto (fun i => L i φ ψ₁ + L i φ ψ₂) atTop (𝓝 (F φ (ψ₁ + ψ₂))) := by
      simpa [map_add] using h φ (ψ₁ + ψ₂)
    exact (tendsto_nhds_unique ((h φ ψ₁).add (h φ ψ₂)) hlim).symm
  · intro c φ ψ
    have hlim : Tendsto (fun i => c * L i φ ψ) atTop (𝓝 (F φ (c • ψ))) := by
      have hp : (fun i : ℕ => c * L i φ ψ) = fun (i : ℕ) => L i φ (c • ψ) := by
        ext i
        simp [map_smul]
      simpa [hp] using h φ (c • ψ)
    have hmul : Tendsto (fun i : ℕ => c * L i φ ψ) atTop (𝓝 (c * F φ ψ)) :=
      Tendsto.const_mul c (h φ ψ)
    simpa [smul_eq_mul] using (tendsto_nhds_unique hmul hlim).symm
  · intro φ ψ
    rfl

/-!
### Quadratic forms
-/

/--
The sesquilinear form associated with a map `Q : H → ℂ` by the polarization
formula of the blueprint.

Blueprint reference: `def:bounded-quadratic-form` (point 2).
-/
noncomputable def polarization (Q : H → ℂ) : H → H → ℂ := fun φ ψ =>
  (1 / 2 : ℂ) * (Q (φ + ψ) - Q φ - Q ψ) -
    (Complex.I / 2) * (Q (φ + Complex.I • ψ) - Q φ - Q (Complex.I • ψ))

/--
A *quadratic form* on `H` is a map `Q : H → ℂ` that is `|λ|²`-homogeneous and
whose polarization is sesquilinear.

Blueprint reference: `def:bounded-quadratic-form`.
-/
structure IsQuadraticForm (Q : H → ℂ) : Prop where
  /-- `Q (λ • ψ) = |λ|² Q ψ`. -/
  smul : ∀ (l : ℂ) (ψ : H), Q (l • ψ) = (‖l‖ : ℂ) ^ 2 * Q ψ
  /-- The polarization of `Q` is a sesquilinear form. -/
  isSesquilinear : ∃ L : SesquilinearForm H, ∀ φ ψ : H, L φ ψ = polarization Q φ ψ

/--
A *bounded quadratic form* is a quadratic form `Q` with `|Q φ| ≤ C ‖φ‖²` for some
real constant `C`.

Blueprint reference: `def:bounded-quadratic-form`.
-/
structure IsBoundedQuadraticForm (Q : H → ℂ) : Prop where
  /-- The underlying form is quadratic. -/
  isQuadratic : IsQuadraticForm Q
  /-- The form is bounded by a multiple of `‖φ‖²`. -/
  bounded : ∃ C : ℝ, ∀ φ : H, ‖Q φ‖ ≤ C * ‖φ‖ ^ 2

omit [CompleteSpace H] in
/--
The polarization of a quadratic form recovers `Q` on the diagonal.

Blueprint reference: `prpstn:hall-a.61` (first part).
-/
theorem polarization_diag {Q : H → ℂ} (hQ : IsQuadraticForm Q) (ψ : H) :
    Q ψ = polarization Q ψ ψ := by
  rw [polarization]
  have h1 : Q (ψ + ψ) - Q ψ - Q ψ = (2 : ℂ) * Q ψ := by
    have hs : ψ + ψ = (2 : ℂ) • ψ := by
      rw [show (2 : ℂ) = (1 : ℂ) + 1 by ring, add_smul, one_smul]
    rw [hs, hQ.smul]
    norm_num
    ring
  have hψ : ψ + Complex.I • ψ = ((1 : ℂ) + Complex.I) • ψ := by
    rw [add_smul, one_smul]
  have hnorm : (‖((1 : ℂ) + Complex.I)‖ : ℂ) ^ 2 = (2 : ℂ) := by
    have hreal : ‖((1 : ℂ) + Complex.I)‖ ^ 2 = (2 : ℝ) := by
      rw [Complex.sq_norm]
      have hcont := Complex.normSq_add_mul_I (1 : ℝ) (1 : ℝ)
      simpa using (hcont.trans (by norm_num : (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = 2))
    exact_mod_cast hreal
  have h2a : Q (ψ + Complex.I • ψ) = (2 : ℂ) * Q ψ := by
    rw [hψ, hQ.smul, hnorm]
  have h2b : Q (Complex.I • ψ) = Q ψ := by
    rw [hQ.smul]
    norm_num
  rw [h1, h2a, h2b]
  ring

omit [CompleteSpace H] in
/--
The polarization of a *bounded* quadratic form is a bounded sesquilinear form.

Blueprint reference: `prpstn:hall-a.61` (second part).
-/
theorem exists_bound_polarization {Q : H → ℂ} (hQ : IsBoundedQuadraticForm Q) :
    ∃ C : ℝ, ∀ φ ψ : H, ‖polarization Q φ ψ‖ ≤ C * ‖φ‖ * ‖ψ‖ := by
  let L : SesquilinearForm H := hQ.isQuadratic.isSesquilinear.choose
  have hL : ∀ x y : H, L x y = polarization Q x y := hQ.isQuadratic.isSesquilinear.choose_spec
  have hdiag : ∀ x : H, L x x = Q x :=
    fun x => (hL x x).trans (polarization_diag hQ.isQuadratic x).symm
  rcases hQ.bounded with ⟨C0, hC0⟩
  let C₀ : ℝ := max C0 0
  have hC0nn : 0 ≤ C₀ := le_max_right C0 0
  have hC₀ : ∀ z : H, ‖Q z‖ ≤ C₀ * ‖z‖ ^ 2 := by
    intro z
    calc
      ‖Q z‖ ≤ C0 * ‖z‖ ^ 2 := hC0 z
      _ ≤ C₀ * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left C0 0) (sq_nonneg ‖z‖)
  have hbdiag : ∀ x : H, ‖L x x‖ ≤ C₀ * ‖x‖ ^ 2 := by
    intro x
    rw [hdiag x]
    exact hC₀ x
  have hpsq : ∀ x y : H, ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    intro x y
    calc
      ‖x + y‖ ^ 2 = ‖x + y‖ * ‖x + y‖ := by rw [pow_two]
      _ ≤ (‖x‖ + ‖y‖) * ‖x + y‖ := by
        exact mul_le_mul_of_nonneg_right (norm_add_le x y) (norm_nonneg (x + y))
      _ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
        exact mul_le_mul_of_nonneg_left (norm_add_le x y) (add_nonneg (norm_nonneg x) (norm_nonneg y))
      _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
        nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hbσ : ∀ x y : H, ‖L x y‖ ≤ 4 * C₀ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    intro x y
    have hI : ‖Complex.I • y‖ = ‖y‖ := by
      rw [norm_smul]
      simp
    have hx : ‖L (x + y) (x + y) - L x x - L y y‖ ≤ 4 * C₀ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      calc
        ‖L (x + y) (x + y) - L x x - L y y‖
            ≤ ‖L (x + y) (x + y) - L x x‖ + ‖L y y‖ := norm_sub_le _ _
        _ ≤ ‖L (x + y) (x + y)‖ + ‖L x x‖ + ‖L y y‖ := by
            nlinarith [norm_sub_le (L (x + y) (x + y)) (L x x)]
        _ ≤ C₀ * ‖x + y‖ ^ 2 + C₀ * ‖x‖ ^ 2 + C₀ * ‖y‖ ^ 2 := by
            exact add_le_add (add_le_add (hbdiag (x + y)) (hbdiag x)) (hbdiag y)
        _ ≤ C₀ * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) + C₀ * ‖x‖ ^ 2 + C₀ * ‖y‖ ^ 2 := by
            exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hpsq x y) hC0nn) (le_refl _)) (le_refl _)
        _ ≤ 4 * C₀ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
            nlinarith [hC0nn, sq_nonneg ‖x‖, sq_nonneg ‖y‖]
    have hy : ‖L (x + Complex.I • y) (x + Complex.I • y) - L x x - L (Complex.I • y) (Complex.I • y)‖ ≤
        4 * C₀ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      calc
        ‖L (x + Complex.I • y) (x + Complex.I • y) - L x x - L (Complex.I • y) (Complex.I • y)‖
            ≤ ‖L (x + Complex.I • y) (x + Complex.I • y) - L x x‖ + ‖L (Complex.I • y) (Complex.I • y)‖ := norm_sub_le _ _
        _ ≤ ‖L (x + Complex.I • y) (x + Complex.I • y)‖ + ‖L x x‖ + ‖L (Complex.I • y) (Complex.I • y)‖ := by
            nlinarith [norm_sub_le (L (x + Complex.I • y) (x + Complex.I • y)) (L x x)]
        _ ≤ C₀ * ‖x + Complex.I • y‖ ^ 2 + C₀ * ‖x‖ ^ 2 + C₀ * ‖Complex.I • y‖ ^ 2 := by
            exact add_le_add (add_le_add (hbdiag (x + Complex.I • y)) (hbdiag x)) (hbdiag (Complex.I • y))
        _ ≤ C₀ * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) + C₀ * ‖x‖ ^ 2 + C₀ * ‖y‖ ^ 2 := by
            rw [hI]
            have hpI : ‖x + Complex.I • y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
              rw [← hI]
              exact hpsq x (Complex.I • y)
            exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hpI hC0nn) (le_refl _)) (le_refl _)
        _ ≤ 4 * C₀ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
            nlinarith [hC0nn, sq_nonneg ‖x‖, sq_nonneg ‖y‖]
    rw [sesquilinear_polarization L x y]
    calc
      ‖(1 / 2 : ℂ) * (L (x + y) (x + y) - L x x - L y y) -
          (Complex.I / 2) * (L (x + Complex.I • y) (x + Complex.I • y) - L x x - L (Complex.I • y) (Complex.I • y))‖
          ≤ ‖(1 / 2 : ℂ) * (L (x + y) (x + y) - L x x - L y y)‖ +
              ‖(Complex.I / 2) * (L (x + Complex.I • y) (x + Complex.I • y) - L x x - L (Complex.I • y) (Complex.I • y))‖ :=
            norm_sub_le _ _
      _ ≤ 1 / 2 * ‖L (x + y) (x + y) - L x x - L y y‖ +
          1 / 2 * ‖L (x + Complex.I • y) (x + Complex.I • y) - L x x - L (Complex.I • y) (Complex.I • y)‖ := by
          have hc1 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
          have hc2 : ‖(Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
          rw [norm_mul, norm_mul]
          rw [hc1, hc2]
      _ ≤ 1 / 2 * (4 * C₀ * (‖x‖ ^ 2 + ‖y‖ ^ 2)) +
          1 / 2 * (4 * C₀ * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hx (by norm_num)) (mul_le_mul_of_nonneg_left hy (by norm_num))
      _ ≤ 4 * C₀ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
          nlinarith [hC0nn, sq_nonneg ‖x‖, sq_nonneg ‖y‖]
  refine ⟨8 * C₀, ?_⟩
  intro φ ψ
  by_cases hφ : φ = 0
  · subst φ
    have hp0 : polarization Q 0 ψ = 0 := by
      rw [← hL 0 ψ]
      simp
    simp [hp0]
  · by_cases hψ : ψ = 0
    · subst ψ
      have hp0 : polarization Q φ 0 = 0 := by
        rw [← hL φ 0]
        simp
      simp [hp0]
    · let t : ℝ := Real.sqrt (‖ψ‖ / ‖φ‖)
      have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
      have ht_ne0 : t ≠ 0 := by
        have hψpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
        have hφpos : 0 < ‖φ‖ := norm_pos_iff.mpr hφ
        have hdivpos : 0 < ‖ψ‖ / ‖φ‖ := div_pos hψpos hφpos
        exact ne_of_gt (by
          dsimp [t]
          exact Real.sqrt_pos.2 hdivpos)
      have ht_sq : t ^ 2 = ‖ψ‖ / ‖φ‖ := by
        dsimp [t]
        exact Real.sq_sqrt (div_nonneg (norm_nonneg ψ) (norm_nonneg φ))
      have hconj : starRingEnd ℂ (t : ℂ) = (t : ℂ) :=
        Complex.conj_ofReal t
      have hfac : L ((t : ℂ) • φ) ((t⁻¹ : ℂ) • ψ) =
          (t : ℂ) * (t⁻¹ : ℂ) * L φ ψ := by
        have hfirst : L ((t : ℂ) • φ) = (starRingEnd ℂ (t : ℂ)) • L φ :=
          map_smulₛₗ L (t : ℂ) φ
        rw [hfirst, LinearMap.smul_apply, smul_eq_mul, hconj, map_smul, smul_eq_mul]
        ring
      have hscale : L φ ψ = L ((t : ℂ) • φ) ((t⁻¹ : ℂ) • ψ) := by
        rw [hfac]
        have hmul : (t : ℂ) * (t⁻¹ : ℂ) = 1 := by
          exact mul_inv_cancel₀ (by exact_mod_cast ht_ne0)
        rw [hmul, one_mul]
      have hnorm1 : ‖((t : ℂ) • φ)‖ = t * ‖φ‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
      have hnorm2 : ‖((t⁻¹ : ℂ) • ψ)‖ = t⁻¹ * ‖ψ‖ := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht_nonneg]
      have hbound : ‖L φ ψ‖ ≤
          4 * C₀ * (‖((t : ℂ) • φ)‖ ^ 2 + ‖((t⁻¹ : ℂ) • ψ)‖ ^ 2) := by
        calc
          ‖L φ ψ‖ = ‖L ((t : ℂ) • φ) ((t⁻¹ : ℂ) • ψ)‖ := by rw [hscale]
          _ ≤ 4 * C₀ * (‖((t : ℂ) • φ)‖ ^ 2 + ‖((t⁻¹ : ℂ) • ψ)‖ ^ 2) :=
            hbσ ((t : ℂ) • φ) ((t⁻¹ : ℂ) • ψ)
      have hterm1 : (t : ℝ) ^ 2 * ‖φ‖ ^ 2 = ‖φ‖ * ‖ψ‖ := by
        rw [ht_sq]
        field_simp [norm_ne_zero_iff.mpr hφ]
      have hterm2 : (t : ℝ)⁻¹ ^ 2 * ‖ψ‖ ^ 2 = ‖φ‖ * ‖ψ‖ := by
        rw [inv_pow, ht_sq]
        field_simp [norm_ne_zero_iff.mpr hφ, norm_ne_zero_iff.mpr hψ]
      have hbfull : ‖L φ ψ‖ ≤ 8 * C₀ * ‖φ‖ * ‖ψ‖ := by
        calc
          ‖L φ ψ‖ ≤ 4 * C₀ * (‖((t : ℂ) • φ)‖ ^ 2 + ‖((t⁻¹ : ℂ) • ψ)‖ ^ 2) := hbound
          _ = 4 * C₀ * ((t * ‖φ‖) ^ 2 + (t⁻¹ * ‖ψ‖) ^ 2) := by rw [hnorm1, hnorm2]
          _ = 4 * C₀ * (t ^ 2 * ‖φ‖ ^ 2 + (t⁻¹) ^ 2 * ‖ψ‖ ^ 2) := by ring
          _ = 4 * C₀ * (‖φ‖ * ‖ψ‖ + ‖φ‖ * ‖ψ‖) := by rw [hterm1, hterm2]
          _ = 8 * C₀ * ‖φ‖ * ‖ψ‖ := by ring
      rw [← hL φ ψ]
      exact hbfull

omit [CompleteSpace H] in
/--
The polarization of a real-valued quadratic form is conjugate symmetric.

Blueprint reference: `prpstn:hall-a.61` (third part).
-/
theorem polarization_conj_symm {Q : H → ℂ} (hQ : IsQuadraticForm Q)
    (hreal : ∀ ψ : H, (Q ψ).im = 0) (φ ψ : H) :
    polarization Q φ ψ = (starRingEnd ℂ) (polarization Q ψ φ) := by
  let L : SesquilinearForm H := hQ.isSesquilinear.choose
  have hL : ∀ a b : H, L a b = polarization Q a b := hQ.isSesquilinear.choose_spec
  have hdiag : ∀ a : H, L a a = Q a :=by
    intro a
    exact (hL a a).trans (polarization_diag hQ a).symm
  have hcrossL : ∀ a b : H,
      L (a + Complex.I • b) (a + Complex.I • b) - L a a - L (Complex.I • b) (Complex.I • b) =
        - (L (b + Complex.I • a) (b + Complex.I • a) - L b b -
            L (Complex.I • a) (Complex.I • a)) :=by
    intro a b
    have ht : ∀ c d : H,
        L (c + Complex.I • d) (c + Complex.I • d) - L c c - L (Complex.I • d) (Complex.I • d) =
                  Complex.I * (L c d - L d c) :=by
      intro c d
      simp [map_add, LinearMap.add_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply,
        Complex.conj_I]
      ring_nf
    rw [ht a b, ht b a]
    ring
  have hB : ∀ a b : H,
      Q (a + Complex.I • b) - Q a - Q (Complex.I • b) =
        - (Q (b + Complex.I • a) - Q b - Q (Complex.I • a)) :=by
    intro a b
    rw [← hdiag (a + Complex.I • b), ← hdiag a, ← hdiag (Complex.I • b),
      ← hdiag (b + Complex.I • a), ← hdiag b, ← hdiag (Complex.I • a)]
    exact hcrossL a b
  have hReal : ∀ r : H, (starRingEnd ℂ) (Q r) = Q r :=by
    intro r
    exact Complex.conj_eq_iff_im.mpr (hreal r)
  unfold polarization
  have hRp :(starRingEnd ℂ) ((1 / 2 : ℂ) * (Q (ψ + φ) - Q ψ - Q φ) -
        (Complex.I / 2) * (Q (ψ + Complex.I • φ) - Q ψ - Q (Complex.I • φ))) =
      (1 / 2 : ℂ) * (Q (ψ + φ) - Q ψ - Q φ) +
        (Complex.I / 2) * (Q (ψ + Complex.I • φ) - Q ψ - Q (Complex.I • φ)) :=by
    simp only [map_mul, map_sub, hReal]
    norm_num
    ring_nf
    rw [show (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) by simpa using (Complex.conj_ofReal (2 : ℝ))]
    ring
  rw [hRp]
  rw [add_comm ψ φ]
  rw [hB ψ φ]
  ring

omit [CompleteSpace H] in
/--
A sum of bounded quadratic forms is a bounded quadratic form.

Blueprint reference: `lmm:bqf-linear-combination`.
-/
theorem IsBoundedQuadraticForm.add {Q R : H → ℂ} (hQ : IsBoundedQuadraticForm Q)
    (hR : IsBoundedQuadraticForm R) : IsBoundedQuadraticForm (Q + R) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro l ψ
    simp [hQ.isQuadratic.smul l ψ, hR.isQuadratic.smul l ψ]
    ring
  · rcases hQ.isQuadratic.isSesquilinear with ⟨LQ, hLQ⟩
    rcases hR.isQuadratic.isSesquilinear with ⟨LR, hLR⟩
    refine ⟨LQ + LR, ?_⟩
    intro φ ψ
    simp [polarization, hLQ φ ψ, hLR φ ψ]
    ring
  · rcases hQ.bounded with ⟨CQ, hCQ⟩
    rcases hR.bounded with ⟨CR, hCR⟩
    refine ⟨|CQ| + |CR|, ?_⟩
    intro φ
    calc
      ‖(Q + R) φ‖ = ‖Q φ + R φ‖ := by rfl
      _ ≤ ‖Q φ‖ + ‖R φ‖ := norm_add_le _ _
      _ ≤ |CQ| * ‖φ‖ ^ 2 + |CR| * ‖φ‖ ^ 2 := by
        exact add_le_add
          (le_trans (hCQ φ) (mul_le_mul_of_nonneg_right (le_abs_self CQ) (sq_nonneg ‖φ‖)))
          (le_trans (hCR φ) (mul_le_mul_of_nonneg_right (le_abs_self CR) (sq_nonneg ‖φ‖)))
      _ = (|CQ| + |CR|) * ‖φ‖ ^ 2 := by ring

omit [CompleteSpace H] in
/--
A scalar multiple of a bounded quadratic form is a bounded quadratic form.

Blueprint reference: `lmm:bqf-linear-combination`.
-/
theorem IsBoundedQuadraticForm.smul {Q : H → ℂ} (hQ : IsBoundedQuadraticForm Q) (α : ℂ) :
    IsBoundedQuadraticForm (α • Q) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro l ψ
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hQ.isQuadratic.smul l ψ]
    ring
  · rcases hQ.isQuadratic.isSesquilinear with ⟨L, hL⟩
    refine ⟨α • L, ?_⟩
    intro φ ψ
    simp [polarization, hL φ ψ, Pi.smul_apply, smul_eq_mul]
    ring
  · rcases hQ.bounded with ⟨C, hC⟩
    refine ⟨‖α‖ * |C|, ?_⟩
    intro φ
    calc
      ‖(α • Q) φ‖ = ‖α • Q φ‖ := by rfl
      _ = ‖α‖ * ‖Q φ‖ := by rw [norm_smul]
      _ ≤ ‖α‖ * (C * ‖φ‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left (hC φ) (norm_nonneg α)
      _ ≤ ‖α‖ * (|C| * ‖φ‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg ‖φ‖)) (norm_nonneg α)
      _ = ‖α‖ * |C| * ‖φ‖ ^ 2 := by ring

omit [CompleteSpace H] in
/--
A finite linear combination of bounded quadratic forms is a bounded quadratic form.

Blueprint reference: `lmm:bqf-linear-combination`.
-/
theorem IsBoundedQuadraticForm.sum {ι : Type*} (s : Finset ι) {Q : ι → H → ℂ}
    (hQ : ∀ k ∈ s, IsBoundedQuadraticForm (Q k)) (α : ι → ℂ) :
    IsBoundedQuadraticForm (fun φ : H => ∑ k ∈ s, α k * Q k φ) := by
  induction s using Finset.cons_induction with
  | empty =>
      have hz : IsBoundedQuadraticForm (fun _ : H => (0 : ℂ)) := by
        refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · intro l ψ
            simp
          · refine ⟨0, ?_⟩
            intro φ ψ
            simp [polarization]
        · refine ⟨0, ?_⟩
          intro φ
          simp
      simpa [Finset.sum_empty] using hz
  | cons a s has ih =>
      have hQa : IsBoundedQuadraticForm (Q a) := hQ a (by simp)
      have hQs : ∀ k ∈ s, IsBoundedQuadraticForm (Q k) := fun k hk => hQ k (by
        simp [Finset.mem_cons, hk])
      have hstep :
          IsBoundedQuadraticForm (fun φ : H => (α a • Q a) φ + (∑ k ∈ s, α k * Q k φ)) :=
        IsBoundedQuadraticForm.add (IsBoundedQuadraticForm.smul hQa (α a)) (ih hQs)
      simpa [Finset.sum_cons, Pi.smul_apply, smul_eq_mul] using hstep

omit [CompleteSpace H] in
/--
A pointwise limit of quadratic forms with a *uniform* bound `C` is a bounded
quadratic form.

The blueprint takes the approximating forms to be bounded, but only their
quadraticity is used: the bound on the limit comes from the uniform bound carried by
`BoundedPointwiseLimit`, so `hQ` asks for no more than `IsQuadraticForm`.

Blueprint reference: `lmm:bqf-pointwise-limit`.
-/
theorem isBoundedQuadraticForm_of_tendsto {Q : ℕ → H → ℂ} {Q₀ : H → ℂ} {C : ℝ}
    (hQ : ∀ i, IsQuadraticForm (Q i))
    (h : BoundedPointwiseLimit Q Q₀ (fun φ => C * ‖φ‖ ^ 2)) :
    IsBoundedQuadraticForm Q₀ := by
  refine { isQuadratic := ?_, bounded := ⟨C, norm_le_of_tendsto h⟩ }
  refine { smul := ?_, isSesquilinear := ?_ }
  · intro l ψ
    have h1 : Tendsto (fun i => Q i (l • ψ)) atTop (𝓝 (Q₀ (l • ψ))) := h.tendsto (l • ψ)
    have h2 : Tendsto (fun i => (‖l‖ : ℂ) ^ 2 * Q i ψ) atTop (𝓝 ((‖l‖ : ℂ) ^ 2 * Q₀ ψ)) :=
      tendsto_const_nhds.mul (h.tendsto ψ)
    have h2' : Tendsto (fun i => Q i (l • ψ)) atTop (𝓝 ((‖l‖ : ℂ) ^ 2 * Q₀ ψ)) :=
      Tendsto.congr (fun i => ((hQ i).smul l ψ).symm) h2
    exact tendsto_nhds_unique h1 h2'
  · have hlim : ∀ φ ψ : H,
        Tendsto (fun i => (hQ i).isSesquilinear.choose φ ψ) atTop (𝓝 (polarization Q₀ φ ψ)) := by
      intro φ ψ
      have hpol : Tendsto (fun i => polarization (Q i) φ ψ) atTop (𝓝 (polarization Q₀ φ ψ)) := by
        have hsum1 : Tendsto (fun i => (Q i (φ + ψ) - Q i φ) - Q i ψ) atTop
            (𝓝 ((Q₀ (φ + ψ) - Q₀ φ) - Q₀ ψ)) :=
          ((h.tendsto (φ + ψ)).sub (h.tendsto φ)).sub (h.tendsto ψ)
        have hsum2 : Tendsto
            (fun i => (Q i (φ + Complex.I • ψ) - Q i φ) - Q i (Complex.I • ψ)) atTop
            (𝓝 ((Q₀ (φ + Complex.I • ψ) - Q₀ φ) - Q₀ (Complex.I • ψ))) :=
          ((h.tendsto (φ + Complex.I • ψ)).sub (h.tendsto φ)).sub
            (h.tendsto (Complex.I • ψ))
        have hterm1 : Tendsto (fun i => (1 / 2 : ℂ) * ((Q i (φ + ψ) - Q i φ) - Q i ψ)) atTop
            (𝓝 ((1 / 2 : ℂ) * ((Q₀ (φ + ψ) - Q₀ φ) - Q₀ ψ))) :=
          tendsto_const_nhds.mul hsum1
        have hterm2 : Tendsto (fun i => (Complex.I / 2 : ℂ) *
            ((Q i (φ + Complex.I • ψ) - Q i φ) - Q i (Complex.I • ψ))) atTop
            (𝓝 ((Complex.I / 2 : ℂ) * ((Q₀ (φ + Complex.I • ψ) - Q₀ φ) -
              Q₀ (Complex.I • ψ)))) :=
          tendsto_const_nhds.mul hsum2
        simpa [polarization] using hterm1.sub hterm2
      exact Tendsto.congr (fun i => ((hQ i).isSesquilinear.choose_spec φ ψ).symm) hpol
    rcases exists_sesquilinearForm_of_tendsto
      (L := fun i => (hQ i).isSesquilinear.choose)
      (F := fun φ ψ => polarization Q₀ φ ψ) hlim with ⟨S, hS⟩
    exact ⟨S, hS⟩

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/--
A pointwise limit of forms obeying a *uniform* bound `C` obeys the same bound. This
is the quantitative half of `lmm:bqf-pointwise-limit`, and needs neither
completeness nor the quadratic-form hypotheses: it is
`Physicslib4.Spectral.norm_le_of_tendsto` with the dominating function
`fun φ => C * ‖φ‖ ^ 2`.

Blueprint reference: `lmm:bqf-pointwise-limit`.
-/
theorem norm_le_of_tendsto_of_bound {Q : ℕ → H → ℂ} {Q₀ : H → ℂ} {C : ℝ}
    (h : BoundedPointwiseLimit Q Q₀ (fun φ => C * ‖φ‖ ^ 2)) (φ : H) :
    ‖Q₀ φ‖ ≤ C * ‖φ‖ ^ 2 :=
  norm_le_of_tendsto h φ

/-!
### Bounded quadratic forms and bounded operators
-/

omit [CompleteSpace H] in
/--
Every bounded operator `A` gives a bounded quadratic form `ψ ↦ ⟪ψ, A ψ⟫`.

Blueprint reference: `prpstn:hall-a.62` (first part).
-/
theorem isBoundedQuadraticForm_inner (A : H →L[ℂ] H) :
    IsBoundedQuadraticForm (fun ψ : H => ⟪ψ, A ψ⟫_ℂ) := by
  have hpq : ∀ χ ψ : H, polarization (fun h : H => ⟪h, A h⟫_ℂ) χ ψ = ⟪χ, A ψ⟫_ℂ := by
    intro χ ψ
    unfold polarization
    have h1 : (fun h : H => ⟪h, A h⟫_ℂ) (χ + ψ) - (fun h : H => ⟪h, A h⟫_ℂ) χ -
        (fun h : H => ⟪h, A h⟫_ℂ) ψ = ⟪χ, A ψ⟫_ℂ + ⟪ψ, A χ⟫_ℂ := by
      simp [map_add, inner_add_right, inner_add_left]
      ring
    have h2 : (fun h : H => ⟪h, A h⟫_ℂ) (χ + Complex.I • ψ) -
        (fun h : H => ⟪h, A h⟫_ℂ) χ - (fun h : H => ⟪h, A h⟫_ℂ) (Complex.I • ψ) =
          Complex.I * ⟪χ, A ψ⟫_ℂ - Complex.I * ⟪ψ, A χ⟫_ℂ := by
      simp [map_add, map_smul, inner_add_right, inner_add_left, inner_smul_left,
        inner_smul_right]
      ring
    rw [h1, h2]
    field_simp
    simp
    ring
  refine ⟨⟨?hsmul, ?hsesq⟩, ?hbdd⟩
  · intro l ψ
    calc
      ⟪l • ψ, A (l • ψ)⟫_ℂ = ⟪l • ψ, l • A ψ⟫_ℂ := by simp [map_smul]
      _ = l * ⟪l • ψ, A ψ⟫_ℂ := by simp [inner_smul_right]
      _ = l * (starRingEnd ℂ l * ⟪ψ, A ψ⟫_ℂ) := by simp [inner_smul_left]
      _ = (starRingEnd ℂ l * l) * ⟪ψ, A ψ⟫_ℂ := by ring
      _ = (‖l‖ : ℂ) ^ 2 * ⟪ψ, A ψ⟫_ℂ := by
        rw [← Complex.normSq_eq_conj_mul_self (z := l), Complex.normSq_eq_norm_sq]
        simp
      _ = (‖l‖ : ℂ) ^ 2 * (fun h : H => ⟪h, A h⟫_ℂ) ψ := rfl
  · let L : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ :=
      { toFun := fun φ =>
          { toFun := fun ψ => ⟪φ, A ψ⟫_ℂ
            map_add' := fun x y => by simp [map_add, inner_add_right]
            map_smul' := fun c ψ => by simp [map_smul, inner_smul_right] }
        map_add' := fun x y => by ext ψ; simp [inner_add_left]
        map_smul' := fun c x => by ext ψ; simp [inner_smul_left] }
    exact ⟨L, fun φ ψ => by
      rw [hpq φ ψ]
      rfl⟩
  · refine ⟨‖A‖, fun η => ?_⟩
    calc
      ‖⟪η, A η⟫_ℂ‖ ≤ ‖η‖ * ‖A η‖ := norm_inner_le_norm η (A η)
      _ ≤ ‖η‖ * (‖A‖ * ‖η‖) := by
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm A η) (norm_nonneg η)
      _ = ‖A‖ * ‖η‖ ^ 2 := by ring

omit [CompleteSpace H] in
/--
The polarization of the quadratic form of `A` is the sesquilinear form
`(φ, ψ) ↦ ⟪φ, A ψ⟫`.

Blueprint reference: `prpstn:hall-a.62` (second part).
-/
theorem polarization_inner (A : H →L[ℂ] H) (φ ψ : H) :
    polarization (fun χ : H => ⟪χ, A χ⟫_ℂ) φ ψ = ⟪φ, A ψ⟫_ℂ := by
  unfold polarization
  have h1 : (fun χ : H => ⟪χ, A χ⟫_ℂ) (φ + ψ) - (fun χ : H => ⟪χ, A χ⟫_ℂ) φ -
      (fun χ : H => ⟪χ, A χ⟫_ℂ) ψ = ⟪φ, A ψ⟫_ℂ + ⟪ψ, A φ⟫_ℂ := by
    simp [map_add, inner_add_right, inner_add_left]
    ring
  have h2 : (fun χ : H => ⟪χ, A χ⟫_ℂ) (φ + Complex.I • ψ) -
      (fun χ : H => ⟪χ, A χ⟫_ℂ) φ - (fun χ : H => ⟪χ, A χ⟫_ℂ) (Complex.I • ψ) =
        Complex.I * ⟪φ, A ψ⟫_ℂ - Complex.I * ⟪ψ, A φ⟫_ℂ := by
    simp [map_add, map_smul, inner_add_right, inner_add_left, inner_smul_left,
      inner_smul_right]
    ring
  rw [h1, h2]
  field_simp
  simp
  ring

/--
The polarization of a bounded quadratic form, packaged as an element of
`BoundedSesquilinearForm H`. Its value function is `polarization Q`
(`IsBoundedQuadraticForm.toSesq_apply`), so nothing about it is left to choice: the
`Exists.choose`s below only pick a sesquilinear structure and a bound for a form
whose values are already pinned down.
-/
noncomputable def IsBoundedQuadraticForm.toSesq {Q : H → ℂ} (hQ : IsBoundedQuadraticForm Q) :
    BoundedSesquilinearForm H :=
  LinearMap.mkContinuous₂ hQ.isQuadratic.isSesquilinear.choose
    (exists_bound_polarization hQ).choose fun φ ψ => by
      rw [hQ.isQuadratic.isSesquilinear.choose_spec φ ψ]
      exact (exists_bound_polarization hQ).choose_spec φ ψ

omit [CompleteSpace H] in
@[simp]
theorem IsBoundedQuadraticForm.toSesq_apply {Q : H → ℂ} (hQ : IsBoundedQuadraticForm Q)
    (φ ψ : H) : hQ.toSesq φ ψ = polarization Q φ ψ :=
  hQ.isQuadratic.isSesquilinear.choose_spec φ ψ

/--
The bounded operator representing a bounded quadratic form: the Riesz
representative of the bounded sesquilinear form `polarization Q`, in Mathlib's
`InnerProductSpace.continuousLinearMapOfBilin`, transposed so that `Q ψ` is
`⟪ψ, A ψ⟫` rather than `⟪A ψ, ψ⟫`.

Downstream files should use `IsBoundedQuadraticForm.inner_toOperator` and
`IsBoundedQuadraticForm.eq_toOperator`, which between them characterise
`toOperator` completely, rather than unfolding it.
-/
noncomputable def IsBoundedQuadraticForm.toOperator {Q : H → ℂ} (hQ : IsBoundedQuadraticForm Q) :
    H →L[ℂ] H :=
  adjoint (InnerProductSpace.continuousLinearMapOfBilin hQ.toSesq)

/-- The defining property of `IsBoundedQuadraticForm.toOperator`. -/
theorem IsBoundedQuadraticForm.inner_toOperator {Q : H → ℂ} (hQ : IsBoundedQuadraticForm Q)
    (ψ : H) : Q ψ = ⟪ψ, hQ.toOperator ψ⟫_ℂ := by
  rw [IsBoundedQuadraticForm.toOperator, adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply, hQ.toSesq_apply]
  exact polarization_diag hQ.isQuadratic ψ

/--
A bounded quadratic form is represented by a unique bounded operator.

Blueprint reference: `prpstn:hall-a.63`.
-/
theorem existsUnique_operator_of_isBoundedQuadraticForm {Q : H → ℂ}
    (hQ : IsBoundedQuadraticForm Q) :
    ∃! A : H →L[ℂ] H, ∀ ψ : H, Q ψ = ⟪ψ, A ψ⟫_ℂ := by
  refine ⟨hQ.toOperator, hQ.inner_toOperator, fun A hA => ?_⟩
  have h0 : ∀ ψ : H, ⟪((A - hQ.toOperator : H →L[ℂ] H) : H →ₗ[ℂ] H) ψ, ψ⟫_ℂ = 0 := by
    intro ψ
    have hψ : ⟪ψ, (A - hQ.toOperator : H →L[ℂ] H) ψ⟫_ℂ = 0 := by
      rw [sub_apply, inner_sub_right, ← hA ψ, ← hQ.inner_toOperator ψ, sub_self]
    rw [← inner_conj_symm]
    simpa using congrArg (starRingEnd ℂ) hψ
  have hzero := (inner_map_self_eq_zero ((A - hQ.toOperator : H →L[ℂ] H) : H →ₗ[ℂ] H)).mp h0
  have : A - hQ.toOperator = 0 := by
    ext ψ
    exact congrFun (congrArg DFunLike.coe hzero) ψ
  exact sub_eq_zero.mp this

/-- `IsBoundedQuadraticForm.toOperator` is the *only* operator representing `Q`. -/
theorem IsBoundedQuadraticForm.eq_toOperator {Q : H → ℂ} (hQ : IsBoundedQuadraticForm Q)
    {A : H →L[ℂ] H} (hA : ∀ ψ : H, Q ψ = ⟪ψ, A ψ⟫_ℂ) : A = hQ.toOperator :=
  (existsUnique_operator_of_isBoundedQuadraticForm hQ).unique hA hQ.inner_toOperator

/--
An operator whose quadratic form `ψ ↦ ⟪ψ, A ψ⟫` is real-valued is self-adjoint.

This is the content of the second part of `prpstn:hall-a.63`, stripped of the
quadratic form: the blueprint hypothesis `IsBoundedQuadraticForm Q` plays no role
once `Q` is known to be `ψ ↦ ⟪ψ, A ψ⟫`, since a bounded operator is determined by,
and symmetric as soon as it is real on, its diagonal.
-/
theorem isSelfAdjoint_of_inner_self_real {A : H →L[ℂ] H}
    (hreal : ∀ ψ : H, (⟪ψ, A ψ⟫_ℂ).im = 0) : IsSelfAdjoint A := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  refine Complex.conj_eq_iff_im.mpr ?_
  have h : (starRingEnd ℂ) ⟪A v, v⟫_ℂ = ⟪v, A v⟫_ℂ := inner_conj_symm v (A v)
  have := congrArg Complex.im h
  simp only [Complex.conj_im, hreal v] at this
  simpa using this

/--
The operator representing a real-valued bounded quadratic form is self-adjoint.

Blueprint reference: `prpstn:hall-a.63` (second part).
-/
theorem IsBoundedQuadraticForm.isSelfAdjoint_toOperator {Q : H → ℂ}
    (hQ : IsBoundedQuadraticForm Q) (hreal : ∀ ψ : H, (Q ψ).im = 0) :
    IsSelfAdjoint hQ.toOperator :=
  isSelfAdjoint_of_inner_self_real fun ψ => by
    rw [← hQ.inner_toOperator ψ]; exact hreal ψ

end Spectral
end Physicslib4
