/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-!
# Reverse Cauchy-Schwarz inequality for timelike vectors

This file formalises the blueprint declaration `lmm:reverse-cauchy-schwarz`
(Chapter 10, `sections/sec10/10-2_spacetime`).

For a symmetric Lorentzian bilinear form `g` (signature `diag(-1,1,1,1)`) and two
timelike vectors `v, w` (i.e. `g v v < 0`, `g w w < 0`) the *reverse* Cauchy-Schwarz
inequality holds:
```
g v v * g w w ≤ (g v w) ^ 2.
```

The abstract statement `reverse_cauchy_schwarz_of_lorentzianAt` depends only on the
pointwise `LorentzianAt` condition, so it transfers verbatim to the metric `g|_p` of
any spacetime; `Spacetime.reverse_cauchy_schwarz` is that specialisation.

## Proof strategy

Expand `v, w` in a Lorentzian basis `b`, so `g x y` is the diagonal sum
`-(x⁰y⁰) + x¹y¹ + x²y² + x³y³` of the coordinates `xⁱ = b.repr x i`. The vector
`u = w⁰ • v - v⁰ • w` has vanishing time coordinate, hence `g u u ≥ 0`; together with
the algebraic identity
```
(w⁰)² * ((g v w)² - g v v * g w w)
  = (g v w * w⁰ - g w w * v⁰)² + (-(g w w)) * (g u u)
```
and `w⁰ ≠ 0` (forced by `g w w < 0`) this gives the inequality.
-/

namespace Physicslib4

open scoped BigOperators

/-- **Reverse Cauchy-Schwarz inequality** for two timelike vectors of a symmetric
Lorentzian bilinear form on a real four-dimensional vector space. -/
theorem reverse_cauchy_schwarz_of_lorentzianAt
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    (hL : LorentzianAt (fun v w => B v w))
    {v w : V} (hv : B v v < 0) (hw : B w w < 0) :
    B v v * B w w ≤ (B v w) ^ 2 := by
  obtain ⟨b, hb⟩ := hL
  -- Coordinate (diagonal) expansion of the bilinear form in the Lorentzian basis.
  have coord : ∀ x y : V, B x y =
      -(b.repr x 0 * b.repr y 0)
        + (b.repr x 1 * b.repr y 1 + b.repr x 2 * b.repr y 2 + b.repr x 3 * b.repr y 3) := by
    intro x y
    have step2 : ∀ i : Fin 4, B (b i) y = ∑ j, b.repr y j * lorentzSignature i j := by
      intro i
      conv_lhs => rw [← b.sum_repr y]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, hb]
    have step1 : B x y = ∑ i, ∑ j, b.repr x i * (b.repr y j * lorentzSignature i j) := by
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, step2 i, Finset.mul_sum]
    rw [step1]
    simp only [lorentzSignature, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Fin.sum_univ_four]
    norm_num
    ring
  -- The time coordinate of `w` is nonzero, since `w` is timelike.
  have hwexp := hw
  rw [coord w w] at hwexp
  have hwc0 : (0 : ℝ) < b.repr w 0 * b.repr w 0 := by
    nlinarith [mul_self_nonneg (b.repr w 1), mul_self_nonneg (b.repr w 2),
      mul_self_nonneg (b.repr w 3)]
  -- `g u u ≥ 0` for `u = w⁰ • v - v⁰ • w`, packaged directly in terms of `B v v`, etc.
  have hH : 0 ≤ (b.repr w 0 * b.repr w 0) * B v v
      - 2 * (b.repr v 0 * b.repr w 0) * B v w
      + (b.repr v 0 * b.repr v 0) * B w w := by
    rw [coord v v, coord v w, coord w w]
    nlinarith [mul_self_nonneg (b.repr w 0 * b.repr v 1 - b.repr v 0 * b.repr w 1),
      mul_self_nonneg (b.repr w 0 * b.repr v 2 - b.repr v 0 * b.repr w 2),
      mul_self_nonneg (b.repr w 0 * b.repr v 3 - b.repr v 0 * b.repr w 3)]
  -- Algebraic certificate.
  have hkey : 0 ≤ (b.repr w 0 * b.repr w 0) * ((B v w) ^ 2 - B v v * B w w) := by
    nlinarith [mul_self_nonneg (B v w * b.repr w 0 - B w w * b.repr v 0),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -(B w w)) hH]
  nlinarith [hkey, hwc0]

namespace Spacetime

/-- **Reverse Cauchy-Schwarz inequality** for the metric of a spacetime: two timelike
tangent vectors at a point satisfy `g v v * g w w ≤ (g v w) ^ 2`. -/
theorem reverse_cauchy_schwarz (M : Spacetime) (x : M.Carrier)
    {v w : TangentSpace M.model x}
    (hv : M.IsTimelike v) (hw : M.IsTimelike w) :
    M.val x v v * M.val x w w ≤ (M.val x v w) ^ 2 := by
  let B : LinearMap.BilinForm ℝ (TangentSpace M.model x) :=
    LinearMap.mk₂ ℝ (fun a c => M.val x a c)
      (fun a₁ a₂ c => by simp) (fun r a c => by simp)
      (fun a c₁ c₂ => by simp) (fun r a c => by simp)
  have hBapp : ∀ a c, B a c = M.val x a c := fun a c => rfl
  have hsymm : ∀ a c, B a c = B c a := by
    intro a c; rw [hBapp, hBapp]; exact M.symm x a c
  have hL : LorentzianAt (fun a c => B a c) := by
    simpa only [hBapp] using M.lorentzian x
  have hv' : B v v < 0 := by rw [hBapp]; exact hv
  have hw' : B w w < 0 := by rw [hBapp]; exact hw
  have h := reverse_cauchy_schwarz_of_lorentzianAt (B := B) hsymm hL hv' hw'
  simpa only [hBapp] using h

end Spacetime

end Physicslib4
