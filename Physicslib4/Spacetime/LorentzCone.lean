/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.LorentzCauchySchwarz

/-!
# Convexity of the timelike cone and the reverse triangle inequality

This file formalises the blueprint declaration `lmm:timelike-cone-convexity`
(Chapter 10, `sections/sec10/10-2_spacetime`).

For a symmetric Lorentzian bilinear form `g` (signature `diag(-1,1,1,1)`) two
timelike vectors `v, w` are *aligned* (share a time cone) when `g v w ≤ 0`. For
such vectors:

* `v + w` is again timelike (convexity of the timelike cone), and
* the *reverse* (Lorentzian) triangle inequality holds:
  `√(-(g v v)) + √(-(g w w)) ≤ √(-(g (v+w) (v+w)))`.

The closure under addition is elementary; the reverse triangle inequality is the
substantive statement and consumes the reverse Cauchy-Schwarz inequality
`reverse_cauchy_schwarz_of_lorentzianAt` (`lmm:reverse-cauchy-schwarz`).

The abstract lemmas depend only on the algebraic `LorentzianAt` condition, so
they transfer verbatim to the metric `g|_p` of any spacetime;
`Spacetime.add_isTimelike` and `Spacetime.reverse_triangle` are the
specialisations.

## Modelling note

The alignment hypothesis `g v w ≤ 0` encodes "`v` and `w` lie in the same time
cone". For two future-pointing timelike vectors this sign holds, but proving it
from the future-pointing condition alone requires the positive-definiteness of
the spacelike complement (a signature/inertia argument), which is not available
from the pointwise `LorentzianAt` data; we therefore take the sign as an
explicit hypothesis.
-/

namespace Physicslib4

/-- Bilinear expansion of `B (v + w) (v + w)` using bilinearity and symmetry. -/
private theorem bilin_add_self {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v) (v w : V) :
    B (v + w) (v + w) = B v v + 2 * B v w + B w w := by
  simp only [map_add, LinearMap.add_apply]
  rw [hsymm w v]; ring

/-- **Convexity of the timelike cone.** The sum of two aligned timelike vectors
(`g v w ≤ 0`) of a symmetric Lorentzian bilinear form is again timelike. -/
theorem add_isTimelike_of_lorentzianAt
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    {v w : V} (hv : B v v < 0) (hw : B w w < 0) (haligned : B v w ≤ 0) :
    B (v + w) (v + w) < 0 := by
  rw [bilin_add_self hsymm]; linarith

/-- **Reverse (Lorentzian) triangle inequality** for two aligned timelike
vectors of a symmetric Lorentzian bilinear form. This is where the reverse
Cauchy-Schwarz inequality is consumed. -/
theorem reverse_triangle_of_lorentzianAt
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    (hL : LorentzianAt (fun v w => B v w))
    {v w : V} (hv : B v v < 0) (hw : B w w < 0) (haligned : B v w ≤ 0) :
    Real.sqrt (-(B v v)) + Real.sqrt (-(B w w))
      ≤ Real.sqrt (-(B (v + w) (v + w))) := by
  have ha : (0 : ℝ) ≤ -(B v v) := by linarith
  have hb : (0 : ℝ) ≤ -(B w w) := by linarith
  have hc : (0 : ℝ) ≤ -(B v w) := by linarith
  -- Reverse Cauchy-Schwarz, rephrased for the nonnegative quantities.
  have hcs : B v v * B w w ≤ (B v w) ^ 2 :=
    reverse_cauchy_schwarz_of_lorentzianAt hsymm hL hv hw
  have hab : (-(B v v)) * (-(B w w)) ≤ (-(B v w)) ^ 2 := by nlinarith [hcs]
  -- Hence `√a · √b ≤ c`.
  have hprod : Real.sqrt (-(B v v)) * Real.sqrt (-(B w w)) ≤ -(B v w) := by
    rw [← Real.sqrt_mul ha]
    calc Real.sqrt ((-(B v v)) * (-(B w w)))
        ≤ Real.sqrt ((-(B v w)) ^ 2) := Real.sqrt_le_sqrt hab
      _ = -(B v w) := Real.sqrt_sq hc
  -- Compare squares and take square roots.
  have key : (Real.sqrt (-(B v v)) + Real.sqrt (-(B w w))) ^ 2
      ≤ -(B (v + w) (v + w)) := by
    have e1 : Real.sqrt (-(B v v)) ^ 2 = -(B v v) := Real.sq_sqrt ha
    have e2 : Real.sqrt (-(B w w)) ^ 2 = -(B w w) := Real.sq_sqrt hb
    rw [bilin_add_self hsymm]
    nlinarith [hprod, e1, e2]
  calc Real.sqrt (-(B v v)) + Real.sqrt (-(B w w))
      = Real.sqrt ((Real.sqrt (-(B v v)) + Real.sqrt (-(B w w))) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (-(B (v + w) (v + w))) := Real.sqrt_le_sqrt key

namespace Spacetime

/-- Bilinear expansion of `g|_p (v + w) (v + w)` for a spacetime metric. -/
private theorem val_add_self (M : Spacetime) (x : M.Carrier)
    (v w : TangentSpace M.model x) :
    M.val x (v + w) (v + w) = M.val x v v + 2 * M.val x v w + M.val x w w := by
  simp only [map_add, ContinuousLinearMap.add_apply]
  rw [M.symm x w v]; ring

/-- **Convexity of the timelike cone** for the metric of a spacetime: the sum of
two aligned timelike tangent vectors (`g|_p(v,w) ≤ 0`) at a point is timelike. -/
theorem add_isTimelike (M : Spacetime) (x : M.Carrier)
    {v w : TangentSpace M.model x}
    (hv : M.IsTimelike v) (hw : M.IsTimelike w) (haligned : M.val x v w ≤ 0) :
    M.IsTimelike (v + w) := by
  have hv' : M.val x v v < 0 := hv
  have hw' : M.val x w w < 0 := hw
  change M.val x (v + w) (v + w) < 0
  rw [val_add_self M x]; linarith

/-- **Reverse (Lorentzian) triangle inequality** for the metric of a spacetime:
two aligned timelike tangent vectors at a point satisfy
`√(-g(v,v)) + √(-g(w,w)) ≤ √(-g(v+w,v+w))`. -/
theorem reverse_triangle (M : Spacetime) (x : M.Carrier)
    {v w : TangentSpace M.model x}
    (hv : M.IsTimelike v) (hw : M.IsTimelike w) (haligned : M.val x v w ≤ 0) :
    Real.sqrt (-(M.val x v v)) + Real.sqrt (-(M.val x w w))
      ≤ Real.sqrt (-(M.val x (v + w) (v + w))) := by
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
  have hal' : B v w ≤ 0 := by rw [hBapp]; exact haligned
  have h := reverse_triangle_of_lorentzianAt (B := B) hsymm hL hv' hw' hal'
  simpa only [hBapp] using h

end Spacetime

end Physicslib4
