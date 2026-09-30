/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Physicslib4.Geometry.PseudoRiemannian.Basic

/-!
# The Levi-Civita connection of a pseudo-Riemannian metric

This file adapts Mathlib's Levi-Civita connection of a Riemannian manifold
(`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`) to a
pseudo-Riemannian metric `g`, which need not be positive definite. Mathlib's covariant
derivatives (`CovariantDerivative`) and torsion (`CovariantDerivative.torsion`) are used as they
are; the inner product of Mathlib's `IsMetricCompatible` is replaced by `g`.

## Main definitions

* `CovariantDerivative.IsMetricCompatibleWith`: `X g(σ, τ) = g(∇_X σ, τ) + g(σ, ∇_X τ)`.
* `CovariantDerivative.IsLeviCivitaFor`: torsion-free and metric-compatible.
* `PseudoRiemannianMetric.leviCivita`: the Levi-Civita connection of `g`.

## Main results

* `CovariantDerivative.IsLeviCivitaFor.koszul`: the Koszul formula.
* `CovariantDerivative.IsLeviCivitaFor.uniqueness`: uniqueness on differentiable vector fields.
* `PseudoRiemannianMetric.exists_isLeviCivitaFor`: existence.

Blueprint reference: `def:metric-compatible-connection`, `def:levi-civita-connection`,
`lmm:koszul-formula`, `thrm:levi-civita-exists-unique`.
-/

open Bundle VectorField
open scoped Manifold ContDiff

namespace Physicslib4

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E]

namespace CovariantDerivative

/-- A covariant derivative `∇` on `TM` is **compatible** with the pseudo-Riemannian metric `g`
if `X g(σ, τ) = g(∇_X σ, τ) + g(σ, ∇_X τ)` at every point where the vector fields `X`, `σ`
and `τ` are differentiable. This is the condition of Mathlib's
`CovariantDerivative.isMetricCompatible_iff`, with `g` in place of the inner product.

Blueprint reference: `def:metric-compatible-connection`. -/
def IsMetricCompatibleWith (g : PseudoRiemannianMetric I M)
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ ⦃x : M⦄ ⦃X σ τ : Π x : M, TangentSpace I x⦄,
    MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (σ y) (τ y)) x (X x))
        = g.val x (cov σ x (X x)) (τ x) + g.val x (σ x) (cov τ x (X x))

/-- A covariant derivative on `TM` is a **Levi-Civita connection** for `g` if it is
torsion-free and compatible with `g`.

Blueprint reference: `def:levi-civita-connection`. -/
structure IsLeviCivitaFor (g : PseudoRiemannianMetric I M)
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop where
  /-- Compatibility with `g`. -/
  isMetricCompatibleWith : IsMetricCompatibleWith g cov
  /-- Vanishing torsion. -/
  torsion : cov.torsion = 0

variable {g : PseudoRiemannianMetric I M}
  {cov cov' : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- **The Koszul formula.** For a Levi-Civita connection of `g` and vector fields `X`, `Y`, `Z`
differentiable at `x`, `2 g(∇_X Y, Z)` is expressed through derivatives of `g` and Lie brackets
alone, without reference to `∇`. This is Mathlib's `IsLeviCivitaConnection.apply_eq` multiplied
by 2, with `g` in place of the inner product; the blueprint's form of the formula is the same
statement after `mlieBracket_swap` and the symmetry of `g`.

Blueprint reference: `lmm:koszul-formula`. -/
theorem IsLeviCivitaFor.koszul (h : IsLeviCivitaFor g cov) {x : M}
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g.val x (cov Y x (X x)) (Z x) =
      (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (Y y) (Z y)) x (X x))
      + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (Z y) (X y)) x (Y x))
      - (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (X y) (Y y)) x (Z x))
      - g.val x (Y x) (mlieBracket I X Z x)
      - g.val x (Z x) (mlieBracket I Y X x)
      + g.val x (X x) (mlieBracket I Z Y x) := by
  -- use the compatibility with `g` in three ways
  have eq1a := h.isMetricCompatibleWith hX hY hZ
  have eq2a := h.isMetricCompatibleWith hY hZ hX
  have eq3a := h.isMetricCompatibleWith hZ hX hY
  -- use the torsion-freeness in three ways
  have eq1b := congr(g.val x (Y x) ($(h.torsion) x (X x) (Z x)))
  have eq2b := congr(g.val x (Z x) ($(h.torsion) x (Y x) (X x)))
  have eq3b := congr(g.val x (X x) ($(h.torsion) x (Z x) (Y x)))
  rw [cov.torsion_apply hX hZ] at eq1b
  rw [cov.torsion_apply hY hX] at eq2b
  rw [cov.torsion_apply hZ hY] at eq3b
  simp only [map_sub, Pi.zero_apply, zero_apply, map_zero] at eq1b eq2b eq3b
  -- align the order of the arguments of `g`
  rw [g.symm x (cov Z x (Y x)) (X x)] at eq2a
  rw [g.symm x (cov X x (Z x)) (Y x)] at eq3a
  rw [g.symm x (Z x) (cov Y x (X x))] at eq2b
  linear_combination -(eq1a + eq2a - eq3a + eq1b + eq2b - eq3b)

/-- **Uniqueness of the Levi-Civita connection.** Two Levi-Civita connections of `g` agree on
every vector field differentiable at `x`. (Covariant derivatives are unconstrained on
non-differentiable vector fields, as in Mathlib's `IsLeviCivitaConnection.uniqueness`.)

Blueprint reference: `thrm:levi-civita-exists-unique`. -/
theorem IsLeviCivitaFor.uniqueness (hcov : IsLeviCivitaFor g cov)
    (hcov' : IsLeviCivitaFor g cov') {x : M} {Y : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (X₀ : TangentSpace I x) :
    cov Y x X₀ = cov' Y x X₀ := by
  set X := FiberBundle.extend E X₀
  have hX : MDiffAt (T% X) x := FiberBundle.mdifferentiableAt_extend I E X₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have key : g.val x (cov Y x X₀) = g.val x (cov' Y x X₀) := by
    apply VectorBundle.injective_eval_mdifferentiableAt_sec I E (TangentSpace I) ℝ x
    ext Z hZ
    have h1 := hcov.koszul hX hY hZ
    have h2 := hcov'.koszul hX hY hZ
    rw [hXx] at h1 h2
    simp only
    linarith
  have h := g.nondegenerate x (cov Y x X₀ - cov' Y x X₀) fun w ↦ by
    rw [map_sub, key, sub_self, zero_apply]
  exact sub_eq_zero.mp h

end CovariantDerivative

namespace PseudoRiemannianMetric

/-- **Existence of the Levi-Civita connection.** Every pseudo-Riemannian metric has a
Levi-Civita connection.

Blueprint reference: `thrm:levi-civita-exists-unique`. -/
theorem exists_isLeviCivitaFor (g : PseudoRiemannianMetric I M) :
    ∃ cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _),
      CovariantDerivative.IsLeviCivitaFor g cov := by
  sorry

/-- A choice of **Levi-Civita connection** of `g`. It is unique on differentiable vector fields
(`CovariantDerivative.IsLeviCivitaFor.uniqueness`).

Blueprint reference: `thrm:levi-civita-exists-unique`. -/
noncomputable def leviCivita (g : PseudoRiemannianMetric I M) :
    _root_.CovariantDerivative I E (TangentSpace I : M → Type _) :=
  g.exists_isLeviCivitaFor.choose

/-- The chosen `leviCivita` connection is a Levi-Civita connection of `g`. -/
theorem isLeviCivitaFor_leviCivita (g : PseudoRiemannianMetric I M) :
    CovariantDerivative.IsLeviCivitaFor g g.leviCivita :=
  g.exists_isLeviCivitaFor.choose_spec

end PseudoRiemannianMetric

end Geometry

end Physicslib4
