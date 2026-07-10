/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# The flat covariant derivative on a self-modelled manifold

This file builds the **flat (trivial) covariant derivative** on the tangent
bundle of a self-modelled real manifold `E` (with model
`𝓘(ℝ, E) = modelWithCornersSelf ℝ E`). On the self-model a section of the
tangent bundle is just a vector field `σ : E → E`, and the flat connection is
the ordinary manifold-vector derivative `mvfderiv`: `∇σ = d% σ`.

This is Phase 1 of upgrading `Physicslib4.Spacetime.IsGeodesic` from a
placeholder to a genuine connection-relative auto-parallel condition
(Levi-Civita geodesics). Mathlib provides the `CovariantDerivative` structure
but no flat/canonical instance; we supply it here. The Minkowski tangent
bundle is a special case (`E = EuclideanSpace ℝ (Fin 4)`), and this flat
connection is the Levi-Civita connection of the flat Minkowski metric.

## Main definitions

* `Physicslib4.Spacetime.flatConnection`: the flat covariant derivative on the
  tangent bundle of a self-modelled manifold, `∇σ = mvfderiv`.
-/

open scoped Manifold

namespace Physicslib4

namespace Spacetime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/--
The **flat covariant derivative** on the tangent bundle of the self-modelled
manifold `E`: it sends a vector field `σ : E → E` to its manifold-vector
derivative `mvfderiv 𝓘(ℝ, E) σ`. Additivity and the Leibniz rule are exactly
`mvfderiv_add` and `mvfderiv_smul`; the section-differentiability hypotheses are
bridged through the identity trivialization of the self-modelled tangent bundle.
-/
noncomputable def flatConnection :
    CovariantDerivative (modelWithCornersSelf ℝ E) E
      (TangentSpace (modelWithCornersSelf ℝ E) : E → Type _) where
  toFun σ := mvfderiv (modelWithCornersSelf ℝ E) σ
  isCovariantDerivativeOnUniv := by
    refine {
      add := ?_
      leibniz := ?_
    }
    · intro σ σ' x hσ hσ' _
      let τ : E → E := σ
      let τ' : E → E := σ'
      have hτ : MDiffAt (T% σ) x := hσ
      have hτ' : MDiffAt (T% σ') x := hσ'
      have b1 : MDiffAt τ x := by
        rw [mdifferentiableAt_section] at hτ
        simpa [trivializationAt_model_space_apply, τ] using hτ
      have b2 : MDiffAt τ' x := by
        rw [mdifferentiableAt_section] at hτ'
        simpa [trivializationAt_model_space_apply, τ'] using hτ'
      have : d% (τ + τ') x = d% τ x + d% τ' x := mvfderiv_add b1 b2
      simpa [τ, τ']
    · intro σ g x hσ hg _
      let τ : E → E := σ
      have hτ : MDiffAt (T% σ) x := hσ
      have b1 : MDiffAt τ x := by
        rw [mdifferentiableAt_section] at hτ
        simpa [trivializationAt_model_space_apply, τ] using hτ
      have : d% (g • τ) x = g x • d% τ x + (d% g x).smulRight (τ x) := mvfderiv_smul hg b1
      simpa [τ]

/-- **The flat connection is torsion-free.** On the self-model, both the
covariant-difference `∇_X Y - ∇_Y X` and the Lie bracket `[X, Y]` collapse to
`fderiv Y (X) - fderiv X (Y)` (via `mlieBracketWithin_eq_lieBracketWithin` and
`mfderiv_eq_fderiv`), so the torsion vanishes identically. Together with metric
compatibility this identifies `flatConnection` as the Levi-Civita connection of
the flat metric. -/
theorem flatConnection_torsion :
    (flatConnection (E := E)).torsion = 0 := by sorry

/--
**Indefinite metric compatibility.** A covariant derivative `cov` on the tangent
bundle is *compatible* with a (possibly indefinite) metric field `g` if the
Leibniz rule for the metric holds in every direction `X₀`:
`X₀⟪σ, τ⟫ = ⟪∇_{X₀} σ, τ⟫ + ⟪σ, ∇_{X₀} τ⟫`, where `⟪·,·⟫` is `g`. This is the
indefinite (Lorentzian) analogue of Mathlib's
`CovariantDerivative.IsMetricCompatible`, which is stated only for a
positive-definite inner-product bundle and so does not apply to a Lorentzian
metric.
-/
def IsMetricCompatible
    (g : ∀ x : E, TangentSpace (modelWithCornersSelf ℝ E) x →L[ℝ]
          TangentSpace (modelWithCornersSelf ℝ E) x →L[ℝ] ℝ)
    (cov : CovariantDerivative (modelWithCornersSelf ℝ E) E
          (TangentSpace (modelWithCornersSelf ℝ E) : E → Type _)) : Prop :=
  ∀ (σ τ : ∀ x, TangentSpace (modelWithCornersSelf ℝ E) x) (x : E)
    (X₀ : TangentSpace (modelWithCornersSelf ℝ E) x),
    MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) σ x →
    MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) τ x →
      mvfderiv (modelWithCornersSelf ℝ E) (fun y => g y (σ y) (τ y)) x X₀
        = g x (cov σ x X₀) (τ x) + g x (σ x) (cov τ x X₀)

/-- **The flat connection is compatible with any constant metric.** For a metric
field that does not vary over the manifold, the metric-derivative term reduces to
the bilinear product rule (`ContinuousLinearMap.fderiv_of_bilinear`), which is
exactly the compatibility Leibniz rule since `∇ = mvfderiv`. In particular the
flat connection is compatible with the constant Minkowski metric. -/
theorem flatConnection_isMetricCompatible_const (g₀ : E →L[ℝ] E →L[ℝ] ℝ) :
    IsMetricCompatible (fun _ => g₀) (flatConnection (E := E)) := by sorry

end Spacetime

end Physicslib4
