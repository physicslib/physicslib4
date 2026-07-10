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
    (flatConnection (E := E)).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  -- Bridge: mvfderiv I f x v = fderiv ℝ f x v for f : E → E
  have hbridge (f : E → E) (v : TangentSpace (modelWithCornersSelf ℝ E) x) :
      (mvfderiv (modelWithCornersSelf ℝ E) f x) v = fderiv ℝ f x v := by
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]; rfl
  -- The manifold Lie bracket reduces to the ordinary Lie bracket, which equals fderiv difference
  have hlie : VectorField.mlieBracket (modelWithCornersSelf ℝ E) X Y x =
      fderiv ℝ (Y : E → E) x (X x) - fderiv ℝ (X : E → E) x (Y x) := by
    have hmlie_to_lie : VectorField.mlieBracket (modelWithCornersSelf ℝ E) X Y x =
        VectorField.lieBracket ℝ (X : E → E) (Y : E → E) x := by
      calc
        VectorField.mlieBracket (modelWithCornersSelf ℝ E) X Y x
            = (VectorField.mlieBracketWithin (modelWithCornersSelf ℝ E) X Y Set.univ) x := by simp
        _ = (VectorField.lieBracketWithin ℝ (X : E → E) (Y : E → E) Set.univ) x := by
          have h := VectorField.mlieBracketWithin_eq_lieBracketWithin
            (𝕜 := ℝ) (V := X) (W := Y) (s := Set.univ)
          simpa using congrArg (fun f => f x) h
        _ = VectorField.lieBracket ℝ (X : E → E) (Y : E → E) x := by simp
    rw [hmlie_to_lie, VectorField.lieBracket_eq]
  -- Unfold flatConnection to mvfderiv and coerce X, Y to E → E
  dsimp [flatConnection]
  change (mvfderiv (modelWithCornersSelf ℝ E) (Y : E → E) x) (X x) -
      (mvfderiv (modelWithCornersSelf ℝ E) (X : E → E) x) (Y x) =
      VectorField.mlieBracket (modelWithCornersSelf ℝ E) X Y x
  rw [hbridge (Y : E → E) (X x), hbridge (X : E → E) (Y x), ← hlie]

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

omit [FiniteDimensional ℝ E] in
/-- **The flat connection is compatible with any constant metric.** For a metric
field that does not vary over the manifold, the metric-derivative term reduces to
the bilinear product rule (`ContinuousLinearMap.fderiv_of_bilinear`), which is
exactly the compatibility Leibniz rule since `∇ = mvfderiv`. In particular the
flat connection is compatible with the constant Minkowski metric. -/
theorem flatConnection_isMetricCompatible_const (g₀ : E →L[ℝ] E →L[ℝ] ℝ) :
    IsMetricCompatible (fun _ => g₀) (flatConnection (E := E)) := by
  intro σ τ x X₀ hσ hτ
  have dσ : DifferentiableAt ℝ σ x := by
    rw [← mdifferentiableAt_iff_differentiableAt]
    exact hσ
  have dτ : DifferentiableAt ℝ τ x := by
    rw [← mdifferentiableAt_iff_differentiableAt]
    exact hτ
  have hprod : fderiv ℝ (fun y : E => g₀ (σ y) (τ y)) x =
      g₀.precompR E (σ x) (fderiv ℝ τ x) + g₀.precompL E (fderiv ℝ σ x) (τ x) :=
    g₀.fderiv_of_bilinear dσ dτ
  have hmvf_fderiv_scalar (f : E → ℝ) (x : E) (v : TangentSpace (modelWithCornersSelf ℝ E) x) :
      (mvfderiv (modelWithCornersSelf ℝ E) f x) v = fderiv ℝ f x v := by
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]; rfl
  have hmvf_fderiv_vec (f : E → E) (x : E) (v : TangentSpace (modelWithCornersSelf ℝ E) x) :
      (mvfderiv (modelWithCornersSelf ℝ E) f x) v = fderiv ℝ f x v := by
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]; rfl
  calc
    mvfderiv (modelWithCornersSelf ℝ E) (fun y => (fun _ => g₀) y (σ y) (τ y)) x X₀
        = mvfderiv (modelWithCornersSelf ℝ E) (fun y => g₀ (σ y) (τ y)) x X₀ := by
      simp
    _ = fderiv ℝ (fun y : E => g₀ (σ y) (τ y)) x X₀ := by
      simpa using hmvf_fderiv_scalar (fun y => g₀ (σ y) (τ y)) x X₀
    _ = (g₀.precompR E (σ x) (fderiv ℝ τ x) + g₀.precompL E (fderiv ℝ σ x) (τ x)) X₀ := by
      rw [hprod]
    _ = (g₀.precompR E (σ x) (fderiv ℝ τ x)) X₀ + (g₀.precompL E (fderiv ℝ σ x) (τ x)) X₀ := rfl
    _ = g₀ (σ x) (fderiv ℝ τ x X₀) + g₀ (fderiv ℝ σ x X₀) (τ x) := by
      simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply]
    _ = g₀ (σ x) ((mvfderiv (modelWithCornersSelf ℝ E) τ x) X₀)
          + g₀ ((mvfderiv (modelWithCornersSelf ℝ E) σ x) X₀) (τ x) := by
      rw [← hmvf_fderiv_vec τ x X₀, ← hmvf_fderiv_vec σ x X₀]
    _ = g₀ (σ x) (flatConnection τ x X₀) + g₀ (flatConnection σ x X₀) (τ x) := by
      simp [flatConnection]; rfl
    _ = ((fun _ => g₀) x) (flatConnection σ x X₀) (τ x)
          + ((fun _ => g₀) x) (σ x) (flatConnection τ x X₀) := by
      ring

end Spacetime

end Physicslib4
