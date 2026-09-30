/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Geometry.PseudoRiemannian.LeviCivita

/-!
# The flat connection on a vector space

On a finite-dimensional real vector space `E`, viewed as a manifold over itself, the tangent
bundle is trivial and the ordinary directional derivative `∇_v σ = Dσ(v)` is a covariant
derivative. For a pseudo-Riemannian metric that is constant (the same bilinear form at every
point), it is the Levi-Civita connection. This is the flat case used for Minkowski spacetime.

## Main definitions

* `Physicslib4.Geometry.flatConnection`: `σ ↦ (x ↦ fderiv ℝ σ x)`.

## Main results

* `PseudoRiemannianMetric.isLeviCivitaFor_flatConnection`: for a constant metric, the flat
  connection is a Levi-Civita connection.
* `PseudoRiemannianMetric.leviCivita_apply_eq_fderiv`: hence the Levi-Civita connection of a
  constant metric is the directional derivative on differentiable vector fields.

Blueprint reference: `lmm:minkowski-directional-derivative-levi-civita`,
`lmm:minkowski-levi-civita-flat`.
-/

open Bundle
open scoped Manifold ContDiff

namespace Physicslib4

namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The directional derivative is a covariant derivative on the tangent bundle of `E`.

Blueprint reference: `lmm:minkowski-directional-derivative-levi-civita`. -/
theorem isCovariantDerivativeOn_fderiv :
    IsCovariantDerivativeOn E
      (fun (σ : Π x : E, TangentSpace 𝓘(ℝ, E) x) (x : E) ↦
        (fderiv ℝ (fun y ↦ (σ y : E)) x : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x))
      Set.univ := by
  have hd : ∀ {σ : Π x : E, TangentSpace 𝓘(ℝ, E) x} {x : E}, MDiffAt (T% σ) x →
      DifferentiableAt ℝ (F := E) (fun y ↦ σ y) x := fun {σ x} h ↦
    mdifferentiableAt_iff_differentiableAt.1 <|
      ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E) (n := 1)).mdifferentiable
        one_ne_zero _).comp x h
  refine ⟨fun {σ σ' x} hσ hσ' _ ↦ ?_, fun {σ g x} hσ hg _ ↦ ?_⟩
  · have h := fderiv_add (F := E) (hd hσ) (hd hσ')
    exact h
  · have h := fderiv_smul (F := E) (mdifferentiableAt_iff_differentiableAt.1 hg) (hd hσ)
    rw [← mfderiv_eq_fderiv (E := E) (E' := ℝ)] at h
    exact h

/-- The **flat connection** on `E`: `∇_v σ = Dσ(v)`.

Blueprint reference: `lmm:minkowski-directional-derivative-levi-civita`. -/
noncomputable def flatConnection :
    _root_.CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _) where
  toFun σ x := fderiv ℝ (fun y ↦ (σ y : E)) x
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_fderiv E

theorem flatConnection_apply (σ : Π x : E, TangentSpace 𝓘(ℝ, E) x) (x : E)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    flatConnection E σ x v = fderiv ℝ (fun y ↦ (σ y : E)) x v := rfl

namespace PseudoRiemannianMetric

variable {E} [FiniteDimensional ℝ E]

/-- For a metric that is the same bilinear form `B` at every point, the flat connection is a
Levi-Civita connection.

Blueprint reference: `lmm:minkowski-directional-derivative-levi-civita`. -/
theorem isLeviCivitaFor_flatConnection (g : PseudoRiemannianMetric 𝓘(ℝ, E) E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hg : ∀ x, g.val x = B) :
    CovariantDerivative.IsLeviCivitaFor g (flatConnection E) := by
  have hdiff : ∀ {V : Π x : E, TangentSpace 𝓘(ℝ, E) x} {x : E}, MDiffAt (T% V) x →
      DifferentiableAt ℝ (fun y ↦ (V y : E)) x := fun {V x} h ↦
    ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).mdifferentiableAt one_ne_zero
      |>.comp x h).differentiableAt
  refine ⟨fun x X σ τ _ hσ hτ ↦ ?_, ?_⟩
  · have h1 := hdiff hσ
    have h2 := hdiff hτ
    have hfun : (fun y ↦ g.val y (σ y) (τ y)) = fun y ↦ B (σ y) (τ y) :=
      funext fun y ↦ by rw [hg]; rfl
    simp only [hg, flatConnection_apply]
    rw [hfun, mfderiv_eq_fderiv, (B.hasFDerivAt_of_bilinear h1.hasFDerivAt h2.hasFDerivAt).fderiv]
    exact add_comm _ _
  · rw [_root_.CovariantDerivative.torsion_eq_zero_iff]
    intro X Y x _ _
    rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin]
    have := VectorField.lieBracketWithin_univ (𝕜 := ℝ) (V := fun y ↦ (X y : E))
      (W := fun y ↦ (Y y : E))
    exact ((congrFun this x).trans (congrFun (VectorField.lieBracket_eq (𝕜 := ℝ)) x)).symm

/-- **The Levi-Civita connection of a constant metric is flat**: on vector fields
differentiable at `x`, it is the directional derivative.

Blueprint reference: `lmm:minkowski-levi-civita-flat`. -/
theorem leviCivita_apply_eq_fderiv (g : PseudoRiemannianMetric 𝓘(ℝ, E) E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hg : ∀ x, g.val x = B) {X : Π x : E, TangentSpace 𝓘(ℝ, E) x}
    {x : E} (hX : MDiffAt (T% X) x) (v : TangentSpace 𝓘(ℝ, E) x) :
    g.leviCivita X x v = fderiv ℝ (fun y ↦ (X y : E)) x v :=
  (g.isLeviCivitaFor_leviCivita.uniqueness (g.isLeviCivitaFor_flatConnection B hg) hX v).trans
    (flatConnection_apply E X x v)

end PseudoRiemannianMetric

end Geometry

end Physicslib4
