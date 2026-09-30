/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Physicslib4.Spacetime.Basic

/-!
# Pseudo-Riemannian metrics

A *pseudo-Riemannian metric* on a manifold `M` modelled on `(E, H)` with model `I` is a
smooth family of symmetric, nondegenerate continuous bilinear forms on the tangent spaces.
Unlike Mathlib's `Bundle.ContMDiffRiemannianMetric`, no positivity is required, so Lorentzian
metrics are included. The smoothness condition has the same bundle-section shape as
`Bundle.ContMDiffRiemannianMetric.contMDiff`.

## Main definitions

* `Physicslib4.Geometry.PseudoRiemannianMetric`: the structure.
* `Physicslib4.Spacetime.toPseudoRiemannianMetric`: the metric of a spacetime.

## Main results

* `Physicslib4.Geometry.PseudoRiemannianMetric.bijective_val`: at each point, `v ↦ g_x(v, ·)` is
  a linear isomorphism `T_xM → T_x*M` (the musical isomorphism).

Blueprint reference: `def:pseudo-riemannian-metric`, `lmm:musical-isomorphism`.
-/

open Bundle
open scoped Manifold ContDiff

namespace Physicslib4

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A **pseudo-Riemannian metric** on `M`: a smooth section `g` of the bundle of continuous
bilinear forms on `TM` that is symmetric and nondegenerate at every point. No positivity is
required.

Blueprint reference: `def:pseudo-riemannian-metric`. -/
structure PseudoRiemannianMetric where
  /-- The bilinear form `g_x` on `T_xM`. -/
  val : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- Symmetry: `g_x(v, w) = g_x(w, v)`. -/
  symm : ∀ (x : M) (v w : TangentSpace I x), val x v w = val x w v
  /-- Nondegeneracy: if `g_x(v, w) = 0` for all `w`, then `v = 0`. -/
  nondegenerate : ∀ (x : M) (v : TangentSpace I x), (∀ w, val x v w = 0) → v = 0
  /-- Smoothness of `g` as a section of the bundle of bilinear forms on `TM`. -/
  contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (val x))

namespace PseudoRiemannianMetric

variable {I M}

/-- **The musical isomorphism.** At each point `x`, the map `v ↦ g_x(v, ·)` from `T_xM` to its
dual is bijective: injective by nondegeneracy and hence bijective since `T_xM` is
finite-dimensional.

Blueprint reference: `lmm:musical-isomorphism`. -/
theorem bijective_val [FiniteDimensional ℝ E] (g : PseudoRiemannianMetric I M) (x : M) :
    Function.Bijective (g.val x) := by
  let A : E →L[ℝ] E →L[ℝ] ℝ := g.val x
  change Function.Bijective A
  have hinj : Function.Injective (A : E →ₗ[ℝ] E →L[ℝ] ℝ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun v hv ↦ g.nondegenerate x v fun w ↦ DFunLike.congr_fun hv w
  have hrank : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq]
    exact (Subspace.dual_finrank_eq).symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj⟩

end PseudoRiemannianMetric

end Geometry

attribute [local instance] Spacetime.topology Spacetime.chartedSpace Spacetime.isManifold

/-- The metric of a spacetime is a pseudo-Riemannian metric on its manifold.

Blueprint reference: `def:pseudo-riemannian-metric`. -/
def Spacetime.toPseudoRiemannianMetric (M : Spacetime) :
    Geometry.PseudoRiemannianMetric M.model M.Carrier where
  val := M.val
  symm := M.symm
  nondegenerate := M.nondegenerate
  contMDiff := M.contMDiff

end Physicslib4
