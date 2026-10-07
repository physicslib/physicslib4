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
  a linear isomorphism `T_xM → T_x*M` (the musical isomorphism), packaged as `flatEquiv`.
* `Physicslib4.Geometry.PseudoRiemannianMetric.contMDiff_flatEquiv_symm`: `x ↦ ♭_x⁻¹` is a `C^∞`
  section of `Hom(T*M, TM)`.

Blueprint reference: `def:pseudo-riemannian-metric`, `lmm:musical-isomorphism`,
`lmm:musical-inverse-smooth`.
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

/-- The musical isomorphism `♭_x : T_xM ≃ T_x*M`, `v ↦ g_x(v, ·)`, as a continuous linear
equivalence (`bijective_val`; continuity of the inverse is automatic in finite dimension).

Blueprint reference: `lmm:musical-isomorphism`. -/
noncomputable def flatEquiv [FiniteDimensional ℝ E] (g : PseudoRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  (LinearEquiv.ofBijective (g.val x : TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ))
    (g.bijective_val x)).toContinuousLinearEquiv

theorem flatEquiv_apply [FiniteDimensional ℝ E] (g : PseudoRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : g.flatEquiv x v = g.val x v :=
  rfl

/-- **Smoothness of the inverse musical isomorphism.** The map `x ↦ ♭_x⁻¹` is a `C^∞` section of
the bundle `Hom(T*M, TM)`, whose fibre at `x` is `T_x*M →L[ℝ] T_xM`, stated in the same
bundle-section idiom as the smoothness of `g` itself.

Blueprint reference: `lmm:musical-inverse-smooth`. -/
theorem contMDiff_flatEquiv_symm [FiniteDimensional ℝ E] (g : PseudoRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' ((E →L[ℝ] ℝ) →L[ℝ] E)
        (E := fun x ↦ (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x) x
        ((g.flatEquiv x).symm : (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hg := (contMDiffAt_hom_bundle _).1 (g.contMDiff x₀) |>.2
  simp only at hg ⊢
  have h₁ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have h₂ : x₀ ∈ (trivializationAt (E →L[ℝ] ℝ)
      (fun x ↦ TangentSpace I x →L[ℝ] ℝ) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hinv := (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)
    (e := ContinuousLinearMap.inCoordinates E (TangentSpace I)
      (E →L[ℝ] ℝ) (fun x ↦ TangentSpace I x →L[ℝ] ℝ) x₀ x₀ x₀ x₀ (g.val x₀)) ?_).contMDiffAt
  · refine (hinv.comp x₀ hg).congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt _ _ x₀).open_baseSet.mem_nhds h₁,
      (trivializationAt _ _ x₀).open_baseSet.mem_nhds h₂] with x hx hx'
    simp only [Function.comp_apply]
    rw [ContinuousLinearMap.inCoordinates_eq hx hx', ContinuousLinearMap.inCoordinates_eq hx' hx]
    change _ = ContinuousLinearMap.inverse
      (_ ∘L ((g.flatEquiv x : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) ∘L _))
    simp only [ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv,
      ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.symm_symm]
    rfl
  · rw [ContinuousLinearMap.inCoordinates_eq h₁ h₂]
    change ContinuousLinearMap.IsInvertible
      (_ ∘L ((g.flatEquiv x₀ : TangentSpace I x₀ →L[ℝ] (TangentSpace I x₀ →L[ℝ] ℝ)) ∘L _))
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (ContinuousLinearMap.isInvertible_equiv.comp ContinuousLinearMap.isInvertible_equiv)

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
