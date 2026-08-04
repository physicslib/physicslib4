/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Spacetime

This file formalises the notion of a *spacetime* used in the AQFT-in-Lean
blueprint, section 10.2.

## Main definitions

* `Physicslib4.LorentzianAt`: the pointwise "Lorentzian" condition on a
  symmetric bilinear form on a real four-dimensional vector space, asserting
  the existence of a basis with respect to which the Gram matrix is the
  diagonal matrix `diag(-1, 1, 1, 1)`.
* `Physicslib4.Spacetime`: a real, four-dimensional, connected, smooth,
  Hausdorff manifold `M` together with a globally defined smooth,
  non-degenerate, symmetric, Lorentzian `(0, 2)` tensor field `g`.
  This corresponds to the blueprint label `def:spacetime`.

## Modelling notes

Mathlib (at `v4.31.0-rc1`) does not provide a packaged "Lorentzian manifold"
or "pseudo-Riemannian metric" type. The closest thing — `PseudoRiemannianMetric`
— lives in the downstream `PhysLean` library, which is not a dependency of
this project. We therefore unbundle the definition into Mathlib primitives:

* the underlying manifold is presented as a `Type*` `M` equipped with a
  `TopologicalSpace`, `T2Space` (Hausdorff), `ConnectedSpace`, `ChartedSpace`
  with model space `ℝ⁴`, and `IsManifold I ∞ M` (smoothness `C^∞`) where
  `I` is the chosen model with corners;
* the metric `g` is a family of continuous bilinear forms
  `TₓM →L[ℝ] TₓM →L[ℝ] ℝ`, packaged together with symmetry, non-degeneracy,
  smoothness in charts, and the Lorentzian condition at every point.

The "smoothness" of `g` is encoded via the standard idiom used by
`PseudoRiemannianMetric`: smoothness of the coordinate-expression in any
extended chart, applied to two arbitrary constant vectors in the model
space `ℝ⁴`. The four-dimensionality of `M` is captured by the choice of
model space `EuclideanSpace ℝ (Fin 4)`.

The Lorentzian condition is captured by `LorentzianAt`: existence of a basis
`b` of the tangent space such that `g (b i) (b j)` equals
`diag(-1, 1, 1, 1) i j` (i.e. `-1` on the `0` index of the diagonal, `1` on
the other three diagonal entries, and `0` off-diagonal).

The structure carries `sorry`-free *statements*; the structure itself is a
plain `structure` definition and contains no proof obligations beyond those
carried by its fields.
-/

namespace Physicslib4

open scoped Manifold

/-- The model space `ℝ⁴` for a spacetime, written using `EuclideanSpace`. -/
abbrev SpacetimeModel : Type := EuclideanSpace ℝ (Fin 4)

/-- The signature matrix `diag(-1, 1, 1, 1)` of a Lorentzian inner product on
`ℝ⁴`, written as a function `Fin 4 → Fin 4 → ℝ`. -/
def lorentzSignature : Fin 4 → Fin 4 → ℝ :=
  Matrix.diagonal (fun i : Fin 4 => if i = 0 then (-1 : ℝ) else 1)

/--
A symmetric bilinear form `g` on a real four-dimensional vector space `V` is
*Lorentzian* if there exists a basis `b : Basis (Fin 4) ℝ V` of `V` such that
`g (b i) (b j) = lorentzSignature i j` for every `i j : Fin 4`.

This matches the blueprint condition that there is a basis relative to which
`g` is `diag(-1, 1, 1, 1)` (i.e. zero off-diagonal and `-1, 1, 1, 1` on the
diagonal).
-/
def LorentzianAt {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : V → V → ℝ) : Prop :=
  ∃ b : Module.Basis (Fin 4) ℝ V,
    ∀ i j : Fin 4, g (b i) (b j) = lorentzSignature i j

/--
A *spacetime*, in the sense of the AQFT-in-Lean blueprint (section 10.2,
`def:spacetime`), is a real, four-dimensional, connected, smooth, Hausdorff
manifold `M` equipped with a globally defined smooth tensor field `g` of type
`(0,2)` which is non-degenerate and Lorentzian.

The underlying manifold data is bundled as the carrier type `Carrier` together
with topological and smooth-manifold typeclass instances (Hausdorff,
connected, `C^∞` `ChartedSpace` modelled on `SpacetimeModel = ℝ⁴`).

The metric `g` is encoded as a family of continuous bilinear forms
`val : ∀ x, TₓM →L[ℝ] TₓM →L[ℝ] ℝ`, with the following pointwise conditions:

* `symm`: each `val x` is symmetric;
* `nondegenerate`: each `val x` is non-degenerate;
* `lorentzian`: each `val x` is Lorentzian;
* `contMDiff`: `g` is smooth, stated in Mathlib's bundle-section idiom as
  `C^∞`-ness of `x ↦ TotalSpace.mk' _ x (val x)` as a section of the bundle of
  continuous bilinear forms on the tangent bundle. This has the same shape as
  `Bundle.ContMDiffRiemannianMetric.contMDiff`, so Mathlib's bundle API applies
  directly — notably `ContMDiff.clm_bundle_apply₂`, giving smoothness of
  `x ↦ g x (V x) (W x)` for smooth vector fields `V, W`.

The non-degeneracy is stated as: if `g x v w = 0` for every `w`, then `v = 0`.

Blueprint reference: `def:spacetime`.
-/
structure Spacetime where
  /-- The underlying point set of the spacetime manifold. -/
  Carrier : Type*
  /-- The topology on the carrier. -/
  [topology : TopologicalSpace Carrier]
  /-- The Hausdorff condition. -/
  [hausdorff : T2Space Carrier]
  /-- The connectedness condition. -/
  [connected : ConnectedSpace Carrier]
  /-- The chart structure giving the manifold a four-dimensional model space. -/
  [chartedSpace : ChartedSpace SpacetimeModel Carrier]
  /-- The model with corners used to define the smooth structure on `Carrier`.
  Typically the trivial / boundaryless one `modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))`. -/
  model : ModelWithCorners ℝ SpacetimeModel SpacetimeModel
  /-- `Carrier` is a `C^∞` manifold modelled on `SpacetimeModel = ℝ⁴`.

  This is instance-implicit so that it is available to the later `contMDiff`
  field: the bundle-section statement there needs the tangent bundle's
  `FiberBundle` / `VectorBundle` instances, which are gated on `IsManifold`. -/
  [isManifold : IsManifold model ⊤ Carrier]
  /-- Each tangent space is finite-dimensional. -/
  tangent_findim : ∀ x : Carrier, FiniteDimensional ℝ (TangentSpace model x)
  /-- The metric tensor `g`, presented as a family of continuous bilinear forms
  on the tangent spaces. -/
  val : ∀ x : Carrier, TangentSpace model x →L[ℝ] TangentSpace model x →L[ℝ] ℝ
  /-- Symmetry of `g`: `g x v w = g x w v`. -/
  symm : ∀ (x : Carrier) (v w : TangentSpace model x),
    val x v w = val x w v
  /-- Non-degeneracy of `g`: if `g x v w = 0` for every `w`, then `v = 0`. -/
  nondegenerate : ∀ (x : Carrier) (v : TangentSpace model x),
    (∀ w : TangentSpace model x, val x v w = 0) → v = 0
  /-- The Lorentzian condition at every point: there exists a basis of the
  tangent space relative to which `g x` has Gram matrix `diag(-1, 1, 1, 1)`. -/
  lorentzian : ∀ x : Carrier,
    LorentzianAt (fun v w : TangentSpace model x => val x v w)
  /-- Smoothness of `g`, stated in Mathlib's **bundle-section** idiom: `g` is a
  `C^∞` section of the bundle of continuous bilinear forms on the tangent
  bundle, whose fibre at `x` is `TₓM →L[ℝ] TₓM →L[ℝ] ℝ`.

  This is deliberately the same shape as `Bundle.ContMDiffRiemannianMetric.contMDiff`.
  Mathlib has no pseudo-Riemannian metric class — `ContMDiffRiemannianMetric`
  additionally carries `pos` and `isVonNBounded`, and the latter is not merely
  unproven but *false* for a Lorentzian form, since `{v | g v v < 1}` contains
  the whole light cone — so only the shape of that field is reused here, not the
  class itself.

  The payoff is that this is the form Mathlib's bundle API speaks natively: in
  particular `ContMDiff.clm_bundle_apply₂` then gives smoothness of
  `x ↦ g x (V x) (W x)` for smooth vector fields `V, W`, which is what causal
  and geodesic arguments need. The previous chart-local `ContDiffWithinAt`
  formulation had no route to it, since Mathlib provides no lemma bridging the
  two forms in either direction. -/
  contMDiff : ContMDiff model
      (model.prod 𝓘(ℝ, SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)) ⊤
      (fun x ↦ Bundle.TotalSpace.mk'
        (SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)
        (E := fun x ↦ TangentSpace model x →L[ℝ] TangentSpace model x →L[ℝ] ℝ)
        x (val x))

end Physicslib4
