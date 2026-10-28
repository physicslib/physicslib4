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
blueprint, section 10.5.

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

Mathlib provides Riemannian metrics (`Bundle.ContMDiffRiemannianMetric`) but no
Lorentzian or pseudo-Riemannian metric type, so the definition is unbundled
into Mathlib primitives:

* the underlying manifold is presented as a `Type*` `M` equipped with a
  `TopologicalSpace`, `T2Space` (Hausdorff), `ConnectedSpace`, `ChartedSpace`
  with model space `ℝ⁴`, and `IsManifold I ∞ M` (smoothness `C^∞`) where
  `I` is the chosen model with corners;
* the metric `g` is a family of continuous bilinear forms
  `TₓM →L[ℝ] TₓM →L[ℝ] ℝ`, packaged together with symmetry, non-degeneracy,
  smoothness, and the Lorentzian condition at every point.

`Physicslib4.Geometry.PseudoRiemannianMetric` is derived from a `Spacetime` by
`Spacetime.toPseudoRiemannianMetric`, giving access to the general
pseudo-Riemannian API (the musical isomorphisms, the Levi-Civita connection).

The smoothness of `g` is stated in Mathlib's bundle-section idiom
(`ContMDiff` of `g` as a section of the bundle of bilinear forms on the
tangent bundle; see the `contMDiff` field), not chart by chart. The
four-dimensionality of `M` is captured by the choice of
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

open scoped Manifold ContDiff

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
A spacetime: a connected four-dimensional smooth manifold with a Lorentzian metric.

A spacetime is a real, four-dimensional, connected, smooth, Hausdorff manifold M without
boundary, together with a smooth symmetric tensor field g of type (0, 2) that is non-degenerate
and Lorentzian: at every point x there is a basis of the tangent space TₓM in which g_x is
diag(-1, 1, 1, 1). This is the signature convention (-, +, +, +), so a tangent vector v is
timelike when g_x(v, v) < 0 (`Spacetime.IsTimelike`).

The structure carries no time orientation and no topology other than the manifold topology;
these are separate data (`Spacetime.TimeOrientation`, `Spacetime.alexandrovTopology`,
`Spacetime.LorentzianSpacetime`).

Implementation note: Mathlib has no Lorentzian metric type, so the manifold and its metric are
unbundled into Mathlib primitives. The manifold is the type `Carrier` with instance fields for
the topology, the Hausdorff and connectedness conditions, the charts modelled on
`SpacetimeModel` (ℝ⁴) and `C^∞` smoothness. The metric is the family `val` of continuous
bilinear forms on the tangent spaces, with the conditions `symm`, `nondegenerate`, `lorentzian`
and `contMDiff`. Smoothness is stated as smoothness of a section of the bundle of bilinear forms
on the tangent bundle, the same shape as `Bundle.ContMDiffRiemannianMetric.contMDiff`, so
Mathlib's bundle API (`ContMDiff.clm_bundle_apply₂`) gives smoothness of x ↦ g_x(V(x), W(x))
for smooth vector fields V and W. The general pseudo-Riemannian API is reached through
`Spacetime.toPseudoRiemannianMetric`.

Blueprint: def:spacetime
-/
structure Spacetime where
  /-- The points of the spacetime manifold M. -/
  Carrier : Type*
  /-- The manifold topology of M. -/
  [topology : TopologicalSpace Carrier]
  /-- M is Hausdorff. -/
  [hausdorff : T2Space Carrier]
  /-- M is connected. -/
  [connected : ConnectedSpace Carrier]
  /-- The atlas of M, with charts valued in the model space ℝ⁴ (`SpacetimeModel`). -/
  [chartedSpace : ChartedSpace SpacetimeModel Carrier]
  /-- The model with corners of the smooth structure on M.

  It is usually `modelWithCornersSelf ℝ SpacetimeModel`; the field `boundaryless` requires
  only that it has no boundary. -/
  model : ModelWithCorners ℝ SpacetimeModel SpacetimeModel
  /-- M is a `C^∞` manifold modelled on ℝ⁴.

  Implementation note: the field is instance-implicit because the field `contMDiff` needs the
  tangent bundle's `FiberBundle` and `VectorBundle` instances, which require `IsManifold`. -/
  [isManifold : IsManifold model ∞ Carrier]
  /-- M has no boundary: chart targets are open in ℝ⁴.

  The pseudo-Riemannian layer (the Levi-Civita connection and geodesics) uses open chart
  targets. -/
  [boundaryless : model.Boundaryless]
  /-- Each tangent space TₓM is finite-dimensional. -/
  tangent_findim : ∀ x : Carrier, FiniteDimensional ℝ (TangentSpace model x)
  /-- The metric g: at each point x, a continuous bilinear form g_x on the tangent space TₓM. -/
  val : ∀ x : Carrier, TangentSpace model x →L[ℝ] TangentSpace model x →L[ℝ] ℝ
  /-- g is symmetric: g_x(v, w) = g_x(w, v). -/
  symm : ∀ (x : Carrier) (v w : TangentSpace model x),
    val x v w = val x w v
  /-- g is non-degenerate: if g_x(v, w) = 0 for every w, then v = 0. -/
  nondegenerate : ∀ (x : Carrier) (v : TangentSpace model x),
    (∀ w : TangentSpace model x, val x v w = 0) → v = 0
  /-- g is Lorentzian: at every point x some basis of TₓM has Gram matrix diag(-1, 1, 1, 1)
  (`LorentzianAt`). -/
  lorentzian : ∀ x : Carrier,
    LorentzianAt (fun v w : TangentSpace model x => val x v w)
  /-- g is smooth: it is a `C^∞` section of the bundle of continuous bilinear forms on the
  tangent bundle, whose fibre at x is the space of bilinear forms on TₓM.

  Implementation note: the statement has the shape of
  `Bundle.ContMDiffRiemannianMetric.contMDiff`, so that Mathlib's bundle API applies; in
  particular `ContMDiff.clm_bundle_apply₂` gives smoothness of x ↦ g_x(V(x), W(x)) for smooth
  vector fields V and W, which causal and geodesic arguments need. Only the shape is reused,
  not the class: `ContMDiffRiemannianMetric` also carries `pos` and `isVonNBounded`, and the
  latter is false for a Lorentzian form, since {v | g(v, v) < 1} contains the whole light cone.
  A chart-local `ContDiffWithinAt` formulation would give no route to the bundle API, since
  Mathlib has no lemma relating the two forms. -/
  contMDiff : ContMDiff model
      (model.prod 𝓘(ℝ, SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)) ∞
      (fun x ↦ Bundle.TotalSpace.mk'
        (SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)
        (E := fun x ↦ TangentSpace model x →L[ℝ] TangentSpace model x →L[ℝ] ℝ)
        x (val x))

end Physicslib4
