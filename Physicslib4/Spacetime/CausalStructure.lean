/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.Basic

/-!
# Causal structure on a spacetime

This file formalises the pointwise causal structure attached to a spacetime,
following section 10.2 of the AQFT-in-Lean blueprint.

## Main definitions

* `Physicslib4.Spacetime.IsTimelike`, `IsSpacelike`, `IsNull`: classification of
  tangent vectors by the sign of `g x v v`.
* `Physicslib4.Spacetime.TimeOrientation`: a smooth non-vanishing global
  timelike vector field, presented as a section of the tangent bundle.
* `Physicslib4.Spacetime.IsTimeOrientable`: existence of a time orientation.
* `Physicslib4.Spacetime.IsFuturePointing` / `IsPastPointing`: the classification
  of timelike (and null, by a limit construction) tangent vectors against a
  chosen time orientation.

## Modelling notes

Mathlib does not currently package "smooth vector field" as a single named type.
We use the obvious unbundled form: a function `t : ∀ x, TangentSpace M.model x`
together with two pointwise predicates (non-vanishing and timelike) and an
unbundled smoothness statement carried as a `Prop` field. Smoothness of a
section of the tangent bundle is captured exactly as in `Spacetime.smooth_in_charts`:
by writing the chart-local expression and requiring `ContDiffWithinAt`.

For the null future/past-pointing case we follow the blueprint and define
future-pointing null vectors as the closure (in the obvious tangent space
topology coming from `TangentSpace M.model x ≃ ℝ⁴`) of the set of
future-pointing timelike vectors. We capture this with the existence of a
sequence of future-pointing timelike vectors tending to `n`. The underlying
topology on each tangent space is inherited from Mathlib's tangent space
typeclass instances.
-/

namespace Physicslib4

namespace Spacetime

variable (M : Spacetime)

attribute [instance] Spacetime.topology Spacetime.hausdorff Spacetime.connected
  Spacetime.chartedSpace Spacetime.isManifold Spacetime.tangent_findim

/-! ### Classification of tangent vectors -/

/-- A tangent vector `v ∈ T_pM` is *timelike* if `g|_p(v,v) < 0`. -/
def IsTimelike {x : M.Carrier} (v : TangentSpace M.model x) : Prop :=
  M.val x v v < 0

/-- A tangent vector `v ∈ T_pM` is *spacelike* if `g|_p(v,v) > 0`. -/
def IsSpacelike {x : M.Carrier} (v : TangentSpace M.model x) : Prop :=
  0 < M.val x v v

/-- A tangent vector `v ∈ T_pM` is *null* if `g|_p(v,v) = 0`. -/
def IsNull {x : M.Carrier} (v : TangentSpace M.model x) : Prop :=
  M.val x v v = 0

/-! ### Time orientation -/

/--
A *time orientation* on a spacetime `M` is a smooth, non-vanishing,
everywhere-timelike vector field on `M`.

We unbundle the data as:
* `field : ∀ x, T_xM`, the pointwise tangent vector;
* `nonvanishing`: `field x ≠ 0` for all `x`;
* `timelike_at`: `field x` is timelike at every `x`;
* `smooth`: smoothness of the section in any extended chart, expressed via
  the chart-local form of the field; we leave the precise smoothness
  predicate as a `sorry`-able `Prop` field of the structure, since
  Mathlib does not currently package smooth sections of the tangent
  bundle in a one-line way.
-/
structure TimeOrientation where
  /-- The underlying tangent vector field. -/
  field : ∀ x : M.Carrier, TangentSpace M.model x
  /-- The field is everywhere non-zero. -/
  nonvanishing : ∀ x : M.Carrier, field x ≠ 0
  /-- The field is timelike at every point. -/
  timelike_at : ∀ x : M.Carrier, M.IsTimelike (field x)
  /-- The field is smooth as a section of the tangent bundle. We express this
  via smoothness of its chart-local representative; see `Spacetime.smooth_in_charts`
  for the analogous condition for the metric. -/
  smooth : ∀ (x₀ : M.Carrier),
    let e := extChartAt M.model x₀
    ContDiffWithinAt ℝ ⊤
      (fun y => mfderiv M.model M.model (e.symm) y
                  (mfderiv M.model M.model e (e.symm y) (field (e.symm y))))
      e.target (e x₀)

/-- A spacetime `M` is *time-orientable* if it admits a time orientation. -/
def IsTimeOrientable : Prop := Nonempty M.TimeOrientation

/-! ### Future and past pointing vectors -/

/-- A timelike tangent vector `v` is *future-pointing* with respect to a time
orientation `t` if `g|_p(t,v) < 0`. The blueprint also extends this notion to
null vectors by taking limits of timelike future-pointing vectors. -/
def IsFuturePointing (t : M.TimeOrientation) {x : M.Carrier}
    (v : TangentSpace M.model x) : Prop :=
  (M.IsTimelike v ∧ M.val x (t.field x) v < 0) ∨
  (M.IsNull v ∧
    ∃ vs : ℕ → TangentSpace M.model x,
      (∀ n, M.IsTimelike (vs n) ∧ M.val x (t.field x) (vs n) < 0) ∧
      Filter.Tendsto vs Filter.atTop (nhds v))

/-- A timelike tangent vector `v` is *past-pointing* with respect to a time
orientation `t` if `g|_p(t,v) > 0`. The blueprint also extends this notion to
null vectors by taking limits of timelike past-pointing vectors. -/
def IsPastPointing (t : M.TimeOrientation) {x : M.Carrier}
    (v : TangentSpace M.model x) : Prop :=
  (M.IsTimelike v ∧ 0 < M.val x (t.field x) v) ∨
  (M.IsNull v ∧
    ∃ vs : ℕ → TangentSpace M.model x,
      (∀ n, M.IsTimelike (vs n) ∧ 0 < M.val x (t.field x) (vs n)) ∧
      Filter.Tendsto vs Filter.atTop (nhds v))

end Spacetime

end Physicslib4
