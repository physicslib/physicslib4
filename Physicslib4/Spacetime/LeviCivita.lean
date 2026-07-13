/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Minkowski
import Physicslib4.Spacetime.Connection

/-!
# Spacetimes with a Levi-Civita connection

This file bundles a `Spacetime` together with a **Levi-Civita connection**: a
covariant derivative on the tangent bundle that is *forced* to be torsion-free
and compatible with the metric `g`.

## Design

The connection is bundled in the richer structure `SpacetimeWithLeviCivita`
rather than as a field of `Spacetime` itself. This is deliberate:

* it keeps `Spacetime` as pure geometric data (a manifold with a metric), so a
  spacetime need not come equipped with a connection;
* the connection here is **not free data**: the two proof fields force it to be
  torsion-free and metric-compatible, and since the metric `g` is
  non-degenerate such a connection is *unique*. Hence `connection` is
  determined by the metric and cannot contradict it — the concern that motivated
  the constrained design.

## Main definitions

* `Physicslib4.SpacetimeWithLeviCivita`: a spacetime with its Levi-Civita
  connection (a bundled torsion-free, metric-compatible covariant derivative).
* `Physicslib4.SpacetimeWithLeviCivita.standardMinkowski`: standard Minkowski
  spacetime with its flat Levi-Civita connection.
-/

open scoped Manifold

namespace Physicslib4

/--
A `Spacetime` together with its **Levi-Civita connection**: a bundled covariant
derivative `connection` on the tangent bundle, constrained by the two proof
fields to be torsion-free and compatible with the metric `g`. Because `g` is
non-degenerate, a torsion-free metric-compatible connection is unique, so
`connection` is *determined* by the metric — it cannot contradict it.

The connection lives on this richer structure rather than on `Spacetime` so that
a bare `Spacetime` remains pure geometric data; only spacetimes whose
Levi-Civita connection has been formalised carry a `SpacetimeWithLeviCivita`.
-/
structure SpacetimeWithLeviCivita extends Spacetime where
  /-- The Levi-Civita connection on the tangent bundle. -/
  connection :
    CovariantDerivative toSpacetime.model SpacetimeModel
      (TangentSpace toSpacetime.model : toSpacetime.Carrier → Type _)
  /-- The connection is **torsion-free**. -/
  connection_torsionFree : connection.torsion = 0
  /-- The connection is **compatible** with the metric `g`. Together with
  torsion-freeness this pins `connection` down as the Levi-Civita connection of
  the metric. -/
  connection_metricCompatible :
    Spacetime.IsMetricCompatible toSpacetime.val connection

namespace SpacetimeWithLeviCivita

/-- **Standard Minkowski spacetime with its Levi-Civita connection.** The flat
connection `∇σ = mvfderiv σ` is torsion-free and compatible with the constant
Minkowski metric, hence is the Levi-Civita connection. -/
noncomputable def standardMinkowski : SpacetimeWithLeviCivita where
  toSpacetime := StandardMinkowskiSpacetime
  connection := Spacetime.flatConnection
  connection_torsionFree := Spacetime.flatConnection_torsion
  connection_metricCompatible :=
    Spacetime.flatConnection_isMetricCompatible_const minkowskiForm

/--
A smooth path `μ` is a **geodesic** of the Levi-Civita connection `∇` if it is
*auto-parallel*, i.e. `∇_{μ'} μ' = 0` along `μ`.

Mathlib provides a covariant derivative only on *global* sections of the tangent
bundle (`M.connection : (∀ x, TₓM) → (∀ x, TₓM →L TₓM)`), not a derivative of a
vector field *along a curve*. We therefore phrase auto-parallelism by asking for
a global vector field `V` that restricts to the velocity `μ.tangent` along `μ`
and whose covariant derivative in the velocity direction vanishes on `μ`:
`(∇_{V} V)(μ s) = M.connection V (μ s) (V (μ s)) = 0`. Because `(∇_X σ) x`
depends only on `X x` and the germ of `σ` at `x`, this value is the genuine
covariant acceleration `∇_{μ'} μ'` and is independent of the chosen extension
`V`.

This is a genuine condition (contrast the placeholder
`Physicslib4.Spacetime.IsGeodesic := True`), now available for any spacetime
carrying a Levi-Civita connection.
-/
def IsGeodesic (M : SpacetimeWithLeviCivita) (μ : M.toSpacetime.SmoothPath) : Prop :=
  ∃ V : ∀ x, TangentSpace M.toSpacetime.model x,
    (∀ s ∈ μ.parameterSpace, V (μ.toFun s) = μ.tangent s) ∧
    (∀ s ∈ μ.parameterSpace, M.connection V (μ.toFun s) (V (μ.toFun s)) = 0)

/-- **Straight lines are geodesics in Minkowski spacetime.** The line-segment
path `s ↦ p + s(q-p)` satisfies the auto-parallel condition: its constant
velocity `q - p` extends to the constant vector field `V ≡ q - p`, whose flat
covariant derivative vanishes (`mvfderiv` of a constant is `0`). This witnesses
that `IsGeodesic` is inhabited and genuinely non-trivial. -/
theorem standardMinkowski_lineSegment_isGeodesic
    (p q : SpacetimeModel) (hpq : p ≠ q) :
    standardMinkowski.IsGeodesic (standardMinkowskiLineSegmentPath p q hpq) := by
  refine ⟨fun _ => q - p, ?_, ?_⟩
  · intro s hs
    change q - p = (standardMinkowskiLineSegmentPath p q hpq).tangent s
    rw [Spacetime.SmoothPath.tangent_def]
    exact (standardMinkowskiLineSegmentPath_mfderivWithin p q s hs).symm
  · intro s _
    change mvfderiv (modelWithCornersSelf ℝ SpacetimeModel) (fun _ => q - p)
        ((standardMinkowskiLineSegmentPath p q hpq).toFun s) (q - p) = 0
    rw [mvfderiv_const]
    simp

end SpacetimeWithLeviCivita

end Physicslib4
