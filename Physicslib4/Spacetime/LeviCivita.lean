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

end SpacetimeWithLeviCivita

end Physicslib4
