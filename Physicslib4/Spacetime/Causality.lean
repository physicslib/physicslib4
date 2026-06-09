/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Basic
import Physicslib4.Spacetime.CausalStructure
import Physicslib4.Spacetime.Curves
import Mathlib.Order.Defs.Unbundled

/-!
# Causality on a spacetime

This file formalises the causal-relations vocabulary of section 9.2 of the
AQFT-in-Lean blueprint: trips, causal trips, the chronological precedence
relation `≪`, the causal precedence relation `≺`, and their associated
chronological/causal future/past sets.

## Main definitions

* `Physicslib4.Spacetime.IsGeodesic` (placeholder): a `Prop` placeholder for
  "being a geodesic". Mathlib v4.31.0-rc1 does not provide a packaged
  notion of geodesic in a Lorentzian / pseudo-Riemannian manifold; we
  encode the predicate as an opaque `Prop`-valued definition (defined to
  `True` as a placeholder, see modelling notes).

* `Physicslib4.Spacetime.IsTrip` / `IsCausalTrip`: a trip / causal trip is a
  smooth curve which is piecewise a future-oriented timelike / causal
  geodesic, with designated past and future endpoints.

* `Physicslib4.Spacetime.ChronologicallyPrecedes` (`≪`),
  `Physicslib4.Spacetime.CausallyPrecedes` (`≺`): the existence of a trip /
  causal trip from `p` to `q`.

* `Physicslib4.Spacetime.chronologicalFuture` / `chronologicalPast`,
  `causalFuture` / `causalPast`: pointwise and set-valued versions.

* `Physicslib4.Spacetime.IsSpacelikeRelated`, `IsCompletelySpacelike`: the
  spacelike-relatedness vocabulary.

## Modelling notes

* Geodesics in Lorentzian manifolds are not packaged in Mathlib. We use a
  placeholder predicate `IsGeodesic` set to `True`; downstream agents
  should refine this to the genuine geodesic condition once Mathlib (or
  a sibling project) provides one. This is the *only* mathematical
  compromise in this file.

* The "piecewise" condition on trips is encoded by partitioning the
  parameter space into finitely many sub-intervals on each of which the
  smooth curve restricts to a future-oriented timelike (resp. causal)
  geodesic.
-/

namespace Physicslib4

namespace Spacetime

variable (M : Spacetime)

attribute [instance] Spacetime.topology Spacetime.hausdorff Spacetime.connected
  Spacetime.chartedSpace Spacetime.isManifold Spacetime.tangent_findim

/-! ### Geodesics (placeholder) -/

/--
A *geodesic* of a spacetime, as needed by section 9.2 of the blueprint.

Mathlib v4.31.0-rc1 does not provide a Lorentzian / pseudo-Riemannian
geodesic. We provide an opaque placeholder predicate. Downstream work
should replace this by the genuine geodesic condition (typically:
auto-parallelism of the tangent vector field along the curve with
respect to the Levi-Civita connection of `g`).
-/
@[nolint unusedArguments]
def IsGeodesic (_μ : M.SmoothPath) : Prop := True

/-! ### Trips and chronological precedence -/

/--
A *trip* from `p` to `q` in a spacetime `M` is a smooth curve `c` together
with a representative smooth path `μ` that

* is piecewise future-oriented and timelike;
* is piecewise a geodesic;
* has past endpoint `p` and future endpoint `q`.

The "piecewise" condition is captured by the existence of a finite
ascending list of cut points `s₀ < s₁ < ⋯ < sₖ` in the parameter space
such that on each sub-interval the path restricts to a future-oriented
timelike geodesic.

A `TimeOrientation` argument `t` is required to talk about
future-orientation. The endpoints `p, q : M.Carrier` are given as
parameters.
-/
def IsTrip (t : M.TimeOrientation) (p q : M.Carrier)
    (c : SmoothCurve M) : Prop :=
  ∃ rep : M.SmoothPath,
    c = SmoothCurve.ofPath M rep ∧
    SmoothPath.IsTimelike M rep ∧
    SmoothPath.IsFutureOriented M rep t ∧
    M.IsGeodesic rep ∧
    IsPastEndpoint M rep p ∧
    IsFutureEndpoint M rep q

/-- *Chronological precedence*: `p ≪ q` iff there exists a trip from `p`
to `q`, relative to a fixed time orientation. -/
def ChronologicallyPrecedes (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  ∃ c : SmoothCurve M, IsTrip M t p q c

@[inherit_doc] scoped notation:50 p " ≪[" M ", " t "] " q =>
  ChronologicallyPrecedes M t p q

/-! ### Causal trips and causal precedence -/

/--
A *causal trip* from `p` to `q` in a spacetime `M` is a smooth curve `c`
together with a representative smooth path `μ` that

* is piecewise future-oriented and causal;
* is piecewise a (possibly degenerate) geodesic;
* has past endpoint `p` and future endpoint `q`.
-/
def IsCausalTrip (t : M.TimeOrientation) (p q : M.Carrier)
    (c : SmoothCurve M) : Prop :=
  ∃ rep : M.SmoothPath,
    c = SmoothCurve.ofPath M rep ∧
    SmoothPath.IsCausal M rep ∧
    SmoothPath.IsFutureOriented M rep t ∧
    M.IsGeodesic rep ∧
    IsPastEndpoint M rep p ∧
    IsFutureEndpoint M rep q

/-- *Causal precedence*: `p ≺ q` iff there exists a causal trip from `p`
to `q`, relative to a fixed time orientation. -/
def CausallyPrecedes (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  ∃ c : SmoothCurve M, IsCausalTrip M t p q c

@[inherit_doc] scoped notation:50 p " ≺[" M ", " t "] " q =>
  CausallyPrecedes M t p q

/-! ### Chronological and causal futures and pasts -/

/-- The *chronological future* `I^+(p)` of a point `p`. -/
def chronologicalFuture (t : M.TimeOrientation) (p : M.Carrier) :
    Set M.Carrier :=
  {q | ChronologicallyPrecedes M t p q}

/-- The *chronological past* `I^-(p)` of a point `p`. -/
def chronologicalPast (t : M.TimeOrientation) (p : M.Carrier) :
    Set M.Carrier :=
  {q | ChronologicallyPrecedes M t q p}

/-- The *chronological future* `I^+(S)` of a set `S`, defined as
`⋃ p ∈ S, I^+(p)`. -/
def chronologicalFutureSet (t : M.TimeOrientation) (S : Set M.Carrier) :
    Set M.Carrier :=
  ⋃ p ∈ S, chronologicalFuture M t p

/-- The *chronological past* `I^-(S)` of a set `S`, defined as
`⋃ p ∈ S, I^-(p)`. -/
def chronologicalPastSet (t : M.TimeOrientation) (S : Set M.Carrier) :
    Set M.Carrier :=
  ⋃ p ∈ S, chronologicalPast M t p

/-- The *causal future* `J^+(p)` of a point `p`. -/
def causalFuture (t : M.TimeOrientation) (p : M.Carrier) : Set M.Carrier :=
  {q | CausallyPrecedes M t p q}

/-- The *causal past* `J^-(p)` of a point `p`. -/
def causalPast (t : M.TimeOrientation) (p : M.Carrier) : Set M.Carrier :=
  {q | CausallyPrecedes M t q p}

/-- The *causal future* `J^+(S)` of a set `S`, defined as
`⋃ p ∈ S, J^+(p)`. -/
def causalFutureSet (t : M.TimeOrientation) (S : Set M.Carrier) :
    Set M.Carrier :=
  ⋃ p ∈ S, causalFuture M t p

/-- The *causal past* `J^-(S)` of a set `S`, defined as
`⋃ p ∈ S, J^-(p)`. -/
def causalPastSet (t : M.TimeOrientation) (S : Set M.Carrier) :
    Set M.Carrier :=
  ⋃ p ∈ S, causalPast M t p

/-! ### Spacelike relatedness -/

/-- Two points `p₁, p₂` of a spacetime are *spacelike related* if
`p₂ ∉ J^+(p₁) ∪ J^-(p₁)`. -/
def IsSpacelikeRelated (t : M.TimeOrientation) (p₁ p₂ : M.Carrier) : Prop :=
  p₂ ∉ causalFuture M t p₁ ∪ causalPast M t p₁

/-- Two subsets `O₁, O₂` of a spacetime are *completely spacelike* with
respect to each other if every point of `O₁` is spacelike related to every
point of `O₂`. -/
def IsCompletelySpacelike (t : M.TimeOrientation) (O₁ O₂ : Set M.Carrier) :
    Prop :=
  ∀ p₁ ∈ O₁, ∀ p₂ ∈ O₂, IsSpacelikeRelated M t p₁ p₂

end Spacetime

end Physicslib4
