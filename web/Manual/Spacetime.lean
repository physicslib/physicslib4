import VersoManual
import Book.Meta
import Physicslib4.Spacetime.Causality
import Physicslib4.Spacetime.CausalComplement
import Physicslib4.Spacetime.LorentzianSpacetime
import Physicslib4.Spacetime.LorentzOrthogonal
import Physicslib4.Spacetime.LorentzCone
import Physicslib4.Spacetime.MinkowskiDilation
import Physicslib4.Spacetime.CrossMetricIsometry
import Physicslib4.Spacetime.Minkowski
import Physicslib4.Spacetime.MinkowskiDirected
import Physicslib4.Spacetime.LorentzCausality
import Physicslib4.Spacetime.IsometryTopology
import Physicslib4.Spacetime.IsometryCausality
import Physicslib4.Geometry.PseudoRiemannian.LeviCivita
import Physicslib4.Geometry.PseudoRiemannian.Flat
-- Imported only so that names in the docstrings shown below resolve and link.
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Physicslib4.AQFT.HaagKastlerCurved.Concrete

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book
-- Docstring code spans are elaborated in this scope; these namespaces let the names they mention,
-- written relative to the library's namespaces, resolve and link.
open Physicslib4 Physicslib4.Spacetime Physicslib4.Spacetime.LorentzianSpacetime
open Physicslib4.Spacetime.Isometry
open Physicslib4.Geometry Physicslib4.Geometry.PseudoRiemannianMetric
open Physicslib4.Geometry.CovariantDerivative

#doc (Manual) "Spacetime and geometry" =>

%%%
tag := "spacetime"
file := "Spacetime-and-geometry"
%%%

This chapter describes how the library encodes spacetimes, their causal structure, the regions to
which the Haag–Kastler axioms attach algebras, the symmetries that act on them, and the geometry
underneath: the Levi-Civita connection and geodesics. It corresponds to Section 10.5 of the
[blueprint](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:spacetime).
The physics is introduced in [chapter 1 of the tutorial](../tutorial/AQFT-in-brief/), and the Lean
needed to read the declarations in [chapter 2](../tutorial/Lean-in-brief/); this chapter assumes
both.

# Overview
%%%
tag := "spacetime-overview"
%%%

As you will recall, the Haag–Kastler axioms need three things from spacetime: a family of regions
(the causal diamonds), a notion of when two regions are spacelike separated, and a group of
symmetries that maps regions to regions. The library builds all three from a single structure, a
four-dimensional Lorentzian manifold, and states the causal notions for any spacetime, not only for
Minkowski space. The section has five parts.

* *Spacetimes.* `Spacetime` is a connected, Hausdorff, smooth four-manifold without boundary with a
  smooth Lorentzian metric of signature $`(-,+,+,+)`. A `TimeOrientation` is a smooth timelike
  vector field, which fixes the future half of each light cone. Standard Minkowski spacetime
  `StandardMinkowskiSpacetime` is $`\mathbb{R}^4` with the constant metric
  $`\eta = \mathrm{diag}(-1,1,1,1)`.
* *Causal structure.* Chronological precedence $`p \ll q` and causal precedence $`p \prec q` are
  defined by curves, as chains of future-oriented timelike or causal geodesic segments, so that the
  same definitions serve a curved spacetime. From them come the futures and pasts $`I^\pm(p)` and
  $`J^\pm(p)`, spacelike separation, and the causality condition.
* *Diamonds and the Alexandrov topology.* The chronological diamonds $`I^+(p) \cap I^-(q)` generate
  the Alexandrov topology. On Minkowski space the diamonds form a basis and the Alexandrov topology
  is the Euclidean one. A `LorentzianSpacetime` is a spacetime with a time orientation whose
  Alexandrov topology is Hausdorff; its causally complete regions form a complete orthocomplemented
  lattice under the causal complement $`\mathbf{B} \mapsto \mathbf{B}^\perp`.
* *Symmetries.* The Lorentz transformations of $`\mathbb{R}^4` and the inhomogeneous Lorentz group
  for Minkowski space; the isometry group of a general spacetime, its identity component and the
  oriented identity component, the group of the curved-spacetime Axiom 5.
* *The pseudo-Riemannian layer.* `Geometry.PseudoRiemannianMetric` is a smooth symmetric
  non-degenerate metric of any signature, with its Levi-Civita connection, constructed without
  charts. Geodesics of a spacetime are defined with it.

From these the library proves, among other things:

* $`\prec` is reflexive and transitive, and a partial order when there is no closed causal curve;
  causal trips are then asymmetric, and $`\ll` is irreflexive;
* no point is spacelike to itself, so a region and its spacelike complement are disjoint;
* on Minkowski space, $`I^+(p)` is the open forward light cone, the Alexandrov topology equals the
  Euclidean topology, the diamonds form a basis, and any two diamonds lie in a common diamond;
* the causal complement is an orthocomplementation of the lattice of causally complete regions;
* causal precedence, spacelike separation and the diamonds are invariant under the inhomogeneous
  Lorentz group, and isometries preserving the time orientation map diamonds to diamonds;
* every pseudo-Riemannian metric has a Levi-Civita connection, unique on differentiable vector
  fields; on Minkowski space it is the ordinary derivative, so the geodesics are the straight lines
  at constant velocity; isometries map geodesics to geodesics.

The declarations are in the namespaces `Physicslib4`, `Physicslib4.Spacetime` and
`Physicslib4.Geometry`, written below without the prefix `Physicslib4`.

# Design
%%%
tag := "spacetime-design"
%%%

The conventions of the causal structure are stated once in the conventions chapter, under
{ref "conventions-causal"}[Causal structure].

The blueprint is the specification, and its entries record the reasons for the choices below. The
reasons for the regions and topology of Minkowski space are set out at length in the blueprint's
[chapter 2](https://physicslib.github.io/physicslib4/blueprint/chptr-axiom-0--minkowski-space-.html),
which is context and is not formalised.

## A spacetime is a structure

Mathlib has Riemannian metrics but no Lorentzian or pseudo-Riemannian ones, so `Spacetime` is
built from Mathlib's primitives: a structure bundling the carrier type, its topology and atlas as
instance fields, and the metric `val` with its conditions. Two details of the encoding matter when
reading the Lean.

* _Smoothness is a bundle condition._ The field `contMDiff` has the shape of the smoothness field
  of Mathlib's `Bundle.ContMDiffRiemannianMetric`, so Mathlib's bundle API applies; the Riemannian
  class itself is not used, since its positivity fields fail for a Lorentzian form.
* _The time orientation is separate data._ It is an argument of every causal notion, as in
  `ChronologicallyPrecedes M t p q`, written `p ≪[M, t] q`.

The blueprint entry [def:spacetime](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacetime)
records the reasons for the smoothness clause and the regularity index; the
{ref "conventions-causal"}[conventions chapter] explains the index.

## Minkowski space and the Alexandrov topology

As you will recall from [chapter 1 of the tutorial](../tutorial/AQFT-in-brief/#physicslib4-tutorial--AQFT-in-brief--Regions-of-spacetime--Causal-diamonds),
the 1964 axioms attach algebras to open sets without naming the topology, and the project uses the
Alexandrov topology, generated by the diamonds $`I^+(p) \cap I^-(q)`. It is defined from the light
cones alone, and on Minkowski space it coincides with the Euclidean topology.

The library has two Minkowski spacetimes, which differ only in the topology instance on the
carrier: `StandardMinkowskiSpacetime`, with the Euclidean topology, on which all the Minkowski
results are stated, and `MinkowskiSpacetime`, the blueprint's Minkowski spacetime, with the
Alexandrov topology. They are interchangeable because the two topologies coincide
(`alexandrov_eq_euclidean_standardMinkowski`). `Spacetime.alexandrovTopology M t` is a reducible
definition, not an instance, so that it never competes with the manifold topology on the same
type; a statement about it names it explicitly, as `@IsOpen M.Carrier (alexandrovTopology M t)`.

## Paths and curves

Two design points of the definitions matter. A smooth path has a velocity $`\dot\mu(s)` that
vanishes nowhere, endpoints included; this excludes constant paths, so a null path moves along the
light cone instead of resting at a point. And past and future endpoints are defined by extremality
of the parameter, not by the boundary of the parameter interval $`\Sigma`, so they make sense for
every parameter space, including $`[0, \infty)` and $`\mathbb{R}` (blueprint
[def:endpoints](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:endpoints)).

## Causal precedence is defined by curves

On Minkowski space $`p \prec q` could be defined by vectors: $`q - p` is causal and
future-directed, or zero. The library defines it by curves, as the blueprint does, so that one
definition serves every spacetime: $`p \ll q` and `IsCausalTrip t p q` are chains of one or more
timelike or causal geodesic segments, and $`p \prec q` is a chain of zero or more causal segments.

So $`\prec` is reflexive, $`p \prec p` for every $`p`, while `IsCausalTrip` is strict;
`causallyPrecedes_iff_eq_or_isCausalTrip` connects the two. Two consequences are worth knowing. No
point is spacelike to itself, so a region and its spacelike complement are disjoint. And the
causality condition `NoClosedCausalCurve` is stated with the strict relation, as "no causal trip
from $`p` to $`p`"; stated as $`\lnot(p \prec p)` it would fail in every spacetime. The reasons
for the reflexive convention are in the {ref "conventions-causal"}[conventions chapter] (blueprint
[def:causal-trip](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-trip)).

The closure operators `Relation.TransGen` and `Relation.ReflTransGen` are what make transitivity
free: concatenating two chains is a chain, so `causallyPrecedes_trans` is
`Relation.ReflTransGen.trans`.

## Diamonds, and when they form a basis

The Alexandrov topology is `TopologicalSpace.generateFrom` of the family `alexandrovBasis M t` of
chronological diamonds, so the diamonds are a subbasis by construction, and every diamond is open.
That they form a _basis_ is a theorem with hypotheses; it needs three conditions:

* the diamonds generate the topology, which holds by definition;
* they cover the space; on a `LorentzianSpacetime` with at least two points this follows from the
  Hausdorff condition, since a point in no diamond would have the whole space as its only open
  neighbourhood;
* they have the _intersection property_: every point in the intersection of two diamonds lies in a
  diamond inside that intersection. In the standard theory it holds in every spacetime, since
  chronological futures are open in the manifold topology; this is not proved in the library, so
  `LorentzianSpacetime.isTopologicalBasis_alexandrovBasis` takes it as the hypothesis `hdir`. On
  standard Minkowski space it is proved, and the diamonds form a basis unconditionally.

The intersection property should not be confused with _upward_ directedness, that any two diamonds
lie in a common diamond (`alexandrovBasis_directed`). The first makes the diamonds a basis; the
second makes the local algebras of a net a directed system, and it is what the quasilocal
algebra and the Minkowski form of Axiom 3 use (blueprint
[lmm:minkowski-diamonds-upward-directed](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-upward-directed)).
In a curved spacetime two diamonds need not lie in a common diamond, which is why the
[Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Design--Local-commutativity-in-a-common-diamond) states
Axiom 3 in a common diamond.

A diamond can be empty: $`I^+(p) \cap I^-(q)` is empty unless $`p \ll q`, so on Minkowski space
the empty set is a diamond. The causal diamonds $`J^+(p) \cap J^-(q)` are also defined, with their
structure lemmas, but on Minkowski space they are closed, and they are not the regions of the
net; the
[tutorial](../tutorial/AQFT-in-brief/#physicslib4-tutorial--AQFT-in-brief--Regions-of-spacetime--Causal-diamonds)
explains why.

## Causal complements

The spacelike complement $`\mathbf{B}^\perp` of a region is the set of points spacelike to every
point of $`\mathbf{B}`. It is the geometric side of locality: by Einstein causality, observables
in $`\mathbf{B}^\perp` commute with those in $`\mathbf{B}`. Complementation is the Galois
connection of the relation "spacelike related", so the causal closure
$`\mathbf{B} \mapsto \mathbf{B}^{\perp\perp}` is a closure operator, and the causally complete
regions, $`\mathbf{B}^{\perp\perp} = \mathbf{B}`, form a complete lattice.

Because no point is spacelike to itself, the causal complement is an orthocomplement on this
lattice. Causally complete regions are a common index set for local algebras in the literature;
the library's Haag–Kastler net is indexed by diamonds instead.

## Symmetries

For Minkowski space the symmetries form the inhomogeneous Lorentz group; tutorial
[chapter 3](../tutorial/Worked-examples/#worked-examples-covariance) proves that they preserve
causal precedence.

For a general spacetime the symmetries are the isometries. The curved-spacetime Axiom 5 asks for
the isometries "connected to the identity", and these must map diamonds to diamonds. An isometry
preserves the causal type of vectors, but it may reverse the time orientation, and then it can map
$`I^+(p)` onto $`I^-(\varphi(p))`. The library therefore uses `orientedIdentityComponent`: the
isometries in the identity component that, with their inverses, preserve the future orientation.

This is an implementation choice, not a restriction: the oriented identity component is the whole
identity component, but the proof needs a Myers–Steenrod-type rigidity theorem, which Mathlib does
not provide, so the library puts orientation preservation into the definition (blueprint
[def:isometric-covariance-in-curved-spacetime](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isometric-covariance-in-curved-spacetime),
formalization note). The {ref "conventions-implementation"}[conventions chapter] discusses it
further.

Preserving the causal structure is weaker than being an isometry: a dilation
$`x \mapsto \lambda x`, $`\lambda > 0`, maps diamonds to diamonds but scales $`\eta` by
$`\lambda^2` (`alexandrovBasis_image_smul`, `exists_minkowskiForm_smul_ne`). Covariance is
therefore stated for isometries, not for a metric-free notion of causal automorphism.

## The pseudo-Riemannian layer

Trips are built from geodesics, and Mathlib has neither geodesics nor a Levi-Civita connection for
an indefinite metric. The library supplies them in `Physicslib4/Geometry/PseudoRiemannian/`, for
any finite-dimensional smooth manifold and any signature; a spacetime metric enters through
`Spacetime.toPseudoRiemannianMetric`, and the Lorentzian signature is never used in this layer.

The construction follows Mathlib's Riemannian one with the inner product replaced by $`g`. A
covariant derivative is Mathlib's `CovariantDerivative`; `IsLeviCivitaFor g ∇` says it is
torsion-free and metric compatible. The right-hand side of the Koszul formula is tensorial in
$`X` and $`Z`, so for each $`Y` it defines at every point a bilinear form in $`X(x)` and $`Z(x)`,
and the musical isomorphism $`v \mapsto g_x(v, \cdot)`, invertible by non-degeneracy, turns it into
$`\nabla_X Y`. No chart appears in any definition; charts and local frames are used only inside
proofs.

A geodesic is defined chart-free, as $`\nabla_{\dot\mu}\dot\mu = 0` tested against smooth
extensions of the velocity, so it is affinely parametrised. The condition is imposed at interior
parameters only; at an endpoint it would follow by continuity, which the library does not prove
(blueprint
[def:geodesic](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:geodesic)).

# Main definitions and theorems
%%%
tag := "spacetime-main"
%%%

Definitions are shown with their docstrings, which give the mathematics and the blueprint entry;
theorems with their statements, as Lean prints them, and a line or two of explanation. Each
subsection opens with the blueprint entries it covers. In the printed statements, `M.Carrier` is
the set of points of the spacetime `M`, `p ≺[M, t] q` is causal precedence for the time orientation
`t`, and `M.IsCausalTrip t p q` is Lean's dot notation for `Spacetime.IsCausalTrip M t p q`. For
the declarations not shown here, see the
[API documentation](https://physicslib.github.io/physicslib4/docs/Physicslib4/Spacetime/Causality.html)
and the files listed at the end of the chapter.

## Spacetimes and time orientations

Blueprint: [def:spacetime][bp-st], [def:timelike-spacelike-null-vectors][bp-tsn],
[def:time-orientable][bp-to], [def:future-and-past-pointing-vectors][bp-fp].

The structure, with its fields. The manifold structure is in the bracketed fields (`topology`,
`chartedSpace`, `isManifold` and the like), which the library registers as instances, so that Lean
finds them wherever `M : Spacetime` is in scope:

{docstring Physicslib4.Spacetime}

The causal type of a tangent vector is the sign of $`g_x(v, v)`: `Spacetime.IsTimelike`,
`Spacetime.IsNull` and `Spacetime.IsSpacelike`, exactly one of which holds
(`isTimelike_or_isNull_or_isSpacelike`). A time orientation picks the future half of each cone:

{docstring Physicslib4.Spacetime.TimeOrientation}

{docstring Physicslib4.Spacetime.IsFuturePointing}

The future-pointing vectors at a point form a convex cone, null boundary included
({apiDocs Physicslib4.Spacetime.isFuturePointing_add_general}[`isFuturePointing_add_general`]);
the proof runs through the reverse Cauchy–Schwarz inequality for timelike vectors,
$`g(v,v)\,g(w,w) \le g(v,w)^2`, in `LorentzCauchySchwarz.lean`.

[bp-st]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacetime
[bp-tsn]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:timelike-spacelike-null-vectors
[bp-to]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:time-orientable
[bp-fp]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-and-past-pointing-vectors

## Paths, curves and geodesics

Blueprint: [def:paths][bp-paths], [def:curves][bp-curves], [def:endpoints][bp-end],
[def:geodesic][bp-geo].

{docstring Physicslib4.Spacetime.Path}

`SmoothPath` extends `Path`; its own fields are smoothness and the non-vanishing velocity:

{docstring Physicslib4.Spacetime.SmoothPath}

The velocity $`\dot\mu(s)` is `SmoothPath.tangent`. The classes under reparametrisation are
`Curve`, `SmoothCurve` and `OrientedSmoothCurve`; the causal type is well defined on smooth curves
(`isTimelikeSmoothCurve_ofPath_iff`), and the orientation on oriented ones
(`isFutureOrientedCurve_ofPath_iff`). The geodesic condition:

{docstring Physicslib4.Spacetime.IsGeodesic}

[bp-paths]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:paths
[bp-curves]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:curves
[bp-end]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:endpoints
[bp-geo]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:geodesic

## Causal relations

Blueprint: [def:trip][bp-trip], [def:causal-trip][bp-ctrip],
[thrm:precedence-transitive][bp-trans], [def:no-closed-causal-curve][bp-nccc],
[thrm:causal-order-refinements][bp-refine], [def:spacelike-related][bp-slr],
[def:completely-spacelike][bp-cs].

The three relations, from the strict ones to the reflexive one. A single segment is
`IsTripSegment` or `IsCausalTripSegment`; the relations chain them.

{docstring Physicslib4.Spacetime.ChronologicallyPrecedes}

{docstring Physicslib4.Spacetime.IsCausalTrip}

{docstring Physicslib4.Spacetime.CausallyPrecedes}

Reflexivity is the chain of no segments, and transitivity is concatenation of chains:

```lean (name := checkRefl)
open Physicslib4 Spacetime in
#check causallyPrecedes_refl
```

```leanOutput checkRefl
Physicslib4.Spacetime.causallyPrecedes_refl (M : Spacetime) (t : M.TimeOrientation) (p : M.Carrier) : p ≺[M, t] p
```

```lean (name := checkTrans)
open Physicslib4 Spacetime in
#check causallyPrecedes_trans
```

```leanOutput checkTrans
Physicslib4.Spacetime.causallyPrecedes_trans (M : Spacetime) (t : M.TimeOrientation) {p q r : M.Carrier}
  (h₁ : p ≺[M, t] q) (h₂ : q ≺[M, t] r) : p ≺[M, t] r
```

The reflexive relation is the strict one plus equality. `chronologicallyPrecedes_trans` and
`isCausalTrip_trans` are the transitivity of the strict relations, and
`causallyPrecedes_of_chronologicallyPrecedes` says that $`p \ll q` implies $`p \prec q`.

```lean (name := checkEqOr)
open Physicslib4 Spacetime in
#check causallyPrecedes_iff_eq_or_isCausalTrip
```

```leanOutput checkEqOr
Physicslib4.Spacetime.causallyPrecedes_iff_eq_or_isCausalTrip (M : Spacetime) (t : M.TimeOrientation)
  {p q : M.Carrier} : (p ≺[M, t] q) ↔ p = q ∨ M.IsCausalTrip t p q
```

The causality condition forbids closed causal curves, stated with the strict relation:

{docstring Physicslib4.Spacetime.NoClosedCausalCurve}

Under it, causal trips are asymmetric, since two opposite trips concatenate to a closed one, and
$`\prec` is antisymmetric, hence a partial order; `chronologicallyPrecedes_irrefl` gives
$`\lnot(p \ll p)`.

```lean (name := checkAsymm)
open Physicslib4 Spacetime in
#check isCausalTrip_asymm
```

```leanOutput checkAsymm
Physicslib4.Spacetime.isCausalTrip_asymm (M : Spacetime) (t : M.TimeOrientation) (hc : M.NoClosedCausalCurve t)
  {p q : M.Carrier} (hpq : M.IsCausalTrip t p q) : ¬M.IsCausalTrip t q p
```

```lean (name := checkAntisymm)
open Physicslib4 Spacetime in
#check causallyPrecedes_antisymm
```

```leanOutput checkAntisymm
Physicslib4.Spacetime.causallyPrecedes_antisymm (M : Spacetime) (t : M.TimeOrientation) (hc : M.NoClosedCausalCurve t)
  {p q : M.Carrier} (hpq : p ≺[M, t] q) (hqp : q ≺[M, t] p) : p = q
```

The futures and pasts are the sets `chronologicalFuture M t p` $`= I^+(p)`,
`chronologicalPast`, `causalFuture` $`= J^+(p)` and `causalPast`, with set-valued versions such as
`causalFutureSet` $`= J^+(S)`. Spacelike separation is the absence of causal precedence in both
directions:

{docstring Physicslib4.Spacetime.IsSpacelikeRelated}

{docstring Physicslib4.Spacetime.IsCompletelySpacelike}

Because $`\prec` is reflexive, no point is spacelike to itself:

```lean (name := checkIrrefl)
open Physicslib4 Spacetime in
#check isSpacelikeRelated_irrefl
```

```leanOutput checkIrrefl
Physicslib4.Spacetime.isSpacelikeRelated_irrefl (M : Spacetime) (t : M.TimeOrientation) (p : M.Carrier) :
  ¬M.IsSpacelikeRelated t p p
```

[bp-trip]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:trip
[bp-ctrip]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-trip
[bp-trans]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:precedence-transitive
[bp-nccc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:no-closed-causal-curve
[bp-refine]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-order-refinements
[bp-slr]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-related
[bp-cs]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completely-spacelike

## Diamonds and the Alexandrov topology

Blueprint: [def:causal-diamond][bp-cd], [lmm:causal-diamond-structure][bp-cds],
[thrm:causal-diamond-vs-chronological][bp-cdvc], [def:causally-convex-region][bp-ccr],
[def:alexandrov-topology][bp-at], [def:lorentzian-spacetime][bp-ls],
[thrm:alexandrov-topological-basis][bp-atb].

The two kinds of diamond. The chronological ones are the regions of the net:

{docstring Physicslib4.Spacetime.chronologicalDiamond}

{docstring Physicslib4.Spacetime.causalDiamond}

The structure lemmas of the causal diamond all follow from transitivity of $`\prec`. Enlarging the
vertices enlarges the diamond (`causalDiamond_subset_of`, proved step by step in the
[tutorial](../tutorial/Lean-in-brief/#physicslib4-tutorial--Lean-in-brief--Tactic-proofs--Worked-proof___-enlarging-a-causal-diamond)),
a nonempty diamond has $`p \prec q`, and the diamond is causally convex:

```lean (name := checkNonempty)
open Physicslib4 Spacetime in
#check causallyPrecedes_of_causalDiamond_nonempty
```

```leanOutput checkNonempty
Physicslib4.Spacetime.causallyPrecedes_of_causalDiamond_nonempty (M : Spacetime) (t : M.TimeOrientation)
  {p q : M.Carrier} (h : (M.causalDiamond t p q).Nonempty) : p ≺[M, t] q
```

{docstring Physicslib4.Spacetime.IsCausallyConvex}

```lean (name := checkConvex)
open Physicslib4 Spacetime in
#check causalDiamond_isCausallyConvex
```

```leanOutput checkConvex
Physicslib4.Spacetime.causalDiamond_isCausallyConvex (M : Spacetime) (t : M.TimeOrientation) (p q : M.Carrier) :
  M.IsCausallyConvex t (M.causalDiamond t p q)
```

The chronological diamond lies inside the causal one
(`chronologicalDiamond_subset_causalDiamond`). The family of all chronological diamonds is
`alexandrovBasis M t`, and its members are exactly the sets `chronologicalDiamond M t p q`
(`mem_alexandrovBasis_iff_eq_chronologicalDiamond`). The topology they generate:

{docstring Physicslib4.Spacetime.alexandrovTopology}

A Lorentzian spacetime bundles a spacetime, a time orientation and the Hausdorff condition:

{docstring Physicslib4.Spacetime.LorentzianSpacetime}

On it, the diamonds form a basis under the intersection hypothesis `hdir`; the covering
condition is proved from the Hausdorff field (`sUnion_alexandrovBasis_eq_univ`), and needs at least
two points:

```lean (name := checkBasis)
open Physicslib4 Spacetime LorentzianSpacetime in
#check isTopologicalBasis_alexandrovBasis
```

```leanOutput checkBasis
Physicslib4.Spacetime.LorentzianSpacetime.isTopologicalBasis_alexandrovBasis (M : LorentzianSpacetime)
  [Nontrivial M.Carrier]
  (hdir :
    ∀ B₁ ∈ M.toSpacetime.alexandrovBasis M.timeOrientation,
      ∀ B₂ ∈ M.toSpacetime.alexandrovBasis M.timeOrientation,
        ∀ x ∈ B₁ ∩ B₂, ∃ B₃ ∈ M.toSpacetime.alexandrovBasis M.timeOrientation, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂) :
  TopologicalSpace.IsTopologicalBasis (M.toSpacetime.alexandrovBasis M.timeOrientation)
```

Lean's printer hides the topology argument of `IsTopologicalBasis`: it is the Alexandrov topology,
which the source passes explicitly with `@`.

[bp-cd]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-diamond
[bp-cds]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-diamond-structure
[bp-cdvc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-diamond-vs-chronological
[bp-ccr]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-convex-region
[bp-at]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:alexandrov-topology
[bp-ls]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentzian-spacetime
[bp-atb]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:alexandrov-topological-basis

## Minkowski space

Blueprint: [def:standard-minkowski-spacetime][bp-sms], [def:minkowski-spacetime][bp-ms],
[lmm:minkowski-chronological-open][bp-mco], [thrm:minkowski-alexandrov-basis][bp-mab],
[lmm:minkowski-diamonds-upward-directed][bp-mud].

{docstring Physicslib4.StandardMinkowskiSpacetime}

{docstring Physicslib4.standardMinkowskiTimeOrientation}

{docstring Physicslib4.MinkowskiSpacetime}

With the curve-based definitions, the chronological future of a point is the open forward light
cone, $`I^+(p) = \{q : \eta(q-p, q-p) < 0,\ q^0 > p^0\}` (`minkowskiForwardCone`). The inclusion
$`\subseteq` integrates the velocity along each trip segment; the inclusion $`\supseteq` uses the
straight segment from $`p` to $`q`, a geodesic.

```lean (name := checkCone)
open Physicslib4 Spacetime in
#check chronologicalFuture_standardMinkowski
```

```leanOutput checkCone
Physicslib4.chronologicalFuture_standardMinkowski (p : SpacetimeModel) :
  StandardMinkowskiSpacetime.chronologicalFuture standardMinkowskiTimeOrientation p = minkowskiForwardCone p
```

From the cone description, the Alexandrov topology of standard Minkowski space is its Euclidean
topology (`inferInstance` in the statement is the Euclidean topology of $`\mathbb{R}^4`):

```lean (name := checkEuclid)
open Physicslib4 Spacetime in
#check alexandrov_eq_euclidean_standardMinkowski
```

```leanOutput checkEuclid
Physicslib4.alexandrov_eq_euclidean_standardMinkowski :
  StandardMinkowskiSpacetime.alexandrovTopology standardMinkowskiTimeOrientation = inferInstance
```

The diamonds of Minkowski space have the intersection property
(`alexandrovBasis_exists_subset_inter_standardMinkowski`), so they form a basis of the Alexandrov
topology without hypotheses
({apiDocs Physicslib4.Spacetime.isTopologicalBasis_alexandrovBasis_standardMinkowski}[`isTopologicalBasis_alexandrovBasis_standardMinkowski`]).
They are also upward directed: any two lie in a common diamond, whose vertices are a common
chronological past point and a common chronological future point of theirs.

```lean (name := checkDirected)
open Physicslib4 Spacetime in
#check alexandrovBasis_directed
```

```leanOutput checkDirected
Physicslib4.Spacetime.alexandrovBasis_directed {B₁ B₂ : Set SpacetimeModel}
  (h₁ : B₁ ∈ StandardMinkowskiSpacetime.alexandrovBasis standardMinkowskiTimeOrientation)
  (h₂ : B₂ ∈ StandardMinkowskiSpacetime.alexandrovBasis standardMinkowskiTimeOrientation) :
  ∃ B ∈ StandardMinkowskiSpacetime.alexandrovBasis standardMinkowskiTimeOrientation, B₁ ⊆ B ∧ B₂ ⊆ B
```

The geodesics of standard Minkowski space are the paths with zero acceleration, so the straight
lines traversed at constant velocity
({apiDocs Physicslib4.standardMinkowski_isGeodesic_iff}[`standardMinkowski_isGeodesic_iff`]),
because its Levi-Civita connection is the ordinary derivative of the components
(`standardMinkowski_leviCivita_apply`).

[bp-sms]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:standard-minkowski-spacetime
[bp-ms]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:minkowski-spacetime
[bp-mco]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-chronological-open
[bp-mab]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-alexandrov-basis
[bp-mud]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-upward-directed

## Causal complements

Blueprint: [def:spacelike-complement][bp-sc], [lmm:spacelike-complement-order][bp-sco],
[def:causal-closure][bp-cc], [def:causally-complete-region][bp-ccomp],
[thrm:causally-complete-lattice][bp-ccl], [thrm:causal-complement-de-morgan][bp-dm],
[thrm:causally-complete-convex][bp-ccc].

The lattice theory is stated on a Lorentzian spacetime, with its own time orientation;
`Spacetime.spacelikeComplement M t` is the same set for an explicit time orientation.

{docstring Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement}

{docstring Physicslib4.Spacetime.LorentzianSpacetime.causalClosure}

{docstring Physicslib4.Spacetime.LorentzianSpacetime.IsCausallyComplete}

{docstring Physicslib4.Spacetime.LorentzianSpacetime.CausallyCompleteRegion}

{docstring Physicslib4.Spacetime.LorentzianSpacetime.causalComplement}

The orthocomplement laws. Their proofs use that $`\mathbf{B} \cap \mathbf{B}^\perp = \emptyset`,
which rests on the reflexivity of $`\prec`, and the set-level De Morgan law
$`(\mathbf{B}_1 \cup \mathbf{B}_2)^\perp = \mathbf{B}_1^\perp \cap \mathbf{B}_2^\perp`:

```lean (name := checkInf)
open Physicslib4 Spacetime in
#check LorentzianSpacetime.inf_causalComplement
```

```leanOutput checkInf
Physicslib4.Spacetime.LorentzianSpacetime.inf_causalComplement (M : LorentzianSpacetime)
  (B : M.CausallyCompleteRegion) : B ⊓ M.causalComplement B = ⊥
```

```lean (name := checkSup)
open Physicslib4 Spacetime in
#check LorentzianSpacetime.sup_causalComplement
```

```leanOutput checkSup
Physicslib4.Spacetime.LorentzianSpacetime.sup_causalComplement (M : LorentzianSpacetime)
  (B : M.CausallyCompleteRegion) : B ⊔ M.causalComplement B = ⊤
```

The De Morgan laws are `causalComplement_sup`, `causalComplement_inf` and their infinitary forms
`causalComplement_iSup` and `causalComplement_iInf`. Every causally complete region is causally
convex (`isCausallyConvex_of_isCausallyComplete`), as is every causal diamond
(`causalDiamond_isCausallyConvex`).

[bp-sc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-complement
[bp-sco]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-order
[bp-cc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-closure
[bp-ccomp]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-complete-region
[bp-ccl]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-lattice
[bp-dm]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-complement-de-morgan
[bp-ccc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-convex

## The Lorentz group and isometries

Blueprint: [def:lorentz-transformation][bp-lt], [lmm:lorentz-closure][bp-lc],
[def:inhomogeneous-lorentz-group][bp-ilg], [def:lorentz-path][bp-lp],
[thrm:causal-precedence-lorentz-invariant][bp-cpli], [lmm:isometry-preserves-chronology][bp-ipc],
[lmm:isometry-preserves-basis-sets][bp-ipb].

The three conditions on a linear automorphism of $`\mathbb{R}^4`:

{docstring Physicslib4.IsLorentz}

{docstring Physicslib4.IsProper}

{docstring Physicslib4.IsOrthochronous}

Their closure properties are `isLorentz_trans`, `isLorentz_symm` and the like. The group
`AQFT.HaagKastler.InhomogeneousLorentzGroup` of pairs $`(\Lambda, a)` is shown in the
[Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Main-definitions-and-theorems--The-axioms).
Its action on smooth paths:

{docstring Physicslib4.lorentzPath}

The pushforward of a causal trip segment is a causal trip segment, so chains go to chains, and the
inverse gives the converse:

```lean (name := checkSmul)
open Physicslib4 Spacetime in
#check causallyPrecedes_smul_iff
```

```leanOutput checkSmul
Physicslib4.causallyPrecedes_smul_iff (g : AQFT.HaagKastler.InhomogeneousLorentzGroup)
  (p q : StandardMinkowskiSpacetime.Carrier) :
  (g • p ≺[StandardMinkowskiSpacetime, standardMinkowskiTimeOrientation] g • q) ↔
    p ≺[StandardMinkowskiSpacetime, standardMinkowskiTimeOrientation] q
```

The same holds for $`\ll` (`chronologicallyPrecedes_smul_iff`); spacelike separation and complete
spacelike separation are invariant (`isSpacelikeRelated_smul_iff`,
`isCompletelySpacelike_smul_iff`); and the group maps diamonds to diamonds
(`isAlexandrovBasisSet_smul`). Tutorial
[chapter 3](../tutorial/Worked-examples/#worked-examples-covariance) proves
`causallyPrecedes_smul_iff` from the segment lemma.

For a general spacetime the symmetries are the isometries:

{docstring Physicslib4.Spacetime.Isometry}

{docstring Physicslib4.Spacetime.Isometry.identityComponent}

An isometry preserves the causal type of vectors (`Isometry.isTimelike_mfderiv_iff` and its null
and spacelike companions), and pushes smooth paths forward (`Isometry.pushforwardPath`). If it
also preserves the future orientation, it maps trips to trips:

{docstring Physicslib4.Spacetime.Isometry.PreservesFutureOrientation}

{docstring Physicslib4.Spacetime.Isometry.orientedIdentityComponent}

Every member of the oriented identity component maps diamonds to diamonds, which is what makes the
curved-spacetime Axiom 5 maps $`\mathfrak{U}(\mathbf{B}) \to \mathfrak{U}(\varphi(\mathbf{B}))`
well defined. In the statement, `⇑g.toDiffeo '' B` is the image $`\varphi(\mathbf{B})`:

```lean (name := checkIsomBasis)
open Physicslib4 Spacetime Isometry in
#check
  alexandrovBasis_image_of_mem_orientedIdentityComponent
```

```leanOutput checkIsomBasis
Physicslib4.Spacetime.Isometry.alexandrovBasis_image_of_mem_orientedIdentityComponent {M : Spacetime} (g : M.Isometry)
  (t : M.TimeOrientation) (hg : g ∈ orientedIdentityComponent M t) {B : Set M.Carrier} (hB : B ∈ M.alexandrovBasis t) :
  ⇑g.toDiffeo '' B ∈ M.alexandrovBasis t
```

The proof is $`\varphi(I^\pm(p)) = I^\pm(\varphi(p))` (`Isometry.chronologicalFuture_image`,
`Isometry.chronologicalPast_image`) and injectivity of $`\varphi`. The curved-spacetime axioms
([Section 10.7](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:haag-kastler-axioms-in-curved-spacetime)
of the blueprint) use this group through `LorentzianSpacetime.toAbstractIdentityComponent`.

[bp-lt]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentz-transformation
[bp-lc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lorentz-closure
[bp-ilg]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:inhomogeneous-lorentz-group
[bp-lp]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentz-path
[bp-cpli]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-precedence-lorentz-invariant
[bp-ipc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-chronology
[bp-ipb]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-basis-sets

## The Levi-Civita connection and geodesics

Blueprint: [def:pseudo-riemannian-metric][bp-prm], [def:metric-compatible-connection][bp-mcc],
[def:levi-civita-connection][bp-lcc], [thrm:levi-civita-exists-unique][bp-lceu],
[lmm:minkowski-levi-civita-flat][bp-flat], [lmm:isometry-preserves-geodesics][bp-ipg].

The metric, of any signature, on a manifold `M` modelled by `I`:

{docstring Physicslib4.Geometry.PseudoRiemannianMetric}

Connections are Mathlib's `CovariantDerivative`, and the two conditions on them are:

{docstring Physicslib4.Geometry.CovariantDerivative.IsMetricCompatibleWith}

{docstring Physicslib4.Geometry.CovariantDerivative.IsLeviCivitaFor}

Existence is the Koszul construction, `koszulConnection`:

```lean (name := checkLCExists)
open Physicslib4 Geometry in
#check PseudoRiemannianMetric.exists_isLeviCivitaFor
```

```leanOutput checkLCExists
Physicslib4.Geometry.PseudoRiemannianMetric.exists_isLeviCivitaFor.{u_1, u_2, u_3} {E : Type u_1} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {H : Type u_2} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type u_3} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (↑⊤) M] [FiniteDimensional ℝ E] (g : PseudoRiemannianMetric I M) :
  ∃ cov, IsLeviCivitaFor g cov
```

Uniqueness compares two Levi-Civita connections through the Koszul formula
(`IsLeviCivitaFor.koszul`), which expresses $`2g(\nabla_X Y, Z)` through derivatives of $`g` and
Lie brackets alone, and non-degeneracy. The hypothesis `hY` is differentiability of $`Y` at $`x`.
(`IsManifold I (↑⊤) M` is Lean's rendering of a $`C^\infty` manifold.)

```lean (name := checkLCUnique)
open Physicslib4 Geometry in
#check CovariantDerivative.IsLeviCivitaFor.uniqueness
```

```leanOutput checkLCUnique
Physicslib4.Geometry.CovariantDerivative.IsLeviCivitaFor.uniqueness.{u_1, u_2, u_3} {E : Type u_1}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type u_2} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u_3} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (↑⊤) M] [FiniteDimensional ℝ E]
  {g : PseudoRiemannianMetric I M} {cov cov' : CovariantDerivative I E (TangentSpace I)} (hcov : IsLeviCivitaFor g cov)
  (hcov' : IsLeviCivitaFor g cov') {x : M} {Y : (x : M) → TangentSpace I x} (hY : (MDiffAt fun x => ⟨x, Y x⟩) x)
  (X₀ : TangentSpace I x) : (↑cov Y x) X₀ = (↑cov' Y x) X₀
```

The connection the library uses, chosen from the existence theorem:

{docstring Physicslib4.Geometry.PseudoRiemannianMetric.leviCivita}

On a vector space with a constant metric, such as standard Minkowski space, the ordinary
directional derivative `Geometry.flatConnection` is a Levi-Civita connection
(`isLeviCivitaFor_flatConnection`), so by uniqueness `leviCivita` is the ordinary derivative on
differentiable fields
({apiDocs Physicslib4.Geometry.PseudoRiemannianMetric.leviCivita_apply_eq_fderiv}[`leviCivita_apply_eq_fderiv`]).

Isometries preserve the Levi-Civita connection, $`d\varphi\big(\nabla_{\varphi^*X}\varphi^*Y\big) =
\nabla_X Y` at corresponding points (`Isometry.mfderiv_leviCivita_mpullback`), because every term of
the Koszul formula is natural under $`\varphi`. Hence they map geodesics to geodesics; the converse
is the same statement for $`\varphi^{-1}`:

```lean (name := checkGeod)
open Physicslib4 Spacetime in
#check Isometry.pushforwardPath_isGeodesic
```

```leanOutput checkGeod
Physicslib4.Spacetime.Isometry.pushforwardPath_isGeodesic.{u_1} {M : Spacetime} (g : M.Isometry) (μ : M.SmoothPath)
  (h : M.IsGeodesic μ) : M.IsGeodesic (g.pushforwardPath μ)
```

The Minkowski counterpart, for `lorentzPath`, is `lorentzPath_isGeodesic`. The cross-metric form,
`CrossIsometry.pushforwardPath_isGeodesic`, is for a diffeomorphism carrying one metric to another,
$`\psi^* g_2 = g_1`, as general covariance needs. The pullback metric $`\psi^* g` and cross-metric
isometries (`Pullback.lean`, `CrossMetricIsometry.lean`) carry all the results above between two
spacetimes; they serve general covariance and are described with it.

[bp-prm]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pseudo-riemannian-metric
[bp-mcc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:metric-compatible-connection
[bp-lcc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:levi-civita-connection
[bp-lceu]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:levi-civita-exists-unique
[bp-flat]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-levi-civita-flat
[bp-ipg]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-geodesics

# Where to look
%%%
tag := "spacetime-files"
%%%

The section is formalised in `Physicslib4/Spacetime/` and `Physicslib4/Geometry/PseudoRiemannian/`,
one topic per file. Each entry links to the API documentation of a representative declaration,
from which the rest of the file can be browsed.

Spacetimes and vectors:

* `Basic.lean`: the structure, {apiDocs Physicslib4.Spacetime}[].
* `CausalStructure.lean`: timelike, null and spacelike vectors, time orientations, future- and
  past-pointing vectors, {apiDocs Physicslib4.Spacetime.TimeOrientation}[].
* `LorentzCauchySchwarz.lean`, `LorentzCone.lean` and `LorentzOrthogonal.lean`: the reverse
  Cauchy–Schwarz and triangle inequalities, and the convexity of the future cone,
  {apiDocs Physicslib4.Spacetime.reverse_triangle}[`reverse_triangle`].

Curves and causality:

* `Curves.lean`: paths, smooth paths, curves, oriented curves and endpoints,
  {apiDocs Physicslib4.Spacetime.SmoothPath}[].
* `AlongPath.lean`: the extension and locality lemmas behind the geodesic condition,
  {apiDocs Physicslib4.Spacetime.SmoothPath.exists_vectorField_eq_tangent}[`SmoothPath.exists_vectorField_eq_tangent`].
* `Causality.lean`: geodesics, trips, $`\ll` and $`\prec`, futures and pasts, spacelike
  separation, the causality condition, diamonds, causal convexity and the Alexandrov topology,
  {apiDocs Physicslib4.Spacetime.CausallyPrecedes}[].
* `CausalComplement.lean`: spacelike complements, the causal closure and the lattice of causally
  complete regions,
  {apiDocs Physicslib4.Spacetime.LorentzianSpacetime.causalComplement}[`LorentzianSpacetime.causalComplement`].
* `LorentzianSpacetime.lean`: the bundled structure and the basis theorem,
  {apiDocs Physicslib4.Spacetime.LorentzianSpacetime}[].

Minkowski space:

* `Minkowski.lean`: standard Minkowski spacetime, the Lorentz conditions, the standard time
  orientation, the cone description of $`I^\pm(p)`, the geodesics, the Alexandrov topology equal to
  the Euclidean one, and `MinkowskiSpacetime`, {apiDocs Physicslib4.StandardMinkowskiSpacetime}[].
* `MinkowskiDirected.lean`: the diamonds have the intersection property, are upward directed,
  and form a basis,
  {apiDocs Physicslib4.Spacetime.alexandrovBasis_directed}[`alexandrovBasis_directed`].
* `LorentzCausality.lean`: the action on paths and the invariance of the causal relations,
  {apiDocs Physicslib4.causallyPrecedes_smul_iff}[].
* `MinkowskiDilation.lean`: dilations preserve the causal structure but not the metric,
  {apiDocs Physicslib4.alexandrovBasis_image_smul}[].

Isometries:

* `Isometry.lean`: the group of isometries, {apiDocs Physicslib4.Spacetime.Isometry}[].
* `IsometryTopology.lean`: its topology and identity component,
  {apiDocs Physicslib4.Spacetime.Isometry.identityComponent}[`Isometry.identityComponent`].
* `IsometryCausality.lean`: pushforward of paths, preservation of the Levi-Civita connection,
  geodesics, trips and diamonds, and the oriented identity component,
  {apiDocs Physicslib4.Spacetime.Isometry.orientedIdentityComponent}[`Isometry.orientedIdentityComponent`].
* `Diffeo.lean`, `DiffeoPath.lean`, `Pullback.lean` and `CrossMetricIsometry.lean`: diffeomorphisms
  between two spacetimes, pullback metrics and cross-metric isometries, for general covariance,
  {apiDocs Physicslib4.Spacetime.CrossIsometry}[`CrossIsometry`].

The pseudo-Riemannian layer, in `Physicslib4/Geometry/PseudoRiemannian/`:

* `Basic.lean`: the metric and the musical isomorphism,
  {apiDocs Physicslib4.Geometry.PseudoRiemannianMetric}[`Geometry.PseudoRiemannianMetric`].
* `LeviCivita.lean`: metric compatibility, the Levi-Civita condition, the Koszul formula,
  existence and uniqueness,
  {apiDocs Physicslib4.Geometry.PseudoRiemannianMetric.leviCivita}[`PseudoRiemannianMetric.leviCivita`].
* `Flat.lean`: the flat connection of a constant metric,
  {apiDocs Physicslib4.Geometry.flatConnection}[`Geometry.flatConnection`].

The blueprint section is
[Section 10.5](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:spacetime),
and the [section page](https://physicslib.github.io/physicslib4/sec10-5-spacetime.html) lists
each of its entries with the Lean declaration that formalises it.
