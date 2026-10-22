import VersoManual
import Book.Meta
import Physicslib4.AQFT.HaagKastlerCurved.Spacetime
import Physicslib4.AQFT.HaagKastlerCurved.Net
import Physicslib4.AQFT.HaagKastlerCurved.Concrete
import Physicslib4.AQFT.HaagKastlerCurved.IdentityComponent
import Physicslib4.AQFT.HaagKastlerCurved.EinsteinCausality
import Physicslib4.AQFT.HaagKastlerCurved.LocalVonNeumann
import Physicslib4.AQFT.HaagKastlerCurved.GeometricCovariance
import Physicslib4.AQFT.HaagKastlerCurved.CovariantState
import Physicslib4.AQFT.HaagKastlerCurved.StabilizerAction
import Physicslib4.AQFT.HaagKastlerCurved.StabilizerKMS
import Physicslib4.AQFT.HaagKastlerCurved.Purity
import Physicslib4.AQFT.HaagKastlerCurved.GeneralCovariance
-- Imported only for the link to the Minkowski equivalence of Axiom 3.
import Physicslib4.AQFT.HaagKastler.LocalCommutativity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book
-- Docstring code spans are elaborated in this scope; these namespaces let the names they mention,
-- written relative to the library's namespaces, resolve and link. `Physicslib4.Spacetime` is not
-- opened, since its `LorentzianSpacetime` would clash with the interface of the same name.
open Physicslib4 Physicslib4.AQFT Physicslib4.AQFT.HaagKastlerCurved
open Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet
open Physicslib4.Spacetime.LorentzianSpacetime

#doc (Manual) "The axioms in curved spacetime and general covariance" =>

%%%
tag := "curved"
file := "The-axioms-in-curved-spacetime-and-general-covariance"
%%%

This chapter describes how the library states the Haag–Kastler axioms on a curved spacetime, what
it proves from them, and how it formulates general covariance, which relates the nets of one theory
over different spacetimes. It corresponds to
[Section 10.7](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:haag-kastler-axioms-in-curved-spacetime)
and
[Section 10.8](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:general-covariance-in-curved-spacetime)
of the blueprint. The physics is introduced in
[chapter 1 of the tutorial](../tutorial/AQFT-in-brief/#physicslib4-tutorial--AQFT-in-brief--What-this-project-sharpens).
The axioms mirror the Minkowski ones closely, so this chapter assumes the
{ref "haag-kastler"}[Haag–Kastler chapter] and describes mainly where the curved axioms differ.

# Overview
%%%
tag := "curved-overview"
%%%

As you will recall, the sharpened Haag–Kastler axioms attach a unital C\*-algebra
$`\mathfrak{U}(\mathbf{B})` to each causal diamond $`\mathbf{B} = I^+(p) \cap I^-(q)`, embed the
algebras of smaller diamonds in those of larger ones, and ask for locality and covariance. On a
curved spacetime $`M` two things change. The Poincaré group is replaced by the isometries of
$`M` connected to the identity, and two diamonds need not lie in a common diamond, so there is in
general no quasilocal algebra. The library states the axioms over an abstract interface,
`HaagKastlerCurved.LorentzianSpacetime`, which records only what the axioms use, and connects a
geometric spacetime to it by `toAbstractIdentityComponent`. Six declarations carry the axioms:

* `LocalNet`, Axiom 1: a unital C\*-algebra $`\mathfrak{U}(\mathbf{B})` for every basis set
  $`\mathbf{B}`, with $`\mathfrak{U}(\emptyset) = \mathbb{C}\mathbf{1}`;
* `Isotony`, Axiom 2: a coherent family of unital \*-monomorphisms
  $`i_{(\mathbf{B}_1\mathbf{B}_2)} : \mathfrak{U}(\mathbf{B}_1) \to \mathfrak{U}(\mathbf{B}_2)`;
* `LocalCommutativity`, Axiom 3: the algebras of completely spacelike basis sets commute in the
  algebra of every basis set containing both;
* `LocalAlgebra`, Axiom 4: every self-adjoint operator in a representation of a local algebra is
  a local observable;
* `IsometricCovariance`, Axiom 5: the isometries $`\varphi` connected to the identity act by
  \*-isomorphisms $`\alpha_\varphi : \mathfrak{U}(\mathbf{B}) \to \mathfrak{U}(\varphi(\mathbf{B}))`
  that respect isotony;
* `HaagKastlerNet`, which bundles the five.

General covariance is not a sixth axiom. A _net theory_ (`NetTheory`) assigns a net to every
geometric Lorentzian spacetime, and it is _generally covariant_ (`IsGenerallyCovariant`) when the
nets over a spacetime and over its pullback by a diffeomorphism are equivalent (`NetEquivalence`).

From the axioms the library proves:

* their consistency, over every instance of the interface and over every geometric spacetime, by
  the trivial net;
* Einstein causality in every representation of a containing algebra
  $`\mathfrak{U}(\mathbf{B})`;
* the basic properties of the local von Neumann algebras
  $`R(\mathbf{B}') = \pi(\mathfrak{U}(\mathbf{B}'))''` of the basis sets
  $`\mathbf{B}' \subseteq \mathbf{B}`: isotony, microcausality, the Schlieder property, and
  the basic facts about relative commutants and factors;
* that the stabiliser $`\mathrm{Stab}(\mathbf{B})` of a basis set acts on
  $`\mathfrak{U}(\mathbf{B})` by \*-automorphisms, that this action is implemented by a unitary
  representation on the GNS space of an invariant state, strongly continuous when the matrix
  coefficients are continuous, and that the unitaries carry $`R(\mathbf{B}_1)` onto
  $`R(g\mathbf{B}_1)` for $`g \in \mathrm{Stab}(\mathbf{B})`;
* the characterisations of pure states on each $`\mathfrak{U}(\mathbf{B})`.

It also defines covariant families of local states, and KMS and ground states for a Killing flow
fixing a region. The declarations are in the namespace `Physicslib4.AQFT.HaagKastlerCurved`,
written without it below, except for the bridge and the pullback relabelling, which are in
`Physicslib4.Spacetime.LorentzianSpacetime`.

# Design
%%%
tag := "curved-design"
%%%

The blueprint is the specification, and its design and formalization notes record the reasons for
the choices below. Where a choice is the one made for Minkowski spacetime, this section points to
the {ref "haag-kastler-design"}[Design section] of the Haag–Kastler chapter instead of repeating it.

## An abstract spacetime interface

The axioms never look at the metric. They need the points of $`M`, the basis sets of its
Alexandrov topology, the relation "completely spacelike" between regions, and a group of
isometries acting on the points. The structure `HaagKastlerCurved.LorentzianSpacetime` records
exactly these, as the fields `Carrier`, `IsBasisSet`, `IsCompletelySpacelike`, `Isom`,
`instGroup` and `instAction`, together with one law, `isBasisSet_smul`: an isometry carries a
basis set to a basis set, so that $`\alpha_\varphi` maps between local algebras of basis sets.
With `open Pointwise`, the image $`\varphi(\mathbf{B})` is written `φ • B`.

The interface imposes nothing else. It does not say that completely spacelike regions are
disjoint, or that complete spacelike separation passes to subregions; the one-point
`trivialSpacetime`, in which every set is a basis set and every two sets are completely spacelike,
is an instance. Results that need such a property take it as a hypothesis: for example
`HaagKastlerNet.commute_of_spacelike_mono` assumes that complete spacelike separation is
inherited by subsets, and its geometric form `commute_of_spacelike_mono_geometric` discharges the
hypothesis.

The theorems of this chapter are proved over the interface, and so apply to any spacetime that
instantiates it, such as the geometric spacetimes of the {ref "spacetime"}[Spacetime chapter]; a
few have geometric forms stated over the bridge.

## The bridge from a geometric spacetime

`Spacetime.LorentzianSpacetime.toAbstractIdentityComponent` turns a geometric Lorentzian spacetime
$`L` into an instance of the interface. Its points are those of the manifold; its basis sets are
the diamonds $`I^+(p) \cap I^-(q)` for the time orientation of $`L`; two regions are completely
spacelike when every point of one is spacelike to every point of the other; and its isometry group
is `Spacetime.Isometry.orientedIdentityComponent`, the isometries in the identity component of the
isometry group that, with their inverses, preserve the future orientation. These isometries map
diamonds to diamonds (`Spacetime.LorentzianSpacetime.isBasisSet_smul`), which supplies the law of
the interface.

The blueprint asks for the isometries "connected to the identity". Including orientation
preservation in the definition is an implementation choice, not a restriction: an isometry
connected to the identity preserves the future orientation, but the proof needs a
Myers–Steenrod-type rigidity theorem that Mathlib does not provide (blueprint
[def:isometric-covariance-in-curved-spacetime][bp-cov], formalization note). The
[Spacetime chapter](Spacetime-and-geometry/#physicslib4-reference-manual--Spacetime-and-geometry--Design--Symmetries)
explains why orientation matters: an isometry that reverses the time orientation maps $`I^+(p)`
onto $`I^-(\varphi(p))`.

## Local algebras, parallel to Minkowski

Axioms 1 and 2 have the shape of their Minkowski counterparts: `LocalNet.algebra` is a function
on all subsets, constrained only on basis sets, and isotony is data with identity and composition
laws. `LocalNet.{u, v} M` has its spacetime in universe `u` and its algebras in universe `v`,
independent of `u`. Hilbert spaces quantified in the axioms (Axiom 4) range over `Type v`, where
`gns_construction` puts the GNS spaces of states on the algebras. The trivial net, built from
$`\mathbb{C}`, has $`v = 0`.

## Local commutativity without a quasilocal algebra

In Minkowski spacetime any two diamonds lie in a common diamond, so the local algebras form a
directed system and the quasilocal algebra exists. In a curved spacetime this fails. In a
Schwarzschild black hole, a diamond just below the singularity and a diamond outside the horizon
at late times lie in no common diamond: the top vertex of a common diamond would have to lie in
the future of both, and the future of the first ends on the singularity (tutorial,
[chapter 1](../tutorial/AQFT-in-brief/#physicslib4-tutorial--AQFT-in-brief--What-this-project-sharpens);
blueprint, Chapter 9,
[Axiom 3][bp-ch9-ax3]). Their algebras then lie in no common algebra, and the construction of a
quasilocal algebra fails. The blueprint argues this informally; the library does not formalise
it.

Axiom 3 is therefore stated as in Minkowski spacetime: for every basis set $`\mathbf{B}`
containing two completely spacelike basis sets $`\mathbf{B}_1` and $`\mathbf{B}_2`, the images
$`i_{(\mathbf{B}_1\mathbf{B})}(a_1)` and $`i_{(\mathbf{B}_2\mathbf{B})}(a_2)` commute in
$`\mathfrak{U}(\mathbf{B})`. When no such $`\mathbf{B}` exists the condition is vacuous: the two
algebras lie in no common algebra, so the question does not arise. In Minkowski spacetime the same
statement is equivalent to commutation in the quasilocal algebra (Minkowski:
{apiDocs Physicslib4.AQFT.HaagKastler.localCommutativity_iff_exists_commute_ι}[`localCommutativity_iff_exists_commute_ι`]).

Every later result follows the same pattern. Einstein causality, the local von Neumann algebras
and the GNS results are stated in, or in a representation of, the algebra
$`\mathfrak{U}(\mathbf{B})` of one containing basis set. Comparing three nested regions
$`\mathbf{B}_1 \subseteq \mathbf{B}_2 \subseteq \mathbf{B}` uses the composition law of Axiom 2,
which makes the embedding of $`\mathfrak{U}(\mathbf{B}_1)` in $`\mathfrak{U}(\mathbf{B})` factor
through $`\mathfrak{U}(\mathbf{B}_2)` for every net; Axiom 3 uses the same family, so no result
assumes the factorisation separately (blueprint [def:isotony-in-curved-spacetime][bp-iso], design
note).

Without a quasilocal algebra, Axiom 4 is read locally: in every representation $`\pi` of a
local algebra $`\mathfrak{U}(\mathbf{B})`, every self-adjoint operator in the range of $`\pi` is
$`\pi(a)` for a self-adjoint $`a \in \mathfrak{U}(\mathbf{B})`. Read this way it holds for every
net (`localAlgebra_of`), since a self-adjoint $`\pi(b)` is also $`\pi\big((b + b^*)/2\big)`. It
is a field of `HaagKastlerNet`, unlike the Minkowski Axiom 4.

## Isometric covariance and stabilisers

Axiom 5 has the shape of the Minkowski `LorentzCovariance`: \*-isomorphisms
$`\alpha_\varphi : \mathfrak{U}(\mathbf{B}) \to \mathfrak{U}(\varphi(\mathbf{B}))` with
$`\alpha_1 = \mathrm{id}`, $`\alpha_{(\varphi'\varphi)} = \alpha_{\varphi'} \circ \alpha_\varphi`,
and compatibility with the net's own isotony family. `HaagKastlerNet.covEquiv` chooses the maps.
A generic spacetime has no isometries but the identity, and then the axiom says nothing.

In Minkowski spacetime the maps $`\alpha_L` extend to automorphisms of the quasilocal algebra. Here
there is no such algebra, and $`\alpha_\varphi` moves $`\mathfrak{U}(\mathbf{B})` to a different
algebra unless $`\varphi(\mathbf{B}) = \mathbf{B}`. The symmetries that act on a single algebra
are therefore those of the stabiliser
$`\mathrm{Stab}(\mathbf{B}) = \{\varphi : \varphi(\mathbf{B}) = \mathbf{B}\}`, Mathlib's
`MulAction.stabilizer`. On it, $`\alpha_\varphi` followed by the identification
$`\mathfrak{U}(\varphi(\mathbf{B})) = \mathfrak{U}(\mathbf{B})` is an automorphism
$`\hat\alpha_\varphi`, and $`\varphi \mapsto \hat\alpha_\varphi` is a group homomorphism. The
GNS unitaries, the covariance of the local von Neumann algebras and the KMS states are all stated
for the stabiliser. Physically one would like it to stand in for the global symmetry group, a
Killing flow such as the stationary flow of a black-hole exterior or the boost of a de Sitter
static patch. Those regions are not diamonds (basis sets), and no such flow fixes a nonempty
diamond, so the axioms as stated place no constraint on their algebras: the examples motivate the
definitions but are not instances of them. For a basis set the stabiliser contains isometries
such as rotations about a timelike axis. The stabiliser and KMS definitions accept any region
`B`, but the axioms constrain $`\mathfrak{U}(\mathbf{B})` only on basis sets.

## General covariance relates nets over different spacetimes

As you will recall, the gauge group of general relativity is the diffeomorphism group, acting on
all fields, the metric included: $`(M, g)` and $`(M, \psi^*g)` describe the same physics. A theory
in curved spacetime is therefore not one net but a rule $`L \mapsto \mathfrak{U}_L` assigning a
net to each background, and general covariance is a property of the rule. The library has three
choices here (blueprint [def:net-equivalence-in-curved-spacetime][bp-neq] and
[def:general-covariance-in-curved-spacetime][bp-gc], with the remarks that follow them).

* Two spacetimes are related by a bijection $`e` of their points, as data, not by an equality of
  their carriers, which would be an equality of types. `NetEquivalence` asks of $`e` only that it
  carry basis sets to basis sets; the isomorphisms
  $`\Theta_{\mathbf{B}} : \mathfrak{U}_1(\mathbf{B}) \to \mathfrak{U}_2(e(\mathbf{B}))` are data,
  since the naturality square refers to them.
* `NetTheory` ranges over all geometric Lorentzian spacetimes, not over the metrics on one fixed
  manifold, so the pullback $`\psi^*L` of any $`L` is again in its domain.
* The relabelling is a diffeomorphism, so the comparison is between isometric backgrounds.
  Quantifying over every bijection that preserves the causal structure would be too strong: the
  dilations of Minkowski space preserve diamonds but are not isometries, and would demand scale
  covariance, which a massive theory does not have.

General covariance is a postulate, not a consequence of Axioms 1 to 5, which constrain one net on
one spacetime. Unlike Axiom 5, it is not restricted to diffeomorphisms connected to the identity:
it compares two nets, and makes no group act on one. Nor is it the locally covariant
framework of Brunetti, Fredenhagen and Verch
([Commun. Math. Phys. 237 (2003) 31–68](https://doi.org/10.1007/s00220-003-0815-7); compared in
[tutorial chapter 1](../tutorial/AQFT-in-brief/#physicslib4-tutorial--AQFT-in-brief--What-this-project-sharpens)),
a functor on a category of globally hyperbolic spacetimes and their embeddings: here only
diffeomorphisms of a whole spacetime are compared.

[bp-cov]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isometric-covariance-in-curved-spacetime
[bp-iso]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony-in-curved-spacetime
[bp-neq]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:net-equivalence-in-curved-spacetime
[bp-gc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:general-covariance-in-curved-spacetime
[bp-ch9-ax3]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-in-curved-spacetime.html#sctn:axiom-3-%28local-commutativity%29

# Main definitions and theorems
%%%
tag := "curved-main"
%%%

Definitions are shown with their docstrings, which give the mathematics and the blueprint entry;
theorems with their statements, as Lean prints them, and a line or two of explanation. Each
subsection opens with the blueprint entries it covers. For the declarations not shown here, see the
[API documentation](https://physicslib.github.io/physicslib4/docs/Physicslib4/AQFT/HaagKastlerCurved/Net.html)
and the files listed at the end of the chapter.

## The spacetime interface and the bridge

Blueprint: [def:lorentzian-spacetime][bp-ls], [def:isometric-covariance-in-curved-spacetime][bp-cov]
(formalization note), [lmm:axiom5-basis-preservation][bp-a5b].

{docstring Physicslib4.AQFT.HaagKastlerCurved.LorentzianSpacetime}

{docstring Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent}

The interface carries no topology on `Isom`, so the strongly continuous results below take
`[TopologicalSpace M.Isom]` as an argument. Over the bridge the instance
{apiDocs Physicslib4.Spacetime.LorentzianSpacetime.instTopologicalSpaceToAbstractIdentityComponentIsom}[`instTopologicalSpaceToAbstractIdentityComponentIsom`]
supplies it: the isometry group has the topology induced by
$`\varphi \mapsto (\varphi, \varphi^{-1})` into $`C(M, M) \times C(M, M)` with the compact-open
topology, and the subgroup inherits it.

[bp-ls]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentzian-spacetime
[bp-a5b]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:axiom5-basis-preservation

## The axioms

Blueprint: [def:local-algebras-in-curved-spacetime][bp-la], [def:isotony-in-curved-spacetime][bp-iso],
[def:local-commutativity-in-curved-spacetime][bp-lc], [def:local-observable][bp-lo],
[def:local-completeness-in-curved-spacetime][bp-lcomp],
[def:isometric-covariance-in-curved-spacetime][bp-cov],
[def:haag-kastler-net-in-curved-spacetime][bp-net],
[thrm:haag-kastler-net-in-curved-spacetime-nonempty][bp-ne].

Axioms 1 and 2. As in Minkowski spacetime, the isotony maps take the basis-set hypotheses
explicitly and the regions as strict-implicit arguments, so the embedding of $`\mathbf{B}_1` in
$`\mathbf{B}_2` is `i.map hB₁ hB₂ h`:

{docstring Physicslib4.AQFT.HaagKastlerCurved.LocalNet}

{docstring Physicslib4.AQFT.HaagKastlerCurved.Isotony}

Axiom 3:

{docstring Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity}

Axiom 4 and the local observables it refers to:

{docstring Physicslib4.AQFT.HaagKastlerCurved.IsLocalObservable}

{docstring Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebra}

Axiom 5:

{docstring Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance}

The bundled net. A theorem about a theory on $`M` takes `N : HaagKastlerNet M`, and reaches the
isotony maps as `N.commIsotony` and the covariance maps as `N.covEquiv`:

{docstring Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet}

The axioms are consistent over every instance of the interface. The witness is the trivial net
`trivialHaagKastlerNet`, which assigns $`\mathbb{C}` to every region with every map the identity;
the [tutorial](../tutorial/Worked-examples/#physicslib4-tutorial--Worked-examples--The-trivial-net--An-aside___-the-trivial-net-in-curved-spacetime)
compares it with the Minkowski one.

```lean (name := checkNonempty)
open Physicslib4 AQFT HaagKastlerCurved in
#check nonempty_haagKastlerNet
```

```leanOutput checkNonempty
Physicslib4.AQFT.HaagKastlerCurved.nonempty_haagKastlerNet.{u} (M : LorentzianSpacetime) : Nonempty (HaagKastlerNet M)
```

Lean does not print the second universe of `HaagKastlerNet`: the net has its algebras in
universe 0, since the model is built from $`\mathbb{C}`. The geometric form, for a Lorentzian
spacetime $`L` with the group of Axiom 5 taken to be its isometries connected to the identity:

```lean (name := checkNonemptyGeom)
open Physicslib4 Spacetime LorentzianSpacetime in
#check nonempty_haagKastlerNet_identityComponent
```

```leanOutput checkNonemptyGeom
Physicslib4.Spacetime.LorentzianSpacetime.nonempty_haagKastlerNet_identityComponent
  (L : Spacetime.LorentzianSpacetime) : Nonempty (HaagKastlerNet L.toAbstractIdentityComponent)
```

[bp-la]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-algebras-in-curved-spacetime
[bp-lc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity-in-curved-spacetime
[bp-lo]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-observable
[bp-lcomp]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-completeness-in-curved-spacetime
[bp-net]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:haag-kastler-net-in-curved-spacetime
[bp-ne]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:haag-kastler-net-in-curved-spacetime-nonempty

## Einstein causality and local von Neumann algebras

Blueprint: [thrm:einstein-causality-in-curved-spacetime][bp-ec],
[lmm:local-commutativity-mono-in-curved-spacetime][bp-lcm],
[def:local-von-neumann-algebra-in-curved-spacetime][bp-lvn],
[thrm:von-neumann-bundled-order-in-curved-spacetime][bp-vno],
[thrm:statistical-independence-bundled-in-curved-spacetime][bp-si],
[def:relative-commutant-in-curved-spacetime][bp-rc],
[thrm:self-inclusion-factor-in-curved-spacetime][bp-sif].

Einstein causality, in any representation $`\pi` of a containing algebra
$`\mathfrak{U}(\mathbf{B})`: the operators of completely spacelike basis sets
$`\mathbf{B}_1, \mathbf{B}_2 \subseteq \mathbf{B}` commute. It is Axiom 3 mapped by $`\pi`.

```lean (name := checkEinstein)
open Physicslib4 AQFT HaagKastlerCurved in
#check HaagKastlerNet.einstein_causality
```

```leanOutput checkEinstein
Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.einstein_causality.{u, v, u_1} {M : LorentzianSpacetime}
  (N : HaagKastlerNet M) {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] H →L[ℂ] H) ⦃B₁ B₂ : Set M.Carrier⦄
  (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂) (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
  (a : N.algebra B₁) (b : N.algebra B₂) : Commute (π ((N.commIsotony hB₁ hB h₁) a)) (π ((N.commIsotony hB₂ hB h₂) b))
```

The GNS form, for a state on $`\mathfrak{U}(\mathbf{B})`, is
{apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_einstein_causality}[`exists_gns_einstein_causality`].
The version for subregions $`\mathbf{B}'_1 \subseteq \mathbf{B}_1` and
$`\mathbf{B}'_2 \subseteq \mathbf{B}_2` of a completely spacelike pair is
{apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.commute_of_spacelike_mono_geometric}[`commute_of_spacelike_mono_geometric`],
over the bridge, where complete spacelike separation is inherited by subsets.

The local von Neumann algebras are relative to a containing basis set and a representation of its
algebra. The local operators $`\pi(\mathfrak{U}(\mathbf{B}'))` and their bicommutant as a set are
{apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localOperators}[`localOperators`] and
{apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann}[`localVonNeumann`];
the bundled form is

{docstring Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra}

Microcausality, $`R(\mathbf{B}_1) \le R(\mathbf{B}_2)'`:

```lean (name := checkMicro)
open Physicslib4 AQFT HaagKastlerCurved in
#check HaagKastlerNet.localVonNeumannAlgebra_le_commutant
```

```leanOutput checkMicro
Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_le_commutant.{u_1, u_2, u_3}
  {M : LorentzianSpacetime} (N : HaagKastlerNet M) {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] H →L[ℂ] H) ⦃B₁ B₂ : Set M.Carrier⦄
  (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂) (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
  N.localVonNeumannAlgebra π hB₁ hB h₁ ≤ (N.localVonNeumannAlgebra π hB₂ hB h₂).commutant
```

Over the bridge, the hypothesis may be weakened to $`\mathbf{B}_1` lying in the spacelike
complement of $`\mathbf{B}_2`, additive-free locality
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric}[`localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric`]);
no algebra is attached to the complement itself.

Isotony, $`R(\mathbf{B}_1) \le R(\mathbf{B}_2)` for
$`\mathbf{B}_1 \subseteq \mathbf{B}_2 \subseteq \mathbf{B}`, with no hypothesis beyond the
axioms, since the composition law of Axiom 2 factors the embedding. Lean prints the proof of
$`\mathbf{B}_1 \subseteq \mathbf{B}`, `h₁₂.trans h₂`, as `⋯`:

```lean (name := checkMono)
open Physicslib4 AQFT HaagKastlerCurved in
#check HaagKastlerNet.localVonNeumannAlgebra_mono
```

```leanOutput checkMono
Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_mono.{u_1, u_2, u_3} {M : LorentzianSpacetime}
  (N : HaagKastlerNet M) {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] H →L[ℂ] H) ⦃B₁ B₂ : Set M.Carrier⦄
  (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂) (h₁₂ : B₁ ⊆ B₂) (h₂ : B₂ ⊆ B) :
  N.localVonNeumannAlgebra π hB₁ hB ⋯ ≤ N.localVonNeumannAlgebra π hB₂ hB h₂
```

The monotone map $`\mathbf{B}' \mapsto R(\mathbf{B}')` on the basis subsets of $`\mathbf{B}` is
{apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.vonNeumannNet}[`vonNeumannNet`]. The
Schlieder property,
{apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_separating}[`localVonNeumannAlgebra_separating`],
says that if $`\mathbf{B}_1` and $`\mathbf{B}_2` are completely spacelike and $`\Omega` is cyclic
for the local operators of $`\mathbf{B}_1`, then $`\Omega` is separating for $`R(\mathbf{B}_2)`.
The library has no Reeh–Schlieder theorem, so cyclicity is a hypothesis. The
relative commutant $`R(\mathbf{B}_1)' \cap R(\mathbf{B}_2)` is
{apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant}[`relativeCommutant`];
the inclusion of $`R(\mathbf{B}')` in itself is irreducible exactly when $`R(\mathbf{B}')` is a
factor
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isIrreducibleInclusion_self_iff_isFactor}[`isIrreducibleInclusion_self_iff_isFactor`]).

[bp-ec]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:einstein-causality-in-curved-spacetime
[bp-lcm]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:local-commutativity-mono-in-curved-spacetime
[bp-lvn]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-algebra-in-curved-spacetime
[bp-vno]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-bundled-order-in-curved-spacetime
[bp-si]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-bundled-in-curved-spacetime
[bp-rc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:relative-commutant-in-curved-spacetime
[bp-sif]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:self-inclusion-factor-in-curved-spacetime

## Stabilisers, covariant states and KMS states

Blueprint: [def:stabilizer-action-in-curved-spacetime][bp-sa],
[lmm:stabilizer-action-laws-in-curved-spacetime][bp-sal],
[thrm:gns-unitary-stabilizer-in-curved-spacetime][bp-gu],
[thrm:gns-unitary-stabilizer-strongly-continuous-in-curved-spacetime][bp-gus],
[thrm:von-neumann-covariance-iso-in-curved-spacetime][bp-vci],
[def:covariant-state-family-in-curved-spacetime][bp-csf],
[def:flow-aut-in-curved-spacetime][bp-fa], [def:kms-state-for-flow-in-curved-spacetime][bp-kms],
[def:ground-state-for-flow-in-curved-spacetime][bp-gs].

The stabiliser automorphisms, and their bundled form as a group homomorphism into the
\*-automorphisms of $`\mathfrak{U}(\mathbf{B})`:

{docstring Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.stabAut}

{docstring Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.stabAutMonoidHom}

A state $`\omega` on $`\mathfrak{U}(\mathbf{B})` invariant under the stabiliser gives a GNS triple
$`(H, \pi, \Omega)` and unitaries $`U(g)`, $`g \in \mathrm{Stab}(\mathbf{B})`, with
$`U(g)\pi(a)\Omega = \pi(\hat\alpha_g a)\Omega`, $`U(g)\Omega = \Omega`, the group laws, and
operator covariance $`U(g)\pi(a)U(g)^{-1} = \pi(\hat\alpha_g a)`
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_unitary_stabilizer}[`exists_gns_unitary_stabilizer`]).
With a topology on `M.Isom` and continuous matrix coefficients
$`g \mapsto \omega(a^*\hat\alpha_g b)`, $`U` is strongly continuous
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_unitary_stabilizer_strongContinuous}[`exists_gns_unitary_stabilizer_strongContinuous`]);
the `Rep` forms return $`U` as a group homomorphism. They are the GNS chapter's
[unitary implementation theorems](The-GNS-construction/#physicslib4-reference-manual--The-GNS-construction--Design--Covariance-and-unitary-implementation) applied to the algebra
$`\mathfrak{U}(\mathbf{B})` and the action $`\hat\alpha`; their statements are long nested
existentials, best read in the API documentation.

Such unitaries carry the local von Neumann algebras along the stabiliser:
$`U(g) R(\mathbf{B}_1) U(g)^{-1} = R(g\mathbf{B}_1)` for $`\mathbf{B}_1 \subseteq \mathbf{B}`
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.lieConj_image_localVonNeumann}[`lieConj_image_localVonNeumann`]),
so being a factor is preserved by the stabiliser
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_isFactor_smul}[`localVonNeumann_isFactor_smul`]).
As a \*-isomorphism:

{docstring Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannEquiv}

Each $`\mathfrak{U}(\mathbf{B})` is a unital C\*-algebra, so the GNS chapter's results on purity
apply to it region by region: a state is pure if and only if it is extreme
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.pure_iff_extreme}[`pure_iff_extreme`]),
if and only if its GNS representation is irreducible
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_pure_iff_irreducible}[`exists_gns_pure_iff_irreducible`]).
A pure invariant state has an irreducible covariant GNS representation
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_irreducible_covariant_stabilizer}[`exists_gns_irreducible_covariant_stabilizer`]).
This is not a vacuum: curved spacetime has no global vacuum, and no analogue of the spectrum
condition is imposed. Further results, one line each: the centre of $`R(\mathbf{B}')` is that of
its commutant ({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_center_eq_commutant}[`localVonNeumannAlgebra_center_eq_commutant`]),
and $`R(\mathbf{B}')` is a factor exactly when its centre is the scalars
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_isFactor_iff_center_eq_scalars}[`localVonNeumannAlgebra_isFactor_iff_center_eq_scalars`]);
two irreducible representations of $`\mathfrak{U}(\mathbf{B})` are disjoint or unitarily
equivalent ({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.areDisjoint_or_unitaryEquiv_of_isIrreducible}[`areDisjoint_or_unitaryEquiv_of_isIrreducible`]);
the GNS representation of a state pulled back along $`\alpha_\varphi` or $`\hat\alpha_g` is,
up to unitary equivalence, the original one composed with the map, so the superselection type is
invariant ({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.unitaryEquiv_gns_covEquiv}[`unitaryEquiv_gns_covEquiv`],
{apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.unitaryEquiv_gns_stabAut}[`unitaryEquiv_gns_stabAut`]);
and purity is invariant under the stabiliser
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isPure_precomp_stabAut_iff}[`isPure_precomp_stabAut_iff`]).

Without a quasilocal algebra there is no single global state; the available form of a covariant
state is a family of local states:

{docstring Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsCovariantFamily}

A curve $`t \mapsto \varphi_t` in $`\mathrm{Stab}(\mathbf{B})` gives automorphisms
$`\tau_t = \hat\alpha_{(\varphi_t)}` of $`\mathfrak{U}(\mathbf{B})`
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.flowAut}[`flowAut`]). When the curve
is a one-parameter subgroup, they form a one-parameter group, the time evolution along the flow:

```lean (name := checkFlow)
open Physicslib4 AQFT HaagKastlerCurved in
#check HaagKastlerNet.isOneParameterAut_flowAut
```

```leanOutput checkFlow
Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isOneParameterAut_flowAut.{u, v} {M : LorentzianSpacetime}
  (N : HaagKastlerNet M) (B : Set M.Carrier) (flow : ℝ → ↥(MulAction.stabilizer M.Isom B)) (h0 : flow 0 = 1)
  (hadd : ∀ (s t : ℝ), flow (s + t) = flow s * flow t) : IsOneParameterAut (N.flowAut B flow)
```

Thermal and ground states for the flow:

{docstring Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow}

{docstring Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsGroundStateForFlow}

The KMS states for a flow at a given $`\beta` form a convex set
({apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow.convexCombo}[`IsKMSStateForFlow.convexCombo`]).
The library does not prove that the Hartle–Hawking or Bunch–Davies states are KMS states; no
concrete net on Schwarzschild or de Sitter spacetime is constructed. The regions of those
examples are not basis sets, and no Killing flow of that kind fixes a nonempty diamond, so the
axioms as stated place no constraint on their algebras: the examples motivate the definitions but
are not instances of them (see the
{ref "curved-design"}[Design section]).

[bp-sa]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:stabilizer-action-in-curved-spacetime
[bp-sal]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:stabilizer-action-laws-in-curved-spacetime
[bp-gu]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-unitary-stabilizer-in-curved-spacetime
[bp-gus]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-unitary-stabilizer-strongly-continuous-in-curved-spacetime
[bp-vci]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-covariance-iso-in-curved-spacetime
[bp-csf]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-state-family-in-curved-spacetime
[bp-fa]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:flow-aut-in-curved-spacetime
[bp-kms]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state-for-flow-in-curved-spacetime
[bp-gs]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:ground-state-for-flow-in-curved-spacetime

## General covariance

Blueprint: [def:net-equivalence-in-curved-spacetime][bp-neq],
[def:general-covariance-in-curved-spacetime][bp-gc].

An equivalence of two nets along a bijection of their spacetimes:

{docstring Physicslib4.AQFT.HaagKastlerCurved.NetEquivalence}

A theory, as a net on every geometric spacetime, and the relabelling map along which general
covariance compares the nets over $`\psi^*L` and over $`L`:

{docstring Physicslib4.AQFT.HaagKastlerCurved.NetTheory}

{docstring Physicslib4.Spacetime.LorentzianSpacetime.pullbackCarrierEquiv}

The postulate:

{docstring Physicslib4.AQFT.HaagKastlerCurved.IsGenerallyCovariant}

The library states the postulate and proves the geometry it rests on: that the pullback of a
Lorentzian spacetime is one, and that $`\psi` carries the diamonds of $`\psi^*L` to those of $`L`
({apiDocs Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent_pullback_isBasisSet}[`toAbstractIdentityComponent_pullback_isBasisSet`];
the {ref "spacetime-main"}[Spacetime chapter] describes pullbacks and cross-metric isometries). It
proves no net theory generally covariant. Mathematically the trivial theory, with
$`\mathfrak{U}_L` the trivial net on every $`L` and every $`\Theta_{\mathbf{B}}` the identity of
$`\mathbb{C}`, is; the library has no lemma for it.

# Where to look
%%%
tag := "curved-files"
%%%

The sections are formalised in `Physicslib4/AQFT/HaagKastlerCurved/`, one topic per file. Each
entry links to the API documentation of a representative declaration, from which the rest of the
file can be browsed.

The axioms:

* `Spacetime.lean`: the abstract interface,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.LorentzianSpacetime}[`LorentzianSpacetime`].
* `LocalAlgebras.lean`, `Isotony.lean`, `LocalCommutativity.lean`: Axioms 1 to 3,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.LocalNet}[`LocalNet`].
* `LocalAlgebra.lean`: local observables and Axiom 4, which holds for every net,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.localAlgebra_of}[`localAlgebra_of`].
* `IsometricCovariance.lean`: Axiom 5,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance}[`IsometricCovariance`].
* `Net.lean`: the bundled net, the maps `commIsotony` and `covEquiv`, and the trivial net,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet}[`HaagKastlerNet`].
* `Concrete.lean`: the bridge from a geometric spacetime and the geometric forms of two results,
  {apiDocs Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent}[`toAbstractIdentityComponent`].
* `IdentityComponent.lean`: consistency over a geometric spacetime,
  {apiDocs Physicslib4.Spacetime.LorentzianSpacetime.nonempty_haagKastlerNet_identityComponent}[`nonempty_haagKastlerNet_identityComponent`].

Consequences:

* `EinsteinCausality.lean`: Einstein causality in a representation,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.einstein_causality}[`einstein_causality`].
* `LocalVonNeumann.lean`: local von Neumann algebras, relative commutants and factors,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra}[`localVonNeumannAlgebra`].
* `Purity.lean`: purity of states on a local algebra,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.pure_iff_extreme}[`pure_iff_extreme`].
* `CovariantState.lean`: covariant families of local states,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsCovariantFamily}[`IsCovariantFamily`].
* `StabilizerAction.lean`: the stabiliser action and its GNS unitary implementation,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.stabAutMonoidHom}[`stabAutMonoidHom`].
* `GeometricCovariance.lean`: covariance of the local von Neumann algebras under the stabiliser,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannEquiv}[`localVonNeumannEquiv`].
* `StabilizerKMS.lean`: flows, KMS states and ground states,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow}[`IsKMSStateForFlow`].

General covariance:

* `GeneralCovariance.lean`: net equivalences, net theories and the postulate,
  {apiDocs Physicslib4.AQFT.HaagKastlerCurved.IsGenerallyCovariant}[`IsGenerallyCovariant`]. The
  geometry it uses, pullback metrics and cross-metric isometries, is in
  `Physicslib4/Spacetime/Pullback.lean` and `Physicslib4/Spacetime/CrossMetricIsometry.lean`.

The general definitions these files use, the KMS condition `AQFT.IsKMSState` and positive energy
`AQFT.IsPositiveEnergy`, are in `Physicslib4/AQFT/KMS.lean` and
`Physicslib4/AQFT/PositiveEnergy.lean`; the GNS results are described in the
{ref "gns"}[GNS chapter]. The blueprint sections are
[Section 10.7](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:haag-kastler-axioms-in-curved-spacetime)
and
[Section 10.8](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:general-covariance-in-curved-spacetime),
and the section pages for [Section 10.7](https://physicslib.github.io/physicslib4/sec10-7-curved.html)
and [Section 10.8](https://physicslib.github.io/physicslib4/sec10-8-general-covariance.html) list
each entry with the Lean declaration that formalises it.
