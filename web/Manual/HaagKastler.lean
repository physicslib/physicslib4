import VersoManual
import Book.Meta
import Physicslib4.AQFT.HaagKastler.Net
import Physicslib4.AQFT.HaagKastler.EinsteinCausality
import Physicslib4.AQFT.HaagKastler.LocalVonNeumann
import Physicslib4.AQFT.HaagKastler.StrongDensity
import Physicslib4.AQFT.HaagKastler.ObservableBridge
import Physicslib4.AQFT.HaagKastler.VacuumState
import Physicslib4.AQFT.HaagKastler.QuasilocalKMS
import Physicslib4.AQFT.HaagKastler.GeometricCovariance
import Physicslib4.AQFT.HaagKastler.CovariantState
import Physicslib4.AQFT.HaagKastler.Purity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book
-- Docstring code spans are elaborated in this scope; these namespaces let the names they mention,
-- written relative to the library's namespaces, resolve and link.
open Physicslib4 Physicslib4.AQFT Physicslib4.AQFT.HaagKastler
open Physicslib4.AQFT.HaagKastler.HaagKastlerNet

#doc (Manual) "The Haag–Kastler axioms in Minkowski spacetime" =>

%%%
tag := "haag-kastler"
file := "Haag-Kastler-axioms-in-Minkowski-spacetime"
%%%

This chapter describes how the library states the Haag–Kastler axioms on Minkowski spacetime and
what it proves from them. It corresponds to Section 10.6 of the
[blueprint](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html).
The physics is introduced in [chapter 1 of the tutorial](../tutorial/AQFT-in-brief/), and the Lean
needed to read the declarations in [chapter 2](../tutorial/Lean-in-brief/); this chapter assumes
both.

# Overview
%%%
tag := "haag-kastler-overview"
%%%

As you will recall, a theory in the Haag–Kastler framework is a _net_ of C\*-algebras: to each
bounded region $`\mathbf{B}` of spacetime it assigns an algebra $`\mathfrak{U}(\mathbf{B})` of
the observables measurable in $`\mathbf{B}`, and the axioms say how these algebras relate. The
library states the axioms in the sharpened form of the blueprint, which fixes the points the 1964
paper leaves open. Five declarations carry them:

* `LocalNet`, Axiom 1: a unital C\*-algebra $`\mathfrak{U}(\mathbf{B})` for every causal diamond
  $`\mathbf{B} = I^+(p) \cap I^-(q)`, with $`\mathfrak{U}(\emptyset) = \mathbb{C}\mathbf{1}`;
* `Isotony`, Axiom 2: a coherent family of unital \*-monomorphisms
  $`i_{\mathbf{B}_1\mathbf{B}_2} : \mathfrak{U}(\mathbf{B}_1) \to \mathfrak{U}(\mathbf{B}_2)` for
  $`\mathbf{B}_1 \subseteq \mathbf{B}_2`;
* `LocalCommutativity`, Axiom 3: the images of the algebras of two completely spacelike diamonds
  commute in the algebra of any diamond containing both;
* `LorentzCovariance`, Axiom 5: the identity component of the Poincaré group acts on the net by
  \*-isomorphisms $`\alpha_L : \mathfrak{U}(\mathbf{B}) \to \mathfrak{U}(L\mathbf{B})` that respect
  isotony;
* `HaagKastlerNet`, which bundles the four.

Axiom 4, that every physical observable is a quasilocal observable, is a statement about the world,
and is the separate structure `ObservableCorrespondence`. The quasilocal algebra $`\mathfrak{U}`,
which the 1964 axioms take for granted, is constructed: every net satisfying Axiom 2 has one, the
completion of the directed colimit of its local algebras. Primitivity, the sixth axiom of 1964, is
not adopted.

From the axioms the library proves:

* the consistency of the axioms, by a model, the trivial net;
* local commutativity in the quasilocal algebra, and its equivalence with Axiom 3;
* Einstein causality: in every representation of $`\mathfrak{U}`, observables of completely
  spacelike diamonds commute as operators on the Hilbert space;
* the basic properties of the local von Neumann algebras
  $`R(\mathbf{B}) = \pi(\mathfrak{U}(\mathbf{B}))''`: isotony, microcausality, and the Schlieder
  property;
* the von Neumann density theorem, by which no finite set of measurements distinguishes an element
  of $`\pi(\mathfrak{U})''`, to any given accuracy, from an element of $`\pi(\mathfrak{U})`;
* the extension of the Poincaré action to automorphisms of $`\mathfrak{U}`, and the unitary
  implementation of the action in the GNS representation of an invariant state.

It also defines vacuum states, by invariance and the spectrum condition, and KMS and ground states
for a one-parameter subgroup of the Poincaré group. All declarations of the chapter are in the
namespace `Physicslib4.AQFT.HaagKastler`, written without it below.

# Design
%%%
tag := "haag-kastler-design"
%%%

The blueprint is the specification: each definition below is checked against its blueprint entry,
which records the reasons for the choices made. This section collects those reasons.

## Regions are causal diamonds

The 1964 axioms attach algebras to the open sets of spacetime with compact closure, without naming
the topology. The library uses the Alexandrov topology, whose basic open sets are the causal
diamonds $`I^+(p) \cap I^-(q)`, and attaches algebras to the diamonds themselves. The predicate is
`IsAlexandrovBasisSet`. Chronological rather than causal cones make every diamond open, so no
algebra is attached to a point, and the empty set counts as a diamond, the one with
$`p \not\ll q`; its algebra is $`\mathbb{C}\mathbf{1}`. The
[tutorial](../tutorial/AQFT-in-brief/#physicslib4-tutorial--AQFT-in-brief--Regions-of-spacetime--Causal-diamonds)
explains why diamonds are the right regions physically.

In Lean the field `LocalNet.algebra` is a function on _all_ subsets of spacetime. This keeps it a
plain function, so that $`\mathfrak{U}(L\mathbf{B})` is simply `U.algebra (L • B)`. Its values on
sets that are not diamonds are never constrained: every axiom, and every embedding into the
quasilocal algebra, takes a proof `hB : IsAlexandrovBasisSet B` as an argument, and quantifies only
over diamonds. Indexing the quasilocal embeddings over all subsets would be wrong, not merely
wasteful: the blueprint gives a net for which no such family exists
([thrm:quasilocal-algebra-exists](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-algebra-exists),
first design note).

## Isotony is data

The 1964 isotony axiom says $`\mathfrak{U}(\mathbf{B}_1) \subset \mathfrak{U}(\mathbf{B}_2)` for
$`\mathbf{B}_1 \subseteq \mathbf{B}_2`. For abstract algebras, inclusion must be a map, and the
library makes the maps part of the net: `Isotony` is a structure, not a proposition, with the
family `map` of unital \*-monomorphisms and the laws

$$`i_{\mathbf{B}\mathbf{B}} = \mathrm{id}, \qquad i_{\mathbf{B}_2\mathbf{B}_3} \circ i_{\mathbf{B}_1\mathbf{B}_2} = i_{\mathbf{B}_1\mathbf{B}_3}.`

An existence statement, "for each inclusion there is some monomorphism", could not express these
laws, which are equations between particular maps. The laws are required rather than derived:
nothing about the spacetime constrains which monomorphism a net chooses. They make the local
algebras a directed system, and this is what gives the quasilocal algebra a well-defined product
(blueprint
[def:isotony](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony)).
Because the maps are unital (Mathlib's `StarAlgHom` preserves $`\mathbf{1}`), the local algebras
have in effect a common unit, as the 1964 Axiom 2 requires; because they are injective, they are
isometric.

Since isotony is data, the later axioms are stated relative to it: `LocalCommutativity U i` and
`LorentzCovariance U i` both take the isotony family `i` as a parameter, and so does
`QuasilocalAlgebra U i`. There is one isotony family in a net, and every condition refers to it.

## Local commutativity in a common diamond

Two completely spacelike diamonds $`\mathbf{B}_1` and $`\mathbf{B}_2` have algebras with nothing
in common, so their elements can only be multiplied after both are mapped into one algebra. The
library's Axiom 3 uses the algebra of a diamond $`\mathbf{B}` containing both:

$$`i_{\mathbf{B}_1\mathbf{B}}(a_1)\, i_{\mathbf{B}_2\mathbf{B}}(a_2) = i_{\mathbf{B}_2\mathbf{B}}(a_2)\, i_{\mathbf{B}_1\mathbf{B}}(a_1) \quad\text{for every such } \mathbf{B}.`

The statement uses only the net and isotony; in particular it does not use the quasilocal algebra.
In Minkowski spacetime a containing diamond always exists (`Spacetime.alexandrovBasis_directed`),
and the axiom is equivalent to commutation of $`\iota_{\mathbf{B}_1}(a_1)` and
$`\iota_{\mathbf{B}_2}(a_2)` in the quasilocal algebra, the textbook form. The reason for the
choice is curved spacetime, where two diamonds need not lie in a common diamond and there may be no
quasilocal algebra at all; the same statement then still makes sense, and is the curved-spacetime
Axiom 3. Stating it the same way in both settings lets the Minkowski axioms be read as the special
case (blueprint
[def:local-commutativity](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity);
the tutorial works through the equivalence in
[chapter 3](../tutorial/Worked-examples/#physicslib4-tutorial--Worked-examples--Local-commutativity-in-a-diamond--Worked-proof___-from-the-common-diamond-to-the-quasilocal-algebra)).

## Covariance under the identity component

As you will recall, the Poincaré group has four connected components. The axioms ask only for the
component of the identity, with $`\det\Lambda = 1` and $`\Lambda` preserving the direction of
time: a theory need not be invariant under parity or time reversal (the weak interaction violates
parity). `InhomogeneousLorentzGroup` is that component, as pairs $`(\Lambda, a)` acting
by $`x \mapsto \Lambda x + a`; it is a topological group. It maps diamonds to diamonds
(`isAlexandrovBasisSet_smul`), since $`\Lambda` preserves chronological precedence.

`LorentzCovariance U i` asserts that there are \*-isomorphisms
$`\alpha_L : \mathfrak{U}(\mathbf{B}) \to \mathfrak{U}(L\mathbf{B})` with $`\alpha_1 = \mathrm{id}`,
$`\alpha_{L'L} = \alpha_{L'} \circ \alpha_L`, and
$`\alpha_L \circ i_{\mathbf{B}_1\mathbf{B}_2} = i_{L\mathbf{B}_1\,L\mathbf{B}_2} \circ \alpha_L`.
Two details of the encoding are worth knowing when reading the Lean.

* The isotony family in the third condition is the net's own `i`, not one chosen for the purpose,
  and the inclusion $`L\mathbf{B}_1 \subseteq L\mathbf{B}_2` and the fact that both are diamonds are
  proved inside the statement, not assumed.
* $`\mathfrak{U}(1\mathbf{B})` and $`\mathfrak{U}(\mathbf{B})` are different types, equal only by
  the theorem `one_smul`; similarly for $`(L'L)\mathbf{B}` and $`L'(L\mathbf{B})`. The first two
  conditions transport along these equalities with `Eq.mp`, which is why they look heavier in Lean
  than on paper. `HaagKastlerNet.covEquiv` chooses the maps, and `covEquiv_one`, `covEquiv_mul` and
  `covEquiv_isotony` state the three conditions for them.

The maps $`\alpha_L` act between local algebras. They extend to \*-automorphisms $`\beta_L` of the
quasilocal algebra, with $`\beta_L(\iota_{\mathbf{B}}a) = \iota_{L\mathbf{B}}(\alpha_L a)`; this is
proved, not assumed, and $`\beta_L` is unique.

## The quasilocal algebra is constructed

The 1964 Axiom 4 takes the set-theoretic union of the local algebras to be a normed \*-algebra and
completes it, which presupposes that the algebras sit inside one another. In the library the
quasilocal algebra is built from the net: the local algebras, glued along the isotony maps, form a
directed colimit; the norm $`\|[a]\| = \|a\|` is well defined because the isotony maps are
isometric; and the completion is a C\*-algebra. Mathlib has no direct limit of C\*-algebras, so the
construction is carried out in `QuasilocalColimit.lean`, and `exists_quasilocalAlgebra` packages the
result. An alternative, a closed subalgebra of some ambient C\*-algebra containing all the local
algebras, is rejected: it would assume the ambient algebra, and nothing in the physics supplies one.

The rest of the library does not see the construction. It uses the structure `QuasilocalAlgebra`,
which records the properties that characterise a quasilocal algebra: an algebra $`\mathfrak{U}`,
embeddings $`\iota_{\mathbf{B}}` compatible with isotony, and density of their images. Results are
stated either for every quasilocal algebra, with `Q : QuasilocalAlgebra U i` as a hypothesis, or
for the net's own, `HaagKastlerNet.quasilocal`, which chooses one. The library does not prove that
the quasilocal algebra is unique up to isomorphism, although it is: injective \*-homomorphisms of
C\*-algebras are isometric, so the norm on the union of the images is forced.

The 1964 Axiom 4 adds that $`\mathfrak{U}` contains "all observables of interest". Once
$`\mathfrak{U}` is constructed, what remains is a claim about physics: every physical observable
corresponds to a self-adjoint element of $`\mathfrak{U}`. The library keeps it apart, as
the structure `ObservableCorrespondence`, which no theorem about nets uses; `HaagKastlerNet`
therefore has no field for it (blueprint
[def:quasilocal-completeness](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-completeness)).
The von Neumann density theorem below is what keeps it consistent with the larger von Neumann
algebras of a representation.

## Universes

`LocalNet` is universe polymorphic: `LocalNet.{u}` has local algebras in `Type u`. A quasilocal
algebra of such a net has its carrier in the same universe. A carrier in `Type 0` could not contain
injective copies of larger algebras; a free universe would not be inferable, and would make the
quasilocal form of Axiom 3 depend on it. Nothing is lost, since density makes $`\mathfrak{U}` the
closure of the images of the local algebras. `HaagKastlerNet` names the universe of its field `U`
so that it, too, is a parameter. The consistency theorem `nonempty_haagKastlerNet` is stated for
`HaagKastlerNet.{0}`, since its model is built from $`\mathbb{C}`; one model suffices. Universes in
general are explained in the
[tutorial](../tutorial/Lean-in-brief/#physicslib4-tutorial--Lean-in-brief--Structures-and-type-classes--An-aside-on-universes).

# Main definitions and theorems
%%%
tag := "haag-kastler-main"
%%%

Definitions are shown with their docstrings, which give the mathematics and the blueprint entry;
theorems with their statements, as Lean prints them, and a line or two of explanation. Each
subsection opens with the blueprint entries it covers. For the declarations not shown here, see the
[API documentation](https://physicslib.github.io/physicslib4/docs/Physicslib4/AQFT/HaagKastler/Net.html)
and the files listed at the end of the chapter.

## The axioms

Blueprint: [def:local-algebras][bp-local], [def:isotony][bp-isotony],
[def:local-commutativity][bp-lc], [def:lorentz-covariance][bp-cov], [def:haag-kastler-net][bp-net].

The regions are the causal diamonds:

{docstring Physicslib4.AQFT.HaagKastler.IsAlexandrovBasisSet}

Axiom 1 is a structure with three fields. Lean finds the field `instCStarAlgebra` automatically
(it is an instance), so `U.algebra B` is a C\*-algebra wherever `U : LocalNet` is in scope:

{docstring Physicslib4.AQFT.HaagKastler.LocalNet}

Axiom 2 is a structure over the net. Its fields take the diamond hypotheses explicitly and the
regions as strict-implicit arguments, so the embedding of $`\mathbf{B}_1` in $`\mathbf{B}_2` is
written `i.map hB₁ hB₂ h`, with `h : B₁ ⊆ B₂`:

{docstring Physicslib4.AQFT.HaagKastler.Isotony}

Axiom 3 is a proposition about a net and its isotony family. Read with the tutorial's
[unfolding](../tutorial/Lean-in-brief/#physicslib4-tutorial--Lean-in-brief--Definitions-that-are-propositions--Local-commutativity)
of its quantifiers, it is the displayed equation of the Design section:

{docstring Physicslib4.AQFT.HaagKastler.LocalCommutativity}

The symmetry group of Axiom 5, and the axiom itself:

{docstring Physicslib4.AQFT.HaagKastler.InhomogeneousLorentzGroup +hideStructureConstructor}

{docstring Physicslib4.AQFT.HaagKastler.LorentzCovariance}

The bundled net. A theorem about a quantum field theory takes `N : HaagKastlerNet` as a
hypothesis, and reaches the axioms as `N.U`, `N.isotony`, `N.localCommutativity` and
`N.lorentzCovariance`:

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet}

The axioms are consistent. The trivial net, which assigns $`\mathbb{C}` to every region with every
map the identity, satisfies all of them; the
[tutorial](../tutorial/Worked-examples/#physicslib4-tutorial--Worked-examples--The-trivial-net--The-Lean-statement)
builds it step by step.

```lean (name := checkNonempty)
open Physicslib4 AQFT HaagKastler in
#check nonempty_haagKastlerNet
```

```leanOutput checkNonempty
Physicslib4.AQFT.HaagKastler.nonempty_haagKastlerNet : Nonempty HaagKastlerNet
```

The statement is at universe 0, since the model is built from $`\mathbb{C}`, a type in `Type`.

[bp-local]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-algebras
[bp-isotony]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony
[bp-lc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity
[bp-cov]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentz-covariance
[bp-net]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:haag-kastler-net

## The quasilocal algebra and Axiom 4

Blueprint: [def:quasilocal-algebra][bp-qa], [thrm:quasilocal-algebra-exists][bp-qa-exists],
[lmm:local-commutativity-any-quasilocal][bp-lc-any],
[lmm:local-commutativity-iff-quasilocal][bp-lc-iff], [def:quasilocal-observable][bp-qo],
[def:quasilocal-completeness][bp-ax4].

The interface through which the library uses the quasilocal algebra:

{docstring Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra}

Every net satisfying Axiom 2 has a quasilocal algebra. The proof assembles the colimit-and-completion
construction of `QuasilocalColimit.lean`; nothing about $`\mathfrak{U}` is assumed.

```lean (name := checkExists)
open Physicslib4 AQFT HaagKastler in
#check exists_quasilocalAlgebra
```

```leanOutput checkExists
Physicslib4.AQFT.HaagKastler.exists_quasilocalAlgebra.{u} (U : LocalNet) (i : Isotony U) :
  Nonempty (QuasilocalAlgebra U i)
```

A net's own quasilocal algebra is chosen from this theorem:

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.quasilocal}

Local commutativity then holds in every quasilocal algebra. The proof picks a diamond containing
both regions, uses the compatibility $`\iota_{\mathbf{B}} \circ i_{\mathbf{B}_k\mathbf{B}} =
\iota_{\mathbf{B}_k}` to move both elements into the image of $`\mathfrak{U}(\mathbf{B})`, and
applies the homomorphism $`\iota_{\mathbf{B}}` to the commutation in $`\mathfrak{U}(\mathbf{B})`:

```lean (name := checkCommuteι)
open Physicslib4 AQFT HaagKastler in
#check LocalCommutativity.commute_ι
```

```leanOutput checkCommuteι
Physicslib4.AQFT.HaagKastler.LocalCommutativity.commute_ι.{u_1} {U : LocalNet} {i : Isotony U}
  (h : LocalCommutativity U i) (Q : QuasilocalAlgebra U i) ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
  (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
  (hs : StandardMinkowskiSpacetime.IsCompletelySpacelike standardMinkowskiTimeOrientation B₁ B₂) (a : U.algebra B₁)
  (b : U.algebra B₂) : Commute ((Q.ι hB₁) a) ((Q.ι hB₂) b)
```

For a bundled net and its own quasilocal algebra this is `HaagKastlerNet.commute_ι_of_spacelike`.
Conversely, commutation in a single quasilocal algebra implies Axiom 3; this direction uses the
injectivity of $`\iota_{\mathbf{B}}`. So the library's axiom is equivalent to the textbook form:

```lean (name := checkIff)
open Physicslib4 AQFT HaagKastler in
#check localCommutativity_iff_exists_commute_ι
```

```leanOutput checkIff
Physicslib4.AQFT.HaagKastler.localCommutativity_iff_exists_commute_ι.{u_1} (U : LocalNet) (i : Isotony U) :
  LocalCommutativity U i ↔
    ∃ Q,
      ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄ (hB₁ : IsAlexandrovBasisSet B₁)
        (hB₂ : IsAlexandrovBasisSet B₂),
        StandardMinkowskiSpacetime.IsCompletelySpacelike standardMinkowskiTimeOrientation B₁ B₂ →
          ∀ (a : U.algebra B₁) (b : U.algebra B₂), Commute ((Q.ι hB₁) a) ((Q.ι hB₂) b)
```

As you will recall, the observables of a theory in a state $`\omega` are the self-adjoint operators
$`\pi_\omega(a)` of its GNS representation. The library defines them for any representation:

{docstring Physicslib4.AQFT.HaagKastler.IsQuasilocalObservable}

Axiom 4 joins the physical observables to these. Its encoding lands in the algebra, not in a
representation, so that whether a physical observable is quasilocal does not depend on a choice of
state:

{docstring Physicslib4.AQFT.HaagKastler.ObservableCorrespondence}

Being a quasilocal observable in every representation is then a theorem:

```lean (name := checkMeasure)
open Physicslib4 AQFT HaagKastler in
#check isQuasilocalObservable_measure
```

```leanOutput checkMeasure
Physicslib4.AQFT.HaagKastler.isQuasilocalObservable_measure.{u, u_1, u_2} {U : LocalNet} {i : Isotony U}
  {Q : QuasilocalAlgebra U i} (C : ObservableCorrespondence Q) {H : Type u_1} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] (π : Q.carrier →⋆ₐ[ℂ] H →L[ℂ] H) (o : C.Observable) :
  IsQuasilocalObservable Q π (π (C.measure o))
```

[bp-qa]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-algebra
[bp-qa-exists]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-algebra-exists
[bp-lc-any]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:local-commutativity-any-quasilocal
[bp-lc-iff]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:local-commutativity-iff-quasilocal
[bp-qo]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-observable
[bp-ax4]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-completeness

## Representations and local von Neumann algebras

Blueprint: [thrm:einstein-causality][bp-ec], [def:local-von-neumann][bp-lvn],
[def:local-von-neumann-algebra][bp-lvna], [thrm:von-neumann-isotony][bp-vn-iso],
[thrm:von-neumann-bundled-order][bp-vn-order], [thrm:statistical-independence-bundled][bp-si],
[thrm:quasilocal-strongly-dense][bp-dense].

The results of this part hold in any \*-representation
`π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)` of the quasilocal algebra on a complex Hilbert space
`H`, in particular in the GNS representation of any state. As a `StarAlgHom`, `π` is unital.

Einstein causality is local commutativity pushed through `π`: the operators representing
observables of completely spacelike diamonds commute.

```lean (name := checkEinstein)
open Physicslib4 AQFT HaagKastler in
#check HaagKastlerNet.einstein_causality
```

```leanOutput checkEinstein
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.einstein_causality.{u, u_1} (N : HaagKastlerNet) {H : Type u_1}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : N.quasilocal.carrier →⋆ₐ[ℂ] H →L[ℂ] H)
  ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄ (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
  (hs : StandardMinkowskiSpacetime.IsCompletelySpacelike standardMinkowskiTimeOrientation B₁ B₂) (a : N.U.algebra B₁)
  (b : N.U.algebra B₂) : Commute (π ((N.quasilocal.ι hB₁) a)) (π ((N.quasilocal.ι hB₂) b))
```

`HaagKastlerNet.exists_gns_einstein_causality` states the same for the GNS triple of a state.

In a representation, the local algebras generate von Neumann algebras. The library defines them in
two forms, as sets of operators and as Mathlib's bundled `VonNeumannAlgebra`, with the same
underlying set:

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann}

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra}

The von Neumann algebras inherit isotony and local commutativity. Isotony, $`R(\mathbf{B}_1) \le
R(\mathbf{B}_2)` for $`\mathbf{B}_1 \subseteq \mathbf{B}_2`, follows from the compatibility of the
embeddings $`\iota` with isotony, and makes $`\mathbf{B} \mapsto R(\mathbf{B})` a monotone map
(`HaagKastlerNet.vonNeumannNet`):

```lean (name := checkVNMono)
open Physicslib4 AQFT HaagKastler in
#check HaagKastlerNet.localVonNeumannAlgebra_mono
```

```leanOutput checkVNMono
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_mono.{u_1, u_2} (N : HaagKastlerNet) {H : Type u_1}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : N.quasilocal.carrier →⋆ₐ[ℂ] H →L[ℂ] H)
  ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄ (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
  (h : B₁ ⊆ B₂) : N.localVonNeumannAlgebra π hB₁ ≤ N.localVonNeumannAlgebra π hB₂
```

Microcausality, $`R(\mathbf{B}_1) \le R(\mathbf{B}_2)'` for completely spacelike diamonds, follows
from Einstein causality, since taking commutants reverses inclusions and $`S''' = S'`:

```lean (name := checkVNComm)
open Physicslib4 AQFT HaagKastler in
#check HaagKastlerNet.localVonNeumannAlgebra_le_commutant
```

```leanOutput checkVNComm
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_le_commutant.{u_1, u_2} (N : HaagKastlerNet)
  {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : N.quasilocal.carrier →⋆ₐ[ℂ] H →L[ℂ] H) ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
  (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
  (hs : StandardMinkowskiSpacetime.IsCompletelySpacelike standardMinkowskiTimeOrientation B₁ B₂) :
  N.localVonNeumannAlgebra π hB₁ ≤ (N.localVonNeumannAlgebra π hB₂).commutant
```

Statistical independence (the Schlieder property): if $`\mathbf{B}_1` and $`\mathbf{B}_2` are
completely spacelike and a vector $`\Omega` is cyclic for the local operators of $`\mathbf{B}_1`,
then $`\Omega` is separating for $`R(\mathbf{B}_2)`, so an element of $`R(\mathbf{B}_2)` that
annihilates $`\Omega` is zero. In a vacuum representation the cyclicity is the content of the
Reeh–Schlieder theorem, which the library does not prove; it is a hypothesis here.

```lean (name := checkSeparating)
open Physicslib4 AQFT HaagKastler in
#check HaagKastlerNet.localVonNeumannAlgebra_separating
```

```leanOutput checkSeparating
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_separating.{u_1, u_2} (N : HaagKastlerNet)
  {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : N.quasilocal.carrier →⋆ₐ[ℂ] H →L[ℂ] H) ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
  (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
  (hs : StandardMinkowskiSpacetime.IsCompletelySpacelike standardMinkowskiTimeOrientation B₁ B₂) {Ω : H}
  (hcyc : Dense ((fun T => T Ω) '' N.localOperators π hB₁)) {R : H →L[ℂ] H} (hR : R ∈ N.localVonNeumannAlgebra π hB₂)
  (hRΩ : R Ω = 0) : R = 0
```

`LocalVonNeumann.lean` also develops relative commutants
$`R(\mathbf{B}_1)' \cap R(\mathbf{B}_2)` and irreducible inclusions, and
`GeometricCovariance.lean` shows that a unitary $`U` implementing $`\beta_L`,
$`U\pi(a)U^{-1} = \pi(\beta_L a)`, carries $`R(\mathbf{B})` onto $`R(L\mathbf{B})`.

The von Neumann density theorem keeps Axiom 4 consistent with these algebras. The bicommutant
$`\pi(\mathfrak{U})''` is in general larger than $`\pi(\mathfrak{U})`, and so contains self-adjoint
operators that are not quasilocal observables. But $`\pi(\mathfrak{U})` is dense in it in the strong
operator topology: for every $`T \in \pi(\mathfrak{U})''`, finite set of vectors and $`\varepsilon >
0` there is an $`a` with $`\|\pi(a)\psi_k - T\psi_k\| < \varepsilon` for all $`k`. No finite set of
measurements distinguishes $`T` from $`\pi(a)` to any given accuracy. The theorem is stated for any
unital \*-representation of a \*-algebra; unitality is essential, since for $`\pi = 0` the
bicommutant is $`\mathbb{C}\mathbf{1}`. The statement expresses the strong operator topology as the
topology of pointwise convergence, that is, uniform convergence on finite sets, through
`UniformConvergenceCLM.ofFun` with the family of finite sets:

```lean (name := checkDensity)
open Physicslib4 AQFT HaagKastler in
#check dense_range_in_bicommutant
```

```leanOutput checkDensity
Physicslib4.AQFT.HaagKastler.dense_range_in_bicommutant.{u_1, u_2} {H : Type u_1} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] {𝔄 : Type u_2} [Ring 𝔄] [StarRing 𝔄] [Algebra ℂ 𝔄]
  (π : 𝔄 →⋆ₐ[ℂ] H →L[ℂ] H) :
  ⇑(UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s | s.Finite}) '' (Set.range ⇑π).centralizer.centralizer ⊆
    closure (⇑(UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s | s.Finite}) '' Set.range ⇑π)
```

The Kaplansky density theorem, which would also make the approximants self-adjoint, is not proved;
the argument above does not need it.

The blueprint section also develops the representation theory used here: irreducibility and
Schur's lemma, unitary equivalence and superselection, disjointness and quasi-equivalence, direct
sums and amplification, and the separating vector of a faithful state. These hold for any
C\*-algebra and are formalised in `Physicslib4/GNS/`
([Section 10.6](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html),
from "Irreducibility and Schur's Lemma"). `Purity.lean` specialises purity and irreducibility to
the quasilocal algebra.

[bp-ec]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:einstein-causality
[bp-lvn]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann
[bp-lvna]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-algebra
[bp-vn-iso]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-isotony
[bp-vn-order]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-bundled-order
[bp-si]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-bundled
[bp-dense]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-strongly-dense

## Symmetry and states

Blueprint: [def:covariant-quasilocal-algebra][bp-action], [lmm:quasilocal-lift-unique][bp-unique],
[def:invariant-state][bp-inv], [thrm:invariant-state-gns-unitary][bp-inv-gns],
[def:vacuum-state][bp-vac], [def:future-timelike-translation][bp-ftl],
[def:vacuum-state-concrete][bp-vac-c], [def:kms-state-for-flow-covariance][bp-kms],
[def:ground-state-for-flow-covariance][bp-ground].

Axiom 5 acts between local algebras. Its action on the quasilocal algebra is constructed:

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.action}

The defining property, $`\beta_L(\iota_{\mathbf{B}}a) = \iota_{L\mathbf{B}}(\alpha_L a)`, is
`action_ι`. (Lean prints the proof that $`L\mathbf{B}` is a diamond as `⋯`.)

```lean (name := checkActionι)
open Physicslib4 AQFT HaagKastler in
#check HaagKastlerNet.action_ι
```

```leanOutput checkActionι
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.action_ι.{u_1} (N : HaagKastlerNet) (L : InhomogeneousLorentzGroup)
  {B : Set StandardMinkowskiSpacetime.Carrier} (hB : IsAlexandrovBasisSet B) (a : N.U.algebra B) :
  (N.action L) ((N.quasilocal.ι hB) a) = (N.quasilocal.ι ⋯) ((N.covEquiv L B) a)
```

The property determines $`\beta_L`: two automorphisms of any quasilocal algebra that satisfy it
agree on the dense union of the local images, and are continuous.

```lean (name := checkUnique)
open Physicslib4 AQFT HaagKastler in
#check HaagKastlerNet.QuasilocalLift.unique
```

```leanOutput checkUnique
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.QuasilocalLift.unique.{u_1} {N : HaagKastlerNet}
  {Q : QuasilocalAlgebra N.U N.isotony} {L : InhomogeneousLorentzGroup} (l₁ l₂ : N.QuasilocalLift Q L) : l₁.β = l₂.β
```

As you will recall, a state on a unital C\*-algebra is a positive linear functional of norm 1; in
the library it is `Physicslib4.GNS.State A`, a continuous linear functional with
$`\omega(a^*a) \ge 0` and $`\|\omega\| = 1`. A state of the net is a state on
`N.quasilocal.carrier`.

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState}

For an invariant state, the library proves that the action is implemented by unitaries on the GNS
space, $`U(L)\pi(a)\Omega = \pi(\beta_L a)\Omega` and $`U(L)\Omega = \Omega`, forming a unitary
representation of the group
({apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState.exists_gns_unitaryRep}[`IsInvariantState.exists_gns_unitaryRep`]).
The representation is strongly continuous when the matrix coefficients
$`L \mapsto \omega(a^*\beta_L b)` are continuous
({apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState.exists_gns_unitaryRep_strongContinuous}[`IsInvariantState.exists_gns_unitaryRep_strongContinuous`]),
and irreducible when $`\omega` is also pure
({apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState.exists_gns_irreducible_covariant}[`IsInvariantState.exists_gns_irreducible_covariant`]).
These statements are long existentials over the Hilbert space and its structure, so they are linked
rather than printed.

A vacuum state adds the spectrum condition. The library states it as positive energy along every
future-timelike translation: the unitary group $`t \mapsto U(\gamma(t))` is strongly continuous and
its generator is a positive operator (`Physicslib4.AQFT.IsPositiveEnergy`). By Stone's theorem,
proved in the library, this says $`U(\gamma(t)) = e^{itA}` with $`A` positive and self-adjoint.

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumState}

{docstring Physicslib4.AQFT.HaagKastler.IsFutureTimelikeTranslation}

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumStateConcrete}

The library proves the consequences of a vacuum state that do not use the spectrum condition: it is
invariant (`HaagKastlerNet.IsVacuumState.invariant`), and if it is pure its GNS representation is
covariant and irreducible
({apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumState.exists_gns_irreducible_covariant}[`IsVacuumState.exists_gns_irreducible_covariant`]).
It does not construct a vacuum state of a nontrivial net, and it does not prove the Reeh–Schlieder
theorem.

Thermal equilibrium is described by KMS states. In Minkowski spacetime every Poincaré
transformation acts on the one algebra $`\mathfrak{U}`, so a one-parameter subgroup $`t \mapsto
L_t`, such as the time translations, defines dynamics on it:

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.flowAut}

```lean (name := checkFlowAut)
open Physicslib4 AQFT HaagKastler in
#check HaagKastlerNet.isOneParameterAut_flowAut
```

```leanOutput checkFlowAut
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.isOneParameterAut_flowAut.{u_1} (N : HaagKastlerNet)
  (flow : ℝ → InhomogeneousLorentzGroup) (h0 : flow 0 = 1) (hadd : ∀ (s t : ℝ), flow (s + t) = flow s * flow t) :
  IsOneParameterAut (N.flowAut flow)
```

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsKMSStateForFlow}

The KMS states for a flow at a given temperature form a convex set:

```lean (name := checkKMSConvex)
open Physicslib4 AQFT HaagKastler in
#check HaagKastlerNet.IsKMSStateForFlow.convexCombo
```

```leanOutput checkKMSConvex
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsKMSStateForFlow.convexCombo.{u_1} (N : HaagKastlerNet)
  (flow : ℝ → InhomogeneousLorentzGroup) {β : ℝ} {ω₁ ω₂ : GNS.State N.quasilocal.carrier} (s : ℝ) (hs0 : 0 ≤ s)
  (hs1 : s ≤ 1) (h₁ : N.IsKMSStateForFlow flow β ω₁) (h₂ : N.IsKMSStateForFlow flow β ω₂) :
  N.IsKMSStateForFlow flow β (ω₁.convexCombo ω₂ s hs0 hs1)
```

The general theory of the KMS condition, including the invariance of a KMS state under its
dynamics at positive inverse temperature, is in `Physicslib4/AQFT/KMS.lean`
({apiDocs Physicslib4.AQFT.IsKMSState}[]). At zero temperature the counterpart is a ground state:

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsGroundStateForFlow}

[bp-action]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-quasilocal-algebra
[bp-unique]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-lift-unique
[bp-inv]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:invariant-state
[bp-inv-gns]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:invariant-state-gns-unitary
[bp-vac]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:vacuum-state
[bp-ftl]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-timelike-translation
[bp-vac-c]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:vacuum-state-concrete
[bp-kms]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state-for-flow-covariance
[bp-ground]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:ground-state-for-flow-covariance

# Where to look
%%%
tag := "haag-kastler-files"
%%%

The Minkowski axioms and their consequences are in `Physicslib4/AQFT/HaagKastler/`, one topic per
file. Each entry links to the API documentation of a representative declaration, from which the
rest of the file can be browsed.

The axioms:

* `LocalAlgebras.lean`: diamonds and Axiom 1,
  {apiDocs Physicslib4.AQFT.HaagKastler.LocalNet}[].
* `Isotony.lean`: Axiom 2, {apiDocs Physicslib4.AQFT.HaagKastler.Isotony}[].
* `LocalCommutativity.lean`: Axiom 3 and its quasilocal forms,
  {apiDocs Physicslib4.AQFT.HaagKastler.LocalCommutativity}[].
* `LorentzCovariance.lean`: the group and its action on spacetime,
  {apiDocs Physicslib4.AQFT.HaagKastler.InhomogeneousLorentzGroup}[].
* `LorentzCovarianceAxiom.lean`: Axiom 5,
  {apiDocs Physicslib4.AQFT.HaagKastler.LorentzCovariance}[].
* `Net.lean`: the bundled net, its chosen quasilocal algebra and covariance maps, and the trivial
  net, {apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet}[].
* `ObservableBridge.lean`: Axiom 4,
  {apiDocs Physicslib4.AQFT.HaagKastler.ObservableCorrespondence}[].

The quasilocal algebra:

* `QuasilocalAlgebra.lean`: the interface,
  {apiDocs Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra}[].
* `QuasilocalColimit.lean`: the directed colimit, its norm and its completion,
  {apiDocs Physicslib4.AQFT.HaagKastler.QuasilocalCompletion}[]; the completion of a normed
  \*-algebra is in `Physicslib4/Analysis/CStarCompletion.lean`.
* `QuasilocalExistence.lean`: existence,
  {apiDocs Physicslib4.AQFT.HaagKastler.exists_quasilocalAlgebra}[].
* `QuasilocalObservable.lean`: quasilocal observables,
  {apiDocs Physicslib4.AQFT.HaagKastler.IsQuasilocalObservable}[].
* `QuasilocalAction.lean` and `QuasilocalIntertwiner.lean`: the action $`\beta_L`, invariant states
  and their GNS unitaries, {apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.action}[].

Representations:

* `EinsteinCausality.lean`: {apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.einstein_causality}[`einstein_causality`].
* `LocalVonNeumann.lean`: local von Neumann algebras, microcausality, the Schlieder property,
  relative commutants, {apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra}[`localVonNeumannAlgebra`].
* `GeometricCovariance.lean`: the action on the local von Neumann algebras,
  {apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.lieConj_image_localVonNeumann}[`lieConj_image_localVonNeumann`].
* `StrongDensity.lean`: the density theorem,
  {apiDocs Physicslib4.AQFT.HaagKastler.dense_range_in_bicommutant}[]; its operator-theoretic core is
  in `Physicslib4/Operators/DensityTheorem.lean`.
* `Purity.lean`: pure states of the quasilocal algebra and irreducibility,
  {apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.pure_iff_extreme}[].

States:

* `CovariantState.lean`: covariant families of local states,
  {apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsCovariantFamily}[`IsCovariantFamily`].
* `VacuumState.lean`: {apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumState}[]; positive
  energy is in `Physicslib4/AQFT/PositiveEnergy.lean`.
* `QuasilocalKMS.lean`: {apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsKMSStateForFlow}[`IsKMSStateForFlow`]; the
  KMS condition itself is in `Physicslib4/AQFT/KMS.lean`.

Elsewhere in the library, the facts about Minkowski spacetime that the axioms rely on are
`Physicslib4/Spacetime/MinkowskiDirected.lean`, where two diamonds lie in a common diamond
({apiDocs Physicslib4.Spacetime.alexandrovBasis_directed}[]), and
`Physicslib4/Spacetime/LorentzCausality.lean`, where the Poincaré group maps diamonds to diamonds
({apiDocs Physicslib4.isAlexandrovBasisSet_smul}[]). The GNS construction and the theory of
representations are in `Physicslib4/GNS/`.

The blueprint section is
[Section 10.6](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html),
and the [section page](https://physicslib.github.io/physicslib4/sec10-6-haag-kastler.html) lists
each of its entries with the Lean declaration that formalises it.
