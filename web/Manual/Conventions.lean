import VersoManual
import Book.Meta
import Physicslib4.Spacetime.Causality

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

#doc (Manual) "Conventions and design decisions" =>

%%%
tag := "conventions"
file := "Conventions-and-design-decisions"
%%%

The other chapters each meet a few of the library's conventions and design decisions where they
arise. This chapter collects them: it states each one once, says why it is made, and links to the
places where it matters. A reader who knows algebraic quantum field theory but not this library
may read it first or second.

# How the blueprint and the Lean fit together
%%%
tag := "conventions-blueprint"
%%%

_The blueprint is the specification._ Its chapters 1 to 9 unpack the 1964 Haag–Kastler axioms one
at a time and argue for each sharpening; they are context and are not formalised. Chapter 10
states the sharpened definitions and theorems in a form ready for formalisation, and the library
formalises Chapter 10 only. A Lean statement is therefore checked against its Chapter 10 entry,
not against the 1964 paper, and where the two differ the blueprint says why. The
[guide to the blueprint](https://physicslib.github.io/physicslib4/guide.html) describes how the
chapters are organised.

_Labels and annotations._ Every entry of Chapter 10 has a label, such as `def:isotony` or
`thrm:hall-10.15`, which is also its anchor in the web blueprint. Three annotations tie the entry
to the Lean:

* `\lean{…}` names the declarations that formalise it, Mathlib's own where Mathlib already has
  the result;
* `\leanok` in the statement marks the statement as formalised, and in the proof the proof;
* `\uses{…}` lists the entries it depends on, from which the dependency graph is drawn.

`leanblueprint checkdecls` checks that every name in a `\lean{…}` exists. The link runs the other
way too: a library docstring carries a line such as `Blueprint: def:isotony` naming its entry.
The section pages, such as the one for
[Section 10.5](https://physicslib.github.io/physicslib4/sec10-5-spacetime.html), list every entry
with the declaration that formalises it, and each chapter of this manual opens its subsections
with the entries they cover.

_Formalization notes._ Where a Lean proof takes a different route from the blueprint's, the entry
says so in a paragraph headed "Formalization note". For example, the existence half of the GNS
theorem uses Mathlib's GNS space instead of the blueprint's quotient construction
([thrm:gns-construction-theorem](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-construction-theorem)),
and the continuous functional calculus is Mathlib's `cfcHom` instead of an extension from
polynomials
([prpstn:hall-8.3](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.3)).
The statement is unchanged; only the proof differs. Lean-specific encodings that the blueprint
does not discuss are explained in the docstrings, in paragraphs headed "Implementation note".

_Restrictions._ When a declaration is deliberately less general than its intended form, for
instance by requiring a bounded generator where the intended form allows an unbounded one, its
docstring says so on a line beginning `**Restriction:**`, which names the intended form and what it
waits on. The library has no such line: every declaration has the generality of its blueprint
entry. A choice of encoding that yields the intended object, such as the group of Axiom 5 in curved
spacetime, is an implementation choice, not a restriction.

_Present tense._ The blueprint, the docstrings and this manual describe the library as it is, in
the present tense. Its history is kept in one place, `CHANGELOG.md` at the root of the
repository.

_Where the library stops._ The standard facts that the library does not prove, such as the
Reeh–Schlieder theorem and the existence of pure states, are marked where they arise and collected
in the {ref "not-proved"}[appendix]. Where a theorem depends on one of them, it is a hypothesis of
that theorem.

# Sign and notational conventions
%%%
tag := "conventions-signs"
%%%

_The metric has signature $`(-,+,+,+)`._ A spacetime metric has, at every point, a basis in which
it is $`\mathrm{diag}(-1,1,1,1)`, and standard Minkowski space carries the constant metric
$`\eta = \mathrm{diag}(-1,1,1,1)`
([def:spacetime](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacetime)).
So a tangent vector $`v` is timelike when $`g(v,v) < 0`, spacelike when $`g(v,v) > 0`, and null
when $`g(v,v) = 0`; the zero vector counts as null. Units have $`\hbar = c = 1`.

_Inner products are linear in the second argument._ As you will recall, this is the physicists'
convention, and it is also Mathlib's: $`\langle \lambda\varphi, \psi \rangle =
\bar\lambda\langle \varphi, \psi \rangle`.

_A generator carries a factor $`1/i`._ The infinitesimal generator of a one-parameter unitary
group $`U` is

$$`A\psi = \lim_{t \to 0,\ t \neq 0} \frac{1}{i}\,\frac{U(t)\psi - \psi}{t},`

so that $`U(t) = e^{itA}` in Stone's theorem
([def:hall-10.13](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.13)).
With this sign the Schrödinger evolution $`e^{-it\hat H}` has generator $`-\hat H`. The
translation unitaries of a field theory are $`U(a) = e^{-iP\cdot a}`, where
$`P\cdot a = -P^0 a^0 + \vec P\cdot\vec a` is the pairing of signature $`(-,+,+,+)` and
$`P^0 = \hat H`. For a time translation $`a = (t, \vec 0)` this gives $`U(t) = e^{it\hat H}`, the
inverse of the Schrödinger evolution, so its generator is $`\hat H` itself. The spectrum
condition is stated as positive energy along every future-timelike translation
$`t \mapsto U(tn)`, whose generator is $`P^0 n^0 - \vec P\cdot\vec n`; for time translations it
says $`\hat H \ge 0`. The
[Stone chapter](Stones-theorem/#physicslib4-reference-manual--Stone___s-theorem--Design--Positive-energy-is-a-property-of-the-generator)
explains how positive energy is imposed on the generator directly, without assuming it bounded.

_Notation shared by the blueprint and the Lean._ The manual uses the blueprint's symbols, and the
library's names correspond to them as follows.

* $`\mathfrak{U}(\mathbf{B})`, the algebra of a region $`\mathbf{B}`, is `U.algebra B` for a
  Minkowski net `U` and `N.algebra B` for a curved one; $`\mathfrak{U}` alone is the quasilocal
  algebra, with embeddings $`\iota_{\mathbf{B}}`, written `Q.ι hB`.
* $`i_{\mathbf{B}_1\mathbf{B}_2}`, the isotony map for $`\mathbf{B}_1 \subseteq \mathbf{B}_2`,
  is `i.map hB₁ hB₂ h`, and the covariance maps $`\alpha_L` are `covEquiv`.
* $`p \ll q` (chronological precedence) and $`p \prec q` (causal precedence) are
  `ChronologicallyPrecedes M t p q` and `CausallyPrecedes M t p q`, with the notation
  `p ≪[M, t] q` and `p ≺[M, t] q`, scoped to the namespace `Physicslib4.Spacetime`. The time
  orientation `t` is always explicit.
* $`I^\pm(p)` and $`J^\pm(p)` are `chronologicalFuture`, `chronologicalPast`, `causalFuture` and
  `causalPast`, and $`\mathbf{B}^\perp` is `spacelikeComplement`.

The {ref "spacetime-main"}[Spacetime chapter] prints these declarations in full.

# Causal structure
%%%
tag := "conventions-causal"
%%%

_Causal precedence is reflexive._ On Minkowski space $`p \prec q` could be defined by vectors,
$`q - p` causal and future-directed or zero. The library defines it by curves, as the blueprint
does, so that one definition serves every spacetime. $`p \ll q` and `M.IsCausalTrip t p q` are
chains of _one or more_ future-oriented timelike or causal geodesic segments, the transitive
closure `Relation.TransGen` of single-segment precedence; $`p \prec q` is a chain of _zero or more_
causal segments, the reflexive-transitive closure `Relation.ReflTransGen`. So $`\prec` is
reflexive while `IsCausalTrip` is strict, and the two are related by

```lean (name := checkEqOr)
open Physicslib4 Spacetime in
#check causallyPrecedes_iff_eq_or_isCausalTrip
```

```leanOutput checkEqOr
Physicslib4.Spacetime.causallyPrecedes_iff_eq_or_isCausalTrip (M : Spacetime) (t : M.TimeOrientation)
  {p q : M.Carrier} : (p ≺[M, t] q) ↔ p = q ∨ M.IsCausalTrip t p q
```

This is the convention of Hawking and Ellis, $`p \in J^+(p)`
([def:causal-trip](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-trip)).
Three consequences are worth knowing.

* $`p \in J^\pm(p)` for every $`p`, and transitivity is free: concatenating two chains gives a
  chain, so `causallyPrecedes_trans` is `Relation.ReflTransGen.trans`.
* No point is spacelike to itself (`isSpacelikeRelated_irrefl`), so a region and its spacelike
  complement are disjoint, and the causal complement is an orthocomplement on the causally
  complete regions.
* The causality condition `NoClosedCausalCurve` is stated with the strict relation, as "no causal
  trip from $`p` to $`p`"; stated as $`\lnot(p \prec p)` it would fail in every spacetime. Under
  it $`\prec` is a partial order
  ([def:no-closed-causal-curve](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:no-closed-causal-curve)).

_Paths have nowhere-vanishing velocity._ A smooth path has $`\dot\mu(s) \neq 0` at every
parameter, endpoints included, so a null path moves along the light cone instead of resting at a
point. Constant curves are excluded, and the trivial case $`p = q` of $`\prec` takes the place a
degenerate causal curve would otherwise fill
([def:paths](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:paths)).

_The intersection property is a hypothesis._ The Alexandrov topology is generated by the
chronological diamonds $`I^+(p) \cap I^-(q)`, so the diamonds are a subbasis by construction. They
form a _basis_ when every point in the intersection of two diamonds lies in a diamond inside that
intersection. In the standard theory this holds in every spacetime, since chronological futures
are open in the manifold topology; the library does not prove it, so the basis theorem
`LorentzianSpacetime.isTopologicalBasis_alexandrovBasis` takes it as the hypothesis `hdir`
([thrm:alexandrov-topological-basis](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:alexandrov-topological-basis)).
On standard Minkowski space it is proved, and the diamonds form a basis unconditionally. The
intersection property is not the _upward_ directedness of the diamonds, that any two lie in a
common diamond, which the quasilocal algebra needs and which can fail in a curved spacetime; the
[Spacetime chapter](Spacetime-and-geometry/#physicslib4-reference-manual--Spacetime-and-geometry--Design--Diamonds___-and-when-they-form-a-basis)
sets the two side by side.

_Smooth means $`C^\infty`, not $`C^\omega`._ Mathlib's `ContMDiff` takes its regularity index in
$`\mathbb{N} \cup \{\infty, \omega\}`, where the top element $`\omega` means real-analytic and
$`\infty` is strictly smaller. A spacetime is a $`C^\infty` manifold, `IsManifold model ∞ Carrier`,
and its metric is a $`C^\infty` section with the index $`\infty`, so the Lean agrees with the
informal word "smooth"; asking for the top index would demand analyticity
([def:spacetime](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacetime),
the remark on the index).

# The axiom structures
%%%
tag := "conventions-axioms"
%%%

As you will recall, the 1964 axioms leave several points open: which regions carry algebras, what
"inclusion" of abstract algebras means, where two local observables are multiplied, and whether
the global algebra is assumed or built. The library settles them in parallel in Minkowski and in
curved spacetime, so that the Minkowski axioms read as a special case; where the two differ, the
paragraph says so.

_Regions are diamonds._ Algebras are attached to the chronological diamonds
$`I^+(p) \cap I^-(q)`, the sets that generate the Alexandrov topology, and the empty set counts
as a diamond, with $`\mathfrak{U}(\emptyset) = \mathbb{C}\mathbf{1}`. The field `algebra` is a
function on all subsets, but every axiom takes a proof that its regions are diamonds and constrains
nothing else
([Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Design--Regions-are-causal-diamonds)).

_Isotony is data._ `Isotony` is a structure, not a proposition: it carries the unital
\*-monomorphisms $`i_{\mathbf{B}_1\mathbf{B}_2}` together with the laws
$`i_{\mathbf{B}\mathbf{B}} = \mathrm{id}` and
$`i_{\mathbf{B}_2\mathbf{B}_3} \circ i_{\mathbf{B}_1\mathbf{B}_2} = i_{\mathbf{B}_1\mathbf{B}_3}`,
which an existence statement could not express. Every later axiom takes the net's one isotony
family as a parameter
([def:isotony](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony)).

_Axiom 3 holds in a common diamond._ Observables of two completely spacelike diamonds
$`\mathbf{B}_1, \mathbf{B}_2` are compared in the algebra of every diamond $`\mathbf{B}` containing
both: their images under $`i_{\mathbf{B}_1\mathbf{B}}` and $`i_{\mathbf{B}_2\mathbf{B}}` commute.
In Minkowski spacetime a containing diamond always exists, and the axiom is equivalent to
commutation in the quasilocal algebra (`localCommutativity_iff_exists_commute_ι`). In curved
spacetime the same statement is the axiom, and it is vacuous for a pair that lies in no common
diamond
([def:local-commutativity](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity),
[def:local-commutativity-in-curved-spacetime](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity-in-curved-spacetime)).

_The quasilocal algebra is constructed, in Minkowski spacetime only._ For a Minkowski net it is
the completion of the directed colimit of the local algebras along the isotony maps, and every
net satisfying Axiom 2 has one (`exists_quasilocalAlgebra`); the rest of the library sees it only
through the interface `QuasilocalAlgebra`. In curved spacetime two diamonds need not lie in a
common diamond, and the blueprint argues, with a Schwarzschild example, that a quasilocal algebra
need not exist; the library does not formalise that argument. It states the curved results inside
the algebra $`\mathfrak{U}(\mathbf{B})` of one containing diamond instead
([curved chapter](The-axioms-in-curved-spacetime-and-general-covariance/#physicslib4-reference-manual--The-axioms-in-curved-spacetime-and-general-covariance--Design--Local-commutativity-without-a-quasilocal-algebra)).

_Covariance is under the identity component._ Axiom 5 asks for an action only of the symmetries
connected to the identity, so a theory need not be invariant under parity or time reversal. In
Minkowski spacetime the group is `InhomogeneousLorentzGroup`, the pairs $`(\Lambda, a)` with
$`\Lambda` proper and orthochronous. In curved spacetime it is the isometries connected to the
identity, encoded as the oriented identity component, which is discussed in the
{ref "conventions-implementation"}[implementation choices] below.

_In curved spacetime, KMS states and flows act on diamonds._ In Minkowski spacetime a one-parameter subgroup of the
Poincaré group acts on the quasilocal algebra, and KMS and ground states are states of that
algebra. In curved spacetime a quasilocal algebra need not exist, and the library constructs
none, so a flow is a curve $`t \mapsto \varphi_t` in the stabiliser $`\mathrm{Stab}(\mathbf{B})` of a region, acting on
$`\mathfrak{U}(\mathbf{B})`
([def:kms-state-for-flow-in-curved-spacetime](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state-for-flow-in-curved-spacetime)).
The examples that motivate these definitions, the stationary flow of a black-hole exterior and the
boost of a de Sitter static patch, are not instances of them: those regions are not diamonds, and
no such Killing flow fixes a nonempty diamond, so the axioms place no constraint on their
algebras. The library keeps it that way deliberately, so that the definitions stay with the
regions the axioms govern
([curved chapter](The-axioms-in-curved-spacetime-and-general-covariance/#physicslib4-reference-manual--The-axioms-in-curved-spacetime-and-general-covariance--Design--Isometric-covariance-and-stabilisers)).

# Universes
%%%
tag := "conventions-universes"
%%%

As you will recall from the
[tutorial](../tutorial/Lean-in-brief/#physicslib4-tutorial--Lean-in-brief--Structures-and-type-classes--An-aside-on-universes),
every Lean type lives in a universe, `Type 0 = Type`, `Type 1`, and so on, and a definition that
quantifies over types must say in which universe they lie. Physics never notices universes, but a
statement of the form "there is a Hilbert space with …" or "for every Hilbert space …" has to fix
one. The library makes four choices.

_GNS Hilbert spaces live in the universe of the algebra._ `gns_construction` asserts, for a state
on a C\*-algebra `A : Type u`, the existence of a GNS triple whose Hilbert space is in `Type u`,
because Mathlib's GNS space of `A` lives there. An existential needs some fixed universe, and this
is the one in which the construction can be carried out. Uniqueness, `gns_unique`, compares two
Hilbert spaces in arbitrary universes. Every later existential over a GNS space inherits the
choice: the unitary implementation of a symmetry on the GNS space of a Minkowski net's quasilocal
algebra, for example, yields a Hilbert space in the universe of that algebra
([GNS chapter](The-GNS-construction/#physicslib4-reference-manual--The-GNS-construction--Design--The-construction-uses-Mathlib___s-GNS-space)).

_A Minkowski net has one universe, that of its algebras._ `LocalNet.{u}` assigns local algebras in
`Type u` to subsets of $`\mathbb{R}^4`, which is in `Type`. A quasilocal algebra of the net has its
carrier in the same universe `Type u`: a smaller universe could not hold injective copies of the
local algebras, and a free universe could not be inferred. `HaagKastlerNet` names the universe of
its net, so it is a parameter
([Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Design--Universes)).

_A curved net's algebras have their own universe._ The spacetime interface
`HaagKastlerCurved.LorentzianSpacetime.{u}` has its points and its isometries in `Type u`. A net
over it, `LocalNet.{u, v} M` or `HaagKastlerNet.{u, v} M`, has its algebras in `Type v`,
independent of `u`, so a spacetime in any universe can carry algebras in any universe. The Hilbert
spaces that Axiom 4 quantifies over range over `Type v`, where `gns_construction` puts the GNS
spaces of states on the local algebras. A geometric spacetime enters through
`toAbstractIdentityComponent`, which produces an interface with points in `Type`, and a
`NetTheory` assigns to every geometric spacetime a net whose algebras are all in one universe, the
universe parameter of `NetTheory`
([curved chapter](The-axioms-in-curved-spacetime-and-general-covariance/#physicslib4-reference-manual--The-axioms-in-curved-spacetime-and-general-covariance--Design--Local-algebras___-parallel-to-Minkowski)).

_The trivial nets are in universe 0._ They assign $`\mathbb{C}` to every region, and
$`\mathbb{C}` is in `Type`. The consistency theorems are therefore stated at universe 0:
`HaagKastler.nonempty_haagKastlerNet` for `HaagKastlerNet.{0}` and
`HaagKastlerCurved.nonempty_haagKastlerNet` for algebras in universe 0 over a spacetime in any
universe. Consistency needs one model, so nothing is lost; the library gives no witness in other
universes.

_For a reader writing a net._ The algebras of physics, $`\mathbb{C}`, matrix algebras, the
bounded operators on a Hilbert space `H : Type`, are in `Type`, so a net built from them has
`u = 0` in Minkowski spacetime and `v = 0` in curved spacetime. Every general theorem of the library is universe-polymorphic and applies to it
unchanged. Universe annotations matter only when a statement mixes objects from different
universes: a Hilbert space obtained from a GNS existential is in the universe of the algebra, and
a hypothesis about "every Hilbert space" in Axiom 4 of a curved net means every Hilbert space in
the universe of its algebras.

# Implementation choices
%%%
tag := "conventions-implementation"
%%%

Some choices concern only how an intended object is encoded. They do not change what the library
states, but they show up when reading or using the Lean.

## The group of the curved-spacetime Axiom 5

The blueprint's Axiom 5 in curved spacetime asks for an action of the isometries connected to the
identity, and these must map diamonds to diamonds. An isometry preserves the causal type of
vectors, but one that reverses the time orientation maps $`I^+(p)` onto $`I^-(\varphi(p))`. The
library therefore takes the group to be `Isometry.orientedIdentityComponent`: the isometries in
the identity component of the isometry group (with the topology induced by
$`\varphi \mapsto (\varphi, \varphi^{-1})` into $`C(M,M) \times C(M,M)`, compact-open on each
factor) that, with their inverses, preserve the future orientation. Its members map diamonds to
diamonds, which is the one law the spacetime interface requires.

This is an implementation choice, not a restriction. An isometry connected to the identity
preserves the future orientation, so the oriented identity component is the whole identity
component, and the group is the one the axiom names. The proof of that equality needs a
Myers–Steenrod-type rigidity theorem, which Mathlib does not provide, so the library puts
orientation preservation into the definition instead of proving it, and no `**Restriction:**`
line is needed
([def:isometric-covariance-in-curved-spacetime](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isometric-covariance-in-curved-spacetime),
formalization note; the
[Spacetime chapter](Spacetime-and-geometry/#physicslib4-reference-manual--Spacetime-and-geometry--Design--Symmetries)
and the
[curved chapter](The-axioms-in-curved-spacetime-and-general-covariance/#physicslib4-reference-manual--The-axioms-in-curved-spacetime-and-general-covariance--Design--The-bridge-from-a-geometric-spacetime)).

## Conventions inherited from Mathlib

Where Mathlib has a notion, the library uses it, together with its conventions. Several of them
differ from the textbook in how they treat degenerate cases. Lean functions are total, so Mathlib
gives a definition a value, often $`0`, where the textbook leaves it undefined, and the theorems
carry the hypothesis that excludes the degenerate case. One such convention is Lean's
$`0^{-1} = 0`.

* _Unbounded operators are partial linear maps._ An unbounded operator is Mathlib's `LinearPMap`,
  written `H →ₗ.[ℂ] H`: a domain submodule with a linear map on it. Equality of partial maps
  includes equality of domains, so $`T^* = T` means what it should. Density of the domain is the
  separate predicate `HasDenseDomain`, not part of the type
  ([unbounded chapter](Unbounded-operators-and-their-spectral-theorem/#physicslib4-reference-manual--Unbounded-operators-and-their-spectral-theorem--Design--Unbounded-operators-are-Mathlib___s-partial-linear-maps)).
* _The adjoint is defined for every operator._ Mathlib's `LinearPMap.adjoint` exists even when
  the domain of $`T` is not dense; it then keeps its natural domain but is the zero map on it. The
  textbook adjoint exists only for densely defined operators, so every theorem about the action of
  $`T^*` assumes `HasDenseDomain T`. Self-adjointness is Mathlib's `IsSelfAdjoint` and implies a
  dense domain
  ([unbounded chapter](Unbounded-operators-and-their-spectral-theorem/#physicslib4-reference-manual--Unbounded-operators-and-their-spectral-theorem--Design--The-adjoint-is-Mathlib___s___-with-its-convention)).
* _The integral of an unbounded function is guarded._ `integralApply μ f`, the action of
  $`\int f \, d\mu` for a possibly unbounded $`f`, is chosen from an existence-and-uniqueness
  statement and is $`0` when $`f` is not measurable or no unique value exists. The guard makes
  `pmapIntegral μ f` a partial linear map for every $`f`; theorems about its values assume
  `Measurable f`
  ([unbounded chapter](Unbounded-operators-and-their-spectral-theorem/#physicslib4-reference-manual--Unbounded-operators-and-their-spectral-theorem--Design--The-integral-of-an-unbounded-function)).
* _The zero representation is irreducible._ `IsIrreducible π` is the commutant form, every
  operator commuting with all $`\pi(a)` is a multiple of $`\mathbf{1}`, as in the blueprint. On
  the zero Hilbert space every operator is $`0 = 0 \cdot \mathbf{1}`, so the zero representation
  counts as irreducible. The library keeps the definition as it is: results that need a nonzero
  space assume `Nontrivial H` or a nonzero vector, and a GNS space is never zero, since
  $`\|\Omega\|^2 = \omega(\mathbf{1}) = 1`
  ([GNS chapter](The-GNS-construction/#physicslib4-reference-manual--The-GNS-construction--Design--Irreducibility___-purity-and-the-commutant)).
* _The continuous functional calculus is Mathlib's._ `realCalculus hA` is Mathlib's `cfcHom hA`,
  constructed independently of the blueprint's route through polynomials. The library adds the
  blueprint's characterisation, that it is the unique bounded linear map sending each polynomial
  $`p` to $`p(A)`
  ([bounded chapter](Bounded-spectral-theory/#physicslib4-reference-manual--Bounded-spectral-theory--Design--The-continuous-calculus-is-Mathlib___s)).
* _The GNS construction is Mathlib's._ The existence half of the GNS theorem uses Mathlib's GNS
  space of a positive functional, `PositiveLinearMap.GNS`, with its left-multiplication
  representation, instead of the blueprint's quotient-and-complete construction; the blueprint's
  lemmas on the null space are formalised separately
  ([GNS chapter](The-GNS-construction/#physicslib4-reference-manual--The-GNS-construction--Design--The-construction-uses-Mathlib___s-GNS-space)).
