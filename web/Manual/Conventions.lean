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
time-translation unitaries of a field theory are the inverse of that evolution,
$`U(t) = e^{it\hat H}`, so their generator is $`\hat H` itself, and the spectrum condition,
stated as positive energy, says $`\hat H \ge 0`. The
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
does, so that one definition serves every spacetime. $`p \ll q` and `IsCausalTrip t p q` are
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
the global algebra is assumed or built. The library settles each the same way in Minkowski and in
curved spacetime, so that the Minkowski axioms read as a special case.

_Regions are diamonds._ Algebras are attached to the chronological diamonds
$`I^+(p) \cap I^-(q)`, the basic open sets of the Alexandrov topology, and the empty set counts
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

_KMS states and flows act on diamonds._ In Minkowski spacetime a one-parameter subgroup of the
Poincaré group acts on the quasilocal algebra, and KMS and ground states are states of that
algebra. In curved spacetime there is no such algebra, so a flow is a curve
$`t \mapsto \varphi_t` in the stabiliser $`\mathrm{Stab}(\mathbf{B})` of a region, acting on
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

This section is in preparation.

# Implementation choices
%%%
tag := "conventions-implementation"
%%%

This section is in preparation.
