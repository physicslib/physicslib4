import VersoManual
import Book.Meta
import Physicslib4.GNS.Construction
import Physicslib4.GNS.NullSpace
import Physicslib4.GNS.CauchySchwarz
import Physicslib4.GNS.Separating
import Physicslib4.GNS.ExtremeState
import Physicslib4.GNS.PureStateExists
import Physicslib4.GNS.Superselection
import Physicslib4.GNS.Amplification
import Physicslib4.GNS.Covariance
import Physicslib4.GNS.UnitaryRepresentation
-- Imported only so that names in the docstrings shown below resolve and link.
import Physicslib4.Operators.DensityTheorem

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book
-- Docstring code spans are elaborated in this scope; these namespaces let the names they mention,
-- written relative to the library's namespaces, resolve and link.
open Physicslib4 Physicslib4.GNS

#doc (Manual) "The GNS construction" =>

%%%
tag := "gns"
file := "The-GNS-construction"
%%%

This chapter describes how the library encodes states on a C\*-algebra, the GNS construction, and
the representation theory built on it. It corresponds to
[Section 10.1](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:gns-construction-details)
of the blueprint, which states and proves the GNS theorem, and to the subsections of
[Section 10.6](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:haag-kastler-axioms)
that develop representation theory, mostly for an arbitrary C\*-algebra: "Irreducibility and Schur's
Lemma" to "Direct Sums, Amplification, and Reducibility", and "The Separating Vector of a Faithful
State". The physics is introduced in
[chapter 1 of the tutorial](../tutorial/AQFT-in-brief/#physicslib4-tutorial--AQFT-in-brief--States-and-the-GNS-construction),
and [chapter 3](../tutorial/Worked-examples/#worked-examples-gns) builds the one state of
$`\mathbb{C}` and runs the GNS construction on it; this chapter assumes both.

# Overview
%%%
tag := "gns-overview"
%%%

As you will recall, a state $`\omega` on a unital C\*-algebra $`A` is a positive, normalised linear
functional, and the GNS construction turns it into a Hilbert space $`H`, a representation $`\pi` of
$`A` on $`H` and a cyclic vector $`\Omega` with

$$`\omega(a) = \langle \Omega, \pi(a)\,\Omega \rangle \qquad\text{for all } a \in A.`

Everything in this chapter is stated for abstract unital C\*-algebras, Mathlib's `CStarAlgebra`. The
{ref "haag-kastler"}[Haag–Kastler chapter] applies it to the
quasilocal algebra $`\mathfrak{U}` and to the local algebras $`\mathfrak{U}(\mathbf{B})`. The
chapter has five parts.

* _States._ `State A` is a continuous linear functional with positivity and normalisation;
  faithfulness is a property of a state. The Cauchy–Schwarz inequality and the null space
  $`N(\omega)` are the blueprint's lemmas for the construction.
* _The construction._ `gns_construction` gives the triple, with $`\pi` injective for a faithful
  state, and `gns_unique` its uniqueness up to unitary equivalence. A vector reproducing a faithful
  state is separating.
* _Irreducibility and purity._ Irreducibility in the commutant form, purity by domination and as
  extremality, the von Neumann algebras $`\pi(A)''` and $`\pi(A)'`, and the centre.
* _Comparing representations._ Unitary equivalence, intertwiners, disjointness and
  quasi-equivalence, which describe superselection sectors; direct sums and amplification.
* _Covariance._ Pulling states back along \*-homomorphisms, the GNS representation of a pulled-back
  state, and the unitary implementation of a symmetry that leaves a state invariant.

From these the library proves, among other things:

* the GNS construction, and its uniqueness with a unitary that maps cyclic vector to cyclic vector;
* the Cauchy–Schwarz inequality for positive functionals, and that $`N(\omega)` is a closed
  subspace;
* $`\omega` is pure if and only if its GNS representation is irreducible, if and only if $`\omega`
  is an extreme point of the state space; $`\pi` is irreducible if and only if
  $`\pi(A)' = \mathbb{C}\mathbf{1}`, if and only if $`\pi(A)'' = B(H)`;
* two irreducible representations are disjoint or unitarily equivalent; unitary equivalence
  implies quasi-equivalence; a direct sum of two nonzero representations is reducible;
* the state space is weak-\* compact;
* along a \*-isomorphism $`\Phi`, the GNS representation of $`\omega \circ \Phi` is that of
  $`\omega` composed with $`\Phi`, up to unitary equivalence, and purity is preserved;
* a symmetry that leaves $`\omega` invariant is implemented by a unitary representation on the GNS
  space, which is strongly continuous when the matrix coefficients are continuous.

Two standard results are not proved: the existence of pure states, and the quasi-equivalence of a
representation with its amplification. The declarations are in the namespace `Physicslib4.GNS`,
written below without the prefix.

# Design
%%%
tag := "gns-design"
%%%

The blueprint is the specification, and its entries record the reasons for the choices below.

## States are a structure

Mathlib has positive linear maps and a GNS construction for them, but no type of states. The
library's `State A` is a structure that extends `A →L[ℂ] ℂ` with two fields, as in the blueprint's
[def:state](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:state):
positivity, $`0 \le \omega(a^*a)`, and normalisation, $`\|\omega\| = 1`. The familiar
$`\omega(\mathbf{1}) = 1` is a theorem (`State.apply_one`), from $`\|\varphi\| = \mathrm{Re}\,\varphi(\mathbf{1})`
for a positive functional (`norm_eq_re_apply_one_of_positive`). Continuity is part of the data,
so that the operator norm is defined; for a positive functional on a C\*-algebra it would be
automatic.

Properties of a state are predicates on it (`State.IsFaithful`, `IsPure`,
`State.IsExtremePoint`), and operations on states are functions that return a state, with the
proof of positivity and normalisation inside (`State.comp`, `State.precomp`,
`State.convexCombo`).

## The construction uses Mathlib's GNS space

The blueprint proves the theorem in the textbook way: quotient $`A` by the null space
$`N(\omega) = \{n : \omega(n^*n) = 0\}`, complete $`A/N(\omega)` for
$`\langle [a], [b] \rangle = \omega(a^*b)`, let $`A` act by left multiplication, and take
$`\Omega = [\mathbf{1}]`. The Lean proof of `gns_construction` uses Mathlib's GNS space of the
positive functional $`\omega` instead (`PositiveLinearMap.GNS`): the completion of $`A` with the
semi-inner product $`\omega(a^*b)`, in which the quotient by $`N(\omega)` happens inside the
completion. The representation is Mathlib's `PositiveLinearMap.gnsStarAlgHom`, and $`\Omega` is
the class of $`\mathbf{1}`. The blueprint's lemmas (the Cauchy–Schwarz inequality, $`N(\omega)`
as a closed subspace) are formalised separately and are not used by the construction (blueprint
[thrm:gns-construction-theorem](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-construction-theorem),
formalization note).

The theorem is an existential over a Hilbert space, which in Lean is a type with three instances.
An existential needs a fixed universe for that type, so `gns_construction` puts $`H` in the universe
of $`A`, where Mathlib's space lives. Uniqueness is the separate theorem `gns_unique`, since the
two Hilbert spaces it compares are different types, in any universes.

A representation is a unital \*-homomorphism `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)` into the bounded operators
on a complex Hilbert space. It is not wrapped in a structure, so `H` is an explicit type and
`π a x` is the operator $`\pi(a)` applied to $`x`.

## Cyclic and separating vectors

`IsCyclicVector π Ω` says that the vectors $`\pi(a)\Omega` are dense in $`H`. The blueprint states
it for any algebra; in Lean $`A` is a unital C\*-algebra, the case used throughout. There is no
separate definition of a separating vector: theorems state the condition inline. In this chapter
it is stated for the elements of $`A`, $`\pi(a)\Omega = 0 \Rightarrow a = 0`, not for the
von Neumann algebra $`\pi(A)''`; the
[Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Main-definitions-and-theorems--Representations-and-local-von-Neumann-algebras)
states the operator form for the local von Neumann algebras.

## Irreducibility, purity and the commutant

Irreducibility has two textbook forms: no nontrivial closed invariant subspace, and a trivial
commutant, $`\pi(A)' = \mathbb{C}\mathbf{1}`. They are equivalent: the projection onto a closed
invariant subspace lies in $`\pi(A)'`, and the von Neumann algebra $`\pi(A)'` is generated by its
projections. The library uses the commutant form, as the blueprint does
([def:irreducible-representation](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-representation)):
`IsIrreducible π` says that every bounded operator commuting with all $`\pi(a)` is a multiple of
$`\mathbf{1}`. On the zero Hilbert space every operator is $`0 = 0 \cdot \mathbf{1}`, so every
representation on it satisfies `IsIrreducible`; results that need a nonzero space assume it, as
`Nontrivial H` or as a nonzero vector. A space carrying a vector that reproduces a state is never
zero, since $`\|\Omega\|^2 = \langle \Omega, \pi(\mathbf{1})\Omega \rangle = \omega(\mathbf{1}) = 1`;
this is immediate from the reproducing condition at $`a = \mathbf{1}`, and the library has no
separate lemma for it. So the zero case does not arise in `isPure_iff_isIrreducible`.

Purity is defined by domination
([def:pure-state](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pure-state)):
every positive functional $`\psi` with $`\psi(a^*a) \le \omega(a^*a)` is a multiple of $`\omega`.
This avoids normalising the parts of a mixture. The convex form, that $`\omega` is not a
nontrivial mixture of two states, is `State.IsExtremePoint`, and the two are proved equivalent.
The equivalence of purity with irreducibility of the GNS representation goes through a
Radon–Nikodym operator `rnOp`, the element of $`\pi(A)'` that represents a dominated $`\psi`.

The state space appears in two topologies. `stateSpace A`, a subset of `A →L[ℂ] ℂ` with the norm
topology, carries convexity and Mathlib's `extremePoints`. `weakStateSet`, a subset of Mathlib's
`WeakDual ℂ A`, carries the weak-\* topology and is compact. The existence of pure states, by the
Krein–Milman theorem applied to `weakStateSet`, is not proved: among the missing pieces, Mathlib
has no instance `LocallyConvexSpace ℝ (WeakDual ℂ A)`, which its Krein–Milman theorem needs.

The von Neumann algebra $`\pi(A)''` is `gnsVonNeumann π` as a set of operators and
`gnsVonNeumannAlgebra π` bundled as Mathlib's `VonNeumannAlgebra`; the commutant is Mathlib's
`Set.centralizer`, and $`\pi(A)'` bundled is `commutantVonNeumann π`. The names refer to the GNS
representation, but $`\pi` is any representation.

## Disjointness, quasi-equivalence and superselection

As you will recall, the superselection sectors of a theory are labelled by unitary equivalence
classes of irreducible representations of its algebra of observables. The library compares representations in three ways, each a
proposition:

* `UnitaryEquiv π₁ π₂`: a unitary $`U : H_1 \to H_2` with $`U\pi_1(a) = \pi_2(a)U`;
* `QuasiEquiv π₁ π₂`: a \*-isomorphism $`\pi_1(A)'' \to \pi_2(A)''` with
  $`\pi_1(a) \mapsto \pi_2(a)`;
* `AreDisjoint π₁ π₂`: the only intertwiner from $`\pi_1` to $`\pi_2` is $`0`.

A unitary is a linear isometric equivalence `H₁ ≃ₗᵢ[ℂ] H₂`. Quasi-equivalence asks for a
\*-isomorphism of the underlying \*-algebras, with no normality condition, since a \*-isomorphism of
von Neumann algebras is automatically normal. The quasi-equivalence of a representation with its
amplification is not proved: it needs the commutant of an amplification,
$`(\pi(A) \otimes \mathbf{1})' = \pi(A)' \mathbin{\bar\otimes} B(\ell^2(\iota))`, which Mathlib does not provide.

## Direct sums and amplification

The direct sum of a family $`(\pi_i)_{i \in \iota}` acts on Mathlib's $`\ell^2` space `lp H 2` of a
family of Hilbert spaces `H : ι → Type*`, over an arbitrary index type, by the block-diagonal
operator with blocks $`\pi_i(a)`. It is bounded by $`\|a\|` because a \*-homomorphism of
C\*-algebras is contractive. The amplification $`\iota \cdot \pi` is the direct sum of the constant
family.

## Covariance and unitary implementation

Symmetries enter in two ways. First, a \*-isomorphism $`\Phi : A \to B` relabels observables. The
pullback $`\omega \circ \Phi` of a state is `State.comp`, defined along any unital
\*-homomorphism, and the GNS representation of $`\omega \circ \Phi` is that of $`\omega` composed
with $`\Phi`, up to unitary equivalence. No new construction is needed: `gns_unique` applies to the
two cyclic representations of $`\omega \circ \Phi`.

Second, a family of \*-automorphisms $`\gamma_g` that leaves $`\omega` invariant is implemented on the
GNS space by unitaries $`U(g)`, the extension of $`\pi(a)\Omega \mapsto \pi(\gamma_g(a))\Omega`. These
theorems are stated for any unital C\*-algebra and any monoid $`G`, with the action either as a function with
the composition laws or as a monoid homomorphism. They apply both to the quasilocal algebra with
the Poincaré action and to a local algebra with the stabiliser of its region. Strong continuity of
$`U` follows from continuity of the matrix coefficients $`g \mapsto \omega(a^*\gamma_g(b))`; it is
what Stone's theorem needs to produce self-adjoint generators, such as the Hamiltonian.

# Main definitions and theorems
%%%
tag := "gns-main"
%%%

Definitions are shown with their docstrings, which give the mathematics and the blueprint entry;
theorems with their statements, as Lean prints them, and a line or two of explanation. Each
subsection opens with the blueprint entries it covers. In the printed statements,
`inner ℂ x y` is the inner product $`\langle x, y \rangle`, linear in the second argument, and
`(π a) Ω` is $`\pi(a)\Omega`. For the declarations not shown here, see the
[API documentation](https://physicslib.github.io/physicslib4/docs/Physicslib4/GNS/Basic.html) and
the files listed at the end of the chapter.

## States

Blueprint: [def:state][bp-state], [lmm:cauchy-schwarz-inequality][bp-cs], [lmm:lmm1][bp-l1],
[lmm:lmm2][bp-l2].

{docstring Physicslib4.GNS.State}

{docstring Physicslib4.GNS.State.IsFaithful}

The Cauchy–Schwarz inequality is stated for any positive linear functional on a complex \*-ring,
with no continuity, normalisation or unit. Since $`\omega(a^*a)` and $`\omega(b^*b)` are
non-negative reals, the right-hand side uses real parts:

```lean (name := checkCS)
open Physicslib4 GNS in
#check cauchy_schwarz_inequality
```

```leanOutput checkCS
Physicslib4.GNS.cauchy_schwarz_inequality.{u_1} {A : Type u_1} [NonUnitalNonAssocRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] (ω : A →ₗ[ℂ] ℂ) (hω : ∀ (a : A), 0 ≤ ω (star a * a))
  (a b : A) : Complex.normSq (ω (star a * b)) ≤ (ω (star a * a)).re * (ω (star b * b)).re
```

From it, the null set $`N(\omega)` equals $`\{n : \omega(b^*n) = 0 \text{ for all } b\}`
(`lmm1`), so it is a closed linear subspace (`lmm2`,
{apiDocs Physicslib4.GNS.nullSubmodule}[`nullSubmodule`]).

[bp-state]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:state
[bp-cs]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cauchy-schwarz-inequality
[bp-l1]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lmm1
[bp-l2]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lmm2

## The GNS construction

Blueprint: [def:cyclic-vector][bp-cyc], [thrm:gns-construction-theorem][bp-gns],
[thrm:separating-faithful][bp-sep].

{docstring Physicslib4.GNS.IsCyclicVector}

The existence half of the theorem. Lean prints the three anonymous instance arguments as
`x : NormedAddCommGroup H`, `x_1 : InnerProductSpace ℂ H` and `x_2 : CompleteSpace H`; tutorial
[chapter 3](../tutorial/Worked-examples/#worked-examples-gns) reads the statement line by line and
applies it to a state.

```lean (name := checkGNS)
open Physicslib4 GNS in
#check gns_construction
```

```leanOutput checkGNS
Physicslib4.GNS.gns_construction.{u} {A : Type u} [CStarAlgebra A] (ω : State A) :
  ∃ H x x_1,
    ∃ (x_2 : CompleteSpace H),
      ∃ π Ω, IsCyclicVector π Ω ∧ (∀ (a : A), ω a = inner ℂ Ω ((π a) Ω)) ∧ (ω.IsFaithful → Function.Injective ⇑π)
```

Uniqueness: any two cyclic representations that reproduce $`\omega` are related by a unitary `U`,
a linear isometric equivalence, that maps $`\Omega_1` to $`\Omega_2` and intertwines $`\pi_1` with
$`\pi_2`:

```lean (name := checkUnique)
open Physicslib4 GNS in
#check gns_unique
```

```leanOutput checkUnique
Physicslib4.GNS.gns_unique.{u_1, u_2, u_3} {A : Type u_1} [CStarAlgebra A] (ω : State A) {H₁ : Type u_2}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (π₁ : A →⋆ₐ[ℂ] H₁ →L[ℂ] H₁) (Ω₁ : H₁)
  (hcyc₁ : IsCyclicVector π₁ Ω₁) (hrep₁ : ∀ (a : A), ω a = inner ℂ Ω₁ ((π₁ a) Ω₁)) {H₂ : Type u_3}
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] (π₂ : A →⋆ₐ[ℂ] H₂ →L[ℂ] H₂) (Ω₂ : H₂)
  (hcyc₂ : IsCyclicVector π₂ Ω₂) (hrep₂ : ∀ (a : A), ω a = inner ℂ Ω₂ ((π₂ a) Ω₂)) :
  ∃ U, U Ω₁ = Ω₂ ∧ ∀ (a : A) (x : H₁), U ((π₁ a) x) = (π₂ a) (U x)
```

For a faithful state the reproducing vector is separating, in any representation, since
$`\|\pi(a)\Omega\|^2 = \omega(a^*a)`:

```lean (name := checkSep)
open Physicslib4 GNS in
#check separating_of_faithful
```

```leanOutput checkSep
Physicslib4.GNS.separating_of_faithful.{u_1, u_2} {A : Type u_1} [CStarAlgebra A] {H : Type u_2} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] {ω : State A} (hω : ω.IsFaithful) (π : A →⋆ₐ[ℂ] H →L[ℂ] H) (Ω : H)
  (hrep : ∀ (a : A), ω a = inner ℂ Ω ((π a) Ω)) {a : A} (ha : (π a) Ω = 0) : a = 0
```

The GNS form, a triple whose vector is both cyclic and separating, is
{apiDocs Physicslib4.GNS.exists_gns_separating}[`exists_gns_separating`].

[bp-cyc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:cyclic-vector
[bp-gns]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-construction-theorem
[bp-sep]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:separating-faithful

## Irreducibility and purity

Blueprint: [def:irreducible-representation][bp-irr], [thrm:schur-lemma][bp-schur],
[thrm:irreducible-generates-all][bp-all], [def:pure-state][bp-pure],
[thrm:gns-radon-nikodym-operator][bp-rn], [thrm:pure-iff-irreducible][bp-pi],
[def:extreme-state][bp-ext], [thrm:pure-iff-extreme][bp-pe],
[thrm:state-space-weak-compact][bp-wc], [def:von-neumann-center][bp-ctr].

{docstring Physicslib4.GNS.IsIrreducible}

In the printed statements Lean writes `GNS.IsIrreducible`, to distinguish it from Mathlib's
`IsIrreducible`, irreducibility of a subset of a topological space. Irreducibility is the statement that the commutant, Mathlib's
`Set.centralizer` of the image, is the set `scalarOperators H` of multiples of $`\mathbf{1}`:

```lean (name := checkCentralizer)
open Physicslib4 GNS in
#check isIrreducible_iff_centralizer
```

```leanOutput checkCentralizer
Physicslib4.GNS.isIrreducible_iff_centralizer.{u_1, u_2} {A : Type u_1} [CStarAlgebra A] {H₁ : Type u_2}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] {π : A →⋆ₐ[ℂ] H₁ →L[ℂ] H₁} :
  GNS.IsIrreducible π ↔ (Set.range ⇑π).centralizer = scalarOperators H₁
```

Equivalently, $`\pi(A)''` is all of $`B(H)`, because the commutant of the scalars is everything and
the centre of $`B(H)` is the scalars:

```lean (name := checkUniv)
open Physicslib4 GNS in
#check isIrreducible_iff_gnsVonNeumann_eq_univ
```

```leanOutput checkUniv
Physicslib4.GNS.isIrreducible_iff_gnsVonNeumann_eq_univ.{u_1, u_2} {A : Type u_1} [CStarAlgebra A] {H : Type u_2}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : A →⋆ₐ[ℂ] H →L[ℂ] H} :
  GNS.IsIrreducible π ↔ gnsVonNeumann π = Set.univ
```

{docstring Physicslib4.GNS.gnsVonNeumann}

The topological Schur lemma, `eq_smul_one_of_commute_of_cyclic`, says that in a cyclic
representation an operator $`T` of $`\pi(A)'` with
$`\langle \Omega, T\pi(a)\Omega \rangle = c\,\langle \Omega, \pi(a)\Omega \rangle` for all $`a` equals
$`c\mathbf{1}`. The centre of a von Neumann algebra $`R` is
{apiDocs Physicslib4.GNS.vonNeumannCenter}[`vonNeumannCenter R`], and $`R` is a factor
(`IsFactor`) when the centre is the scalars. For an irreducible representation the centre of
$`\pi(A)''` is the scalars (`center_gnsVonNeumann_eq_of_isIrreducible`), so it generates a factor
(`isFactor_gnsVonNeumann_of_isIrreducible`).

{docstring Physicslib4.GNS.IsPure}

The headline theorem of the section, for any cyclic representation that reproduces $`\omega`:

```lean (name := checkPureIrr)
open Physicslib4 GNS in
#check isPure_iff_isIrreducible
```

```leanOutput checkPureIrr
Physicslib4.GNS.isPure_iff_isIrreducible.{u_1, u_2} {A : Type u_1} [CStarAlgebra A] {H : Type u_2}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ω : State A} {π : A →⋆ₐ[ℂ] H →L[ℂ] H} {Ω : H}
  (hcyc : IsCyclicVector π Ω) (hrep : ∀ (a : A), ω a = inner ℂ Ω ((π a) Ω)) : IsPure ω ↔ GNS.IsIrreducible π
```

From irreducible to pure, a dominated $`\psi` gives the Radon–Nikodym operator
{apiDocs Physicslib4.GNS.rnOp}[`rnOp`] in $`\pi(A)'`, with
$`\psi(a) = \langle \Omega, T\pi(a)\Omega \rangle`, which irreducibility makes a scalar. From pure
to irreducible, an element of $`\pi(A)'` splits into self-adjoint parts, which rescale into
functionals dominated by $`\omega`. With the GNS triple, a pure state therefore gives a factor
(`exists_gns_factor_of_isPure`) and $`\pi(A)'' = B(H)` (`exists_gns_generates_all_of_isPure`).

{docstring Physicslib4.GNS.State.IsExtremePoint}

```lean (name := checkExtreme)
open Physicslib4 GNS in
#check isPure_iff_isExtremePoint
```

```leanOutput checkExtreme
Physicslib4.GNS.isPure_iff_isExtremePoint.{u_1} {A : Type u_1} [CStarAlgebra A] (ω : State A) :
  IsPure ω ↔ ω.IsExtremePoint
```

The proof rests on $`\|\varphi\| = \mathrm{Re}\,\varphi(\mathbf{1})` for positive $`\varphi`,
which fixes the weights of a mixture. Extremality agrees with Mathlib's `extremePoints` of
{apiDocs Physicslib4.GNS.stateSpace}[`stateSpace A`]
(`mem_extremePoints_iff_isExtremePoint`), which is convex (`convex_stateSpace`). In the weak-\*
topology:

{docstring Physicslib4.GNS.weakStateSet}

```lean (name := checkCompact)
open Physicslib4 GNS in
#check isCompact_weakStateSet
```

```leanOutput checkCompact
Physicslib4.GNS.isCompact_weakStateSet.{u_1} {A : Type u_1} [CStarAlgebra A] : IsCompact weakStateSet
```

The proof is the Banach–Alaoglu theorem: the set is weak-\* closed and lies in the unit ball.

[bp-irr]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-representation
[bp-schur]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:schur-lemma
[bp-all]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-generates-all
[bp-pure]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pure-state
[bp-rn]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-radon-nikodym-operator
[bp-pi]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible
[bp-ext]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:extreme-state
[bp-pe]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme
[bp-wc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-space-weak-compact
[bp-ctr]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-center

## Equivalence and disjointness of representations

Blueprint: [def:unitary-equivalence][bp-ue], [thrm:unitary-equiv-invariants][bp-uei],
[def:disjoint-representations][bp-dis], [def:quasi-equivalence][bp-qe],
[thrm:irreducible-dichotomy][bp-dich], [thrm:pure-state-dichotomy][bp-pdich],
[thrm:commutant-von-neumann][bp-cvn].

{docstring Physicslib4.GNS.UnitaryEquiv}

{docstring Physicslib4.GNS.Intertwines}

{docstring Physicslib4.GNS.AreDisjoint}

Unitarily equivalent representations on a nonzero space are not disjoint
(`UnitaryEquiv.not_areDisjoint`, which assumes `Nontrivial H₁`). For irreducible representations
the two notions are complementary: a nonzero intertwiner $`T` between irreducibles has
$`T^*T` and $`TT^*` scalar, so a multiple of $`T` is unitary.

```lean (name := checkDichotomy)
open Physicslib4 GNS in
#check areDisjoint_or_unitaryEquiv_of_isIrreducible
```

```leanOutput checkDichotomy
Physicslib4.GNS.areDisjoint_or_unitaryEquiv_of_isIrreducible.{u_1, u_2, u_3} {A : Type u_1} [CStarAlgebra A]
  {H₁ : Type u_2} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] {H₂ : Type u_3}
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] {π₁ : A →⋆ₐ[ℂ] H₁ →L[ℂ] H₁}
  {π₂ : A →⋆ₐ[ℂ] H₂ →L[ℂ] H₂} (h1 : GNS.IsIrreducible π₁) (h2 : GNS.IsIrreducible π₂) :
  AreDisjoint π₁ π₂ ∨ UnitaryEquiv π₁ π₂
```

For pure states, applied to their GNS representations, this is
{apiDocs Physicslib4.GNS.exists_gns_areDisjoint_or_unitaryEquiv_of_isPure}[`exists_gns_areDisjoint_or_unitaryEquiv_of_isPure`]:
the GNS representations of two pure states are unitarily equivalent (the same superselection
sector) or disjoint. Unitary equivalence
preserves irreducibility and the factor property (`UnitaryEquiv.isIrreducible_iff`,
`UnitaryEquiv.isFactor_iff`).

{docstring Physicslib4.GNS.QuasiEquiv}

```lean (name := checkQuasi)
open Physicslib4 GNS in
#check UnitaryEquiv.quasiEquiv
```

```leanOutput checkQuasi
Physicslib4.GNS.UnitaryEquiv.quasiEquiv.{u_1, u_2, u_3} {A : Type u_1} [CStarAlgebra A] {H₁ : Type u_2}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] {H₂ : Type u_3} [NormedAddCommGroup H₂]
  [InnerProductSpace ℂ H₂] [CompleteSpace H₂] {π₁ : A →⋆ₐ[ℂ] H₁ →L[ℂ] H₁} {π₂ : A →⋆ₐ[ℂ] H₂ →L[ℂ] H₂}
  (h : UnitaryEquiv π₁ π₂) : QuasiEquiv π₁ π₂
```

The commutant $`\pi(A)'`, the algebra of intertwiners from $`\pi` to itself, as a von Neumann
algebra:

{docstring Physicslib4.GNS.commutantVonNeumann}

[bp-ue]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:unitary-equivalence
[bp-uei]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:unitary-equiv-invariants
[bp-dis]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:disjoint-representations
[bp-qe]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasi-equivalence
[bp-dich]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-dichotomy
[bp-pdich]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-state-dichotomy
[bp-cvn]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-von-neumann

## Direct sums and amplification

Blueprint: [def:direct-sum-representation][bp-ds], [thrm:direct-sum-subrepresentation][bp-dss],
[def:amplification][bp-amp], [thrm:direct-sum-reducible][bp-dsr].

{docstring Physicslib4.GNS.directSum}

{docstring Physicslib4.GNS.amplification}

The projection onto one summand commutes with the direct sum
(`summandProj_mem_commutant`), and it is not a scalar when its own summand and another summand
are both nonzero:

```lean (name := checkReducible)
open Physicslib4 GNS in
#check not_isIrreducible_directSum
```

```leanOutput checkReducible
Physicslib4.GNS.not_isIrreducible_directSum.{u_1, u_2, u_3} {A : Type u_1} [CStarAlgebra A] {ι : Type u_2}
  [DecidableEq ι] {H : ι → Type u_3} [(i : ι) → NormedAddCommGroup (H i)] [(i : ι) → InnerProductSpace ℂ (H i)]
  [∀ (i : ι), CompleteSpace (H i)] (π : (i : ι) → A →⋆ₐ[ℂ] H i →L[ℂ] H i) {j k : ι} (hjk : j ≠ k) {v : H j} (hv : v ≠ 0)
  {w : H k} (hw : w ≠ 0) : ¬GNS.IsIrreducible (directSum π)
```

[bp-ds]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:direct-sum-representation
[bp-dss]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:direct-sum-subrepresentation
[bp-amp]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:amplification
[bp-dsr]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:direct-sum-reducible

## Covariance

Blueprint: [def:state-pullback][bp-pb], [thrm:pure-pullback-invariant][bp-ppb],
[thrm:gns-covariance][bp-cov], [thrm:gns-covariance-unitary-equiv][bp-covue],
[thrm:gns-sector-transport][bp-sector], and, for the unitary implementation,
[thrm:invariant-state-gns-unitary][bp-inv] and
[thrm:invariant-state-gns-unitary-strongly-continuous][bp-invsc], of which the theorems below are the
general form.

{docstring Physicslib4.GNS.State.comp}

Pulling back along a \*-isomorphism preserves purity in both directions:

```lean (name := checkPureComp)
open Physicslib4 GNS in
#check isPure_comp_iff
```

```leanOutput checkPureComp
Physicslib4.GNS.isPure_comp_iff.{u_1, u_2} {A : Type u_1} [CStarAlgebra A] {B : Type u_2} [CStarAlgebra B]
  (Φ : A ≃⋆ₐ[ℂ] B) (ω : State B) : IsPure (ω.comp Φ.toStarAlgHom) ↔ IsPure ω
```

The automorphism case, with `State.precomp`, is `isPure_precomp_iff`. The GNS data of
$`\omega \circ \Phi` and of $`\omega` correspond through a unitary: for a cyclic representation
$`(H_1, \pi_1, \Omega_1)` of $`A` reproducing $`\omega \circ \Phi` and one, $`(H_2, \pi_2, \Omega_2)`,
of $`B` reproducing $`\omega`, there is $`U` with $`U\Omega_1 = \Omega_2` and
$`U\pi_1(a) = \pi_2(\Phi(a))U`:

```lean (name := checkCov)
open Physicslib4 GNS in
#check exists_unitary_of_gns_comp
```

```leanOutput checkCov
Physicslib4.GNS.exists_unitary_of_gns_comp.{u_1, u_2, u_4, u_5} {A : Type u_1} [CStarAlgebra A] {B : Type u_2}
  [CStarAlgebra B] (Φ : A ≃⋆ₐ[ℂ] B) (ω : State B) {H₁ : Type u_4} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁] (π₁ : A →⋆ₐ[ℂ] H₁ →L[ℂ] H₁) (Ω₁ : H₁) (hcyc₁ : IsCyclicVector π₁ Ω₁)
  (hrep₁ : ∀ (a : A), (ω.comp Φ.toStarAlgHom) a = inner ℂ Ω₁ ((π₁ a) Ω₁)) {H₂ : Type u_5} [NormedAddCommGroup H₂]
  [InnerProductSpace ℂ H₂] [CompleteSpace H₂] (π₂ : B →⋆ₐ[ℂ] H₂ →L[ℂ] H₂) (Ω₂ : H₂) (hcyc₂ : IsCyclicVector π₂ Ω₂)
  (hrep₂ : ∀ (b : B), ω b = inner ℂ Ω₂ ((π₂ b) Ω₂)) :
  ∃ U, U Ω₁ = Ω₂ ∧ ∀ (a : A) (x : H₁), U ((π₁ a) x) = (π₂ (Φ a)) (U x)
```

In the language of `UnitaryEquiv` this is
{apiDocs Physicslib4.GNS.unitaryEquiv_comp_of_gns}[`unitaryEquiv_comp_of_gns`], and with it
irreducibility and the factor property transport along $`\Phi`
(`isIrreducible_iff_of_gns_comp`, `isFactor_iff_of_gns_comp`).

The unitary implementation of a symmetry that leaves $`\omega` invariant is
{apiDocs Physicslib4.GNS.exists_gns_unitary_of_invariant}[`exists_gns_unitary_of_invariant`].
For \*-automorphisms $`\gamma_g` of $`A`, $`g` in a monoid $`G`, with
$`\gamma_{g'g} = \gamma_{g'} \circ \gamma_g`, $`\gamma_1 = \mathrm{id}` and
$`\omega \circ \gamma_g = \omega`, it gives a GNS triple of $`\omega` and unitaries $`U(g)` with

$$`U(g)\,\pi(a)\Omega = \pi(\gamma_g(a))\,\Omega, \quad U(g)\,\Omega = \Omega, \quad U(g'g) = U(g')\,U(g), \quad U(1) = \mathbf{1},`

and $`U(g)\,\pi(a)\,U(g)^{-1} = \pi(\gamma_g(a))` on all of $`H`.
{apiDocs Physicslib4.GNS.exists_gns_unitaryRep_of_invariant}[`exists_gns_unitaryRep_of_invariant`]
takes $`\gamma` and returns $`U` as monoid homomorphisms. When $`G` has a topology and the matrix
coefficients $`g \mapsto \omega(a^*\gamma_g(b))` are continuous, $`g \mapsto U(g)\psi` is
continuous for every $`\psi`
({apiDocs Physicslib4.GNS.exists_gns_unitary_of_invariant_strongContinuous}[`exists_gns_unitary_of_invariant_strongContinuous`],
{apiDocs Physicslib4.GNS.exists_gns_unitaryRep_of_invariant_strongContinuous}[`exists_gns_unitaryRep_of_invariant_strongContinuous`]).
These statements are long existentials over the Hilbert space and its structure, so they are
linked rather than printed.

[bp-pb]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:state-pullback
[bp-ppb]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-pullback-invariant
[bp-cov]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance
[bp-covue]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-unitary-equiv
[bp-sector]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-sector-transport
[bp-inv]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:invariant-state-gns-unitary
[bp-invsc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:invariant-state-gns-unitary-strongly-continuous

# Where to look
%%%
tag := "gns-files"
%%%

The section is formalised in `Physicslib4/GNS/`, one topic per file. Each entry links to the API
documentation of a representative declaration, from which the rest of the file can be browsed.

States and the construction:

* `Basic.lean`: states, faithful states and cyclic vectors, {apiDocs Physicslib4.GNS.State}[].
* `CauchySchwarz.lean`: the Cauchy–Schwarz inequality for positive functionals,
  {apiDocs Physicslib4.GNS.cauchy_schwarz_inequality}[`cauchy_schwarz_inequality`].
* `NullSpace.lean`: the null set $`N(\omega)` and its closed subspace,
  {apiDocs Physicslib4.GNS.nullSubmodule}[`nullSubmodule`].
* `Construction.lean`: existence and uniqueness of the GNS triple,
  {apiDocs Physicslib4.GNS.gns_construction}[`gns_construction`].
* `Separating.lean`: the vector of a faithful state is separating,
  {apiDocs Physicslib4.GNS.separating_of_faithful}[`separating_of_faithful`].

Irreducibility and purity:

* `Irreducibility.lean`: irreducibility, the Schur lemma, purity, $`\pi(A)''`, von Neumann
  algebras from self-adjoint sets, and the centre (`IsFactor` itself is in
  `Operators/Conjugation.lean`), {apiDocs Physicslib4.GNS.IsIrreducible}[`IsIrreducible`].
* `RadonNikodym.lean`: the Radon–Nikodym operator and purity equivalent to irreducibility,
  {apiDocs Physicslib4.GNS.isPure_iff_isIrreducible}[`isPure_iff_isIrreducible`].
* `ExtremeState.lean`: extreme points, the state space, mixtures, and pullbacks of states,
  {apiDocs Physicslib4.GNS.isPure_iff_isExtremePoint}[`isPure_iff_isExtremePoint`].
* `PureStateExists.lean`: the state space in the weak-\* topology and its compactness,
  {apiDocs Physicslib4.GNS.isCompact_weakStateSet}[`isCompact_weakStateSet`].

Comparing representations:

* `UnitaryEquiv.lean`: unitary equivalence and the invariance of irreducibility and the factor
  property, {apiDocs Physicslib4.GNS.UnitaryEquiv}[`UnitaryEquiv`].
* `Superselection.lean`: intertwiners, disjointness, the dichotomy for irreducibles, the
  commutant as a von Neumann algebra, and quasi-equivalence,
  {apiDocs Physicslib4.GNS.areDisjoint_or_unitaryEquiv_of_isIrreducible}[`areDisjoint_or_unitaryEquiv_of_isIrreducible`].
* `DirectSum.lean`: the direct sum and its summand projections,
  {apiDocs Physicslib4.GNS.directSum}[`directSum`].
* `Amplification.lean`: amplification and the reducibility of direct sums,
  {apiDocs Physicslib4.GNS.amplification}[`amplification`].

Covariance:

* `Covariance.lean`: the GNS representation of a pulled-back state,
  {apiDocs Physicslib4.GNS.exists_unitary_of_gns_comp}[`exists_unitary_of_gns_comp`].
* `UnitaryRepresentation.lean`: the unitary implementation of an invariant symmetry,
  {apiDocs Physicslib4.GNS.exists_gns_unitaryRep_of_invariant}[`exists_gns_unitaryRep_of_invariant`].

The von Neumann density theorem, cited in the `gnsVonNeumann` docstring, is in
`Physicslib4/Operators/DensityTheorem.lean` and is described in the
[Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Main-definitions-and-theorems--Representations-and-local-von-Neumann-algebras).
The blueprint sections are
[Section 10.1](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:gns-construction-details)
and the representation-theory subsections of
[Section 10.6](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:haag-kastler-axioms),
and the section pages for [Section 10.1](https://physicslib.github.io/physicslib4/sec10-1-gns.html)
and [Section 10.6](https://physicslib.github.io/physicslib4/sec10-6-haag-kastler.html) list each
entry with the Lean declaration that formalises it.
