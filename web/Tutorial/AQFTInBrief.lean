import VersoManual
import Tutorial.Meta
import Tutorial.Papers

open Verso.Genre Manual
open Tutorial

#doc (Manual) "AQFT in brief" =>

%%%
tag := "aqft-in-brief"
%%%

Algebraic quantum field theory (AQFT) describes a relativistic quantum system by the observables
that can be measured in each region of spacetime, and by the relations between them that relativity
and quantum mechanics impose. This chapter introduces it to a reader who knows quantum mechanics and
special relativity. It covers nets of local algebras on causal diamonds, the Haag–Kastler axioms,
states and the GNS construction, and the points at which this project makes the 1964 axioms precise.
Lean appears from the next chapter on.

# Why algebras

As you will recall from a first course in quantum field theory, a field such as the free scalar
field $`\phi` is not a function from spacetime to operators. The expression $`\phi(x)` makes sense
only inside an integral: the field is an operator-valued distribution, and the objects that act on
the Hilbert space are its smearings

$$`\phi(f) = \int f(x)\, \phi(x)\, d^4x,`

where $`f` is a smooth test function with compact support. If the support of $`f` lies in a region
$`\mathbf{B}` of spacetime, then $`\phi(f)` is something an experimenter confined to $`\mathbf{B}`
can, at least in principle, control.

Fields are a convenient way to generate observables, but they are not observables themselves, and
they are far from unique. A Dirac field is not self-adjoint and anticommutes, rather than commutes,
at spacelike separation; it cannot be measured. A gauge potential changes under gauge
transformations that leave every measurable quantity untouched. Even for a scalar field, different
fields, such as the free field $`\phi` and $`\phi + {:}\phi^3{:}` with $`{:}\phi^3{:}` the
Wick-ordered cube, commute with each other at spacelike separation. Such relatively local fields
belong to one _Borchers class_, and in an interacting theory any two fields of the class that create
the same particles give the same scattering matrix. The choice of field is a choice of coordinates
on the theory.

What does not depend on that choice is the answer to the question: _which observables can be
measured in which region of spacetime?_ Haag's idea is to take this assignment as the primary
object. To each region $`\mathbf{B}` one attaches an algebra $`\mathfrak{U}(\mathbf{B})` of
observables measurable in $`\mathbf{B}`, generated, in a theory with a field, by bounded functions
of the smeared fields $`\phi(f)` with $`f` real and supported in $`\mathbf{B}`. The physics is then
encoded in how these algebras sit inside one another and how they relate across spacetime. The
assignment $`\mathbf{B} \mapsto \mathfrak{U}(\mathbf{B})` is called a _net of local algebras_.

Two features of the approach matter from the start.

* The algebras consist of _bounded_ operators, or abstract versions of them. Unbounded operators
  such as $`\phi(f)` have domains, and their sums and products need not be defined. Bounded
  functions of them, such as $`e^{i\phi(f)}` or the spectral projections of $`\phi(f)`, carry the
  same physical information without these difficulties.
* The algebras are _abstract_: no Hilbert space is fixed in advance. In quantum mechanics with
  finitely many degrees of freedom, the Stone–von Neumann theorem guarantees that the canonical
  commutation relations have, up to unitary equivalence, one irreducible representation (with the
  usual regularity assumptions). A field has infinitely many degrees of freedom, and the theorem
  fails: the same algebra has many inequivalent representations, describing, for instance, different
  thermal equilibria or different charge sectors. The algebraic approach keeps them all, and
  recovers a Hilbert space from a state, by the GNS construction, when it is needed.

:::::exercise
Let $`f` and $`g` be real test functions, and suppose that the smeared field satisfies the
commutation relation $`[\phi(f), \phi(g)] = i\Delta(f,g)\,\mathbf{1}` for a real number
$`\Delta(f,g)`. Assuming that the formal manipulations are justified, show that the unitaries
$`W(f) = e^{i\phi(f)}` satisfy the Weyl relations
$$`W(f)\,W(g) = e^{-i\Delta(f,g)/2}\, W(f+g).`
What does this say about $`W(f)` and $`W(g)` when $`\Delta(f,g) = 0`?

::::solution
For operators $`A` and $`B` whose commutator is a multiple of the identity, the
Baker–Campbell–Hausdorff formula reduces to $`e^{A}e^{B} = e^{A+B}e^{[A,B]/2}`. With $`A = i\phi(f)`
and $`B = i\phi(g)`, $`[A,B] = -[\phi(f),\phi(g)] = -i\Delta(f,g)\mathbf{1}`, and linearity of the
smearing gives $`A + B = i\phi(f+g)`. Hence $`W(f)W(g) = e^{-i\Delta(f,g)/2}\,W(f+g)`. Exchanging
$`f` and $`g` changes the sign of $`\Delta`, so $`W(f)W(g) = e^{-i\Delta(f,g)}W(g)W(f)`. When
$`\Delta(f,g) = 0` the two unitaries commute. For the free field $`\Delta(f,g)` vanishes whenever
the supports of $`f` and $`g` are spacelike separated: a first sign of the locality axiom below.
::::
:::::

*In the library:* the net, with its axioms, is the structure
`Physicslib4.AQFT.HaagKastler.HaagKastlerNet`.

# Regions of spacetime

You will be familiar with Minkowski space: the set $`\mathbb{R}^4` of points
$`x = (x^0, x^1, x^2, x^3)`, with time coordinate $`x^0` and the Minkowski form

$$`\eta(v, w) = -v^0 w^0 + v^1 w^1 + v^2 w^2 + v^3 w^3,`

of signature $`(-,+,+,+)`, in units with $`c = 1`. A nonzero vector $`v` is _timelike_ if
$`\eta(v,v) < 0`, _null_ if $`\eta(v,v) = 0` and _spacelike_ if $`\eta(v,v) > 0`; a timelike or null
vector is _causal_, and it is _future-directed_ if $`v^0 > 0`. Two points are compared through their
difference:

* $`p \ll q`, read "$`p` chronologically precedes $`q`", if $`q - p` is timelike and
  future-directed;
* $`p \prec q`, read "$`p` causally precedes $`q`", if $`q - p` is causal and future-directed, or
  zero.

The _chronological future_ and _chronological past_ of a point are the open light cones

$$`I^+(p) = \{x : p \ll x\}, \qquad I^-(q) = \{x : x \ll q\},`

and the causal future and past $`J^{\pm}` are defined in the same way with $`\prec` in place of
$`\ll`. Two points are _spacelike separated_ if neither causally precedes the other, and two sets
are _completely spacelike_ if every point of one is spacelike separated from every point of the
other.

## Causal diamonds

Consider an experiment, carried out by an apparatus with mass, that starts at a spacetime point $`p`
and ends at a point $`q`. Every part of the apparatus moves on a timelike curve, so everything the
experiment touches lies to the future of $`p` and to the past of $`q`. This is the region

$$`\mathbf{B} = I^+(p) \cap I^-(q),`

called the _causal diamond_ (also double cone, or Alexandrov set) of $`p` and $`q`. It is open and
bounded, and it is nonempty exactly when $`p \ll q`; when it is empty we still count it as a
diamond, the empty diamond. In the frame in which $`q - p` points along the time axis, $`\mathbf{B}`
is the _domain of dependence_ of the open ball of radius $`(q^0 - p^0)/2` centred at the midpoint of
$`p` and $`q`: every inextendible causal curve through $`\mathbf{B}` meets the ball, so initial data
on the ball fix a hyperbolically propagating field throughout $`\mathbf{B}`.

:::figure "cones"
The diamond $`\mathbf{B} = I^+(p) \cap I^-(q)` in one space and one time dimension: the part of the
future cone of $`p` that lies in the past cone of $`q`.
:::

Why chronological rather than causal cones? With $`J^\pm`, the region $`J^+(p) \cap J^-(q)` is, when
nonempty, compact, so not open, and for $`q = p` it is the single point $`\{p\}`; an operator-valued
distribution has no value at a point, so there is no algebra of observables at a point to assign.
The chronological cones, and every diamond, are open.

The 1964 axioms of {citet haagKastler1964}[] attach algebras instead to all open sets with compact
closure. That phrase needs a topology on $`\mathbb{R}^4`, which the axioms do not name. The natural
candidate is the one built from the causal structure itself.

The _Alexandrov topology_ is the topology whose open sets are the unions of causal diamonds. For
this to define a topology, the diamonds must form a basis: the intersection of two diamonds must be
a union of diamonds. In Minkowski space it is, and the Alexandrov topology coincides with the usual
Euclidean topology of $`\mathbb{R}^4`, but it is defined by the light cones alone, without reference
to a Euclidean metric that has no physical meaning. In a curved spacetime the two topologies can
differ; they agree precisely when the spacetime is _strongly causal_.

So, in this project, _Minkowski spacetime_ is $`\mathbb{R}^4` with the form $`\eta`, the time
orientation given by the vector $`(1,0,0,0)`, and the Alexandrov topology, and the regions of the
net are its causal diamonds. One fact about them is used throughout: any two diamonds lie in a
common, larger diamond (the diamonds are _upward directed_ under inclusion).

:::::exercise
Show that $`I^+(p) \cap I^-(q)` is nonempty if and only if $`p \ll q`.

::::solution
If $`x` lies in the intersection, then $`p \ll x` and $`x \ll q`. The sum of two future-directed
timelike vectors is future-directed timelike (both lie in the open forward cone, which is convex),
so $`q - p = (q - x) + (x - p)` is future-directed timelike, and $`p \ll q`. Conversely, if
$`p \ll q`, the midpoint $`m = (p+q)/2` satisfies $`m - p = q - m = (q-p)/2`, which is
future-directed timelike, so $`m` lies in the intersection.
::::
:::::

:::::exercise
Show that any two diamonds $`I^+(p_1) \cap I^-(q_1)` and $`I^+(p_2) \cap I^-(q_2)` lie in a common
diamond.

::::solution
Choose $`p = (t, 0, 0, 0)` with $`t` so negative that $`p_k^0 - t > |\mathbf{p}_k|` for $`k = 1, 2`,
where $`\mathbf{p}_k` is the spatial part of $`p_k`. Then $`p_k - p` is future-directed timelike, so
$`p \ll p_k`, and by transitivity of $`\ll` (the convexity argument of the previous exercise)
$`I^+(p_k) \subseteq I^+(p)`. Choose $`q` in the same way, far in the future, so that
$`I^-(q_k) \subseteq I^-(q)`. Then both diamonds lie in $`I^+(p) \cap I^-(q)`.
::::
:::::

*In the library:* `Physicslib4.MinkowskiSpacetime`, with the Alexandrov topology
`Physicslib4.Spacetime.alexandrovTopology` and the diamonds
`Physicslib4.Spacetime.chronologicalDiamond`.

# C\*-algebras of observables

Recall that a Hilbert space $`\mathcal{H}` is a complex vector space with an inner product
$`\langle \cdot, \cdot \rangle`, linear in the second argument, that is complete in the norm
$`\|\psi\| = \langle \psi, \psi \rangle^{1/2}`. A linear operator $`A` on $`\mathcal{H}` is bounded
if its operator norm $`\|A\| = \sup_{\|\psi\| = 1} \|A\psi\|` is finite; the bounded operators form
an algebra $`\mathcal{B}(\mathcal{H})`. Each bounded $`A` has an adjoint $`A^*`, defined by
$`\langle \psi, A\chi \rangle = \langle A^*\psi, \chi \rangle`, and the observables of quantum
mechanics are the self-adjoint operators, $`A = A^*`, whose spectra are the possible outcomes of a
measurement. (Physicists often write $`A^\dagger`; this chapter writes $`A^*`, as mathematicians
do.)

One identity links the algebra $`\mathcal{B}(\mathcal{H})` to its norm:

$$`\|A^* A\| = \|A\|^2.`

(The bound $`\|A\|^2 \le \|A^*A\|` follows from $`\|A\psi\|^2 = \langle \psi, A^*A\psi \rangle`, and
$`\|A^*A\| \le \|A^*\|\,\|A\| = \|A\|^2`, since $`\|A^*\| = \|A\|` for bounded operators.) The
abstract counterpart of $`\mathcal{B}(\mathcal{H})` keeps these properties and forgets the Hilbert
space.

A _C\*-algebra_ is a complex algebra $`\mathfrak{A}` with

* a norm in which it is complete, with $`\|ab\| \le \|a\|\,\|b\|` (a Banach algebra);
* an _involution_ $`a \mapsto a^*`: antilinear, with $`(ab)^* = b^*a^*` and $`a^{**} = a`;
* the _C\*-identity_ $`\|a^*a\| = \|a\|^2` for every $`a`.

It is _unital_ if it has a unit $`\mathbf{1}`, with $`\mathbf{1}a = a\mathbf{1} = a`. All the
algebras of this chapter are unital. Examples are $`\mathcal{B}(\mathcal{H})` itself, any
norm-closed subalgebra of it that is closed under adjoints, the matrix algebras $`M_n(\mathbb{C})`,
and, as a commutative example, the continuous complex functions on a compact space with the supremum
norm and complex conjugation as involution.

A _\*-homomorphism_ $`\pi : \mathfrak{A} \to \mathfrak{B}` is a linear map with
$`\pi(ab) = \pi(a)\pi(b)` and $`\pi(a^*) = \pi(a)^*`; it is _unital_ if
$`\pi(\mathbf{1}) = \mathbf{1}`. A \*-homomorphism between C\*-algebras is automatically continuous,
with $`\|\pi(a)\| \le \|a\|`, and if it is injective it is isometric, $`\|\pi(a)\| = \|a\|`: the
norm of a C\*-algebra is fixed by its algebraic structure. An injective \*-homomorphism is a
_\*-monomorphism_, and a bijective one a _\*-isomorphism_. A _representation_ of $`\mathfrak{A}` on
a Hilbert space $`\mathcal{H}` is a \*-homomorphism
$`\pi : \mathfrak{A} \to \mathcal{B}(\mathcal{H})`.

Nothing is lost by the abstraction: by the Gelfand–Naimark theorem, every C\*-algebra is
\*-isomorphic to a norm-closed, adjoint-closed algebra of operators on some Hilbert space. What is
gained is that no particular Hilbert space is singled out.

The self-adjoint elements $`a = a^*` of a C\*-algebra are its _observables_. The possible results of
measuring $`a` are the points of its _spectrum_,

$$`\sigma(a) = \{\lambda \in \mathbb{C} : a - \lambda\mathbf{1} \text{ has no inverse in } \mathfrak{A}\},`

a nonempty compact subset of $`\mathbb{R}` when $`a` is self-adjoint. The definition refers to the
algebra in which inverses are sought. For C\*-algebras the choice does not matter: if
$`\mathfrak{A}` is a C\*-subalgebra of $`\mathfrak{B}` with the same unit, an element of
$`\mathfrak{A}` has the same spectrum in both. This _spectral permanence_ fails for general Banach
algebras, and it is one reason the axioms ask for C\*-algebras: an observable measured in a small
region is also an observable of any larger region, and its possible values must not depend on which
region we regard it as belonging to.

:::::exercise
Let $`\mathfrak{A}` be a nonzero unital C\*-algebra. Show that $`\|a^*\| = \|a\|` for every $`a`,
that $`\mathbf{1}^* = \mathbf{1}`, and that $`\|\mathbf{1}\| = 1`.

::::solution
For $`a \neq 0`, $`\|a\|^2 = \|a^*a\| \le \|a^*\|\,\|a\|`, so $`\|a\| \le \|a^*\|`. Applying this to
$`a^*` gives $`\|a^*\| \le \|a^{**}\| = \|a\|`. Next, $`\mathbf{1}^* a = (a^*\mathbf{1})^* = a` and
likewise $`a\mathbf{1}^* = a`, so $`\mathbf{1}^*` is a unit, and units are unique. Finally
$`\|\mathbf{1}\| = \|\mathbf{1}^*\mathbf{1}\| = \|\mathbf{1}\|^2`, so $`\|\mathbf{1}\|` is $`0` or
$`1`, and it is not $`0` because $`\mathbf{1} \neq 0` in a nonzero algebra.
::::
:::::

*In the library:* C\*-algebras are Mathlib's class `CStarAlgebra` (unital, complex); the net assigns
one to each diamond in `Physicslib4.AQFT.HaagKastler.LocalNet`.

# The axioms

A theory, in the Haag–Kastler framework, is a net of C\*-algebras on the diamonds of Minkowski
spacetime, subject to a short list of axioms, each of which rules something out. They are stated
here in the form this project uses.

## Axiom 1: local algebras

To every causal diamond $`\mathbf{B}` there is assigned a unital C\*-algebra
$`\mathfrak{U}(\mathbf{B})`, the algebra of observables measurable in $`\mathbf{B}`. The empty
diamond is assigned the one-dimensional algebra $`\mathbb{C}\mathbf{1}` of multiples of the unit.

This axiom makes a theory an assignment of algebras to regions, not a field, and rules out
observables attached to single points.

## Axiom 2: isotony

An observable that can be measured in a diamond $`\mathbf{B}_1` can also be measured in any larger
diamond $`\mathbf{B}_2 \supseteq \mathbf{B}_1`. Since the algebras are abstract, "is also an element
of" must be supplied by a map. Isotony provides, for each such pair, a unital \*-monomorphism

$$`i_{\mathbf{B}_1\mathbf{B}_2} : \mathfrak{U}(\mathbf{B}_1) \to \mathfrak{U}(\mathbf{B}_2),`

and requires these maps to be coherent:

$$`i_{\mathbf{B}\mathbf{B}} = \mathrm{id}, \qquad i_{\mathbf{B}_2\mathbf{B}_3} \circ i_{\mathbf{B}_1\mathbf{B}_2} = i_{\mathbf{B}_1\mathbf{B}_3} \quad\text{for } \mathbf{B}_1 \subseteq \mathbf{B}_2 \subseteq \mathbf{B}_3.`

Because the maps are unital, every local algebra shares the unit of
$`\mathfrak{U}(\emptyset) = \mathbb{C}\mathbf{1}`, and $`\mathbf{1}` means the same thing in every
region. Because they are injective, they are isometric, and by spectral permanence an observable has
the same spectrum in every algebra it is embedded in.

Isotony rules out a theory in which enlarging the region of an experiment changes the observable
being measured.

## Axiom 3: local commutativity

If $`\mathbf{B}_1` and $`\mathbf{B}_2` are completely spacelike, their observables commute. To
multiply an element of $`\mathfrak{U}(\mathbf{B}_1)` by one of $`\mathfrak{U}(\mathbf{B}_2)`, both
must lie in one algebra. Isotony supplies one: the algebra of any diamond $`\mathbf{B}` containing
both regions, and in Minkowski spacetime such a diamond exists. The axiom states that for every such
$`\mathbf{B}`,

$$`i_{\mathbf{B}_1\mathbf{B}}(a_1)\, i_{\mathbf{B}_2\mathbf{B}}(a_2) = i_{\mathbf{B}_2\mathbf{B}}(a_2)\, i_{\mathbf{B}_1\mathbf{B}}(a_1) \qquad\text{for all } a_1 \in \mathfrak{U}(\mathbf{B}_1),\ a_2 \in \mathfrak{U}(\mathbf{B}_2).`

:::figure "diamond"
Two completely spacelike diamonds $`\mathbf{B}_1` and $`\mathbf{B}_2` inside a diamond
$`\mathbf{B}`. The dashed lines bound the causal future and past of $`\mathbf{B}_1`, which
$`\mathbf{B}_2` avoids.
:::

This is _Einstein causality_. Commuting observables can be measured together, and measuring one does
not change the statistics of the other (see the exercise below), so the axiom rules out signalling
faster than light. It does not rule out correlations: the vacuum of a quantum field is entangled
across spacelike separation.

## Axiom 4: the quasilocal algebra

The local algebras fit together into a single algebra. Take all the $`\mathfrak{U}(\mathbf{B})` and
identify each $`a \in \mathfrak{U}(\mathbf{B}_1)` with its images $`i_{\mathbf{B}_1\mathbf{B}_2}(a)`
in the larger algebras. The result is the _inductive limit_ of the local algebras (in
category-theory language, the directed colimit). Elements from $`\mathfrak{U}(\mathbf{B}_1)` and
$`\mathfrak{U}(\mathbf{B}_2)` are added or multiplied in any diamond containing both, and the
coherence laws of isotony make the answer independent of the choice; the norm is inherited, since
the embeddings are isometric. This normed \*-algebra completes to a C\*-algebra $`\mathfrak{U}`, the
_quasilocal algebra_. It comes with unital \*-monomorphisms
$`\iota_{\mathbf{B}} : \mathfrak{U}(\mathbf{B}) \to \mathfrak{U}`, compatible with isotony:
$`\iota_{\mathbf{B}_2} \circ i_{\mathbf{B}_1\mathbf{B}_2} = \iota_{\mathbf{B}_1}`.

An element of $`\mathfrak{U}` need not belong to any single diamond, but it is approximated
arbitrarily well, in norm, by elements that do: hence _quasilocal_. Local commutativity can equally
be stated in $`\mathfrak{U}`: $`\iota_{\mathbf{B}_1}(a_1)` and $`\iota_{\mathbf{B}_2}(a_2)` commute.

The 1964 axiom adds that $`\mathfrak{U}` contains "all observables of interest". This is a claim
about physics, not mathematics: it says that every quantity that can actually be measured is
represented by a self-adjoint element of $`\mathfrak{U}`. For a set $`S` of bounded operators, the
_commutant_ $`S'` is the set of bounded operators that commute with every element of $`S`. In a
representation $`\pi`, the bicommutant $`\pi(\mathfrak{U})'' = (\pi(\mathfrak{U})')'` is, by von
Neumann's bicommutant theorem, the closure of $`\pi(\mathfrak{U})` in the weak operator topology,
and it is in general larger than $`\pi(\mathfrak{U})`. But by the von Neumann density theorem, for
every $`T \in \pi(\mathfrak{U})''`, every finite set of vectors $`\psi_1, \dots, \psi_n` and every
$`\varepsilon > 0` there is an $`a \in \mathfrak{U}` with
$`\|\pi(a)\psi_k - T\psi_k\| < \varepsilon` for all $`k`, so no finite set of measurements
distinguishes them. What the principle rules out is a measurable quantity that cannot be
approximated by local observables.

## Axiom 5: Lorentz covariance

As you will recall, the Poincaré group consists of the maps $`x \mapsto \Lambda x + a` with
$`a \in \mathbb{R}^4` and $`\Lambda` a Lorentz transformation,
$`\eta(\Lambda v, \Lambda w) = \eta(v, w)`. (Haag and Kastler call it the inhomogeneous Lorentz
group, hence the name of the axiom.) It has four connected components. The component of the
identity, the proper orthochronous group, has $`\det\Lambda = 1` and $`\Lambda^0{}_0 \geq 1`; the
other three are reached by space and time reflections, which are not symmetries of nature (the weak
interaction violates parity), so the axiom uses only the identity component. Its elements $`L`
preserve $`\ll`, and therefore map diamonds to diamonds:
$`L(I^+(p) \cap I^-(q)) = I^+(Lp) \cap I^-(Lq)`.

The axiom provides, for each such $`L` and each diamond $`\mathbf{B}`, a unital \*-isomorphism

$$`\alpha_L : \mathfrak{U}(\mathbf{B}) \to \mathfrak{U}(L\mathbf{B}),`

with $`\alpha_e = \mathrm{id}` for the identity $`e` of the group,
$`\alpha_{L'L} = \alpha_{L'} \circ \alpha_L`, and compatibility with isotony,
$`\alpha_L \circ i_{\mathbf{B}_1\mathbf{B}_2} = i_{L\mathbf{B}_1\,L\mathbf{B}_2} \circ \alpha_L`.
The maps then extend, by continuity, to automorphisms of $`\mathfrak{U}`. The laws of physics are
thus the same at every place and in every inertial frame; the axiom rules out a preferred origin or
a preferred rest frame.

## An aside: primitivity

The 1964 list has a sixth axiom: $`\mathfrak{U}` is _primitive_, that is, it has a representation
that is both faithful (injective) and irreducible (no closed subspace other than $`0` and the whole
space is invariant). Its physical motivation is thin, and Haag's later account in _Local Quantum
Physics_ omits it. This project omits it too. For orientation: a commutative C\*-algebra is
primitive only if it is $`\mathbb{C}\mathbf{1}`, so the axiom excludes classical nets other than the
trivial one.

:::::exercise
Let $`\omega` be a state, a positive normalised expectation functional (defined in the next
section), and let $`P \in \mathfrak{U}(\mathbf{B}_1)` be a projection, $`P = P^* = P^2`. A
measurement of $`P` whose result is not recorded changes the state to
$`\omega'(b) = \omega(PbP) + \omega((\mathbf{1}-P)\,b\,(\mathbf{1}-P))`. Show that
$`\omega'(b) = \omega(b)` for every $`b` that commutes with $`P`, in particular for every $`b` in a
completely spacelike region. What does this say about signalling?

::::solution
If $`bP = Pb`, then $`PbP = bP^2 = bP` and
$`(\mathbf{1}-P)b(\mathbf{1}-P) = b(\mathbf{1}-P)^2 = b(\mathbf{1}-P)`, because $`\mathbf{1}-P` is
also a projection. The sum is $`bP + b - bP = b`, so $`\omega'(b) = \omega(b)`. By local
commutativity this holds for every observable $`b` of a region completely spacelike to
$`\mathbf{B}_1`: an observer there sees the same expectation values whether or not the measurement
in $`\mathbf{B}_1` took place, so the measurement cannot be used to send a signal.
::::
:::::

*In the library:* `Physicslib4.AQFT.HaagKastler.LocalNet`, `Physicslib4.AQFT.HaagKastler.Isotony`,
`Physicslib4.AQFT.HaagKastler.LocalCommutativity`, `Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra`
and `Physicslib4.AQFT.HaagKastler.LorentzCovariance`.

# States and the GNS construction

To make predictions, the axioms need a state: an assignment of expectation values to observables.

A _state_ on a unital C\*-algebra $`\mathfrak{A}` is a linear functional
$`\omega : \mathfrak{A} \to \mathbb{C}` that is

* _positive_: $`\omega(a^*a) \geq 0` for every $`a`;
* _normalised_: $`\|\omega\| = 1`, which for a positive functional is the same as
  $`\omega(\mathbf{1}) = 1`.

The number $`\omega(a)` is the expectation value of the observable $`a`. The familiar states of
quantum mechanics are examples: for a representation $`\pi` on $`\mathcal{H}`, a unit vector $`\psi`
gives the vector state $`\omega(a) = \langle \psi, \pi(a)\psi \rangle`, and a density matrix $`\rho`
gives $`\omega(a) = \operatorname{tr}(\rho\,\pi(a))`. The states form a convex set; its extreme
points, the states that are not mixtures of two others, are the _pure_ states. A state is _faithful_
if $`\omega(a^*a) > 0` whenever $`a \neq 0`.

## The GNS construction

A state determines a Hilbert space representation, uniquely up to unitary equivalence, by a theorem
of Gelfand, Naimark and Segal.

_Let $`\omega` be a state on a unital C\*-algebra $`\mathfrak{A}`. There are a Hilbert space
$`\mathcal{H}_\omega`, a representation $`\pi_\omega` of $`\mathfrak{A}` on it and a unit vector
$`\Omega_\omega` such that_

$$`\omega(a) = \langle \Omega_\omega, \pi_\omega(a)\,\Omega_\omega \rangle \quad\text{for all } a \in \mathfrak{A},`

_and $`\Omega_\omega` is cyclic: the vectors $`\pi_\omega(a)\Omega_\omega` are dense in
$`\mathcal{H}_\omega`. Any two such triples are related by a unitary map. If $`\omega` is faithful,
so is $`\pi_\omega`._

The proof builds the Hilbert space out of the algebra, in four steps.

1. *A semi-inner product.* Define $`\langle a, b \rangle = \omega(a^*b)` on $`\mathfrak{A}`. It is
   linear in $`b`, conjugate-linear in $`a`, and $`\langle a, a \rangle \geq 0` by positivity, so it
   satisfies the Cauchy–Schwarz inequality $`|\omega(a^*b)|^2 \le \omega(a^*a)\,\omega(b^*b)`. It is
   not an inner product, because $`\omega(a^*a)` may vanish for $`a \neq 0`.
2. *The null space.* Let $`\mathcal{N} = \{n : \omega(n^*n) = 0\}`. By Cauchy–Schwarz,
   $`\mathcal{N}` is a subspace and a left ideal: $`an \in \mathcal{N}` for all $`a` and all
   $`n \in \mathcal{N}`. On the quotient $`\mathfrak{A}/\mathcal{N}`, the form
   $`\langle [a], [b] \rangle = \omega(a^*b)` is well defined and is an inner product.
3. *Completion and representation.* $`\mathcal{H}_\omega` is the completion of
   $`\mathfrak{A}/\mathcal{N}`. The algebra acts by left multiplication, $`\pi_\omega(a)[b] = [ab]`,
   which is well defined because $`\mathcal{N}` is a left ideal, and bounded,
   $`\|[ab]\| \le \|a\|\,\|[b]\|`, because $`b^*a^*ab \le \|a\|^2\, b^*b`. It extends to the
   completion, and $`\pi_\omega(a^*) = \pi_\omega(a)^*` follows from
   $`\omega((a^*b)^*c) = \omega(b^*(ac))`.
4. *The cyclic vector.* $`\Omega_\omega = [\mathbf{1}]`. Then $`\pi_\omega(a)\Omega_\omega = [a]`,
   so these vectors are all of $`\mathfrak{A}/\mathcal{N}`, which is dense, and
   $`\langle \Omega_\omega, \pi_\omega(a)\Omega_\omega \rangle = \omega(\mathbf{1}^*a) = \omega(a)`.

Here the unit is used: without it there is no vector $`[\mathbf{1}]`. Uniqueness comes from mapping
$`\pi_1(a)\Omega_1 \mapsto \pi_2(a)\Omega_2`, which preserves inner products because both equal
$`\omega(a^*b)`. Faithfulness: if $`\pi_\omega(a) = 0`, then $`[a] = 0`, so $`\omega(a^*a) = 0` and,
for faithful $`\omega`, $`a = 0`.

The GNS construction connects the abstract algebras to the Hilbert spaces of ordinary quantum
theory: applied to a state on $`\mathfrak{U}`, it gives the Hilbert space of the theory in that
state, with $`\pi_\omega(a)` the operator of the observable $`a`. The state is pure exactly when
$`\pi_\omega` is irreducible.

## The vacuum

A _vacuum state_ is a state $`\omega` on $`\mathfrak{U}` that is invariant and has positive energy.

It is _invariant_ if $`\omega \circ \alpha_L = \omega` for every $`L` in the identity component of
the Poincaré group. Then $`U(L)\,\pi_\omega(a)\Omega_\omega = \pi_\omega(\alpha_L a)\Omega_\omega`
defines unitaries on $`\mathcal{H}_\omega` that represent the group, leave $`\Omega_\omega` fixed
and implement the symmetry: $`U(L)\,\pi_\omega(a)\,U(L)^{-1} = \pi_\omega(\alpha_L a)` (see the
second exercise below).

Recall Stone's theorem: a strongly continuous one-parameter group of unitaries has the form
$`U(t) = e^{itH}` with a self-adjoint, in general unbounded, generator $`H`. For the time
translations, $`H` is the Hamiltonian. _Positive energy_, or the _spectrum condition_, requires that
for every future-directed timelike vector $`a` the translations $`t \mapsto U(ta)` form such a group
with nonnegative generator; equivalently, the joint spectrum of the energy-momentum operators lies
in the closed forward light cone. This makes the vacuum a state of lowest energy.

## Superselection sectors

Different states can give inequivalent representations of the same algebra $`\mathfrak{U}`. Two
irreducible representations $`\pi_1` and $`\pi_2` are either unitarily equivalent or _disjoint_: no
nonzero bounded operator $`T` satisfies $`T\pi_1(a) = \pi_2(a)T` for all $`a`. The equivalence
classes of the irreducible representations of physical interest are the _superselection sectors_ of
the theory, labelled by conserved charges such as electric charge. No observable in $`\mathfrak{U}`
connects two sectors, so a superposition of state vectors from different sectors cannot be told
apart from the corresponding mixture: the relative phase is not measurable.

:::::exercise
Let $`\mathfrak{A} = M_2(\mathbb{C})` and $`\omega(a) = a_{11}`, the state given by the unit vector
$`e_1`. Find $`\mathcal{N}`, $`\mathcal{H}_\omega`, $`\pi_\omega` and $`\Omega_\omega`. What changes
for the faithful state $`\omega(a) = \tfrac{1}{2}\operatorname{tr} a`?

::::solution
$`\omega(n^*n) = (n^*n)_{11} = \|n e_1\|^2`, so $`\mathcal{N}` is the set of matrices whose first
column is zero. The map $`[a] \mapsto a e_1` identifies $`\mathfrak{A}/\mathcal{N}` with
$`\mathbb{C}^2`, preserving inner products since $`\omega(a^*b) = \langle a e_1, b e_1 \rangle`.
Under it, $`\pi_\omega(a)` is the matrix $`a` acting on $`\mathbb{C}^2` and $`\Omega_\omega = e_1`:
the GNS construction returns the defining representation. For
$`\omega = \tfrac12 \operatorname{tr}`, $`\mathcal{N} = 0`, and $`\mathcal{H}_\omega` is
$`M_2(\mathbb{C})` itself, four-dimensional, with
$`\langle a, b \rangle = \tfrac12 \operatorname{tr}(a^*b)`. The algebra acts by left multiplication
and $`\Omega_\omega = \mathbf{1}`. The representation is faithful but reducible: the two columns of
a matrix are invariant subspaces, each a copy of $`\mathbb{C}^2`. This matches the facts that the
first state is pure and the second is a mixture.
::::
:::::

:::::exercise
Show that the operators $`U(L)` defined above for an invariant state are well defined and preserve
inner products.

::::solution
For $`a, b \in \mathfrak{U}`,

$$`\langle \pi_\omega(\alpha_L a)\Omega_\omega, \pi_\omega(\alpha_L b)\Omega_\omega \rangle = \omega(\alpha_L(a^*b)) = \omega(a^*b) = \langle \pi_\omega(a)\Omega_\omega, \pi_\omega(b)\Omega_\omega \rangle,`

using that $`\alpha_L` is a \*-homomorphism and that $`\omega` is invariant. So the map preserves
inner products on the dense set of vectors $`\pi_\omega(a)\Omega_\omega`. In particular, if
$`\pi_\omega(a)\Omega_\omega = 0`, its image has norm zero, so the map is well defined. It extends
by continuity to an isometry of $`\mathcal{H}_\omega`, and it is onto because $`U(L^{-1})` inverts
it.
::::
:::::

*In the library:* `Physicslib4.GNS.State`, `Physicslib4.GNS.gns_construction`, and for the vacuum
`Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumState`.

# What this project sharpens

The axioms of {citet haagKastler1964}[] leave open some details that a proof needs. The project's
blueprint fixes them, and the formal statements are checked against the blueprint. The forms above
differ from the 1964 text in these points.

* *Topology and regions.* Minkowski spacetime carries the Alexandrov topology, and the regions are
  the causal diamonds, including the empty one, rather than all open sets with compact closure in an
  unnamed topology.
* *The unit.* The 1964 isotony axiom allows the two algebras of each nested pair to have a common
  unit or neither to have one. Here all have one, fixed by
  $`\mathfrak{U}(\emptyset) = \mathbb{C}\mathbf{1}` and unital embeddings; the GNS construction
  needs it.
* *Isotony as data.* "$`\mathfrak{U}(\mathbf{B}_1) \subset \mathfrak{U}(\mathbf{B}_2)`" becomes a
  chosen family of \*-monomorphisms with identity and composition laws, without which the union of
  the local algebras has no well-defined product.
* *Local commutativity in a containing diamond,* using only the net and isotony; in Minkowski
  spacetime this is equivalent to commutation in $`\mathfrak{U}`.
* *The quasilocal algebra is constructed* from the local algebras and isotony, not assumed. The
  claim that it contains all observables of interest is kept apart as a physical principle.
* *The symmetry group.* Covariance uses the identity component of the Poincaré group, and the
  transported algebras must respect isotony.
* *Primitivity* is dropped.

The sharpened axioms carry over to a curved spacetime, a four-dimensional Lorentzian manifold used
as a fixed classical background, provided its Alexandrov topology is Hausdorff (equivalently, the
spacetime is strongly causal; the Alexandrov and manifold topologies then agree). The local algebras
and isotony are unchanged, and the Poincaré group is replaced by the isometries connected to the
identity.

One thing fails: two diamonds need not lie in a common diamond. In a Schwarzschild black hole, a
diamond just below the singularity and a diamond outside the horizon at sufficiently late times have
none: the top vertex of a common diamond would have to lie in the future of both, and inside the
hole the future of the first ends on the singularity before it meets the future of the second. Their
algebras then lie in no common algebra, and there is no quasilocal algebra. Local commutativity is
stated, as above, inside every diamond that contains both regions, and says nothing when there is
none: no experiment could compare the two. "All observables of interest" becomes a statement about
the local algebras.

This differs from the locally covariant framework of {citet brunettiFredenhagenVerch2003}[], in
which a theory is a functor on a category of globally hyperbolic spacetimes; here it is a net on one
fixed spacetime. Later chapters develop both the Minkowski and the curved-spacetime axioms in Lean.

:::::exercise
Let $`M` be the strip $`-1 < x^0 < 1` of two-dimensional Minkowski space, with the causal structure
of Minkowski space. Show that two small diamonds centred at $`(0, 0)` and $`(0, 10)` lie in no
common diamond of $`M`.

::::solution
A diamond of $`M` is $`I^+(p) \cap I^-(q)` with $`p, q \in M`, so $`q^0 - p^0 < 2`. A point $`x` of
it satisfies $`|x^1 - p^1| < x^0 - p^0` and $`|q^1 - x^1| < q^0 - x^0`. Adding the two inequalities,
$`|2x^1 - p^1 - q^1| < q^0 - p^0 < 2`, so all points of the diamond have $`x^1` within $`1` of
$`(p^1 + q^1)/2`. The two given diamonds contain points whose $`x^1` coordinates differ by almost
$`10`, so no diamond of $`M` contains both.
::::
:::::

*In the library:* the curved-spacetime net is `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet`,
and the physical principle of the quasilocal algebra is
`Physicslib4.AQFT.HaagKastler.ObservableCorrespondence`.

# Further reading

* Rudolf Haag, [_Local Quantum Physics: Fields, Particles,
  Algebras_](https://doi.org/10.1007/978-3-642-61458-3), 2nd edition, Springer, 1996. The standard
  monograph.
* {citehere haagKastler1964}[] The paper that introduced the axioms.
* {citehere brunettiFredenhagenVerch2003}[] The locally covariant framework, on all globally
  hyperbolic spacetimes at once.
* {citehere grossi2024}[] A clear introduction to C\*-algebras, states, the GNS construction and
  nets, whose proof of the GNS theorem the blueprint follows.
* The [physicslib4 blueprint](https://physicslib.github.io/physicslib4/blueprint/). Chapters 1 to 9
  discuss each 1964 axiom and the choices made in sharpening it; Chapter 10 states the sharpened
  axioms and the results proved about them.
