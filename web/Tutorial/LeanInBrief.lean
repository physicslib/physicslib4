import VersoManual
import Tutorial.Meta
import Tutorial.Papers
import Physicslib4.AQFT.HaagKastler.Net
import Physicslib4.GNS.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Tutorial

#doc (Manual) "Lean in brief" =>

%%%
tag := "lean-in-brief"
%%%

This chapter teaches enough Lean to read the library: its definitions, its statements and its
proofs. It assumes no experience with a proof assistant. By the end you should be able to take a
declaration such as `LocalNet` or `LocalCommutativity`, say what it means in the language of
chapter 1, follow a short proof step by step, and write a small proof of your own. It does not
teach Lean in general; the books listed at the end do that.

Every piece of Lean code in this chapter is checked by Lean against the library when the tutorial
is built. Hover over a name to see its type. In a proof, click a tactic to show or hide the goal
that remains after it. The exercises can be read here, but not run: chapter 4 explains how to set up
Lean on your own machine and work with the library there.

# What a proof assistant does

%%%
tag := "lean-in-brief-checking"
%%%

A _proof assistant_ is a program that checks mathematical definitions and proofs written in a
formal language. Lean 4 is both a programming language and a proof assistant. You write
definitions, statements and proofs in a file; Lean reads each one, fills in the details you leave
implicit (types, coercions, routine arguments), and then checks the result. The final check is done
by a small program called the _kernel_, which knows only a few rules of logic. Everything else in
Lean, including the automation that finds proofs for you, produces a proof that the kernel must
accept. To trust a theorem you therefore trust the kernel, a few standard axioms, and the
statement itself: that it says what you mean.

A wrong proof is rejected. Here Lean is asked to prove $`2 + 2 = 5` by computation and refuses:

```lean +error (name := twoTwoFive)
example : 2 + 2 = 5 := by
  rfl
```

```leanOutput twoTwoFive
Tactic `rfl` failed: The left-hand side
  2 + 2
is not definitionally equal to the right-hand side
  5

⊢ 2 + 2 = 5
```

The word `sorry` stands for a missing proof. Lean accepts a declaration that contains it, so that
you can work on the rest of a file, but warns that the declaration uses `sorry`. The exercises of
this chapter use it for the part you are to fill in.

```lean (name := sorryWarning)
example : 2 + 2 = 4 := by
  sorry
```

```leanOutput sorryWarning
declaration uses `sorry`
```

Two words describe the state of this library.

* A definition or theorem is _formalised_ when it is a Lean declaration whose statement matches the
  blueprint. Matching the blueprint is checked by people, not by Lean: Lean checks that a proof
  proves the statement, not that the statement is the one intended.
* The library is _sorry-free_: no proof in it contains `sorry`.

The command `#print axioms` lists the axioms a theorem depends on, and it is how the second point
is checked. Here it is for the theorem that the algebra of the empty region is commutative, a
consequence of Axiom 1:

```lean (name := axiomsEmpty)
open Physicslib4.AQFT.HaagKastler in
#print axioms LocalNet.mul_comm_algebra_empty
```

```leanOutput axiomsEmpty
'Physicslib4.AQFT.HaagKastler.LocalNet.mul_comm_algebra_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These three are the standard axioms of Lean's mathematics: propositional extensionality (two
equivalent statements are equal), the axiom of choice, and the soundness of quotients. A proof
with a gap would also list `sorryAx`.

:::::exercise
Why does a theorem whose proof uses `sorry` prove nothing, even though Lean accepts the file? And
why can `#print axioms` not tell you whether a sorry-free theorem states the right thing?

::::solution
`sorry` is elaborated as the axiom `sorryAx`, which produces a term of any type, so it "proves"
every statement, false ones included. `#print axioms` lists what a proof depends on; it says nothing
about the statement. A sorry-free proof of a statement that misrepresents the mathematics (a wrong
definition, a hypothesis that can never hold) is still a correct proof of that statement. This is
why the project checks each statement against the blueprint by reading it.
::::
:::::

# Types and terms

%%%
tag := "lean-in-brief-types"
%%%

You will know that in ordinary mathematics everything is built from sets: a number, a function
and a Hilbert space are all sets, and $`x \in A` is a statement about two sets. Lean is built on a
different foundation, _type theory_. Every object has a _type_, and a _term_ of a type is an object
of that type. Writing `x : T` means "`x` is a term of type `T`". The type is part of what the object
is, not a property it may or may not have: a real number is a term of type `ℝ`, and the question
"is $`2 \in \mathbb{R}`?" does not arise, because `(2 : ℝ)` and `(2 : ℂ)` are different terms of
different types.

The command `#check` shows the type of a term, and `#eval` computes the value of a term when it can
be computed:

```lean (name := checkTwo)
#check (2 : ℝ)
```

```leanOutput checkTwo
2 : ℝ
```

```lean (name := evalSum)
#eval 2 + 3
```

```leanOutput evalSum
5
```

A function from `X` to `Y` is a term of type `X → Y`. It is written with `fun`, and applied by
juxtaposition: `f x` rather than $`f(x)`.

```lean (name := checkSquare)
#check fun x : ℝ => x ^ 2
```

```leanOutput checkSquare
fun x => x ^ 2 : ℝ → ℝ
```

A function of two arguments is a function that returns a function: `X → Y → Z` means
`X → (Y → Z)`, and `g x y` means `(g x) y`. The subsets of a type `X` form a type `Set X`, written
with the familiar set-builder notation:

```lean (name := checkSet)
#check {x : ℝ | 0 < x}
```

```leanOutput checkSet
{x | 0 < x} : Set ℝ
```

Types are themselves terms: `ℝ` has type `Type`, the type of types, as do `Set ℝ` and `ℝ → ℝ`.

## Points and regions

Minkowski spacetime is a term `StandardMinkowskiSpacetime` of type `Spacetime`, and the type of
its points is `StandardMinkowskiSpacetime.Carrier`, the field `Carrier` of the structure
`StandardMinkowskiSpacetime` ({ref "lean-in-brief-structures"}[section 5]). A region is a term of
type `Set StandardMinkowskiSpacetime.Carrier`. The library's names are long, because they are
organised in _namespaces_ ({ref "lean-in-brief-mathlib"}[section 7]); the command below makes the
short names available, and all the code that follows uses them.

```lean
open Physicslib4 Spacetime AQFT.HaagKastler
```

```lean (name := checkCarrier)
#check StandardMinkowskiSpacetime.Carrier
```

```leanOutput checkCarrier
StandardMinkowskiSpacetime.Carrier : Type
```

The diamond $`I^+(p) \cap I^-(q)` of chapter 1 is, in the library, the _chronological diamond_
`chronologicalDiamond M t p q`, for a spacetime `M`, a time orientation `t` and two points `p` and
`q`. The library keeps the name `causalDiamond` for the closed version $`J^+(p) \cap J^-(q)`, which
{ref "lean-in-brief-tactics"}[section 4] uses.

```lean (name := checkDiamond)
#check chronologicalDiamond
```

```leanOutput checkDiamond
Physicslib4.Spacetime.chronologicalDiamond (M : Spacetime) (t : M.TimeOrientation) (p q : M.Carrier) : Set M.Carrier
```

This is the form in which the library writes its declarations: the name, then the arguments, each
in parentheses with its type, then a colon and the type of the result. Here the result is a set of
points of `M`.

## Dependent functions

The arguments of `chronologicalDiamond` begin with `(M : Spacetime)`, and the types of the others
mention `M`: `t` is a time orientation _of `M`_, and `p` and `q` are points _of `M`_. As a type,
`chronologicalDiamond` is `(M : Spacetime) → M.TimeOrientation → M.Carrier → M.Carrier → Set
M.Carrier`. This is a _dependent function type_. The type of the output, or of later arguments,
depends on the value of an earlier argument. In mathematics such functions are common: a vector
field, a section of the tangent bundle, assigns to each point $`x` a vector in $`T_x M`, a space
that changes with $`x`. Lean writes the type of such a function as `(x : X) → T x`, or equivalently
`∀ x, T x`.

The net of chapter 1 is the central example. It assigns to each region $`\mathbf{B}` an algebra
$`\mathfrak{U}(\mathbf{B})`, and an observable of the region is an element
$`a \in \mathfrak{U}(\mathbf{B})`. In Lean, a net `U` has a function `U.algebra` from regions to
types, and an observable of `B` is a term `a : U.algebra B`, whose type depends on `B`. The notation
`U.algebra B` is short for `LocalNet.algebra U B`: when `U` has type `LocalNet`, Lean looks up
`algebra` in the namespace `LocalNet`. This "dot notation" is used throughout the library.

```lean (name := checkAlgebra)
#check LocalNet.algebra
```

```leanOutput checkAlgebra
Physicslib4.AQFT.HaagKastler.LocalNet.algebra.{u_1} (self : LocalNet) :
  Set StandardMinkowskiSpacetime.Carrier → Type u_1
```

(The `u_1` is a universe level; {ref "lean-in-brief-structures"}[section 5] explains it.)

:::::exercise
Replace `sorry` by the set of real numbers strictly between $`0` and $`1`, and by an element of the
local algebra of a region `B`.

```lean
example : Set ℝ := sorry

example (U : LocalNet)
    (B : Set StandardMinkowskiSpacetime.Carrier) :
    U.algebra B := sorry
```

::::solution
```lean
example : Set ℝ := {x | 0 < x ∧ x < 1}

example (U : LocalNet)
    (B : Set StandardMinkowskiSpacetime.Carrier) :
    U.algebra B := 1
```

Every local algebra is a unital C\*-algebra, so it has a unit `1` (and a zero `0`). Lean finds the
unit of `U.algebra B` by itself; {ref "lean-in-brief-structures"}[section 5] explains how.
::::
:::::

# Propositions and proofs

%%%
tag := "lean-in-brief-propositions"
%%%

You will be used to building statements from a few connectives: "for all" ($`\forall`), "there
exists" ($`\exists`), "implies" ($`\Rightarrow`), "and", "or", "not" and "if and only if". Lean
uses the same connectives, written `∀`, `∃`, `→`, `∧`, `∨`, `¬` and `↔`. A statement is a term of
the type `Prop`, the type of propositions:

```lean (name := checkProp)
#check 2 + 2 = 4
```

```leanOutput checkProp
2 + 2 = 4 : Prop
```

## Propositions as types

The step that makes Lean work is to treat each proposition as a type in its own right, whose terms
are its proofs. Writing `h : P` means "`h` is a proof of `P`". A true proposition has proofs, a
false one has none, and checking a proof means checking that a term has the type it claims. Each
connective then corresponds to a construction on types, and the proofs follow:

* A proof of `P → Q` is a function that turns any proof of `P` into a proof of `Q`. Using an
  implication `h : P → Q` on a proof `hp : P` is function application, `h hp`.
* A proof of `∀ x, P x` is a dependent function: for each `x`, a proof of `P x`. Applying it to a
  particular `a` gives `h a : P a`.
* A proof of `P ∧ Q` is a pair `⟨hp, hq⟩`; from `h : P ∧ Q`, the components are `h.1 : P` and
  `h.2 : Q`.
* A proof of `∃ x, P x` is a pair of a witness `a` and a proof of `P a`, written `⟨a, ha⟩`.
* `P ↔ Q` is a pair of implications, and `¬ P` is `P → False`.

## Theorems and examples

A theorem is written `theorem name (arguments) : statement := proof`. The arguments are the
objects and hypotheses of the statement. Here is one from the library, as `#check` shows it:

```lean (name := checkCausalOfChrono)
#check causallyPrecedes_of_chronologicallyPrecedes
```

```leanOutput checkCausalOfChrono
Physicslib4.Spacetime.causallyPrecedes_of_chronologicallyPrecedes (M : Spacetime) (t : M.TimeOrientation)
  {p q : M.Carrier} (h : p ≪[M, t] q) : p ≺[M, t] q
```

It says that chronological precedence implies causal precedence: if $`p \ll q`, then
$`p \prec q`. The library writes `p ≪[M, t] q` and `p ≺[M, t] q`, naming the spacetime and the
time orientation. Arguments in curly braces, like `{p q : M.Carrier}`, are _implicit_: you do not
supply them, because Lean can read them off the type of `h`. The hypothesis `h` is an argument like
any other, and the theorem itself is a function from proofs of `p ≪[M, t] q` to proofs of
`p ≺[M, t] q`.

As in chapter 1, `≺` is reflexive: `p ≺[M, t] p` always holds (`causallyPrecedes_refl`), the
trivial case `p = q`. The strict version, which asks for a genuine causal curve from `p` to `q`, is
`IsCausalTrip M t p q`:

```lean
example (M : Spacetime) (t : M.TimeOrientation)
    (p q : M.Carrier) :
    (p ≺[M, t] q) ↔ p = q ∨ IsCausalTrip M t p q :=
  causallyPrecedes_iff_eq_or_isCausalTrip M t
```

An `example` is a theorem without a name, checked and then forgotten. Here the theorem above is
used as a function:

```lean
example (M : Spacetime) (t : M.TimeOrientation)
    {p q : M.Carrier} (h : p ≪[M, t] q) : p ≺[M, t] q :=
  causallyPrecedes_of_chronologicallyPrecedes M t h
```

The simplest proofs are by definition. `rfl` proves `a = a`, and more generally an equation whose
two sides are equal once the definitions are unfolded; `Iff.rfl` does the same for `↔`. A point lies
in the diamond $`I^+(p) \cap I^-(q)` exactly when $`p \ll x` and $`x \ll q`, and in the library
this holds by definition, since an intersection is defined by "and" (the parentheses are needed
because of how the library's notation `≪[M, t]` parses):

```lean
example (M : Spacetime) (t : M.TimeOrientation)
    {p q x : M.Carrier} :
    x ∈ chronologicalDiamond M t p q ↔
      (p ≪[M, t] x) ∧ (x ≪[M, t] q) :=
  Iff.rfl
```

Since the two sides are the same proposition, a proof `h` of membership in the diamond is itself a
pair, and `h.1 : p ≪[M, t] x`.

:::::exercise
Replace each `sorry` by a proof term. The first statement says that a point of a diamond lies in
the chronological future of its lower vertex; the second, that a nonempty diamond has
$`p \ll q`. The library's theorem `chronologicallyPrecedes_trans M t` turns proofs of `p ≪[M, t] x`
and `x ≪[M, t] q` into a proof of `p ≪[M, t] q`.

```lean
example (M : Spacetime) (t : M.TimeOrientation)
    {p q x : M.Carrier}
    (h : x ∈ chronologicalDiamond M t p q) :
    p ≪[M, t] x :=
  sorry

example (M : Spacetime) (t : M.TimeOrientation)
    {p q x : M.Carrier}
    (h : x ∈ chronologicalDiamond M t p q) :
    p ≪[M, t] q :=
  sorry
```

::::solution
```lean
example (M : Spacetime) (t : M.TimeOrientation)
    {p q x : M.Carrier}
    (h : x ∈ chronologicalDiamond M t p q) :
    p ≪[M, t] x :=
  h.1

example (M : Spacetime) (t : M.TimeOrientation)
    {p q x : M.Carrier}
    (h : x ∈ chronologicalDiamond M t p q) :
    p ≪[M, t] q :=
  chronologicallyPrecedes_trans M t h.1 h.2
```

Membership in the diamond is, by definition, the conjunction `(p ≪[M, t] x) ∧ (x ≪[M, t] q)`, so
`h.1` and `h.2` are its two halves. This is the first half of the first exercise of chapter 1, in
Lean.
::::
:::::

# Tactic proofs

%%%
tag := "lean-in-brief-tactics"
%%%

Longer proofs are written not as one term but, after `by`, as a sequence of _tactics_:
instructions that build the term step by step. At each step Lean
keeps a _proof state_: the hypotheses available, and the _goal_ that remains to be proved. It is
displayed as

```
h₁ : hypothesis
h₂ : another hypothesis
⊢ goal
```

with the goal after the turnstile `⊢`. Each tactic changes the state, and the proof is finished
when no goals remain. Reading a tactic proof means following these states.

## A small vocabulary

Most proofs in the library use a handful of tactics, each the counterpart of a phrase of written
mathematics:

* `intro x hx`: "let `x` be arbitrary and suppose `hx`." It applies to a goal `∀ x, …` or `P → Q`.
* `exact e`: "this follows from `e`." It closes the goal with a term `e` of exactly that type.
* `apply f`: "by `f`, it suffices to show …." It replaces the goal by the hypotheses of `f` that
  are still needed.
* `constructor`: splits a goal `P ∧ Q` (or `P ↔ Q`) into two goals.
* `rcases h with ⟨a, ha⟩` (or `obtain ⟨a, ha⟩ := h`): takes apart a hypothesis `h : ∃ x, P x` or
  `h : P ∧ Q`: "choose `a` with `ha`."
* `rw [e]`: rewrites the goal with an equation `e : a = b` or an equivalence `e : P ↔ Q`,
  replacing the left side by the right. `rw [e] at h` rewrites a hypothesis instead.
* `simp`: simplifies the goal with a large collection of lemmas, and closes it if it becomes
  trivial.
* `calc`: a chain of equalities or inequalities, each step with its own proof.
* `linarith`: closes goals that follow from the hypotheses by linear arithmetic over an ordered
  field such as `ℝ`.

As an example of `constructor`, a point lies in a diamond if it lies above the lower vertex and
below the upper one. The goal is a membership, but `constructor` sees through its definition to
the conjunction, as `Iff.rfl` showed in {ref "lean-in-brief-propositions"}[section 3]. The two
goals it creates are each closed by `exact`; the dots `·` mark the proof of each goal.

```lean
example (M : Spacetime) (t : M.TimeOrientation)
    {p q x : M.Carrier}
    (hp : p ≪[M, t] x) (hq : x ≪[M, t] q) :
    x ∈ chronologicalDiamond M t p q := by
  constructor
  · exact hp
  · exact hq
```

Recall that a proof by cases splits a statement into finitely many cases that together cover all
possibilities. In Lean, `rcases h with h | h` splits a hypothesis `h : P ∨ Q` into the case `P` and
the case `Q`. Here $`x \cdot x \geq 0` is proved from the two cases $`x \geq 0` and
$`x \leq 0`, using two of Mathlib's lemmas:

```lean
example (x : ℝ) : 0 ≤ x * x := by
  rcases le_total 0 x with h | h
  · exact mul_nonneg h h
  · exact mul_nonneg_of_nonpos_of_nonpos h h
```

Proof by induction is the tactic `induction`, which the library seldom needs. Finally, `calc` and
`linarith` handle routine algebra, and `simp` routine simplification:

```lean
example (a b c : ℝ) (h₁ : a = b + 1) (h₂ : b = 2 * c) :
    a = 2 * c + 1 := by
  calc a = b + 1 := h₁
    _ = 2 * c + 1 := by rw [h₂]

example (a b : ℝ) (hab : a < b) : a < (a + b) / 2 := by
  linarith

example (s : Set ℝ) : s ∩ s = s := by
  simp
```

## Worked proof: the algebra of the empty region is commutative

Axiom 1 assigns to the empty region the algebra $`\mathfrak{U}(\emptyset) = \mathbb{C}\mathbf{1}`.
In the library this is a \*-isomorphism `U.emptyEquivComplex` from `U.algebra ∅` to `ℂ`, and the
library proves that `U.algebra ∅` is commutative (`LocalNet.mul_comm_algebra_empty`). On paper:
let $`\varphi : \mathfrak{U}(\emptyset) \to \mathbb{C}` be the isomorphism. Since $`\varphi` is
injective, it suffices to show $`\varphi(ab) = \varphi(ba)`. Since $`\varphi` is multiplicative,
this is $`\varphi(a)\varphi(b) = \varphi(b)\varphi(a)`, which holds because $`\mathbb{C}` is
commutative.

The Lean proof has the same three steps (the library writes the first as
`U.emptyEquivComplex.injective`). Below, the state after each tactic is shown under it.

:::goals
```lean
example (U : LocalNet) (a b : U.algebra ∅) :
    a * b = b * a := by
  apply EquivLike.injective U.emptyEquivComplex
  rw [map_mul, map_mul]
  exact mul_comm _ _
```
:::

* `apply EquivLike.injective U.emptyEquivComplex`: injectivity says that `φ x = φ y` implies
  `x = y`, so applying it leaves the goal `φ (a * b) = φ (b * a)`, with `φ` written out as
  `U.emptyEquivComplex`.
* `rw [map_mul, map_mul]`: Mathlib's lemma `map_mul` states `f (x * y) = f x * f y` for any
  multiplicative map `f`. The first rewrite applies it on the left, the second on the right.
* `exact mul_comm _ _`: the goal is now the commutativity of multiplication in `ℂ`, Mathlib's
  `mul_comm`. Its two arguments are written `_`, which asks Lean to find them from the goal.

## Worked proof: enlarging a causal diamond

The second exercise of chapter 1 enlarged a diamond by moving its vertices outwards. For the
library's causal diamonds $`J^+(p) \cap J^-(q)` (chapter 1 explains why the net does not use them),
the statement reads: if $`p' \prec p` and $`q \prec q'`, then
$`J^+(p) \cap J^-(q) \subseteq J^+(p') \cap J^-(q')`. On paper: let $`x` be a point of the first
diamond, so $`p \prec x` and $`x \prec q`. By transitivity, $`p' \prec x` and $`x \prec q'`, so
$`x` lies in the second.

The library states this for any spacetime as `causalDiamond_subset_of`. Here is its proof:

:::goals
```lean
example (M : Spacetime) (t : M.TimeOrientation)
    {p p' q q' : M.Carrier}
    (hp : p' ≺[M, t] p) (hq : q ≺[M, t] q') :
    causalDiamond M t p q ⊆ causalDiamond M t p' q' := by
  intro x hx
  rw [mem_causalDiamond] at hx ⊢
  rcases hx with ⟨hpx, hxq⟩
  exact ⟨M.causallyPrecedes_trans t hp hpx,
    M.causallyPrecedes_trans t hxq hq⟩
```
:::

* `intro x hx`: for sets, `A ⊆ B` is defined as `∀ x, x ∈ A → x ∈ B`, so `intro` applies. It adds
  the point `x` and the hypothesis `hx : x ∈ causalDiamond M t p q`, and the goal becomes
  `x ∈ causalDiamond M t p' q'`. (Lean displays `causalDiamond M t p q` as
  `M.causalDiamond t p q`, in dot notation; the two are the same term.)
* `rw [mem_causalDiamond] at hx ⊢`: the library's `mem_causalDiamond` says that
  `x ∈ causalDiamond M t p q` is equivalent to `(p ≺[M, t] x) ∧ (x ≺[M, t] q)`. The rewrite is
  done in `hx` and in the goal (written `⊢`).
* `rcases hx with ⟨hpx, hxq⟩`: splits the conjunction into `hpx : p ≺[M, t] x` and
  `hxq : x ≺[M, t] q`.
* `exact ⟨…, …⟩`: the goal is a conjunction, and `⟨…, …⟩` builds it from two proofs, each given
  by transitivity of `≺`, `causallyPrecedes_trans`.

:::::exercise
Prove that a nonempty causal diamond has $`p \prec q`. Recall that `s.Nonempty` means
`∃ x, x ∈ s`. (The library's version is `causallyPrecedes_of_causalDiamond_nonempty`.)

```lean
example (M : Spacetime) (t : M.TimeOrientation)
    {p q : M.Carrier}
    (h : (causalDiamond M t p q).Nonempty) :
    p ≺[M, t] q := by
  sorry
```

::::solution
:::goals
```lean
example (M : Spacetime) (t : M.TimeOrientation)
    {p q : M.Carrier}
    (h : (causalDiamond M t p q).Nonempty) :
    p ≺[M, t] q := by
  obtain ⟨x, hx⟩ := h
  rw [mem_causalDiamond] at hx
  rcases hx with ⟨hpx, hxq⟩
  exact M.causallyPrecedes_trans t hpx hxq
```
:::

`obtain` chooses a point `x` of the diamond; the rest is as in the worked proof.
::::
:::::

:::::exercise
In a C\*-algebra `A`, prove that $`a^*a` is self-adjoint: $`(a^*a)^* = a^*a`. Lean writes $`a^*`
as `star a`, and `[CStarAlgebra A]` says that `A` is a C\*-algebra (the square brackets are
explained in {ref "lean-in-brief-structures"}[section 5]). Mathlib's lemmas `star_mul : star (x * y) = star y * star x` and
`star_star : star (star x) = x` are what you need.

```lean
example (A : Type) [CStarAlgebra A] (a : A) :
    star (star a * a) = star a * a := by
  sorry
```

::::solution
:::goals
```lean
example (A : Type) [CStarAlgebra A] (a : A) :
    star (star a * a) = star a * a := by
  rw [star_mul, star_star]
```
:::

The first rewrite turns the left side into `star a * star (star a)`, the second into
`star a * a`. The two sides are then identical, and `rw` closes such a goal by itself.
::::
:::::

# Structures and type classes

%%%
tag := "lean-in-brief-structures"
%%%

In algebra, a structure is a set together with some data and some axioms: a
group is a set with a multiplication, a unit and inverses, such that the group laws hold. Lean
represents such a thing as a `structure`: a type whose terms are records of named _fields_. Some
fields are data (a set, an operation, a map) and some are proofs (the axioms). To give a term of a
structure, you give every field; to use one, you read off its fields with dot notation.

## The net of local algebras

Axiom 1 of chapter 1 assigns to each diamond a unital C\*-algebra, and to the empty diamond
$`\mathbb{C}\mathbf{1}`. In the library this is the structure `LocalNet`. Here is its
declaration, without the documentation comments of the source:

```
structure LocalNet where
  algebra : Set StandardMinkowskiSpacetime.Carrier → Type*
  instCStarAlgebra : ∀ B, CStarAlgebra (algebra B)
  emptyEquivComplex : StarAlgEquiv ℂ (algebra ∅) ℂ
```

```lean -show
universe u

example (algebra : Set StandardMinkowskiSpacetime.Carrier → Type u)
    [inst : ∀ B, CStarAlgebra (algebra B)]
    (e : StarAlgEquiv ℂ (algebra ∅) ℂ) : LocalNet.{u} :=
  ⟨algebra, inst, e⟩

example (U : LocalNet.{u}) : Set StandardMinkowskiSpacetime.Carrier → Type u := U.algebra
example (U : LocalNet) : ∀ B, CStarAlgebra (U.algebra B) := U.instCStarAlgebra
example (U : LocalNet) : StarAlgEquiv ℂ (U.algebra ∅) ℂ := U.emptyEquivComplex
```

The three fields are the three parts of the axiom.

* `algebra` assigns to each region `B` a type `U.algebra B`, the algebra $`\mathfrak{U}(\mathbf{B})`.
  (`Type*` means a type in some universe; see the aside below.) The family is indexed by all subsets
  of spacetime, for simplicity; only the diamonds (the empty one among them) are used, since the
  other axioms quantify over diamonds only.
* `instCStarAlgebra` gives, for each `B`, a C\*-algebra structure on `U.algebra B`: its addition,
  multiplication, norm, involution and the axioms relating them.
* `emptyEquivComplex` is a \*-isomorphism `U.algebra ∅ ≃⋆ₐ[ℂ] ℂ`: the normalisation
  $`\mathfrak{U}(\emptyset) = \mathbb{C}\mathbf{1}`.

## Isotony

Axiom 2 is a structure that takes the net as a parameter: `Isotony U` is the type of isotony data
for the net `U`. Its declaration, without documentation comments, and with the type
`Set StandardMinkowskiSpacetime.Carrier` of the regions written only once:

```
structure Isotony (U : LocalNet) where
  map : ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄,
    IsAlexandrovBasisSet B₁ → IsAlexandrovBasisSet B₂ →
      B₁ ⊆ B₂ → StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂)
  injective : ∀ ⦃B₁ B₂⦄ (h₁ : IsAlexandrovBasisSet B₁)
    (h₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂),
    Function.Injective (map h₁ h₂ h)
  map_self : ∀ ⦃B⦄ (h : IsAlexandrovBasisSet B),
    map h h (subset_refl B) = StarAlgHom.id ℂ (U.algebra B)
  map_comp : ∀ ⦃B₁ B₂ B₃⦄ (h₁ : IsAlexandrovBasisSet B₁)
    (h₂ : IsAlexandrovBasisSet B₂)
    (h₃ : IsAlexandrovBasisSet B₃)
    (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃),
    (map h₂ h₃ h₂₃).comp (map h₁ h₂ h₁₂) =
      map h₁ h₃ (h₁₂.trans h₂₃)
```

```lean -show
example (U : LocalNet) (i : Isotony U) {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) :
    StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂) := i.map h₁ h₂ h
example (U : LocalNet) (i : Isotony U) {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) :
    Function.Injective (i.map h₁ h₂ h) := i.injective h₁ h₂ h
example (U : LocalNet) (i : Isotony U) {B : Set StandardMinkowskiSpacetime.Carrier}
    (h : IsAlexandrovBasisSet B) :
    i.map h h (subset_refl B) = StarAlgHom.id ℂ (U.algebra B) := i.map_self h
example (U : LocalNet) (i : Isotony U) {B₁ B₂ B₃ : Set StandardMinkowskiSpacetime.Carrier}
    (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂)
    (h₃ : IsAlexandrovBasisSet B₃) (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃) :
    (i.map h₂ h₃ h₂₃).comp (i.map h₁ h₂ h₁₂) = i.map h₁ h₃ (h₁₂.trans h₂₃) :=
  i.map_comp h₁ h₂ h₃ h₁₂ h₂₃
example (U : LocalNet) (map : ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄,
      IsAlexandrovBasisSet B₁ → IsAlexandrovBasisSet B₂ → B₁ ⊆ B₂ →
        StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂))
    (inj : ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
      (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂),
      Function.Injective (map h₁ h₂ h))
    (self : ∀ ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄ (h : IsAlexandrovBasisSet B),
      map h h (subset_refl B) = StarAlgHom.id ℂ (U.algebra B))
    (comp : ∀ ⦃B₁ B₂ B₃ : Set StandardMinkowskiSpacetime.Carrier⦄
      (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂)
      (h₃ : IsAlexandrovBasisSet B₃) (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃),
      (map h₂ h₃ h₂₃).comp (map h₁ h₂ h₁₂) = map h₁ h₃ (h₁₂.trans h₂₃)) :
    Isotony U :=
  ⟨map, inj, self, comp⟩
```

Read against chapter 1, field by field:

* `map` is the family of embeddings $`i_{\mathbf{B}_1\mathbf{B}_2}`. Given two regions, proofs that
  both are diamonds (`IsAlexandrovBasisSet`, {ref "lean-in-brief-predicates"}[section 6]) and a proof of `B₁ ⊆ B₂`, it returns a
  \*-homomorphism `U.algebra B₁ →⋆ₐ[ℂ] U.algebra B₂`. Mathlib's \*-algebra homomorphisms
  preserve the unit, so these are unital. The proofs are arguments: the map exists only for nested
  diamonds.
* `injective` says that each embedding is injective, so the embeddings are \*-monomorphisms.
* `map_self` is the law $`i_{\mathbf{B}\mathbf{B}} = \mathrm{id}`.
* `map_comp` is the law $`i_{\mathbf{B}_2\mathbf{B}_3} \circ i_{\mathbf{B}_1\mathbf{B}_2} =
  i_{\mathbf{B}_1\mathbf{B}_3}`; `.comp` is composition, and `h₁₂.trans h₂₃` is the proof of
  `B₁ ⊆ B₃` obtained from the two inclusions.

The braces `⦃B₁ B₂⦄` mark _strict implicit_ arguments: like `{B₁ B₂}`, they are found by Lean, but
only once a later explicit argument, such as the proof `IsAlexandrovBasisSet B₁`, is supplied.

## Type classes

The fields of `LocalNet` give each `U.algebra B` a C\*-algebra structure, but the proofs above
multiply, take adjoints and use the unit without ever mentioning `instCStarAlgebra`. This is the
work of _type classes_. A type class is a structure that Lean is allowed to find by itself. Mathlib
defines `CStarAlgebra A`, the class of unital complex C\*-algebras, by extending the classes of
normed rings, rings with an involution (`StarRing`), complete spaces, rings satisfying the
C\*-identity (`CStarRing`), normed algebras over `ℂ`, and star modules over `ℂ`
($`(\lambda a)^* = \bar\lambda a^*`). A term of `CStarAlgebra A` is called an
_instance_.

An argument in square brackets, `[CStarAlgebra A]`, is an _instance argument_. It is not written
when the theorem is used: Lean searches its list of instances for one of the right type. The
library declares the field `instCStarAlgebra` to be an instance, so for every net `U` and region `B`
the search succeeds. `inferInstance` asks for that search explicitly:

```lean
example (U : LocalNet)
    (B : Set StandardMinkowskiSpacetime.Carrier) :
    CStarAlgebra (U.algebra B) :=
  inferInstance
```

Every theorem Mathlib proves for C\*-algebras therefore applies to every local algebra, such as the
C\*-identity $`\|a^*a\| = \|a\|^2` in $`\mathfrak{U}(\mathbf{B})`, from Mathlib's
`CStarRing.norm_star_mul_self`:

```lean
example (U : LocalNet)
    (B : Set StandardMinkowskiSpacetime.Carrier)
    (a : U.algebra B) :
    ‖star a * a‖ = ‖a‖ * ‖a‖ :=
  CStarRing.norm_star_mul_self
```

## The Haag–Kastler net

The structure `HaagKastlerNet` bundles the axioms. Without its documentation comments:

```
structure HaagKastlerNet where
  U : LocalNet.{u}
  isotony : Isotony U
  localCommutativity : LocalCommutativity U isotony
  lorentzCovariance : LorentzCovariance U isotony
```

```lean -show
example : (U : LocalNet.{u}) → (i : Isotony U) → LocalCommutativity U i →
    LorentzCovariance U i → HaagKastlerNet.{u} :=
  fun U i h₃ h₅ => ⟨U, i, h₃, h₅⟩
```

A Haag–Kastler net is a local net `U`, isotony data for it, and proofs of local commutativity and
Lorentz covariance for that isotony. The type of each field depends on the earlier ones: this is
the dependent typing of {ref "lean-in-brief-types"}[section 2] at work. The quasilocal algebra of Axiom 4 is not a field. As
chapter 1 explains, it is constructed from the net (`HaagKastlerNet.quasilocal`), and the claim
that it contains all observables of interest is kept apart as a physical principle.

## An aside on universes

`Type` is itself a term, of type `Type 1`, which has type `Type 2`, and so on. These levels,
called _universes_, avoid the paradox of a "type of all types", as set theory avoids a set of all
sets. A declaration can be stated for every universe at once by taking a _universe parameter_,
written `u` or `u_1`; `Type u` is then the universe at level `u`.

`LocalNet` has one: its field `algebra` returns types in `Type u_1`, so the algebras of a net may
live in any universe. A structure with such a field is one level higher:

```lean (name := checkLocalNet)
#check LocalNet
```

```leanOutput checkLocalNet
Physicslib4.AQFT.HaagKastler.LocalNet.{u_1} : Type (u_1 + 1)
```

`HaagKastlerNet` writes `LocalNet.{u}` for its field `U`, so that it, too, takes the universe as a
parameter rather than fixing it. In practice the algebras lie in `Type`, which is `Type 0`, and
`HaagKastlerNet.{0}` is the type of such nets. Most of the library can be read without thinking
about universes.

:::::exercise
Use `map_self` to show that the embedding of a diamond in itself fixes every element. After
rewriting with `i.map_self hB`, the goal is `(StarAlgHom.id ℂ (U.algebra B)) a = a`, which holds
by definition.

```lean
example (U : LocalNet) (i : Isotony U)
    {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B) (a : U.algebra B) :
    i.map hB hB (subset_refl B) a = a := by
  sorry
```

::::solution
:::goals
```lean
example (U : LocalNet) (i : Isotony U)
    {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B) (a : U.algebra B) :
    i.map hB hB (subset_refl B) a = a := by
  rw [i.map_self hB]
  rfl
```
:::
::::
:::::

:::::exercise
Show that every isotony embedding maps the unit to the unit. Mathlib's `map_one f` proves
`f 1 = 1` for any map `f` that preserves the unit.

```lean
example (U : LocalNet) (i : Isotony U)
    {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    (h₁ : IsAlexandrovBasisSet B₁)
    (h₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) :
    i.map h₁ h₂ h 1 = 1 :=
  sorry
```

::::solution
```lean
example (U : LocalNet) (i : Isotony U)
    {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    (h₁ : IsAlexandrovBasisSet B₁)
    (h₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) :
    i.map h₁ h₂ h 1 = 1 :=
  map_one _
```

This is why the unit $`\mathbf{1}` means the same thing in every region (chapter 1, Axiom 2): it
follows from the type of `map`, with no extra axiom.
::::
:::::

# Definitions that are propositions

%%%
tag := "lean-in-brief-predicates"
%%%

A `def` gives a name to a term. When the term is a proposition, the definition is a _predicate_:
`def P (x : X) : Prop := …` defines, for each `x`, the statement `P x`. Axiom 3 is of this kind: a
property of a net and its isotony maps, not data. `HaagKastlerNet` has a field holding a proof of
it.

## Diamonds

The simplest example is the predicate "is a diamond". Its signature, checked against the library:

```signature
def Physicslib4.AQFT.HaagKastler.IsAlexandrovBasisSet
    (B : Set StandardMinkowskiSpacetime.Carrier) : Prop
```

Its value is membership in `Spacetime.alexandrovBasis`, the basis of the Alexandrov topology,
which is the set of all intersections $`I^+(p) \cap I^-(q)`. Unfolding both definitions gives the
familiar statement, and `Iff.rfl` confirms that the two agree:

```lean
example (B : Set StandardMinkowskiSpacetime.Carrier) :
    IsAlexandrovBasisSet B ↔
      ∃ p q, B = chronologicalFuture
          StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation p ∩
        chronologicalPast
          StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation q :=
  Iff.rfl
```

Nothing requires $`p \ll q`, so the empty set is a diamond, as in chapter 1.

## Local commutativity

The signature of Axiom 3 shows that it is a property of a net `U` together with isotony data `i`:

```signature
def Physicslib4.AQFT.HaagKastler.LocalCommutativity
    (U : LocalNet) (i : Isotony U) : Prop
```

The isotony maps are needed because, as chapter 1 explains, elements of
$`\mathfrak{U}(\mathbf{B}_1)` and $`\mathfrak{U}(\mathbf{B}_2)` can only be multiplied in a common
algebra $`\mathfrak{U}(\mathbf{B})`. Here is the value of the definition, checked by `Iff.rfl`:

```lean
example (U : LocalNet) (i : Isotony U) :
    LocalCommutativity U i ↔
      ∀ ⦃B₁ B₂ B : Set StandardMinkowskiSpacetime.Carrier⦄
        (hB₁ : IsAlexandrovBasisSet B₁)
        (hB₂ : IsAlexandrovBasisSet B₂)
        (hB : IsAlexandrovBasisSet B),
        IsCompletelySpacelike StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation B₁ B₂ →
        (h₁ : B₁ ⊆ B) → (h₂ : B₂ ⊆ B) →
        ∀ (a : U.algebra B₁) (b : U.algebra B₂),
          Commute (i.map hB₁ hB h₁ a) (i.map hB₂ hB h₂ b) :=
  Iff.rfl
```

Read it line by line against Axiom 3:

1. for any three regions $`\mathbf{B}_1`, $`\mathbf{B}_2` and $`\mathbf{B}`,
2. that are diamonds,
3. such that $`\mathbf{B}_1` and $`\mathbf{B}_2` are completely spacelike,
4. and both lie in $`\mathbf{B}`,
5. for all $`a_1 \in \mathfrak{U}(\mathbf{B}_1)` and $`a_2 \in \mathfrak{U}(\mathbf{B}_2)`,
6. the images $`i_{\mathbf{B}_1\mathbf{B}}(a_1)` and $`i_{\mathbf{B}_2\mathbf{B}}(a_2)` commute.

Mathlib's `Commute x y` means `x * y = y * x`; a proof `h : Commute x y` gives the equation as
`h.eq`. Some hypotheses are named, like `(h₁ : B₁ ⊆ B) →`, because the last line uses them: the map
`i.map hB₁ hB h₁` needs the proof of the inclusion. A hypothesis is a term like any other, and
the statement may refer to it.

## States

The library's notion of state, `Physicslib4.GNS.State`, is a structure built on another one. For a
type `A` with `[CStarAlgebra A]`, and without documentation comments:

```
structure State extends A →L[ℂ] ℂ where
  isPositive : ∀ a : A, 0 ≤ toContinuousLinearMap (star a * a)
  isNormalized : ‖toContinuousLinearMap‖ = 1
```

```lean -show
open scoped ComplexOrder in
example (A : Type u) [CStarAlgebra A] : (f : A →L[ℂ] ℂ) →
    (∀ a : A, 0 ≤ f (star a * a)) → ‖f‖ = 1 → GNS.State A :=
  fun f hp hn => ⟨f, hp, hn⟩
```

`structure State extends A →L[ℂ] ℂ` means that a state has all the fields of a continuous
$`\mathbb{C}`-linear map $`A \to \mathbb{C}` (Mathlib's `A →L[ℂ] ℂ`), available as
`ω.toContinuousLinearMap`, and two more:

* `isPositive`: $`\omega(a^*a) \geq 0` for every `a`. The order on `ℂ` is Mathlib's: `0 ≤ z` holds
  when `z` is a nonnegative real number. It is made available by `open scoped ComplexOrder`.
* `isNormalized`: the operator norm of $`\omega` is $`1`.

These are the two conditions of chapter 1. The library also lets you apply a state directly, `ω a`,
in place of `ω.toContinuousLinearMap a`.

:::::exercise
Local commutativity states that `i.map hB₁ hB h₁ a` commutes with `i.map hB₂ hB h₂ b`. Derive the
equation in the other order, `i.map hB₂ hB h₂ b * i.map hB₁ hB h₁ a = i.map hB₁ hB h₁ a *
i.map hB₂ hB h₂ b`. Apply the hypothesis `hlc` to all its arguments, then use `.eq` and `.symm`
(which turns `x = y` into `y = x`).

```lean
example (U : LocalNet) (i : Isotony U)
    (hlc : LocalCommutativity U i)
    {B₁ B₂ B : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁)
    (hB₂ : IsAlexandrovBasisSet B₂)
    (hB : IsAlexandrovBasisSet B)
    (hs : IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
    (a : U.algebra B₁) (b : U.algebra B₂) :
    i.map hB₂ hB h₂ b * i.map hB₁ hB h₁ a =
      i.map hB₁ hB h₁ a * i.map hB₂ hB h₂ b :=
  sorry
```

::::solution
```lean
example (U : LocalNet) (i : Isotony U)
    (hlc : LocalCommutativity U i)
    {B₁ B₂ B : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁)
    (hB₂ : IsAlexandrovBasisSet B₂)
    (hB : IsAlexandrovBasisSet B)
    (hs : IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
    (a : U.algebra B₁) (b : U.algebra B₂) :
    i.map hB₂ hB h₂ b * i.map hB₁ hB h₁ a =
      i.map hB₁ hB h₁ a * i.map hB₂ hB h₂ b :=
  (hlc hB₁ hB₂ hB hs h₁ h₂ a b).eq.symm
```

The arguments `B₁`, `B₂` and `B` are strict implicit, so they are not written: Lean reads them off
`hB₁`, `hB₂` and `hB`. The proof term mirrors a sentence: "by local commutativity applied to these
regions and elements, the products agree; read the equation backwards."
::::
:::::

:::::exercise
Show that a state takes a nonnegative value on every element of the form $`a^*a`.

```lean
open scoped ComplexOrder in
example (A : Type) [CStarAlgebra A]
    (ω : GNS.State A) (a : A) :
    0 ≤ ω (star a * a) :=
  sorry
```

::::solution
```lean
open scoped ComplexOrder in
example (A : Type) [CStarAlgebra A]
    (ω : GNS.State A) (a : A) :
    0 ≤ ω (star a * a) :=
  ω.isPositive a
```

The field `isPositive` is a function that takes `a` and returns the proof. Its statement is about
`ω.toContinuousLinearMap (star a * a)`, and Lean accepts it for `ω (star a * a)` because the two
are equal by definition.
::::
:::::

# Mathlib and finding things

%%%
tag := "lean-in-brief-mathlib"
%%%

_Mathlib_ is Lean's community library of mathematics, covering much of undergraduate and graduate
mathematics. From it this library takes the real and complex numbers, sets, topologies, normed and
Hilbert spaces, continuous linear maps, manifolds, C\*-algebras (`CStarAlgebra`) and their
\*-homomorphisms (`→⋆ₐ[ℂ]`). It adds what physics needs on top: spacetimes and their causal
structure, the Alexandrov topology, nets of local algebras and the Haag–Kastler axioms. Where
Mathlib lacks a notion, the library defines it: Mathlib has no packaged type of states on a
C\*-algebra, so the library introduces `GNS.State`.

## Namespaces

Lean's names are hierarchical, like paths in a file system. The full name of the net is
`Physicslib4.AQFT.HaagKastler.LocalNet`: the declaration `LocalNet` in the _namespace_
`Physicslib4.AQFT.HaagKastler`. Source files open a namespace with `namespace … end`, and every
name declared inside receives the prefix. Three mechanisms keep the names short in use.

* `open Physicslib4 Spacetime AQFT.HaagKastler`, as in {ref "lean-in-brief-types"}[section 2], makes the names in those
  namespaces available without prefix, until the end of the file or section. `open … in` does the
  same for the next command only, as in the `#print axioms` example of {ref "lean-in-brief-checking"}[section 1].
* Dot notation, as in {ref "lean-in-brief-types"}[section 2]: if `U : LocalNet`, then `U.algebra` means `LocalNet.algebra U`,
  and `i.map_self` means `Isotony.map_self i`. Lean looks the name up in the namespace of the type.
* `open scoped` makes available only the notation and instances of a namespace, such as the order
  on `ℂ` in `open scoped ComplexOrder`.

Mathlib's names follow a convention that this library also uses: a theorem is named after its
statement, the conclusion first and the hypotheses after `_of_`. So `map_mul` says that a map
preserves multiplication, and `causallyPrecedes_of_chronologicallyPrecedes` proves causal
precedence from chronological precedence. With practice you can guess a name before looking it up.

## Searching

To find a theorem, there are four tools.

* [Loogle](https://loogle.lean-lang.org/) searches Mathlib by the shape of a statement. The query
  `‖star ?a * ?a‖` finds the theorems whose statement contains that expression, among them the
  C\*-identity `CStarRing.norm_star_mul_self`; `?a` stands for any term.
* The tactic `exact?`, used in place of a proof in your editor, searches for a theorem that
  closes the goal and suggests the proof it found.
* The API documentation lists every declaration with its signature and docstring, organised by
  namespace and file: [Mathlib's](https://leanprover-community.github.io/mathlib4_docs/) and
  [this library's](https://physicslib.github.io/physicslib4/docs/).
* The [blueprint](https://physicslib.github.io/physicslib4/blueprint/) states each definition and
  theorem of the project in ordinary mathematics. Each one names the Lean declarations that
  formalise it and links to their API documentation, and the dependency graph shows which are
  formalised. In the other direction, the docstrings in the library give the blueprint label.

Here is the documentation of `Isotony` as the API documentation shows it, with its docstring, the
blueprint label `def:isotony`, and the docstring of each field:

{docstring Physicslib4.AQFT.HaagKastler.Isotony +hideStructureConstructor}

:::::exercise
Mathlib proves that the involution of a C\*-algebra preserves the norm, $`\|a^*\| = \|a\|`
(chapter 1 proves it from the C\*-identity). Find the lemma, for instance with the Loogle query
`‖star ?a‖`, and use it.

```lean
example (A : Type) [CStarAlgebra A] (a : A) :
    ‖star a‖ = ‖a‖ :=
  sorry
```

::::solution
```lean
example (A : Type) [CStarAlgebra A] (a : A) :
    ‖star a‖ = ‖a‖ :=
  norm_star a
```

The lemma is `norm_star`. It holds in any normed group whose involution preserves the norm (the
class `NormedStarGroup`), and Lean finds by type class search that a C\*-algebra is one.
::::
:::::

:::::exercise
Using the naming convention, say what the library's theorem
`chronologicalFuture_subset_causalFuture` states, and check your answer with `#check`.

::::solution
"The chronological future is a subset of the causal future": $`I^+(p) \subseteq J^+(p)`.

```lean (name := checkFutureSubset)
#check chronologicalFuture_subset_causalFuture
```

```leanOutput checkFutureSubset
Physicslib4.Spacetime.chronologicalFuture_subset_causalFuture (M : Spacetime) (t : M.TimeOrientation) (p : M.Carrier) :
  M.chronologicalFuture t p ⊆ M.causalFuture t p
```
::::
:::::

# Further reading

* [_Theorem Proving in Lean 4_](https://lean-lang.org/theorem_proving_in_lean4/), by Jeremy
  Avigad, Leonardo de Moura, Soonho Kong and Sebastian Ullrich. The systematic introduction to
  Lean's logic: dependent types, propositions as types, tactics, structures and type classes.
* [_Mathematics in Lean_](https://leanprover-community.github.io/mathematics_in_lean/), by Jeremy
  Avigad and Patrick Massot. Formalising mathematics with Mathlib, by worked examples and
  exercises; the natural next step after this chapter.
* [_Functional Programming in Lean_](https://lean-lang.org/functional_programming_in_lean/), by
  David Thrane Christiansen. Lean as a programming language, for readers who want to understand
  the language itself.
* [_The Lean Language Reference_](https://lean-lang.org/doc/reference/latest/). The precise
  description of the language, its syntax, its elaborator and its tactics.
* [Mathlib's documentation](https://leanprover-community.github.io/mathlib4_docs/), and the
  [Mathlib community pages](https://leanprover-community.github.io/), with installation
  instructions, an overview of the library and the Zulip chat where questions are answered.
