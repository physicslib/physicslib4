import VersoManual
import Tutorial.Meta
import Tutorial.Papers
import Tutorial.WorkedExamples
import Physicslib4.AQFT.HaagKastler.Net
import Physicslib4.GNS.ExtremeState

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Tutorial

#doc (Manual) "Doing it yourself" =>

%%%
tag := "doing-it-yourself"
%%%

The first three chapters are written to be read in the browser. This one moves you onto your own
machine. By its end you should be able to build the library, run and change the tutorial's examples,
state a new result in the blueprint and in Lean, find the API you need, prove the result, and open a
pull request that passes the project's checks. The chapter follows one small project from start to
finish: a state on the quasilocal algebra of the trivial net, the construction that
{ref "worked-examples-gns"}[chapter 3] left open.

Commands to type in a terminal are shown as plain code blocks; they are not run when the tutorial
is built. Lean code is checked against the library, as in chapters 2 and 3. The code below uses
the short names of chapter 3:

```lean
open Physicslib4 Spacetime AQFT.HaagKastler
open scoped ComplexOrder
```

# Setting up

%%%
tag := "doing-it-yourself-setup"
%%%

## Installing Lean and building the library

Lean is installed through _elan_, which downloads and manages Lean versions. Each project names the
version it needs in a file `lean-toolchain` at its root, and elan fetches that version when you
first build the project, so you never install a Lean version by hand. The Lean community's
[installation guide](https://leanprover-community.github.io/get_started.html) covers each
operating system; on Linux and macOS it comes down to

```
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

and a new terminal. With `git` installed, fetch the library and build it:

```
git clone https://github.com/physicslib/physicslib4.git
cd physicslib4
lake exe cache get
lake build
```

_Lake_ is Lean's build tool, installed with elan. `lakefile.toml` names the project's dependencies,
Mathlib among them, and `lake-manifest.json` pins each to an exact commit.

* `lake exe cache get` downloads Mathlib's compiled files, several gigabytes: minutes on a fast
  connection, longer on a slow one. Without it, `lake build` would compile Mathlib itself, which
  takes hours. (`lake exe cache get!` downloads everything again, if a download was interrupted.)
* `lake build` then compiles the library's hundred-odd files. The first time takes a while (tens
  of minutes on a laptop is normal); later builds recompile only the files that changed and those
  that import them.

A build that ends without errors has checked every proof in the library.

## The editor

The standard editor is [VS Code](https://code.visualstudio.com/) with the _Lean 4_ extension.
Open the folder `physicslib4` itself, so that the extension finds `lean-toolchain`, and then a
library file, say `Physicslib4/AQFT/HaagKastler/Net.lean`, the home of chapter 3's trivial net.
A Lean server starts, loads the file's imports (seconds, once `lake build` has run) and checks the
file as you type. Three things are then at hand.

* The _infoview_, a panel beside the file (the ∀ menu, "Toggle Infoview"). With the cursor in a
  tactic proof it shows the goal at that point, as the `goals` blocks of chapters 2 and 3 do for a
  whole proof. Step through `trivialLocalNet_localCommutativity` and watch the goal change.
* _Hovers_, as on these pages: the type and docstring of a name. Ctrl-click (Cmd-click on macOS)
  jumps to its definition, in the library or in Mathlib.
* _Errors_ and warnings, underlined in the file and listed in the infoview. Lean checks past an
  error, so one mistake does not hide the next.

A file sees changes to the files it imports once they are saved and its server is restarted
("Lean 4: Server: Restart File").

## Running the tutorial's exercises

Create a file at the root of the repository, say `Playground.lean`, and start it with

```
import Physicslib4

open Physicslib4 Spacetime AQFT.HaagKastler
open scoped ComplexOrder InnerProductSpace
```

`import Physicslib4` loads the whole library, and Mathlib with it. Below, paste an exercise from
chapter 2 or 3, together with any definition from the text it uses, such as chapter 3's
`identityState`, and replace the `sorry` by a proof. The file is yours; do not commit it.

The tutorial itself is the Lean package in `web/`, one file per chapter: this one is
`web/Tutorial/DoingItYourself.lean`. Its Lean examples are checked when the package is built:

```
cd web
lake exe cache get
lake build
lake exe generate-tutorial --output _out/tutorial
```

The first `lake build` in `web/` compiles Verso, the tool that renders these pages, and the native
code of the modules it links, and takes a while. The last command writes the HTML to
`web/_out/tutorial/html-multi/`, and `web/README.md` explains how to view it. Change an example so
that it fails to check, and the build stops there.

:::::exercise
_Needs a local setup._ Build the library, open `Physicslib4/AQFT/HaagKastler/Net.lean`, and find
the proof of `trivialLocalNet_localCommutativity`. Put the cursor after `intro` and read the goal
in the infoview. Then replace `@mul_comm ℂ _ _ _` by `mul_comm` and read the error.

::::solution
After the `intro` the goal is the commutation of the two embedded elements, as in the worked proof
of {ref "worked-examples-trivial-net"}[chapter 3]. With plain `mul_comm`, the error is
`typeclass instance problem is stuck`, followed by `CommMagma ?m`: Lean needs a commutative
multiplication on some type, but the goal, a `Commute` statement about elements of
`trivialLocalNet.algebra B`, does not tell it which type, and it will not search for an instance on
an unknown one. Chapter 3 gave the fix: name the type, `@mul_comm ℂ _ _ _` or
`mul_comm (G := ℂ)`. Undo the change before going on.
::::
:::::

:::::exercise
_Needs a local setup._ Create `Playground.lean` as above and run the first exercise of
{ref "worked-examples-gns"}[chapter 3, section 2]: show that `identityState` is faithful.

::::solution
Paste the definition of `identityState` from chapter 3, then the exercise, and complete it:

```
example : identityState.IsFaithful := by
  intro a ha
  exact star_mul_self_pos_iff.mpr ha
```

The infoview shows the goal `0 < identityState (star a * a)` after `intro a ha`. If the file reports
an unknown identifier, check the `open` lines at its top.
::::
:::::

# How the project is organised

%%%
tag := "doing-it-yourself-organisation"
%%%

## The blueprint is the specification

As you will recall from chapter 1, the project's starting point is the blueprint, a document in
ordinary mathematics that sharpens the 1964 axioms of {citet haagKastler1964}[] where they are
under-specified. Its chapters 1 to 9 analyse the original axioms one by one and give the context;
only chapter 10 is formalised. Every definition and theorem of chapter 10 carries a label, such as
`def:state`, and names the Lean declarations that formalise it. A Lean statement is correct when it
says what its blueprint entry says, so it is checked against the blueprint, and not against the
1964 paper or a textbook. If you think the blueprint is wrong or imprecise, the fix starts there.

## Where things are

The repository has four parts.

* `Physicslib4/`: the library, by subject. `Spacetime/` and `Geometry/` hold spacetimes, their
  causal structure and the Alexandrov topology; `GNS/` states and the GNS construction;
  `Spectral/` and `Operators/` the spectral theorems, Stone's theorem and operator algebra;
  `Analysis/` supporting analysis; `AQFT/HaagKastler/` and `AQFT/HaagKastlerCurved/` the axioms
  in Minkowski and in curved spacetime. The file `Physicslib4.lean` imports every file of the
  library.
* `blueprint/src/`: the blueprint's LaTeX source; chapter 10 is in `sections/sec10/`, one file per
  section.
* `web/`: the project's website, this tutorial and the reference manual, which follows the
  sections of chapter 10 and collects the library's conventions.

The published versions are linked from the header of this page: the blueprint, with its dependency
graph, and the API documentation, generated from the docstrings.

## Conventions

A few rules keep the library and the blueprint in agreement.

* _Definitions are design decisions._ The topology on Minkowski space, the class of regions, and the
  fields of structures such as `LocalNet`, `Isotony` and `HaagKastlerNet` fix what the library
  means by a net. A change to them changes what every theorem says, so it is proposed and discussed
  in an issue before it is made. Theorems, lemmas and proofs can be added freely.
* _Restrictions are recorded._ When a declaration is deliberately less general than the blueprint
  intends, its docstring says so on a line starting `**Restriction:**`, naming the intended general
  form and what it is waiting on, in the form
  `**Restriction:** <restriction>; the intended form <general form>, and is waiting on <result>.`
  The line is removed when the general form is formalised.
* _Documentation is in the present tense._ Docstrings, comments, the blueprint and the home page
  describe what the project is, not how it came to be: no "previously" or "now". The history goes in
  `CHANGELOG.md`.
* _No `sorry`._ A `sorry` is useful while you work, as you will see, but the library contains none,
  and a contribution adds none.

:::::exercise
Find Einstein causality, `thrm:einstein-causality`, in the blueprint (the theorem of chapter 3's
third example), and follow it to the Lean. Which declarations formalise it, in which file, and which
blueprint entries does it use?

::::solution
The entry names two declarations, `HaagKastlerNet.einstein_causality` and
`HaagKastlerNet.exists_gns_einstein_causality`, both in the namespace
`Physicslib4.AQFT.HaagKastler` and in the file
`Physicslib4/AQFT/HaagKastler/EinsteinCausality.lean`.
It uses `def:haag-kastler-net`, `thrm:gns-construction-theorem` and `def:state`: the edges into
its node in the dependency graph.
::::
:::::

# From an idea to a statement

%%%
tag := "doing-it-yourself-statement"
%%%

The project of this chapter comes from the end of {ref "worked-examples-gns"}[chapter 3, section 2].
Every net has a quasilocal algebra `N.quasilocal`, chosen once and for all, and for the trivial net
it is isomorphic to $`\mathbb{C}`, but not literally `ℂ`. So `identityState` is not a state on it,
and the library constructs none. The claim to prove: _the quasilocal algebra of the
trivial net consists of the multiples of the unit, and has exactly one state,
$`\lambda\mathbf{1} \mapsto \lambda`._

## Start from the blueprint

A new result begins as a blueprint entry. In `blueprint/src/sections/sec10/haag-kastler-axioms.tex`,
next to the entries it depends on, it would read:

```
\begin{proposition}[The State of the Trivial Net]
    \label{prpstn:trivial-net-state}
    \uses{def:state, def:quasilocal-algebra}
    Let $\mathfrak{U}$ be the quasilocal algebra of the net that
    assigns $\mathbb{C}$ to every diamond. Every element of
    $\mathfrak{U}$ is a multiple $\lambda\mathbf{1}$ of the unit,
    and $\lambda\mathbf{1} \mapsto \lambda$ is the only state
    on $\mathfrak{U}$.
\end{proposition}
\begin{proof}
    \uses{def:quasilocal-algebra}
    Each local algebra is $\mathbb{C}$, so its image in $\mathfrak{U}$
    lies in $\mathbb{C}\mathbf{1}$. This subspace is finite-dimensional,
    hence closed, and the union of the images is dense, so
    $\mathfrak{U} = \mathbb{C}\mathbf{1}$. ...
\end{proof}
```

`\label` gives the entry its name. `\uses` lists the entries the statement, or the proof, depends
on; they become the edges of the dependency graph. Two more commands come later, once the Lean
exists: `\lean{…}`, with the full names of the declarations that formalise the entry (and
`\leanfile{…}`, this project's own addition, with their file), and `\leanok`, which marks the
statement as formalised when it is in the statement and the proof as formalised when it is in the
proof. The graph colours each node accordingly. Writing the proof on paper first is not a formality:
it tells you which lemmas the Lean proof needs.

## Translate it into Lean

The statement goes in the library next to what it uses. Here that is a new file,
`Physicslib4/AQFT/HaagKastler/TrivialState.lean`, which imports the files that define the trivial
net and `GNS.State.comp`, opens `namespace Physicslib4.AQFT.HaagKastler` like its neighbours, and
is added to `Physicslib4.lean`. The two claims, with `sorry` for their proofs:

```lean
example (x : trivialHaagKastlerNet.quasilocal.carrier) :
    ∃ z : ℂ, algebraMap ℂ _ z = x := by
  sorry

example (ω : GNS.State
      trivialHaagKastlerNet.quasilocal.carrier)
    (z : ℂ) :
    ω (algebraMap ℂ _ z) = z := by
  sorry
```

`algebraMap ℂ A` is Mathlib's name for the map $`\lambda \mapsto \lambda\mathbf{1}` of a complex
algebra `A`, and the underscore lets Lean fill in `A` from the type of `x`. The first statement
says that every element is a multiple of the unit; the second that every state takes the value
$`\lambda` on $`\lambda\mathbf{1}`, which, with the first, is uniqueness. Existence is a
construction, a term of type `GNS.State trivialHaagKastlerNet.quasilocal.carrier`, and
{ref "doing-it-yourself-project"}[section 6] builds it.

A `sorry` lets everything else be checked: Lean reports a warning, "declaration uses `sorry`", and
otherwise accepts the file. You can state all the lemmas of a proof this way, check that they fit
together, and fill them in one at a time.

## Check what the statement says

A Lean statement can fail to mean what you intend, and a proof of the wrong statement is worth
nothing. Before proving, check it.

* _Read it back._ Hover over each name, or `#check` the statement, and read the result as
  mathematics. Is `trivialHaagKastlerNet.quasilocal.carrier` the algebra the blueprint means? It is:
  the quasilocal algebra that every predicate of the library, such as `IsVacuumState`, refers to.
* _Beware of statements that are too easy._ The library's `trivialQuasilocalAlgebra` is also a
  quasilocal algebra of the trivial net, with carrier `ℂ`, and a state on it is just
  `identityState`. Stated for it, the project would be a one-liner, and would say nothing about the
  algebra that matters.
* _Beware of hypotheses that cannot hold._ A theorem with contradictory hypotheses is true and
  useless. If you suspect this, try to prove `False` from them.
* _Test special cases._ Specialise the statement to a case you can check by hand, or try to prove a
  slightly stronger one and see where it fails.

:::::exercise
State in Lean that every state on the quasilocal algebra of every Haag–Kastler net takes the value
$`1` on the unit, and prove it with the library's `GNS.State.apply_one`.

::::solution
```lean
example (N : HaagKastlerNet)
    (ω : GNS.State N.quasilocal.carrier) :
    ω 1 = 1 :=
  ω.apply_one
```

The net is an argument, as in chapter 3, so the statement holds for every net. The lemma holds for
a state on any C\*-algebra; dot notation finds it in the namespace `GNS.State`.
::::
:::::

:::::exercise
Is the following a faithful translation of "the quasilocal algebra of the trivial net has a
state"? What is wrong with it?

```lean
example : Nonempty (GNS.State ℂ) :=
  ⟨identityState⟩
```

::::solution
It is true, and proved, but it is a statement about `ℂ`, not about
`trivialHaagKastlerNet.quasilocal.carrier`. The two algebras are isomorphic, and the isomorphism
is precisely what the project has to construct. The faithful statement is
`Nonempty (GNS.State trivialHaagKastlerNet.quasilocal.carrier)`.
::::
:::::

# Finding the API

%%%
tag := "doing-it-yourself-api"
%%%

Most of the work in a proof is finding what already exists. The paper proof of the last section
needs three facts: a unital \*-homomorphism sends $`\lambda\mathbf{1}` to $`\lambda\mathbf{1}`; a
finite-dimensional subspace is closed; and a closed set that contains a set contains its closure.
All three are in Mathlib. Chapter 2 ({ref "lean-in-brief-mathlib"}[section 7]) listed several ways
to find them; here each is applied to one of the three.

## Guessing a name, and `#check`

Mathlib's naming convention suggests where to look. A \*-homomorphism is in particular an algebra
homomorphism, and for these the property "commutes with `algebraMap`" is called `commutes`.
`#check` confirms the guess:

```lean (name := checkCommutes)
#check AlgHomClass.commutes
  (trivialHaagKastlerNet.quasilocal.ι
    isAlexandrovBasisSet_trivialBasisSet)
```

```leanOutput checkCommutes
AlgHomClass.commutes
  (trivialHaagKastlerNet.quasilocal.ι
    isAlexandrovBasisSet_trivialBasisSet) : ∀ (r : ℂ),
  (trivialHaagKastlerNet.quasilocal.ι isAlexandrovBasisSet_trivialBasisSet)
      ((algebraMap ℂ (trivialHaagKastlerNet.U.algebra trivialBasisSet)) r) =
    (algebraMap ℂ trivialHaagKastlerNet.quasilocal.carrier) r
```

`AlgHomClass.commutes f r` holds for any algebra homomorphism `f`, \*-homomorphisms included,
and applying it to the embedding `ι` of one diamond (`trivialBasisSet`, the library's sample
diamond) shows what it says there: `ι` sends $`r\mathbf{1}` to $`r\mathbf{1}`. Applying a lemma
to the objects at hand is often the quickest way to read it.

## `exact?`, `apply?` and `rw?`

When the goal is a standard fact, let Lean search. `exact?` looks for a single lemma, applied to
hypotheses in context, that closes the goal:

```lean (name := exactClosure)
example {X : Type} [TopologicalSpace X] (s t : Set X)
    (ht : IsClosed t) (h : s ⊆ t) : closure s ⊆ t := by
  exact?
```

```leanOutput exactClosure
Try this:
  [apply] exact (IsClosed.closure_subset_iff ht).mpr h
```

Replace `exact?` by the suggestion, which in the editor is one click. `apply?` lists lemmas whose
conclusion matches the goal, leaving their hypotheses as new goals, and `rw?` lists equations
that can rewrite it. These searches work well for small, general facts. They fail, or time out,
when the goal is large or the lemma needs an argument that is not in context, and they see the
goal as written: a goal phrased with the library's own definitions may need `change` or `unfold`
first.

## Loogle

[Loogle](https://loogle.lean-lang.org/) searches Mathlib by the constants and patterns a statement
contains. The query `IsClosed, Submodule, FiniteDimensional` asks for statements that mention all
three, and among the first results is

```
Submodule.closed_of_finiteDimensional (s : Submodule 𝕜 E)
  [FiniteDimensional 𝕜 ↥s] : IsClosed ↑s
```

(with the hypotheses on the field `𝕜` and the space `E` omitted): a finite-dimensional subspace
of a Hausdorff topological vector space over a complete field is closed. Patterns with `?x` for
unknown terms, such as `closure ?s ⊆ ?t`, narrow the search further.

## Documentation and sources

The [API documentation](https://physicslib.github.io/physicslib4/docs/) lists each declaration of
the library, and Mathlib's lists each of Mathlib's, with its docstring and a link to its source.
From the blueprint, each entry links to the documentation of its Lean declarations, so a concept
you know in mathematics leads to its Lean name. Finally, the sources are on your disk: Mathlib is
in `.lake/packages/mathlib/Mathlib/`, and a text search such as

```
grep -rn "closed_of_finiteDimensional" .lake/packages/mathlib/Mathlib
```

finds the declaration first, and its file, where the lemmas around it are often the ones you need
next.

:::::exercise
_Needs a local setup._ Use `exact?` to find the lemma that `algebraMap ℂ A` is injective when the
C\*-algebra `A` is nonzero:

```lean
example (A : Type) [CStarAlgebra A] [Nontrivial A] :
    Function.Injective (algebraMap ℂ A) := by
  sorry
```

::::solution
`exact?` suggests `exact FaithfulSMul.algebraMap_injective ℂ A`:

```lean
example (A : Type) [CStarAlgebra A] [Nontrivial A] :
    Function.Injective (algebraMap ℂ A) :=
  FaithfulSMul.algebraMap_injective ℂ A
```

The kernel of a ring homomorphism out of a field is an ideal without $`1`, hence zero, so the map
is injective as soon as the target is nonzero. `(algebraMap ℂ A).injective` works as well.
::::
:::::

# Proving it

%%%
tag := "doing-it-yourself-proving"
%%%

## Working interactively

A Lean proof is written in a loop: read the goal in the infoview, take one step, read the new goal.
Each step should correspond to a sentence of the paper proof; if you cannot say which sentence, stop
and write it on paper first. Two habits help.

* _Keep the file checking._ Write `sorry` for whatever you have not done yet, so that Lean checks
  the rest and the infoview shows the goals that remain.
* _State intermediate facts._ `have h : P := by sorry` records a fact you will need, and you prove
  it once the main argument goes through. If the main argument does not go through, you have lost
  nothing.

## Breaking a proof into lemmas

A long proof is a sequence of lemmas, each a short statement with a short proof. The paper proof of
{ref "doing-it-yourself-statement"}[section 3] has four steps, and the Lean has four lemmas:
local elements are scalars; the scalars form a closed set; therefore every element is a scalar; and
therefore $`\lambda \mapsto \lambda\mathbf{1}` is a bijection. Small lemmas are easier to prove,
easier to read, and often useful elsewhere. A rule of thumb: if a proof does not fit on a screen,
or a `have` is used twice, make it a lemma.

## Common errors

Three kinds of error account for most of the time a beginner spends stuck. Each appeared, in a
mild form, in chapters 2 and 3.

_Type class problems._ Lean finds structure, such as a norm or a commutative multiplication, by type
class search ({ref "lean-in-brief-structures"}[chapter 2, section 5]). When the search fails, the
message says `failed to synthesize`; when Lean does not yet know the type to search on, it says
`typeclass instance problem is stuck`, as in the first exercise of
{ref "doing-it-yourself-setup"}[section 1]. Another case: a `GNS.State` can be applied to an element,
like a function, but it is not registered as a linear map, so Mathlib's `map_smul` does not apply to
it:

```lean +error (name := smulError)
example (ω : GNS.State ℂ) (z : ℂ) :
    ω (z • 1) = z • ω 1 := by
  rw [map_smul]
```

```leanOutput smulError
failed to synthesize instance of type class
  MulActionHomClass (GNS.State ℂ) ℂ ℂ ℂ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

`MulActionHomClass` is the class of maps that commute with scalar multiplication, and Lean finds no
instance saying that states are such maps. (The second error, an unsolved goal of the same type,
is a consequence of the first.) The fix is to apply the lemma to the state's underlying continuous
linear map, `ω.toContinuousLinearMap`, as in the exercise below.

_Universe mismatches._ Recall the aside on universes in
{ref "lean-in-brief-structures"}[chapter 2, section 5]: a structure such as `HaagKastlerNet.{u}` is
a family of types, one for each universe level.
The trivial net has its algebras in `Type`, so `nonempty_haagKastlerNet` is about level `0`, and
it cannot be used at level `1`:

```lean +error (name := univError)
example : Nonempty HaagKastlerNet.{1} :=
  nonempty_haagKastlerNet
```

```leanOutput univError
Type mismatch
  nonempty_haagKastlerNet
has type
  Nonempty.{2} HaagKastlerNet
but is expected to have type
  Nonempty.{3} HaagKastlerNet
```

The levels in the message are those of `Nonempty`, which records where its argument lives:
`HaagKastlerNet.{0}` is a type in `Sort 2`, `HaagKastlerNet.{1}` one in `Sort 3`. Different levels,
different types. Lean's display omits the level of `HaagKastlerNet` itself, so a mismatch in which
two types print identically is often a universe mismatch; `set_option pp.universes true` shows
the levels. The fix is to state the result at the level where it holds, or to generalise the
construction.

_Coercions._ A state `ω` is applied to `a` through a coercion to a function, displayed `ω a`; its
field `ω.toContinuousLinearMap` is applied through another. The two are equal by definition, but
`rw` looks for a term as written, not up to definitions:

```lean +error (name := coeError)
example (ω : GNS.State ℂ) :
    ω.toContinuousLinearMap 1 = 1 := by
  rw [ω.apply_one]
```

```leanOutput coeError
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ω 1
in the target expression
  ω.toContinuousLinearMap 1 = 1

ω : GNS.State ℂ
⊢ ω.toContinuousLinearMap 1 = 1
```

The fix is `change ω 1 = 1`, which replaces the goal by one equal to it by definition, followed by
the rewrite; or simply `exact ω.apply_one`, since `exact` does unfold definitions. Hover over the
terms in the infoview to see which coercion each uses.

:::::exercise
Fix the first failing example above: prove `ω (z • 1) = z • ω 1` for a state on `ℂ`.

::::solution
:::goals
```lean
example (ω : GNS.State ℂ) (z : ℂ) :
    ω (z • 1) = z • ω 1 := by
  change ω.toContinuousLinearMap (z • 1) =
    z • ω.toContinuousLinearMap 1
  rw [map_smul]
```
:::

`change` restates the goal in terms of the continuous linear map, to which it is equal by
definition. Then `rw [map_smul]` rewrites the left side to the right side, and `rw` closes the
goal by `rfl`.
::::
:::::

# The worked project

%%%
tag := "doing-it-yourself-project"
%%%

This section carries out the project of {ref "doing-it-yourself-statement"}[section 3] in full,
with the lemmas found in {ref "doing-it-yourself-api"}[section 4]. To keep the lines short, the
quasilocal algebra of the trivial net gets a local name:

```lean
noncomputable abbrev Q₀ :=
  trivialHaagKastlerNet.quasilocal
```

An `abbrev` is a definition that Lean unfolds freely, so type class search sees through `Q₀` to
the C\*-algebra structure of `trivialHaagKastlerNet.quasilocal.carrier`.

## Local elements are scalars

The algebra of every diamond is `ℂ`, so an element `a` of it is a number, and `ι` sends it to
$`a\mathbf{1}`. This is `AlgHomClass.commutes` applied to `ι`:

```lean
theorem trivial_ι_eq_algebraMap
    {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B)
    (a : trivialHaagKastlerNet.algebra B) :
    Q₀.ι hB a = algebraMap ℂ Q₀.carrier a :=
  AlgHomClass.commutes (Q₀.ι hB) a
```

The lemma's left side is `ι (algebraMap ℂ ℂ a)`, which is `ι a` by definition; on the right, Lean
accepts `a` as a complex number, although its type is the algebra of `B`, because the two types
are equal by definition.

## The scalars are closed

The multiples of the unit form the range of `Algebra.linearMap ℂ A`, the map
$`\lambda \mapsto \lambda\mathbf{1}` as a linear map. Its range is a finite-dimensional subspace,
so `Submodule.closed_of_finiteDimensional` applies:

```lean
theorem isClosed_range_algebraMap {A : Type*}
    [CStarAlgebra A] :
    IsClosed (Set.range (algebraMap ℂ A)) := by
  have h := (LinearMap.range
    (Algebra.linearMap ℂ A)).closed_of_finiteDimensional
  rwa [LinearMap.coe_range] at h
```

`h` says that the range, as a subspace, is closed. `LinearMap.coe_range` turns the subspace into
the set `Set.range (Algebra.linearMap ℂ A)`, which is the goal up to definitions, and `rwa` closes
it. The finite-dimensionality is found by type class search: the range of a linear map out of a
finite-dimensional space is finite-dimensional. The lemma holds in every C\*-algebra, so it is
stated for every C\*-algebra.

## Every element is a scalar

Now the paper argument: the union of the local images lies in the closed set of scalars, so its
closure does too, and the closure is everything.

:::goals
```lean
theorem trivial_exists_scalar (x : Q₀.carrier) :
    ∃ z : ℂ, algebraMap ℂ Q₀.carrier z = x := by
  have hsub :
      (⋃ (B : Set StandardMinkowskiSpacetime.Carrier)
        (hB : IsAlexandrovBasisSet B),
          Set.range (Q₀.ι hB)) ⊆
      Set.range (algebraMap ℂ Q₀.carrier) := by
    simp only [Set.iUnion_subset_iff]
    rintro B hB _ ⟨a, rfl⟩
    exact ⟨a, (trivial_ι_eq_algebraMap hB a).symm⟩
  have hcl :=
    isClosed_range_algebraMap.closure_subset_iff.mpr hsub
  exact hcl (Q₀.dense_range x)
```
:::

* `have hsub : … := by …` states the inclusion of the union of the images in the scalars. Its
  proof: `simp only [Set.iUnion_subset_iff]` turns "a union is contained in a set" into "each
  member is", and `rintro` introduces a diamond `B`, its proof `hB`, and an element of the range of
  `ι`, written `ι a` by the pattern `⟨a, rfl⟩`. Then `a` itself is the scalar.
* `have hcl := …` applies `IsClosed.closure_subset_iff`, found by `exact?` in section 4, to get
  the closure of the union inside the scalars.
* `exact hcl (Q₀.dense_range x)`: the field `dense_range` of a quasilocal algebra says that the
  union is dense, so `x` is in its closure, and hence a scalar.

## The isomorphism, and the state

The map $`\lambda \mapsto \lambda\mathbf{1}` is Mathlib's `StarAlgHom.ofId ℂ Q₀.carrier`. It is
surjective by the last lemma, and injective because the algebra is nonzero: `ι` is injective and
$`1 \neq 0` in `ℂ`.

:::goals
```lean
theorem trivial_bijective :
    Function.Bijective
      (StarAlgHom.ofId ℂ Q₀.carrier) := by
  refine ⟨?_, trivial_exists_scalar⟩
  have hB := isAlexandrovBasisSet_trivialBasisSet
  have h10 : (1 : Q₀.carrier) ≠ 0 := by
    intro h
    have h' : Q₀.ι hB 1 = Q₀.ι hB 0 := by
      rw [map_one, map_zero]
      exact h
    exact one_ne_zero (α := ℂ) (Q₀.ι_injective hB h')
  have : Nontrivial Q₀.carrier := ⟨⟨1, 0, h10⟩⟩
  exact FaithfulSMul.algebraMap_injective ℂ Q₀.carrier
```
:::

* `refine ⟨?_, trivial_exists_scalar⟩`: a bijection is a pair, injective and surjective. The
  second is the last lemma; `?_` leaves the first as the goal.
* `h10` proves $`1 \neq 0` in `Q₀.carrier`: if $`1 = 0`, then `ι 1 = ι 0` in the sample diamond,
  and injectivity of `ι` gives $`1 = 0` in its algebra, which is `ℂ`. Note `(α := ℂ)`, which
  names the type as in chapter 3: the algebra of the diamond is `ℂ` only by definition.
* `have : Nontrivial Q₀.carrier` puts the instance in context, and the lemma of the section 4
  exercise finishes.

A bijective \*-homomorphism is a \*-isomorphism (`StarAlgEquiv.ofBijective`). Its inverse is the
\*-homomorphism to `ℂ` the project needs, and the state is chapter 3's `identityState` pulled back
along it with `GNS.State.comp`:

```lean
noncomputable def trivialNetState :
    GNS.State Q₀.carrier :=
  identityState.comp
    (StarAlgEquiv.ofBijective _
      trivial_bijective).symm.toStarAlgHom

example (z : ℂ) :
    trivialNetState
      (algebraMap ℂ Q₀.carrier z) = z := by
  change identityState
    ((StarAlgEquiv.ofBijective _ trivial_bijective).symm
      (StarAlgEquiv.ofBijective _ trivial_bijective z))
    = z
  rw [StarAlgEquiv.symm_apply_apply]
  rfl
```

The check confirms that the state is $`\lambda\mathbf{1} \mapsto \lambda`: `change` writes
$`\lambda\mathbf{1}` as the image of $`\lambda` under the isomorphism, the isomorphism and its
inverse cancel, and `identityState z = z` by definition.

## Recording it

In the library the four lemmas and the definition go into the file of
{ref "doing-it-yourself-statement"}[section 3], each with a docstring giving the blueprint label.
The blueprint entry then gets its links and its marks:

```
\begin{proposition}[The State of the Trivial Net]
    \label{prpstn:trivial-net-state}
    \lean{Physicslib4.AQFT.HaagKastler.trivial_exists_scalar,
      Physicslib4.AQFT.HaagKastler.trivialNetState}
    \leanfile{Physicslib4/AQFT/HaagKastler/TrivialState.lean}
    \uses{def:state, def:quasilocal-algebra}
    \leanok
    ...
\end{proposition}
\begin{proof}
    \uses{def:quasilocal-algebra}
    \leanok
    ...
\end{proof}
```

The `\leanok` in the proof belongs there only once the whole proposition is proved in Lean,
uniqueness included, which is the exercise below; until then the proof carries none, and the
dependency graph shows the gap.

:::::exercise
Prove uniqueness: every state on `Q₀.carrier` agrees with `trivialNetState`. Write `x` as a
scalar with `trivial_exists_scalar`, then use `Algebra.algebraMap_eq_smul_one`, linearity of the
underlying continuous linear maps, as in section 5, and `GNS.State.apply_one`.

```lean
example (ω : GNS.State Q₀.carrier) (x : Q₀.carrier) :
    ω x = trivialNetState x := by
  sorry
```

::::solution
:::goals
```lean
example (ω : GNS.State Q₀.carrier) (x : Q₀.carrier) :
    ω x = trivialNetState x := by
  obtain ⟨z, rfl⟩ := trivial_exists_scalar x
  rw [Algebra.algebraMap_eq_smul_one]
  change ω.toContinuousLinearMap (z • 1) =
    trivialNetState.toContinuousLinearMap (z • 1)
  rw [map_smul, map_smul]
  change z • ω 1 = z • trivialNetState 1
  rw [ω.apply_one, trivialNetState.apply_one]
```
:::

`obtain ⟨z, rfl⟩` replaces `x` by `algebraMap ℂ _ z` everywhere. After rewriting it as `z • 1`, the
two `change` steps move between a state and its continuous linear map, so that `map_smul` applies
and then `apply_one` does. The final goal `z • 1 = z • 1` is closed by `rw`. With `DFunLike.ext`
this gives `ω = trivialNetState`: $`\mathfrak{U}` has exactly one state.
::::
:::::

# Checking and contributing

%%%
tag := "doing-it-yourself-checking"
%%%

## What CI checks

Every push and every pull request runs the workflow `.github/workflows/lean_action_ci.yml` on
GitHub. It checks, in order:

* that the library builds (`lake build`);
* that it passes the linters of Mathlib's companion library Batteries (`lake lint`): every
  definition has a docstring, no argument is unused, `simp` lemmas are in the right form, and so
  on;
* that `Physicslib4.lean` imports every file of the library (`lake exe mk_all --check`), so a new
  file must be added there;
* that every Lean name in a blueprint `\lean{…}` exists (`checkdecls`, from the package of the
  same name);
* that the documentation is in the present tense (`scripts/check_temporal_wording.py`), as
  {ref "doing-it-yourself-organisation"}[section 2] asked;
* when `web/`, the library or the toolchain changes, that the website and this tutorial build, and
  that their pages use no root-relative links.

A second workflow, `.github/workflows/blueprint.yml`, runs on the `main` branch only. It builds the
blueprint's web and PDF versions, the API documentation, the website and the tutorial, and
publishes them.

## Running the checks yourself

Run the checks before you push; it is faster than waiting for CI. From the root of the repository:

```
lake build
lake lint
lake exe mk_all --check
python3 scripts/check_temporal_wording.py
```

The blueprint needs `leanblueprint`, a Python package (`pip install leanblueprint`; it needs
Graphviz for the dependency graph and a LaTeX installation for the PDF; its README gives the
details per system). After a successful `lake build`,

```
leanblueprint web
leanblueprint pdf
leanblueprint checkdecls
```

build the blueprint into `blueprint/web/` and `blueprint/print/`, and then check the `\lean{…}`
names against the build (`checkdecls` reads the list of names that `leanblueprint web` writes). Open
`blueprint/web/index.html` and the dependency graph, and check that your entry and its edges look as
intended. For changes to the tutorial or the website, build them as in
{ref "doing-it-yourself-setup"}[section 1].

## Pull requests

Contributions follow the usual GitHub process. Create a branch, commit your work to it, and open a
pull request against `main`. A pull request is merged when it passes all the checks above, has no
conflicts with `main`, and is approved by a reviewer. A notable change, such as a new result, a
changed definition or a new section of the blueprint, also gets a line in `CHANGELOG.md`, under
"Unreleased"; that file, not the documentation, is where the project's history is recorded. Keep a
pull request to one topic: a reviewer can check one new result with its blueprint entry far more
easily than five.

When you are stuck, ask. The [Lean Zulip chat](https://leanprover.zulipchat.com/), in particular
its "new members" and "Is there code for X?" channels, answers questions about Lean and Mathlib,
usually within hours; a question with a short complete example that shows the problem gets the
best answers. Questions and proposals about this project, including proposed changes to its
definitions, go to the
[repository's issues](https://github.com/physicslib/physicslib4/issues).

:::::exercise
You add the file `Physicslib4/AQFT/HaagKastler/TrivialState.lean` of the worked project, with a
docstring on `trivialNetState` that reads "The state is now proved unique." You forget to add the
file to `Physicslib4.lean`. Which checks fail?

::::solution
Two. `lake exe mk_all --check` fails, because `Physicslib4.lean` does not import the new file. And
`scripts/check_temporal_wording.py` fails on "now proved", which narrates history; the docstring
should say "The state is unique." Note that `lake build` passes: it builds only what
`Physicslib4.lean` imports, so the new file is not even compiled, and an error in it would go
unnoticed, which is one reason for the import check. If the blueprint entry of section 6 is
already in place, `checkdecls` fails too: its `\lean{…}` names are declared in a file that is not
built.
::::
:::::

# Where to go next

%%%
tag := "doing-it-yourself-next"
%%%

The library formalises every entry of the blueprint's chapter 10, so new work extends the
blueprint as well as the Lean. Some directions, from small to large:

* _The vacuum of the trivial net._ Chapter 3 noted that the library constructs no vacuum state
  for any net. `trivialNetState` is the candidate for the trivial net: it is invariant (the
  exercise below), and the spectrum condition should hold in a one-dimensional GNS space where
  every translation acts as the identity.
* _A net with quantum physics in it._ The free scalar field, as a net of Weyl algebras with its
  Fock vacuum, would be the first model whose local algebras are not commutative.
* _Restrictions._ A declaration that is less general than intended says so in a
  `**Restriction:**` line, naming what it waits on; `grep -rn "Restriction:" Physicslib4` lists
  them, and each is a ready-made project. The search can come back empty, when every declaration
  has its intended general form.
* _Mathlib._ Results proved here that are not about physics, such as the extension of a
  \*-homomorphism from a dense \*-subalgebra (`exists_starAlgHom_extend_of_dense`), belong in
  Mathlib, where everyone can use them.

The reference manual, linked from the header, is in preparation. It is the companion to this
tutorial, meant to describe the library's definitions and theorems systematically where the
tutorial teaches by example. For Lean and Mathlib themselves, the further reading at the end of
{ref "lean-in-brief"}[chapter 2] is the place to continue, with _Mathematics in Lean_ first; for
the physics, the further reading at the end of {ref "aqft-in-brief"}[chapter 1], and the
blueprint.

:::::exercise
Show that `trivialNetState` is invariant under the covariance action of the trivial net, the first
half of the vacuum conditions. A \*-automorphism, like any algebra homomorphism, satisfies
`AlgHomClass.commutes`.

```lean
example : trivialHaagKastlerNet.IsInvariantState
    trivialNetState := by
  sorry
```

::::solution
:::goals
```lean
example : trivialHaagKastlerNet.IsInvariantState
    trivialNetState := by
  intro L a
  obtain ⟨z, rfl⟩ := trivial_exists_scalar a
  rw [AlgHomClass.commutes]
```
:::

After `intro L a` the goal is
`trivialNetState (trivialHaagKastlerNet.action L a) = trivialNetState a`. Writing `a` as
$`z\mathbf{1}`, the action fixes it, since every unital \*-automorphism fixes the multiples of
the unit; `rw` rewrites the left side to the right and closes the goal. Every state
on this algebra is invariant, in fact, since there is only one.
::::
:::::
