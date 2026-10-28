import VersoManual
import Tutorial.Meta
import Tutorial.Papers
import Physicslib4.AQFT.HaagKastler.EinsteinCausality
import Physicslib4.AQFT.HaagKastler.VacuumState
import Physicslib4.AQFT.HaagKastlerCurved.Net

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Tutorial

#doc (Manual) "Worked examples" =>

%%%
tag := "worked-examples"
%%%

{ref "aqft-in-brief"}[Chapter 1] gave the physics, and {ref "lean-in-brief"}[chapter 2] the Lean
needed to read it. This chapter puts the two together in four examples, each a piece of AQFT worked
through in the library: a net that satisfies every axiom, a state and its GNS representation,
local commutativity in a diamond, and the Lorentz invariance of causal precedence. Each example
follows the same pattern. A short reminder of the physics comes first, then the Lean statement,
read line by line, then a proof or construction with the goal shown after every step, and finally
one or two exercises.

As in chapter 2, every piece of Lean code on this page is checked against the library when the
tutorial is built, and the solutions to the exercises are checked too. Each example also names the
blueprint entry that it formalises, so that you can find the statement in ordinary mathematics.
All code below uses the short names made available by

```lean
open Physicslib4 Spacetime AQFT.HaagKastler
open scoped Pointwise
```

where `Pointwise` supplies the notation `L • B` for the image of a region under a Lorentz
transformation, used in the last example.

# The trivial net

%%%
tag := "worked-examples-trivial-net"
%%%

As you will recall from chapter 1, a theory in the Haag–Kastler framework is a net: a unital
C\*-algebra $`\mathfrak{U}(\mathbf{B})` for each diamond, unital \*-monomorphisms
$`i_{\mathbf{B}_1\mathbf{B}_2}` for nested diamonds, commutation at spacelike separation, and an
action $`\alpha_L` of the Poincaré group. First, can the conditions be met at all? If not, every
theorem about Haag–Kastler nets would hold vacuously.

The simplest candidate assigns the same algebra to every region: $`\mathfrak{U}(\mathbf{B}) =
\mathbb{C}` for every $`\mathbf{B}`. Each axiom then holds for an elementary reason.

* *Axiom 1.* $`\mathbb{C}` is a unital C\*-algebra, with complex conjugation as involution and the
  modulus as norm, and $`\mathfrak{U}(\emptyset) = \mathbb{C} = \mathbb{C}\mathbf{1}`.
* *Axiom 2.* Every embedding $`i_{\mathbf{B}_1\mathbf{B}_2}` is the identity of $`\mathbb{C}`,
  which is injective, and identities compose to identities.
* *Axiom 3.* $`\mathbb{C}` is commutative, so any two of its elements commute, spacelike or not.
* *Axiom 4.* The quasilocal algebra is $`\mathbb{C}` again, up to isomorphism.
* *Axiom 5.* Every $`\alpha_L` is the identity of $`\mathbb{C}`, which satisfies the group and
  isotony laws trivially.

## The Lean statement

The library builds this net in stages, following the structures of
{ref "lean-in-brief-structures"}[chapter 2, section 5]: a `LocalNet`, its `Isotony` data, a theorem
for each of Axioms 3 and 5, and the bundled `HaagKastlerNet`. The local net comes first. Its
source, without the documentation comment:

```
noncomputable def trivialLocalNet : LocalNet where
  algebra := fun _ => ℂ
  instCStarAlgebra := fun _ => inferInstance
  emptyEquivComplex := StarAlgEquiv.refl ℂ ℂ
```

Read it line by line against Axiom 1.

* `noncomputable def trivialLocalNet : LocalNet where` defines a term of the structure `LocalNet`
  by giving its fields. `noncomputable` tells Lean not to generate executable code: the real
  numbers, and with them the norm of `ℂ`, are not computable in Lean.
* `algebra := fun _ => ℂ` assigns to every region the type `ℂ`; the underscore marks a variable
  that is not used.
* `instCStarAlgebra := fun _ => inferInstance` gives each `ℂ` its C\*-algebra structure, found by
  type class search ({ref "lean-in-brief-structures"}[chapter 2, section 5]).
* `emptyEquivComplex := StarAlgEquiv.refl ℂ ℂ` is the normalisation
  $`\mathfrak{U}(\emptyset) \cong \mathbb{C}`, here the identity \*-isomorphism of `ℂ`.

Its consequences hold by unfolding it, so `rfl` proves that every region gets `ℂ`:

```lean
example (B : Set StandardMinkowskiSpacetime.Carrier) :
    trivialLocalNet.algebra B = ℂ :=
  rfl
```

The isotony data come next:

```
def trivialLocalNetIsotony : Isotony trivialLocalNet where
  map := fun _ _ _ _ _ => StarAlgHom.id ℂ ℂ
  injective := by
    intro B₁ B₂ h₁ h₂ h
    change Function.Injective (StarAlgHom.id ℂ ℂ)
    simpa using Function.injective_id
  map_self := by
    intro B h
    rfl
  map_comp := by
    intro B₁ B₂ B₃ h₁ h₂ h₃ h₁₂ h₂₃
    rfl
```

The field `map` takes five arguments, the two regions, the two proofs that they are diamonds and
the proof of `B₁ ⊆ B₂`, and ignores them all: every embedding is `StarAlgHom.id ℂ ℂ`. The three
laws are statements about the identity, proved by `simpa` with `Function.injective_id` and by
`rfl`. Lean confirms that each embedding fixes
every element:

```lean
example {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    (h₁ : IsAlexandrovBasisSet B₁)
    (h₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) (a : ℂ) :
    trivialLocalNetIsotony.map h₁ h₂ h a = a :=
  rfl
```

## Worked proof: local commutativity

Axiom 3 for the trivial net is the theorem `trivialLocalNet_localCommutativity`. On paper: let
$`\mathbf{B}_1, \mathbf{B}_2 \subseteq \mathbf{B}` be diamonds and $`a, b \in \mathbb{C}`. The
embeddings are identities, so the claim is $`ab = ba`, which holds in $`\mathbb{C}`. The spacelike
hypothesis is never used. Here is the proof in Lean, with the goal after each step:

:::goals
```lean
example : LocalCommutativity trivialLocalNet
    trivialLocalNetIsotony := by
  intro B₁ B₂ B hB₁ hB₂ hB hs h₁ h₂ a b
  exact mul_comm (G := ℂ) a b
```
:::

* `intro B₁ B₂ B hB₁ hB₂ hB hs h₁ h₂ a b`: `LocalCommutativity` is a definition whose value is a
  chain of `∀` and `→` ({ref "lean-in-brief-predicates"}[chapter 2, section 6]), and `intro` sees
  through it. It introduces the three regions, the three proofs that they are diamonds, the
  spacelike hypothesis `hs`, the two inclusions and the two elements. The goal is the commutation of
  the two images in `trivialLocalNet.algebra B`.
* `exact mul_comm (G := ℂ) a b`: Mathlib's `mul_comm a b : a * b = b * a` holds in any commutative
  multiplication. `Commute x y` is by definition `x * y = y * x`, each `map … a` unfolds to `a`, and
  `trivialLocalNet.algebra B` unfolds to `ℂ`, so the goal is `mul_comm` in `ℂ`, up to definitions.
  The named argument `(G := ℂ)` tells Lean which type to use. Without it, Lean takes the type from
  `a`, which is `trivialLocalNet.algebra B`, and looks for a commutative multiplication on it. Type
  class search unfolds only definitions marked reducible, and `trivialLocalNet` is an ordinary
  `def`, so the search sees only the C\*-algebra instance supplied by the field `instCStarAlgebra`,
  which does not include commutativity. With `G := ℂ`, Lean instead checks, unfolding definitions,
  that `a` and `b` have type `ℂ` and that the two multiplications agree.

The library's proof is the same, written `exact @mul_comm ℂ _ _ _`.

## Covariance, and the bundled net

Axiom 5 is the theorem `trivialLocalNet_lorentzCovariance`. Its proof supplies the identity
\*-isomorphism `StarAlgEquiv.refl ℂ ℂ` for every Lorentz transformation and every region, and checks
the three laws of `LorentzCovariance` by `rfl`.
The four pieces are then bundled:

```
noncomputable def trivialHaagKastlerNet : HaagKastlerNet where
  U := trivialLocalNet
  isotony := trivialLocalNetIsotony
  localCommutativity := trivialLocalNet_localCommutativity
  lorentzCovariance := trivialLocalNet_lorentzCovariance
```

```lean -show
example : trivialHaagKastlerNet =
    ⟨trivialLocalNet, trivialLocalNetIsotony,
      trivialLocalNet_localCommutativity,
      trivialLocalNet_lorentzCovariance⟩ :=
  rfl
```

The existence of this term is the theorem that the axioms are consistent:

```lean (name := checkNonempty)
#check nonempty_haagKastlerNet
```

```leanOutput checkNonempty
Physicslib4.AQFT.HaagKastler.nonempty_haagKastlerNet : Nonempty HaagKastlerNet
```

`Nonempty T` says that the type `T` has at least one term; the proof is `⟨trivialHaagKastlerNet⟩`.
The algebras of the trivial net lie in `Type`, so the theorem is stated for `HaagKastlerNet.{0}`
(Lean's display omits the universe; see the universe aside of
{ref "lean-in-brief-structures"}[chapter 2, section 5]).

The axioms can be satisfied, so theorems about `HaagKastlerNet` are not vacuous. But satisfying
them says nothing about physics. The
trivial net has a single observable up to scale, the unit, and every state assigns it the value
$`1`. A model of physical interest needs non-commutative local algebras, such as the algebras
generated by the Weyl operators of chapter 1's first exercise, and constructing such a net in Lean
is a much larger task. The trivial net has no blueprint entry of its own; it is the library's
witness that `def:haag-kastler-net` is consistent.

## An aside: the trivial net in curved spacetime

The curved-spacetime axioms of chapter 1 have their own trivial net,
`AQFT.HaagKastlerCurved.trivialHaagKastlerNet`:

```lean (name := checkCurvedTrivial)
#check AQFT.HaagKastlerCurved.trivialHaagKastlerNet
```

```leanOutput checkCurvedTrivial
Physicslib4.AQFT.HaagKastlerCurved.trivialHaagKastlerNet.{u} (M : AQFT.HaagKastlerCurved.LorentzianSpacetime) :
  AQFT.HaagKastlerCurved.HaagKastlerNet M
```

It takes as argument an interface, `HaagKastlerCurved.LorentzianSpacetime`, recording only what
the axioms use: points, diamonds, complete spacelike separation, and a group, standing for the
isometries connected to the identity, acting on the points. The net again assigns `ℂ` to every
region, and its proofs repeat those above. Two fields differ: `localAlgebra` (the curved Axiom 4,
which holds for every net by `HaagKastlerCurved.localAlgebra_of`) and `isometricCovariance`. A
one-point spacetime, `HaagKastlerCurved.trivialSpacetime`, gives the curved axioms a model.

:::::exercise
Show that every local algebra of the trivial net is commutative. As in the worked proof, name the
type in which `mul_comm` is to be used.

```lean
example (B : Set StandardMinkowskiSpacetime.Carrier)
    (a b : trivialHaagKastlerNet.algebra B) :
    a * b = b * a :=
  sorry
```

::::solution
```lean
example (B : Set StandardMinkowskiSpacetime.Carrier)
    (a b : trivialHaagKastlerNet.algebra B) :
    a * b = b * a :=
  mul_comm (G := ℂ) a b
```

For a general net the library proves this only for the empty region
(`HaagKastlerNet.mul_comm_algebra_empty`, the worked proof of chapter 2).
::::
:::::

:::::exercise
Every net has a one-dimensional algebra on the empty region (`HaagKastlerNet.finrank_algebra_empty`).
Show that in the trivial net every region has one. Mathlib's `Module.finrank_self ℂ` states
`Module.finrank ℂ ℂ = 1`.

```lean
example (B : Set StandardMinkowskiSpacetime.Carrier) :
    Module.finrank ℂ
      (trivialHaagKastlerNet.algebra B) = 1 :=
  sorry
```

::::solution
```lean
example (B : Set StandardMinkowskiSpacetime.Carrier) :
    Module.finrank ℂ
      (trivialHaagKastlerNet.algebra B) = 1 :=
  Module.finrank_self ℂ
```

The algebra unfolds to `ℂ`, so the statement is `Module.finrank_self ℂ` up to definitions.
::::
:::::

# A state and its GNS representation

%%%
tag := "worked-examples-gns"
%%%

Recall from chapter 1 that a state on a unital C\*-algebra $`\mathfrak{A}` is a linear functional
$`\omega` with $`\omega(a^*a) \geq 0` and $`\|\omega\| = 1`, and that the GNS construction turns it
into a Hilbert space $`\mathcal{H}_\omega`, a representation $`\pi_\omega` and a cyclic unit vector
$`\Omega_\omega` with

$$`\omega(a) = \langle \Omega_\omega, \pi_\omega(a)\,\Omega_\omega \rangle \qquad\text{for all } a \in \mathfrak{A}.`

The smallest example is $`\mathfrak{A} = \mathbb{C}`. A linear functional on $`\mathbb{C}` is
multiplication by the number $`\omega(1)`. Positivity gives
$`\omega(1) = \omega(\bar 1 \cdot 1) \geq 0` and normalisation gives $`|\omega(1)| = 1`, so
$`\omega(1) = 1`. So $`\mathbb{C}` has exactly one state, the identity $`\omega(z) = z`. It is positive, since
$`\omega(\bar z z) = |z|^2 \geq 0`, and faithful, since $`|z|^2 > 0` for $`z \neq 0`. Its GNS space
is $`\mathbb{C}` itself: the null space $`\mathcal{N}` is $`\{0\}`, the inner product is
$`\langle w, z \rangle = \bar w z`, $`\pi(z)` is multiplication by $`z`, and $`\Omega = 1`. The
example is transparent enough that every step of the Lean version can be compared with this
calculation.

The library's notion of state is the structure `GNS.State` of
{ref "lean-in-brief-predicates"}[chapter 2, section 6], and its blueprint entry is `def:state`. The
code below needs the order on `ℂ`, for positivity, and the notation `⟪x, y⟫_ℂ` for the inner
product:

```lean
open scoped ComplexOrder InnerProductSpace
```

## The Lean statement

The GNS theorem is `GNS.gns_construction`, the existence half of the blueprint's
`thrm:gns-construction-theorem`. Here is its statement, restated for an algebra in `Type` and
checked against the library by using the theorem as the proof:

```lean
example {A : Type} [CStarAlgebra A] (ω : GNS.State A) :
    ∃ (H : Type) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        GNS.IsCyclicVector π Ω ∧
        (∀ a : A, ω a = ⟪Ω, π a Ω⟫_ℂ) ∧
        (ω.IsFaithful → Function.Injective π) :=
  GNS.gns_construction ω
```

Read it line by line.

1. For a C\*-algebra `A` and a state `ω` on it,
2. there are a type `H` and a norm on it,
3. making it a complex inner product space that is complete, that is, a Hilbert space;
4. a \*-homomorphism `π` from `A` to the bounded operators `H →L[ℂ] H`, which is a representation,
   and a vector `Ω`;
5. such that `Ω` is cyclic for `π`,
6. the reproducing formula holds,
7. and `π` is injective if `ω` is faithful.

Lines 2 and 3 quantify over structures. A Hilbert space is a type together with instances, and the
instances are data, so "there is a Hilbert space" becomes "there are a type and three instances".
The instances are written `(_ : …)`, without names, because Lean finds them by type class search
once they are in context. The library states the theorem for `A` in any universe `Type u`, with `H`
in the same universe. Uniqueness up to unitary equivalence is the separate theorem
`GNS.gns_unique`.

## Worked construction: the identity state

A state is a structure, so a state is defined by giving its fields
({ref "lean-in-brief-structures"}[chapter 2, section 5]). The functional is Mathlib's identity map
`ContinuousLinearMap.id ℂ ℂ`, and the two proofs are short:

:::goals
```lean
noncomputable def identityState : GNS.State ℂ where
  toContinuousLinearMap := ContinuousLinearMap.id ℂ ℂ
  isPositive := by
    intro a
    exact star_mul_self_nonneg a
  isNormalized := ContinuousLinearMap.norm_id
```
:::

* `toContinuousLinearMap` is the field inherited from `A →L[ℂ] ℂ`
  ({ref "lean-in-brief-predicates"}[chapter 2, section 6]): here the identity of `ℂ`.
* `isPositive`: after `intro a` the goal is `0 ≤ (ContinuousLinearMap.id ℂ ℂ) (star a * a)`. The
  identity map unfolds, and Mathlib's `star_mul_self_nonneg a : 0 ≤ star a * a` closes the goal. It
  holds in any star-ordered ring, and `ℂ` with the order of `ComplexOrder` is one. On `ℂ`,
  `star a` is the complex conjugate.
* `isNormalized`: the operator norm of the identity is $`1`, Mathlib's `ContinuousLinearMap.norm_id`.
  (It assumes the space is nonzero, which Lean confirms for `ℂ` by type class search.) The value
  of a field can be a proof term, as here, as well as a tactic proof.

Lean checks that the state is the identity, by definition:

```lean
example (a : ℂ) : identityState a = a :=
  rfl
```

## Worked proof: running the GNS construction

The GNS theorem applies to any state, so to `identityState`. It returns an existential, which
`obtain` takes apart ({ref "lean-in-brief-tactics"}[chapter 2, section 4]). Here the reproducing
formula is extracted, with `identityState a` replaced by `a`:

:::goals
```lean
example : ∃ (H : Type) (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (π : ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
      ∀ a : ℂ, a = ⟪Ω, π a Ω⟫_ℂ := by
  obtain ⟨H, _, _, _, π, Ω, _, hrep, _⟩ :=
    GNS.gns_construction identityState
  exact ⟨H, _, _, _, π, Ω, hrep⟩
```
:::

* `obtain ⟨H, _, _, _, π, Ω, _, hrep, _⟩ := GNS.gns_construction identityState`: the pattern
  follows the shape of the statement, a nested existential and then a conjunction of three. It puts
  the type `H`, its three instances, the representation `π` and the vector `Ω` into context, with
  `hrep : ∀ a, identityState a = ⟪Ω, π a Ω⟫_ℂ`. The cyclicity and faithfulness clauses are not
  needed and are discarded with `_`.
* `exact ⟨H, _, _, _, π, Ω, hrep⟩`: builds the existential from these witnesses. The goal asks for
  `a = ⟪Ω, π a Ω⟫_ℂ`, while `hrep` gives `identityState a = ⟪Ω, π a Ω⟫_ℂ`. The two are equal by
  definition, as the `rfl` above shows, so Lean accepts `hrep`.

What the proof does not tell you is what `H` is. The theorem asserts existence, and the proof in the
library builds `H` as Mathlib's `PositiveLinearMap.GNS`: the completion of $`\mathfrak{A}` with the
semi-inner product $`\omega(a^*b)`, in which the null vectors are identified with $`0`, steps 2 and
3 of chapter 1 at once. To identify it with the
$`\mathbb{C}` of the calculation above, one checks that $`\mathbb{C}`, with $`\pi(z)w = zw` and
the vector $`1`, is also a cyclic representation reproducing $`\omega`, and applies
`GNS.gns_unique`, which gives a
unitary between the two spaces that intertwines the representations and maps one cyclic vector to
the other.

## States of a net

For a net, the state of interest lives on the quasilocal algebra. For the trivial net of the
first example, that algebra is $`\mathbb{C}` up to isomorphism. Every net has a quasilocal algebra, by the
theorem `exists_quasilocalAlgebra`, and for the trivial net the library also writes one down,
`trivialQuasilocalAlgebra`, with carrier `ℂ`. The identity state is a state on it:

```lean
noncomputable example :
    GNS.State trivialQuasilocalAlgebra.carrier :=
  identityState
```

`trivialQuasilocalAlgebra` is a quasilocal algebra of the trivial net, but not the one
`trivialHaagKastlerNet.quasilocal` chosen by the library, and the predicates below are stated for
the chosen one. For a general net `N`, the quasilocal algebra is `N.quasilocal`, chosen once and
for all from the existence theorem by `Classical.choice`, and the vacuum is a property of a state on its carrier:

```lean (name := checkVacuum)
#check HaagKastlerNet.IsVacuumState
```

```leanOutput checkVacuum
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumState.{u} (N : HaagKastlerNet)
  (ftl : (ℝ → InhomogeneousLorentzGroup) → Prop) (ω : GNS.State N.quasilocal.carrier) : Prop
```

The predicate `N.IsVacuumState ftl ω` has the two parts of chapter 1: `ω` is invariant under the
covariance action (`N.IsInvariantState ω`), and in some representation reproducing `ω`, with
unitaries implementing the action, the one-parameter groups of future timelike translations, those picked
out by `ftl`, have positive energy. `HaagKastlerNet.IsVacuumStateConcrete` fixes `ftl` to the
translations $`t \mapsto x + tn` with $`n` future timelike. The library constructs no vacuum state
for a concrete net. For the trivial net one would expect the unique state to be the vacuum, with a
one-dimensional GNS space on which every translation acts as the identity, but proving it means
first building a state on the chosen `N.quasilocal.carrier`, which is isomorphic to `ℂ` but not
literally `ℂ`. One route: show that every element is a scalar multiple of the unit, which gives a
unital \*-homomorphism to `ℂ`, and pull `identityState` back along it with the library's
`GNS.State.comp`. This is a natural project for chapter 4.

:::::exercise
Show that `identityState` is faithful. Mathlib's `star_mul_self_pos_iff : 0 < star a * a ↔ a ≠ 0`
holds in `ℂ`. What does the third clause of the GNS theorem then give?

```lean
example : identityState.IsFaithful := by
  intro a ha
  sorry
```

::::solution
:::goals
```lean
example : identityState.IsFaithful := by
  intro a ha
  exact star_mul_self_pos_iff.mpr ha
```
:::

After `intro a ha`, with `ha : a ≠ 0`, the goal is `0 < identityState (star a * a)`, which unfolds
to `0 < star a * a`. The GNS representation of `identityState` is therefore injective: no nonzero
element of `ℂ` acts as the zero operator, as for multiplication by $`z` on $`\mathbb{C}`.
::::
:::::

:::::exercise
Let $`\Omega` be a unit vector in $`\mathbb{C}^n`. Show that $`\omega(a) = \langle \Omega,
a\Omega \rangle` is a state on the algebra of bounded operators on $`\mathbb{C}^n`. In Lean,
$`\mathbb{C}^n` is `EuclideanSpace ℂ (Fin n)`, abbreviated below as `Cn n`, and Mathlib makes
`Cn n →L[ℂ] Cn n` a C\*-algebra. The functional is built from two of Mathlib's continuous linear
maps, evaluation at `Ω` followed by the inner product with `Ω`:

```lean
abbrev Cn (n : ℕ) := EuclideanSpace ℂ (Fin n)

noncomputable def vectorFun {n : ℕ} (Ω : Cn n) :
    (Cn n →L[ℂ] Cn n) →L[ℂ] ℂ :=
  (innerSL ℂ Ω).comp
    (ContinuousLinearMap.apply ℂ (Cn n) Ω)

example {n : ℕ} (Ω : Cn n) (a : Cn n →L[ℂ] Cn n) :
    vectorFun Ω a = ⟪Ω, a Ω⟫_ℂ :=
  rfl
```

Prove positivity and normalisation.

```lean
example {n : ℕ} (Ω : Cn n) (a : Cn n →L[ℂ] Cn n) :
    0 ≤ vectorFun Ω (star a * a) := by
  sorry

example {n : ℕ} (Ω : Cn n) (hΩ : ‖Ω‖ = 1) :
    ‖vectorFun Ω‖ = 1 := by
  sorry
```

For positivity, rewrite $`\langle \Omega, a^*a\Omega \rangle` as $`\langle a\Omega, a\Omega \rangle`
with `mul_apply_eq_comp`, `ContinuousLinearMap.star_eq_adjoint` and
`ContinuousLinearMap.adjoint_inner_right`, then use `inner_self_eq_norm_sq_to_K` and `positivity`.
For normalisation, prove $`\|\omega\| \le 1` with `ContinuousLinearMap.opNorm_le_bound`, the
Cauchy–Schwarz inequality `norm_inner_le_norm` and `ContinuousLinearMap.le_opNorm`, and
$`\|\omega\| \ge 1` from $`\omega(\mathbf{1}) = 1`. The unit operator has norm $`1` only on a
nonzero space: first give Lean an instance `Nontrivial (Cn n)`, using $`\Omega \neq 0`.

::::solution
:::goals
```lean
theorem vectorFun_nonneg {n : ℕ} (Ω : Cn n)
    (a : Cn n →L[ℂ] Cn n) :
    0 ≤ vectorFun Ω (star a * a) := by
  change 0 ≤ ⟪Ω, (star a * a) Ω⟫_ℂ
  rw [mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  positivity
```
:::

`change` unfolds `vectorFun`. The rewrites turn $`\langle \Omega, a^*(a\Omega) \rangle` into
$`\langle a\Omega, a\Omega \rangle` and then into $`\|a\Omega\|^2`, a nonnegative real number, which
`positivity` recognises.

```lean
theorem norm_vectorFun {n : ℕ} (Ω : Cn n)
    (hΩ : ‖Ω‖ = 1) : ‖vectorFun Ω‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _
      zero_le_one
    intro a
    calc ‖vectorFun Ω a‖ = ‖⟪Ω, a Ω⟫_ℂ‖ := rfl
      _ ≤ ‖Ω‖ * ‖a Ω‖ := norm_inner_le_norm _ _
      _ ≤ ‖Ω‖ * (‖a‖ * ‖Ω‖) := by
        gcongr
        exact a.le_opNorm Ω
      _ = 1 * ‖a‖ := by rw [hΩ]; ring
  · have : Nontrivial (Cn n) :=
      ⟨⟨Ω, 0, by intro h; simp [h] at hΩ⟩⟩
    have h1 : vectorFun Ω 1 = 1 := by
      change ⟪Ω, Ω⟫_ℂ = 1
      rw [inner_self_eq_norm_sq_to_K, hΩ]
      simp
    calc (1 : ℝ) = ‖vectorFun Ω 1‖ := by
          rw [h1, norm_one]
      _ ≤ ‖vectorFun Ω‖ * ‖(1 : Cn n →L[ℂ] Cn n)‖ :=
          (vectorFun Ω).le_opNorm 1
      _ = ‖vectorFun Ω‖ := by rw [norm_one, mul_one]

noncomputable def vectorState {n : ℕ} (Ω : Cn n)
    (hΩ : ‖Ω‖ = 1) : GNS.State (Cn n →L[ℂ] Cn n) :=
  ⟨vectorFun Ω, vectorFun_nonneg Ω, norm_vectorFun Ω hΩ⟩
```

The bound $`\|\omega\| \le 1` is the chain
$`|\langle \Omega, a\Omega \rangle| \le \|\Omega\|\,\|a\Omega\| \le \|a\|`. For the reverse, the
unit operator has norm $`1` once the space is nonzero (the `Nontrivial` instance, which holds
because $`\Omega \neq 0`), and $`1 = |\omega(\mathbf{1})| \le \|\omega\|\,\|\mathbf{1}\|`. The last
line assembles the state. Its GNS representation is the defining one on $`\mathbb{C}^n`, up to
unitary equivalence, since every vector of $`\mathbb{C}^n` is $`a\Omega` for some $`a`, as in the
$`M_2(\mathbb{C})` exercise of chapter 1.
::::
:::::

# Local commutativity in a diamond

%%%
tag := "worked-examples-locality"
%%%

You will remember Axiom 3 from chapter 1: if the diamonds $`\mathbf{B}_1` and $`\mathbf{B}_2` are
completely spacelike, their observables commute in the algebra of every diamond $`\mathbf{B}`
containing both, and therefore also in the quasilocal algebra $`\mathfrak{U}`. The second form is
the one used in practice, since $`\mathfrak{U}` holds the observables of all regions at once. This
example derives it from the first.

:::figure "diamond"
Two completely spacelike diamonds $`\mathbf{B}_1` and $`\mathbf{B}_2` inside a diamond
$`\mathbf{B}`.
:::

The argument uses one property of the embeddings $`\iota_{\mathbf{B}} : \mathfrak{U}(\mathbf{B})
\to \mathfrak{U}`: they are compatible with isotony,
$`\iota_{\mathbf{B}} \circ i_{\mathbf{B}_1\mathbf{B}} = \iota_{\mathbf{B}_1}`. Let
$`a \in \mathfrak{U}(\mathbf{B}_1)` and $`b \in \mathfrak{U}(\mathbf{B}_2)`, and write
$`a' = i_{\mathbf{B}_1\mathbf{B}}(a)` and $`b' = i_{\mathbf{B}_2\mathbf{B}}(b)`. Then

$$`\iota_{\mathbf{B}_1}(a)\,\iota_{\mathbf{B}_2}(b) = \iota_{\mathbf{B}}(a')\,\iota_{\mathbf{B}}(b') = \iota_{\mathbf{B}}(a'b') = \iota_{\mathbf{B}}(b'a') = \iota_{\mathbf{B}_2}(b)\,\iota_{\mathbf{B}_1}(a),`

using compatibility, that $`\iota_{\mathbf{B}}` is multiplicative, and Axiom 3 in
$`\mathfrak{U}(\mathbf{B})`. In the library, Axiom 3 is `LocalCommutativity` (blueprint
`def:local-commutativity`), and the statement in $`\mathfrak{U}` is
`LocalCommutativity.commute_ι` (`lmm:local-commutativity-any-quasilocal`).

## The Lean statement

For a Haag–Kastler net `N`, the quasilocal algebra is `N.quasilocal`, a structure
`QuasilocalAlgebra` whose fields include the carrier `N.quasilocal.carrier`, the embeddings
`N.quasilocal.ι hB`, one for each proof `hB` that `B` is a diamond, and the compatibility law
`N.quasilocal.ι_inclusion`. The law reads:

```lean (name := checkInclusion)
#check QuasilocalAlgebra.ι_inclusion
```

```leanOutput checkInclusion
Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra.ι_inclusion.{u} {U : LocalNet} {i : Isotony U}
  (self : QuasilocalAlgebra U i) ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄ (hB₁ : IsAlexandrovBasisSet B₁)
  (hB₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) (a : U.algebra B₁) : (self.ι hB₂) ((i.map hB₁ hB₂ h) a) = (self.ι hB₁) a
```

It is the equation $`\iota_{\mathbf{B}_2}(i_{\mathbf{B}_1\mathbf{B}_2}(a)) = \iota_{\mathbf{B}_1}(a)`,
for the net `U` with isotony `i`. For a Haag–Kastler net these are `N.U` and `N.isotony`. The
statement of the worked proof below says, in words:

1. for a Haag–Kastler net `N` and diamonds `B₁`, `B₂` and `B`,
2. with `B₁` and `B₂` completely spacelike, both inside `B`,
3. and for elements `a : N.algebra B₁` and `b : N.algebra B₂`,
4. the images `N.quasilocal.ι hB₁ a` and `N.quasilocal.ι hB₂ b` commute.

Here `N.algebra B` abbreviates `N.U.algebra B`, the algebra of `B` in the underlying local net.

## Worked proof: from the common diamond to the quasilocal algebra

The Lean proof follows the calculation: it records Axiom 3 in the algebra of `B`, rewrites the
goal so that both elements pass through `B`, and maps the commutation into the quasilocal algebra.

:::goals
```lean
example (N : HaagKastlerNet)
    {B₁ B₂ B : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁)
    (hB₂ : IsAlexandrovBasisSet B₂)
    (hB : IsAlexandrovBasisSet B)
    (hs : IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
    (a : N.algebra B₁) (b : N.algebra B₂) :
    Commute (N.quasilocal.ι hB₁ a)
      (N.quasilocal.ι hB₂ b) := by
  have hloc := N.localCommutativity hB₁ hB₂ hB hs h₁ h₂ a b
  rw [← N.quasilocal.ι_inclusion hB₁ hB h₁ a,
    ← N.quasilocal.ι_inclusion hB₂ hB h₂ b]
  exact hloc.map (N.quasilocal.ι hB)
```
:::

* `have hloc := N.localCommutativity hB₁ hB₂ hB hs h₁ h₂ a b`: the field `localCommutativity` of
  the net is a proof of Axiom 3, and applying it to all its arguments gives
  `hloc : Commute (N.isotony.map hB₁ hB h₁ a) (N.isotony.map hB₂ hB h₂ b)`, commutation in
  `N.algebra B`. The tactic `have` adds a new hypothesis, proved by the term after `:=`.
* `rw [← N.quasilocal.ι_inclusion hB₁ hB h₁ a, ← …]`: the arrow `←` rewrites from right to left,
  replacing `N.quasilocal.ι hB₁ a` by `N.quasilocal.ι hB (N.isotony.map hB₁ hB h₁ a)`, and likewise
  for `b`. Both elements now enter $`\mathfrak{U}` through the same embedding.
* `exact hloc.map (N.quasilocal.ι hB)`: Mathlib's `Commute.map` says that a multiplicative map
  sends commuting elements to commuting elements. Applied to `hloc` and the embedding of `B`, it is
  the goal.

The library's `LocalCommutativity.commute_ι` has the same proof, but needs no `B`: it obtains one
from `Spacetime.alexandrovBasis_directed`, the fact of chapter 1 that any two diamonds lie in a
common diamond. For a net the result is `HaagKastlerNet.commute_ι_of_spacelike`, whose hypotheses
are the two diamonds, the spacelike condition and the elements. The converse holds as well: by
`localCommutativity_iff_exists_commute_ι` (`lmm:local-commutativity-iff-quasilocal`), a net
satisfies Axiom 3 if and only if spacelike observables commute in some quasilocal algebra.

## Einstein causality in a representation

The physical content is in Hilbert space: in any representation, spacelike observables are
commuting operators. That is `HaagKastlerNet.einstein_causality` (`thrm:einstein-causality`),
`Commute.map` once more, now along the representation `π`:

```lean
example (N : HaagKastlerNet) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁)
    (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (a : N.algebra B₁) (b : N.algebra B₂) :
    Commute (π (N.quasilocal.ι hB₁ a))
      (π (N.quasilocal.ι hB₂ b)) :=
  (N.commute_ι_of_spacelike hB₁ hB₂ hs a b).map π
```

Applied to the GNS representation of a state, this is
`HaagKastlerNet.exists_gns_einstein_causality`: for every state on $`\mathfrak{U}` there is a GNS
triple, as in the previous example, in which spacelike observables commute as operators on
$`\mathcal{H}_\omega`.

One remark on the hypothesis. Since `≺` is reflexive, no point is spacelike to itself: the library's
`isSpacelikeRelated_irrefl` states `¬ IsSpacelikeRelated M t p p`. So two regions that share a point
are never completely spacelike, and Axiom 3 says nothing about them. This is as it should be: an
observable localised in a diamond inside the overlap embeds, by isotony, into both algebras, and
nothing makes it commute with the other observables of either.

:::::exercise
Show that two regions with a common point `x` are not completely spacelike. A proof of
`IsCompletelySpacelike M t B₁ B₂` is a function: given a point of `B₁` with a proof of membership,
and a point of `B₂` with one, it returns a proof that they are spacelike related.

```lean
example {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    {x : StandardMinkowskiSpacetime.Carrier}
    (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂) :
    ¬ IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂ := by
  sorry
```

::::solution
:::goals
```lean
example {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    {x : StandardMinkowskiSpacetime.Carrier}
    (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂) :
    ¬ IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂ := by
  intro hs
  exact isSpacelikeRelated_irrefl _ _ x (hs x hx₁ x hx₂)
```
:::

As in chapter 2, `¬ P` is `P → False`, so `intro hs` leaves the goal `False`. Then `hs x hx₁ x hx₂` says that `x` is
spacelike to itself, which `isSpacelikeRelated_irrefl` refutes. Its first two arguments, the
spacetime and the time orientation, are read off the type and written `_`.
::::
:::::

:::::exercise
Observables of smaller regions inherit the commutation: if `B₁' ⊆ B₁` and `B₂' ⊆ B₂`, and `B₁` and
`B₂` are completely spacelike, the observables of `B₁'` and `B₂'` commute in $`\mathfrak{U}`. Use
`HaagKastlerNet.commute_ι_of_spacelike` and the library's `isCompletelySpacelike_mono`, which
states that complete spacelike separation survives shrinking either region.

```lean
example (N : HaagKastlerNet)
    {B₁ B₂ B₁' B₂' : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁' : IsAlexandrovBasisSet B₁')
    (hB₂' : IsAlexandrovBasisSet B₂')
    (hs : IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (h₁ : B₁' ⊆ B₁) (h₂ : B₂' ⊆ B₂)
    (a : N.algebra B₁') (b : N.algebra B₂') :
    Commute (N.quasilocal.ι hB₁' a)
      (N.quasilocal.ι hB₂' b) :=
  sorry
```

::::solution
```lean
example (N : HaagKastlerNet)
    {B₁ B₂ B₁' B₂' : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁' : IsAlexandrovBasisSet B₁')
    (hB₂' : IsAlexandrovBasisSet B₂')
    (hs : IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (h₁ : B₁' ⊆ B₁) (h₂ : B₂' ⊆ B₂)
    (a : N.algebra B₁') (b : N.algebra B₂') :
    Commute (N.quasilocal.ι hB₁' a)
      (N.quasilocal.ι hB₂' b) :=
  N.commute_ι_of_spacelike hB₁' hB₂'
    (isCompletelySpacelike_mono _ _ h₁ h₂ hs) a b
```

The regions `B₁` and `B₂` need not be diamonds: only the smaller regions carry algebras here, and
only their separation is used.
::::
:::::

# Lorentz invariance of causal precedence

%%%
tag := "worked-examples-covariance"
%%%

Chapter 1 described the identity component of the Poincaré group: its elements are the maps
$`x \mapsto \Lambda x + a`, where $`\Lambda` preserves the Minkowski form, has determinant $`1`
and preserves the direction of time. On vectors, invariance of causal precedence is then immediate: the translation cancels in
$`(\Lambda q + a) - (\Lambda p + a) = \Lambda(q - p)`, and $`\Lambda` maps a causal future-directed
vector to a causal future-directed vector. Axiom 5 rests on this. The covariance maps
$`\alpha_L : \mathfrak{U}(\mathbf{B}) \to \mathfrak{U}(L\mathbf{B})` make sense only if $`L`
maps diamonds to diamonds, and they can respect locality only if $`L` maps spacelike pairs to
spacelike pairs.

The library defines $`\prec` not by vectors but by curves, as the blueprint does, so that the same
definition works in a curved spacetime. A _causal trip segment_ from $`p` to $`q` is a
future-oriented causal geodesic with past endpoint $`p` and future endpoint $`q`, and
$`p \prec q` means that a chain of zero or more segments leads from $`p` to $`q`. The empty chain
gives $`p \prec p`. In Lean the one-segment relation is `CausalSegmentPrecedes`, and `≺` is its
reflexive-transitive closure, Mathlib's `Relation.ReflTransGen`; this is why `≺` is reflexive
({ref "lean-in-brief-propositions"}[chapter 2, section 3]). The proof of invariance therefore has
two layers: a Lorentz transformation maps each segment to a segment, and so it maps chains to
chains. This is the blueprint's `thrm:causal-precedence-lorentz-invariant`.

## The Lean statement

An element of the group is a structure with five fields. Without the documentation comments:

```
structure InhomogeneousLorentzGroup where
  linear : StandardMinkowskiSpacetime.Carrier ≃ₗ[ℝ]
    StandardMinkowskiSpacetime.Carrier
  translation : StandardMinkowskiSpacetime.Carrier
  isLorentz : IsLorentz linear
  isProper : IsProper linear
  isOrthochronous : IsOrthochronous linear
```

```lean -show
example (L : InhomogeneousLorentzGroup) :
    InhomogeneousLorentzGroup :=
  ⟨L.linear, L.translation, L.isLorentz, L.isProper,
    L.isOrthochronous⟩
```

The field `linear` is $`\Lambda`, an invertible real-linear map (`≃ₗ[ℝ]`), and `translation` is
$`a`. The three proofs say that $`\Lambda` preserves the Minkowski form, has determinant $`1` and
preserves the direction of time: together, that $`(\Lambda, a)` lies in the identity component. The
group acts on points, written `g • x`, by the affine map, as Lean confirms by `rfl`:

```lean
example (g : InhomogeneousLorentzGroup)
    (x : StandardMinkowskiSpacetime.Carrier) :
    g • x = g.linear x + g.translation :=
  rfl
```

The theorem `causallyPrecedes_smul_iff` reads:

```lean
example (g : InhomogeneousLorentzGroup)
    (p q : StandardMinkowskiSpacetime.Carrier) :
    (g • p ≺[StandardMinkowskiSpacetime,
        standardMinkowskiTimeOrientation] g • q) ↔
      (p ≺[StandardMinkowskiSpacetime,
        standardMinkowskiTimeOrientation] q) :=
  causallyPrecedes_smul_iff g p q
```

For every group element `g` and points `p` and `q`, the image of `p` causally precedes the image of
`q` exactly when `p` causally precedes `q`, with the standard time orientation throughout.

The segment layer is done by `lorentzPath g μ`, the image of a smooth path `μ` under `g`, the path
$`s \mapsto \Lambda\mu(s) + a`. Its tangent at each parameter is $`\Lambda` applied to the tangent
of `μ` (`lorentzPath_mfderivWithin`), since the translation is constant. Five lemmas then transport
the five conditions of a causal trip segment: `lorentzPath_isCausal`,
`lorentzPath_isFutureOriented` and `lorentzPath_isGeodesic` for the curve, and
`lorentzPath_isPastEndpoint` and `lorentzPath_isFutureEndpoint` for its endpoints, which become
`g • p` and `g • q`. Together they give

```lean (name := checkSegment)
#check causalSegmentPrecedes_smul
```

```leanOutput checkSegment
Physicslib4.causalSegmentPrecedes_smul (g : InhomogeneousLorentzGroup) {p q : StandardMinkowskiSpacetime.Carrier}
  (h : StandardMinkowskiSpacetime.CausalSegmentPrecedes standardMinkowskiTimeOrientation p q) :
  StandardMinkowskiSpacetime.CausalSegmentPrecedes standardMinkowskiTimeOrientation (g • p) (g • q)
```

## Worked proof: from segments to causal precedence

The step from segments to chains is a case distinction. By
`causallyPrecedes_iff_eq_or_isCausalTrip` ({ref "lean-in-brief-propositions"}[chapter 2,
section 3]), either `p = q`, and then `g • p ≺ g • p` by reflexivity, or there is a causal trip, a
chain of one or more segments, and then `g` maps it segment by segment:

:::goals
```lean
example (g : InhomogeneousLorentzGroup)
    {p q : StandardMinkowskiSpacetime.Carrier}
    (h : p ≺[StandardMinkowskiSpacetime,
      standardMinkowskiTimeOrientation] q) :
    g • p ≺[StandardMinkowskiSpacetime,
      standardMinkowskiTimeOrientation] g • q := by
  rcases (causallyPrecedes_iff_eq_or_isCausalTrip _ _).mp h
    with rfl | htrip
  · exact causallyPrecedes_refl _ _ _
  · apply causallyPrecedes_of_isCausalTrip
    exact Relation.TransGen.lift (fun x => g • x)
      (fun _ _ hs => causalSegmentPrecedes_smul g hs)
      _ _ htrip
```
:::

* `rcases … with rfl | htrip`: `.mp` turns `h` into `p = q ∨ IsCausalTrip …`, and `rcases` splits
  the two cases; the two `_` are the spacetime and the time orientation. In the first case, the
  pattern `rfl` does more than name the equation: it substitutes `q := p` everywhere, so the goal
  becomes `g • p ≺ g • p`.
* `exact causallyPrecedes_refl _ _ _`: reflexivity of `≺`, applied to the spacetime, the time
  orientation and the point, all read off the goal.
* `apply causallyPrecedes_of_isCausalTrip`: in the second case it suffices to give a causal trip
  from `g • p` to `g • q`, since every causal trip gives causal precedence.
* `exact Relation.TransGen.lift …`: Mathlib's `Relation.TransGen.lift f` lifts a map `f` that
  preserves a relation to its transitive closure. Here `f` is `x ↦ g • x`, the relation is
  `CausalSegmentPrecedes`, which `causalSegmentPrecedes_smul` shows is preserved, and `htrip` is the
  chain to be transported. The two `_` are the endpoints `p` and `q`.

This direction is the library's `causallyPrecedes_smul`, proved in one line with
`Relation.ReflTransGen.lift`, which handles both cases at once. The converse comes from the inverse
group element:

:::goals
```lean
example (g : InhomogeneousLorentzGroup)
    (p q : StandardMinkowskiSpacetime.Carrier) :
    (g • p ≺[StandardMinkowskiSpacetime,
        standardMinkowskiTimeOrientation] g • q) ↔
      (p ≺[StandardMinkowskiSpacetime,
        standardMinkowskiTimeOrientation] q) := by
  constructor
  · intro h
    have h' := causallyPrecedes_smul g⁻¹ h
    rwa [inv_smul_smul, inv_smul_smul] at h'
  · exact causallyPrecedes_smul g
```
:::

* `constructor` splits the `↔` into its two implications.
* `have h' := causallyPrecedes_smul g⁻¹ h`: applying the forward direction with `g⁻¹` to
  `h : g • p ≺ g • q` gives `g⁻¹ • g • p ≺ g⁻¹ • g • q`.
* `rwa [inv_smul_smul, inv_smul_smul] at h'`: Mathlib's `inv_smul_smul` states
  `g⁻¹ • g • x = x` for any group action. After the two rewrites, `h'` is the goal `p ≺ q`; `rwa` is
  `rw` followed by closing the goal with a hypothesis.
* `exact causallyPrecedes_smul g`: the second implication is the forward direction itself.

## Covariance of the net

Spacelike relatedness is defined from `≺` alone, so it is invariant too
(`isSpacelikeRelated_smul_iff`), and so is complete spacelike separation of two regions
(`isCompletelySpacelike_smul_iff`, and its one-directional form `isCompletelySpacelike_smul`).
The same argument for `≪` gives `chronologicallyPrecedes_smul_iff`, so a Lorentz transformation
maps diamonds to diamonds:
`isAlexandrovBasisSet_smul L hB` proves `IsAlexandrovBasisSet (L • B)` from
`hB : IsAlexandrovBasisSet B`.

These facts are what Axiom 5 needs. For a net `N`, the map $`\alpha_L` on the diamond `B` is
`N.covEquiv L B`, a \*-isomorphism from `N.algebra B` to `N.algebra (L • B)` chosen from the
existence statement of `LorentzCovariance`. It is compatible with isotony
(`HaagKastlerNet.covEquiv_isotony`), it preserves norms (`HaagKastlerNet.norm_covEquiv`), and it
preserves commutation within one algebra (`HaagKastlerNet.commute_covEquiv_iff`). With the
invariance of spacelike separation, the hypothesis of Axiom 3 is itself Lorentz invariant: if
$`\mathbf{B}_1` and $`\mathbf{B}_2` are completely spacelike diamonds, so are `L • B₁` and
`L • B₂`, and Axiom 3 applies to them. In particular the transported observables commute, as the
second exercise below shows; the proof needs nothing about `covEquiv` beyond its type.

:::::exercise
Show that spacelike relatedness is Lorentz invariant. The library's
`isSpacelikeRelated_congr M t f hf p₁ p₂` proves
`IsSpacelikeRelated M t (f p₁) (f p₂) ↔ IsSpacelikeRelated M t p₁ p₂` for any map `f` with
`hf : ∀ p q, (f p ≺[M, t] f q) ↔ (p ≺[M, t] q)`.

```lean
example (g : InhomogeneousLorentzGroup)
    (p₁ p₂ : StandardMinkowskiSpacetime.Carrier) :
    IsSpacelikeRelated StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation (g • p₁) (g • p₂) ↔
      IsSpacelikeRelated StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation p₁ p₂ :=
  sorry
```

::::solution
```lean
example (g : InhomogeneousLorentzGroup)
    (p₁ p₂ : StandardMinkowskiSpacetime.Carrier) :
    IsSpacelikeRelated StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation (g • p₁) (g • p₂) ↔
      IsSpacelikeRelated StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation p₁ p₂ :=
  isSpacelikeRelated_congr _ _ (fun x => g • x)
    (causallyPrecedes_smul_iff g) p₁ p₂
```

`causallyPrecedes_smul_iff g` is a function of `p` and `q`, so it is exactly the hypothesis `hf`.
This is the library's proof of `isSpacelikeRelated_smul_iff`.
::::
:::::

:::::exercise
Show that transported observables of completely spacelike diamonds commute: if `B₁` and `B₂` are
completely spacelike, the transported observables `N.covEquiv L B₁ a` and `N.covEquiv L B₂ b`, which live in the algebras of
`L • B₁` and `L • B₂`, commute in $`\mathfrak{U}`. Use `HaagKastlerNet.commute_ι_of_spacelike`,
`isAlexandrovBasisSet_smul` and `isCompletelySpacelike_smul`.

```lean
example (N : HaagKastlerNet) (L : InhomogeneousLorentzGroup)
    {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁)
    (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (a : N.algebra B₁) (b : N.algebra B₂) :
    Commute
      (N.quasilocal.ι (isAlexandrovBasisSet_smul L hB₁)
        (N.covEquiv L B₁ a))
      (N.quasilocal.ι (isAlexandrovBasisSet_smul L hB₂)
        (N.covEquiv L B₂ b)) :=
  sorry
```

::::solution
```lean
example (N : HaagKastlerNet) (L : InhomogeneousLorentzGroup)
    {B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁)
    (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (a : N.algebra B₁) (b : N.algebra B₂) :
    Commute
      (N.quasilocal.ι (isAlexandrovBasisSet_smul L hB₁)
        (N.covEquiv L B₁ a))
      (N.quasilocal.ι (isAlexandrovBasisSet_smul L hB₂)
        (N.covEquiv L B₂ b)) :=
  N.commute_ι_of_spacelike _ _
    (isCompletelySpacelike_smul L hs) _ _
```

The images `L • B₁` and `L • B₂` are diamonds, by `isAlexandrovBasisSet_smul`, and completely
spacelike, by `isCompletelySpacelike_smul`, so Axiom 3 in $`\mathfrak{U}` applies to them. The four `_` are
the two diamond proofs and the two elements, which Lean reads off the goal. Commutation inside one
algebra is carried by `commute_covEquiv_iff` instead.
::::
:::::

# What the examples show

%%%
tag := "worked-examples-summary"
%%%

The four examples share a method, and it is the method of the whole library.

* *Start from the blueprint.* The examples rest on blueprint entries: `def:haag-kastler-net` for
  the axioms, `def:state` and `thrm:gns-construction-theorem` for the state and its representation,
  `def:local-commutativity`, `lmm:local-commutativity-any-quasilocal` and `thrm:einstein-causality`
  for locality, and `thrm:causal-precedence-lorentz-invariant` for covariance. The blueprint gives
  the statement and a proof in ordinary mathematics; the Lean statement is reviewed against it.
* *Take the axioms as hypotheses.* A theorem about AQFT takes a net `N : HaagKastlerNet` as an
  argument and uses its fields: `N.localCommutativity` in the third example, `N.covEquiv` and the
  quasilocal algebra `N.quasilocal` in the fourth. Every result then holds for every net, the
  trivial one included, and for the nets of physical interest once they are built.
* *Build objects by their fields.* The trivial net, the identity state and the vector state are
  each defined by giving the data and proving the conditions, field by field, as for any structure.
* *Prove by the paper argument.* Each Lean proof is the paper proof with its steps made explicit:
  unfold a definition, split into cases, rewrite with a law such as the compatibility of the
  embeddings with isotony, and apply a general lemma such as `Commute.map` or
  `Relation.TransGen.lift`. The goal after each step is what a careful written proof would state.

The examples also show where the library stops. Its only concrete net is the trivial one, which
contains no quantum physics; the states of this chapter are states on single algebras, not on the
quasilocal algebra of a physical net; and the library constructs no vacuum state. A
free field, as a net of Weyl algebras with its Fock vacuum, would be the natural next model.

Chapter 4, "Doing it yourself", turns from reading to writing. It explains how to install Lean,
work with the library on your own machine, run the exercises of these chapters there, and go from
a blueprint statement to a checked Lean theorem of your own.
