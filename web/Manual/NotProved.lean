import VersoManual
import Book.Meta

open Verso.Genre Manual
open Book

#doc (Manual) "Appendix: what the library does not prove" =>

%%%
tag := "not-proved"
file := "What-the-library-does-not-prove"
%%%

The chapters mark, where they arise, the standard facts that the library takes as hypotheses,
mentions in prose without proof, or leaves out. This appendix collects them in one list, so that it
is clear where the library stops. Each item links to the place where it matters. The list
describes the library as it is, and it changes as results are formalised. None of these facts is
assumed silently: where a theorem depends on one, it is a hypothesis of that theorem or, for the
group of the curved-spacetime Axiom 5, part of a definition.

# Operator algebras and spectral theory
%%%
tag := "not-proved-operators"
%%%

* _The existence of pure states._ By the Krein–Milman theorem every C\*-algebra has pure states.
  The library has the compact, convex state space in the weak-\* topology, but not the theorem:
  among the missing pieces, Mathlib has no instance `LocallyConvexSpace ℝ (WeakDual ℂ A)`, which
  its Krein–Milman theorem needs
  ([GNS chapter](The-GNS-construction/#physicslib4-reference-manual--The-GNS-construction--Design--Irreducibility___-purity-and-the-commutant)).
* _A representation is quasi-equivalent to its amplifications._ The proof needs the commutant of
  an amplification,
  $`(\pi(A) \otimes \mathbf{1})' = \pi(A)' \mathbin{\bar\otimes} B(\ell^2(\iota))`, which Mathlib
  does not provide
  ([GNS chapter](The-GNS-construction/#physicslib4-reference-manual--The-GNS-construction--Design--Disjointness___-quasi-equivalence-and-superselection)).
* _The spectral theorem for unbounded normal operators._ The library proves the spectral theorem
  for unbounded self-adjoint and for bounded normal operators; the unbounded normal case is neither
  stated in the blueprint nor proved
  ({ref "unbounded-overview"}[unbounded chapter]).
* _The Kaplansky density theorem._ The von Neumann density theorem is proved; Kaplansky's
  refinement, which would also make the approximants self-adjoint, is not, and the library does
  not need it
  ([Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Main-definitions-and-theorems--Representations-and-local-von-Neumann-algebras)).

# Spacetime
%%%
tag := "not-proved-spacetime"
%%%

* _The intersection property of diamonds in a general spacetime._ In the standard theory every
  point in the intersection of two diamonds lies in a diamond inside the intersection, since
  chronological futures are open in the manifold topology. The library proves this for standard
  Minkowski space only; for a general Lorentzian spacetime the basis theorem takes it as the
  hypothesis `hdir`
  ([Spacetime chapter](Spacetime-and-geometry/#physicslib4-reference-manual--Spacetime-and-geometry--Design--Diamonds___-and-when-they-form-a-basis)).
* _The geodesic equation at the endpoints._ A geodesic satisfies
  $`\nabla_{\dot\mu}\dot\mu = 0` at interior parameters by definition; that it holds at the
  endpoints too, by continuity, is not proved
  ([Spacetime chapter](Spacetime-and-geometry/#physicslib4-reference-manual--Spacetime-and-geometry--Design--The-pseudo-Riemannian-layer)).
* _Isometries connected to the identity preserve the time orientation._ So the oriented identity
  component, the group of the curved-spacetime Axiom 5, is the whole identity component. The proof
  needs a Myers–Steenrod-type rigidity theorem, which Mathlib does not provide; the library builds
  orientation preservation into the definition instead
  ([Spacetime chapter](Spacetime-and-geometry/#physicslib4-reference-manual--Spacetime-and-geometry--Design--Symmetries);
  {ref "conventions-implementation"}[conventions chapter]).
* _The isometries of Minkowski space connected to the identity are the proper orthochronous
  Poincaré transformations._ This standard fact, with parity and time reversal in other
  components, is not formalised; the Minkowski axioms use the proper orthochronous group
  `InhomogeneousLorentzGroup` directly
  ([Spacetime chapter](Spacetime-and-geometry/#physicslib4-reference-manual--Spacetime-and-geometry--Main-definitions-and-theorems--The-Lorentz-group-and-isometries)).

# The axioms in Minkowski spacetime
%%%
tag := "not-proved-minkowski"
%%%

* _The quasilocal algebra is unique up to isomorphism._ It is, since injective \*-homomorphisms of
  C\*-algebras are isometric; the library constructs one and states its results for every
  quasilocal algebra, but does not prove uniqueness
  ([Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Design--The-quasilocal-algebra-is-constructed)).
* _The Reeh–Schlieder theorem._ In a vacuum representation the vacuum is cyclic for the algebra
  of every nonempty diamond. The library does not prove it, so the Schlieder property takes
  cyclicity as a hypothesis, in Minkowski and in curved spacetime
  ([Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Main-definitions-and-theorems--Representations-and-local-von-Neumann-algebras)).
* _The spectrum condition in its joint-spectrum form._ The library states the spectrum condition
  as positive energy along every future-timelike translation. Its equivalence with the textbook
  form, that the joint spectrum of the energy-momentum operators lies in the closed forward cone,
  needs a joint spectral measure for commuting unbounded operators and is not formalised
  ([Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Main-definitions-and-theorems--Symmetry-and-states)).
* _Vacuum states of nontrivial nets._ The library defines vacuum states and proves their
  consequences that do not use the spectrum condition, but constructs no vacuum state of a
  nontrivial net
  ([Haag–Kastler chapter](Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--The-Haag___Kastler-axioms-in-Minkowski-spacetime--Main-definitions-and-theorems--Symmetry-and-states)).

# Curved spacetime and general covariance
%%%
tag := "not-proved-curved"
%%%

* _A quasilocal algebra need not exist._ The blueprint argues, with two diamonds in a
  Schwarzschild black hole that lie in no common diamond, that the construction of a quasilocal
  algebra fails in curved spacetime. The argument is informal, and the library does not formalise
  it
  ([curved chapter](The-axioms-in-curved-spacetime-and-general-covariance/#physicslib4-reference-manual--The-axioms-in-curved-spacetime-and-general-covariance--Design--Local-commutativity-without-a-quasilocal-algebra)).
* _The Hartle–Hawking and Bunch–Davies states are KMS states._ The library constructs no net on
  Schwarzschild or de Sitter spacetime. Their Killing-flow regions are not diamonds, so these
  examples motivate the definitions of KMS and ground states for a flow but are not instances of
  them
  ([curved chapter](The-axioms-in-curved-spacetime-and-general-covariance/#physicslib4-reference-manual--The-axioms-in-curved-spacetime-and-general-covariance--Main-definitions-and-theorems--Stabilisers___-covariant-states-and-KMS-states)).
* _A generally covariant theory._ The library states general covariance and proves the geometry it
  rests on, but proves no net theory generally covariant. The trivial theory is, mathematically;
  the library has no lemma for it
  ([curved chapter](The-axioms-in-curved-spacetime-and-general-covariance/#physicslib4-reference-manual--The-axioms-in-curved-spacetime-and-general-covariance--Main-definitions-and-theorems--General-covariance)).
