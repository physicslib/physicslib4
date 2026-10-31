import VersoBlog
import Site.Components

open Verso Genre Blog
open Site

#doc (Page) "About" =>

:::pageToc
- [What This Enables](about/#what-this-enables)
- [With Openness and Intent](about/#with-openness-and-intent)
:::

Physics rests on mathematics, yet few of its theories are stated with the precision of a mathematical
theory. In 1900 David Hilbert asked, as the sixth of his problems, for the axioms of physics to be
treated mathematically, in the manner of the axioms of geometry. Proof assistants give that question
a new kind of answer: an axiom system written in a proof assistant is unambiguous, every definition
is explicit, and every theorem drawn from it is checked by machine. They are also a natural setting
for AI systems that reason about physics.

At the heart of this effort is *physicslib4*, an open-source library in the
[Lean proof assistant](https://lean-lang.org/). Its aim is to solve Hilbert's sixth problem in Lean 4
by presenting physical theories axiomatically: algebraic quantum field theory (AQFT), locally
covariant quantum field theory (LCQFT), topological quantum field theory (TQFT), axiomatic quantum
mechanics and others. It aims to be for physics what [Mathlib](https://leanprover-community.github.io/)
is for mathematics. The library's foundation is AQFT: the Haag–Kastler axioms in Minkowski and curved
spacetime, with the GNS construction, spectral theory and Stone's theorem beneath them, and no `sorry`.
The other theories are the directions in which the library grows.

::::anchoredHeading "what-this-enables" "What This Enables"
::::

A library of axiomatic physics in Lean means researchers and students can build on verified
foundations rather than reinvent them: causal structure, nets of local algebras, states and their
representations, and the spectral theory of operators, all mechanically verified. It means a
standardization of axioms: each axiom system has one precise statement that anyone can read and cite,
so a result says exactly what it assumes, and competing formulations can be compared definition by
definition. And it means a foundation for AI-assisted proofs: formal physics for AI systems to train on
and reason over, and a proof checker that accepts a machine-generated proof only if it is correct.

::::anchoredHeading "with-openness-and-intent" "With Openness and Intent"
::::

physicslib4 is a global effort. It is open source under the Apache 2.0 licence, developed in public on
[GitHub](https://github.com/physicslib/physicslib4), and open to contributions from anyone, anywhere:
physicists, mathematicians, Lean users and students alike. Every statement is written down first in
a public [blueprint](https://physicslib.github.io/physicslib4/blueprint/), so that what the library
claims can be read and questioned without knowing Lean.

To see where the project is heading, read the [roadmap](roadmap/). To take part, see
[how to get involved](get-involved/). To learn the library, start with the [tutorial](tutorial/).
