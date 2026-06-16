---
canonical: https://physicslib.github.io/physicslib4/
meta-description: by Kelly J Davis
meta-og:description: by Kelly J Davis
meta-og:locale: en_US
meta-og:site_name: Formalising Algebraic Quantum Field Theory in Lean
meta-og:title: AQFT in Lean
meta-og:type: website
meta-og:url: https://physicslib.github.io/physicslib4/
meta-theme-color: #157878
meta-twitter:card: summary
meta-twitter:title: AQFT in Lean
meta-viewport: width=device-width, initial-scale=1
title: Formalising AQFT in Lean
---

# AQFT in Lean

## by Kelly J Davis

[Blueprint (web)](https://physicslib.github.io/physicslib4/blueprint/) [Blueprint (pdf)](https://physicslib.github.io/physicslib4/blueprint.pdf) [Documentation](https://physicslib.github.io/physicslib4/docs) [GitHub](https://github.com/physicslib/physicslib4)

# AQFT in Lean

In 1964, Rudolf Haag and Daniel Kastler introduced a set of axioms for Algebraic Quantum Field Theory (AQFT) in Minkowski spacetime, proposing a mathematically rigorous, operator-algebraic framework for quantum field theory in terms of nets of C\*-algebras indexed by regions of Minkowski spacetime. This project formalises a "sharpened" version of these axioms in the [Lean Theorem Prover](https://leanprover-community.github.io), following the [original paper by Haag and Kastler](https://doi.org/10.1063/1.1704187). The original axioms, while revolutionary, left several details underspecified. This project clarifies those details and produces definitions, theorems, and axioms amenable to computer-assisted formalisation. In addition, this project formalises these "sharpened" axioms in curved spacetime too.

The blueprint is structured so that Chapters 1–9 motivate and analyse each of the original Haag–Kastler axioms in turn as well as their generalization to curved spacetime. These chapters serve as mathematical background and are not themselves formalised in Lean. Chapter 10 then collects the "sharpened" axioms together with the supporting definitions and theorems that have been carefully stated for formalisation; it is the content of Chapter 10—and only Chapter 10—that is formalised in Lean.

If you'd like to contribute, you may find the following links useful:

- [Blueprint (web)](https://physicslib.github.io/physicslib4/blueprint/)
- [Blueprint (pdf)](https://physicslib.github.io/physicslib4/blueprint.pdf)
- [Dependency graph](https://physicslib.github.io/physicslib4/blueprint/dep_graph_document.html)
- [Documentation pages for this repository](https://physicslib.github.io/physicslib4/docs/)
- [Original Haag–Kastler paper](https://doi.org/10.1063/1.1704187)

## The Blueprint

Chapters 1–9 of the blueprint unpack and analyse the original Haag–Kastler axioms one by one:

- **Chapter 1** presents the original Haag–Kastler axioms as stated in the 1964 paper.
- **Chapter 2 (Axiom 0 – Minkowski Space)** examines the role of Minkowski spacetime and compares the standard, indiscrete, Euclidean, and Alexandrov topologies on it.
- **Chapter 3 (Axiom 1 – Local Algebras)** discusses the notion of regions of measurement and the assignment of a C\*-algebra to each such region.
- **Chapter 4 (Axiom 2 – Isotony)** introduces the GNS Construction in motivating context and studies the isotony condition—the requirement that inclusions of spacetime regions induce *-monomorphisms of the corresponding algebras.
- **Chapter 5 (Axiom 3 – Local Commutativity)** introduces the notion of completely spacelike separated regions and the quasilocal algebra, and studies the requirement that observables localised in spacelike separated regions commute.
- **Chapter 6 (Axiom 4 – Quasilocal Algebra)** analyses the construction of the quasilocal algebra as the completion of the set-theoretic union of all local algebras, and the axiom that all observables are quasilocal.
- **Chapter 7 (Axiom 5 – Lorentz Covariance)** studies the action of the inhomogeneous Lorentz group (connected to the identity) on the net of local algebras and the covariance requirement.
- **Chapter 8 (Axiom 6 – Primitivity)** examines faithful and irreducible representations; this axiom is ultimately abandoned in the sharpened formulation.
- **Chapter 9 (Haag–Kastler Axioms in Curved Spacetime)** generalizes the Haag–Kastler Axioms in Minkowski spacetime to curved spacetime, i.e. Lorentzian spacetime.

Chapter 10 assembles the formalisation-ready content. It begins by carefully stating and proving the **GNS Construction Theorem** (with full detail, since both the theorem and specific steps of its proof are used in the axioms). It then gives precise definitions for spacetime, Minkowski spacetime, Lorentzian spacetime, causal structure (timelike, spacelike, and null vectors; trips; causal trips; chronological and causal futures and pasts; the Alexandrov topology), and finally states the **sharpened Haag–Kastler Axioms**: Local Algebras, Isotony, Local Commutativity, Quasilocal Algebra, and Lorentz Covariance as well as their generalization to curved spacetime.

## What is Being Formalised

Only the content of Chapter 10 is formalised in Lean. This comprises:

- **Definitions** — State, Cyclic Vector, Spacetime, Standard Minkowski Spacetime, Timelike/Spacelike/Null Vectors, Time Orientation, Future and Past Pointing Vectors, Paths, Curves, Timelike and Causal Smooth Curves, Future and Past Oriented Smooth Curves, Endpoints, Trip, Causal Trip, Chronological Future and Past, Causal Future and Past, Spacelike Related, Completely Spacelike, Alexandrov Topology, Minkowski Spacetime, Lorentzian spacetime, Quasilocal Algebra, Quasilocal Observable, Local Observable.
- **Lemmas and Theorems** — the Cauchy–Schwarz inequality for states, equivalence of the two descriptions of the left-ideal \(\mathcal{N}\), the fact that \(\mathcal{N}\) is a closed linear subspace, and the full GNS Construction Theorem (including construction of the GNS Hilbert space, the \(\ast\)-representation, the cyclic vector, faithfulness, and uniqueness up to unitary equivalence).
- **Axioms** — Local Algebras, Isotony, Local Commutativity, Quasilocal Algebra, and Lorentz Covariance and their generalization to curved spacetime.

## Contributing

1. Make sure you have [installed Lean](https://leanprover-community.github.io/get_started.html).
2. Download the repository using `git clone https://github.com/physicslib/physicslib4.git`.
3. Run `lake exe cache get!` to download built dependencies (this speeds up the build process).
4. Run `lake build` to build all files in this repository.

For more on getting started with Lean, visit the [Lean community website](https://leanprover-community.github.io) and the [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/).

Contributions are welcome. If you would like to contribute, please add your work to a new branch and open a pull request. Your PR will need to pass the relevant status checks, be approved by a reviewer, and have no conflicts with the base branch before it can be merged.

## Acknowledgements

We are grateful to Rudolf Haag and Daniel Kastler for their foundational work, and to the authors of [Entanglement in Algebraic Quantum Field Theories](https://arxiv.org/abs/2410.16599) for their clear presentation of the GNS construction that this blueprint in part follows. We would also like to thank the Mathlib maintainers and the broader Lean community for their continued support.

[physicslib4](https://github.com/physicslib/physicslib4) is maintained by Kelly J Davis.
