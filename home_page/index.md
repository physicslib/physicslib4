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
- **Chapter 4 (Axiom 2 – Isotony)** introduces the GNS Construction in motivating context and studies the isotony condition—the requirement that inclusions of spacetime regions induce \*-monomorphisms of the corresponding algebras.
- **Chapter 5 (Axiom 3 – Local Commutativity)** introduces the notion of completely spacelike separated regions and the quasilocal algebra, and studies the requirement that observables localised in spacelike separated regions commute.
- **Chapter 6 (Axiom 4 – Quasilocal Algebra)** analyses the construction of the quasilocal algebra as the completion of the set-theoretic union of all local algebras, and the axiom that all observables are quasilocal.
- **Chapter 7 (Axiom 5 – Lorentz Covariance)** studies the action of the inhomogeneous Lorentz group (connected to the identity) on the net of local algebras and the covariance requirement.
- **Chapter 8 (Axiom 6 – Primitivity)** examines faithful and irreducible representations; this axiom is ultimately abandoned in the sharpened formulation.
- **Chapter 9 (Haag–Kastler Axioms in Curved Spacetime)** generalizes the Haag–Kastler Axioms in Minkowski spacetime to curved spacetime, i.e. Lorentzian spacetime.

Chapter 10 assembles the formalisation-ready content, organised into four main blocks:

- **GNS Construction.** Carefully states and proves the GNS Construction Theorem in full detail—construction of the GNS Hilbert space, the \*-representation, the cyclic vector, faithfulness, and uniqueness up to unitary equivalence—since both the theorem and specific steps of its proof are used in the axioms that follow.

- **Spacetime and causal structure.** Gives precise definitions of spacetime, Minkowski spacetime, and Lorentzian spacetime, together with the full apparatus of causal structure: timelike, spacelike, and null vectors; time orientation; future- and past-pointing vectors; paths, curves, and trips; causal trips; chronological and causal futures and pasts; spacelike separation; and the Alexandrov topology. Supporting lemmas establish the basic geometry (the causal classification trichotomy, the reverse Cauchy–Schwarz and reverse triangle inequalities for timelike vectors, convexity of the future and past cones, monotonicity of futures and pasts, symmetry of spacelike separation, and the fact that isometries preserve causal classification, chronology, and Alexandrov-basis sets).

- **Sharpened Haag–Kastler Axioms in Minkowski and curved spacetime.** States the sharpened axioms—Local Algebras, Isotony, Local Commutativity, Quasilocal Algebra, and Lorentz Covariance—bundled into a single `HaagKastlerNet` structure, together with their curved-spacetime generalisation (`HaagKastlerNet` in curved spacetime). Derives the operator form of Einstein Causality in both settings. Develops covariant families of local states, the lift of the fiberwise covariance action to a \*-automorphism of the quasilocal algebra, group-action coherence of the covariance automorphism, and GNS-unitary implementation of a Poincaré-invariant (vacuum) state. In the curved-spacetime setting, where no quasilocal algebra exists, the covariance action restricts to the stabilizer subgroup of a region, and the GNS unitary represents that stabilizer action.

- **KMS condition and thermal equilibrium.** Introduces one-parameter automorphism groups and KMS states as the algebraic characterisation of thermal equilibrium. Proves the strip-Liouville principle (via a periodic entire extension / strip Schwarz reflection argument) and derives from it that every KMS state at positive inverse temperature is automatically invariant, that the KMS correlation function is unique, and that the separating-vector property holds for faithful states. In the curved-spacetime setting, identifies Killing flows as one-parameter subgroups of the stabilizer, and defines KMS states for a Killing flow—the precise algebraic sense in which the Hartle–Hawking and Gibbons–Hawking states are thermal.

## What is Being Formalised

Only the content of Chapter 10 is formalised in Lean. This comprises:

### Definitions

**GNS Construction**
- State, Cyclic Vector

**Spacetime and causal structure**
- Spacetime, Standard Minkowski Spacetime
- Timelike / Spacelike / Null Vectors, Time Orientation, Future- and Past-Pointing Vectors
- Paths, Curves, Timelike and Causal Smooth Curves, Future- and Past-Oriented Smooth Curves, Endpoints
- Trip, Causal Trip
- Chronological Future and Past, Causal Future and Past
- Spacelike Related, Completely Spacelike
- Alexandrov Topology, Minkowski Spacetime, Lorentzian Spacetime

**Sharpened axioms – Minkowski spacetime**
- Haag–Kastler Net, Quasilocal Algebra, Quasilocal Observable, Local Observable
- Covariant Family of Local States, Quasilocal Covariance Automorphism, Covariant Quasilocal Algebra, Invariant State

**Sharpened axioms – curved spacetime**
- Haag–Kastler Net in Curved Spacetime
- Covariant Family of Local States in Curved Spacetime
- Stabilizer Action on a Local Algebra
- Killing-Flow Automorphism Family

**KMS condition**
- One-Parameter Automorphism Group, KMS State
- Strip-Liouville Principle
- KMS State for a Killing Flow

### Lemmas and Theorems

**GNS Construction**
- Cauchy–Schwarz inequality for states
- Equivalence of the two descriptions of the left-ideal $$\mathcal{N}$$; $$\mathcal{N}$$ is a closed linear subspace
- Full GNS Construction Theorem (Hilbert space, \*-representation, cyclic vector, faithfulness, uniqueness up to unitary equivalence)
- Separating vector of a faithful state

**Causal structure**
- Causal classification trichotomy
- Reverse Cauchy–Schwarz inequality and reverse triangle inequality for timelike vectors
- Convexity of the timelike and future/past cones; sign and definiteness lemmas for the future cone
- Chronological precedence implies causal precedence
- Monotonicity of futures and pasts; symmetry of spacelike separation
- Structural properties of complete spacelike separation; basis sets are Alexandrov-open; bundled spacelike separation

**Isometry preservation**
- Isometries preserve the causal classification, chronology, and Alexandrov-basis sets
- Unique differentials along a path; pushforward of a path under an isometry
- Axiom 5 basis-set preservation

**Covariance – Minkowski spacetime**
- Composition of covariance
- Uniqueness and existence of the quasilocal covariance lift
- Group-action coherence of the covariance automorphism
- Existence for the trivial net
- GNS-unitary implementation of an invariant state (Theorem 75)
- Einstein Causality in a representation (Theorem 65)

**Covariance – curved spacetime**
- Composition of covariance in curved spacetime
- The stabilizer action is a group action
- GNS unitary representation of the stabilizer (Theorem 98); strongly continuous stabilizer GNS unitary
- Einstein Causality in a representation, curved spacetime (Theorem 93)

**KMS condition**
- Boundary coincidence for $$a = 1$$
- $$i\beta$$-periodic entire extension (strip Schwarz reflection)
- Strip-Liouville holds for $$\beta > 0$$
- KMS states are invariant (Theorem 83)
- Uniqueness on the strip from boundary values; uniqueness of the KMS correlation function
- A Killing flow induces a one-parameter automorphism group

### Axioms

**Minkowski spacetime:** Local Algebras, Isotony, Local Commutativity, Quasilocal Algebra, Lorentz Covariance.

**Curved spacetime:** Local Algebras, Isotony, Local Commutativity, Local Completeness, Isometric Covariance.

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
