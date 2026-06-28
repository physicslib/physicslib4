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
usemathjax: true
---

# AQFT in Lean

## by Kelly J Davis

[Blueprint (web)](https://physicslib.github.io/physicslib4/blueprint/) [Blueprint (pdf)](https://physicslib.github.io/physicslib4/blueprint.pdf) [Documentation](https://physicslib.github.io/physicslib4/docs) [GitHub](https://github.com/physicslib/physicslib4)

# AQFT in Lean

In 1964, Rudolf Haag and Daniel Kastler introduced a set of axioms for Algebraic Quantum Field Theory (AQFT) in Minkowski spacetime, proposing a mathematically rigorous, operator-algebraic framework for quantum field theory in terms of nets of C\*-algebras indexed by regions of Minkowski spacetime. This project formalises a "sharpened" version of these axioms in the [Lean Theorem Prover](https://leanprover-community.github.io), following the [original paper by Haag and Kastler](https://doi.org/10.1063/1.1704187). The original axioms, while revolutionary, left several details underspecified. This project clarifies those details and produces definitions, theorems, and axioms amenable to computer-assisted formalisation. In addition, this project formalises these "sharpened" axioms in curved spacetime too.

The blueprint is structured so that Chapters 1–9 motivate and analyse each of the original Haag–Kastler axioms in turn as well as their generalisation to curved spacetime. These chapters serve as mathematical background and are not themselves formalised in Lean. Chapter 10 then collects the "sharpened" axioms together with the supporting definitions and theorems that have been carefully stated for formalisation; it is the content of Chapter 10—and only Chapter 10—that is formalised in Lean.

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
- **Chapter 9 (Haag–Kastler Axioms in Curved Spacetime)** generalises the Haag–Kastler Axioms in Minkowski spacetime to curved spacetime, i.e. Lorentzian spacetime.

Chapter 10 assembles the formalisation-ready content, organised into six main blocks:

- **GNS Construction.** Carefully states and proves the GNS Construction Theorem in full detail—construction of the GNS Hilbert space, the \*-representation, the cyclic vector, faithfulness, and uniqueness up to unitary equivalence—since both the theorem and specific steps of its proof are used in the axioms that follow.

- **Spacetime and causal structure.** Gives precise definitions of spacetime, Minkowski spacetime, and Lorentzian spacetime, together with the full apparatus of causal structure: timelike, spacelike, and null vectors; time orientation; future- and past-pointing vectors; paths, curves, and trips; causal trips; chronological and causal futures and pasts; spacelike separation; and the Alexandrov topology. Supporting lemmas establish the basic geometry (the causal classification trichotomy, the reverse Cauchy–Schwarz and reverse triangle inequalities for timelike vectors, convexity of the future and past cones, monotonicity of futures and pasts, symmetry of spacelike separation, and the fact that isometries preserve causal classification, chronology, and Alexandrov-basis sets).

- **Sharpened Haag–Kastler Axioms in Minkowski spacetime.** States the sharpened axioms—Local Algebras, Isotony, Local Commutativity, Quasilocal Completeness, and Lorentz Covariance—bundled into a single `HaagKastlerNet` structure. Derives the operator form of Einstein Causality in a representation (Theorem 65). Then develops the covariance structure:
  - Defines covariant families of local states (Definition 89) and the lift of the fiberwise covariance action to a \*-automorphism of the quasilocal algebra—the `QuasilocalCovarianceAutomorphism` (Definition 91)—and establishes its uniqueness (Lemma 92), existence (Theorem 93), and group-action coherence (Lemma 96).
  - Defines invariant states (Definition 97) and proves GNS-unitary implementation of a Poincaré-invariant state (Theorem 98).
  - Proves that purity of a state is preserved by any \*-automorphism and is therefore a Lorentz-covariance-invariant property (Theorem 100).
  - Proves that a state that is both invariant and pure yields a GNS representation that is simultaneously covariant and irreducible—a necessary precursor to a vacuum representation (Theorem 99).

- **Sharpened Haag–Kastler Axioms in curved spacetime.** States the curved-spacetime axioms—Local Algebras, Isotony, Local Commutativity, Local Completeness, and Isometric Covariance—bundled into a `HaagKastlerNet` in curved spacetime. Derives the operator form of Einstein Causality relative to a containing local algebra (Theorem 123). Then develops the curved-spacetime covariance structure:
  - Since no quasilocal algebra exists in a generic Lorentzian spacetime, the covariance action restricts to the stabiliser subgroup $$\mathrm{Stab}(\mathbf{B})$$ of a region—the isometries that fix $$\mathbf{B}$$—defining automorphisms of the single local algebra $$\mathfrak{U}(\mathbf{B})$$ (Definition 135).
  - Proves that the stabiliser action is a genuine group action (Lemma 136) and that a stabiliser-invariant state carries a unitary GNS representation of $$\mathrm{Stab}(\mathbf{B})$$ (Theorem 137), strongly continuous when the matrix coefficients are continuous (Theorem 138).
  - Proves that purity of a state on a local algebra is invariant under the stabiliser action (Theorem 140).
  - Proves that a state that is both stabiliser-invariant and pure yields an irreducible covariant GNS representation of $$\mathrm{Stab}(\mathbf{B})$$—the curved-spacetime analogue of the precursor to a vacuum representation (Theorem 139).

- **Local von Neumann algebras and irreducibility.** Develops the von Neumann algebra layer of the theory in both settings:
  - Defines the local von Neumann algebra $$R(\mathbf{B}) = \pi(\mathfrak{U}(\mathbf{B}))''$$ of a region in a representation (Definitions 66–67, 124–125), and proves Microcausality (Theorems 68, 126) and isotony of the von Neumann net (Theorems 69, 127) in both Minkowski and curved spacetime.
  - Proves the Statistical Independence (Schlieder) property: if the cyclic vector of one region is cyclic for its local observables, it is separating for the local von Neumann algebra of any spacelike-separated region (Theorems 71–72, 129–130).
  - Introduces irreducible representations via their commutant (Definition 73) and establishes the Topological Schur Lemma for cyclic representations (Theorem 74).
  - Proves the equivalence Pure $$\iff$$ Irreducible (Theorem 80), including the GNS Radon–Nikodym theorem (Theorems 78–79) that realises every dominated positive functional as an operator in the commutant.
  - Proves that the norm of any positive linear functional on a unital C\*-algebra equals its value on the unit (Theorem 83), and uses this to establish Pure $$\iff$$ Extreme Point of the state space (Theorem 85).
  - Proves that an irreducible representation generates a factor (Theorem 81), and consequently that the GNS representation of a pure state generates a factor (Theorem 82).
  - Specialises all of the above to the quasilocal algebra $$\mathfrak{U}$$ (Theorems 87–88) and to each local algebra $$\mathfrak{U}(\mathbf{B})$$ in curved spacetime (Theorems 131–132).

- **Separating vectors and faithful states.** Proves that the cyclic vector of a faithful state is also separating for the image of the GNS representation (Theorem 101)—the basic datum of Tomita–Takesaki modular theory. This result holds in any representation reproducing a faithful state, not only the canonical GNS one.

- **KMS condition and thermal equilibrium.** Introduces one-parameter automorphism groups and KMS states as the algebraic characterisation of thermal equilibrium. The main analytical ingredients are:
  - The Strip-Liouville Principle (Definition 106): a function continuous and bounded on a closed strip, holomorphic on the open strip, and with equal boundary values on both edges must be constant along the real axis.
  - This is proved at positive inverse temperature via a periodic entire extension—the strip Schwarz reflection (Theorem 107)—followed by Liouville's theorem (Theorem 108).

  From these ingredients the following consequences are derived:

  - Every KMS state at positive inverse temperature is automatically invariant under the time evolution (Theorem 109).
  - The analytic completion of a KMS correlation function is unique: any two strip-functions sharing both boundary values agree everywhere on the strip (Theorems 110–111).
  - The set of KMS states at fixed temperature and flow is convex (Theorem 104).

  In the Minkowski setting, a one-parameter subgroup of the inhomogeneous Lorentz group induces a one-parameter automorphism group on the quasilocal algebra via the covariance lift (Lemma 113), and KMS states for that flow are defined accordingly (Definition 114; convexity Theorem 115).

  In the curved-spacetime setting, Killing flows are identified as one-parameter subgroups of the stabiliser of a region, inducing a one-parameter automorphism group on the local algebra $$\mathfrak{U}(\mathbf{B})$$ (Definition 141, Lemma 142). KMS states for a Killing flow are the precise algebraic sense in which the Hartle–Hawking and Gibbons–Hawking states are thermal (Definition 143). A KMS state for a Killing flow at positive inverse temperature automatically carries a strongly continuous one-parameter unitary group on its GNS Hilbert space implementing the flow, yielding the curved-spacetime thermal (equilibrium) representation (Theorem 144; convexity Theorem 145).

## What is Being Formalised

Only the content of Chapter 10 is formalised in Lean. This comprises:

### Definitions

**GNS Construction**
- State (Definition 13), Cyclic Vector (Definition 14)

**Spacetime and causal structure**
- Spacetime (Definition 19), Standard Minkowski Spacetime (Definition 20)
- Timelike / Spacelike / Null Vectors (Definition 21), Time Orientation (Definition 25), Future- and Past-Pointing Vectors (Definition 26)
- Paths (Definition 31), Curves (Definition 32), Timelike and Causal Smooth Curves (Definition 33), Future- and Past-Oriented Smooth Curves (Definition 34), Endpoints (Definition 35)
- Trip (Definition 36), Causal Trip (Definition 37)
- Chronological Future and Past (Definition 38), Causal Future and Past (Definition 39)
- Spacelike Related (Definition 42), Completely Spacelike (Definition 43)
- Alexandrov Topology (Definition 46), Minkowski Spacetime (Definition 48), Lorentzian Spacetime (Definition 49)

**Sharpened axioms – Minkowski spacetime**
- Axiom 1: Local Algebras (Definition 57), Axiom 2: Isotony (Definition 58)
- Quasilocal Algebra (Definition 59), Axiom 3: Local Commutativity (Definition 60)
- Quasilocal Observable (Definition 61), Axiom 4: Quasilocal Completeness (Definition 62)
- Axiom 5: Lorentz Covariance (Definition 63), Haag–Kastler Net (Definition 64)
- Covariant Family of Local States (Definition 89), Quasilocal Covariance Automorphism (Definition 91)
- Covariant Quasilocal Algebra (Definition 95), Invariant State (Definition 97)

**Sharpened axioms – curved spacetime**
- Axiom 1: Local Algebras (Definition 116), Axiom 2: Isotony (Definition 117)
- Axiom 3: Local Commutativity (Definition 118), Local Observable (Definition 119)
- Axiom 4: Local Completeness (Definition 120), Axiom 5: Isometric Covariance (Definition 121)
- Haag–Kastler Net in Curved Spacetime (Definition 122)
- Covariant Family of Local States in Curved Spacetime (Definition 133)
- Stabiliser Action on a Local Algebra (Definition 135)
- Killing-Flow Automorphism Family (Definition 141), KMS State for a Killing Flow (Definition 143)

**Local von Neumann algebras and irreducibility**
- Local von Neumann Algebra – Minkowski spacetime (Definition 66)
- Local von Neumann Algebra – curved spacetime (Definition 124)
- Irreducible Representation (Definition 73)
- Pure State (Definition 76)
- Extreme Point of the State Space (Definition 84)

**KMS condition**
- One-Parameter Automorphism Group (Definition 102), KMS State (Definition 103)
- Covariance-Flow Automorphism Family (Definition 112), KMS State for the Covariance Flow (Definition 114)
- Strip-Liouville Principle (Definition 106)

### Lemmas and Theorems

**GNS Construction**
- Cauchy–Schwarz inequality for states (Lemma 16)
- Equivalence of the two descriptions of the left-ideal $$\mathcal{N}$$ (Lemma 17); $$\mathcal{N}$$ is a closed linear subspace (Lemma 18)
- Full GNS Construction Theorem: Hilbert space, \*-representation, cyclic vector, faithfulness, uniqueness up to unitary equivalence (Theorem 15)

**Causal structure**
- Causal classification trichotomy (Lemma 22)
- Reverse Cauchy–Schwarz inequality for timelike vectors (Lemma 23); reverse triangle inequality (Lemma 24)
- Sign lemma for the future cone (Lemma 28); definiteness of the spacelike complement (Lemma 29); convexity of the future and past cones (Lemma 30)
- Chronological precedence implies causal precedence (Lemma 40)
- Monotonicity of futures and pasts (Lemma 41); symmetry of spacelike separation (Lemma 44)
- Structural properties of complete spacelike separation (Lemma 45); basis sets are Alexandrov-open (Lemma 47); bundled spacelike separation and basis openness (Lemma 50)

**Isometry preservation**
- Isometries preserve the causal classification (Lemma 51)
- Unique differentials along a path (Lemma 52); pushforward of a path under an isometry (Lemma 53)
- Isometries preserve chronology (Lemma 54); isometries preserve Alexandrov-basis sets (Lemma 55)
- Axiom 5 basis-set preservation (Lemma 56)

**Covariance – Minkowski spacetime**
- Composition of covariance (Lemma 90)
- Uniqueness of the quasilocal covariance lift (Lemma 92); existence of the quasilocal covariance lift (Theorem 93); existence for the trivial net (Theorem 94)
- Group-action coherence of the covariance automorphism (Lemma 96)
- GNS-unitary implementation of an invariant state (Theorem 98)
- Irreducible covariant GNS representation of a pure invariant state (Theorem 99)
- Purity is covariance-invariant: purity is preserved under pullback by any \*-automorphism, and in particular under the covariance automorphism $$\beta_L$$ (Theorem 100)
- Einstein Causality in a representation (Theorem 65)

**Covariance – curved spacetime**
- Composition of covariance in curved spacetime (Lemma 134)
- The stabiliser action is a group action (Lemma 136)
- GNS unitary representation of the stabiliser (Theorem 137); strongly continuous stabiliser GNS unitary (Theorem 138)
- Irreducible covariant GNS representation of a pure invariant state on a local algebra (Theorem 139)
- Purity is invariant under the stabiliser action (Theorem 140)
- Einstein Causality in a representation, curved spacetime (Theorem 123)

**Local von Neumann algebras – Minkowski spacetime**
- $$R(\mathbf{B})$$ as a von Neumann algebra (Definition 67)
- Microcausality: spacelike-separated local von Neumann algebras commute (Theorem 68)
- Isotony of the von Neumann net (Theorem 69)
- Bundled von Neumann microcausality and isotony (Theorem 70)
- Statistical Independence (Schlieder Property): the cyclic vector of one region is separating for the local von Neumann algebra of any spacelike-separated region (Theorems 71–72)
- Topological Schur Lemma for cyclic representations (Theorem 74)
- Commutant operator is scalar iff its diagonal coefficient is proportional to the state (Theorem 75)
- Pure state implies irreducible GNS representation (Theorem 77)
- GNS Radon–Nikodym form is bounded (Theorem 78); GNS Radon–Nikodym operator exists and commutes with the representation (Theorem 79)
- Pure state $$\iff$$ irreducible GNS representation (Theorem 80)
- An irreducible representation generates a von Neumann algebra with trivial centre, i.e. a factor (Theorem 81)
- The GNS representation of a pure state generates a factor (Theorem 82)
- Norm of a positive linear functional equals its value on the unit (Theorem 83)
- Pure state $$\iff$$ extreme point of the state space (Theorem 85); state-space convexity and the extreme-point bridge (Theorem 86)
- Pure state $$\iff$$ extreme point of the state space of the quasilocal algebra (Theorem 87)
- Pure state $$\iff$$ irreducible GNS representation on the quasilocal algebra (Theorem 88)

**Local von Neumann algebras – curved spacetime**
- $$R(\mathbf{B}')$$ as a von Neumann algebra in curved spacetime (Definition 125)
- Microcausality relative to a containing local algebra (Theorem 126)
- Isotony of the curved von Neumann net (Theorem 127)
- Bundled von Neumann microcausality and isotony, curved spacetime (Theorem 128)
- Statistical Independence (Schlieder Property) in curved spacetime (Theorems 129–130)
- Pure state $$\iff$$ extreme point of the state space of a local algebra (Theorem 131)
- Pure state $$\iff$$ irreducible GNS representation on a local algebra (Theorem 132)

**Separating vectors and faithful states**
- Separating vector of a faithful state (Theorem 101)

**KMS condition**
- The KMS state set is convex (Theorem 104)
- Boundary coincidence for $$a = 1$$ (Lemma 105)
- $$i\beta$$-periodic entire extension / strip Schwarz reflection (Theorem 107)
- Strip-Liouville holds for $$\beta > 0$$ (Theorem 108)
- KMS states are invariant (Theorem 109)
- Uniqueness on the strip from boundary values (Theorem 110)
- Uniqueness of the KMS correlation function (Theorem 111)
- A Lorentz one-parameter subgroup induces a one-parameter automorphism group on the quasilocal algebra (Lemma 113)
- Convexity of the covariance-flow KMS states – Minkowski spacetime (Theorem 115)
- A Killing flow induces a one-parameter automorphism group on the local algebra (Lemma 142)
- The Killing-Flow KMS Thermal Representation: a KMS state for a Killing flow at positive inverse temperature carries a strongly continuous one-parameter unitary group on its GNS Hilbert space implementing the flow (Theorem 144)
- Convexity of the Killing-flow KMS states – curved spacetime (Theorem 145)

### Axioms

**Minkowski spacetime:** Local Algebras (Definition 57), Isotony (Definition 58), Local Commutativity (Definition 60), Quasilocal Completeness (Definition 62), Lorentz Covariance (Definition 63).

**Curved spacetime:** Local Algebras (Definition 116), Isotony (Definition 117), Local Commutativity (Definition 118), Local Completeness (Definition 120), Isometric Covariance (Definition 121).

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
