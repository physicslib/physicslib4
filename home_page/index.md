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

In 1964, Rudolf Haag and Daniel Kastler introduced a set of axioms for Algebraic Quantum Field Theory (AQFT) in Minkowski spacetime, proposing a mathematically rigorous, operator-algebraic framework for quantum field theory in terms of nets of C\*-algebras indexed by regions of Minkowski spacetime. This project formalises a "sharpened" version of these axioms in the [Lean Theorem Prover](https://leanprover-community.github.io), following the [original paper by Haag and Kastler](https://doi.org/10.1063/1.1704187). The original axioms, while revolutionary, left several details underspecified. This project clarifies those details and produces definitions, theorems, and axioms amenable to computer-assisted formalisation. In addition, this project formalises these "sharpened" axioms in curved spacetime, and adds a general-covariance postulate relating the nets over diffeomorphism-related backgrounds.

## How the blueprint is organised

The blueprint is 314 pages long and splits cleanly in two.

**Chapters 1–9 are mathematical background and are not formalised in Lean.** They motivate and analyse each of the original Haag–Kastler axioms in turn, and then generalise them to curved spacetime. Along the way they cite twelve supporting results, numbered 1 through 12 — Gelfand–Naimark, the Bounded Linear Transformation Theorem, the existence of a Lorentz metric, and so on. These are quoted from the literature where needed; none of them carries a Lean declaration.

**Chapter 10 collects the formalisation-ready content, and it is the content of Chapter 10 that is formalised in Lean.** Its items are numbered consecutively, running from Definition 13 through Definition 585, and comprise **570 declarations in total: 139 definitions, 152 theorems, 178 lemmas, 97 propositions, and 4 corollaries**, mapped onto **1,004 distinct Lean declarations** (where Mathlib already supplies a result, the blueprint names the Mathlib declaration directly). Three further numbered items — Conventions 22, 210 and 257, standing hypotheses of the two spectral-theory sections — share the numbering but are conventions rather than declarations, and are not counted. Chapter 10 is divided into seven top-level sections, §10.1 through §10.7.

**569 of the 570 are formalised, statements and proofs alike.** Of the 431 theorems, lemmas, propositions and corollaries in Chapter 10, 395 carry a written proof in the blueprint; the other 36, all in §10.2 and §10.3, are standard results quoted from the literature (Heine–Borel, Stone–Weierstrass, dominated convergence and the like) that the blueprint states in full but deliberately does not prove. 430 of the 431 proofs are formalised in Lean, including all 36 of the quoted results. The single exception, in both counts, is Theorem 422, whose statement is formalised but whose proof is not; it is discussed under [Formalisation status](#formalisation-status) below.

At a glance, the 570 declarations break down by top-level section as follows:

| Section | Topic | Pages | Definitions | Theorems | Lemmas | Propositions | Corollaries | Total | Formalised |
|---|---|---|---|---|---|---|---|---|---|
| §10.1 | GNS Construction | 29–38 | 2 | 1 | 3 | 0 | 0 | 6 | 6 |
| §10.2 | Spectral Theorems (bounded) | 38–155 | 25 | 24 | 27 | 67 | 1 | 144 | 144 |
| §10.3 | Unbounded Spectral Theorems | 155–232 | 24 | 13 | 47 | 30 | 3 | 117 | 117 |
| §10.4 | Spacetime and causal structure | 232–263 | 30 | 16 | 66 | 0 | 0 | 112 | 112 |
| §10.5 | Haag–Kastler Axioms (Minkowski) | 263–300 | 39 | 69 | 32 | 0 | 0 | 140 | 139 |
| §10.6 | Haag–Kastler Axioms (curved spacetime) | 300–310 | 17 | 29 | 3 | 0 | 0 | 49 | 49 |
| §10.7 | General Covariance | 310–312 | 2 | 0 | 0 | 0 | 0 | 2 | 2 |
| **Total** | | | **139** | **152** | **178** | **97** | **4** | **570** | **569** |

### Where the Lean lives

Each blueprint section maps onto a compact set of Lean modules, which is the fastest way to find the code behind a given piece of the theory:

| Section | Principal Lean modules |
|---|---|
| §10.1 | `Physicslib4/GNS/` (`Basic`, `Construction`, `NullSpace`, `CauchySchwarz`) |
| §10.2 | `Physicslib4/Spectral/` (`Basic`, `Spectrum`, `Forms`, `ProjectionValuedMeasure`, `OperatorIntegral`, `ContinuousCalculus`, `BorelClasses`, `BorelCalculus`, `SpectralTheorem`) |
| §10.3 | `Physicslib4/Spectral/Unbounded/` (`Basic`, `Spectrum`, `DirectSum`, `Integral`, `Normal`, `AbstractCalculus`, `Cayley`) |
| §10.4 | `Physicslib4/Spacetime/` (`Causality`, `Curves`, `CausalComplement`, `CausalStructure`, `Minkowski`, `MinkowskiDirected`, `LorentzianSpacetime`, `IsometryCausality`, …) |
| §10.5 | `Physicslib4/AQFT/HaagKastler/`, `Physicslib4/GNS/` (`Irreducibility`, `Superselection`, `RadonNikodym`, `ExtremeState`, …), `Physicslib4/AQFT/KMS.lean`, `Physicslib4/Analysis/StripPeriodicExtension.lean` |
| §10.6 | `Physicslib4/AQFT/HaagKastlerCurved/` (`LocalVonNeumann`, `StabilizerAction`, `StabilizerKMS`, `Purity`, `GeometricCovariance`, …) |
| §10.7 | `Physicslib4/AQFT/HaagKastlerCurved/GeneralCovariance.lean` |

### Formalisation status

The blueprint annotates every node with the Lean declarations that realise it, so the status of each node is a matter of record rather than of estimate. There is exactly one node in Chapter 10 that is not fully formalised, and two further places where the Lean is deliberately weaker or differently shaped than the prose. All three are flagged in the blueprint text itself; they are collected here so that they are not discovered by surprise.

**Not fully formalised (one node).**

- **Theorem 422, "Quasilocal Observables are Strongly Dense in the Bicommutant."** This is the von Neumann density theorem, which Mathlib does not have. The node sits in §10.5 (p. 279). Its statement is formalised as `Physicslib4.AQFT.HaagKastler.dense_range_in_bicommutant` (in `Physicslib4/AQFT/HaagKastler/StrongDensity.lean`), but the proof is a deliberate `sorry`, and the blueprint leaves the node as a stated result of the literature, not decomposed further. The Lean docstring records this in a **Restriction:** note: the intended form is the same statement with a proof, which is waiting on von Neumann's bicommutant theorem in the strong operator topology, either in Mathlib or as a local development. Nothing else in the project depends on it. The blueprint records exactly what is missing, because it is easy to get wrong: the strong operator topology itself *is* in Mathlib, as `PointwiseConvergenceCLM` (with the weak operator topology as `ContinuousLinearMapWOT`), so the statement is phraseable today. What is absent is the density theorem, and with it Kaplansky. Supplying it — the interaction of the strong topology with commutants — is a development of its own.

**Formalised, but the Lean is weaker than the prose (two places).** Both nodes below carry Lean declarations and formalised proofs; the caveat is one of fidelity, not of coverage.

- **The geodesic clause of a trip (Definitions 306–307).** In Lean, `Physicslib4.Spacetime.IsGeodesic` is defined to be `True`, so it imposes no constraint. A faithful geodesic condition needs the Levi-Civita connection of the metric — auto-parallelism of the tangent vector along the curve — which the pinned version of Mathlib does not provide. The formalised (causal) trip segments are therefore future-oriented timelike (respectively causal) curves with the correct past and future endpoints: the endpoint, timelike/causal, and future-orientation content is faithful, and only the geodesic property is unenforced. This is the one place where the blueprint and the Lean diverge on content.
- **Axiom 5 in curved spacetime (Definition 540).** "Isometries connected to the identity" and "identity-component isometries preserving the future orientation" describe the same group, but the inclusion of the former in the latter rests on a Myers–Steenrod-type rigidity result not yet in Mathlib. The Lean therefore intersects the identity component with the explicitly orientation-preserving subgroup. This is an implementation choice and does not alter the mathematical content of the axiom.

If you'd like to contribute, you may find the following links useful:

- [Blueprint (web)](https://physicslib.github.io/physicslib4/blueprint/)
- [Blueprint (pdf)](https://physicslib.github.io/physicslib4/blueprint.pdf)
- [Dependency graph](https://physicslib.github.io/physicslib4/blueprint/dep_graph_document.html)
- [Documentation pages for this repository](https://physicslib.github.io/physicslib4/docs/)
- [Original Haag–Kastler paper](https://doi.org/10.1063/1.1704187)

## The Blueprint

### Chapters 1–9: unpacking the original axioms

Chapters 1–9 unpack and analyse the original Haag–Kastler axioms one by one:

- **Chapter 1 (p. 4)** presents the original Haag–Kastler axioms as stated in the 1964 paper.
- **Chapter 2 (Axiom 0 – Minkowski Space, p. 5)** examines the role of Minkowski spacetime and compares the standard, indiscrete, Euclidean, and Alexandrov topologies on it, settling on the Alexandrov topology—generated by the "double cone" sets $$I^+(p) \cap I^-(q)$$—as the physically natural choice, which happens to coincide with the Euclidean topology on $$\mathbb{R}^4$$.
- **Chapter 3 (Axiom 1 – Local Algebras, p. 7)** discusses the notion of regions of measurement and the assignment of a C\*-algebra to each such region, arguing that the "physically natural" regions are double cones $$I^+(p) \cap I^-(q)$$ rather than arbitrary open sets with compact closure, and rejecting the causal (light-cone) alternative $$J^+(p) \cap J^-(q)$$ because it would force single points to carry algebras, which conflicts with fields being operator-valued distributions.
- **Chapter 4 (Axiom 2 – Isotony, p. 10)** introduces the GNS Construction in motivating context, studies the isotony condition—the requirement that inclusions of spacetime regions induce \*-monomorphisms of the corresponding algebras—and settles the "common unit" convention flagged in the original axiom by assigning the empty region the algebra $$\mathbb{C}1$$, so that every local algebra automatically contains a unit.
- **Chapter 5 (Axiom 3 – Local Commutativity, p. 13)** introduces the notion of completely spacelike separated regions and the quasilocal algebra, and studies the requirement that observables localised in spacelike separated regions commute, clarifying that this commutation is to be understood inside the quasilocal algebra $$\mathfrak{U}$$, since isotony alone cannot place two spacelike-separated (and hence non-nested) regions in a common algebra.
- **Chapter 6 (Axiom 4 – Quasilocal Algebra, p. 15)** analyses the construction of the quasilocal algebra as the completion of the set-theoretic union of all local algebras, and the axiom that $$\mathfrak{U}$$ contains all observables of interest—which is shown to mean that $$\pi_\omega(\mathfrak{U})$$ is strongly dense in the von Neumann algebra $$\pi_\omega(\mathfrak{U})''$$ it generates, so that any "missing" observable in $$\pi_\omega(\mathfrak{U})'' \setminus \pi_\omega(\mathfrak{U})$$ is experimentally indistinguishable from one in $$\mathfrak{U}$$.
- **Chapter 7 (Axiom 5 – Lorentz Covariance, p. 18)** studies the action of the inhomogeneous Lorentz group (connected to the identity) on the net of local algebras and the covariance requirement, and shows, via the Bounded Linear Transformation Theorem, how this norm-one action extends uniquely from the dense union of local algebras to the whole quasilocal algebra.
- **Chapter 8 (Axiom 6 – Primitivity, p. 20)** examines faithful and irreducible representations, noting that every unital C\*-algebra already has a faithful representation (Gelfand–Naimark) so primitivity is a genuinely extra condition; this axiom is ultimately abandoned in the sharpened formulation, following later presentations by Haag himself, on the grounds that its physical motivation is thin.
- **Chapter 9 (Haag–Kastler Axioms in Curved Spacetime, p. 22)** generalises the Haag–Kastler axioms from Minkowski spacetime to curved (Lorentzian) spacetime. It first pins down a precise definition of Lorentzian spacetime and its Alexandrov topology, then shows—via a Schwarzschild black-hole counterexample—that a quasilocal algebra need not exist on a generic Lorentzian spacetime, so Local Commutativity and the local-algebra axiom must be restated relative to a common containing region rather than a global algebra. The final section replaces Lorentz covariance with covariance under identity-component isometries, together with the Myers–Steenrod formalisation remark recorded under [Formalisation status](#formalisation-status).

### Chapter 10: the formalisation-ready content

Chapter 10 restates the axioms in a form amenable to auto-formalisation and proves everything they depend on. Its seven top-level sections are described below in order; the complete, itemised list of all 570 numbered declarations follows in [What is Being Formalised](#what-is-being-formalised).

- **§10.1 GNS Construction Details (pp. 29–38).** States and proves the GNS Construction Theorem (Theorem 15) in full detail—construction of the GNS Hilbert space, the \*-representation, the cyclic vector, faithfulness of the representation for a faithful state, and uniqueness up to unitary equivalence—since both the theorem and specific steps of its proof are used in the axioms that follow. The two supporting objects are the state (Definition 13) and the cyclic vector (Definition 14); the auxiliary results are the Cauchy–Schwarz inequality for positive functionals (Lemma 16) and the two equivalent descriptions of the GNS left ideal $$\mathcal{N}$$, which is shown to be a closed linear subspace (Lemmas 17–18). §10.1.3 is a prose summary and carries no numbered items.

- **§10.2 Spectral Theorems (pp. 38–155).** The largest section by declaration count (144 declarations, items 19–163, together with Convention 22), stating and proving the Spectral Theorem for Bounded, Self-Adjoint Operators (Theorem 162), a result the blueprint describes as sitting at the core of much of AQFT. It follows the presentation of Hall's *Quantum Theory for Mathematicians*. Standard results whose proofs lie outside the development — Heine–Borel, Riesz representation, Stone–Weierstrass, bounded convergence and the like — are stated in full but not proved in the prose, and are formalised all the same, usually directly by the corresponding Mathlib declaration. The whole section is a single subsection, §10.2.1 Spectral Theorem: Bounded Self-Adjoint Operators (p. 38), which proceeds in six layers.
  - *Elementary properties of bounded operators (pp. 39–45, items 19–37).* Fixes the inner product, the induced norm and the bounded-operator notation (Definitions 19–21), the standing convention that the Hilbert space is non-zero (Convention 22), the identity operator, indicator functions and orthogonal complements (Definitions 23–26), and basic facts about integrals, Cauchy–Schwarz, the reverse triangle inequality and continuity of the norm and inner product (Propositions 27–30). $$\mathcal{B}(\mathbf{H})$$ is a Banach space (Lemma 31); bounded inverses, the resolvent and the spectrum are defined (Definitions 32–33); and the Riesz theorem (Theorem 34) yields the adjoint of a bounded operator (Definition 35), which is bounded (Proposition 36) and has the expected algebraic properties (Lemma 37).
  - *Projection-valued measures (p. 45, items 38–67).* Orthogonal projections (Definition 38, Lemma 39) and projection-valued measures (Definition 40), with their associated scalar measures (Theorem 41) and operator-valued integration of bounded measurable functions (Theorem 42). The integral is built from bounded sesquilinear and quadratic forms (Definitions 43–44) and the simple-function approximation theorem (Theorem 45): the quadratic form of a bounded measurable function is bounded (Lemma 46, Propositions 47–49), and a bounded quadratic form determines a unique bounded operator (Propositions 50 and 55, Lemmas 51–54). The section then proves the norm bounds (Propositions 57 and 60, Lemmas 58–59), approximation by integrals of simple functions (Proposition 61), multiplicativity (Propositions 62–66), and compatibility with conjugation and the adjoint (Proposition 67).
  - *Stage 1: the continuous functional calculus (p. 80, items 68–104).* The Neumann series (Lemma 70) shows the spectrum is closed, bounded and non-empty (Proposition 73), with holomorphy of the resolvent (Proposition 74). The spectrum of a self-adjoint operator is real (Proposition 78) and compact (Lemma 80). The spectral radius (Definition 81) is at most the operator norm (Corollary 82), is given by Gelfand's formula (Theorem 85), and equals the norm for a self-adjoint operator (Lemma 86). Polynomial spectral mapping (Lemma 89), Stone–Weierstrass (Theorem 92) and the Bounded Linear Transformation Theorem (Theorem 94) then give the continuous functional calculus (Proposition 95), which is multiplicative, produces self-adjoint operators, preserves non-negativity, and satisfies the norm and spectral-mapping identities (Propositions 99–104).
  - *Stage 2: an operator-valued Riesz representation theorem (p. 107, items 105–133).* Riesz representation (Theorem 105) attaches measures to a self-adjoint operator (Proposition 106), and hence a bounded quadratic form to every bounded measurable function (Definition 107, Proposition 109). The class of functions with bounded quadratic form (Definition 110) contains the continuous functions (Proposition 115) and is closed under bounded pointwise limits (Proposition 117). A monotone-class argument through the algebra of sets $$\mathcal{L}_0$$ and bump functions (Definitions 119, 122 and 127, Theorems 128–129, Lemmas 121, 130 and 132–133) shows that the class contains every bounded Borel function.
  - *The bounded Borel functional calculus and the spectral measure (pp. 127–146, items 134–155).* The bounded Borel functional calculus (Definition 134) sends real functions to self-adjoint operators (Lemma 135) and is multiplicative (Proposition 137, via the classes $$\mathcal{F}_1$$ and $$\mathcal{F}_2$$ of Definition 138 and Propositions 139–142). The spectral projections of Borel sets form the spectral measure of the operator (Theorem 143): each is an orthogonal projection, they multiply to the intersection, and they are countably additive (Propositions 144–147, using the convergence of sums of pairwise orthogonal projections, Lemma 149 and Propositions 150–152). The two bounded functional calculi agree, and the spectral measure integrates to the operator itself (Propositions 153–155).
  - *Uniqueness and the spectral theorem (p. 147, items 156–163).* The spectral measure is unique (Theorem 156): two spectral measures of the same operator agree on polynomials, on continuous functions (via complex Stone–Weierstrass, Theorem 159, and Lemma 160) and on bounded measurable functions (Propositions 157, 158 and 161). This gives the Spectral Theorem for Bounded, Self-Adjoint Operators (Theorem 162) and the functional calculus it induces (Definition 163).

- **§10.3 Unbounded Spectral Theorems (pp. 155–232).** 117 declarations (items 164–282, together with Conventions 210 and 257), extending §10.2 to the Spectral Theorem for Unbounded, Self-Adjoint Operators (Theorem 282). The blueprint motivates this with the few genuinely unbounded self-adjoint operators that arise in AQFT, the momentum operator being the standard example. The section reuses §10.2 without restating it, follows the same Hall presentation, and builds up unbounded operators from scratch. Its single subsection, §10.3.1 Spectral Theorem: Unbounded Self-Adjoint Operators (p. 156), proceeds in five stages.
  - *Unbounded operators (pp. 156–179, items 164–209).* Unbounded operators (Definition 164), their adjoints (Definition 168, Propositions 169–170, Lemma 171), symmetric operators, extensions and self-adjointness (Definitions 172–173 and 175, Proposition 174), and closed and closable operators via the graph in $$\mathbf{H} \times \mathbf{H}$$ (Definitions 176 and 179, Proposition 180), with the closure of a symmetric operator symmetric (Lemma 181) and essential self-adjointness defined (Definition 182). Elementary properties follow: symmetric operators are closable (Proposition 184), the adjoint of a closure (Proposition 185), uniqueness of the self-adjoint extension of an essentially self-adjoint operator (Proposition 187), and kernel and range, with the orthogonal complement of the range equal to the kernel of the adjoint (Definitions 188–189, Proposition 192). Next come the resolvent set and spectrum of an unbounded operator (Definition 196), which agree with the bounded notions (Lemma 198) and are real for self-adjoint operators (Theorem 200). The layer closes with criteria for essential self-adjointness: dense range (Theorem 201), and, through Hilbert direct sums and internal orthogonal decompositions (Definitions 202, 204 and 205, Lemmas 203 and 207), direct sums of bounded self-adjoint operators (Propositions 208–209).
  - *Integration against a projection-valued measure (p. 180, items 210–237).* Under standing hypotheses (Convention 210), and with sesquilinear and quadratic forms on subspaces (Definitions 213–214) and the needed measure theory (Theorems 217–218, Propositions 219–223, Definition 221), the integral of an unbounded measurable function against a projection-valued measure is constructed on its natural domain (Propositions 229 and 231). It coincides with the bounded integral of §10.2 (Proposition 232), ignores null sets (Lemma 233), is the limit of its truncations (Lemma 234), and is self-adjoint for real-valued functions (Proposition 237).
  - *Bounded normal operators (p. 198, items 238–256).* For normal operators (Definition 238) the norm equals the spectral radius (Proposition 243). Spectral subspaces (Definition 244, Propositions 245–246) and almost eigenvectors (Definition 248, Lemmas 247 and 249–253) lead to the two-variable spectral mapping theorem for polynomials in $$A$$ and $$A^*$$ (Theorem 254, Corollary 255), and hence to the continuous functional calculus for a normal operator (Theorem 256).
  - *From a continuous functional calculus to a projection-valued measure (p. 212, items 257–271).* Under standing hypotheses (Convention 257), an abstract continuous functional calculus (Definition 258) is extended, through its associated measures (Definition 260), to bounded measurable functions (Definition 263). The extension is linear, multiplicative and compatible with conjugation (Lemmas 264 and 268, Proposition 267), and it yields a projection-valued measure (Theorem 269). Combined with the previous stage, this gives the Spectral Theorem for Bounded Normal Operators (Theorem 271).
  - *The Cayley transform and the unbounded spectral theorem (pp. 220–230, items 272–282).* Unitary operators are normal, with spectrum on the unit circle (Lemmas 272–273). The Cayley map (Lemma 274) and the Cayley transform of a self-adjoint operator (Theorem 275), with its spectral mapping (Lemma 276), reduce the unbounded self-adjoint case to the bounded normal one: a projection-valued measure is transported along a Borel bijection (Lemma 278), the Cayley transform omits the point $$1$$ (Lemma 279), and the spectral measure is transported through the Cayley transform (Theorem 281). The result is the Spectral Theorem for Unbounded, Self-Adjoint Operators (Theorem 282).

- **§10.4 Spacetime (pp. 232–263).** 112 items (Definitions 283–394), building the entire causal and topological apparatus the axioms are indexed on. It proceeds in seven layers.
  - *Spacetime, tangent-vector causality, curves, and trips (pp. 232–239, items 283–314).* Gives precise definitions of spacetime (Definition 283) and standard Minkowski spacetime (Definition 284); classifies tangent vectors as timelike, spacelike, or null (Definition 285) and proves the trichotomy (Lemma 286), the reverse Cauchy–Schwarz and reverse triangle inequalities for timelike vectors (Lemmas 287–288), and the cone geometry—orientation of pointing vectors, the sign lemma, definiteness of the spacelike complement of a timelike vector, and convexity of the cones (Lemmas 291–294)—alongside time orientations (Definition 289) and future- and past-pointing vectors (Definition 290). Then paths, curves, and oriented curves are defined as equivalence classes of paths up to reparametrisation (Definitions 295–300), with causal type and future/past orientation each shown well-defined on the quotient (Theorems 299 and 301) and a forgetful projection from oriented to unoriented curves (Theorem 302). Endpoints (Definition 303) come with two point-set lemmas—an extremal parameter lies in the frontier, and two endpoints force a compact parameter interval (Lemmas 304–305)—followed by trips and causal trips (Definitions 306–307, subject to the geodesic-placeholder caveat under [Formalisation status](#formalisation-status)), transitivity of chronological and causal precedence (Theorem 308), the causality condition (Definition 309) and the resulting strict partial order (Theorem 310), chronological and causal futures and pasts (Definitions 311–312), and their basic inclusion and monotonicity properties (Lemmas 313–314).
  - *§10.4.1 Causal diamonds (p. 239, items 315–329).* Introduces the causal diamond $$J^+(p) \cap J^-(q)$$ and the chronological (Alexandrov) diamond $$I^+(p) \cap I^-(q)$$ (Definition 315), with the structural properties of the causal diamond—monotonicity under endpoint spread, causal convexity, and that nonemptiness forces $$p \prec q$$ (Lemma 316)—and the containment of chronological diamonds in causal ones, together with the identification of the Alexandrov basis as exactly the chronological diamonds (Theorem 317). It then develops spacelike separation of points and of regions (Definitions 318–319, Lemmas 320–321), the spacelike complement $$\mathbf{B}^\perp$$ (Definition 322) and its order structure—antitone, extensive on the double complement, with the triple complement collapsing, making complementation the Galois connection attached to the spacelike-separation relation (Lemma 323). The double complement is packaged as the causal closure operator (Definition 324, Lemma 325), whose fixed points are the causally complete regions (Definition 326). These form a complete lattice—meets are intersections, joins are causal closures of unions—on which the causal complement is an order-reversing involution (Theorem 327); the set-level De Morgan laws (Lemma 328) then lift to full binary and infinitary De Morgan laws on the lattice (Theorem 329). The blueprint is careful to record what does *not* hold: the full orthocomplement law $$\mathbf{B} \wedge \mathbf{B}^\perp = \bot$$ fails at this generality, because the trip-based causal relation is irreflexive and so a point is spacelike-separated from itself.
  - *§10.4.2 Causal convexity (p. 243, items 330–332).* Defines a causally convex region as one containing every point causally between two of its own points (Definition 330), shows causal diamonds are causally convex (Lemma 331), and shows every spacelike complement—hence every causally complete region—is causally convex (Theorem 332).
  - *§10.4.3 Causal convexity: closure structure, and the Alexandrov basis theorems (p. 244, items 333–353).* The causally convex regions are shown to form a closure system (Lemma 333), giving the causal-convex hull (Definition 334) as a genuine closure operator whose closed sets are exactly the causally convex regions (Lemmas 335, Theorem 336). The subsection then turns to the Alexandrov topology (Definition 337): every diamond is open (Lemma 338); chronological futures and pasts are open under an explicit "no endpoints" hypothesis (Lemma 339) and unconditionally on standard Minkowski spacetime, where the coordinate-cone description discharges the hypothesis (Lemma 340). Minkowski spacetime and Lorentzian spacetime are then defined (Definitions 341–342, the latter as a spacetime whose Alexandrov topology is Hausdorff), with a bundled form of spacelike separation and basis openness (Lemma 343). A point lying in no diamond is pathological: its only Alexandrov neighbourhood is the whole space (Lemma 344), and the Hausdorff assumption rules this out, forcing the diamonds to cover the space (Lemma 345). Given downward-directedness the diamonds form a genuine topological basis (Theorem 346); past and future interpolation on standard Minkowski (Lemmas 347–348) supply downward-directedness there (Lemma 349), and common chronological predecessors and successors supply upward-directedness (Lemmas 350–352), so on standard Minkowski the diamonds are an unconditional basis (Theorem 353). Upward-directedness is what the quasilocal colimit of §10.5.1 later consumes.
  - *§10.4.4 Dilations are causal automorphisms but not isometries (p. 249, items 354–356).* The dilations $$x \mapsto \lambda x$$ preserve the Minkowski cones (Lemma 354) and are therefore causal automorphisms (Theorem 355), yet scale the metric by $$\lambda^2$$ and so are not isometries for $$\lambda \neq 1$$ (Theorem 356). This is the counterexample that forces the general-covariance morphism of §10.7 to be specified geometrically rather than causally.
  - *§10.4.5 Isometries and basis-set preservation (p. 250, items 357–362).* Single-metric transport: isometries preserve the causal classification of tangent vectors (Lemma 357), paths have unique differentials and well-defined pushforwards (Lemmas 358–359), future-orientation-preserving isometries preserve chronology (Lemma 360) and map Alexandrov-basis diamonds to diamonds (Lemma 361), which is exactly the well-definedness condition for the Axiom 5 action (Lemma 362).
  - *§10.4.6 Pullback metrics and cross-metric isometries (p. 251, items 363–394).* The single-metric lemmas above compare a spacetime with itself; general covariance instead compares two different metrics on one carrier, so the transport statements are redone cross-metric. This subsection defines the pullback $$\psi^* g$$ of a spacetime metric as a bundled family of continuous bilinear forms (Definition 363) and verifies every obligation in turn: the differential of a diffeomorphism is a linear equivalence (Lemma 364), with the two round-trip cancellation identities that Mathlib does not supply for a global `Diffeomorph` proved by hand (Lemmas 365–367); the pullback metric is symmetric, non-degenerate, Lorentzian, and a smooth section of the bilinear-form bundle (Lemmas 368–371), so the pullback of a spacetime is a spacetime (Theorem 372). Two-sided preservation of future orientation is then defined (Definition 373) and the pullback time orientation is shown to be bundle-smooth, nowhere vanishing, and everywhere timelike (Lemmas 374–377), with transport of future-pointing timelike and null vectors (Lemmas 378–379) giving two-sided orientation preservation (Lemma 380). Cross-metric isometries are defined (Definition 381) and shown closed under inverses (Lemma 382), to preserve causal classification (Lemma 383), to push paths forward preserving the timelike/causal conditions and endpoints (Lemmas 384–387), and to transport chronological precedence and the chronological future and past (Lemmas 388–390), hence to preserve Alexandrov-basis sets (Lemma 391). A general topological lemma—a bijection matching generating families is a homeomorphism (Lemma 392)—then identifies the pullback Alexandrov topology (Lemma 393) and yields that the pullback of a Lorentzian spacetime is again a Lorentzian spacetime (Theorem 394). Without Theorem 394 the phrase "the net over $$\psi^*(M,g)$$" in §10.7 would have no referent.

- **§10.5 Haag–Kastler Axioms in Minkowski spacetime (pp. 263–300).** The largest section by definition and theorem count (140 items, Definitions 395–534). Each axiom is stated as a definition so that it appears as a node in the declaration graph.
  - *The axioms and the quasilocal colimit (§10.5 and §10.5.1, pp. 263–282, items 395–424).* Axiom 1 (Local Algebras, Definition 395) assigns an abstract C\*-algebra to every Alexandrov-basis set, with $$\emptyset \mapsto \mathbb{C}1$$. Axiom 2 (Isotony, Definition 396) now supplies the family of unital \*-monomorphisms $$i_{\mathbf{B}_1 \mathbf{B}_2}$$ **as chosen data**, subject to injectivity, an identity law, and a composition law—so that $$\mathbf{B} \mapsto \mathfrak{U}(\mathbf{B})$$ is a functor on the inclusion order of basis sets. The blueprint is explicit that the family cannot be an existence statement (the identity and composition conditions are equations between the maps themselves) and that the inclusion hypothesis is non-strict, matching the Lean. §10.5.1 then cashes this in: the diamonds are directed under inclusion (Lemma 397), the isotony family is a directed system in Mathlib's sense (Lemma 398), and the direct limit carries a well-defined norm (Lemmas 399–401) making it a normed \*-algebra (Lemma 402) satisfying the C\*-inequality (Lemma 403) but not, in general, complete. A block of results stated for an arbitrary normed \*-algebra under standing hypotheses (Definition 404) then carries the structure through completion—the involution and its extension (Definition 405, Lemma 406), the completion coercion as a bundled \*-algebra homomorphism (Lemma 407), and the passage of the C\*-inequality, the normed $$\mathbb{C}$$-algebra structure, and finally the C\*-algebra property to the completion (Lemmas 408–410)—yielding that the completion of the quasilocal colimit is a C\*-algebra (Lemma 411). The quasilocal algebra $$\mathfrak{U}$$ is defined as that colimit-then-completion (Definition 412); the blueprint records why the shortcut of realising $$\mathfrak{U}$$ as a closed \*-subalgebra of an ambient C\*-algebra is rejected—it would assume an ambient algebra containing copies of every $$\mathfrak{U}(\mathbf{B})$$, for which the physics supplies no justification. Axiom 3 (Local Commutativity, Definition 413) and the quasilocal observable (Definition 414) follow. **Axiom 4 is now split in two.** Axiom 4 (Quasilocal Completeness, Definition 415) is presented as a bridge principle—the one axiom joining physical reality to the formalism, asserting the one-way inclusion that every physical observable corresponds to a quasilocal observable, and therefore having no mathematical consumers. The mathematical content previously conflated with it is separated out as a theorem: every local net satisfying Axiom 2 admits a quasilocal algebra, with an injective cocone of canonical embeddings whose images are dense (Theorem 416, with the supporting Lemmas 417–421). The indexing over Alexandrov-basis sets only is essential and not stylistic, since the algebras attached to non-basis subsets are junk fibres about which the axioms say nothing. Theorem 422 is the density result that keeps the bridge principle tenable in the presence of larger bicommutants, and is the one node whose proof is deliberately left unformalised (its statement is formalised). Axiom 5 (Lorentz Covariance, Definition 423) and the bundled `HaagKastlerNet` (Definition 424) close the block.
  - *§10.5.2 Einstein Causality (p. 282, item 425).* Derives the operator form of local commutativity in any \*-representation of the quasilocal algebra (Theorem 425).
  - *§10.5.3 Local von Neumann Algebras (p. 282, items 426–438).* Defines the local von Neumann algebra $$R(\mathbf{B}) = \pi(\mathfrak{U}(\mathbf{B}))''$$ of a region in a representation (Definition 426), registers it as a first-class `VonNeumannAlgebra` via the bicommutant-of-a-self-adjoint-set lemma (Lemma 427, Definition 428), and proves Microcausality (Theorem 429) and Isotony of the von Neumann net (Theorem 430), together with their bundled forms (Theorem 431) and the region-indexed assignment $$\mathbf{B} \mapsto R(\mathbf{B})$$ as an order-preserving map—the net of von Neumann algebras itself (Definition 432). It then proves the Statistical Independence (Schlieder) property in set-level and bundled forms (Theorems 433–434): if the cyclic vector of one region is cyclic for its local observables, it is separating for the local von Neumann algebra of any spacelike-separated region. Additive-free locality (Theorem 435) expresses locality through the spacelike complement without attaching an algebra to the unbounded complement itself. Geometric Covariance (Theorem 436) shows conjugation by the implementing unitary carries $$R(\mathbf{B})$$ onto $$R(L \cdot \mathbf{B})$$; being a factor is therefore constant along the Lorentz orbit of a region (Theorem 437), and the set equality upgrades to a first-class \*-algebra isomorphism of the bundled algebras (Theorem 438).
  - *§10.5.4 Relative Commutants of Nested Local Algebras (p. 284, items 439–446).* A new block organising the theory of inclusions $$R(\mathbf{B}_1) \subseteq R(\mathbf{B}_2)$$ around the relative commutant $$R(\mathbf{B}_1)' \cap R(\mathbf{B}_2)$$ (Definition 439). It proves antitonicity of the commutant (Theorem 440), that the relative commutant lies in the larger algebra and commutes with the smaller (Theorems 441–442), and that it always contains the centre of the ambient algebra (Theorem 443). An inclusion is irreducible when its relative commutant is trivial (Definition 444); an irreducible inclusion forces the ambient algebra to be a factor (Theorem 445), and the trivial self-inclusion is irreducible exactly when the algebra is a factor (Theorem 446).
  - *§10.5.5 Irreducibility and Schur's Lemma (p. 285, items 447–469).* Introduces irreducible representations via their commutant (Definition 447) and establishes the Topological Schur Lemma for cyclic representations (Theorem 448) together with the operator-theoretic bridge identifying commutant scalars with coefficients proportional to the state (Theorem 449). Defines pure states (Definition 450) and proves "pure implies irreducible" directly (Theorem 451), then the full equivalence Pure $$\iff$$ Irreducible (Theorem 454) via a GNS Radon–Nikodym theorem realising every dominated positive functional as an operator in the commutant (Theorems 452–453). An irreducible representation generates a factor (Theorem 455) and, more sharply, all of $$\mathcal{B}(H)$$ (Theorem 456), with a bundled density form (Theorem 457); consequently the GNS representation of a pure state generates a factor (Theorem 458) and all of $$\mathcal{B}(H)$$ (Theorem 459). The norm of a positive linear functional on a unital C\*-algebra equals its value on the unit (Theorem 460), which supports Pure $$\iff$$ Extreme Point of the state space (Definition 461, Theorem 462), the underlying convexity and the bridge to Mathlib's extreme-points API (Theorem 463), and weak-\* compactness of the state space (Theorem 467), which supplies the existence of pure states via Krein–Milman. The pullback of a state along a unital \*-homomorphism is introduced as its own object (Definition 464) with functoriality (Theorem 465) and the invariance of purity under a \*-isomorphism (Theorem 466). The section closes by specialising to the quasilocal algebra (Theorems 468–469).
  - *§10.5.6 Unitary Equivalence and Superselection (p. 289, items 470–471).* Defines unitary equivalence of representations (Definition 470) and shows irreducibility and factoriality are unitary invariants, transported by the cross-space conjugation induced by the implementing unitary (Theorem 471).
  - *§10.5.7 GNS Covariance (p. 290, items 472–477).* A new block. Cyclicity pulls back along a surjective \*-homomorphism (Lemma 472), so GNS data transports covariantly along a \*-isomorphism of the algebras (Theorem 473), restated as a unitary equivalence (Theorem 474). Pullback along a surjection preserves the image algebra (Lemma 475), whence superselection type transports along a \*-isomorphism (Theorem 476): the whole sector structure is an invariant of the algebra, not of its presentation. Applied to the covariance equivalence $$\alpha_L : \mathfrak{U}(\mathbf{B}) \simeq \mathfrak{U}(L \cdot \mathbf{B})$$ supplied by Axiom 5, this says the superselection type of a local state is constant along the Lorentz orbit of its region (Theorem 477).
  - *§10.5.8 Disjointness and Quasi-Equivalence (p. 291, items 478–495).* Defines disjointness via the vanishing of all intertwiners (Definition 478) and the coarser quasi-equivalence via a \*-isomorphism of generated von Neumann algebras (Definition 479). Proves Schur's Lemma in the form of the Irreducible Dichotomy—two irreducible representations are either disjoint or unitarily equivalent (Theorem 480)—together with Schur multiplicity (Lemma 481) and the triviality of the endomorphism algebra of an irreducible representation (Lemma 482). The commutant is packaged as the self-intertwiner (gauge) von Neumann algebra, trivial exactly when the representation is irreducible (Theorem 483), with double-commutant duality (Theorem 484) and the factor/triviality duality between an algebra and its commutant (Theorem 485). A supporting run develops the centre from scratch: abelian $$\iff$$ self-commuting (Lemma 486), the centre $$Z(R) = R \cap R'$$ (Definition 487) and its being a von Neumann algebra (Lemma 488), the general two-algebra intersection lemma that the relative commutants of §10.5.4 need (Lemma 489), the centre is abelian (Theorem 490), $$R$$ is abelian iff it equals its centre (Lemma 491), a factor is abelian iff it is the scalars (Theorem 492), an algebra and its commutant share a centre (Theorem 493), and factoriality is triviality of the centre (Theorem 494). The Pure-State Dichotomy underlying superselection sectors (Theorem 495) closes the block.
  - *§10.5.9 Direct Sums, Amplification, and Reducibility (p. 294, items 496–499).* Defines the direct-sum representation on the $$\ell^2$$-direct sum (Definition 496), shows each summand embeds as a subrepresentation whose projection lies in the commutant of the sum (Theorem 497), defines the $$\iota$$-fold amplification (Definition 498), and proves a direct sum with at least two nonzero summands is reducible, so a multiply-amplified representation is never irreducible (Theorem 499).
  - *§10.5.10 Covariant States and the Covariance Action (p. 295, items 500–518).* Defines covariant families of local states (Definition 500) with their composition law (Lemma 501), and the lift of the fibrewise covariance action to a \*-automorphism of the quasilocal algebra (Definition 502), with uniqueness (Lemma 503), existence (Theorem 504), and existence for the trivial net (Theorem 505). On the canonical quasilocal algebra this gives the covariance action (Definition 506), which is the action is a genuine group action (Lemma 507). Invariant states are defined (Definition 508) and shown to be implemented by GNS unitaries (Theorem 509); a state that is both invariant and pure yields a GNS representation that is simultaneously covariant and irreducible (Theorem 510). A "bounded-generator" scaffold toward the spectrum condition follows, deliberately sidestepping Stone's theorem and unbounded self-adjoint operators: positive energy for a bounded generator (Definition 511) with its API (Theorem 512), a generator-parameterised vacuum state (Definition 513) and its Stone-free consequences (Theorem 514), the future-timelike translation subgroup (Definition 515), and the vacuum state with that concrete predicate substituted in, leaving no free parameter (Definition 516). Purity is preserved by any \*-automorphism and is therefore covariance-invariant (Theorem 517), and GNS data transports along the quasilocal covariance action (Theorem 518).
  - *§10.5.11 The Separating Vector of a Faithful State (p. 298, item 519).* The cyclic vector of a faithful state is also separating for the image of the representation (Theorem 519)—the basic datum of Tomita–Takesaki modular theory. This holds in any representation reproducing a faithful state, not only the canonical GNS one.
  - *§10.5.12 The KMS Condition and Thermal Equilibrium (p. 298, items 520–529).* Introduces one-parameter automorphism groups (Definition 520) and KMS states (Definition 521) as the algebraic characterisation of thermal equilibrium. The condition is phrased purely as an analyticity statement about correlation functions, so—unlike the spectrum condition—it needs no unbounded-operator theory. The KMS state set is convex (Theorem 522); a boundary-coincidence argument at $$a = 1$$ (Lemma 523) together with the Strip-Liouville Principle (Definition 524), proved at positive inverse temperature via an $$i\beta$$-periodic entire extension (Theorem 525) and Liouville's theorem (Theorem 526), yields that KMS states are automatically invariant under the time evolution (Theorem 527); uniqueness on the strip from boundary values (Theorem 528) gives uniqueness of the analytic completion of a KMS correlation function (Theorem 529).
  - *§10.5.13 KMS States for the Covariance Flow (p. 300, items 530–534).* A one-parameter subgroup of the inhomogeneous Lorentz group induces a one-parameter automorphism group on the quasilocal algebra via the covariance lift (Definition 530, Lemma 531); KMS states for that flow are defined accordingly (Definition 532) and shown convex (Theorem 533). The zero-temperature ($$\beta \to \infty$$) counterpart—a ground state for a covariance flow, whose GNS-implementing unitary group has positive energy—is recorded alongside it (Definition 534).

- **§10.6 Haag–Kastler Axioms in Curved Spacetime (pp. 300–310).** 49 items, Definitions 535–583. The axioms are restated for a Lorentzian spacetime: Local Algebras (Definition 535), Isotony (Definition 536, again supplying the family as chosen data with identity and composition laws), Local Commutativity (Definition 537, which now **consumes** the Axiom 2 family rather than choosing its own witnesses), local observables (Definition 538), Local Completeness (Definition 539), and Isometric Covariance (Definition 540), bundled into a `HaagKastlerNet` in curved spacetime (Definition 541). The change to Axioms 2 and 3 has a visible consequence downstream: statements about nested regions have to factor a three-fold inclusion $$\mathbf{B}_1 \subseteq \mathbf{B}_2 \subseteq \mathbf{B}$$ inside a common containing algebra, and that factorisation is now the composition law of Axiom 2, so **the coherence hypotheses that earlier versions carried at each such site are gone**—curved isotony (Theorem 546) and the curved von Neumann net (Definition 548) are unconditional. Explicit hypotheses remain only where the abstract interface genuinely cannot supply them, namely basis-set preservation and the coherence of the stabiliser action with the chosen embeddings in Geometric Covariance (Theorem 552), discharged for nets arising from a concrete geometric spacetime.
  - *§10.6.1 Einstein Causality in Curved Spacetime (p. 303, item 542).* The operator form of local commutativity, expressed in a representation of a common containing local algebra rather than of a global quasilocal algebra (Theorem 542).
  - *§10.6.2 Local von Neumann Algebras in Curved Spacetime (p. 303, items 543–554).* The Minkowski development of §10.5.3 mirrored relative to a containing region: the local von Neumann algebra of a subregion and its bundled registration (Definitions 543–544), Microcausality (Theorem 545), unconditional Isotony (Theorem 546), the bundled form (Theorem 547), the net as an order-preserving map on the poset of subregions (Definition 548), Statistical Independence in set-level and bundled forms (Theorems 549–550), additive-free locality (Theorem 551), and Geometric Covariance via the stabiliser GNS representation (Theorem 552) with orbit-invariance of factoriality (Theorem 553) and the upgrade to a \*-algebra isomorphism (Theorem 554).
  - *§10.6.3 Relative Commutants of Nested Local Algebras in Curved Spacetime (p. 305, items 555–563).* The curved counterpart of §10.5.4: the relative commutant of a nested pair inside a containing region (Definition 555), its containment in the larger algebra, commutation with the smaller, and containment of the centre (Theorems 556–558), irreducible inclusions (Definition 559) and their consequences (Theorems 560–561), plus the abelian/centre facts specialised to curved local algebras (Theorems 562–563).
  - *§10.6.4 Purity of States on Local Algebras in Curved Spacetime (p. 306, items 564–568).* Each local algebra is a unital C\*-algebra with its own state space, so the abstract purity characterisations are registered per region: Pure $$\iff$$ Extreme Point (Theorem 564), Pure $$\iff$$ Irreducible GNS (Theorem 565), the GNS representation of a pure state generates a factor and indeed all of $$\mathcal{B}(H)$$ (Theorem 566), the Irreducible Dichotomy for a curved local algebra (Theorem 567), and GNS covariance for curved local algebras (Theorem 568).
  - *§10.6.5 Covariant States in Curved Spacetime (p. 307, items 569–570).* Covariant families of local states in curved spacetime (Definition 569) and their composition law (Lemma 570).
  - *§10.6.6 The Stabilizer GNS Unitary in Curved Spacetime (p. 308, items 571–577).* Since no quasilocal algebra exists on a generic Lorentzian spacetime, the covariance action restricts to the stabiliser subgroup $$\mathrm{Stab}(\mathbf{B})$$ of a region, giving automorphisms of the single local algebra $$\mathfrak{U}(\mathbf{B})$$ (Definition 571) that form a genuine group action (Lemma 572). A stabiliser-invariant state carries a unitary GNS representation of $$\mathrm{Stab}(\mathbf{B})$$ (Theorem 573), strongly continuous when the matrix coefficients are continuous (Theorem 574); a state both stabiliser-invariant and pure yields an irreducible covariant representation (Theorem 575); purity is invariant under the stabiliser action (Theorem 576), and GNS data transports along it (Theorem 577).
  - *§10.6.7 KMS States for a Killing Flow (p. 309, items 578–583).* Killing flows are identified as one-parameter subgroups of the stabiliser of a region, inducing a one-parameter automorphism group on $$\mathfrak{U}(\mathbf{B})$$ (Definition 578, Lemma 579). KMS states for a Killing flow (Definition 580) are the precise algebraic sense in which the Hartle–Hawking and Gibbons–Hawking states are thermal. Such a state at positive inverse temperature automatically carries a strongly continuous one-parameter unitary group on its GNS Hilbert space implementing the flow, yielding the curved-spacetime thermal representation—the analogue of the Minkowski vacuum representation (Theorem 581); these states form a convex set (Theorem 582), and the corresponding ground state is recorded alongside them (Definition 583).

- **§10.7 General Covariance: Nets on Pullback-Related Metrics (pp. 310–312).** Two definitions, and the newest structural addition to the blueprint. The gauge group of general relativity is the full diffeomorphism group of $$M$$, so the physical content of a spacetime is its diffeomorphism-equivalence class and not the pair $$(M, g)$$; the hole argument shows that treating a relabelling as physical would destroy determinism, and Leibniz equivalence resolves it by declaring diffeomorphic models to represent the same physical situation. Accordingly, an equivalence of Haag–Kastler nets is defined (Definition 584) as a chosen family of unital \*-isomorphisms $$\Theta_\mathbf{B} : \mathfrak{U}_1(\mathbf{B}) \to \mathfrak{U}_2(e(\mathbf{B}))$$ along a basis-set-preserving bijection $$e$$ of carriers, natural with respect to the isotony embeddings. The carriers are related by data rather than by a type equality, deliberately: an equality of carrier types cannot be transported along and would force every comparison through a cast. A net theory is then a section assigning a net to every Lorentzian spacetime, and it is generally covariant when the nets over $$L$$ and over its pullback $$\psi^* L$$ are equivalent along $$\psi$$ (Definition 585). Four points are worth carrying away: this is a **postulate, not a theorem**—nothing forces the two nets to be isomorphic, and it says nothing about backgrounds that are not diffeomorphism-related; the morphism is specified geometrically rather than causally, because a purely causal morphism would admit the dilations (Theorems 355–356) and thereby demand a scale covariance that is false for a massive theory; the relabelling must be $$\psi$$ and not the identity, since a basis set of one metric is in general not a basis set of the other; and general covariance is a property of the section $$L \mapsto \mathfrak{U}_L$$, not a sixth field of the net structure, so no restriction to diffeomorphisms connected to the identity is needed here.


## What is Being Formalised

Only the content of Chapter 10 is formalised in Lean. Its items are numbered consecutively from Definition 13 through Definition 585 — 570 declarations, plus the three standing conventions of §10.2 and §10.3 — and **every one of them is listed below**, in numerical order, under the blueprint subsection in which it appears. Each entry links to the node in the web blueprint and names the principal Lean declaration that realises it; where a node maps onto several declarations, the count of the remainder is shown. This list is derived mechanically from the blueprint's own `\lean` and `\leanok` annotations, so it can be checked line by line against the source.

The lower numbers, 1 through 12, label supporting theorems and definitions introduced along the way in the motivational Chapters 4–9. None of them carries a Lean declaration, and they are **not** formalised: C\*-spectrum invariance under inclusion (Theorem 1), uniqueness of the C\*-norm (Theorem 2), strong density of unital \*-algebras (Theorem 3), the Bounded Linear Transformation Theorem (Theorem 4), Gelfand–Naimark (Theorem 5), the rarity of primitive abelian C\*-algebras (Lemma 6), existence of a Lorentz metric (Theorem 7), causal convexity and strong causality (Definitions 8–9), properties of the Alexandrov topology (Theorem 10), Lorentzian spacetime (Definition 11), and the local observable (Definition 12).

### §10.1 GNS Construction (pp. 29–38)

**§10.1.1 GNS Construction Theorem (p. 29)**

- [**Definition 13**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:state) — State · `Physicslib4.GNS.State` (+1 more)
- [**Definition 14**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:cyclic-vector) — Cyclic Vector · `Physicslib4.GNS.IsCyclicVector`
- [**Theorem 15**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-construction-theorem) — GNS Construction Theorem · `Physicslib4.GNS.gns_construction`

**§10.1.2 Auxiliary Results Used in the Proof (p. 35)**

- [**Lemma 16**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cauchy-schwarz-inequality) — Cauchy–Schwarz Inequality · `Physicslib4.GNS.cauchy_schwarz_inequality`
- [**Lemma 17**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lmm1) — The two descriptions of the GNS left ideal $$\mathcal{N}$$ agree · `Physicslib4.GNS.lmm1`
- [**Lemma 18**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lmm2) — $$\mathcal{N}$$ is a closed linear subspace · `Physicslib4.GNS.lmm2`

### §10.2 Spectral Theorems (pp. 38–155)

**§10.2.1 · Elementary Properties of Bounded Operators (p. 39)**

- [**Definition 19**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:inner-product) — Inner Product · `InnerProductSpace`
- [**Definition 20**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:induced-norm) — Norm Induced by an Inner Product · `norm_eq_sqrt_re_inner`
- [**Definition 21**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-operator-notation) — Bounded Operator Notation · `ContinuousLinearMap.le_opNorm` (+4 more)
- [**Convention 22**](blueprint/chptr-haag-kastler-axioms-blueprint.html#conv:nonzero-hilbert-space) — The Hilbert Space is Non-Zero *(a standing convention, not a declaration; it carries no Lean annotation)*

**§10.2.1 · Elementary Properties of Bounded Operators › Preliminaries: Notation (p. 40)**

- [**Definition 23**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:identity-operator) — The Identity Operator · `ContinuousLinearMap.id_apply` (+1 more)
- [**Definition 24**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:indicator-function) — Indicator Function · `Set.indicator` (+2 more)
- [**Definition 25**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:identity-and-indicator) — The Identity Operator and Indicator Functions · `Physicslib4.Spectral.one_apply_and_indicator_apply`
- [**Definition 26**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:orthogonal-complement) — Orthogonal Complement · `Physicslib4.Spectral.mem_span_orthogonal_iff`
- [**Proposition 27**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:basic-integral-properties) — Basic Properties of the Integral, and Integration over a Subset · `MeasureTheory.integral_indicator` (+4 more)
- [**Proposition 28**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.43) — Cauchy–Schwarz Inequality · `inner_mul_inner_self_le` (+1 more)
- [**Proposition 29**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:reverse-triangle-inequality) — Reverse Triangle Inequality · `abs_norm_sub_norm_le`
- [**Proposition 30**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:continuity-of-norm-and-inner-product) — Continuity of the Norm and Inner Product · `Filter.Tendsto.norm` (+1 more)
- [**Lemma 31**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bounded-operators-form-a-banach-space) — Bounded Operators form a Banach Space · `Physicslib4.Spectral.completeSpace_boundedOp`
- [**Definition 32**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-inverse) — Bounded Inverse · `isUnit_iff_exists`
- [**Definition 33**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-operator-resolvent-and-spectrum) — Resolvent and Spectrum · `Physicslib4.Spectral.mem_resolventSet_iff_isUnit_sub_smul` (+1 more)
- [**Theorem 34**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-a.52) — Riesz Theorem · `Physicslib4.Spectral.riesz_representation`
- [**Definition 35**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:adjoint-bounded) — Adjoint of a Bounded Operator · `ContinuousLinearMap.adjoint` (+1 more)
- [**Proposition 36**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:adjoint-is-bounded) — The Adjoint is a Bounded Operator · `Physicslib4.Spectral.norm_adjoint`
- [**Lemma 37**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:adjoint-algebra) — Algebraic Properties of the Adjoint · `Physicslib4.Spectral.adjoint_add` (+4 more)

**§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › Projection-Valued Measures (p. 45)**

- [**Definition 38**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-orthogonal-projection) — Orthogonal Projection · `IsStarProjection` (+2 more)
- [**Lemma 39**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:projection-norm-decreasing) — Orthogonal Projections are Norm-Decreasing · `Physicslib4.Spectral.norm_apply_le_of_isStarProjection`
- [**Definition 40**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:projection-valued-measure) — Projection-Valued Measure · `Physicslib4.Spectral.ProjectionValuedMeasure`
- [**Theorem 41**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:projection-valued-measures-associated-measure) — Projection-Valued Measure's Associated Measure · `Physicslib4.Spectral.ProjectionValuedMeasure.existsUnique_assoc`
- [**Theorem 42**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:operator-valued-integration) — Operator-Valued Integration · `Physicslib4.Spectral.ProjectionValuedMeasure.existsUnique_integral`
- [**Definition 43**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-sesquilinear-form) — (Bounded) Sesquilinear Form · `Physicslib4.Spectral.BoundedSesquilinearForm`
- [**Definition 44**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-quadratic-form) — (Bounded) Quadratic Form · `Physicslib4.Spectral.IsBoundedQuadraticForm`
- [**Theorem 45**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:complex-valued-simple-approximation-theorem) — Complex-Valued Simple Approximation Theorem · `Physicslib4.Spectral.exists_simpleFunc_tendstoUniformly`
- [**Lemma 46**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma1-of-operator-valued-integration) — The Quadratic Form of a Bounded Measurable Function · `Physicslib4.Spectral.ProjectionValuedMeasure.isBoundedQuadraticForm_integral`
- [**Proposition 47**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:Q-indicator-bounded-form) — The Quadratic Form of an Indicator Function is Bounded · `Physicslib4.Spectral.ProjectionValuedMeasure.isBoundedQuadraticForm_integral_indicator` (+1 more)
- [**Proposition 48**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:Q-simple-bounded-form) — The Quadratic Form of a Simple Function is Bounded · `Physicslib4.Spectral.ProjectionValuedMeasure.isBoundedQuadraticForm_integral_simpleFunc`
- [**Proposition 49**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:Q-measurable-bounded-form) — The Quadratic Form of a Bounded Measurable Function is Bounded · `Physicslib4.Spectral.ProjectionValuedMeasure.isBoundedQuadraticForm_integral_bddMeasurable`
- [**Proposition 50**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.61) — Properties of the Sesquilinear Form Associated to a Quadratic Form · `Physicslib4.Spectral.polarization_diag` (+2 more)
- [**Lemma 51**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:sesquilinear-linear-combination) — Linear Combinations of Sesquilinear Forms are Sesquilinear · `Physicslib4.Spectral.exists_sesquilinearForm_sum`
- [**Lemma 52**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:sesquilinear-pointwise-limit) — Pointwise Limits of Sesquilinear Forms are Sesquilinear · `Physicslib4.Spectral.exists_sesquilinearForm_of_tendsto`
- [**Lemma 53**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bqf-linear-combination) — Linear Combinations of Bounded Quadratic Forms are Bounded Quadratic Forms · `Physicslib4.Spectral.IsBoundedQuadraticForm.sum`
- [**Lemma 54**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bqf-pointwise-limit) — Uniformly Bounded Pointwise Limits of Bounded Quadratic Forms · `Physicslib4.Spectral.isBoundedQuadraticForm_of_tendsto`
- [**Proposition 55**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.63) — A Bounded Quadratic Form Determines a Unique Bounded Operator · `Physicslib4.Spectral.existsUnique_operator_of_isBoundedQuadraticForm`
- [**Proposition 56**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-of-indicator) — Integral of an Indicator Function · `Physicslib4.Spectral.ProjectionValuedMeasure.integral_indicator`
- [**Proposition 57**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-norm-bound) — Norm Bound for the Operator-Valued Integral · `Physicslib4.Spectral.ProjectionValuedMeasure.norm_integral_le`
- [**Lemma 58**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma2-of-operator-valued-integration) — Orthogonality of Spectral Projections on a Disjoint Cover · `Physicslib4.Spectral.ProjectionValuedMeasure.inner_eq_zero_of_disjoint` (+1 more)
- [**Lemma 59**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma-1) — Operator Norm via the Inner Product · `Physicslib4.Spectral.opNorm_eq_sSup_inner`
- [**Proposition 60**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-norm-bound-simple) — Norm Bound for the Integral of a Simple Function · `Physicslib4.Spectral.ProjectionValuedMeasure.norm_integral_simple_le`
- [**Proposition 61**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-as-limit-of-simple) — The Integral as a Limit of Integrals of Simple Functions · `Physicslib4.Spectral.ProjectionValuedMeasure.tendsto_integral_of_tendstoUniformly`
- [**Proposition 62**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-multiplicative) — Operator-Valued Integration is Multiplicative · `Physicslib4.Spectral.ProjectionValuedMeasure.integral_mul`
- [**Proposition 63**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-mult-indicator) — Multiplicativity of the Integral for Indicator Functions · `Physicslib4.Spectral.ProjectionValuedMeasure.integral_indicator_mul`
- [**Proposition 64**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-mult-simple) — Multiplicativity of the Integral for Simple Functions · `Physicslib4.Spectral.ProjectionValuedMeasure.integral_simpleFunc_mul`
- [**Proposition 65**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:products-converge-uniformly) — Products of Uniform Approximants Converge Uniformly · `Physicslib4.Spectral.tendstoUniformly_mul_of_bounded`
- [**Proposition 66**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-mult-measurable) — Multiplicativity of the Integral for Bounded Measurable Functions · `Physicslib4.Spectral.ProjectionValuedMeasure.integral_bddMeasurable_mul`
- [**Proposition 67**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-conjugation) — Operator-Valued Integration Intertwines Conjugation and the Adjoint · `Physicslib4.Spectral.ProjectionValuedMeasure.integral_conj`

**§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › Stage 1: The Continuous Functional Calculus (p. 80)**

- [**Lemma 68**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma-2) — Bounded Operator Product is Submultiplicative · `norm_mul_le`
- [**Proposition 69**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.34) — Absolute Convergence Implies Convergence in a Banach Space · `Summable.of_norm`
- [**Lemma 70**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-7.6) — Neumann Series for a Contraction · `Physicslib4.Spectral.isUnit_one_sub` (+1 more)
- [**Theorem 71**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:analytic-equivalence-theorem) — Analytic Equivalence Theorem · `Complex.analyticOnNhd_iff_differentiableOn`
- [**Theorem 72**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:maximum-modulus-principle) — Maximum Modulus Principle · `Complex.exists_mem_frontier_isMaxOn_norm` (+1 more)
- [**Proposition 73**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.5) — The Spectrum is Closed, Bounded and Non-Empty · `Physicslib4.Spectral.mem_resolventSet_of_norm_lt`
- [**Proposition 74**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:resolvent-holomorphy-and-neumann-series) — Operator-Norm Holomorphy and the Neumann Series of the Resolvent · `Physicslib4.Spectral.isOpen_resolventSet` (+2 more)
- [**Proposition 75**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.3) — The Orthogonal Complement of the Range is the Kernel of the Adjoint · `ContinuousLinearMap.orthogonal_range`
- [**Lemma 76**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-7.8) — The $$b^2$$ Inequality for a Self-Adjoint Operator · `Physicslib4.Spectral.sq_norm_sub_smul_apply_le`
- [**Proposition 77**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:bounded-operators-are-continuous) — Bounded Operators are Continuous · `Physicslib4.Spectral.continuous_iff_exists_bound`
- [**Proposition 78**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.7) — The Spectrum of a Self-Adjoint Operator is Real · `Physicslib4.Spectral.spectrum_subset_real`
- [**Theorem 79**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:heine-borel-theorem) — Heine–Borel Theorem · `Metric.isCompact_iff_isClosed_bounded`
- [**Lemma 80**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spectrum-is-compact-metric-measurable) — The Spectrum is a Compact Metric Measurable Space · `Physicslib4.Spectral.isCompact_spectrum` (+1 more)
- [**Definition 81**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spectral-radius) — Spectral Radius · `spectralRadius`
- [**Corollary 82**](blueprint/chptr-haag-kastler-axioms-blueprint.html#crllr:crllr-1) — The Spectral Radius is at Most the Operator Norm · `spectrum.spectralRadius_le_nnnorm`
- [**Proposition 83**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.2) — The Adjoint Preserves the Operator Norm · `Physicslib4.Spectral.norm_adjoint` (+1 more)
- [**Proposition 84**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:continuity-of-the-adjoint) — Continuity of the Adjoint · `Physicslib4.Spectral.tendsto_adjoint`
- [**Theorem 85**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gelfand-formula) — Gelfand's Formula for the Spectral Radius · `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`
- [**Lemma 86**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-8.1) — The Norm of a Self-Adjoint Operator is its Spectral Radius · `IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm`
- [**Lemma 87**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-ex-8.3.1) — A Product with a Non-Invertible Commuting Factor is Non-Invertible · `Physicslib4.Spectral.not_isUnit_mul_of_commute`
- [**Theorem 88**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:fundamental-theorem-of-algebra) — Fundamental Theorem of Algebra · `Complex.isAlgClosed`
- [**Lemma 89**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spectral-mapping-theorem) — Spectral Mapping Theorem · `spectrum.map_polynomial_aeval`
- [**Lemma 90**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:real-polynomial-self-adjoint) — A Real Polynomial in a Self-Adjoint Operator is Self-Adjoint · `Physicslib4.Spectral.isSelfAdjoint_aeval_real`
- [**Definition 91**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:separates-points) — Separates Points · `Subalgebra.SeparatesPoints`
- [**Theorem 92**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:stone-weierstrass-real) — Stone–Weierstrass for Real Numbers · `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`
- [**Theorem 93**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:boundedness-theorem) — Boundedness Theorem · `IsCompact.exists_bound_of_continuousOn`
- [**Theorem 94**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:bounded-linear-transformation-theorem) — Bounded Linear Transformation Theorem · `Physicslib4.Spectral.existsUnique_extension_of_dense`
- [**Proposition 95**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.3) — The Continuous Functional Calculus · `Physicslib4.Spectral.existsUnique_realCalculus` (+1 more)
- [**Definition 96**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:non-negative-operator) — Non-Negative Bounded Operator · `ContinuousLinearMap.IsPositive`
- [**Lemma 97**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-prblm-7.4.8) — Invertibility is an Open Condition · `Units.isOpen`
- [**Theorem 98**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:composition-theorem) — Composition Theorem · `ContinuousAt.comp`
- [**Proposition 99**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.4) — Properties of the Continuous Functional Calculus · `Physicslib4.Spectral.realCalculus_properties`
- [**Proposition 100**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:cfc-multiplicative) — The Continuous Functional Calculus is Multiplicative · `Physicslib4.Spectral.realCalculus_mul`
- [**Proposition 101**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:cfc-self-adjoint) — The Continuous Functional Calculus Yields Self-Adjoint Operators · `Physicslib4.Spectral.isSelfAdjoint_realCalculus`
- [**Proposition 102**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:cfc-non-negative) — The Continuous Functional Calculus Preserves Non-Negativity · `Physicslib4.Spectral.isPositive_realCalculus`
- [**Proposition 103**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:cfc-norm) — Norm of an Operator from the Continuous Functional Calculus · `Physicslib4.Spectral.norm_realCalculus`
- [**Proposition 104**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:cfc-spectral-mapping) — Spectral Mapping for the Continuous Functional Calculus · `Physicslib4.Spectral.spectrum_realCalculus`

**§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › Stage 2: An Operator-Valued Riesz Representation Theorem (p. 107)**

- [**Theorem 105**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:riesz-representation) — Riesz Representation · `Physicslib4.Spectral.existsUnique_measure_of_positive_linear`
- [**Proposition 106**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:associated-measures-self-adjoint) — The Measures Associated to a Self-Adjoint Operator · `Physicslib4.Spectral.existsUnique_assocMeasure`
- [**Definition 107**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-8.6) — The Quadratic Form Associated to a Bounded Measurable Function · `Physicslib4.Spectral.borelForm`
- [**Lemma 108**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:associated-measures-are-finite) — The Associated Measures are Finite · `Physicslib4.Spectral.assocMeasure_univ`
- [**Proposition 109**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.7) — The Associated Quadratic Form is Bounded · `Physicslib4.Spectral.isBoundedQuadraticForm_borelForm`
- [**Definition 110**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:F-class) — The Class of Functions with Bounded Quadratic Form · `Physicslib4.Spectral.FClass`
- [**Proposition 111**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:Q-is-linear) — The Map $$f \mapsto Q_f$$ is Linear · `Physicslib4.Spectral.borelForm_add` (+1 more)
- [**Proposition 112**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F-homogeneous) — Homogeneity of the Quadratic Form of a Linear Combination · `Physicslib4.Spectral.borelForm_smul_of_mem_FClass`
- [**Proposition 113**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F-sesquilinear) — The Associated Form of a Linear Combination is Sesquilinear · `Physicslib4.Spectral.isSesquilinearForm_polarization_borelForm`
- [**Proposition 114**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F-bounded) — The Quadratic Form of a Linear Combination is Bounded · `Physicslib4.Spectral.bounded_borelForm_of_mem_FClass` (+1 more)
- [**Proposition 115**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F-contains-continuous) — The Class Contains the Continuous Functions · `Physicslib4.Spectral.continuous_mem_FClass`
- [**Proposition 116**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.62) — The Quadratic Form of a Bounded Operator · `Physicslib4.Spectral.isBoundedQuadraticForm_inner` (+1 more)
- [**Proposition 117**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F-closed-under-limits) — The Class is Closed under Bounded Pointwise Limits · `Physicslib4.Spectral.mem_FClass_of_tendsto`
- [**Theorem 118**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:bounded-convergence-theorem) — Bounded Convergence Theorem · `Physicslib4.Spectral.tendsto_integral_of_boundedPointwiseLimit`
- [**Definition 119**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:algebra-of-sets) — Algebra of Sets · `MeasureTheory.IsSetAlgebra`
- [**Theorem 120**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:archimedean-property) — Archimedean Property · `exists_nat_one_div_lt`
- [**Lemma 121**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-prblm-8.3.3a) — The Class $$\mathcal{L}_0$$ is an Algebra Containing the Open Sets · `Physicslib4.Spectral.isSetAlgebra_L0`
- [**Definition 122**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:L0-class) — The Class $$\mathcal{L}_0$$ · `Physicslib4.Spectral.L0`
- [**Proposition 123**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:L0-contains-empty) — The Empty Set Lies in $$\mathcal{L}_0$$ · `Physicslib4.Spectral.empty_mem_L0`
- [**Proposition 124**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:L0-complement) — $$\mathcal{L}_0$$ is Closed under Complements · `Physicslib4.Spectral.compl_mem_L0`
- [**Proposition 125**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:L0-union) — $$\mathcal{L}_0$$ is Closed under Finite Unions · `Physicslib4.Spectral.union_mem_L0`
- [**Proposition 126**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:L0-contains-closed) — $$\mathcal{L}_0$$ Contains all Closed Sets · `Physicslib4.Spectral.isClosed_mem_L0`
- [**Definition 127**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bump-function) — Bump Function · `Physicslib4.Spectral.IsBumpFunction`
- [**Theorem 128**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:existence-of-bump-functions) — Existence of Bump Functions · `Physicslib4.Spectral.exists_isBumpFunction`
- [**Theorem 129**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:monotone-class-theorem) — Monotone Class Theorem · `Physicslib4.Spectral.generateFrom_subset_of_isMonotoneClass`
- [**Lemma 130**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-prblm-8.3.3b) — Extension from an Algebra to the Generated $$\sigma$$-Algebra · `Physicslib4.Spectral.IsBorelGenerating.indicator_mem`
- [**Theorem 131**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:monotone-convergence-theorem-nonincreasing) — Monotone Convergence Theorem, Non-Increasing Case · `tendsto_atTop_ciInf`
- [**Lemma 132**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pointwise-limits-of-borel-measurable-functions) — Pointwise Limits of Uniformly Bounded, Borel-Measurable Functions · `Physicslib4.Spectral.measurable_of_tendsto_pointwise` (+1 more)
- [**Lemma 133**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-prblm-8.3.3c) — A Class Containing the Continuous Functions and Closed under Bounded Limits is Everything · `Physicslib4.Spectral.IsBorelGenerating.eq_bddMeasurable`

**§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › The Bounded Borel Functional Calculus (p. 127)**

- [**Definition 134**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-8.8) — The Bounded Borel Functional Calculus · `Physicslib4.Spectral.existsUnique_borelCalculus` (+1 more)
- [**Lemma 135**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma-3) — The Operator of a Real-Valued Function is Self-Adjoint · `Physicslib4.Spectral.isSelfAdjoint_borelCalculus`
- [**Proposition 136**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.59) — Polarization Identity · `Physicslib4.Spectral.sesquilinear_polarization`
- [**Proposition 137**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.9) — The Bounded Borel Functional Calculus is Multiplicative · `Physicslib4.Spectral.borelCalculus_mul`
- [**Definition 138**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:F1-F2-classes) — The Classes $$\mathcal{F}_1$$ and $$\mathcal{F}_2$$ · `Physicslib4.Spectral.F1Class` (+1 more)
- [**Proposition 139**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F1-vector-space) — $$\mathcal{F}_1$$ is a Vector Space · `Physicslib4.Spectral.isBorelGenerating_F1Class`
- [**Proposition 140**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:Q-continuous-under-limits) — The Quadratic Form is Continuous under Bounded Pointwise Limits · `Physicslib4.Spectral.tendsto_borelForm`
- [**Proposition 141**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F1-closed-under-limits) — $$\mathcal{F}_1$$ is Closed under Bounded Pointwise Limits · `Physicslib4.Spectral.mem_F1Class_of_tendsto` (+1 more)
- [**Proposition 142**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F2-is-everything) — $$\mathcal{F}_2$$ Contains all Bounded Borel Functions · `Physicslib4.Spectral.isBorelGenerating_F2Class` (+1 more)

**§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › The Spectral Measure (p. 133)**

- [**Theorem 143**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-8.10) — The Spectral Measure of a Self-Adjoint Operator · `Physicslib4.Spectral.exists_spectralMeasure`
- [**Proposition 144**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:mua-projection) — Each Spectral Projection is an Orthogonal Projection · `Physicslib4.Spectral.isStarProjection_borelCalculus_indicator`
- [**Proposition 145**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:mua-multiplicative) — Spectral Projections Multiply to the Intersection · `Physicslib4.Spectral.borelCalculus_indicator_mul`
- [**Proposition 146**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:mua-empty-and-whole) — Spectral Projections of the Empty Set and the Whole Spectrum · `Physicslib4.Spectral.borelCalculus_indicator_empty` (+1 more)
- [**Proposition 147**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:mua-countably-additive) — Spectral Projections are Countably Additive · `Physicslib4.Spectral.hasSum_borelCalculus_indicator`
- [**Theorem 148**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:monotone-convergence-theorem) — Monotone Convergence Theorem · `Physicslib4.Spectral.tendsto_iff_isBounded_of_monotone` (+1 more)
- [**Lemma 149**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma-4) — Sums of Pairwise Orthogonal Projections · `Physicslib4.Spectral.exists_isStarProjection_tendsto_partialSum`
- [**Proposition 150**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:orthogonal-sum-converges) — Partial Sums of Pairwise Orthogonal Projections Converge · `Physicslib4.Spectral.exists_tendsto_partialSum_of_isStarProjection`
- [**Proposition 151**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:orthogonal-sum-is-projection) — The Limit of the Partial Sums is a Bounded Orthogonal Projection · `Physicslib4.Spectral.exists_isStarProjection_tendsto_partialSum'`
- [**Proposition 152**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:orthogonal-sum-range) — The Range of the Limit Projection · `Physicslib4.Spectral.range_eq_topologicalClosure_iSup_of_tendsto_partialSum`
- [**Proposition 153**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:mua-indicator-integral) — Spectral Projections are the Integrals of their Indicators · `Physicslib4.Spectral.spectralMeasure_integral_indicator`
- [**Proposition 154**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:mua-bounded-calculus-agrees) — The Two Bounded Functional Calculi Agree · `Physicslib4.Spectral.borelCalculus_eq_integral`
- [**Proposition 155**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:mua-integrates-to-A) — The Spectral Measure Integrates to the Operator · `Physicslib4.Spectral.spectralMeasure_integral_id`

**§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › Uniqueness of the Spectral Measure (p. 147)**

- [**Theorem 156**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-prblm-8.3.4) — Uniqueness of the Spectral Measure · `Physicslib4.Spectral.pvm_eq_of_integral_id_eq`
- [**Proposition 157**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:pvm-agree-on-polynomials) — Two Spectral Measures Agree on Polynomials · `Physicslib4.Spectral.pvm_integral_polynomial_eq`
- [**Proposition 158**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:pvm-agree-on-continuous) — Two Spectral Measures Agree on Continuous Functions · `Physicslib4.Spectral.pvm_integral_continuous_eq`
- [**Theorem 159**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:stone-weierstrass-complex) — Stone–Weierstrass for Complex Numbers · `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`
- [**Lemma 160**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma-5) — Polynomials are Dense in the Continuous Functions on the Spectrum · `Physicslib4.Spectral.dense_polynomial_spectrum`
- [**Proposition 161**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:pvm-agree-on-measurable) — Two Spectral Measures Agree on Bounded Measurable Functions · `Physicslib4.Spectral.pvm_integral_bddMeasurable_eq`
- [**Theorem 162**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:spectral-theorem-for-bounded-operators) — Spectral Theorem for Bounded, Self-Adjoint Operators · `Physicslib4.Spectral.existsUnique_spectralMeasure`
- [**Definition 163**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:functional-calculus) — Functional Calculus · `Physicslib4.Spectral.functionalCalculus`

### §10.3 Unbounded Spectral Theorems (pp. 155–232)

**§10.3.1 · Unbounded Operators › Adjoint and Closure of an Unbounded Operator (p. 156)**

- [**Definition 164**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-3.1) — Unbounded Operator · `LinearPMap` (+1 more)
- [**Proposition 165**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:convergence-facts) — Convergence Facts for Sequences and Series · `tendsto_atTop_ciSup` (+5 more)
- [**Lemma 166**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-dense-testing) — Equality Testing on a Dense Subspace, First Slot · `Dense.eq_of_inner_left`
- [**Lemma 167**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-dense-testing-second-slot) — Equality Testing on a Dense Subspace, Second Slot · `Dense.eq_of_inner_right`
- [**Definition 168**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-9.1) — Adjoint of an Unbounded Operator · `LinearPMap.adjointDomain` (+3 more)
- [**Proposition 169**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:adjoint-well-defined) — The Adjoint is Well Defined · `Physicslib4.Spectral.Unbounded.existsUnique_adjoint_apply`
- [**Proposition 170**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-linearity-of-the-adjoint) — Linearity of the Adjoint · `Physicslib4.Spectral.Unbounded.smul_add_mem_adjoint_domain` (+1 more)
- [**Lemma 171**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:characterizing-adjoint-domain-membership) — Characterizing Membership in the Adjoint's Domain · `Physicslib4.Spectral.Unbounded.mem_adjoint_domain_iff_exists` (+1 more)
- [**Definition 172**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-9.2) — Symmetric Operator · `Physicslib4.Spectral.Unbounded.IsSymmetric` (+1 more)
- [**Definition 173**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-9.3) — Extension of an Operator · `LinearPMap.le` (+2 more)
- [**Proposition 174**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.4) — Symmetric Operators and the Adjoint · `Physicslib4.Spectral.Unbounded.isSymmetric_iff_le_adjoint`
- [**Definition 175**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-9.5) — Self-Adjoint Operator · `LinearPMap.instStar` (+1 more)
- [**Definition 176**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:product-hilbert-space) — The Product Hilbert Space $$\mathbf{H} \times \mathbf{H}$$ · `WithLp.instProdInnerProductSpace` (+2 more)
- [**Theorem 177**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:sequential-closedness) — Sequential Characterization of Closed Sets and Closures · `isSeqClosed_iff_isClosed` (+1 more)
- [**Lemma 178**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:componentwise-convergence) — Convergence in $$\mathbf{H} \times \mathbf{H}$$ is Componentwise · `Prod.tendsto_iff`
- [**Definition 179**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-9.6) — Closed and Closable Operators · `LinearPMap.graph` (+4 more)
- [**Proposition 180**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:closure-linearity-and-sequential-description) — Linearity and the Sequential Description of the Closure · `Physicslib4.Spectral.Unbounded.hasDenseDomain_closure` (+5 more)
- [**Lemma 181**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:closure-of-symmetric-is-symmetric) — The Closure of a Symmetric Operator is Symmetric · `Physicslib4.Spectral.Unbounded.isSymmetric_closure`
- [**Definition 182**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-9.7) — Essentially Self-Adjoint Operator · `Physicslib4.Spectral.Unbounded.IsEssentiallySelfAdjoint`

**§10.3.1 · Unbounded Operators › Elementary Properties of Adjoints and Closed Operators (p. 163)**

- [**Definition 183**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:closed-linear-map-on-a-subspace) — Closed Linear Map on a Subspace · `LinearPMap.IsClosed` (+1 more)
- [**Proposition 184**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.8) — Closedness of the Adjoint's Graph; Closability of Symmetric Operators · `Physicslib4.Spectral.Unbounded.isClosable_of_isSymmetric` (+1 more)
- [**Proposition 185**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.10) — The Adjoint of a Closure · `Physicslib4.Spectral.Unbounded.adjoint_closure_eq_adjoint`
- [**Lemma 186**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:extension-reverses-adjoint-domains) — Extension Reverses Adjoint Domains · `Physicslib4.Spectral.Unbounded.adjoint_le_adjoint_of_le`
- [**Proposition 187**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.11) — Uniqueness of the Self-Adjoint Extension of an Essentially Self-Adjoint Operator · `Physicslib4.Spectral.Unbounded.existsUnique_isSelfAdjoint_extension` (+1 more)
- [**Definition 188**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kernel-of-an-unbounded-operator) — Kernel of an Unbounded Operator · `Physicslib4.Spectral.Unbounded.ker`
- [**Definition 189**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:range-of-an-unbounded-operator) — Range of an Unbounded Operator · `Physicslib4.Spectral.Unbounded.range`
- [**Proposition 190**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.49) — Orthogonal Decomposition and the Double Complement · `Physicslib4.Spectral.Unbounded.existsUnique_add_mem_orthogonal` (+1 more)
- [**Corollary 191**](blueprint/chptr-haag-kastler-axioms-blueprint.html#crllr:trivial-complement-characterizes-density) — Trivial Complement Characterizes Density · `Physicslib4.Spectral.Unbounded.dense_iff_orthogonal_eq_bot`
- [**Proposition 192**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.12) — Orthogonal Complement of the Range · `Physicslib4.Spectral.Unbounded.orthogonal_range_eq_ker_adjoint`
- [**Proposition 193**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.13) — Adjoint of a Sum with a Bounded Operator · `Physicslib4.Spectral.Unbounded.adjoint_add_toPMap` (+1 more)
- [**Lemma 194**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:adjoint-of-scalar-multiple-of-identity) — Adjoint of a Scalar Multiple of the Identity · `Physicslib4.Spectral.Unbounded.adjoint_smul_id`
- [**Proposition 195**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.14) — Closedness of the Range from a Lower Bound · `Physicslib4.Spectral.Unbounded.isClosed_range_subSmul`

**§10.3.1 · Unbounded Operators › The Spectrum of an Unbounded Operator (p. 169)**

- [**Definition 196**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-9.16) — Resolvent Set and Spectrum of an Unbounded Operator · `Physicslib4.Spectral.Unbounded.pmapResolventSet` (+2 more)
- [**Lemma 197**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:uniqueness-of-resolvent) — Uniqueness of the Resolvent · `Physicslib4.Spectral.Unbounded.existsUnique_isResolvent`
- [**Lemma 198**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spectrum-notions-agree) — The Two Notions of Spectrum Agree for Bounded Operators · `Physicslib4.Spectral.Unbounded.pmapResolventSet_toPMap_top` (+1 more)
- [**Lemma 199**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:b-squared-inequality-symmetric) — The $$b^2$$ Inequality for Symmetric Operators · `Physicslib4.Spectral.Unbounded.sq_norm_le_of_isSymmetric`
- [**Theorem 200**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-9.17) — Spectrum of a Self-Adjoint Operator is Real · `Physicslib4.Spectral.Unbounded.pmapSpectrum_subset_real`

**§10.3.1 · Unbounded Operators › Conditions for Self-Adjointness and Essential Self-Adjointness (p. 172)**

- [**Theorem 201**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-9.21) — Essential Self-Adjointness via Dense Range · `Physicslib4.Spectral.Unbounded.isEssentiallySelfAdjoint_iff_dense_range`
- [**Definition 202**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-a.45) — Hilbert Space Direct Sum · `lp` (+1 more)
- [**Lemma 203**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:finite-direct-sum-dense) — The Finite Direct Sum is Dense · `Physicslib4.Spectral.Unbounded.dense_setOf_finite_support`
- [**Definition 204**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:unitary-operator) — Unitary Operator · `unitary` (+2 more)
- [**Definition 205**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:internal-orthogonal-decomposition) — Internal Orthogonal Decomposition · `Physicslib4.Spectral.Unbounded.IsInternalOrthogonalDecomposition`
- [**Proposition 206**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:polarization-identity) — Polarization Identity for the Inner Product · `inner_eq_sum_norm_sq_div_four` (+1 more)
- [**Lemma 207**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:internal-decomposition-unitary) — Internal Decompositions are Unitarily External Direct Sums · `Physicslib4.Spectral.Unbounded.hasSum_injective_of_isInternalOrthogonalDecomposition` (+2 more)
- [**Proposition 208**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.26) — Direct Sums of Bounded Self-Adjoint Operators · `Physicslib4.Spectral.Unbounded.isEssentiallySelfAdjoint_of_isDirectSumOperator` (+6 more)
- [**Proposition 209**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.26-internal) — Direct Sums of Bounded Self-Adjoint Operators, Internal Form · `Physicslib4.Spectral.Unbounded.isEssentiallySelfAdjoint_of_isInternalDirectSumOperator` (+6 more)

**§10.3.1 · Integration Against a Projection-Valued Measure (p. 180)**

- [**Convention 210**](blueprint/chptr-haag-kastler-axioms-blueprint.html#conv:section-integration) — Standing Hypotheses: Integration against a Projection-Valued Measure *(a standing convention, not a declaration; it carries no Lean annotation)*
- [**Lemma 211**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:associated-measure-total-mass) — The Associated Measure has Total Mass $$\left\| \psi \right\|^2$$ · `Physicslib4.Spectral.Unbounded.assoc_univ_eq` (+1 more)
- [**Lemma 212**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:norm-identity-bounded-integral) — Norm Identity for the Bounded Integral · `Physicslib4.Spectral.Unbounded.norm_sq_integral_apply`
- [**Definition 213**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-sesquilinear-form-on-a-subspace) — Sesquilinear Form on a Subspace · `Physicslib4.Spectral.Unbounded.SesquilinearFormOn`
- [**Definition 214**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-quadratic-form-on-a-subspace) — Quadratic Form on a Subspace · `Physicslib4.Spectral.Unbounded.IsQuadraticFormOn` (+2 more)
- [**Proposition 215**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:quadratic-forms-on-a-subspace-properties) — Properties of Quadratic Forms on a Subspace · `Physicslib4.Spectral.Unbounded.polarizationOn_eq_inner` (+1 more)
- [**Lemma 216**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:restriction-of-quadratic-form) — Restriction of a Quadratic Form to a Subspace · `Physicslib4.Spectral.Unbounded.isQuadraticFormOn_restrict` (+1 more)
- [**Theorem 217**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:monotone-convergence-theorem-for-integrals) — Monotone Convergence Theorem, for Integrals · `MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone` (+1 more)
- [**Theorem 218**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:dominated-convergence-theorem) — Dominated Convergence Theorem · `MeasureTheory.tendsto_integral_of_dominated_convergence` (+2 more)
- [**Proposition 219**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:additivity-of-the-integral-in-the-measure) — Linearity of the Integral in the Measure · `MeasureTheory.lintegral_add_measure` (+3 more)
- [**Proposition 220**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:monotonicity-of-the-integral-in-the-measure) — Monotonicity of the Integral in the Measure · `MeasureTheory.lintegral_mono'` (+1 more)
- [**Definition 221**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-a.46) — $$L^2$$ of a Measure Space · `MeasureTheory.MemLp` (+3 more)
- [**Proposition 222**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:countable-additivity-of-the-integral) — Countable Additivity of the Integral over a Disjoint Cover · `MeasureTheory.lintegral_iUnion` (+1 more)
- [**Proposition 223**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integrals-agree-when-measures-agree) — Integrals Agree when Measures Agree on a Set · `Physicslib4.Spectral.Unbounded.setLIntegral_congr_measure`
- [**Lemma 224**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:range-of-projection-is-kernel) — The Range of a Projection is the Kernel of its Complement · `Physicslib4.Spectral.Unbounded.range_eq_ker_one_sub` (+2 more)
- [**Lemma 225**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:closed-subspace-is-hilbert) — A Closed Subspace is a Separable Hilbert Space · `Physicslib4.Spectral.Unbounded.completeSpace_and_separableSpace_of_isClosed` (+2 more)
- [**Lemma 226**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:range-membership-concentrates-measure) — Range Membership Concentrates the Associated Measure · `Physicslib4.Spectral.Unbounded.assoc_compl_eq_zero` (+1 more)
- [**Lemma 227**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:norm-convergent-decomposition) — Norm-Convergent Decomposition over a Disjoint Cover · `Physicslib4.Spectral.Unbounded.hasSum_apply_of_partition` (+1 more)
- [**Lemma 228**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:l2-implies-l1) — $$L^2$$ Implies $$L^1$$ on a Finite Measure Space · `MeasureTheory.MemLp.integrable` (+1 more)
- [**Proposition 229**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.2) — Properties of the Integral against a Projection-Valued Measure · `Physicslib4.Spectral.Unbounded.integralDomain` (+7 more)
- [**Lemma 230**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bounded-on-set-range-in-domain) — Bounded on a Set Implies the Range Lies in the Domain · `Physicslib4.Spectral.Unbounded.range_subset_integralDomain` (+1 more)
- [**Proposition 231**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.1) — The Integral against a Projection-Valued Measure · `Physicslib4.Spectral.Unbounded.pmapIntegral` (+5 more)
- [**Proposition 232**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:coincidence-with-the-bounded-integral) — Coincidence with the Bounded Integral · `Physicslib4.Spectral.Unbounded.integralDomain_eq_top_of_bddMeasurable` (+1 more)
- [**Lemma 233**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:integral-ignores-null-sets) — The Integral Ignores Null Sets · `Physicslib4.Spectral.Unbounded.integralDomain_congr_of_null` (+1 more)
- [**Lemma 234**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:truncations-converge) — Truncations Converge to the Unbounded Integral · `Physicslib4.Spectral.Unbounded.tendsto_integral_truncation`
- [**Lemma 235**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:associated-measure-of-image) — The Associated Measure of a Bounded-Calculus Image · `Physicslib4.Spectral.Unbounded.assoc_integral_apply` (+1 more)
- [**Lemma 236**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:integral-preserves-spectral-subspaces) — The Integral Preserves Spectral Subspaces on which the Integrand is Bounded · `Physicslib4.Spectral.Unbounded.mapsTo_pmapIntegral_range` (+1 more)
- [**Proposition 237**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.3) — The Integral of a Real-Valued Function is Self-Adjoint · `Physicslib4.Spectral.Unbounded.isSelfAdjoint_pmapIntegral_of_real`

**§10.3.1 · The Spectral Theorem for Bounded Normal Operators (p. 198)**

- [**Definition 238**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.19) — Normal Operator · `IsStarNormal`
- [**Lemma 239**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:self-adjoint-is-normal) — Bounded Self-Adjoint Operators are Normal · `IsSelfAdjoint.isStarNormal`
- [**Lemma 240**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:power-growth-controlled-by-spectral-radius) — Power Growth is Controlled by the Spectral Radius · `Physicslib4.Spectral.Unbounded.tendsto_norm_pow_div_atTop`
- [**Lemma 241**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.22) — Spectral Radius of a Product of Commuting Operators · `Physicslib4.Spectral.Unbounded.spectralRadius_mul_le_of_commute`
- [**Lemma 242**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:adjoint-product-and-involution) — Adjoint of a Product; the Adjoint is an Involution · `ContinuousLinearMap.adjoint_comp` (+1 more)
- [**Proposition 243**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.21) — Norm Equals Spectral Radius for Normal Operators · `IsStarNormal.spectralRadius_eq_nnnorm`

**§10.3.1 · The Spectral Theorem for Bounded Normal Operators › Spectral Subspaces (p. 202)**

- [**Definition 244**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-7.14) — Spectral Subspaces · `Physicslib4.Spectral.Unbounded.spectralSubspace`
- [**Proposition 245**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.15) — Properties of Spectral Subspaces · `Physicslib4.Spectral.Unbounded.pvmOperator` (+3 more)
- [**Proposition 246**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.16) — Commuting Operators Preserve Spectral Subspaces · `Physicslib4.Spectral.Unbounded.commute_borelCalculus` (+1 more)

**§10.3.1 · The Spectral Theorem for Bounded Normal Operators › Almost Eigenvectors (p. 205)**

- [**Lemma 247**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:normality-balances-norms) — Normality Balances the Two Norms · `Physicslib4.Spectral.Unbounded.norm_adjoint_sub_smul_apply`
- [**Definition 248**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.24) — $$\varepsilon$$-Almost Eigenvector · `Physicslib4.Spectral.Unbounded.IsAlmostEigenvector`
- [**Lemma 249**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.25) — Almost Eigenvectors and the Spectrum of a Normal Operator · `Physicslib4.Spectral.Unbounded.isAlmostEigenvector_adjoint` (+1 more)
- [**Lemma 250**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.26) — Polynomials Preserve Almost Eigenvectors · `Physicslib4.Spectral.Unbounded.exists_const_isAlmostEigenvector_mvApply`
- [**Lemma 251**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:polynomials-in-normal-are-normal) — Polynomials in a Normal Operator are Normal · `Physicslib4.Spectral.Unbounded.mvApply` (+4 more)
- [**Lemma 252**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:restriction-of-normal-operator) — Restriction of a Normal Operator to a Doubly Invariant Subspace · `Physicslib4.Spectral.Unbounded.exists_restrict_isStarNormal`
- [**Lemma 253**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.27) — An Almost-Eigenvector Subspace for a Polynomial in a Normal Operator · `Physicslib4.Spectral.Unbounded.exists_subspace_isAlmostEigenvector`

**§10.3.1 · The Spectral Theorem for Bounded Normal Operators › The Two-Variable Spectral Mapping Theorem (p. 209)**

- [**Theorem 254**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.23) — Spectral Mapping for Polynomials in $$A$$ and $$A^*$$ · `Physicslib4.Spectral.Unbounded.spectrum_mvApply`
- [**Corollary 255**](blueprint/chptr-haag-kastler-axioms-blueprint.html#crllr:norm-of-polynomial-in-a-astar) — Norm of a Polynomial in $$A$$ and $$A^*$$ · `Physicslib4.Spectral.Unbounded.norm_mvApply`

**§10.3.1 · The Spectral Theorem for Bounded Normal Operators › The Continuous Functional Calculus for a Normal Operator (p. 211)**

- [**Theorem 256**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:continuous-functional-calculus-normal) — Continuous Functional Calculus for a Normal Operator · `Physicslib4.Spectral.Unbounded.mvPolyOn` (+9 more)

**§10.3.1 · From a Continuous Functional Calculus to a Projection-Valued Measure (p. 212)**

- [**Convention 257**](blueprint/chptr-haag-kastler-axioms-blueprint.html#conv:section-abstract) — Standing Hypotheses: The Abstract Functional Calculus *(a standing convention, not a declaration; it carries no Lean annotation)*
- [**Definition 258**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:abstract-continuous-functional-calculus) — Abstract Continuous Functional Calculus · `Physicslib4.Spectral.Unbounded.IsAbstractCalculus`
- [**Lemma 259**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-calculus-non-negative) — An Abstract Calculus is Non-Negative · `Physicslib4.Spectral.Unbounded.isSelfAdjoint_of_real` (+2 more)
- [**Definition 260**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:abstract-associated-measures) — The Measures Associated to an Abstract Calculus · `Physicslib4.Spectral.Unbounded.abstractMeasure` (+2 more)
- [**Lemma 261**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-associated-measures-finite) — The Abstract Associated Measures are Finite · `Physicslib4.Spectral.Unbounded.abstractMeasure_univ`
- [**Proposition 262**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:abstract-extended-forms-are-bounded) — The Extended Forms are Bounded Quadratic Forms · `Physicslib4.Spectral.Unbounded.isBoundedQuadraticForm_abstractForm` (+3 more)
- [**Definition 263**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:abstract-extended-calculus) — The Extended Calculus · `Physicslib4.Spectral.Unbounded.extendedCalculus` (+2 more)
- [**Lemma 264**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-extended-linear) — The Extended Calculus is Linear · `Physicslib4.Spectral.Unbounded.extendedCalculus_smul_add`
- [**Lemma 265**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-extended-convergence) — Off-Diagonal Formula and Bounded Convergence for the Extended Calculus · `Physicslib4.Spectral.Unbounded.polarization_abstractForm` (+1 more)
- [**Lemma 266**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-extended-real-self-adjoint) — Real Functions Give Self-Adjoint Operators · `Physicslib4.Spectral.Unbounded.isSelfAdjoint_extendedCalculus_of_real`
- [**Proposition 267**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:abstract-extended-multiplicative) — The Extended Calculus is Multiplicative · `Physicslib4.Spectral.Unbounded.extendedCalculus_mul`
- [**Lemma 268**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-extended-conjugation) — The Extended Calculus Respects Conjugation · `Physicslib4.Spectral.Unbounded.extendedCalculus_conj`
- [**Theorem 269**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:abstract-calculus-yields-pvm) — A Continuous Functional Calculus Yields a Projection-Valued Measure · `Physicslib4.Spectral.Unbounded.abstractPVM` (+2 more)
- [**Corollary 270**](blueprint/chptr-haag-kastler-axioms-blueprint.html#crllr:abstract-extended-norm-bound) — The Extended Calculus is Norm-Bounded · `Physicslib4.Spectral.Unbounded.norm_extendedCalculus_le`

**§10.3.1 · From a Continuous Functional Calculus to a Projection-Valued Measure › The Spectral Theorem for Bounded Normal Operators (p. 219)**

- [**Theorem 271**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.20) — Spectral Theorem for Bounded Normal Operators · `Physicslib4.Spectral.Unbounded.existsUnique_spectralMeasure_normal` (+1 more)

**§10.3.1 · The Cayley Transform (p. 220)**

- [**Lemma 272**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:unitary-is-normal) — Unitary Operators are Normal · `Physicslib4.Spectral.Unbounded.unitary_mul_adjoint`
- [**Lemma 273**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:unitary-spectrum-circle) — The Spectrum of a Unitary Operator Lies on the Unit Circle · `spectrum.subset_circle_of_unitary` (+1 more)
- [**Lemma 274**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cayley-map) — The Cayley Map and its Inverse · `Physicslib4.Spectral.Unbounded.unitCircleMinusOne` (+9 more)
- [**Theorem 275**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.28) — Cayley Transform · `Physicslib4.Spectral.Unbounded.IsCayleyTransform` (+1 more)
- [**Lemma 276**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cayley-spectral-mapping) — Spectral Mapping for the Cayley Transform · `Physicslib4.Spectral.Unbounded.mem_spectrum_iff_cayleyMap_mem_spectrum` (+1 more)

**§10.3.1 · Proof of the Spectral Theorem for Unbounded Self-Adjoint Operators (p. 225)**

- [**Theorem 277**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:change-of-variables) — Change of Variables for a Pushforward Measure · `MeasureTheory.lintegral_map_equiv` (+1 more)
- [**Lemma 278**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:borel-bijection-transports-pvm) — A Borel Bijection Transports a Projection-Valued Measure · `Physicslib4.Spectral.Unbounded.restrictPVM` (+2 more)
- [**Lemma 279**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cayley-omits-one) — The Cayley Transform Omits the Point $$1$$ · `Physicslib4.Spectral.Unbounded.spectralMeasure_singleton_one_eq_zero`
- [**Proposition 280**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.29) — Spectral Subspaces of the Cayley Transform · `Physicslib4.Spectral.Unbounded.pmapIntegral_cayleyInv_eq`
- [**Theorem 281**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.30) — Transporting the Spectral Measure through the Cayley Transform · `Physicslib4.Spectral.Unbounded.cayleyPVM` (+1 more)
- [**Theorem 282**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.4) — Spectral Theorem for Unbounded, Self-Adjoint Operators · `Physicslib4.Spectral.Unbounded.existsUnique_spectralMeasure_unbounded` (+1 more)

### §10.4 Spacetime and causal structure (pp. 232–263)

**§10.4 opening run — spacetime, tangent-vector causality, curves, trips, futures and pasts (p. 232)**

- [**Definition 283**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacetime) — Spacetime · `Physicslib4.Spacetime`
- [**Definition 284**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:standard-minkowski-spacetime) — Standard Minkowski Spacetime · `Physicslib4.StandardMinkowskiSpacetime`
- [**Definition 285**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:timelike-spacelike-null-vectors) — Timelike, Spacelike, or Null Vectors · `Physicslib4.Spacetime.IsTimelike` (+2 more)
- [**Lemma 286**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-classification) — Causal Classification · `Physicslib4.Spacetime.isTimelike_or_isNull_or_isSpacelike` (+5 more)
- [**Lemma 287**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:reverse-cauchy-schwarz) — Reverse Cauchy–Schwarz for Timelike Vectors · `Physicslib4.reverse_cauchy_schwarz_of_lorentzianAt` (+1 more)
- [**Lemma 288**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:timelike-cone-convexity) — Timelike Cone Convexity and Reverse Triangle Inequality · `Physicslib4.add_isTimelike_of_lorentzianAt` (+3 more)
- [**Definition 289**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:time-orientable) — Time Orientation · `Physicslib4.Spacetime.TimeOrientation` (+1 more)
- [**Definition 290**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-and-past-pointing-vectors) — Future and Past Pointing Vectors · `Physicslib4.Spacetime.IsFuturePointing` (+1 more)
- [**Lemma 291**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pointing-orientation) — Orientation of Pointing Vectors · `Physicslib4.Spacetime.isTimelike_or_isNull_of_isFuturePointing` (+2 more)
- [**Lemma 292**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cone-sign-lemma) — Sign Lemma for the Future Cone · `Physicslib4.nonneg_of_orthogonal_timelike` (+4 more)
- [**Lemma 293**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-definite) — Definiteness of the Spacelike Complement · `Physicslib4.eq_zero_of_forall_bilin_eq_zero` (+2 more)
- [**Lemma 294**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:future-cone-convexity) — Convexity of the Future Cone · `Physicslib4.Spacetime.isFuturePointing_add` (+10 more)
- [**Definition 295**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:paths) — Paths · `Physicslib4.Spacetime.Path` (+1 more)
- [**Definition 296**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:curves) — Curves · `Physicslib4.Spacetime.Curve` (+1 more)
- [**Definition 297**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:timelike-and-causal-smooth-curves) — Timelike and Causal Smooth Curves · `Physicslib4.Spacetime.IsTimelikeSmoothCurve` (+1 more)
- [**Definition 298**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-and-past-oriented-smooth-curves) — Future and Past Oriented Smooth Curves · `Physicslib4.Spacetime.IsFutureOrientedSmoothCurve` (+1 more)
- [**Theorem 299**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:smooth-curve-causal-well-defined) — Reparametrisation-Invariance of the Causal Type · `Physicslib4.Spacetime.isTimelikeSmoothCurve_ofPath_iff` (+1 more)
- [**Definition 300**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:oriented-smooth-curve) — Oriented Smooth Curve · `Physicslib4.Spacetime.OrientedSmoothCurve`
- [**Theorem 301**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:oriented-curve-well-defined) — Reparametrisation-Invariance of Orientation · `Physicslib4.Spacetime.isFutureOrientedCurve_ofPath_iff` (+1 more)
- [**Theorem 302**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:oriented-curve-projection) — The Forgetful Projection of Oriented Curves · `Physicslib4.Spacetime.OrientedSmoothCurve.toSmoothCurve` (+1 more)
- [**Definition 303**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:endpoints) — Endpoints · `Physicslib4.Spacetime.IsEndpoint` (+2 more)
- [**Lemma 304**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:extremal-parameter-mem-frontier) — An extremal parameter lies in the frontier · `Physicslib4.Spacetime.mem_frontier_of_isMin` (+3 more)
- [**Lemma 305**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:endpoint-parameter-space-eq-Icc) — Two endpoints force a compact parameter interval · `Physicslib4.Spacetime.parameterSpace_eq_Icc_of_endpoints`
- [**Definition 306**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:trip) — Trip · `Physicslib4.Spacetime.IsTripSegment` (+2 more) *(geodesic clause is a placeholder in Lean — see [Formalisation status](#formalisation-status))*
- [**Definition 307**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-trip) — Causal Trip · `Physicslib4.Spacetime.IsCausalTripSegment` (+2 more) *(geodesic clause is a placeholder in Lean — see [Formalisation status](#formalisation-status))*
- [**Theorem 308**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:precedence-transitive) — Transitivity of chronological and causal precedence · `Physicslib4.Spacetime.chronologicallyPrecedes_trans` (+1 more)
- [**Definition 309**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:no-closed-causal-curve) — No Closed Causal Curve (Causality Condition) · `Physicslib4.Spacetime.NoClosedCausalCurve`
- [**Theorem 310**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-order-refinements) — Irreflexivity and Antisymmetry under Causality · `Physicslib4.Spacetime.chronologicallyPrecedes_irrefl` (+2 more)
- [**Definition 311**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:chronological-future-and-chronological-past) — Chronological Future and Chronological Past · `Physicslib4.Spacetime.chronologicalFuture` (+3 more)
- [**Definition 312**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-future-and-causal-past) — Causal Future and Causal Past · `Physicslib4.Spacetime.causalFuture` (+3 more)
- [**Lemma 313**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:chronological-implies-causal) — Chronological Precedence Implies Causal Precedence · `Physicslib4.Spacetime.isCausal_of_isTimelike` (+3 more)
- [**Lemma 314**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:future-past-monotone) — Monotonicity of Futures and Pasts · `Physicslib4.Spacetime.chronologicalFutureSet_mono` (+3 more)

**§10.4.1 Causal diamonds, spacelike complement, and causal closure (p. 239)**

- [**Definition 315**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-diamond) — Causal and chronological diamonds · `Physicslib4.Spacetime.causalDiamond` (+3 more)
- [**Lemma 316**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-diamond-structure) — Structural properties of the causal diamond · `Physicslib4.Spacetime.causalDiamond_subset_of` (+2 more)
- [**Theorem 317**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-diamond-vs-chronological) — Chronological diamonds inside causal diamonds · `Physicslib4.Spacetime.chronologicalDiamond_subset_causalDiamond` (+1 more)
- [**Definition 318**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-related) — Spacelike Related · `Physicslib4.Spacetime.IsSpacelikeRelated`
- [**Definition 319**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completely-spacelike) — Completely Spacelike · `Physicslib4.Spacetime.IsCompletelySpacelike`
- [**Lemma 320**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completely-spacelike-symm) — Symmetry of Spacelike Separation · `Physicslib4.Spacetime.isSpacelikeRelated_comm` (+1 more)
- [**Lemma 321**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completely-spacelike-structural) — Structural Properties of Complete Spacelike Separation · `Physicslib4.Spacetime.isCompletelySpacelike_mono` (+9 more)
- [**Definition 322**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-complement) — Spacelike Complement of a Region · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement`
- [**Lemma 323**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-order) — Order Structure of the Spacelike Complement · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement_antitone` (+3 more)
- [**Definition 324**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-closure) — Causal closure operator · `Physicslib4.Spacetime.LorentzianSpacetime.causalClosure`
- [**Lemma 325**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-closure-is-closure-operator) — The Causal Closure is a Closure Operator · `Physicslib4.Spacetime.LorentzianSpacetime.causalClosure` (+1 more)
- [**Definition 326**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-complete-region) — Causally complete region · `Physicslib4.Spacetime.LorentzianSpacetime.IsCausallyComplete`
- [**Theorem 327**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-lattice) — Lattice of causally complete regions · `Physicslib4.Spacetime.LorentzianSpacetime.CausallyCompleteRegion` (+8 more)
- [**Lemma 328**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-de-morgan) — De Morgan Laws for the Spacelike Complement · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement_union` (+1 more)
- [**Theorem 329**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-complement-de-morgan) — De Morgan Laws for the Causal Complement · `Physicslib4.Spacetime.LorentzianSpacetime.causalComplement_antitone` (+6 more)

**§10.4.2 Causal convexity (p. 243)**

- [**Definition 330**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-convex-region) — Causally convex region · `Physicslib4.Spacetime.IsCausallyConvex`
- [**Lemma 331**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-diamond-causally-convex) — Causal diamonds are causally convex · `Physicslib4.Spacetime.causalDiamond_isCausallyConvex`
- [**Theorem 332**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-convex) — Causally complete regions are causally convex · `Physicslib4.Spacetime.spacelikeComplement_isCausallyConvex` (+2 more)

**§10.4.3 Causal convexity: closure structure, and the Alexandrov basis theorems (p. 244)**

- [**Lemma 333**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causally-convex-closure-ops) — Causally convex regions form a closure system · `Physicslib4.Spacetime.isCausallyConvex_univ` (+4 more)
- [**Definition 334**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-convex-hull) — Causal-convex hull · `Physicslib4.Spacetime.causalConvexHull`
- [**Lemma 335**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-convex-hull-extensive) — The Causal-Convex Hull is Extensive and Causally Convex · `Physicslib4.Spacetime.subset_causalConvexHull` (+1 more)
- [**Theorem 336**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-convex-hull-closure) — The causal-convex hull is a closure operator · `Physicslib4.Spacetime.causalConvexHull_minimal` (+3 more)
- [**Definition 337**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:alexandrov-topology) — Alexandrov Topology · `Physicslib4.Spacetime.alexandrovTopology`
- [**Lemma 338**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-basis-open) — Basis Sets Are Alexandrov-Open · `Physicslib4.Spacetime.isOpen_alexandrov_of_mem_basis`
- [**Lemma 339**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:chronological-future-past-open) — Openness of Chronological Futures and Pasts · `Physicslib4.Spacetime.isOpen_chronologicalFuture_inter_chronologicalPast` (+2 more)
- [**Lemma 340**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-chronological-open) — Unconditional Openness of Chronological Futures and Pasts on Standard Minkowski · `Physicslib4.exists_chronologicalFuture_standardMinkowski` (+5 more)
- [**Definition 341**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:minkowski-spacetime) — Minkowski Spacetime · `Physicslib4.MinkowskiSpacetime`
- [**Definition 342**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentzian-spacetime) — Lorentzian Spacetime · `Physicslib4.Spacetime.LorentzianSpacetime`
- [**Lemma 343**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lorentzian-causal-lifts) — Bundled Spacelike Separation and Basis Openness · `Physicslib4.Spacetime.LorentzianSpacetime.isCompletelySpacelike_comm` (+1 more)
- [**Lemma 344**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-nbhd-univ-of-no-diamond) — No-Diamond Points Have Only the Whole Space as Neighbourhood · `Physicslib4.Spacetime.alexandrov_nbhd_univ_of_no_diamond`
- [**Lemma 345**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-covering-hausdorff) — Covering from the Hausdorff Assumption · `Physicslib4.Spacetime.LorentzianSpacetime.sUnion_alexandrovBasis_eq_univ`
- [**Theorem 346**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:alexandrov-topological-basis) — The Alexandrov Diamonds Form a Topological Basis · `Physicslib4.Spacetime.LorentzianSpacetime.isTopologicalBasis_alexandrovBasis`
- [**Lemma 347**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-past-between) — Past Interpolation on Standard Minkowski · `Physicslib4.Spacetime.exists_past_between_standardMinkowski`
- [**Lemma 348**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-future-between) — Future Interpolation on Standard Minkowski · `Physicslib4.Spacetime.exists_future_between_standardMinkowski`
- [**Lemma 349**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-downward-directed) — Standard Minkowski Diamonds Are Downward-Directed · `Physicslib4.Spacetime.alexandrovBasis_exists_subset_inter_standardMinkowski`
- [**Lemma 350**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-exists-common-past) — Common Chronological Predecessor on Standard Minkowski · `Physicslib4.Spacetime.exists_common_past`
- [**Lemma 351**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-exists-common-future) — Common Chronological Successor on Standard Minkowski · `Physicslib4.Spacetime.exists_common_future`
- [**Lemma 352**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-upward-directed) — Standard Minkowski Diamonds Are Upward-Directed · `Physicslib4.Spacetime.alexandrovBasis_directed`
- [**Theorem 353**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-alexandrov-basis) — The Alexandrov Diamonds are a Basis on Standard Minkowski · `Physicslib4.Spacetime.isTopologicalBasis_alexandrovBasis_standardMinkowski`

**§10.4.4 Dilations are causal automorphisms but not isometries (p. 249)**

- [**Lemma 354**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-dilation-cone) — Dilations Preserve the Minkowski Cones · `Physicslib4.minkowskiForwardCone_smul` (+1 more)
- [**Theorem 355**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-dilation-causal-automorphism) — Dilations are Causal Automorphisms · `Physicslib4.alexandrovBasis_image_smul`
- [**Theorem 356**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-dilation-not-isometry) — Dilations are Not Isometries · `Physicslib4.minkowskiForm_smul` (+1 more)

**§10.4.5 Isometries and basis-set preservation (p. 250)**

- [**Lemma 357**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-classification) — Isometries Preserve the Causal Classification · `Physicslib4.Spacetime.Isometry.preserves_self` (+3 more)
- [**Lemma 358**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:path-parameter-unique-diff) — Unique Differentials Along a Path · `Physicslib4.Spacetime.Path.uniqueDiffOn_parameterSpace`
- [**Lemma 359**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pushforward-path) — Pushforward of a Path Under an Isometry · `Physicslib4.Spacetime.Isometry.pushforwardPath` (+5 more)
- [**Lemma 360**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-chronology) — Isometries Preserve Chronology · `Physicslib4.Spacetime.Isometry.PreservesFutureOrientation` (+8 more)
- [**Lemma 361**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-basis-sets) — Isometries Preserve Basis Sets · `Physicslib4.Spacetime.Isometry.futureOrientationPreserving` (+8 more)
- [**Lemma 362**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:axiom5-basis-preservation) — Axiom 5 Basis-Set Preservation · `Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent_isBasisSet_smul`

**§10.4.6 Pullback metrics and cross-metric isometries (p. 251)**

- [**Definition 363**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pullback-metric) — Pullback of a Spacetime Metric · `Physicslib4.Spacetime.bilinearPrecomp` (+3 more)
- [**Lemma 364**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-diffeo-linear-equiv) — The Differential of a Diffeomorphism is a Linear Equivalence · `Physicslib4.Spacetime.Diffeo` (+4 more)
- [**Lemma 365**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-symm-cancel-left) — Round-Trip Cancellation: $$d\psi$$ After $$d(\psi^{-1})$$ · `Physicslib4.Spacetime.mfderiv_symm_cancel_left`
- [**Lemma 366**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-symm-cancel-right) — Round-Trip Cancellation: $$d(\psi^{-1})$$ After $$d\psi$$ · `Physicslib4.Spacetime.mfderiv_symm_cancel_right`
- [**Lemma 367**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-inverse-eq-symm) — The Formal Inverse of $$d\psi_x$$ is the Inverse Equivalence · `Physicslib4.Spacetime.inverse_mfderiv_eq_symm` (+2 more)
- [**Lemma 368**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-symm) — The Pullback Metric is Symmetric · `Physicslib4.Spacetime.pullbackVal_symm`
- [**Lemma 369**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-nondegenerate) — The Pullback Metric is Non-Degenerate · `Physicslib4.Spacetime.pullbackVal_nondegenerate`
- [**Lemma 370**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-lorentzian) — The Pullback Metric is Lorentzian · `Physicslib4.Spacetime.pullbackVal_lorentzian`
- [**Lemma 371**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-smooth-in-charts) — The Pullback Metric is a Smooth Section of the Bilinear-Form Bundle · `Physicslib4.Spacetime.pullbackVal_contMDiff`
- [**Theorem 372**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pullback-is-spacetime) — The Pullback of a Spacetime is a Spacetime · `Physicslib4.Spacetime.pullback` (+4 more)
- [**Definition 373**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:preserves-future-orientation) — Two-Sided Preservation of Future Orientation · `Physicslib4.Spacetime.PreservesFutureOrientation` (+1 more)
- [**Lemma 374**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mpullback-vectorField-contMDiff-of-diffeo) — The Pullback of a Bundle-Smooth Vector Field Along a Diffeomorphism is Bundle-Smooth · `Physicslib4.Spacetime.contMDiff_mpullback_vectorField`
- [**Lemma 375**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation-ne-zero) — The Pullback Time Orientation is Nowhere Vanishing · `Physicslib4.Spacetime.mpullback_field_ne_zero`
- [**Lemma 376**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation-timelike) — The Pullback Time Orientation is Everywhere Timelike · `Physicslib4.Spacetime.pullbackVal_mpullback_field_self` (+1 more)
- [**Lemma 377**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation) — Pullback of a Time Orientation · `Physicslib4.Spacetime.pullbackTimeOrientation` (+1 more)
- [**Lemma 378**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-future-pointing-timelike) — Transport of Future-Pointing Timelike Vectors · `Physicslib4.Spacetime.pullbackVal_mpullback_field_apply` (+1 more)
- [**Lemma 379**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-future-pointing-null) — Transport of Future-Pointing Null Vectors · `Physicslib4.Spacetime.isFuturePointing_pullback_iff_of_isNull`
- [**Lemma 380**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-preserves-future-orientation) — The Pullback Preserves the Future Orientation Two-Sidedly · `Physicslib4.Spacetime.pullback_preservesFutureOrientationTwoSided`
- [**Definition 381**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:cross-metric-isometry) — Isometry Between Two Metrics on One Manifold · `Physicslib4.Spacetime.CrossIsometry` (+4 more)
- [**Lemma 382**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-symm) — The Inverse of a Cross-Metric Isometry is a Cross-Metric Isometry · `Physicslib4.Spacetime.CrossIsometry.symm_preserves` (+1 more)
- [**Lemma 383**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-classification) — Cross-Metric Isometries Preserve the Causal Classification · `Physicslib4.Spacetime.CrossIsometry.preserves_self` (+3 more)
- [**Lemma 384**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-tangent) — The Tangent Chain Rule Along a Path · `Physicslib4.Spacetime.mfderivWithin_comp_diffeo` (+1 more)
- [**Lemma 385**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path) — Pushforward of a Path Under a Cross-Metric Isometry · `Physicslib4.Spacetime.pushforwardPath` (+2 more)
- [**Lemma 386**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-causal) — The Pushforward Preserves the Timelike and Causal Conditions · `Physicslib4.Spacetime.CrossIsometry.pushforwardPath_isTimelike` (+1 more)
- [**Lemma 387**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-endpoints) — The Pushforward Transports Endpoints · `Physicslib4.Spacetime.pushforwardPath_isPastEndpoint` (+1 more)
- [**Lemma 388**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-chronology) — Cross-Metric Isometries Transport Chronological Precedence · `Physicslib4.Spacetime.pushforwardPath_isFutureOriented` (+2 more)
- [**Lemma 389**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-chronological-future-image) — Image of the Chronological Future · `Physicslib4.Spacetime.CrossIsometry.chronologicalFuture_image`
- [**Lemma 390**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-chronological-past-image) — Image of the Chronological Past · `Physicslib4.Spacetime.CrossIsometry.chronologicalPast_image`
- [**Lemma 391**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-basis-sets) — Cross-Metric Isometries Preserve Basis Sets · `Physicslib4.Spacetime.CrossIsometry.alexandrovDiamond_image` (+1 more)
- [**Lemma 392**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bijection-generated-topology-homeomorphism) — A Bijection Matching Generating Families is a Homeomorphism · `Physicslib4.continuous_generateFrom_of_preimage_mem` (+4 more)
- [**Lemma 393**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-alexandrov-homeomorphism) — The Pullback Alexandrov Topology · `Physicslib4.Spacetime.pullback_alexandrovBasis_image` (+3 more)
- [**Theorem 394**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pullback-is-lorentzian-spacetime) — The Pullback of a Lorentzian Spacetime is a Lorentzian Spacetime · `Physicslib4.Spacetime.LorentzianSpacetime.pullback_alexandrov_t2` (+3 more)

### §10.5 Haag–Kastler Axioms in Minkowski spacetime (pp. 263–300)

**§10.5 The axioms (p. 263)**

- [**Definition 395**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-algebras) — Axiom 1: Local Algebras · `Physicslib4.AQFT.HaagKastler.LocalNet`
- [**Definition 396**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony) — Axiom 2: Isotony · `Physicslib4.AQFT.HaagKastler.Isotony`

**§10.5.1 The Quasilocal Colimit (p. 264)**

- [**Lemma 397**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-diamonds-isDirected) — Alexandrov Diamonds are Directed under Inclusion · `Physicslib4.AQFT.HaagKastler.Diamond` (+2 more)
- [**Lemma 398**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isotony-directed-system) — The Isotony Family is a Directed System · `Physicslib4.AQFT.HaagKastler.transitionHom` (+1 more)
- [**Lemma 399**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-norm-well-defined) — The Colimit Norm is Well Defined · `Physicslib4.AQFT.HaagKastler.QuasilocalColimit` (+3 more)
- [**Lemma 400**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-common-representatives) — Common Representatives for Two Colimit Elements · `Physicslib4.AQFT.HaagKastler.exists_common_representatives`
- [**Lemma 401**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-norm-axioms) — The Colimit Norm is a Ring Norm and a Normed-Space Norm · `Physicslib4.AQFT.HaagKastler.instNonemptyDiamond` (+3 more)
- [**Lemma 402**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-union-normed-star-algebra) — The Quasilocal Union is a Normed \*-Algebra · `Physicslib4.AQFT.HaagKastler.norm_eq_colimitNorm` (+1 more)
- [**Lemma 403**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-cstar-identity) — The Colimit Satisfies the C\*-Inequality · `Physicslib4.AQFT.HaagKastler.colimitCStarRing`
- [**Definition 404**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completion-standing-hypotheses) — Standing Hypotheses for the Completion Results · `Physicslib4.CStarCompletion`
- [**Definition 405**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completion-star) — The Involution on a Completion · `Physicslib4.instStarCompletion` (+1 more)
- [**Lemma 406**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:star-extends-to-completion) — The Involution Extends to the Completion · `Physicslib4.instStarRingCompletion` (+1 more)
- [**Lemma 407**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-coe-star-alg-hom) — The Completion Coercion as a Bundled \*-Algebra Homomorphism · `Physicslib4.coeStarAlgHom`
- [**Lemma 408**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-cstar-identity) — The C\*-Inequality Passes to the Completion · `Physicslib4.instCStarRingCompletion`
- [**Lemma 409**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-normed-algebra) — The Completion is a Normed $$\mathbb{C}$$-Algebra · `Physicslib4.instNormedAlgebraCompletion`
- [**Lemma 410**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-of-cstar-normed-star-algebra) — The Completion of a C\*-Normed \*-Algebra is a C\*-Algebra · `Physicslib4.instCStarAlgebraCompletion`
- [**Lemma 411**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-completion-cstar) — The Completion of the Quasilocal Colimit is a C\*-Algebra · `Physicslib4.AQFT.HaagKastler.QuasilocalCompletion` (+1 more)
- [**Definition 412**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-algebra) — Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra`
- [**Definition 413**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity) — Axiom 3: Local Commutativity · `Physicslib4.AQFT.HaagKastler.LocalCommutativity`
- [**Definition 414**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-observable) — Quasilocal Observable · `Physicslib4.AQFT.HaagKastler.IsQuasilocalObservable`
- [**Definition 415**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-completeness) — Axiom 4: Quasilocal Completeness · `Physicslib4.AQFT.HaagKastler.ObservableCorrespondence`
- [**Theorem 416**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-algebra-exists) — Existence of a Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.exists_quasilocalAlgebra`
- [**Lemma 417**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embedding) — The Canonical Embeddings into the Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.colimitStarOf` (+1 more)
- [**Lemma 418**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embedding-injective) — The Canonical Embeddings are Injective · `Physicslib4.AQFT.HaagKastler.quasilocalEmbedding_injective`
- [**Lemma 419**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embedding-cocone) — The Canonical Embeddings Form a Cocone · `Physicslib4.AQFT.HaagKastler.quasilocalEmbedding_transitionHom`
- [**Lemma 420**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-union-of-insertions) — The Colimit is the Union of the Images of its Insertions · `Physicslib4.AQFT.HaagKastler.exists_eq_colimitStarOf`
- [**Lemma 421**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embeddings-dense) — The Images of the Canonical Embeddings are Dense · `Physicslib4.AQFT.HaagKastler.dense_iUnion_range_quasilocalEmbedding`
- [**Theorem 422**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-strongly-dense) — Quasilocal Observables are Strongly Dense in the Bicommutant · `Physicslib4.AQFT.HaagKastler.dense_range_in_bicommutant` — **the one Chapter 10 node whose proof is not formalised**: the statement is formalised, the proof is a deliberate `sorry` with a **Restriction:** note (see [Formalisation status](#formalisation-status))
- [**Definition 423**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentz-covariance) — Axiom 5: Lorentz Covariance · `Physicslib4.AQFT.HaagKastler.LorentzCovariance`
- [**Definition 424**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:haag-kastler-net) — Haag–Kastler Net · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet`

**§10.5.2 Einstein Causality (p. 282)**

- [**Theorem 425**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:einstein-causality) — Einstein Causality in a Representation · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.einstein_causality` (+1 more)

**§10.5.3 Local von Neumann Algebras (p. 282)**

- [**Definition 426**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann) — Local von Neumann Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localOperators` (+1 more)
- [**Lemma 427**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bicommutant-of-selfadjoint-is-von-neumann) — The Bicommutant of a Self-Adjoint Set is a von Neumann Algebra · `Physicslib4.GNS.vonNeumannOfSelfAdjoint`
- [**Definition 428**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-algebra) — $$R(\mathbf{B})$$ as a von Neumann Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra`
- [**Theorem 429**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-microcausality) — Microcausality at the von Neumann Level · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_subset_centralizer`
- [**Theorem 430**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-isotony) — Isotony of the von Neumann Net · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_mono`
- [**Theorem 431**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-bundled-order) — Bundled von Neumann Microcausality and Isotony · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_le_commutant` (+1 more)
- [**Definition 432**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-net) — The Net of von Neumann Algebras · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.vonNeumannNet`
- [**Theorem 433**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence) — Statistical Independence (Schlieder Property) · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_separating` (+1 more)
- [**Theorem 434**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-bundled) — Statistical Independence, bundled · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_separating`
- [**Theorem 435**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:additive-free-locality) — Additive-Free Locality via the Spacelike Complement · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement`
- [**Theorem 436**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-geometric-covariance) — Geometric Covariance of the von Neumann Net · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.lieConj_image_localVonNeumann` (+1 more)
- [**Theorem 437**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-factor-orbit) — Orbit-Invariance of Factoriality · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_isFactor_smul`
- [**Theorem 438**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-covariance-iso) — Geometric Covariance as a von Neumann Algebra Isomorphism · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannEquiv`

**§10.5.4 Relative Commutants of Nested Local Algebras (p. 284)**

- [**Definition 439**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:relative-commutant) — Relative Commutant of a Nested Pair · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.relativeCommutant`
- [**Theorem 440**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-antitone) — Antitonicity of the Commutant · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.commutant_le_commutant_of_le`
- [**Theorem 441**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-le-right) — Relative Commutant Lies in the Larger Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.relativeCommutant_le_right`
- [**Theorem 442**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-coe-commutant) — Relative Commutant Commutes with the Smaller Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.relativeCommutant_coe_subset_commutant`
- [**Theorem 443**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-center) — Relative Commutant Contains the Centre · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.center_le_relativeCommutant`
- [**Definition 444**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-inclusion) — Irreducible Inclusion · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsIrreducibleInclusion`
- [**Theorem 445**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-inclusion-factor) — An Irreducible Inclusion has Factor Ambient · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.isFactor_of_isIrreducibleInclusion`
- [**Theorem 446**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:self-inclusion-factor) — Self-Inclusion is Irreducible iff Factor · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.isIrreducibleInclusion_self_iff_isFactor`

**§10.5.5 Irreducibility and Schur's Lemma (p. 285)**

- [**Definition 447**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-representation) — Irreducible Representation · `Physicslib4.GNS.IsIrreducible`
- [**Theorem 448**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:schur-lemma) — Topological Schur Lemma · `Physicslib4.GNS.eq_smul_one_of_commute_of_cyclic`
- [**Theorem 449**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-scalar-iff) — Commutant Scalar iff Proportional Coefficient · `Physicslib4.GNS.isScalar_iff_coeff_proportional`
- [**Definition 450**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pure-state) — Pure State · `Physicslib4.GNS.IsPure`
- [**Theorem 451**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-implies-irreducible) — Pure Implies Irreducible · `Physicslib4.GNS.isIrreducible_of_isPure`
- [**Theorem 452**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-form-bound) — The GNS Radon–Nikodym Form is Bounded · `Physicslib4.GNS.gns_form_norm_le` (+1 more)
- [**Theorem 453**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-radon-nikodym-operator) — The GNS Radon–Nikodym Operator · `Physicslib4.GNS.rnOp` (+3 more)
- [**Theorem 454**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible) — Pure $$\iff$$ Irreducible · `Physicslib4.GNS.isPure_iff_isIrreducible`
- [**Theorem 455**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-factor) — An Irreducible Representation Generates a Factor · `Physicslib4.GNS.center_gnsVonNeumann_eq_of_isIrreducible`
- [**Theorem 456**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-generates-all) — Irreducibility $$\iff$$ Generating $$\mathcal{B}(H)$$ · `Physicslib4.GNS.isIrreducible_iff_gnsVonNeumann_eq_univ` (+1 more)
- [**Theorem 457**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-generates-all-bundled) — Bundled Density Form of Irreducibility · `Physicslib4.GNS.coe_gnsVonNeumannAlgebra_eq_univ_of_isIrreducible` (+1 more)
- [**Theorem 458**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-factor) — The GNS Representation of a Pure State is a Factor · `Physicslib4.GNS.exists_gns_factor_of_isPure`
- [**Theorem 459**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-generates-all) — The GNS Representation of a Pure State Generates $$\mathcal{B}(H)$$ · `Physicslib4.GNS.exists_gns_generates_all_of_isPure`
- [**Theorem 460**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:norm-positive-functional) — Norm of a Positive Functional · `Physicslib4.GNS.norm_eq_re_apply_one_of_positive`
- [**Definition 461**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:extreme-state) — Extreme Point of the State Space · `Physicslib4.GNS.State.IsExtremePoint`
- [**Theorem 462**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme) — Pure $$\iff$$ Extreme Point · `Physicslib4.GNS.isPure_iff_isExtremePoint`
- [**Theorem 463**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-space-convex-bridge) — State-Space Convexity and the Extreme-Point Bridge · `Physicslib4.GNS.convex_stateSpace` (+1 more)
- [**Definition 464**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:state-pullback) — Pullback of a State · `Physicslib4.GNS.State.comp`
- [**Theorem 465**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-pullback-functorial) — Functoriality of the State Pullback · `Physicslib4.GNS.State.comp_id` (+1 more)
- [**Theorem 466**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-pullback-invariant) — Purity is Invariant under a \*-Isomorphism · `Physicslib4.GNS.isPure_comp_iff`
- [**Theorem 467**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-space-weak-compact) — Weak-\* Compactness of the State Space · `Physicslib4.GNS.isCompact_weakStateSet`
- [**Theorem 468**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme-quasilocal) — Pure $$\iff$$ Extreme Point on the Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.pure_iff_extreme`
- [**Theorem 469**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible-quasilocal) — Pure $$\iff$$ Irreducible GNS on the Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.exists_gns_pure_iff_irreducible`

**§10.5.6 Unitary Equivalence and Superselection (p. 289)**

- [**Definition 470**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:unitary-equivalence) — Unitary Equivalence of Representations · `Physicslib4.GNS.UnitaryEquiv`
- [**Theorem 471**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:unitary-equiv-invariants) — Irreducibility and Factoriality are Unitary Invariants · `Physicslib4.GNS.UnitaryEquiv.isIrreducible_iff` (+1 more)

**§10.5.7 GNS Covariance (p. 290)**

- [**Lemma 472**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cyclic-pullback-surjective) — Cyclicity pulls back along a surjective \*-homomorphism · `Physicslib4.GNS.isCyclicVector_comp_of_surjective`
- [**Theorem 473**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance) — GNS covariance under a \*-isomorphism · `Physicslib4.GNS.exists_unitary_of_gns_comp`
- [**Theorem 474**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-unitary-equiv) — The GNS representation of a pullback state · `Physicslib4.GNS.unitaryEquiv_comp_of_gns`
- [**Lemma 475**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-image-invariants) — Pullback along a surjection preserves the image algebra · `Physicslib4.GNS.range_comp_of_surjective` (+2 more)
- [**Theorem 476**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-sector-transport) — Superselection type transports along a \*-isomorphism · `Physicslib4.GNS.isIrreducible_iff_of_gns_comp` (+1 more)
- [**Theorem 477**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-local) — GNS covariance for local algebras · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.unitaryEquiv_gns_covEquiv` (+2 more)

**§10.5.8 Disjointness and Quasi-Equivalence (p. 291)**

- [**Definition 478**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:disjoint-representations) — Disjoint Representations · `Physicslib4.GNS.AreDisjoint`
- [**Definition 479**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasi-equivalence) — Quasi-Equivalence of Representations · `Physicslib4.GNS.QuasiEquiv`
- [**Theorem 480**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-dichotomy) — Schur's Lemma and the Irreducible Dichotomy · `Physicslib4.GNS.UnitaryEquiv.of_intertwines_of_isIrreducible` (+1 more)
- [**Lemma 481**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:schur-multiplicity) — Schur Multiplicity · `Physicslib4.GNS.eq_smul_of_intertwines_of_isIrreducible`
- [**Lemma 482**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:endomorphism-scalar) — Endomorphism Algebra of an Irreducible Representation · `Physicslib4.GNS.intertwines_self_iff_isScalar`
- [**Theorem 483**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-von-neumann) — The commutant (self-intertwiner) von Neumann algebra · `Physicslib4.GNS.commutantVonNeumann` (+2 more)
- [**Theorem 484**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:double-commutant-duality) — Double-Commutant Duality · `Physicslib4.GNS.commutant_gnsVonNeumannAlgebra` (+1 more)
- [**Theorem 485**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-factor-duality) — A Factor and its Commutant; Triviality Duality · `Physicslib4.GNS.isFactor_gnsVonNeumann_iff_isFactor_commutant` (+1 more)
- [**Lemma 486**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-abelian-self-commuting) — Abelian $$\iff$$ Self-Commuting · `Physicslib4.GNS.isAbelian_iff_le_commutant`
- [**Definition 487**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-center) — Centre of a von Neumann algebra · `Physicslib4.GNS.vonNeumannCenter`
- [**Lemma 488**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-inter-is-von-neumann) — The centre is a von Neumann algebra · `Physicslib4.GNS.bicommutant_inter_commutant_eq`
- [**Lemma 489**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-inter-general) — The intersection of two von Neumann algebras is a von Neumann algebra · `Physicslib4.GNS.bicommutant_inter_eq`
- [**Theorem 490**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-center-abelian) — The centre of a von Neumann algebra is abelian · `Physicslib4.GNS.vonNeumannCenter_isAbelian`
- [**Lemma 491**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-center-eq-self-iff-abelian) — $$R$$ is abelian iff it equals its centre · `Physicslib4.GNS.vonNeumannCenter_eq_self_iff_isAbelian`
- [**Theorem 492**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:factor-abelian-iff-scalars) — A factor is abelian iff it is the scalars · `Physicslib4.GNS.isAbelian_iff_eq_scalars_of_isFactor`
- [**Theorem 493**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:center-eq-commutant-center) — A von Neumann algebra and its commutant share a centre · `Physicslib4.GNS.vonNeumannCenter_eq_commutant`
- [**Theorem 494**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:factor-iff-center-scalars) — A von Neumann algebra is a factor iff its centre is the scalars · `Physicslib4.GNS.isFactor_iff_center_eq_scalars`
- [**Theorem 495**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-state-dichotomy) — The Pure-State Dichotomy · `Physicslib4.GNS.exists_gns_areDisjoint_or_unitaryEquiv_of_isPure`

**§10.5.9 Direct Sums, Amplification, and Reducibility (p. 294)**

- [**Definition 496**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:direct-sum-representation) — Direct-Sum Representation · `Physicslib4.GNS.directSum`
- [**Theorem 497**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:direct-sum-subrepresentation) — Subrepresentations and Commutant of a Direct Sum · `Physicslib4.GNS.intertwines_single` (+1 more)
- [**Definition 498**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:amplification) — Amplification · `Physicslib4.GNS.amplification`
- [**Theorem 499**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:direct-sum-reducible) — Reducibility of a Direct Sum · `Physicslib4.GNS.not_isIrreducible_directSum`

**§10.5.10 Covariant States and the Covariance Action (p. 295)**

- [**Definition 500**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-state-family) — Covariant Family of Local States · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsCovariantFamily`
- [**Lemma 501**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:covariant-state-family-compose) — Composition of Covariance · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsCovariantFamily.comp`
- [**Definition 502**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-lift) — Quasilocal Covariance Automorphism · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.QuasilocalLift`
- [**Lemma 503**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-lift-unique) — Uniqueness of the Quasilocal Lift · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.QuasilocalLift.unique`
- [**Theorem 504**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-lift-exists) — Existence of the Quasilocal Lift · `Physicslib4.AQFT.HaagKastler.nonempty_quasilocalLift`
- [**Theorem 505**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-lift-trivial) — Existence for the Trivial Net · `Physicslib4.AQFT.HaagKastler.nonempty_trivialQuasilocalLift`
- [**Definition 506**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-quasilocal-algebra) — Covariant Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.action`
- [**Lemma 507**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-action-coherence) — Group-Action Coherence of the Covariance Automorphism · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.action_one` (+1 more)
- [**Definition 508**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:invariant-state) — Invariant State · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState`
- [**Theorem 509**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:invariant-state-gns-unitary) — GNS Unitary Implementation of an Invariant State · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState.exists_gns_unitary`
- [**Theorem 510**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-covariant-representation) — Irreducible Covariant Representation of a Pure Invariant State · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState.exists_gns_irreducible_covariant`
- [**Definition 511**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:positive-energy) — Positive Energy (bounded-generator scaffold) · `Physicslib4.AQFT.IsPositiveEnergy`
- [**Theorem 512**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:positive-energy-api) — Positive-Energy API · `Physicslib4.AQFT.isPositiveEnergy_const_refl` (+3 more)
- [**Definition 513**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:vacuum-state) — Vacuum State (generator-parameterised scaffold) · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumState`
- [**Theorem 514**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:vacuum-no-stone) — No-Stone Consequences of a Vacuum State · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumState.invariant` (+1 more)
- [**Definition 515**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-timelike-translation) — Future-Timelike Translation Subgroup · `Physicslib4.AQFT.HaagKastler.translationSub` (+3 more)
- [**Definition 516**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:vacuum-state-concrete) — Vacuum State with the Concrete Spectrum Condition · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumStateConcrete`
- [**Theorem 517**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:purity-covariance-invariant) — Purity is Covariance-Invariant · `Physicslib4.GNS.isPure_precomp_iff` (+1 more)
- [**Theorem 518**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-quasilocal-action) — GNS covariance along the quasilocal action · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.unitaryEquiv_gns_action` (+2 more)

**§10.5.11 The Separating Vector of a Faithful State (p. 298)**

- [**Theorem 519**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:separating-faithful) — Separating Vector of a Faithful State · `Physicslib4.GNS.separating_of_faithful` (+1 more)

**§10.5.12 The KMS Condition and Thermal Equilibrium (p. 298)**

- [**Definition 520**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:one-parameter-aut) — One-Parameter Automorphism Group · `Physicslib4.AQFT.IsOneParameterAut`
- [**Definition 521**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state) — KMS State · `Physicslib4.AQFT.IsKMSState`
- [**Theorem 522**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-convex) — The KMS State Set is Convex · `Physicslib4.AQFT.IsKMSState.convexCombo`
- [**Lemma 523**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:kms-correlation-one) — Boundary Coincidence for $$a = 1$$ · `Physicslib4.AQFT.IsKMSState.correlationOne`
- [**Definition 524**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:strip-liouville) — Strip-Liouville Principle · `Physicslib4.AQFT.StripLiouville`
- [**Theorem 525**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:strip-periodic-extension) — $$i\beta$$-Periodic Entire Extension (Strip Schwarz Reflection) · `Physicslib4.exists_bounded_entire_extension_of_strip_periodic`
- [**Theorem 526**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:strip-liouville-pos) — Strip-Liouville Holds for $$\beta > 0$$ · `Physicslib4.AQFT.stripLiouville_of_pos`
- [**Theorem 527**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-invariance) — KMS States are Invariant · `Physicslib4.AQFT.IsKMSState.invariant_of_pos`
- [**Theorem 528**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:strip-uniqueness) — Uniqueness on the Strip from Boundary Values · `Physicslib4.eqOn_strip_of_eq_boundary`
- [**Theorem 529**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-correlation-unique) — Uniqueness of the KMS Correlation Function · `Physicslib4.AQFT.IsKMSState.correlation_eqOn`

**§10.5.13 KMS States for the Covariance Flow (p. 300)**

- [**Definition 530**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:flow-aut-covariance) — Covariance-Flow Automorphism Family · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.flowAut`
- [**Lemma 531**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:one-parameter-aut-flow-covariance) — A Lorentz One-Parameter Subgroup Induces a One-Parameter Group · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.isOneParameterAut_flowAut`
- [**Definition 532**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state-for-flow-covariance) — KMS State for the Covariance Flow · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsKMSStateForFlow`
- [**Theorem 533**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-convex-for-flow-covariance) — Convexity of the Covariance-Flow KMS States · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsKMSStateForFlow.convexCombo`
- [**Definition 534**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:ground-state-for-flow-covariance) — Ground State for a Covariance Flow · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsGroundStateForFlow` (+2 more)

### §10.6 Haag–Kastler Axioms in curved spacetime (pp. 300–310)

**§10.6 The axioms (p. 300)**

- [**Definition 535**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-algebras-in-curved-spacetime) — Axiom 1: Local Algebras · `Physicslib4.AQFT.HaagKastlerCurved.LocalNet`
- [**Definition 536**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony-in-curved-spacetime) — Axiom 2: Isotony · `Physicslib4.AQFT.HaagKastlerCurved.Isotony`
- [**Definition 537**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity-in-curved-spacetime) — Axiom 3: Local Commutativity · `Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity`
- [**Definition 538**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-observable) — Local Observable · `Physicslib4.AQFT.HaagKastlerCurved.IsLocalObservable`
- [**Definition 539**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-completeness-in-curved-spacetime) — Axiom 4: Local Completeness · `Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebra`
- [**Definition 540**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isometric-covariance-in-curved-spacetime) — Axiom 5: Isometric Covariance · `Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance` *(implemented via the explicitly orientation-preserving subgroup — see [Formalisation status](#formalisation-status))*
- [**Definition 541**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:haag-kastler-net-in-curved-spacetime) — Haag–Kastler Net in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet`

**§10.6.1 Einstein Causality in Curved Spacetime (p. 303)**

- [**Theorem 542**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:einstein-causality-in-curved-spacetime) — Einstein Causality in a Representation (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.einstein_causality` (+1 more)

**§10.6.2 Local von Neumann Algebras in Curved Spacetime (p. 303)**

- [**Definition 543**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-in-curved-spacetime) — Local von Neumann Algebra in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localOperators` (+1 more)
- [**Definition 544**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-algebra-in-curved-spacetime) — $$R(\mathbf{B}')$$ as a von Neumann Algebra (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra`
- [**Theorem 545**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-microcausality-in-curved-spacetime) — Microcausality at the von Neumann Level (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_subset_centralizer`
- [**Theorem 546**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-isotony-in-curved-spacetime) — Isotony of the von Neumann Net (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_mono`
- [**Theorem 547**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-bundled-order-in-curved-spacetime) — Bundled von Neumann Microcausality and Isotony (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_le_commutant` (+1 more)
- [**Definition 548**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-net-in-curved-spacetime) — The Net of von Neumann Algebras in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.vonNeumannNet`
- [**Theorem 549**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-in-curved-spacetime) — Statistical Independence (Schlieder Property) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_separating` (+1 more)
- [**Theorem 550**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-bundled-in-curved-spacetime) — Statistical Independence, bundled (curved spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_separating`
- [**Theorem 551**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:additive-free-locality-in-curved-spacetime) — Additive-Free Locality via the Spacelike Complement (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric`
- [**Theorem 552**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-geometric-covariance-in-curved-spacetime) — Geometric Covariance of the von Neumann Net (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.lieConj_image_localVonNeumann` (+1 more)
- [**Theorem 553**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-factor-orbit-in-curved-spacetime) — Orbit-Invariance of Factoriality (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_isFactor_smul`
- [**Theorem 554**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-covariance-iso-in-curved-spacetime) — Geometric Covariance as a von Neumann Algebra Isomorphism (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannEquiv`

**§10.6.3 Relative Commutants of Nested Local Algebras in Curved Spacetime (p. 305)**

- [**Definition 555**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:relative-commutant-in-curved-spacetime) — Relative Commutant of a Nested Pair (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant`
- [**Theorem 556**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-le-right-in-curved-spacetime) — Relative Commutant Lies in the Larger Algebra (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant_le_right`
- [**Theorem 557**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-coe-commutant-in-curved-spacetime) — Relative Commutant Commutes with the Smaller Algebra (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant_coe_subset_commutant`
- [**Theorem 558**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-center-in-curved-spacetime) — Relative Commutant Contains the Centre (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.center_le_relativeCommutant`
- [**Definition 559**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-inclusion-in-curved-spacetime) — Irreducible Inclusion (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsIrreducibleInclusion`
- [**Theorem 560**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-inclusion-factor-in-curved-spacetime) — An Irreducible Inclusion has Factor Ambient (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isFactor_of_isIrreducibleInclusion`
- [**Theorem 561**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:self-inclusion-factor-in-curved-spacetime) — Self-Inclusion is Irreducible iff Factor (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isIrreducibleInclusion_self_iff_isFactor`
- [**Theorem 562**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:abelian-local-von-neumann-in-curved-spacetime) — Abelian Local von Neumann Algebras (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_center_isAbelian` (+1 more)
- [**Theorem 563**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:center-duality-local-von-neumann-in-curved-spacetime) — Centre Duality for Local von Neumann Algebras (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_center_eq_commutant` (+1 more)

**§10.6.4 Purity of States on Local Algebras in Curved Spacetime (p. 306)**

- [**Theorem 564**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme-in-curved-spacetime) — Pure $$\iff$$ Extreme Point on a Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.pure_iff_extreme`
- [**Theorem 565**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible-in-curved-spacetime) — Pure $$\iff$$ Irreducible GNS on a Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_pure_iff_irreducible`
- [**Theorem 566**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-factor-generates-in-curved-spacetime) — Pure GNS on a Local Algebra is a Factor Generating $$\mathcal{B}(H)$$ · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_factor_of_isPure` (+1 more)
- [**Theorem 567**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-dichotomy-in-curved-spacetime) — The Irreducible Dichotomy for a Curved Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.areDisjoint_or_unitaryEquiv_of_isIrreducible`
- [**Theorem 568**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-local-in-curved-spacetime) — GNS covariance for curved local algebras · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.unitaryEquiv_gns_covEquiv` (+2 more)

**§10.6.5 Covariant States in Curved Spacetime (p. 307)**

- [**Definition 569**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-state-family-in-curved-spacetime) — Covariant Family of Local States in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsCovariantFamily`
- [**Lemma 570**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:covariant-state-family-compose-in-curved-spacetime) — Composition of Covariance in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsCovariantFamily.comp`

**§10.6.6 The Stabiliser GNS Unitary in Curved Spacetime (p. 308)**

- [**Definition 571**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:stabilizer-action-in-curved-spacetime) — Stabiliser Action on a Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.stabAut`
- [**Lemma 572**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:stabilizer-action-laws-in-curved-spacetime) — The Stabiliser Action is a Group Action · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.stabAut_one` (+1 more)
- [**Theorem 573**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-unitary-stabilizer-in-curved-spacetime) — GNS Unitary Representation of the Stabiliser · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_unitary_stabilizer`
- [**Theorem 574**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-unitary-stabilizer-strongly-continuous-in-curved-spacetime) — Strongly Continuous Stabiliser GNS Unitary · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_unitary_stabilizer_strongContinuous`
- [**Theorem 575**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-covariant-representation-in-curved-spacetime) — Irreducible Covariant Representation of a Pure Invariant State (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_irreducible_covariant_stabilizer`
- [**Theorem 576**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:purity-covariance-invariant-in-curved-spacetime) — Purity is Invariant under the Stabiliser Action · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isPure_precomp_stabAut_iff`
- [**Theorem 577**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-stabilizer-action) — GNS covariance along the stabiliser action · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.unitaryEquiv_gns_stabAut` (+2 more)

**§10.6.7 KMS States for a Killing Flow (p. 309)**

- [**Definition 578**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:flow-aut-in-curved-spacetime) — Killing-Flow Automorphism Family · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.flowAut`
- [**Lemma 579**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:one-parameter-aut-flow-in-curved-spacetime) — A Killing Flow Induces a One-Parameter Group · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isOneParameterAut_flowAut`
- [**Definition 580**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state-for-flow-in-curved-spacetime) — KMS State for a Killing Flow · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow`
- [**Theorem 581**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-thermal-representation-in-curved-spacetime) — The Killing-Flow KMS Thermal Representation · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow.exists_gns_unitary_strongContinuous`
- [**Theorem 582**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-convex-for-flow-in-curved-spacetime) — Convexity of the Killing-Flow KMS States · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow.convexCombo`
- [**Definition 583**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:ground-state-for-flow-in-curved-spacetime) — Ground State for a Killing Flow · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsGroundStateForFlow` (+2 more)

### §10.7 General Covariance: Nets on Pullback-Related Metrics (pp. 310–312)

**§10.7 General Covariance: Nets on Pullback-Related Metrics (p. 310)**

- [**Definition 584**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:net-equivalence-in-curved-spacetime) — Equivalence of Haag–Kastler Nets · `Physicslib4.AQFT.HaagKastlerCurved.NetEquivalence`
- [**Definition 585**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:general-covariance-in-curved-spacetime) — General Covariance · `Physicslib4.AQFT.HaagKastlerCurved.NetTheory` (+4 more)

### The axioms at a glance

Axiom 6 (Primitivity) from the original 1964 Haag–Kastler paper is not carried into the sharpened axiom set — see Chapter 8 for the discussion of why it is dropped. The five sharpened axioms in each setting, bundled together as a `HaagKastlerNet`, are what is actually formalised.

**Minkowski spacetime** — bundled as `Physicslib4.AQFT.HaagKastler.HaagKastlerNet` (Definition 424):

| Axiom | Node | Lean |
|---|---|---|
| 1. Local Algebras | Definition 395 | `Physicslib4.AQFT.HaagKastler.LocalNet` |
| 2. Isotony | Definition 396 | `Physicslib4.AQFT.HaagKastler.Isotony` |
| 3. Local Commutativity | Definition 413 | `Physicslib4.AQFT.HaagKastler.LocalCommutativity` |
| 4. Quasilocal Completeness | Definition 415 | `Physicslib4.AQFT.HaagKastler.ObservableCorrespondence` |
| 5. Lorentz Covariance | Definition 423 | `Physicslib4.AQFT.HaagKastler.LorentzCovariance` |

**Curved spacetime** — bundled as `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet` (Definition 541):

| Axiom | Node | Lean |
|---|---|---|
| 1. Local Algebras | Definition 535 | `Physicslib4.AQFT.HaagKastlerCurved.LocalNet` |
| 2. Isotony | Definition 536 | `Physicslib4.AQFT.HaagKastlerCurved.Isotony` |
| 3. Local Commutativity | Definition 537 | `Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity` |
| 4. Local Completeness | Definition 539 | `Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebra` |
| 5. Isometric Covariance | Definition 540 | `Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance` |

**General Covariance (Definition 585, `Physicslib4.AQFT.HaagKastlerCurved.IsGenerallyCovariant`)** is deliberately *not* a sixth axiom. Axioms 1–5 each constrain a single net over a single fixed spacetime, whereas general covariance relates two nets over two spacetimes; it is therefore a property of the section $$L \mapsto \mathfrak{U}_L$$ assigning a net to every Lorentzian spacetime, not an extra field of the net structure.

Two changes to the axioms are worth calling out for readers coming from an earlier version of this blueprint:

- **Isotony now supplies its embeddings as data.** Axiom 2 (Definitions 396 and 536) fixes the family $$i_{\mathbf{B}_1 \mathbf{B}_2}$$ together with identity and composition laws, making $$\mathbf{B} \mapsto \mathfrak{U}(\mathbf{B})$$ a functor on the inclusion order. Axiom 3 consumes that family rather than choosing witnesses of its own. This is what makes the quasilocal colimit well posed in Minkowski spacetime, and it removes the coherence side-hypotheses that curved-spacetime statements about nested regions previously had to carry.
- **Axiom 4 has been split.** The mathematical claim that a quasilocal algebra exists is now Theorem 416 (`Physicslib4.AQFT.HaagKastler.exists_quasilocalAlgebra`), proved from the colimit-and-completion chain; what remains as Axiom 4 (Definition 415) is the bridge principle relating physical observables to quasilocal ones, which has — by design — no mathematical consumers.

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

