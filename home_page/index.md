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

The blueprint is 116 pages long and splits cleanly in two.

**Chapters 1–9 are mathematical background and are not formalised in Lean.** They motivate and analyse each of the original Haag–Kastler axioms in turn, and then generalise them to curved spacetime. Along the way they cite twelve supporting results, numbered 1 through 12 — Gelfand–Naimark, the Bounded Linear Transformation Theorem, the existence of a Lorentz metric, and so on. These are quoted from the literature where needed; none of them carries a Lean declaration.

**Chapter 10 collects the formalisation-ready content, and it is the content of Chapter 10 that is formalised in Lean.** Its declarations are numbered consecutively, running from Definition 13 through Definition 321, and comprise **309 declarations in total: 90 definitions, 115 theorems, and 104 lemmas**, mapped onto **563 Lean declarations**. Chapter 10 is divided into five top-level sections, §10.1 through §10.5.

**308 of the 309 are formalised, statements and proofs alike.** Every one of the 219 theorems and lemmas in Chapter 10 carries a written proof in the blueprint, and 218 of those proofs are formalised in Lean. The single exception, in both counts, is Theorem 158; it is discussed under [Formalisation status](#formalisation-status) below.

At a glance, the 309 declarations break down by top-level section as follows:

| Section | Topic | Pages | Definitions | Theorems | Lemmas | Total | Formalised |
|---|---|---|---|---|---|---|---|
| §10.1 | GNS Construction | 28–37 | 2 | 1 | 3 | 6 | 6 |
| §10.2 | Spacetime and causal structure | 37–67 | 30 | 16 | 66 | 112 | 112 |
| §10.3 | Haag–Kastler Axioms (Minkowski) | 67–104 | 39 | 69 | 32 | 140 | 139 |
| §10.4 | Haag–Kastler Axioms (curved spacetime) | 105–114 | 17 | 29 | 3 | 49 | 49 |
| §10.5 | General Covariance | 114–116 | 2 | 0 | 0 | 2 | 2 |
| **Total** | | | **90** | **115** | **104** | **309** | **308** |

### Where the Lean lives

Each blueprint section maps onto a compact set of Lean modules, which is the fastest way to find the code behind a given piece of the theory:

| Section | Principal Lean modules |
|---|---|
| §10.1 | `Physicslib4/GNS/` (`Basic`, `Construction`, `NullSpace`, `CauchySchwarz`) |
| §10.2 | `Physicslib4/Spacetime/` (`Causality`, `Curves`, `CausalComplement`, `CausalStructure`, `Minkowski`, `MinkowskiDirected`, `LorentzianSpacetime`, `IsometryCausality`, …) |
| §10.3 | `Physicslib4/AQFT/HaagKastler/`, `Physicslib4/GNS/` (`Irreducibility`, `Superselection`, `RadonNikodym`, `ExtremeState`, …), `Physicslib4/AQFT/KMS.lean`, `Physicslib4/Analysis/StripPeriodicExtension.lean` |
| §10.4 | `Physicslib4/AQFT/HaagKastlerCurved/` (`LocalVonNeumann`, `StabilizerAction`, `StabilizerKMS`, `Purity`, `GeometricCovariance`, …) |
| §10.5 | `Physicslib4/AQFT/HaagKastlerCurved/GeneralCovariance.lean` |

### Formalisation status

The blueprint annotates every node with the Lean declarations that realise it, so the status of each node is a matter of record rather than of estimate. There is exactly one node in Chapter 10 that is not formalised, and two further places where the Lean is deliberately weaker or differently shaped than the prose. All three are flagged in the blueprint text itself; they are collected here so that they are not discovered by surprise.

**Not formalised (one node).**

- **Theorem 158, "Quasilocal Observables are Strongly Dense in the Bicommutant."** This is the von Neumann density theorem, which Mathlib does not have. The node is left as a stated result of the literature, deliberately not decomposed further, and carries no Lean declaration. The blueprint records exactly what is missing, because it is easy to get wrong: the strong operator topology itself *is* in Mathlib, as `PointwiseConvergenceCLM` (with the weak operator topology as `ContinuousLinearMapWOT`), so the statement is phraseable today. What is absent is the density theorem, and with it Kaplansky. Supplying it — the interaction of the strong topology with commutants — is a development of its own.

**Formalised, but the Lean is weaker than the prose (two places).** Both nodes below carry Lean declarations and formalised proofs; the caveat is one of fidelity, not of coverage.

- **The geodesic clause of a trip (Definitions 42–43).** In Lean, `Physicslib4.Spacetime.IsGeodesic` is defined to be `True`, so it imposes no constraint. A faithful geodesic condition needs the Levi-Civita connection of the metric — auto-parallelism of the tangent vector along the curve — which the pinned version of Mathlib does not provide. The formalised (causal) trip segments are therefore future-oriented timelike (respectively causal) curves with the correct past and future endpoints: the endpoint, timelike/causal, and future-orientation content is faithful, and only the geodesic property is unenforced. This is the one place where the blueprint and the Lean diverge on content.
- **Axiom 5 in curved spacetime (Definition 276).** "Isometries connected to the identity" and "identity-component isometries preserving the future orientation" describe the same group, but the inclusion of the former in the latter rests on a Myers–Steenrod-type rigidity result not yet in Mathlib. The Lean therefore intersects the identity component with the explicitly orientation-preserving subgroup. This is an implementation choice and does not alter the mathematical content of the axiom.

If you'd like to contribute, you may find the following links useful:

- [Blueprint (web)](https://physicslib.github.io/physicslib4/blueprint/)
- [Blueprint (pdf)](https://physicslib.github.io/physicslib4/blueprint.pdf)
- [Dependency graph](https://physicslib.github.io/physicslib4/blueprint/dep_graph_document.html)
- [Documentation pages for this repository](https://physicslib.github.io/physicslib4/docs/)
- [Original Haag–Kastler paper](https://doi.org/10.1063/1.1704187)

## The Blueprint

### Chapters 1–9: unpacking the original axioms

Chapters 1–9 unpack and analyse the original Haag–Kastler axioms one by one:

- **Chapter 1 (p. 3)** presents the original Haag–Kastler axioms as stated in the 1964 paper.
- **Chapter 2 (Axiom 0 – Minkowski Space, p. 4)** examines the role of Minkowski spacetime and compares the standard, indiscrete, Euclidean, and Alexandrov topologies on it, settling on the Alexandrov topology—generated by the "double cone" sets $$I^+(p) \cap I^-(q)$$—as the physically natural choice, which happens to coincide with the Euclidean topology on $$\mathbb{R}^4$$.
- **Chapter 3 (Axiom 1 – Local Algebras, p. 6)** discusses the notion of regions of measurement and the assignment of a C\*-algebra to each such region, arguing that the "physically natural" regions are double cones $$I^+(p) \cap I^-(q)$$ rather than arbitrary open sets with compact closure, and rejecting the causal (light-cone) alternative $$J^+(p) \cap J^-(q)$$ because it would force single points to carry algebras, which conflicts with fields being operator-valued distributions.
- **Chapter 4 (Axiom 2 – Isotony, p. 9)** introduces the GNS Construction in motivating context, studies the isotony condition—the requirement that inclusions of spacetime regions induce \*-monomorphisms of the corresponding algebras—and settles the "common unit" convention flagged in the original axiom by assigning the empty region the algebra $$\mathbb{C}1$$, so that every local algebra automatically contains a unit.
- **Chapter 5 (Axiom 3 – Local Commutativity, p. 12)** introduces the notion of completely spacelike separated regions and the quasilocal algebra, and studies the requirement that observables localised in spacelike separated regions commute, clarifying that this commutation is to be understood inside the quasilocal algebra $$\mathfrak{U}$$, since isotony alone cannot place two spacelike-separated (and hence non-nested) regions in a common algebra.
- **Chapter 6 (Axiom 4 – Quasilocal Algebra, p. 14)** analyses the construction of the quasilocal algebra as the completion of the set-theoretic union of all local algebras, and the axiom that $$\mathfrak{U}$$ contains all observables of interest—which is shown to mean that $$\pi_\omega(\mathfrak{U})$$ is strongly dense in the von Neumann algebra $$\pi_\omega(\mathfrak{U})''$$ it generates, so that any "missing" observable in $$\pi_\omega(\mathfrak{U})'' \setminus \pi_\omega(\mathfrak{U})$$ is experimentally indistinguishable from one in $$\mathfrak{U}$$.
- **Chapter 7 (Axiom 5 – Lorentz Covariance, p. 17)** studies the action of the inhomogeneous Lorentz group (connected to the identity) on the net of local algebras and the covariance requirement, and shows, via the Bounded Linear Transformation Theorem, how this norm-one action extends uniquely from the dense union of local algebras to the whole quasilocal algebra.
- **Chapter 8 (Axiom 6 – Primitivity, p. 19)** examines faithful and irreducible representations, noting that every unital C\*-algebra already has a faithful representation (Gelfand–Naimark) so primitivity is a genuinely extra condition; this axiom is ultimately abandoned in the sharpened formulation, following later presentations by Haag himself, on the grounds that its physical motivation is thin.
- **Chapter 9 (Haag–Kastler Axioms in Curved Spacetime, p. 21)** generalises the Haag–Kastler axioms from Minkowski spacetime to curved (Lorentzian) spacetime. It first pins down a precise definition of Lorentzian spacetime and its Alexandrov topology, then shows—via a Schwarzschild black-hole counterexample—that a quasilocal algebra need not exist on a generic Lorentzian spacetime, so Local Commutativity and the local-algebra axiom must be restated relative to a common containing region rather than a global algebra. The final section replaces Lorentz covariance with covariance under identity-component isometries, together with the Myers–Steenrod formalisation remark recorded under [Formalisation status](#formalisation-status).

### Chapter 10: the formalisation-ready content

Chapter 10 restates the axioms in a form amenable to auto-formalisation and proves everything they depend on. Its five top-level sections are described below in order; the complete, itemised list of all 309 numbered declarations follows in [What is Being Formalised](#what-is-being-formalised).

- **§10.1 GNS Construction Details (pp. 28–37).** States and proves the GNS Construction Theorem (Theorem 15) in full detail—construction of the GNS Hilbert space, the \*-representation, the cyclic vector, faithfulness of the representation for a faithful state, and uniqueness up to unitary equivalence—since both the theorem and specific steps of its proof are used in the axioms that follow. The two supporting objects are the state (Definition 13) and the cyclic vector (Definition 14); the auxiliary results are the Cauchy–Schwarz inequality for positive functionals (Lemma 16) and the two equivalent descriptions of the GNS left ideal $$\mathcal{N}$$, which is shown to be a closed linear subspace (Lemmas 17–18). §10.1.3 is a prose summary and carries no numbered items.

- **§10.2 Spacetime (pp. 37–67).** The largest section by declaration count (112 items, Definitions 19–130), building the entire causal and topological apparatus the axioms are indexed on. It proceeds in seven layers.
  - *Spacetime, tangent-vector causality, curves, and trips (pp. 37–44, items 19–50).* Gives precise definitions of spacetime (Definition 19) and standard Minkowski spacetime (Definition 20); classifies tangent vectors as timelike, spacelike, or null (Definition 21) and proves the trichotomy (Lemma 22), the reverse Cauchy–Schwarz and reverse triangle inequalities for timelike vectors (Lemmas 23–24), and the cone geometry—orientation of pointing vectors, the sign lemma, definiteness of the spacelike complement of a timelike vector, and convexity of the cones (Lemmas 27–30)—alongside time orientations (Definition 25) and future- and past-pointing vectors (Definition 26). Then paths, curves, and oriented curves are defined as equivalence classes of paths up to reparametrisation (Definitions 31–36), with causal type and future/past orientation each shown well-defined on the quotient (Theorems 35 and 37) and a forgetful projection from oriented to unoriented curves (Theorem 38). Endpoints (Definition 39) come with two point-set lemmas—an extremal parameter lies in the frontier, and two endpoints force a compact parameter interval (Lemmas 40–41)—followed by trips and causal trips (Definitions 42–43, subject to the geodesic-placeholder caveat under [Formalisation status](#formalisation-status)), transitivity of chronological and causal precedence (Theorem 44), the causality condition (Definition 45) and the resulting strict partial order (Theorem 46), chronological and causal futures and pasts (Definitions 47–48), and their basic inclusion and monotonicity properties (Lemmas 49–50).
  - *§10.2.1 Causal diamonds (p. 44, items 51–65).* Introduces the causal diamond $$J^+(p) \cap J^-(q)$$ and the chronological (Alexandrov) diamond $$I^+(p) \cap I^-(q)$$ (Definition 51), with the structural properties of the causal diamond—monotonicity under endpoint spread, causal convexity, and that nonemptiness forces $$p \prec q$$ (Lemma 52)—and the containment of chronological diamonds in causal ones, together with the identification of the Alexandrov basis as exactly the chronological diamonds (Theorem 53). It then develops spacelike separation of points and of regions (Definitions 54–55, Lemmas 56–57), the spacelike complement $$\mathbf{B}^\perp$$ (Definition 58) and its order structure—antitone, extensive on the double complement, with the triple complement collapsing, making complementation the Galois connection attached to the spacelike-separation relation (Lemma 59). The double complement is packaged as the causal closure operator (Definition 60, Lemma 61), whose fixed points are the causally complete regions (Definition 62). These form a complete lattice—meets are intersections, joins are causal closures of unions—on which the causal complement is an order-reversing involution (Theorem 63); the set-level De Morgan laws (Lemma 64) then lift to full binary and infinitary De Morgan laws on the lattice (Theorem 65). The blueprint is careful to record what does *not* hold: the full orthocomplement law $$\mathbf{B} \wedge \mathbf{B}^\perp = \bot$$ fails at this generality, because the trip-based causal relation is irreflexive and so a point is spacelike-separated from itself.
  - *§10.2.2 Causal convexity (p. 48, items 66–68).* Defines a causally convex region as one containing every point causally between two of its own points (Definition 66), shows causal diamonds are causally convex (Lemma 67), and shows every spacelike complement—hence every causally complete region—is causally convex (Theorem 68).
  - *§10.2.3 Causal convexity: closure structure, and the Alexandrov basis theorems (p. 49, items 69–89).* The causally convex regions are shown to form a closure system (Lemma 69), giving the causal-convex hull (Definition 70) as a genuine closure operator whose closed sets are exactly the causally convex regions (Lemmas 71, Theorem 72). The subsection then turns to the Alexandrov topology (Definition 73): every diamond is open (Lemma 74); chronological futures and pasts are open under an explicit "no endpoints" hypothesis (Lemma 75) and unconditionally on standard Minkowski spacetime, where the coordinate-cone description discharges the hypothesis (Lemma 76). Minkowski spacetime and Lorentzian spacetime are then defined (Definitions 77–78, the latter as a spacetime whose Alexandrov topology is Hausdorff), with a bundled form of spacelike separation and basis openness (Lemma 79). A point lying in no diamond is pathological: its only Alexandrov neighbourhood is the whole space (Lemma 80), and the Hausdorff assumption rules this out, forcing the diamonds to cover the space (Lemma 81). Given downward-directedness the diamonds form a genuine topological basis (Theorem 82); past and future interpolation on standard Minkowski (Lemmas 83–84) supply downward-directedness there (Lemma 85), and common chronological predecessors and successors supply upward-directedness (Lemmas 86–88), so on standard Minkowski the diamonds are an unconditional basis (Theorem 89). Upward-directedness is what the quasilocal colimit of §10.3.1 later consumes.
  - *§10.2.4 Dilations are causal automorphisms but not isometries (p. 54, items 90–92).* The dilations $$x \mapsto \lambda x$$ preserve the Minkowski cones (Lemma 90) and are therefore causal automorphisms (Theorem 91), yet scale the metric by $$\lambda^2$$ and so are not isometries for $$\lambda \neq 1$$ (Theorem 92). This is the counterexample that forces the general-covariance morphism of §10.5 to be specified geometrically rather than causally.
  - *§10.2.5 Isometries and basis-set preservation (p. 54, items 93–98).* Single-metric transport: isometries preserve the causal classification of tangent vectors (Lemma 93), paths have unique differentials and well-defined pushforwards (Lemmas 94–95), future-orientation-preserving isometries preserve chronology (Lemma 96) and map Alexandrov-basis diamonds to diamonds (Lemma 97), which is exactly the well-definedness condition for the Axiom 5 action (Lemma 98).
  - *§10.2.6 Pullback metrics and cross-metric isometries (p. 55, items 99–130).* The single-metric lemmas above compare a spacetime with itself; general covariance instead compares two different metrics on one carrier, so the transport statements are redone cross-metric. This subsection defines the pullback $$\psi^* g$$ of a spacetime metric as a bundled family of continuous bilinear forms (Definition 99) and verifies every obligation in turn: the differential of a diffeomorphism is a linear equivalence (Lemma 100), with the two round-trip cancellation identities that Mathlib does not supply for a global `Diffeomorph` proved by hand (Lemmas 101–103); the pullback metric is symmetric, non-degenerate, Lorentzian, and a smooth section of the bilinear-form bundle (Lemmas 104–107), so the pullback of a spacetime is a spacetime (Theorem 108). Two-sided preservation of future orientation is then defined (Definition 109) and the pullback time orientation is shown to be bundle-smooth, nowhere vanishing, and everywhere timelike (Lemmas 110–113), with transport of future-pointing timelike and null vectors (Lemmas 114–115) giving two-sided orientation preservation (Lemma 116). Cross-metric isometries are defined (Definition 117) and shown closed under inverses (Lemma 118), to preserve causal classification (Lemma 119), to push paths forward preserving the timelike/causal conditions and endpoints (Lemmas 120–123), and to transport chronological precedence and the chronological future and past (Lemmas 124–126), hence to preserve Alexandrov-basis sets (Lemma 127). A general topological lemma—a bijection matching generating families is a homeomorphism (Lemma 128)—then identifies the pullback Alexandrov topology (Lemma 129) and yields that the pullback of a Lorentzian spacetime is again a Lorentzian spacetime (Theorem 130). Without Theorem 130 the phrase "the net over $$\psi^*(M,g)$$" in §10.5 would have no referent.

- **§10.3 Haag–Kastler Axioms in Minkowski spacetime (pp. 67–104).** The largest section by definition and theorem count (140 items, Definitions 131–270). Each axiom is stated as a definition so that it appears as a node in the declaration graph.
  - *The axioms and the quasilocal colimit (§10.3 and §10.3.1, pp. 67–86, items 131–160).* Axiom 1 (Local Algebras, Definition 131) assigns an abstract C\*-algebra to every Alexandrov-basis set, with $$\emptyset \mapsto \mathbb{C}1$$. Axiom 2 (Isotony, Definition 132) now supplies the family of unital \*-monomorphisms $$i_{\mathbf{B}_1 \mathbf{B}_2}$$ **as chosen data**, subject to injectivity, an identity law, and a composition law—so that $$\mathbf{B} \mapsto \mathfrak{U}(\mathbf{B})$$ is a functor on the inclusion order of basis sets. The blueprint is explicit that the family cannot be an existence statement (the identity and composition conditions are equations between the maps themselves) and that the inclusion hypothesis is non-strict, matching the Lean. §10.3.1 then cashes this in: the diamonds are directed under inclusion (Lemma 133), the isotony family is a directed system in Mathlib's sense (Lemma 134), and the direct limit carries a well-defined norm (Lemmas 135–137) making it a normed \*-algebra (Lemma 138) satisfying the C\*-inequality (Lemma 139) but not, in general, complete. A block of results stated for an arbitrary normed \*-algebra under standing hypotheses (Definition 140) then carries the structure through completion—the involution and its extension (Definition 141, Lemma 142), the completion coercion as a bundled \*-algebra homomorphism (Lemma 143), and the passage of the C\*-inequality, the normed $$\mathbb{C}$$-algebra structure, and finally the C\*-algebra property to the completion (Lemmas 144–146)—yielding that the completion of the quasilocal colimit is a C\*-algebra (Lemma 147). The quasilocal algebra $$\mathfrak{U}$$ is defined as that colimit-then-completion (Definition 148); the blueprint records why the shortcut of realising $$\mathfrak{U}$$ as a closed \*-subalgebra of an ambient C\*-algebra is rejected—it would assume an ambient algebra containing copies of every $$\mathfrak{U}(\mathbf{B})$$, for which the physics supplies no justification. Axiom 3 (Local Commutativity, Definition 149) and the quasilocal observable (Definition 150) follow. **Axiom 4 is now split in two.** Axiom 4 (Quasilocal Completeness, Definition 151) is presented as a bridge principle—the one axiom joining physical reality to the formalism, asserting the one-way inclusion that every physical observable corresponds to a quasilocal observable, and therefore having no mathematical consumers. The mathematical content previously conflated with it is separated out as a theorem: every local net satisfying Axiom 2 admits a quasilocal algebra, with an injective cocone of canonical embeddings whose images are dense (Theorem 152, with the supporting Lemmas 153–157). The indexing over Alexandrov-basis sets only is essential and not stylistic, since the algebras attached to non-basis subsets are junk fibres about which the axioms say nothing. Theorem 158 is the density result that keeps the bridge principle tenable in the presence of larger bicommutants, and is the one node deliberately left unformalised. Axiom 5 (Lorentz Covariance, Definition 159) and the bundled `HaagKastlerNet` (Definition 160) close the block.
  - *§10.3.2 Einstein Causality (p. 86, item 161).* Derives the operator form of local commutativity in any \*-representation of the quasilocal algebra (Theorem 161).
  - *§10.3.3 Local von Neumann Algebras (p. 86, items 162–174).* Defines the local von Neumann algebra $$R(\mathbf{B}) = \pi(\mathfrak{U}(\mathbf{B}))''$$ of a region in a representation (Definition 162), registers it as a first-class `VonNeumannAlgebra` via the bicommutant-of-a-self-adjoint-set lemma (Lemma 163, Definition 164), and proves Microcausality (Theorem 165) and Isotony of the von Neumann net (Theorem 166), together with their bundled forms (Theorem 167) and the region-indexed assignment $$\mathbf{B} \mapsto R(\mathbf{B})$$ as an order-preserving map—the net of von Neumann algebras itself (Definition 168). It then proves the Statistical Independence (Schlieder) property in set-level and bundled forms (Theorems 169–170): if the cyclic vector of one region is cyclic for its local observables, it is separating for the local von Neumann algebra of any spacelike-separated region. Additive-free locality (Theorem 171) expresses locality through the spacelike complement without attaching an algebra to the unbounded complement itself. Geometric Covariance (Theorem 172) shows conjugation by the implementing unitary carries $$R(\mathbf{B})$$ onto $$R(L \cdot \mathbf{B})$$; being a factor is therefore constant along the Lorentz orbit of a region (Theorem 173), and the set equality upgrades to a first-class \*-algebra isomorphism of the bundled algebras (Theorem 174).
  - *§10.3.4 Relative Commutants of Nested Local Algebras (p. 88, items 175–182).* A new block organising the theory of inclusions $$R(\mathbf{B}_1) \subseteq R(\mathbf{B}_2)$$ around the relative commutant $$R(\mathbf{B}_1)' \cap R(\mathbf{B}_2)$$ (Definition 175). It proves antitonicity of the commutant (Theorem 176), that the relative commutant lies in the larger algebra and commutes with the smaller (Theorems 177–178), and that it always contains the centre of the ambient algebra (Theorem 179). An inclusion is irreducible when its relative commutant is trivial (Definition 180); an irreducible inclusion forces the ambient algebra to be a factor (Theorem 181), and the trivial self-inclusion is irreducible exactly when the algebra is a factor (Theorem 182).
  - *§10.3.5 Irreducibility and Schur's Lemma (p. 90, items 183–205).* Introduces irreducible representations via their commutant (Definition 183) and establishes the Topological Schur Lemma for cyclic representations (Theorem 184) together with the operator-theoretic bridge identifying commutant scalars with coefficients proportional to the state (Theorem 185). Defines pure states (Definition 186) and proves "pure implies irreducible" directly (Theorem 187), then the full equivalence Pure $$\iff$$ Irreducible (Theorem 190) via a GNS Radon–Nikodym theorem realising every dominated positive functional as an operator in the commutant (Theorems 188–189). An irreducible representation generates a factor (Theorem 191) and, more sharply, all of $$\mathcal{B}(H)$$ (Theorem 192), with a bundled density form (Theorem 193); consequently the GNS representation of a pure state generates a factor (Theorem 194) and all of $$\mathcal{B}(H)$$ (Theorem 195). The norm of a positive linear functional on a unital C\*-algebra equals its value on the unit (Theorem 196), which supports Pure $$\iff$$ Extreme Point of the state space (Definition 197, Theorem 198), the underlying convexity and the bridge to Mathlib's extreme-points API (Theorem 199), and weak-\* compactness of the state space (Theorem 203), which supplies the existence of pure states via Krein–Milman. The pullback of a state along a unital \*-homomorphism is introduced as its own object (Definition 200) with functoriality (Theorem 201) and the invariance of purity under a \*-isomorphism (Theorem 202). The section closes by specialising to the quasilocal algebra (Theorems 204–205).
  - *§10.3.6 Unitary Equivalence and Superselection (p. 93, items 206–207).* Defines unitary equivalence of representations (Definition 206) and shows irreducibility and factoriality are unitary invariants, transported by the cross-space conjugation induced by the implementing unitary (Theorem 207).
  - *§10.3.7 GNS Covariance (p. 94, items 208–213).* A new block. Cyclicity pulls back along a surjective \*-homomorphism (Lemma 208), so GNS data transports covariantly along a \*-isomorphism of the algebras (Theorem 209), restated as a unitary equivalence (Theorem 210). Pullback along a surjection preserves the image algebra (Lemma 211), whence superselection type transports along a \*-isomorphism (Theorem 212): the whole sector structure is an invariant of the algebra, not of its presentation. Applied to the covariance equivalence $$\alpha_L : \mathfrak{U}(\mathbf{B}) \simeq \mathfrak{U}(L \cdot \mathbf{B})$$ supplied by Axiom 5, this says the superselection type of a local state is constant along the Lorentz orbit of its region (Theorem 213).
  - *§10.3.8 Disjointness and Quasi-Equivalence (p. 95, items 214–231).* Defines disjointness via the vanishing of all intertwiners (Definition 214) and the coarser quasi-equivalence via a \*-isomorphism of generated von Neumann algebras (Definition 215). Proves Schur's Lemma in the form of the Irreducible Dichotomy—two irreducible representations are either disjoint or unitarily equivalent (Theorem 216)—together with Schur multiplicity (Lemma 217) and the triviality of the endomorphism algebra of an irreducible representation (Lemma 218). The commutant is packaged as the self-intertwiner (gauge) von Neumann algebra, trivial exactly when the representation is irreducible (Theorem 219), with double-commutant duality (Theorem 220) and the factor/triviality duality between an algebra and its commutant (Theorem 221). A supporting run develops the centre from scratch: abelian $$\iff$$ self-commuting (Lemma 222), the centre $$Z(R) = R \cap R'$$ (Definition 223) and its being a von Neumann algebra (Lemma 224), the general two-algebra intersection lemma that the relative commutants of §10.3.4 need (Lemma 225), the centre is abelian (Theorem 226), $$R$$ is abelian iff it equals its centre (Lemma 227), a factor is abelian iff it is the scalars (Theorem 228), an algebra and its commutant share a centre (Theorem 229), and factoriality is triviality of the centre (Theorem 230). The Pure-State Dichotomy underlying superselection sectors (Theorem 231) closes the block.
  - *§10.3.9 Direct Sums, Amplification, and Reducibility (p. 98, items 232–235).* Defines the direct-sum representation on the $$\ell^2$$-direct sum (Definition 232), shows each summand embeds as a subrepresentation whose projection lies in the commutant of the sum (Theorem 233), defines the $$\iota$$-fold amplification (Definition 234), and proves a direct sum with at least two nonzero summands is reducible, so a multiply-amplified representation is never irreducible (Theorem 235).
  - *§10.3.10 Covariant States and the Covariance Action (p. 99, items 236–254).* Defines covariant families of local states (Definition 236) with their composition law (Lemma 237), and the lift of the fibrewise covariance action to a \*-automorphism of the quasilocal algebra (Definition 238), with uniqueness (Lemma 239), existence (Theorem 240), and existence for the trivial net (Theorem 241). This data is bundled as a `CovariantQuasilocalAlgebra` (Definition 242) on which the action is a genuine group action (Lemma 243). Invariant states are defined (Definition 244) and shown to be implemented by GNS unitaries (Theorem 245); a state that is both invariant and pure yields a GNS representation that is simultaneously covariant and irreducible (Theorem 246). A "bounded-generator" scaffold toward the spectrum condition follows, deliberately sidestepping Stone's theorem and unbounded self-adjoint operators: positive energy for a bounded generator (Definition 247) with its API (Theorem 248), a generator-parameterised vacuum state (Definition 249) and its Stone-free consequences (Theorem 250), the future-timelike translation subgroup (Definition 251), and the vacuum state with that concrete predicate substituted in, leaving no free parameter (Definition 252). Purity is preserved by any \*-automorphism and is therefore covariance-invariant (Theorem 253), and GNS data transports along the quasilocal covariance action (Theorem 254).
  - *§10.3.11 The Separating Vector of a Faithful State (p. 102, item 255).* The cyclic vector of a faithful state is also separating for the image of the representation (Theorem 255)—the basic datum of Tomita–Takesaki modular theory. This holds in any representation reproducing a faithful state, not only the canonical GNS one.
  - *§10.3.12 The KMS Condition and Thermal Equilibrium (p. 102, items 256–265).* Introduces one-parameter automorphism groups (Definition 256) and KMS states (Definition 257) as the algebraic characterisation of thermal equilibrium. The condition is phrased purely as an analyticity statement about correlation functions, so—unlike the spectrum condition—it needs no unbounded-operator theory. The KMS state set is convex (Theorem 258); a boundary-coincidence argument at $$a = 1$$ (Lemma 259) together with the Strip-Liouville Principle (Definition 260), proved at positive inverse temperature via an $$i\beta$$-periodic entire extension (Theorem 261) and Liouville's theorem (Theorem 262), yields that KMS states are automatically invariant under the time evolution (Theorem 263); uniqueness on the strip from boundary values (Theorem 264) gives uniqueness of the analytic completion of a KMS correlation function (Theorem 265).
  - *§10.3.13 KMS States for the Covariance Flow (p. 104, items 266–270).* A one-parameter subgroup of the inhomogeneous Lorentz group induces a one-parameter automorphism group on the quasilocal algebra via the covariance lift (Definition 266, Lemma 267); KMS states for that flow are defined accordingly (Definition 268) and shown convex (Theorem 269). The zero-temperature ($$\beta \to \infty$$) counterpart—a ground state for a covariance flow, whose GNS-implementing unitary group has positive energy—is recorded alongside it (Definition 270).

- **§10.4 Haag–Kastler Axioms in Curved Spacetime (pp. 105–114).** 49 items, Definitions 271–319. The axioms are restated for a Lorentzian spacetime: Local Algebras (Definition 271), Isotony (Definition 272, again supplying the family as chosen data with identity and composition laws), Local Commutativity (Definition 273, which now **consumes** the Axiom 2 family rather than choosing its own witnesses), local observables (Definition 274), Local Completeness (Definition 275), and Isometric Covariance (Definition 276), bundled into a `HaagKastlerNet` in curved spacetime (Definition 277). The change to Axioms 2 and 3 has a visible consequence downstream: statements about nested regions have to factor a three-fold inclusion $$\mathbf{B}_1 \subseteq \mathbf{B}_2 \subseteq \mathbf{B}$$ inside a common containing algebra, and that factorisation is now the composition law of Axiom 2, so **the coherence hypotheses that earlier versions carried at each such site are gone**—curved isotony (Theorem 282) and the curved von Neumann net (Definition 284) are unconditional. Explicit hypotheses remain only where the abstract interface genuinely cannot supply them, namely basis-set preservation and the coherence of the stabiliser action with the chosen embeddings in Geometric Covariance (Theorem 288), discharged for nets arising from a concrete geometric spacetime.
  - *§10.4.1 Einstein Causality in Curved Spacetime (p. 107, item 278).* The operator form of local commutativity, expressed in a representation of a common containing local algebra rather than of a global quasilocal algebra (Theorem 278).
  - *§10.4.2 Local von Neumann Algebras in Curved Spacetime (p. 107, items 279–290).* The Minkowski development of §10.3.3 mirrored relative to a containing region: the local von Neumann algebra of a subregion and its bundled registration (Definitions 279–280), Microcausality (Theorem 281), unconditional Isotony (Theorem 282), the bundled form (Theorem 283), the net as an order-preserving map on the poset of subregions (Definition 284), Statistical Independence in set-level and bundled forms (Theorems 285–286), additive-free locality (Theorem 287), and Geometric Covariance via the stabiliser GNS representation (Theorem 288) with orbit-invariance of factoriality (Theorem 289) and the upgrade to a \*-algebra isomorphism (Theorem 290).
  - *§10.4.3 Relative Commutants of Nested Local Algebras in Curved Spacetime (p. 109, items 291–299).* The curved counterpart of §10.3.4: the relative commutant of a nested pair inside a containing region (Definition 291), its containment in the larger algebra, commutation with the smaller, and containment of the centre (Theorems 292–294), irreducible inclusions (Definition 295) and their consequences (Theorems 296–297), plus the abelian/centre facts specialised to curved local algebras (Theorems 298–299).
  - *§10.4.4 Purity of States on Local Algebras in Curved Spacetime (p. 110, items 300–304).* Each local algebra is a unital C\*-algebra with its own state space, so the abstract purity characterisations are registered per region: Pure $$\iff$$ Extreme Point (Theorem 300), Pure $$\iff$$ Irreducible GNS (Theorem 301), the GNS representation of a pure state generates a factor and indeed all of $$\mathcal{B}(H)$$ (Theorem 302), the Irreducible Dichotomy for a curved local algebra (Theorem 303), and GNS covariance for curved local algebras (Theorem 304).
  - *§10.4.5 Covariant States in Curved Spacetime (p. 111, items 305–306).* Covariant families of local states in curved spacetime (Definition 305) and their composition law (Lemma 306).
  - *§10.4.6 The Stabilizer GNS Unitary in Curved Spacetime (p. 112, items 307–313).* Since no quasilocal algebra exists on a generic Lorentzian spacetime, the covariance action restricts to the stabiliser subgroup $$\mathrm{Stab}(\mathbf{B})$$ of a region, giving automorphisms of the single local algebra $$\mathfrak{U}(\mathbf{B})$$ (Definition 307) that form a genuine group action (Lemma 308). A stabiliser-invariant state carries a unitary GNS representation of $$\mathrm{Stab}(\mathbf{B})$$ (Theorem 309), strongly continuous when the matrix coefficients are continuous (Theorem 310); a state both stabiliser-invariant and pure yields an irreducible covariant representation (Theorem 311); purity is invariant under the stabiliser action (Theorem 312), and GNS data transports along it (Theorem 313).
  - *§10.4.7 KMS States for a Killing Flow (p. 113, items 314–319).* Killing flows are identified as one-parameter subgroups of the stabiliser of a region, inducing a one-parameter automorphism group on $$\mathfrak{U}(\mathbf{B})$$ (Definition 314, Lemma 315). KMS states for a Killing flow (Definition 316) are the precise algebraic sense in which the Hartle–Hawking and Gibbons–Hawking states are thermal. Such a state at positive inverse temperature automatically carries a strongly continuous one-parameter unitary group on its GNS Hilbert space implementing the flow, yielding the curved-spacetime thermal representation—the analogue of the Minkowski vacuum representation (Theorem 317); these states form a convex set (Theorem 318), and the corresponding ground state is recorded alongside them (Definition 319).

- **§10.5 General Covariance: Nets on Pullback-Related Metrics (pp. 114–116).** Two definitions, and the newest structural addition to the blueprint. The gauge group of general relativity is the full diffeomorphism group of $$M$$, so the physical content of a spacetime is its diffeomorphism-equivalence class and not the pair $$(M, g)$$; the hole argument shows that treating a relabelling as physical would destroy determinism, and Leibniz equivalence resolves it by declaring diffeomorphic models to represent the same physical situation. Accordingly, an equivalence of Haag–Kastler nets is defined (Definition 320) as a chosen family of unital \*-isomorphisms $$\Theta_\mathbf{B} : \mathfrak{U}_1(\mathbf{B}) \to \mathfrak{U}_2(e(\mathbf{B}))$$ along a basis-set-preserving bijection $$e$$ of carriers, natural with respect to the isotony embeddings. The carriers are related by data rather than by a type equality, deliberately: an equality of carrier types cannot be transported along and would force every comparison through a cast. A net theory is then a section assigning a net to every Lorentzian spacetime, and it is generally covariant when the nets over $$L$$ and over its pullback $$\psi^* L$$ are equivalent along $$\psi$$ (Definition 321). Four points are worth carrying away: this is a **postulate, not a theorem**—nothing forces the two nets to be isomorphic, and it says nothing about backgrounds that are not diffeomorphism-related; the morphism is specified geometrically rather than causally, because a purely causal morphism would admit the dilations (Theorems 91–92) and thereby demand a scale covariance that is false for a massive theory; the relabelling must be $$\psi$$ and not the identity, since a basis set of one metric is in general not a basis set of the other; and general covariance is a property of the section $$L \mapsto \mathfrak{U}_L$$, not a sixth field of the net structure, so no restriction to diffeomorphisms connected to the identity is needed here.


## What is Being Formalised

Only the content of Chapter 10 is formalised in Lean. Its declarations are numbered consecutively from Definition 13 through Definition 321 — 309 in total — and **every one of them is listed below**, in numerical order, under the blueprint subsection in which it appears. Each entry links to the node in the web blueprint and names the principal Lean declaration that realises it; where a node maps onto several declarations, the count of the remainder is shown. This list is derived mechanically from the blueprint's own `\lean` and `\leanok` annotations, so it can be checked line by line against the source.

The lower numbers, 1 through 12, label supporting theorems and definitions introduced along the way in the motivational Chapters 4–9. None of them carries a Lean declaration, and they are **not** formalised: C\*-spectrum invariance under inclusion (Theorem 1), uniqueness of the C\*-norm (Theorem 2), strong density of unital \*-algebras (Theorem 3), the Bounded Linear Transformation Theorem (Theorem 4), Gelfand–Naimark (Theorem 5), the rarity of primitive abelian C\*-algebras (Lemma 6), existence of a Lorentz metric (Theorem 7), causal convexity and strong causality (Definitions 8–9), properties of the Alexandrov topology (Theorem 10), Lorentzian spacetime (Definition 11), and the local observable (Definition 12).

### §10.1 GNS Construction (pp. 28–37)

**§10.1.1 GNS Construction Theorem (p. 28)**

- [**Definition 13**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:state) — State · `Physicslib4.GNS.State` (+1 more)
- [**Definition 14**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:cyclic-vector) — Cyclic Vector · `Physicslib4.GNS.IsCyclicVector`
- [**Theorem 15**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-construction-theorem) — GNS Construction Theorem · `Physicslib4.GNS.gns_construction`

**§10.1.2 Auxiliary Results Used in the Proof (p. 34)**

- [**Lemma 16**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cauchy-schwarz-inequality) — Cauchy–Schwarz Inequality · `Physicslib4.GNS.cauchy_schwarz_inequality`
- [**Lemma 17**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lmm1) — The two descriptions of the GNS left ideal $$\mathcal{N}$$ agree · `Physicslib4.GNS.lmm1`
- [**Lemma 18**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lmm2) — $$\mathcal{N}$$ is a closed linear subspace · `Physicslib4.GNS.lmm2`

### §10.2 Spacetime and causal structure (pp. 37–67)

**§10.2 opening run — spacetime, tangent-vector causality, curves, trips, futures and pasts (p. 37)**

- [**Definition 19**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacetime) — Spacetime · `Physicslib4.Spacetime`
- [**Definition 20**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:standard-minkowski-spacetime) — Standard Minkowski Spacetime · `Physicslib4.StandardMinkowskiSpacetime`
- [**Definition 21**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:timelike-spacelike-null-vectors) — Timelike, Spacelike, or Null Vectors · `Physicslib4.Spacetime.IsTimelike` (+2 more)
- [**Lemma 22**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-classification) — Causal Classification · `Physicslib4.Spacetime.isTimelike_or_isNull_or_isSpacelike` (+5 more)
- [**Lemma 23**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:reverse-cauchy-schwarz) — Reverse Cauchy–Schwarz for Timelike Vectors · `Physicslib4.reverse_cauchy_schwarz_of_lorentzianAt` (+1 more)
- [**Lemma 24**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:timelike-cone-convexity) — Timelike Cone Convexity and Reverse Triangle Inequality · `Physicslib4.add_isTimelike_of_lorentzianAt` (+3 more)
- [**Definition 25**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:time-orientable) — Time Orientation · `Physicslib4.Spacetime.TimeOrientation` (+1 more)
- [**Definition 26**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-and-past-pointing-vectors) — Future and Past Pointing Vectors · `Physicslib4.Spacetime.IsFuturePointing` (+1 more)
- [**Lemma 27**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pointing-orientation) — Orientation of Pointing Vectors · `Physicslib4.Spacetime.isTimelike_or_isNull_of_isFuturePointing` (+2 more)
- [**Lemma 28**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cone-sign-lemma) — Sign Lemma for the Future Cone · `Physicslib4.nonneg_of_orthogonal_timelike` (+4 more)
- [**Lemma 29**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-definite) — Definiteness of the Spacelike Complement · `Physicslib4.eq_zero_of_forall_bilin_eq_zero` (+2 more)
- [**Lemma 30**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:future-cone-convexity) — Convexity of the Future Cone · `Physicslib4.Spacetime.isFuturePointing_add` (+10 more)
- [**Definition 31**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:paths) — Paths · `Physicslib4.Spacetime.Path` (+1 more)
- [**Definition 32**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:curves) — Curves · `Physicslib4.Spacetime.Curve` (+1 more)
- [**Definition 33**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:timelike-and-causal-smooth-curves) — Timelike and Causal Smooth Curves · `Physicslib4.Spacetime.IsTimelikeSmoothCurve` (+1 more)
- [**Definition 34**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-and-past-oriented-smooth-curves) — Future and Past Oriented Smooth Curves · `Physicslib4.Spacetime.IsFutureOrientedSmoothCurve` (+1 more)
- [**Theorem 35**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:smooth-curve-causal-well-defined) — Reparametrisation-Invariance of the Causal Type · `Physicslib4.Spacetime.isTimelikeSmoothCurve_ofPath_iff` (+1 more)
- [**Definition 36**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:oriented-smooth-curve) — Oriented Smooth Curve · `Physicslib4.Spacetime.OrientedSmoothCurve`
- [**Theorem 37**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:oriented-curve-well-defined) — Reparametrisation-Invariance of Orientation · `Physicslib4.Spacetime.isFutureOrientedCurve_ofPath_iff` (+1 more)
- [**Theorem 38**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:oriented-curve-projection) — The Forgetful Projection of Oriented Curves · `Physicslib4.Spacetime.OrientedSmoothCurve.toSmoothCurve` (+1 more)
- [**Definition 39**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:endpoints) — Endpoints · `Physicslib4.Spacetime.IsEndpoint` (+2 more)
- [**Lemma 40**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:extremal-parameter-mem-frontier) — An extremal parameter lies in the frontier · `Physicslib4.Spacetime.mem_frontier_of_isMin` (+3 more)
- [**Lemma 41**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:endpoint-parameter-space-eq-Icc) — Two endpoints force a compact parameter interval · `Physicslib4.Spacetime.parameterSpace_eq_Icc_of_endpoints`
- [**Definition 42**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:trip) — Trip · `Physicslib4.Spacetime.IsTripSegment` (+2 more) *(geodesic clause is a placeholder in Lean — see [Formalisation status](#formalisation-status))*
- [**Definition 43**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-trip) — Causal Trip · `Physicslib4.Spacetime.IsCausalTripSegment` (+2 more) *(geodesic clause is a placeholder in Lean — see [Formalisation status](#formalisation-status))*
- [**Theorem 44**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:precedence-transitive) — Transitivity of chronological and causal precedence · `Physicslib4.Spacetime.chronologicallyPrecedes_trans` (+1 more)
- [**Definition 45**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:no-closed-causal-curve) — No Closed Causal Curve (Causality Condition) · `Physicslib4.Spacetime.NoClosedCausalCurve`
- [**Theorem 46**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-order-refinements) — Irreflexivity and Antisymmetry under Causality · `Physicslib4.Spacetime.chronologicallyPrecedes_irrefl` (+2 more)
- [**Definition 47**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:chronological-future-and-chronological-past) — Chronological Future and Chronological Past · `Physicslib4.Spacetime.chronologicalFuture` (+3 more)
- [**Definition 48**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-future-and-causal-past) — Causal Future and Causal Past · `Physicslib4.Spacetime.causalFuture` (+3 more)
- [**Lemma 49**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:chronological-implies-causal) — Chronological Precedence Implies Causal Precedence · `Physicslib4.Spacetime.isCausal_of_isTimelike` (+3 more)
- [**Lemma 50**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:future-past-monotone) — Monotonicity of Futures and Pasts · `Physicslib4.Spacetime.chronologicalFutureSet_mono` (+3 more)

**§10.2.1 Causal diamonds, spacelike complement, and causal closure (p. 44)**

- [**Definition 51**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-diamond) — Causal and chronological diamonds · `Physicslib4.Spacetime.causalDiamond` (+3 more)
- [**Lemma 52**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-diamond-structure) — Structural properties of the causal diamond · `Physicslib4.Spacetime.causalDiamond_subset_of` (+2 more)
- [**Theorem 53**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-diamond-vs-chronological) — Chronological diamonds inside causal diamonds · `Physicslib4.Spacetime.chronologicalDiamond_subset_causalDiamond` (+1 more)
- [**Definition 54**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-related) — Spacelike Related · `Physicslib4.Spacetime.IsSpacelikeRelated`
- [**Definition 55**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completely-spacelike) — Completely Spacelike · `Physicslib4.Spacetime.IsCompletelySpacelike`
- [**Lemma 56**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completely-spacelike-symm) — Symmetry of Spacelike Separation · `Physicslib4.Spacetime.isSpacelikeRelated_comm` (+1 more)
- [**Lemma 57**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completely-spacelike-structural) — Structural Properties of Complete Spacelike Separation · `Physicslib4.Spacetime.isCompletelySpacelike_mono` (+9 more)
- [**Definition 58**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-complement) — Spacelike Complement of a Region · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement`
- [**Lemma 59**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-order) — Order Structure of the Spacelike Complement · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement_antitone` (+3 more)
- [**Definition 60**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-closure) — Causal closure operator · `Physicslib4.Spacetime.LorentzianSpacetime.causalClosure`
- [**Lemma 61**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-closure-is-closure-operator) — The Causal Closure is a Closure Operator · `Physicslib4.Spacetime.LorentzianSpacetime.causalClosure` (+1 more)
- [**Definition 62**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-complete-region) — Causally complete region · `Physicslib4.Spacetime.LorentzianSpacetime.IsCausallyComplete`
- [**Theorem 63**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-lattice) — Lattice of causally complete regions · `Physicslib4.Spacetime.LorentzianSpacetime.CausallyCompleteRegion` (+8 more)
- [**Lemma 64**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-de-morgan) — De Morgan Laws for the Spacelike Complement · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement_union` (+1 more)
- [**Theorem 65**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-complement-de-morgan) — De Morgan Laws for the Causal Complement · `Physicslib4.Spacetime.LorentzianSpacetime.causalComplement_antitone` (+6 more)

**§10.2.2 Causal convexity (p. 48)**

- [**Definition 66**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-convex-region) — Causally convex region · `Physicslib4.Spacetime.IsCausallyConvex`
- [**Lemma 67**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-diamond-causally-convex) — Causal diamonds are causally convex · `Physicslib4.Spacetime.causalDiamond_isCausallyConvex`
- [**Theorem 68**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-convex) — Causally complete regions are causally convex · `Physicslib4.Spacetime.spacelikeComplement_isCausallyConvex` (+2 more)

**§10.2.3 Causal convexity: closure structure, and the Alexandrov basis theorems (p. 49)**

- [**Lemma 69**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causally-convex-closure-ops) — Causally convex regions form a closure system · `Physicslib4.Spacetime.isCausallyConvex_univ` (+4 more)
- [**Definition 70**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-convex-hull) — Causal-convex hull · `Physicslib4.Spacetime.causalConvexHull`
- [**Lemma 71**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-convex-hull-extensive) — The Causal-Convex Hull is Extensive and Causally Convex · `Physicslib4.Spacetime.subset_causalConvexHull` (+1 more)
- [**Theorem 72**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-convex-hull-closure) — The causal-convex hull is a closure operator · `Physicslib4.Spacetime.causalConvexHull_minimal` (+3 more)
- [**Definition 73**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:alexandrov-topology) — Alexandrov Topology · `Physicslib4.Spacetime.alexandrovTopology`
- [**Lemma 74**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-basis-open) — Basis Sets Are Alexandrov-Open · `Physicslib4.Spacetime.isOpen_alexandrov_of_mem_basis`
- [**Lemma 75**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:chronological-future-past-open) — Openness of Chronological Futures and Pasts · `Physicslib4.Spacetime.isOpen_chronologicalFuture_inter_chronologicalPast` (+2 more)
- [**Lemma 76**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-chronological-open) — Unconditional Openness of Chronological Futures and Pasts on Standard Minkowski · `Physicslib4.exists_chronologicalFuture_standardMinkowski` (+5 more)
- [**Definition 77**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:minkowski-spacetime) — Minkowski Spacetime · `Physicslib4.MinkowskiSpacetime`
- [**Definition 78**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentzian-spacetime) — Lorentzian Spacetime · `Physicslib4.Spacetime.LorentzianSpacetime`
- [**Lemma 79**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lorentzian-causal-lifts) — Bundled Spacelike Separation and Basis Openness · `Physicslib4.Spacetime.LorentzianSpacetime.isCompletelySpacelike_comm` (+1 more)
- [**Lemma 80**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-nbhd-univ-of-no-diamond) — No-Diamond Points Have Only the Whole Space as Neighbourhood · `Physicslib4.Spacetime.alexandrov_nbhd_univ_of_no_diamond`
- [**Lemma 81**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-covering-hausdorff) — Covering from the Hausdorff Assumption · `Physicslib4.Spacetime.LorentzianSpacetime.sUnion_alexandrovBasis_eq_univ`
- [**Theorem 82**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:alexandrov-topological-basis) — The Alexandrov Diamonds Form a Topological Basis · `Physicslib4.Spacetime.LorentzianSpacetime.isTopologicalBasis_alexandrovBasis`
- [**Lemma 83**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-past-between) — Past Interpolation on Standard Minkowski · `Physicslib4.Spacetime.exists_past_between_standardMinkowski`
- [**Lemma 84**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-future-between) — Future Interpolation on Standard Minkowski · `Physicslib4.Spacetime.exists_future_between_standardMinkowski`
- [**Lemma 85**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-downward-directed) — Standard Minkowski Diamonds Are Downward-Directed · `Physicslib4.Spacetime.alexandrovBasis_exists_subset_inter_standardMinkowski`
- [**Lemma 86**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-exists-common-past) — Common Chronological Predecessor on Standard Minkowski · `Physicslib4.Spacetime.exists_common_past`
- [**Lemma 87**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-exists-common-future) — Common Chronological Successor on Standard Minkowski · `Physicslib4.Spacetime.exists_common_future`
- [**Lemma 88**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-upward-directed) — Standard Minkowski Diamonds Are Upward-Directed · `Physicslib4.Spacetime.alexandrovBasis_directed`
- [**Theorem 89**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-alexandrov-basis) — The Alexandrov Diamonds are a Basis on Standard Minkowski · `Physicslib4.Spacetime.isTopologicalBasis_alexandrovBasis_standardMinkowski`

**§10.2.4 Dilations are causal automorphisms but not isometries (p. 54)**

- [**Lemma 90**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-dilation-cone) — Dilations Preserve the Minkowski Cones · `Physicslib4.minkowskiForwardCone_smul` (+1 more)
- [**Theorem 91**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-dilation-causal-automorphism) — Dilations are Causal Automorphisms · `Physicslib4.alexandrovBasis_image_smul`
- [**Theorem 92**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-dilation-not-isometry) — Dilations are Not Isometries · `Physicslib4.minkowskiForm_smul` (+1 more)

**§10.2.5 Isometries and basis-set preservation (p. 54)**

- [**Lemma 93**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-classification) — Isometries Preserve the Causal Classification · `Physicslib4.Spacetime.Isometry.preserves_self` (+3 more)
- [**Lemma 94**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:path-parameter-unique-diff) — Unique Differentials Along a Path · `Physicslib4.Spacetime.Path.uniqueDiffOn_parameterSpace`
- [**Lemma 95**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pushforward-path) — Pushforward of a Path Under an Isometry · `Physicslib4.Spacetime.Isometry.pushforwardPath` (+5 more)
- [**Lemma 96**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-chronology) — Isometries Preserve Chronology · `Physicslib4.Spacetime.Isometry.PreservesFutureOrientation` (+8 more)
- [**Lemma 97**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-basis-sets) — Isometries Preserve Basis Sets · `Physicslib4.Spacetime.Isometry.futureOrientationPreserving` (+8 more)
- [**Lemma 98**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:axiom5-basis-preservation) — Axiom 5 Basis-Set Preservation · `Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent_isBasisSet_smul`

**§10.2.6 Pullback metrics and cross-metric isometries (p. 55)**

- [**Definition 99**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pullback-metric) — Pullback of a Spacetime Metric · `Physicslib4.Spacetime.bilinearPrecomp` (+3 more)
- [**Lemma 100**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-diffeo-linear-equiv) — The Differential of a Diffeomorphism is a Linear Equivalence · `Physicslib4.Spacetime.Diffeo` (+4 more)
- [**Lemma 101**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-symm-cancel-left) — Round-Trip Cancellation: $$d\psi$$ After $$d(\psi^{-1})$$ · `Physicslib4.Spacetime.mfderiv_symm_cancel_left`
- [**Lemma 102**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-symm-cancel-right) — Round-Trip Cancellation: $$d(\psi^{-1})$$ After $$d\psi$$ · `Physicslib4.Spacetime.mfderiv_symm_cancel_right`
- [**Lemma 103**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-inverse-eq-symm) — The Formal Inverse of $$d\psi_x$$ is the Inverse Equivalence · `Physicslib4.Spacetime.inverse_mfderiv_eq_symm` (+2 more)
- [**Lemma 104**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-symm) — The Pullback Metric is Symmetric · `Physicslib4.Spacetime.pullbackVal_symm`
- [**Lemma 105**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-nondegenerate) — The Pullback Metric is Non-Degenerate · `Physicslib4.Spacetime.pullbackVal_nondegenerate`
- [**Lemma 106**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-lorentzian) — The Pullback Metric is Lorentzian · `Physicslib4.Spacetime.pullbackVal_lorentzian`
- [**Lemma 107**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-smooth-in-charts) — The Pullback Metric is a Smooth Section of the Bilinear-Form Bundle · `Physicslib4.Spacetime.pullbackVal_contMDiff`
- [**Theorem 108**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pullback-is-spacetime) — The Pullback of a Spacetime is a Spacetime · `Physicslib4.Spacetime.pullback` (+4 more)
- [**Definition 109**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:preserves-future-orientation) — Two-Sided Preservation of Future Orientation · `Physicslib4.Spacetime.PreservesFutureOrientation` (+1 more)
- [**Lemma 110**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mpullback-vectorField-contMDiff-of-diffeo) — The Pullback of a Bundle-Smooth Vector Field Along a Diffeomorphism is Bundle-Smooth · `Physicslib4.Spacetime.contMDiff_mpullback_vectorField`
- [**Lemma 111**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation-ne-zero) — The Pullback Time Orientation is Nowhere Vanishing · `Physicslib4.Spacetime.mpullback_field_ne_zero`
- [**Lemma 112**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation-timelike) — The Pullback Time Orientation is Everywhere Timelike · `Physicslib4.Spacetime.pullbackVal_mpullback_field_self` (+1 more)
- [**Lemma 113**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation) — Pullback of a Time Orientation · `Physicslib4.Spacetime.pullbackTimeOrientation` (+1 more)
- [**Lemma 114**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-future-pointing-timelike) — Transport of Future-Pointing Timelike Vectors · `Physicslib4.Spacetime.pullbackVal_mpullback_field_apply` (+1 more)
- [**Lemma 115**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-future-pointing-null) — Transport of Future-Pointing Null Vectors · `Physicslib4.Spacetime.isFuturePointing_pullback_iff_of_isNull`
- [**Lemma 116**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-preserves-future-orientation) — The Pullback Preserves the Future Orientation Two-Sidedly · `Physicslib4.Spacetime.pullback_preservesFutureOrientationTwoSided`
- [**Definition 117**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:cross-metric-isometry) — Isometry Between Two Metrics on One Manifold · `Physicslib4.Spacetime.CrossIsometry` (+4 more)
- [**Lemma 118**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-symm) — The Inverse of a Cross-Metric Isometry is a Cross-Metric Isometry · `Physicslib4.Spacetime.CrossIsometry.symm_preserves` (+1 more)
- [**Lemma 119**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-classification) — Cross-Metric Isometries Preserve the Causal Classification · `Physicslib4.Spacetime.CrossIsometry.preserves_self` (+3 more)
- [**Lemma 120**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-tangent) — The Tangent Chain Rule Along a Path · `Physicslib4.Spacetime.mfderivWithin_comp_diffeo` (+1 more)
- [**Lemma 121**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path) — Pushforward of a Path Under a Cross-Metric Isometry · `Physicslib4.Spacetime.pushforwardPath` (+2 more)
- [**Lemma 122**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-causal) — The Pushforward Preserves the Timelike and Causal Conditions · `Physicslib4.Spacetime.CrossIsometry.pushforwardPath_isTimelike` (+1 more)
- [**Lemma 123**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-endpoints) — The Pushforward Transports Endpoints · `Physicslib4.Spacetime.pushforwardPath_isPastEndpoint` (+1 more)
- [**Lemma 124**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-chronology) — Cross-Metric Isometries Transport Chronological Precedence · `Physicslib4.Spacetime.pushforwardPath_isFutureOriented` (+2 more)
- [**Lemma 125**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-chronological-future-image) — Image of the Chronological Future · `Physicslib4.Spacetime.CrossIsometry.chronologicalFuture_image`
- [**Lemma 126**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-chronological-past-image) — Image of the Chronological Past · `Physicslib4.Spacetime.CrossIsometry.chronologicalPast_image`
- [**Lemma 127**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-basis-sets) — Cross-Metric Isometries Preserve Basis Sets · `Physicslib4.Spacetime.CrossIsometry.alexandrovDiamond_image` (+1 more)
- [**Lemma 128**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bijection-generated-topology-homeomorphism) — A Bijection Matching Generating Families is a Homeomorphism · `Physicslib4.continuous_generateFrom_of_preimage_mem` (+4 more)
- [**Lemma 129**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-alexandrov-homeomorphism) — The Pullback Alexandrov Topology · `Physicslib4.Spacetime.pullback_alexandrovBasis_image` (+3 more)
- [**Theorem 130**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pullback-is-lorentzian-spacetime) — The Pullback of a Lorentzian Spacetime is a Lorentzian Spacetime · `Physicslib4.Spacetime.LorentzianSpacetime.pullback_alexandrov_t2` (+3 more)

### §10.3 Haag–Kastler Axioms in Minkowski spacetime (pp. 67–104)

**§10.3 The axioms (p. 67)**

- [**Definition 131**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-algebras) — Axiom 1: Local Algebras · `Physicslib4.AQFT.HaagKastler.LocalNet`
- [**Definition 132**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony) — Axiom 2: Isotony · `Physicslib4.AQFT.HaagKastler.Isotony`

**§10.3.1 The Quasilocal Colimit (p. 68)**

- [**Lemma 133**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-diamonds-isDirected) — Alexandrov Diamonds are Directed under Inclusion · `Physicslib4.AQFT.HaagKastler.Diamond` (+2 more)
- [**Lemma 134**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isotony-directed-system) — The Isotony Family is a Directed System · `Physicslib4.AQFT.HaagKastler.transitionHom` (+1 more)
- [**Lemma 135**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-norm-well-defined) — The Colimit Norm is Well Defined · `Physicslib4.AQFT.HaagKastler.QuasilocalColimit` (+3 more)
- [**Lemma 136**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-common-representatives) — Common Representatives for Two Colimit Elements · `Physicslib4.AQFT.HaagKastler.exists_common_representatives`
- [**Lemma 137**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-norm-axioms) — The Colimit Norm is a Ring Norm and a Normed-Space Norm · `Physicslib4.AQFT.HaagKastler.instNonemptyDiamond` (+3 more)
- [**Lemma 138**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-union-normed-star-algebra) — The Quasilocal Union is a Normed \*-Algebra · `Physicslib4.AQFT.HaagKastler.norm_eq_colimitNorm` (+1 more)
- [**Lemma 139**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-cstar-identity) — The Colimit Satisfies the C\*-Inequality · `Physicslib4.AQFT.HaagKastler.colimitCStarRing`
- [**Definition 140**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completion-standing-hypotheses) — Standing Hypotheses for the Completion Results · `Physicslib4.CStarCompletion`
- [**Definition 141**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completion-star) — The Involution on a Completion · `Physicslib4.instStarCompletion` (+1 more)
- [**Lemma 142**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:star-extends-to-completion) — The Involution Extends to the Completion · `Physicslib4.instStarRingCompletion` (+1 more)
- [**Lemma 143**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-coe-star-alg-hom) — The Completion Coercion as a Bundled \*-Algebra Homomorphism · `Physicslib4.coeStarAlgHom`
- [**Lemma 144**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-cstar-identity) — The C\*-Inequality Passes to the Completion · `Physicslib4.instCStarRingCompletion`
- [**Lemma 145**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-normed-algebra) — The Completion is a Normed $$\mathbb{C}$$-Algebra · `Physicslib4.instNormedAlgebraCompletion`
- [**Lemma 146**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-of-cstar-normed-star-algebra) — The Completion of a C\*-Normed \*-Algebra is a C\*-Algebra · `Physicslib4.instCStarAlgebraCompletion`
- [**Lemma 147**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-completion-cstar) — The Completion of the Quasilocal Colimit is a C\*-Algebra · `Physicslib4.AQFT.HaagKastler.QuasilocalCompletion` (+1 more)
- [**Definition 148**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-algebra) — Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra`
- [**Definition 149**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity) — Axiom 3: Local Commutativity · `Physicslib4.AQFT.HaagKastler.LocalCommutativity`
- [**Definition 150**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-observable) — Quasilocal Observable · `Physicslib4.AQFT.HaagKastler.IsQuasilocalObservable`
- [**Definition 151**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-completeness) — Axiom 4: Quasilocal Completeness · `Physicslib4.AQFT.HaagKastler.ObservableCorrespondence`
- [**Theorem 152**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-algebra-exists) — Existence of a Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.exists_quasilocalAlgebra`
- [**Lemma 153**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embedding) — The Canonical Embeddings into the Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.colimitStarOf` (+1 more)
- [**Lemma 154**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embedding-injective) — The Canonical Embeddings are Injective · `Physicslib4.AQFT.HaagKastler.quasilocalEmbedding_injective`
- [**Lemma 155**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embedding-cocone) — The Canonical Embeddings Form a Cocone · `Physicslib4.AQFT.HaagKastler.quasilocalEmbedding_transitionHom`
- [**Lemma 156**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-union-of-insertions) — The Colimit is the Union of the Images of its Insertions · `Physicslib4.AQFT.HaagKastler.exists_eq_colimitStarOf`
- [**Lemma 157**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embeddings-dense) — The Images of the Canonical Embeddings are Dense · `Physicslib4.AQFT.HaagKastler.dense_iUnion_range_quasilocalEmbedding`
- [**Theorem 158**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-strongly-dense) — Quasilocal Observables are Strongly Dense in the Bicommutant — **the one Chapter 10 node that is not formalised** (see [Formalisation status](#formalisation-status))
- [**Definition 159**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentz-covariance) — Axiom 5: Lorentz Covariance · `Physicslib4.AQFT.HaagKastler.LorentzCovariance`
- [**Definition 160**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:haag-kastler-net) — Haag–Kastler Net · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet`

**§10.3.2 Einstein Causality (p. 86)**

- [**Theorem 161**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:einstein-causality) — Einstein Causality in a Representation · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.einstein_causality` (+1 more)

**§10.3.3 Local von Neumann Algebras (p. 86)**

- [**Definition 162**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann) — Local von Neumann Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localOperators` (+1 more)
- [**Lemma 163**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bicommutant-of-selfadjoint-is-von-neumann) — The Bicommutant of a Self-Adjoint Set is a von Neumann Algebra · `Physicslib4.GNS.vonNeumannOfSelfAdjoint`
- [**Definition 164**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-algebra) — $$R(\mathbf{B})$$ as a von Neumann Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra`
- [**Theorem 165**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-microcausality) — Microcausality at the von Neumann Level · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_subset_centralizer`
- [**Theorem 166**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-isotony) — Isotony of the von Neumann Net · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_mono`
- [**Theorem 167**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-bundled-order) — Bundled von Neumann Microcausality and Isotony · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_le_commutant` (+1 more)
- [**Definition 168**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-net) — The Net of von Neumann Algebras · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.vonNeumannNet`
- [**Theorem 169**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence) — Statistical Independence (Schlieder Property) · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_separating` (+1 more)
- [**Theorem 170**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-bundled) — Statistical Independence, bundled · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_separating`
- [**Theorem 171**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:additive-free-locality) — Additive-Free Locality via the Spacelike Complement · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement`
- [**Theorem 172**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-geometric-covariance) — Geometric Covariance of the von Neumann Net · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.lieConj_image_covLocalVonNeumann` (+1 more)
- [**Theorem 173**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-factor-orbit) — Orbit-Invariance of Factoriality · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.covLocalVonNeumann_isFactor_smul`
- [**Theorem 174**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-covariance-iso) — Geometric Covariance as a von Neumann Algebra Isomorphism · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.covLocalVonNeumannEquiv`

**§10.3.4 Relative Commutants of Nested Local Algebras (p. 88)**

- [**Definition 175**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:relative-commutant) — Relative Commutant of a Nested Pair · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.relativeCommutant`
- [**Theorem 176**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-antitone) — Antitonicity of the Commutant · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.commutant_le_commutant_of_le`
- [**Theorem 177**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-le-right) — Relative Commutant Lies in the Larger Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.relativeCommutant_le_right`
- [**Theorem 178**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-coe-commutant) — Relative Commutant Commutes with the Smaller Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.relativeCommutant_coe_subset_commutant`
- [**Theorem 179**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-center) — Relative Commutant Contains the Centre · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.center_le_relativeCommutant`
- [**Definition 180**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-inclusion) — Irreducible Inclusion · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsIrreducibleInclusion`
- [**Theorem 181**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-inclusion-factor) — An Irreducible Inclusion has Factor Ambient · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.isFactor_of_isIrreducibleInclusion`
- [**Theorem 182**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:self-inclusion-factor) — Self-Inclusion is Irreducible iff Factor · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.isIrreducibleInclusion_self_iff_isFactor`

**§10.3.5 Irreducibility and Schur's Lemma (p. 90)**

- [**Definition 183**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-representation) — Irreducible Representation · `Physicslib4.GNS.IsIrreducible`
- [**Theorem 184**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:schur-lemma) — Topological Schur Lemma · `Physicslib4.GNS.eq_smul_one_of_commute_of_cyclic`
- [**Theorem 185**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-scalar-iff) — Commutant Scalar iff Proportional Coefficient · `Physicslib4.GNS.isScalar_iff_coeff_proportional`
- [**Definition 186**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pure-state) — Pure State · `Physicslib4.GNS.IsPure`
- [**Theorem 187**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-implies-irreducible) — Pure Implies Irreducible · `Physicslib4.GNS.isIrreducible_of_isPure`
- [**Theorem 188**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-form-bound) — The GNS Radon–Nikodym Form is Bounded · `Physicslib4.GNS.gns_form_norm_le` (+1 more)
- [**Theorem 189**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-radon-nikodym-operator) — The GNS Radon–Nikodym Operator · `Physicslib4.GNS.rnOp` (+3 more)
- [**Theorem 190**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible) — Pure $$\iff$$ Irreducible · `Physicslib4.GNS.isPure_iff_isIrreducible`
- [**Theorem 191**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-factor) — An Irreducible Representation Generates a Factor · `Physicslib4.GNS.center_gnsVonNeumann_eq_of_isIrreducible`
- [**Theorem 192**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-generates-all) — Irreducibility $$\iff$$ Generating $$\mathcal{B}(H)$$ · `Physicslib4.GNS.isIrreducible_iff_gnsVonNeumann_eq_univ` (+1 more)
- [**Theorem 193**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-generates-all-bundled) — Bundled Density Form of Irreducibility · `Physicslib4.GNS.coe_gnsVonNeumannAlgebra_eq_univ_of_isIrreducible` (+1 more)
- [**Theorem 194**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-factor) — The GNS Representation of a Pure State is a Factor · `Physicslib4.GNS.exists_gns_factor_of_isPure`
- [**Theorem 195**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-generates-all) — The GNS Representation of a Pure State Generates $$\mathcal{B}(H)$$ · `Physicslib4.GNS.exists_gns_generates_all_of_isPure`
- [**Theorem 196**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:norm-positive-functional) — Norm of a Positive Functional · `Physicslib4.GNS.norm_eq_re_apply_one_of_positive`
- [**Definition 197**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:extreme-state) — Extreme Point of the State Space · `Physicslib4.GNS.State.IsExtremePoint`
- [**Theorem 198**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme) — Pure $$\iff$$ Extreme Point · `Physicslib4.GNS.isPure_iff_isExtremePoint`
- [**Theorem 199**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-space-convex-bridge) — State-Space Convexity and the Extreme-Point Bridge · `Physicslib4.GNS.convex_stateSpace` (+1 more)
- [**Definition 200**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:state-pullback) — Pullback of a State · `Physicslib4.GNS.State.comp`
- [**Theorem 201**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-pullback-functorial) — Functoriality of the State Pullback · `Physicslib4.GNS.State.comp_id` (+1 more)
- [**Theorem 202**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-pullback-invariant) — Purity is Invariant under a \*-Isomorphism · `Physicslib4.GNS.isPure_comp_iff`
- [**Theorem 203**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-space-weak-compact) — Weak-\* Compactness of the State Space · `Physicslib4.GNS.isCompact_weakStateSet`
- [**Theorem 204**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme-quasilocal) — Pure $$\iff$$ Extreme Point on the Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.pure_iff_extreme`
- [**Theorem 205**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible-quasilocal) — Pure $$\iff$$ Irreducible GNS on the Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.exists_gns_pure_iff_irreducible`

**§10.3.6 Unitary Equivalence and Superselection (p. 93)**

- [**Definition 206**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:unitary-equivalence) — Unitary Equivalence of Representations · `Physicslib4.GNS.UnitaryEquiv`
- [**Theorem 207**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:unitary-equiv-invariants) — Irreducibility and Factoriality are Unitary Invariants · `Physicslib4.GNS.UnitaryEquiv.isIrreducible_iff` (+1 more)

**§10.3.7 GNS Covariance (p. 94)**

- [**Lemma 208**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cyclic-pullback-surjective) — Cyclicity pulls back along a surjective \*-homomorphism · `Physicslib4.GNS.isCyclicVector_comp_of_surjective`
- [**Theorem 209**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance) — GNS covariance under a \*-isomorphism · `Physicslib4.GNS.exists_unitary_of_gns_comp`
- [**Theorem 210**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-unitary-equiv) — The GNS representation of a pullback state · `Physicslib4.GNS.unitaryEquiv_comp_of_gns`
- [**Lemma 211**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-image-invariants) — Pullback along a surjection preserves the image algebra · `Physicslib4.GNS.range_comp_of_surjective` (+2 more)
- [**Theorem 212**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-sector-transport) — Superselection type transports along a \*-isomorphism · `Physicslib4.GNS.isIrreducible_iff_of_gns_comp` (+1 more)
- [**Theorem 213**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-local) — GNS covariance for local algebras · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.unitaryEquiv_gns_covEquiv` (+2 more)

**§10.3.8 Disjointness and Quasi-Equivalence (p. 95)**

- [**Definition 214**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:disjoint-representations) — Disjoint Representations · `Physicslib4.GNS.AreDisjoint`
- [**Definition 215**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasi-equivalence) — Quasi-Equivalence of Representations · `Physicslib4.GNS.QuasiEquiv`
- [**Theorem 216**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-dichotomy) — Schur's Lemma and the Irreducible Dichotomy · `Physicslib4.GNS.UnitaryEquiv.of_intertwines_of_isIrreducible` (+1 more)
- [**Lemma 217**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:schur-multiplicity) — Schur Multiplicity · `Physicslib4.GNS.eq_smul_of_intertwines_of_isIrreducible`
- [**Lemma 218**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:endomorphism-scalar) — Endomorphism Algebra of an Irreducible Representation · `Physicslib4.GNS.intertwines_self_iff_isScalar`
- [**Theorem 219**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-von-neumann) — The commutant (self-intertwiner) von Neumann algebra · `Physicslib4.GNS.commutantVonNeumann` (+2 more)
- [**Theorem 220**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:double-commutant-duality) — Double-Commutant Duality · `Physicslib4.GNS.commutant_gnsVonNeumannAlgebra` (+1 more)
- [**Theorem 221**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-factor-duality) — A Factor and its Commutant; Triviality Duality · `Physicslib4.GNS.isFactor_gnsVonNeumann_iff_isFactor_commutant` (+1 more)
- [**Lemma 222**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-abelian-self-commuting) — Abelian $$\iff$$ Self-Commuting · `Physicslib4.GNS.isAbelian_iff_le_commutant`
- [**Definition 223**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-center) — Centre of a von Neumann algebra · `Physicslib4.GNS.vonNeumannCenter`
- [**Lemma 224**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-inter-is-von-neumann) — The centre is a von Neumann algebra · `Physicslib4.GNS.bicommutant_inter_commutant_eq`
- [**Lemma 225**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-inter-general) — The intersection of two von Neumann algebras is a von Neumann algebra · `Physicslib4.GNS.bicommutant_inter_eq`
- [**Theorem 226**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-center-abelian) — The centre of a von Neumann algebra is abelian · `Physicslib4.GNS.vonNeumannCenter_isAbelian`
- [**Lemma 227**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-center-eq-self-iff-abelian) — $$R$$ is abelian iff it equals its centre · `Physicslib4.GNS.vonNeumannCenter_eq_self_iff_isAbelian`
- [**Theorem 228**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:factor-abelian-iff-scalars) — A factor is abelian iff it is the scalars · `Physicslib4.GNS.isAbelian_iff_eq_scalars_of_isFactor`
- [**Theorem 229**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:center-eq-commutant-center) — A von Neumann algebra and its commutant share a centre · `Physicslib4.GNS.vonNeumannCenter_eq_commutant`
- [**Theorem 230**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:factor-iff-center-scalars) — A von Neumann algebra is a factor iff its centre is the scalars · `Physicslib4.GNS.isFactor_iff_center_eq_scalars`
- [**Theorem 231**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-state-dichotomy) — The Pure-State Dichotomy · `Physicslib4.GNS.exists_gns_areDisjoint_or_unitaryEquiv_of_isPure`

**§10.3.9 Direct Sums, Amplification, and Reducibility (p. 98)**

- [**Definition 232**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:direct-sum-representation) — Direct-Sum Representation · `Physicslib4.GNS.directSum`
- [**Theorem 233**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:direct-sum-subrepresentation) — Subrepresentations and Commutant of a Direct Sum · `Physicslib4.GNS.intertwines_single` (+1 more)
- [**Definition 234**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:amplification) — Amplification · `Physicslib4.GNS.amplification`
- [**Theorem 235**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:direct-sum-reducible) — Reducibility of a Direct Sum · `Physicslib4.GNS.not_isIrreducible_directSum`

**§10.3.10 Covariant States and the Covariance Action (p. 99)**

- [**Definition 236**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-state-family) — Covariant Family of Local States · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsCovariantFamily`
- [**Lemma 237**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:covariant-state-family-compose) — Composition of Covariance · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsCovariantFamily.comp`
- [**Definition 238**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-lift) — Quasilocal Covariance Automorphism · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.QuasilocalLift`
- [**Lemma 239**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-lift-unique) — Uniqueness of the Quasilocal Lift · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.QuasilocalLift.unique`
- [**Theorem 240**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-lift-exists) — Existence of the Quasilocal Lift · `Physicslib4.AQFT.HaagKastler.nonempty_quasilocalLift`
- [**Theorem 241**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-lift-trivial) — Existence for the Trivial Net · `Physicslib4.AQFT.HaagKastler.nonempty_trivialQuasilocalLift`
- [**Definition 242**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-quasilocal-algebra) — Covariant Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra`
- [**Lemma 243**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-action-coherence) — Group-Action Coherence of the Covariance Automorphism · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.action_one` (+1 more)
- [**Definition 244**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:invariant-state) — Invariant State · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.IsInvariantState`
- [**Theorem 245**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:invariant-state-gns-unitary) — GNS Unitary Implementation of an Invariant State · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.IsInvariantState.exists_gns_unitary`
- [**Theorem 246**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-covariant-representation) — Irreducible Covariant Representation of a Pure Invariant State · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.IsInvariantState.exists_gns_irreducible_covariant`
- [**Definition 247**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:positive-energy) — Positive Energy (bounded-generator scaffold) · `Physicslib4.AQFT.IsPositiveEnergy`
- [**Theorem 248**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:positive-energy-api) — Positive-Energy API · `Physicslib4.AQFT.isPositiveEnergy_const_refl` (+3 more)
- [**Definition 249**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:vacuum-state) — Vacuum State (generator-parameterised scaffold) · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.IsVacuumState`
- [**Theorem 250**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:vacuum-no-stone) — No-Stone Consequences of a Vacuum State · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.IsVacuumState.invariant` (+1 more)
- [**Definition 251**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-timelike-translation) — Future-Timelike Translation Subgroup · `Physicslib4.AQFT.HaagKastler.translationSub` (+3 more)
- [**Definition 252**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:vacuum-state-concrete) — Vacuum State with the Concrete Spectrum Condition · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.IsVacuumStateConcrete`
- [**Theorem 253**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:purity-covariance-invariant) — Purity is Covariance-Invariant · `Physicslib4.GNS.isPure_precomp_iff` (+1 more)
- [**Theorem 254**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-quasilocal-action) — GNS covariance along the quasilocal action · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.unitaryEquiv_gns_action` (+2 more)

**§10.3.11 The Separating Vector of a Faithful State (p. 102)**

- [**Theorem 255**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:separating-faithful) — Separating Vector of a Faithful State · `Physicslib4.GNS.separating_of_faithful` (+1 more)

**§10.3.12 The KMS Condition and Thermal Equilibrium (p. 102)**

- [**Definition 256**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:one-parameter-aut) — One-Parameter Automorphism Group · `Physicslib4.AQFT.IsOneParameterAut`
- [**Definition 257**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state) — KMS State · `Physicslib4.AQFT.IsKMSState`
- [**Theorem 258**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-convex) — The KMS State Set is Convex · `Physicslib4.AQFT.IsKMSState.convexCombo`
- [**Lemma 259**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:kms-correlation-one) — Boundary Coincidence for $$a = 1$$ · `Physicslib4.AQFT.IsKMSState.correlationOne`
- [**Definition 260**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:strip-liouville) — Strip-Liouville Principle · `Physicslib4.AQFT.StripLiouville`
- [**Theorem 261**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:strip-periodic-extension) — $$i\beta$$-Periodic Entire Extension (Strip Schwarz Reflection) · `Physicslib4.exists_bounded_entire_extension_of_strip_periodic`
- [**Theorem 262**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:strip-liouville-pos) — Strip-Liouville Holds for $$\beta > 0$$ · `Physicslib4.AQFT.stripLiouville_of_pos`
- [**Theorem 263**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-invariance) — KMS States are Invariant · `Physicslib4.AQFT.IsKMSState.invariant_of_pos`
- [**Theorem 264**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:strip-uniqueness) — Uniqueness on the Strip from Boundary Values · `Physicslib4.eqOn_strip_of_eq_boundary`
- [**Theorem 265**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-correlation-unique) — Uniqueness of the KMS Correlation Function · `Physicslib4.AQFT.IsKMSState.correlation_eqOn`

**§10.3.13 KMS States for the Covariance Flow (p. 104)**

- [**Definition 266**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:flow-aut-covariance) — Covariance-Flow Automorphism Family · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.flowAut`
- [**Lemma 267**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:one-parameter-aut-flow-covariance) — A Lorentz One-Parameter Subgroup Induces a One-Parameter Group · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.isOneParameterAut_flowAut`
- [**Definition 268**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state-for-flow-covariance) — KMS State for the Covariance Flow · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.IsKMSStateForFlow`
- [**Theorem 269**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-convex-for-flow-covariance) — Convexity of the Covariance-Flow KMS States · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.IsKMSStateForFlow.convexCombo`
- [**Definition 270**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:ground-state-for-flow-covariance) — Ground State for a Covariance Flow · `Physicslib4.AQFT.HaagKastler.CovariantQuasilocalAlgebra.IsGroundStateForFlow` (+2 more)

### §10.4 Haag–Kastler Axioms in curved spacetime (pp. 105–114)

**§10.4 The axioms (p. 105)**

- [**Definition 271**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-algebras-in-curved-spacetime) — Axiom 1: Local Algebras · `Physicslib4.AQFT.HaagKastlerCurved.LocalNet`
- [**Definition 272**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony-in-curved-spacetime) — Axiom 2: Isotony · `Physicslib4.AQFT.HaagKastlerCurved.Isotony`
- [**Definition 273**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity-in-curved-spacetime) — Axiom 3: Local Commutativity · `Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity`
- [**Definition 274**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-observable) — Local Observable · `Physicslib4.AQFT.HaagKastlerCurved.IsLocalObservable`
- [**Definition 275**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-completeness-in-curved-spacetime) — Axiom 4: Local Completeness · `Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebra`
- [**Definition 276**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isometric-covariance-in-curved-spacetime) — Axiom 5: Isometric Covariance · `Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance` *(implemented via the explicitly orientation-preserving subgroup — see [Formalisation status](#formalisation-status))*
- [**Definition 277**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:haag-kastler-net-in-curved-spacetime) — Haag–Kastler Net in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet`

**§10.4.1 Einstein Causality in Curved Spacetime (p. 107)**

- [**Theorem 278**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:einstein-causality-in-curved-spacetime) — Einstein Causality in a Representation (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.einstein_causality` (+1 more)

**§10.4.2 Local von Neumann Algebras in Curved Spacetime (p. 107)**

- [**Definition 279**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-in-curved-spacetime) — Local von Neumann Algebra in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localOperators` (+1 more)
- [**Definition 280**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-algebra-in-curved-spacetime) — $$R(\mathbf{B}')$$ as a von Neumann Algebra (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra`
- [**Theorem 281**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-microcausality-in-curved-spacetime) — Microcausality at the von Neumann Level (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_subset_centralizer`
- [**Theorem 282**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-isotony-in-curved-spacetime) — Isotony of the von Neumann Net (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_mono`
- [**Theorem 283**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-bundled-order-in-curved-spacetime) — Bundled von Neumann Microcausality and Isotony (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_le_commutant` (+1 more)
- [**Definition 284**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-net-in-curved-spacetime) — The Net of von Neumann Algebras in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.vonNeumannNet`
- [**Theorem 285**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-in-curved-spacetime) — Statistical Independence (Schlieder Property) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_separating` (+1 more)
- [**Theorem 286**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-bundled-in-curved-spacetime) — Statistical Independence, bundled (curved spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_separating`
- [**Theorem 287**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:additive-free-locality-in-curved-spacetime) — Additive-Free Locality via the Spacelike Complement (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric`
- [**Theorem 288**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-geometric-covariance-in-curved-spacetime) — Geometric Covariance of the von Neumann Net (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.lieConj_image_localVonNeumann` (+1 more)
- [**Theorem 289**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-factor-orbit-in-curved-spacetime) — Orbit-Invariance of Factoriality (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_isFactor_smul`
- [**Theorem 290**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-covariance-iso-in-curved-spacetime) — Geometric Covariance as a von Neumann Algebra Isomorphism (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannEquiv`

**§10.4.3 Relative Commutants of Nested Local Algebras in Curved Spacetime (p. 109)**

- [**Definition 291**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:relative-commutant-in-curved-spacetime) — Relative Commutant of a Nested Pair (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant`
- [**Theorem 292**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-le-right-in-curved-spacetime) — Relative Commutant Lies in the Larger Algebra (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant_le_right`
- [**Theorem 293**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-coe-commutant-in-curved-spacetime) — Relative Commutant Commutes with the Smaller Algebra (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant_coe_subset_commutant`
- [**Theorem 294**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-center-in-curved-spacetime) — Relative Commutant Contains the Centre (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.center_le_relativeCommutant`
- [**Definition 295**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-inclusion-in-curved-spacetime) — Irreducible Inclusion (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsIrreducibleInclusion`
- [**Theorem 296**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-inclusion-factor-in-curved-spacetime) — An Irreducible Inclusion has Factor Ambient (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isFactor_of_isIrreducibleInclusion`
- [**Theorem 297**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:self-inclusion-factor-in-curved-spacetime) — Self-Inclusion is Irreducible iff Factor (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isIrreducibleInclusion_self_iff_isFactor`
- [**Theorem 298**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:abelian-local-von-neumann-in-curved-spacetime) — Abelian Local von Neumann Algebras (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_center_isAbelian` (+1 more)
- [**Theorem 299**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:center-duality-local-von-neumann-in-curved-spacetime) — Centre Duality for Local von Neumann Algebras (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_center_eq_commutant` (+1 more)

**§10.4.4 Purity of States on Local Algebras in Curved Spacetime (p. 110)**

- [**Theorem 300**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme-in-curved-spacetime) — Pure $$\iff$$ Extreme Point on a Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.pure_iff_extreme`
- [**Theorem 301**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible-in-curved-spacetime) — Pure $$\iff$$ Irreducible GNS on a Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_pure_iff_irreducible`
- [**Theorem 302**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-factor-generates-in-curved-spacetime) — Pure GNS on a Local Algebra is a Factor Generating $$\mathcal{B}(H)$$ · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_factor_of_isPure` (+1 more)
- [**Theorem 303**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-dichotomy-in-curved-spacetime) — The Irreducible Dichotomy for a Curved Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.areDisjoint_or_unitaryEquiv_of_isIrreducible`
- [**Theorem 304**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-local-in-curved-spacetime) — GNS covariance for curved local algebras · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.unitaryEquiv_gns_covEquiv` (+2 more)

**§10.4.5 Covariant States in Curved Spacetime (p. 111)**

- [**Definition 305**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-state-family-in-curved-spacetime) — Covariant Family of Local States in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsCovariantFamily`
- [**Lemma 306**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:covariant-state-family-compose-in-curved-spacetime) — Composition of Covariance in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsCovariantFamily.comp`

**§10.4.6 The Stabiliser GNS Unitary in Curved Spacetime (p. 112)**

- [**Definition 307**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:stabilizer-action-in-curved-spacetime) — Stabiliser Action on a Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.stabAut`
- [**Lemma 308**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:stabilizer-action-laws-in-curved-spacetime) — The Stabiliser Action is a Group Action · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.stabAut_one` (+1 more)
- [**Theorem 309**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-unitary-stabilizer-in-curved-spacetime) — GNS Unitary Representation of the Stabiliser · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_unitary_stabilizer`
- [**Theorem 310**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-unitary-stabilizer-strongly-continuous-in-curved-spacetime) — Strongly Continuous Stabiliser GNS Unitary · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_unitary_stabilizer_strongContinuous`
- [**Theorem 311**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-covariant-representation-in-curved-spacetime) — Irreducible Covariant Representation of a Pure Invariant State (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_irreducible_covariant_stabilizer`
- [**Theorem 312**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:purity-covariance-invariant-in-curved-spacetime) — Purity is Invariant under the Stabiliser Action · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isPure_precomp_stabAut_iff`
- [**Theorem 313**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-stabilizer-action) — GNS covariance along the stabiliser action · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.unitaryEquiv_gns_stabAut` (+2 more)

**§10.4.7 KMS States for a Killing Flow (p. 113)**

- [**Definition 314**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:flow-aut-in-curved-spacetime) — Killing-Flow Automorphism Family · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.flowAut`
- [**Lemma 315**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:one-parameter-aut-flow-in-curved-spacetime) — A Killing Flow Induces a One-Parameter Group · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isOneParameterAut_flowAut`
- [**Definition 316**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state-for-flow-in-curved-spacetime) — KMS State for a Killing Flow · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow`
- [**Theorem 317**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-thermal-representation-in-curved-spacetime) — The Killing-Flow KMS Thermal Representation · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow.exists_gns_unitary_strongContinuous`
- [**Theorem 318**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-convex-for-flow-in-curved-spacetime) — Convexity of the Killing-Flow KMS States · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow.convexCombo`
- [**Definition 319**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:ground-state-for-flow-in-curved-spacetime) — Ground State for a Killing Flow · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsGroundStateForFlow` (+2 more)

### §10.5 General Covariance: Nets on Pullback-Related Metrics (pp. 114–116)

**§10.5 General Covariance: Nets on Pullback-Related Metrics (p. 114)**

- [**Definition 320**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:net-equivalence-in-curved-spacetime) — Equivalence of Haag–Kastler Nets · `Physicslib4.AQFT.HaagKastlerCurved.NetEquivalence`
- [**Definition 321**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:general-covariance-in-curved-spacetime) — General Covariance · `Physicslib4.AQFT.HaagKastlerCurved.NetTheory` (+4 more)

### The axioms at a glance

Axiom 6 (Primitivity) from the original 1964 Haag–Kastler paper is not carried into the sharpened axiom set — see Chapter 8 for the discussion of why it is dropped. The five sharpened axioms in each setting, bundled together as a `HaagKastlerNet`, are what is actually formalised.

**Minkowski spacetime** — bundled as `Physicslib4.AQFT.HaagKastler.HaagKastlerNet` (Definition 160):

| Axiom | Node | Lean |
|---|---|---|
| 1. Local Algebras | Definition 131 | `Physicslib4.AQFT.HaagKastler.LocalNet` |
| 2. Isotony | Definition 132 | `Physicslib4.AQFT.HaagKastler.Isotony` |
| 3. Local Commutativity | Definition 149 | `Physicslib4.AQFT.HaagKastler.LocalCommutativity` |
| 4. Quasilocal Completeness | Definition 151 | `Physicslib4.AQFT.HaagKastler.ObservableCorrespondence` |
| 5. Lorentz Covariance | Definition 159 | `Physicslib4.AQFT.HaagKastler.LorentzCovariance` |

**Curved spacetime** — bundled as `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet` (Definition 277):

| Axiom | Node | Lean |
|---|---|---|
| 1. Local Algebras | Definition 271 | `Physicslib4.AQFT.HaagKastlerCurved.LocalNet` |
| 2. Isotony | Definition 272 | `Physicslib4.AQFT.HaagKastlerCurved.Isotony` |
| 3. Local Commutativity | Definition 273 | `Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity` |
| 4. Local Completeness | Definition 275 | `Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebra` |
| 5. Isometric Covariance | Definition 276 | `Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance` |

**General Covariance (Definition 321, `Physicslib4.AQFT.HaagKastlerCurved.IsGenerallyCovariant`)** is deliberately *not* a sixth axiom. Axioms 1–5 each constrain a single net over a single fixed spacetime, whereas general covariance relates two nets over two spacetimes; it is therefore a property of the section $$L \mapsto \mathfrak{U}_L$$ assigning a net to every Lorentzian spacetime, not an extra field of the net structure.

Two changes to the axioms are worth calling out for readers coming from an earlier version of this blueprint:

- **Isotony now supplies its embeddings as data.** Axiom 2 (Definitions 132 and 272) fixes the family $$i_{\mathbf{B}_1 \mathbf{B}_2}$$ together with identity and composition laws, making $$\mathbf{B} \mapsto \mathfrak{U}(\mathbf{B})$$ a functor on the inclusion order. Axiom 3 consumes that family rather than choosing witnesses of its own. This is what makes the quasilocal colimit well posed in Minkowski spacetime, and it removes the coherence side-hypotheses that curved-spacetime statements about nested regions previously had to carry.
- **Axiom 4 has been split.** The mathematical claim that a quasilocal algebra exists is now Theorem 152 (`Physicslib4.AQFT.HaagKastler.exists_quasilocalAlgebra`), proved from the colimit-and-completion chain; what remains as Axiom 4 (Definition 151) is the bridge principle relating physical observables to quasilocal ones, which has — by design — no mathematical consumers.

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

