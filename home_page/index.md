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

**Chapters 1–9 are mathematical background and are not themselves formalised in Lean.** They motivate and analyse each of the original Haag–Kastler axioms in turn, and then generalise them to curved spacetime. Along the way they cite twelve supporting results, numbered 1 through 12; these are background facts (Gelfand–Naimark, the Bounded Linear Transformation Theorem, the existence of a Lorentz metric, and so on), quoted where needed rather than proved or formalised here.

**Chapter 10 collects the formalisation-ready content, and it is the content of Chapter 10 that is formalised in Lean.** Its declarations are numbered consecutively, running from Definition 13 through Definition 321, and comprise **309 declarations in total: 90 definitions, 115 theorems, and 104 lemmas.** Chapter 10 is divided into five top-level sections, §10.1 through §10.5.

At a glance, these 309 declarations break down by top-level section as follows:

| Section | Topic | Pages | Definitions | Theorems | Lemmas | Total |
|---|---|---|---|---|---|---|
| §10.1 | GNS Construction | 28–37 | 2 | 1 | 3 | 6 |
| §10.2 | Spacetime and causal structure | 37–67 | 30 | 16 | 66 | 112 |
| §10.3 | Haag–Kastler Axioms (Minkowski) | 67–104 | 39 | 69 | 32 | 140 |
| §10.4 | Haag–Kastler Axioms (curved spacetime) | 105–114 | 17 | 29 | 3 | 49 |
| §10.5 | General Covariance | 114–116 | 2 | 0 | 0 | 2 |
| **Total** | | | **90** | **115** | **104** | **309** |

### Known divergences and gaps

Three places where the blueprint and the Lean development are deliberately not in step are flagged in the text itself, and are repeated here so that they are not discovered by surprise:

- **The geodesic clause of a trip is a placeholder (Definitions 42–43).** In Lean, `Physicslib4.Spacetime.IsGeodesic` is defined to be `True`, so it imposes no constraint. A faithful geodesic condition needs the Levi-Civita connection of the metric, which the pinned version of Mathlib does not provide. The formalised (causal) trip segments are therefore future-oriented timelike (respectively causal) curves with the correct past and future endpoints; the endpoint, timelike/causal, and future-orientation content is faithful, and only the geodesic property is unenforced.
- **Theorem 158 is stated from the literature and not formalised.** That quasilocal observables are strongly dense in the bicommutant is the von Neumann density theorem, which Mathlib does not have. The blueprint records exactly what is missing: the strong operator topology itself *is* available, as `PointwiseConvergenceCLM`, so the statement is phraseable today; what is absent is the density theorem (and with it Kaplansky), which is a development of its own.
- **Axiom 5 in curved spacetime is implemented with an explicitly orientation-preserving subgroup.** "Isometries connected to the identity" and "identity-component isometries preserving the future orientation" describe the same group, but the inclusion of the former in the latter rests on a Myers–Steenrod-type rigidity result not yet in Mathlib, so the Lean development intersects the identity component with the orientation-preserving subgroup. This is an implementation choice and does not alter the mathematical content of the axiom.

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
- **Chapter 9 (Haag–Kastler Axioms in Curved Spacetime, p. 21)** generalises the Haag–Kastler axioms from Minkowski spacetime to curved (Lorentzian) spacetime. It first pins down a precise definition of Lorentzian spacetime and its Alexandrov topology, then shows—via a Schwarzschild black-hole counterexample—that a quasilocal algebra need not exist on a generic Lorentzian spacetime, so Local Commutativity and the local-algebra axiom must be restated relative to a common containing region rather than a global algebra. The final section replaces Lorentz covariance with covariance under identity-component isometries, together with the Myers–Steenrod formalisation remark noted above.

### Chapter 10: the formalisation-ready content

Chapter 10 restates the axioms in a form amenable to auto-formalisation and proves everything they depend on. Its five top-level sections are described below in order; the complete, itemised list of all 309 numbered declarations follows in [What is Being Formalised](#what-is-being-formalised).

- **§10.1 GNS Construction Details (pp. 28–37).** States and proves the GNS Construction Theorem (Theorem 15) in full detail—construction of the GNS Hilbert space, the \*-representation, the cyclic vector, faithfulness of the representation for a faithful state, and uniqueness up to unitary equivalence—since both the theorem and specific steps of its proof are used in the axioms that follow. The two supporting objects are the state (Definition 13) and the cyclic vector (Definition 14); the auxiliary results are the Cauchy–Schwarz inequality for positive functionals (Lemma 16) and the two equivalent descriptions of the GNS left ideal $$\mathcal{N}$$, which is shown to be a closed linear subspace (Lemmas 17–18). §10.1.3 is a prose summary and carries no numbered items.

- **§10.2 Spacetime (pp. 37–67).** The largest section by declaration count (112 items, Definitions 19–130), building the entire causal and topological apparatus the axioms are indexed on. It proceeds in seven layers.
  - *Spacetime, tangent-vector causality, curves, and trips (pp. 37–44, items 19–50).* Gives precise definitions of spacetime (Definition 19) and standard Minkowski spacetime (Definition 20); classifies tangent vectors as timelike, spacelike, or null (Definition 21) and proves the trichotomy (Lemma 22), the reverse Cauchy–Schwarz and reverse triangle inequalities for timelike vectors (Lemmas 23–24), and the cone geometry—orientation of pointing vectors, the sign lemma, definiteness of the spacelike complement of a timelike vector, and convexity of the cones (Lemmas 27–30)—alongside time orientations (Definition 25) and future- and past-pointing vectors (Definition 26). Then paths, curves, and oriented curves are defined as equivalence classes of paths up to reparametrisation (Definitions 31–36), with causal type and future/past orientation each shown well-defined on the quotient (Theorems 35 and 37) and a forgetful projection from oriented to unoriented curves (Theorem 38). Endpoints (Definition 39) come with two point-set lemmas—an extremal parameter lies in the frontier, and two endpoints force a compact parameter interval (Lemmas 40–41)—followed by trips and causal trips (Definitions 42–43, subject to the geodesic-placeholder caveat above), transitivity of chronological and causal precedence (Theorem 44), the causality condition (Definition 45) and the resulting strict partial order (Theorem 46), chronological and causal futures and pasts (Definitions 47–48), and their basic inclusion and monotonicity properties (Lemmas 49–50).
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

Only the content of Chapter 10 is formalised in Lean. Its declarations are numbered consecutively from Definition 13 through Definition 321 — 309 in total — and every one of them is listed below, in numerical order, under the blueprint subsection in which it appears. Listing them exhaustively and in the blueprint's own order is deliberate: it makes the list checkable line by line against the PDF. The two exceptions to "formalised" are noted in place.

The lower numbers, 1 through 12, label supporting theorems and definitions introduced along the way in the motivational Chapters 4–9. These are background results, cited when needed, and are **not** formalised in Lean: C\*-spectrum invariance under inclusion (Theorem 1), uniqueness of the C\*-norm (Theorem 2), strong density of unital \*-algebras (Theorem 3), the Bounded Linear Transformation Theorem (Theorem 4), Gelfand–Naimark (Theorem 5), the rarity of primitive abelian C\*-algebras (Lemma 6), existence of a Lorentz metric (Theorem 7), causal convexity and strong causality (Definitions 8–9), properties of the Alexandrov topology (Theorem 10), Lorentzian spacetime (Definition 11), and the local observable (Definition 12).

### §10.1 GNS Construction (pp. 28–37)

**§10.1.1 GNS Construction Theorem (p. 28)**

- **Definition 13** — State
- **Definition 14** — Cyclic Vector
- **Theorem 15** — GNS Construction Theorem: Hilbert space, \*-representation, cyclic vector, faithfulness, and uniqueness up to unitary equivalence

**§10.1.2 Auxiliary Results Used in the Proof (p. 34)**

- **Lemma 16** — Cauchy–Schwarz inequality for positive functionals
- **Lemma 17** — The two descriptions of the GNS left ideal $$\mathcal{N}$$ agree
- **Lemma 18** — $$\mathcal{N}$$ is a closed linear subspace

### §10.2 Spacetime and causal structure (pp. 37–67)

**§10.2 opening run: spacetime, tangent-vector causality, curves, trips, futures and pasts (p. 37)**

- **Definition 19** — Spacetime
- **Definition 20** — Standard Minkowski Spacetime
- **Definition 21** — Timelike, Spacelike, or Null Vectors
- **Lemma 22** — Causal Classification (trichotomy)
- **Lemma 23** — Reverse Cauchy–Schwarz for Timelike Vectors
- **Lemma 24** — Timelike Cone Convexity and Reverse Triangle Inequality
- **Definition 25** — Time Orientation
- **Definition 26** — Future and Past Pointing Vectors
- **Lemma 27** — Orientation of Pointing Vectors
- **Lemma 28** — Sign Lemma for the Future Cone
- **Lemma 29** — Definiteness of the Spacelike Complement
- **Lemma 30** — Convexity of the Future Cone
- **Definition 31** — Paths
- **Definition 32** — Curves
- **Definition 33** — Timelike and Causal Smooth Curves
- **Definition 34** — Future and Past Oriented Smooth Curves
- **Theorem 35** — Reparametrisation-Invariance of the Causal Type
- **Definition 36** — Oriented Smooth Curve
- **Theorem 37** — Reparametrisation-Invariance of Orientation
- **Theorem 38** — The Forgetful Projection of Oriented Curves
- **Definition 39** — Endpoints
- **Lemma 40** — An extremal parameter lies in the frontier
- **Lemma 41** — Two endpoints force a compact parameter interval
- **Definition 42** — Trip *(geodesic clause is a placeholder in Lean; see above)*
- **Definition 43** — Causal Trip *(geodesic clause is a placeholder in Lean; see above)*
- **Theorem 44** — Transitivity of chronological and causal precedence
- **Definition 45** — No Closed Causal Curve (the Causality Condition)
- **Theorem 46** — Irreflexivity and Antisymmetry under Causality
- **Definition 47** — Chronological Future and Chronological Past
- **Definition 48** — Causal Future and Causal Past
- **Lemma 49** — Chronological Precedence Implies Causal Precedence
- **Lemma 50** — Monotonicity of Futures and Pasts

**§10.2.1 Causal diamonds, spacelike complement, and causal closure (p. 44)**

- **Definition 51** — Causal and chronological diamonds
- **Lemma 52** — Structural properties of the causal diamond
- **Theorem 53** — Chronological diamonds inside causal diamonds; the Alexandrov basis is exactly the chronological diamonds
- **Definition 54** — Spacelike Related
- **Definition 55** — Completely Spacelike
- **Lemma 56** — Symmetry of Spacelike Separation
- **Lemma 57** — Structural Properties of Complete Spacelike Separation
- **Definition 58** — Spacelike Complement of a Region
- **Lemma 59** — Order Structure of the Spacelike Complement (antitone, extensive on the double complement, triple-complement collapse — the Galois connection of the spacelike-separation relation)
- **Definition 60** — Causal closure operator
- **Lemma 61** — The Causal Closure is a Closure Operator
- **Definition 62** — Causally complete region
- **Theorem 63** — Lattice of causally complete regions
- **Lemma 64** — De Morgan Laws for the Spacelike Complement (set level)
- **Theorem 65** — De Morgan Laws for the Causal Complement (binary and infinitary, on the lattice)

**§10.2.2 Causal convexity (p. 48)**

- **Definition 66** — Causally convex region
- **Lemma 67** — Causal diamonds are causally convex
- **Theorem 68** — Causally complete regions are causally convex

**§10.2.3 Causal convexity: closure structure, and the Alexandrov basis theorems (p. 49)**

- **Lemma 69** — Causally convex regions form a closure system
- **Definition 70** — Causal-convex hull
- **Lemma 71** — The Causal-Convex Hull is Extensive and Causally Convex
- **Theorem 72** — The causal-convex hull is a closure operator
- **Definition 73** — Alexandrov Topology
- **Lemma 74** — Basis Sets Are Alexandrov-Open
- **Lemma 75** — Openness of Chronological Futures and Pasts (under a "no endpoints" hypothesis)
- **Lemma 76** — Unconditional Openness of Chronological Futures and Pasts on Standard Minkowski
- **Definition 77** — Minkowski Spacetime (standard Minkowski with the Alexandrov topology)
- **Definition 78** — Lorentzian Spacetime (a spacetime whose Alexandrov topology is Hausdorff)
- **Lemma 79** — Bundled Spacelike Separation and Basis Openness
- **Lemma 80** — No-Diamond Points Have Only the Whole Space as Neighbourhood
- **Lemma 81** — Covering from the Hausdorff Assumption
- **Theorem 82** — The Alexandrov Diamonds Form a Topological Basis (given downward-directedness)
- **Lemma 83** — Past Interpolation on Standard Minkowski
- **Lemma 84** — Future Interpolation on Standard Minkowski
- **Lemma 85** — Standard Minkowski Diamonds Are Downward-Directed
- **Lemma 86** — Common Chronological Predecessor on Standard Minkowski
- **Lemma 87** — Common Chronological Successor on Standard Minkowski
- **Lemma 88** — Standard Minkowski Diamonds Are Upward-Directed
- **Theorem 89** — The Alexandrov Diamonds are a Basis on Standard Minkowski (unconditional)

**§10.2.4 Dilations are causal automorphisms but not isometries (p. 54)**

- **Lemma 90** — Dilations Preserve the Minkowski Cones
- **Theorem 91** — Dilations are Causal Automorphisms
- **Theorem 92** — Dilations are Not Isometries

**§10.2.5 Isometries and basis-set preservation (p. 54)**

- **Lemma 93** — Isometries Preserve the Causal Classification
- **Lemma 94** — Unique Differentials Along a Path
- **Lemma 95** — Pushforward of a Path Under an Isometry
- **Lemma 96** — Isometries Preserve Chronology
- **Lemma 97** — Isometries Preserve Basis Sets
- **Lemma 98** — Axiom 5 Basis-Set Preservation

**§10.2.6 Pullback metrics and cross-metric isometries (p. 55)**

- **Definition 99** — Pullback of a Spacetime Metric
- **Lemma 100** — The Differential of a Diffeomorphism is a Linear Equivalence
- **Lemma 101** — Round-Trip Cancellation: $$d\psi$$ after $$d(\psi^{-1})$$
- **Lemma 102** — Round-Trip Cancellation: $$d(\psi^{-1})$$ after $$d\psi$$
- **Lemma 103** — The Formal Inverse of $$d\psi_x$$ is the Inverse Equivalence
- **Lemma 104** — The Pullback Metric is Symmetric
- **Lemma 105** — The Pullback Metric is Non-Degenerate
- **Lemma 106** — The Pullback Metric is Lorentzian
- **Lemma 107** — The Pullback Metric is a Smooth Section of the Bilinear-Form Bundle
- **Theorem 108** — The Pullback of a Spacetime is a Spacetime
- **Definition 109** — Two-Sided Preservation of Future Orientation
- **Lemma 110** — The Pullback of a Bundle-Smooth Vector Field Along a Diffeomorphism is Bundle-Smooth
- **Lemma 111** — The Pullback Time Orientation is Nowhere Vanishing
- **Lemma 112** — The Pullback Time Orientation is Everywhere Timelike
- **Lemma 113** — Pullback of a Time Orientation
- **Lemma 114** — Transport of Future-Pointing Timelike Vectors
- **Lemma 115** — Transport of Future-Pointing Null Vectors
- **Lemma 116** — The Pullback Preserves the Future Orientation Two-Sidedly
- **Definition 117** — Isometry Between Two Metrics on One Manifold
- **Lemma 118** — The Inverse of a Cross-Metric Isometry is a Cross-Metric Isometry
- **Lemma 119** — Cross-Metric Isometries Preserve the Causal Classification
- **Lemma 120** — The Tangent Chain Rule Along a Path
- **Lemma 121** — Pushforward of a Path Under a Cross-Metric Isometry
- **Lemma 122** — The Pushforward Preserves the Timelike and Causal Conditions
- **Lemma 123** — The Pushforward Transports Endpoints
- **Lemma 124** — Cross-Metric Isometries Transport Chronological Precedence
- **Lemma 125** — Image of the Chronological Future
- **Lemma 126** — Image of the Chronological Past
- **Lemma 127** — Cross-Metric Isometries Preserve Basis Sets
- **Lemma 128** — A Bijection Matching Generating Families is a Homeomorphism
- **Lemma 129** — The Pullback Alexandrov Topology
- **Theorem 130** — The Pullback of a Lorentzian Spacetime is a Lorentzian Spacetime

### §10.3 Haag–Kastler Axioms in Minkowski spacetime (pp. 67–104)

**§10.3 The axioms (p. 67)**

- **Definition 131** — Axiom 1: Local Algebras
- **Definition 132** — Axiom 2: Isotony (the isotony family supplied as chosen data, with injectivity, identity, and composition laws)

**§10.3.1 The Quasilocal Colimit (p. 68)**

- **Lemma 133** — Alexandrov Diamonds are Directed under Inclusion
- **Lemma 134** — The Isotony Family is a Directed System
- **Lemma 135** — The Colimit Norm is Well Defined
- **Lemma 136** — Common Representatives for Two Colimit Elements
- **Lemma 137** — The Colimit Norm is a Ring Norm and a Normed-Space Norm
- **Lemma 138** — The Quasilocal Union is a Normed \*-Algebra
- **Lemma 139** — The Colimit Satisfies the C\*-Inequality
- **Definition 140** — Standing Hypotheses for the Completion Results
- **Definition 141** — The Involution on a Completion
- **Lemma 142** — The Involution Extends to the Completion
- **Lemma 143** — The Completion Coercion as a Bundled \*-Algebra Homomorphism
- **Lemma 144** — The C\*-Inequality Passes to the Completion
- **Lemma 145** — The Completion is a Normed $$\mathbb{C}$$-Algebra
- **Lemma 146** — The Completion of a C\*-Normed \*-Algebra is a C\*-Algebra
- **Lemma 147** — The Completion of the Quasilocal Colimit is a C\*-Algebra
- **Definition 148** — Quasilocal Algebra (the directed colimit of the local algebras, completed)
- **Definition 149** — Axiom 3: Local Commutativity
- **Definition 150** — Quasilocal Observable
- **Definition 151** — Axiom 4: Quasilocal Completeness (a bridge principle: every physical observable corresponds to a quasilocal observable)
- **Theorem 152** — Existence of a Quasilocal Algebra (the mathematical content formerly bundled into Axiom 4)
- **Lemma 153** — The Canonical Embeddings into the Quasilocal Algebra
- **Lemma 154** — The Canonical Embeddings are Injective
- **Lemma 155** — The Canonical Embeddings Form a Cocone
- **Lemma 156** — The Colimit is the Union of the Images of its Insertions
- **Lemma 157** — The Images of the Canonical Embeddings are Dense
- **Theorem 158** — Quasilocal Observables are Strongly Dense in the Bicommutant *(stated from the literature; deliberately not formalised — the von Neumann density theorem is absent from Mathlib)*
- **Definition 159** — Axiom 5: Lorentz Covariance
- **Definition 160** — Haag–Kastler Net

**§10.3.2 Einstein Causality (p. 86)**

- **Theorem 161** — Einstein Causality in a Representation

**§10.3.3 Local von Neumann Algebras (p. 86)**

- **Definition 162** — Local von Neumann Algebra
- **Lemma 163** — The Bicommutant of a Self-Adjoint Set is a von Neumann Algebra
- **Definition 164** — $$R(\mathbf{B})$$ as a von Neumann Algebra
- **Theorem 165** — Microcausality at the von Neumann Level
- **Theorem 166** — Isotony of the von Neumann Net
- **Theorem 167** — Bundled von Neumann Microcausality and Isotony
- **Definition 168** — The Net of von Neumann Algebras
- **Theorem 169** — Statistical Independence (Schlieder Property)
- **Theorem 170** — Statistical Independence, bundled
- **Theorem 171** — Additive-Free Locality via the Spacelike Complement
- **Theorem 172** — Geometric Covariance of the von Neumann Net
- **Theorem 173** — Orbit-Invariance of Factoriality
- **Theorem 174** — Geometric Covariance as a von Neumann Algebra Isomorphism

**§10.3.4 Relative Commutants of Nested Local Algebras (p. 88)**

- **Definition 175** — Relative Commutant of a Nested Pair
- **Theorem 176** — Antitonicity of the Commutant
- **Theorem 177** — Relative Commutant Lies in the Larger Algebra
- **Theorem 178** — Relative Commutant Commutes with the Smaller Algebra
- **Theorem 179** — Relative Commutant Contains the Center
- **Definition 180** — Irreducible Inclusion
- **Theorem 181** — An Irreducible Inclusion has Factor Ambient
- **Theorem 182** — Self-Inclusion is Irreducible iff Factor

**§10.3.5 Irreducibility and Schur's Lemma (p. 90)**

- **Definition 183** — Irreducible Representation
- **Theorem 184** — Topological Schur Lemma
- **Theorem 185** — Commutant Scalar iff Proportional Coefficient
- **Definition 186** — Pure State
- **Theorem 187** — Pure Implies Irreducible
- **Theorem 188** — The GNS Radon–Nikodym Form is Bounded
- **Theorem 189** — The GNS Radon–Nikodym Operator
- **Theorem 190** — Pure $$\iff$$ Irreducible
- **Theorem 191** — An Irreducible Representation Generates a Factor
- **Theorem 192** — Irreducibility $$\iff$$ Generating $$\mathcal{B}(H)$$
- **Theorem 193** — Bundled Density Form of Irreducibility
- **Theorem 194** — The GNS Representation of a Pure State is a Factor
- **Theorem 195** — The GNS Representation of a Pure State Generates $$\mathcal{B}(H)$$
- **Theorem 196** — Norm of a Positive Functional (equals its value on the unit)
- **Definition 197** — Extreme Point of the State Space
- **Theorem 198** — Pure $$\iff$$ Extreme Point
- **Theorem 199** — State-Space Convexity and the Extreme-Point Bridge
- **Definition 200** — Pullback of a State
- **Theorem 201** — Functoriality of the State Pullback
- **Theorem 202** — Purity is Invariant under a \*-Isomorphism
- **Theorem 203** — Weak-\* Compactness of the State Space
- **Theorem 204** — Pure $$\iff$$ Extreme Point on the Quasilocal Algebra
- **Theorem 205** — Pure $$\iff$$ Irreducible GNS on the Quasilocal Algebra

**§10.3.6 Unitary Equivalence and Superselection (p. 93)**

- **Definition 206** — Unitary Equivalence of Representations
- **Theorem 207** — Irreducibility and Factoriality are Unitary Invariants

**§10.3.7 GNS Covariance (p. 94)**

- **Lemma 208** — Cyclicity pulls back along a surjective \*-homomorphism
- **Theorem 209** — GNS covariance under a \*-isomorphism
- **Theorem 210** — The GNS representation of a pullback state
- **Lemma 211** — Pullback along a surjection preserves the image algebra
- **Theorem 212** — Superselection type transports along a \*-isomorphism
- **Theorem 213** — GNS covariance for local algebras (superselection type is constant along the Lorentz orbit of a region)

**§10.3.8 Disjointness and Quasi-Equivalence (p. 95)**

- **Definition 214** — Disjoint Representations
- **Definition 215** — Quasi-Equivalence of Representations
- **Theorem 216** — Schur's Lemma and the Irreducible Dichotomy
- **Lemma 217** — Schur Multiplicity
- **Lemma 218** — Endomorphism Algebra of an Irreducible Representation
- **Theorem 219** — The commutant (self-intertwiner, or gauge) von Neumann algebra
- **Theorem 220** — Double-Commutant Duality
- **Theorem 221** — A Factor and its Commutant; Triviality Duality
- **Lemma 222** — Abelian $$\iff$$ Self-Commuting
- **Definition 223** — Center of a von Neumann algebra
- **Lemma 224** — The center is a von Neumann algebra
- **Lemma 225** — The intersection of two von Neumann algebras is a von Neumann algebra
- **Theorem 226** — The center of a von Neumann algebra is abelian
- **Lemma 227** — $$R$$ is abelian iff it equals its center
- **Theorem 228** — A factor is abelian iff it is the scalars
- **Theorem 229** — A von Neumann algebra and its commutant share a center
- **Theorem 230** — A von Neumann algebra is a factor iff its center is the scalars
- **Theorem 231** — The Pure-State Dichotomy

**§10.3.9 Direct Sums, Amplification, and Reducibility (p. 98)**

- **Definition 232** — Direct-Sum Representation
- **Theorem 233** — Subrepresentations and Commutant of a Direct Sum
- **Definition 234** — Amplification
- **Theorem 235** — Reducibility of a Direct Sum

**§10.3.10 Covariant States and the Covariance Action (p. 99)**

- **Definition 236** — Covariant Family of Local States
- **Lemma 237** — Composition of Covariance
- **Definition 238** — Quasilocal Covariance Automorphism
- **Lemma 239** — Uniqueness of the Quasilocal Lift
- **Theorem 240** — Existence of the Quasilocal Lift
- **Theorem 241** — Existence for the Trivial Net
- **Definition 242** — Covariant Quasilocal Algebra
- **Lemma 243** — Group-Action Coherence of the Covariance Automorphism
- **Definition 244** — Invariant State
- **Theorem 245** — GNS Unitary Implementation of an Invariant State
- **Theorem 246** — Irreducible Covariant Representation of a Pure Invariant State
- **Definition 247** — Positive Energy (bounded-generator scaffold)
- **Theorem 248** — Positive-Energy API
- **Definition 249** — Vacuum State (generator-parameterised scaffold)
- **Theorem 250** — No-Stone Consequences of a Vacuum State
- **Definition 251** — Future-Timelike Translation Subgroup
- **Definition 252** — Vacuum State with the Concrete Spectrum Condition
- **Theorem 253** — Purity is Covariance-Invariant
- **Theorem 254** — GNS covariance along the quasilocal action

**§10.3.11 The Separating Vector of a Faithful State (p. 102)**

- **Theorem 255** — Separating Vector of a Faithful State

**§10.3.12 The KMS Condition and Thermal Equilibrium (p. 102)**

- **Definition 256** — One-Parameter Automorphism Group
- **Definition 257** — KMS State
- **Theorem 258** — The KMS State Set is Convex
- **Lemma 259** — Boundary Coincidence for $$a = 1$$
- **Definition 260** — Strip-Liouville Principle
- **Theorem 261** — $$i\beta$$-Periodic Entire Extension (Strip Schwarz Reflection)
- **Theorem 262** — Strip-Liouville Holds for $$\beta > 0$$
- **Theorem 263** — KMS States are Invariant
- **Theorem 264** — Uniqueness on the Strip from Boundary Values
- **Theorem 265** — Uniqueness of the KMS Correlation Function

**§10.3.13 KMS States for the Covariance Flow (p. 104)**

- **Definition 266** — Covariance-Flow Automorphism Family
- **Lemma 267** — A Lorentz One-Parameter Subgroup Induces a One-Parameter Group
- **Definition 268** — KMS State for the Covariance Flow
- **Theorem 269** — Convexity of the Covariance-Flow KMS States
- **Definition 270** — Ground State for a Covariance Flow

### §10.4 Haag–Kastler Axioms in curved spacetime (pp. 105–114)

**§10.4 The axioms (p. 105)**

- **Definition 271** — Axiom 1: Local Algebras
- **Definition 272** — Axiom 2: Isotony (chosen data, with injectivity, identity, and composition laws)
- **Definition 273** — Axiom 3: Local Commutativity (consuming the Axiom 2 isotony family)
- **Definition 274** — Local Observable
- **Definition 275** — Axiom 4: Local Completeness
- **Definition 276** — Axiom 5: Isometric Covariance
- **Definition 277** — Haag–Kastler Net in Curved Spacetime

**§10.4.1 Einstein Causality in Curved Spacetime (p. 107)**

- **Theorem 278** — Einstein Causality in a Representation (Curved Spacetime)

**§10.4.2 Local von Neumann Algebras in Curved Spacetime (p. 107)**

- **Definition 279** — Local von Neumann Algebra in Curved Spacetime
- **Definition 280** — $$R(\mathbf{B}')$$ as a von Neumann Algebra (Curved Spacetime)
- **Theorem 281** — Microcausality at the von Neumann Level (Curved Spacetime)
- **Theorem 282** — Isotony of the von Neumann Net (Curved Spacetime) — no coherence hypothesis needed
- **Theorem 283** — Bundled von Neumann Microcausality and Isotony (Curved Spacetime)
- **Definition 284** — The Net of von Neumann Algebras in Curved Spacetime
- **Theorem 285** — Statistical Independence (Schlieder Property)
- **Theorem 286** — Statistical Independence, bundled (Curved Spacetime)
- **Theorem 287** — Additive-Free Locality via the Spacelike Complement (Curved Spacetime)
- **Theorem 288** — Geometric Covariance of the von Neumann Net (Curved Spacetime) — basis-set preservation and stabiliser/isotony coherence enter as explicit hypotheses
- **Theorem 289** — Orbit-Invariance of Factoriality (Curved Spacetime)
- **Theorem 290** — Geometric Covariance as a von Neumann Algebra Isomorphism (Curved Spacetime)

**§10.4.3 Relative Commutants of Nested Local Algebras in Curved Spacetime (p. 109)**

- **Definition 291** — Relative Commutant of a Nested Pair (Curved Spacetime)
- **Theorem 292** — Relative Commutant Lies in the Larger Algebra (Curved Spacetime)
- **Theorem 293** — Relative Commutant Commutes with the Smaller Algebra (Curved Spacetime)
- **Theorem 294** — Relative Commutant Contains the Center (Curved Spacetime)
- **Definition 295** — Irreducible Inclusion (Curved Spacetime)
- **Theorem 296** — An Irreducible Inclusion has Factor Ambient (Curved Spacetime)
- **Theorem 297** — Self-Inclusion is Irreducible iff Factor (Curved Spacetime)
- **Theorem 298** — Abelian Local von Neumann Algebras (Curved Spacetime)
- **Theorem 299** — Center Duality for Local von Neumann Algebras (Curved Spacetime)

**§10.4.4 Purity of States on Local Algebras in Curved Spacetime (p. 110)**

- **Theorem 300** — Pure $$\iff$$ Extreme Point on a Local Algebra
- **Theorem 301** — Pure $$\iff$$ Irreducible GNS on a Local Algebra
- **Theorem 302** — Pure GNS on a Local Algebra is a Factor Generating $$\mathcal{B}(H)$$
- **Theorem 303** — The Irreducible Dichotomy for a Curved Local Algebra
- **Theorem 304** — GNS covariance for curved local algebras

**§10.4.5 Covariant States in Curved Spacetime (p. 111)**

- **Definition 305** — Covariant Family of Local States in Curved Spacetime
- **Lemma 306** — Composition of Covariance in Curved Spacetime

**§10.4.6 The Stabilizer GNS Unitary in Curved Spacetime (p. 112)**

- **Definition 307** — Stabilizer Action on a Local Algebra
- **Lemma 308** — The Stabilizer Action is a Group Action
- **Theorem 309** — GNS Unitary Representation of the Stabilizer
- **Theorem 310** — Strongly Continuous Stabilizer GNS Unitary
- **Theorem 311** — Irreducible Covariant Representation of a Pure Invariant State (Curved Spacetime)
- **Theorem 312** — Purity is Invariant under the Stabilizer Action
- **Theorem 313** — GNS covariance along the stabilizer action

**§10.4.7 KMS States for a Killing Flow (p. 113)**

- **Definition 314** — Killing-Flow Automorphism Family
- **Lemma 315** — A Killing Flow Induces a One-Parameter Group
- **Definition 316** — KMS State for a Killing Flow
- **Theorem 317** — The Killing-Flow KMS Thermal Representation
- **Theorem 318** — Convexity of the Killing-Flow KMS States
- **Definition 319** — Ground State for a Killing Flow

### §10.5 General Covariance: Nets on Pullback-Related Metrics (pp. 114–116)

- **Definition 320** — Equivalence of Haag–Kastler Nets
- **Definition 321** — General Covariance

### The axioms at a glance

Axiom 6 (Primitivity) from the original 1964 Haag–Kastler paper is not carried into the sharpened axiom set — see Chapter 8 for the discussion of why it is dropped. The five sharpened axioms in each setting, bundled together as a `HaagKastlerNet`, are what is actually formalised.

**Minkowski spacetime:** Local Algebras (Definition 131), Isotony (Definition 132), Local Commutativity (Definition 149), Quasilocal Completeness (Definition 151), Lorentz Covariance (Definition 159); bundled as a Haag–Kastler net (Definition 160).

**Curved spacetime:** Local Algebras (Definition 271), Isotony (Definition 272), Local Commutativity (Definition 273), Local Completeness (Definition 275), Isometric Covariance (Definition 276); bundled as a Haag–Kastler net in curved spacetime (Definition 277).

**General Covariance (Definition 321)** is deliberately *not* a sixth axiom. Axioms 1–5 each constrain a single net over a single fixed spacetime, whereas general covariance relates two nets over two spacetimes; it is therefore a property of the section $$L \mapsto \mathfrak{U}_L$$ assigning a net to every Lorentzian spacetime, not an extra field of the net structure.

Two changes to the axioms are worth calling out for readers coming from an earlier version of this blueprint:

- **Isotony now supplies its embeddings as data.** Axiom 2 (Definitions 132 and 272) fixes the family $$i_{\mathbf{B}_1 \mathbf{B}_2}$$ together with identity and composition laws, making $$\mathbf{B} \mapsto \mathfrak{U}(\mathbf{B})$$ a functor on the inclusion order. Axiom 3 consumes that family rather than choosing witnesses of its own. This is what makes the quasilocal colimit well posed in Minkowski spacetime, and it removes the coherence side-hypotheses that curved-spacetime statements about nested regions previously had to carry.
- **Axiom 4 has been split.** The mathematical claim that a quasilocal algebra exists is now Theorem 152, proved from the colimit-and-completion chain; what remains as Axiom 4 (Definition 151) is the bridge principle relating physical observables to quasilocal ones, which has — by design — no mathematical consumers.

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
