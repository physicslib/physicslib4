---
title: "§10.5 Haag–Kastler Axioms in Minkowski spacetime (pp. 270–310)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Spacetime](sec10-4-spacetime.html) · **§10.5 Minkowski** · [§10.6 Curved](sec10-6-curved.html) · [§10.7 Covariance](sec10-7-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.4 Spacetime](sec10-4-spacetime.html) · [§10.6 Curved](sec10-6-curved.html) →

# §10.5 Haag–Kastler Axioms in Minkowski spacetime (pp. 270–310)

The largest section by definition and theorem count (152 items, Definitions 420–571). Each axiom is stated as a definition so that it appears as a node in the declaration graph.

- *The axioms and the quasilocal colimit (§10.5 and §10.5.1, pp. 270–287, items 420–447).* Axiom 1 (Local Algebras, Definition 420) assigns an abstract C\*-algebra to every Alexandrov-basis set, with $$\emptyset \mapsto \mathbb{C}1$$. Axiom 2 (Isotony, Definition 421) now supplies the family of unital \*-monomorphisms $$i_{\mathbf{B}_1 \mathbf{B}_2}$$ **as chosen data**, subject to injectivity, an identity law, and a composition law—so that $$\mathbf{B} \mapsto \mathfrak{U}(\mathbf{B})$$ is a functor on the inclusion order of basis sets. The blueprint is explicit that the family cannot be an existence statement (the identity and composition conditions are equations between the maps themselves) and that the inclusion hypothesis is non-strict, matching the Lean. §10.5.1 then cashes this in: the diamonds are directed under inclusion (Lemma 422), the isotony family is a directed system in Mathlib's sense (Lemma 423), and the direct limit carries a well-defined norm (Lemmas 424–426) making it a normed \*-algebra (Lemma 427) satisfying the C\*-inequality (Lemma 428) but not, in general, complete. A block of results stated for an arbitrary normed \*-algebra under standing hypotheses (Definition 429) then carries the structure through completion—the involution and its extension (Definition 430, Lemma 431), the completion coercion as a bundled \*-algebra homomorphism (Lemma 432), and the passage of the C\*-inequality, the normed $$\mathbb{C}$$-algebra structure, and finally the C\*-algebra property to the completion (Lemmas 433–435)—yielding that the completion of the quasilocal colimit is a C\*-algebra (Lemma 436). The quasilocal algebra $$\mathfrak{U}$$ is defined as that colimit-then-completion (Definition 437); the blueprint records why the shortcut of realising $$\mathfrak{U}$$ as a closed \*-subalgebra of an ambient C\*-algebra is rejected—it would assume an ambient algebra containing copies of every $$\mathfrak{U}(\mathbf{B})$$, for which the physics supplies no justification. Axiom 3 (Local Commutativity, Definition 438) follows, together with the new Lemma 439: local commutativity transfers from any one quasilocal algebra to every other, so the choice of quasilocal algebra in Axiom 3 is immaterial and the canonical $$\mathfrak{U}$$ of a net can be used throughout. The quasilocal observable (Definition 440) follows. **Axiom 4 is now split in two.** Axiom 4 (Quasilocal Completeness, Definition 441) is presented as a bridge principle—the one axiom joining physical reality to the formalism, asserting the one-way inclusion that every physical observable corresponds to a quasilocal observable, and therefore having no mathematical consumers. The mathematical content previously conflated with it is separated out as a theorem: every local net satisfying Axiom 2 admits a quasilocal algebra, with an injective cocone of canonical embeddings whose images are dense (Theorem 442, with the supporting Lemmas 443–447). The indexing over Alexandrov-basis sets only is essential and not stylistic, since the algebras attached to non-basis subsets are junk fibres about which the axioms say nothing.
- *§10.5.2 The von Neumann Density Theorem (pp. 287–290, items 448–458).* A new subsection of general operator theory for a unital \*-homomorphism $$\pi : \mathfrak{A} \to \mathcal{B}(H)$$, whose only consumer is Theorem 458, the density result that keeps the bridge principle tenable in the presence of larger bicommutants: $$\pi_\omega(\mathfrak{U})$$ is strongly dense in $$\pi_\omega(\mathfrak{U})$$. Mathlib lacks the density theorem, so it is proved here following Murphy, Lemma 4.1.4. A closed subspace invariant under an operator and its adjoint has a commuting orthogonal projection (Lemma 448), so the closed cyclic subspace $$\overline{\pi(\mathfrak{A})\xi}$$ reduces the representation (Lemma 449) and every $$T \in \pi(\mathfrak{A})$$ maps $$\xi$$ into it (Lemma 450). The finite amplification $$\pi^\iota$$ on $$\ell^2(\iota; H)$$ (Definition 451) is a unital \*-homomorphism (Lemma 452); the block entries of an operator in its commutant lie in $$\pi(\mathfrak{A})'$$ (Lemma 453), an operator on $$\ell^2(\iota; H)$$ is recovered from its block entries (Lemma 454), and so $$\mathrm{diag}(T)$$ lies in the amplified bicommutant (Lemma 455). Applying the one-vector case to the amplification approximates $$T$$ on any finite set of vectors (Lemma 456), and a neighbourhood basis for the strong operator topology (Lemma 457) turns this into the density theorem (Theorem 458), now fully proved. The Kaplansky density theorem, which would also keep approximants self-adjoint, remains out of scope; nothing needs it.
- *§10.5.3 Lorentz Covariance and the Haag–Kastler Net (p. 290, items 459–460).* Axiom 5 (Lorentz Covariance, Definition 459), whose coherence condition is now stated for the Axiom 2 isotony family itself, and the bundled `HaagKastlerNet` (Definition 460) close the axiomatic block.
- *§10.5.4 Einstein Causality (p. 291, item 461).* Derives the operator form of local commutativity in any \*-representation of the quasilocal algebra (Theorem 461).
- *§10.5.5 Local von Neumann Algebras (p. 291, items 462–474).* Defines the local von Neumann algebra $$R(\mathbf{B}) = \pi(\mathfrak{U}(\mathbf{B}))''$$ of a region in a representation (Definition 462), registers it as a first-class `VonNeumannAlgebra` via the bicommutant-of-a-self-adjoint-set lemma (Lemma 463, Definition 464), and proves Microcausality (Theorem 465) and Isotony of the von Neumann net (Theorem 466), together with their bundled forms (Theorem 467) and the region-indexed assignment $$\mathbf{B} \mapsto R(\mathbf{B})$$ as an order-preserving map—the net of von Neumann algebras itself (Definition 468). It then proves the Statistical Independence (Schlieder) property in set-level and bundled forms (Theorems 469–470): if the cyclic vector of one region is cyclic for its local observables, it is separating for the local von Neumann algebra of any spacelike-separated region. Additive-free locality (Theorem 471) expresses locality through the spacelike complement without attaching an algebra to the unbounded complement itself. Geometric Covariance (Theorem 472) shows conjugation by the implementing unitary carries $$R(\mathbf{B})$$ onto $$R(L \cdot \mathbf{B})$$; being a factor is therefore constant along the Lorentz orbit of a region (Theorem 473), and the set equality upgrades to a first-class \*-algebra isomorphism of the bundled algebras (Theorem 474).
- *§10.5.6 Relative Commutants of Nested Local Algebras (p. 294, items 475–482).* A new block organising the theory of inclusions $$R(\mathbf{B}_1) \subseteq R(\mathbf{B}_2)$$ around the relative commutant $$R(\mathbf{B}_1)' \cap R(\mathbf{B}_2)$$ (Definition 475). It proves antitonicity of the commutant (Theorem 476), that the relative commutant lies in the larger algebra and commutes with the smaller (Theorems 477–478), and that it always contains the centre of the ambient algebra (Theorem 479). An inclusion is irreducible when its relative commutant is trivial (Definition 480); an irreducible inclusion forces the ambient algebra to be a factor (Theorem 481), and the trivial self-inclusion is irreducible exactly when the algebra is a factor (Theorem 482).
- *§10.5.7 Irreducibility and Schur's Lemma (p. 295, items 483–505).* Introduces irreducible representations via their commutant (Definition 483) and establishes the Topological Schur Lemma for cyclic representations (Theorem 484) together with the operator-theoretic bridge identifying commutant scalars with coefficients proportional to the state (Theorem 485). Defines pure states (Definition 486) and proves "pure implies irreducible" directly (Theorem 487), then the full equivalence Pure $$\iff$$ Irreducible (Theorem 490) via a GNS Radon–Nikodym theorem realising every dominated positive functional as an operator in the commutant (Theorems 488–489). An irreducible representation generates a factor (Theorem 491) and, more sharply, all of $$\mathcal{B}(H)$$ (Theorem 492), with a bundled density form (Theorem 493); consequently the GNS representation of a pure state generates a factor (Theorem 494) and all of $$\mathcal{B}(H)$$ (Theorem 495). The norm of a positive linear functional on a unital C\*-algebra equals its value on the unit (Theorem 496), which supports Pure $$\iff$$ Extreme Point of the state space (Definition 497, Theorem 498), the underlying convexity and the bridge to Mathlib's extreme-points API (Theorem 499), and weak-\* compactness of the state space (Theorem 503), which supplies the existence of pure states via Krein–Milman. The pullback of a state along a unital \*-homomorphism is introduced as its own object (Definition 500) with functoriality (Theorem 501) and the invariance of purity under a \*-isomorphism (Theorem 502). The section closes by specialising to the quasilocal algebra (Theorems 504–505).
- *§10.5.8 Unitary Equivalence and Superselection (p. 299, items 506–507).* Defines unitary equivalence of representations (Definition 506) and shows irreducibility and factoriality are unitary invariants, transported by the cross-space conjugation induced by the implementing unitary (Theorem 507).
- *§10.5.9 GNS Covariance (p. 299, items 508–513).* A new block. Cyclicity pulls back along a surjective \*-homomorphism (Lemma 508), so GNS data transports covariantly along a \*-isomorphism of the algebras (Theorem 509), restated as a unitary equivalence (Theorem 510). Pullback along a surjection preserves the image algebra (Lemma 511), whence superselection type transports along a \*-isomorphism (Theorem 512): the whole sector structure is an invariant of the algebra, not of its presentation. Applied to the covariance equivalence $$\alpha_L : \mathfrak{U}(\mathbf{B}) \simeq \mathfrak{U}(L \cdot \mathbf{B})$$ supplied by Axiom 5, this says the superselection type of a local state is constant along the Lorentz orbit of its region (Theorem 513).
- *§10.5.10 Disjointness and Quasi-Equivalence (p. 301, items 514–531).* Defines disjointness via the vanishing of all intertwiners (Definition 514) and the coarser quasi-equivalence via a \*-isomorphism of generated von Neumann algebras (Definition 515). Proves Schur's Lemma in the form of the Irreducible Dichotomy—two irreducible representations are either disjoint or unitarily equivalent (Theorem 516)—together with Schur multiplicity (Lemma 517) and the triviality of the endomorphism algebra of an irreducible representation (Lemma 518). The commutant is packaged as the self-intertwiner (gauge) von Neumann algebra, trivial exactly when the representation is irreducible (Theorem 519), with double-commutant duality (Theorem 520) and the factor/triviality duality between an algebra and its commutant (Theorem 521). A supporting run develops the centre from scratch: abelian $$\iff$$ self-commuting (Lemma 522), the centre $$Z(R) = R \cap R'$$ (Definition 523) and its being a von Neumann algebra (Lemma 524), the general two-algebra intersection lemma that the relative commutants of §10.5.6 need (Lemma 525), the centre is abelian (Theorem 526), $$R$$ is abelian iff it equals its centre (Lemma 527), a factor is abelian iff it is the scalars (Theorem 528), an algebra and its commutant share a centre (Theorem 529), and factoriality is triviality of the centre (Theorem 530). The Pure-State Dichotomy underlying superselection sectors (Theorem 531) closes the block.
- *§10.5.11 Direct Sums, Amplification, and Reducibility (p. 303, items 532–535).* Defines the direct-sum representation on the $$\ell^2$$-direct sum (Definition 532), shows each summand embeds as a subrepresentation whose projection lies in the commutant of the sum (Theorem 533), defines the $$\iota$$-fold amplification (Definition 534), and proves a direct sum with at least two nonzero summands is reducible, so a multiply-amplified representation is never irreducible (Theorem 535).
- *§10.5.12 Covariant States and the Covariance Action (p. 304, items 536–555).* Defines covariant families of local states (Definition 536) with their composition law (Lemma 537), and the lift of the fibrewise covariance action to a \*-automorphism of the quasilocal algebra (Definition 538), with uniqueness (Lemma 539) and existence for every quasilocal algebra (Theorem 541), no covariance-compatibility hypothesis being needed because every quasilocal algebra is automatically covariance-compatible (Lemma 540, new), and the trivial net as a special case (Theorem 542). The covariant quasilocal algebra of a net is then simply its canonical quasilocal algebra together with the covariance action (Definition 543, realised in Lean as `HaagKastlerNet.action`, so the covariance dynamics are stated directly for the net), which is a genuine group action (Lemma 544). Invariant states are defined (Definition 545) and shown to be implemented by GNS unitaries (Theorem 546); a state that is both invariant and pure yields a GNS representation that is simultaneously covariant and irreducible (Theorem 547). A "bounded-generator" scaffold toward the spectrum condition follows, deliberately sidestepping Stone's theorem and unbounded self-adjoint operators (the Lean records this bounded-generator restriction in **Restriction:** notes): positive energy for a bounded generator (Definition 548) with its API (Theorem 549), a generator-parameterised vacuum state (Definition 550) and its Stone-free consequences (Theorem 551), the future-timelike translation subgroup (Definition 552), and the vacuum state with that concrete predicate substituted in, leaving no free parameter (Definition 553). Purity is preserved by any \*-automorphism and is therefore covariance-invariant (Theorem 554), and GNS data transports along the quasilocal covariance action (Theorem 555).
- *§10.5.13 The Separating Vector of a Faithful State (p. 307, item 556).* The cyclic vector of a faithful state is also separating for the image of the representation (Theorem 556)—the basic datum of Tomita–Takesaki modular theory. This holds in any representation reproducing a faithful state, not only the canonical GNS one.
- *§10.5.14 The KMS Condition and Thermal Equilibrium (p. 308, items 557–566).* Introduces one-parameter automorphism groups (Definition 557) and KMS states (Definition 558) as the algebraic characterisation of thermal equilibrium. The condition is phrased purely as an analyticity statement about correlation functions, so—unlike the spectrum condition—it needs no unbounded-operator theory. The KMS state set is convex (Theorem 559); a boundary-coincidence argument at $$a = 1$$ (Lemma 560) together with the Strip-Liouville Principle (Definition 561), proved at positive inverse temperature via an $$i\beta$$-periodic entire extension (Theorem 562) and Liouville's theorem (Theorem 563), yields that KMS states are automatically invariant under the time evolution (Theorem 564); uniqueness on the strip from boundary values (Theorem 565) gives uniqueness of the analytic completion of a KMS correlation function (Theorem 566).
- *§10.5.15 KMS States for the Covariance Flow (p. 309, items 567–571).* A one-parameter subgroup of the inhomogeneous Lorentz group induces a one-parameter automorphism group on the quasilocal algebra via the covariance lift (Definition 567, Lemma 568); KMS states for that flow are defined accordingly (Definition 569) and shown convex (Theorem 570). The zero-temperature ($$\beta \to \infty$$) counterpart—a ground state for a covariance flow, whose GNS-implementing unitary group has positive energy—is recorded alongside it (Definition 571).

**Where the Lean lives:** `Physicslib4/AQFT/HaagKastler/`, `Physicslib4/GNS/` (`Irreducibility`, `Superselection`, `RadonNikodym`, `ExtremeState`, …), `Physicslib4/Operators/` (`ReducingSubspace`, `DensityTheorem`), `Physicslib4/AQFT/KMS.lean`, `Physicslib4/Analysis/StripPeriodicExtension.lean`

## Items

Each blueprint subsection below is collapsed; click a heading to see its items. Every entry links to its node in the web blueprint and names the principal Lean declaration.

<details markdown="1">
<summary>§10.5 The axioms (p. 270) — 2 items</summary>

- [**Definition 420**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-algebras) — Axiom 1: Local Algebras · `Physicslib4.AQFT.HaagKastler.LocalNet`
- [**Definition 421**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony) — Axiom 2: Isotony · `Physicslib4.AQFT.HaagKastler.Isotony`

</details>

<details markdown="1">
<summary>§10.5.1 The Quasilocal Colimit (p. 272) — 26 items</summary>

- [**Lemma 422**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-diamonds-isDirected) — Alexandrov Diamonds are Directed under Inclusion · `Physicslib4.AQFT.HaagKastler.Diamond` (+2 more)
- [**Lemma 423**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isotony-directed-system) — The Isotony Family is a Directed System · `Physicslib4.AQFT.HaagKastler.transitionHom` (+1 more)
- [**Lemma 424**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-norm-well-defined) — The Colimit Norm is Well Defined · `Physicslib4.AQFT.HaagKastler.QuasilocalColimit` (+3 more)
- [**Lemma 425**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-common-representatives) — Common Representatives for Two Colimit Elements · `Physicslib4.AQFT.HaagKastler.exists_common_representatives`
- [**Lemma 426**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-norm-axioms) — The Colimit Norm is a Ring Norm and a Normed-Space Norm · `Physicslib4.AQFT.HaagKastler.instNonemptyDiamond` (+3 more)
- [**Lemma 427**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-union-normed-star-algebra) — The Quasilocal Union is a Normed \*-Algebra · `Physicslib4.AQFT.HaagKastler.norm_eq_colimitNorm` (+1 more)
- [**Lemma 428**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-cstar-identity) — The Colimit Satisfies the C\*-Inequality · `Physicslib4.AQFT.HaagKastler.colimitCStarRing`
- [**Definition 429**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completion-standing-hypotheses) — Standing Hypotheses for the Completion Results · `Physicslib4.CStarCompletion`
- [**Definition 430**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completion-star) — The Involution on a Completion · `Physicslib4.instStarCompletion` (+1 more)
- [**Lemma 431**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:star-extends-to-completion) — The Involution Extends to the Completion · `Physicslib4.instStarRingCompletion` (+1 more)
- [**Lemma 432**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-coe-star-alg-hom) — The Completion Coercion as a Bundled \*-Algebra Homomorphism · `Physicslib4.coeStarAlgHom`
- [**Lemma 433**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-cstar-identity) — The C\*-Inequality Passes to the Completion · `Physicslib4.instCStarRingCompletion`
- [**Lemma 434**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-normed-algebra) — The Completion is a Normed $$\mathbb{C}$$-Algebra · `Physicslib4.instNormedAlgebraCompletion`
- [**Lemma 435**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completion-of-cstar-normed-star-algebra) — The Completion of a C\*-Normed \*-Algebra is a C\*-Algebra · `Physicslib4.instCStarAlgebraCompletion`
- [**Lemma 436**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-completion-cstar) — The Completion of the Quasilocal Colimit is a C\*-Algebra · `Physicslib4.AQFT.HaagKastler.QuasilocalCompletion` (+1 more)
- [**Definition 437**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-algebra) — Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra`
- [**Definition 438**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity) — Axiom 3: Local Commutativity · `Physicslib4.AQFT.HaagKastler.LocalCommutativity`
- [**Lemma 439**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:local-commutativity-any-quasilocal) — Local Commutativity Holds in Every Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.LocalCommutativity.commute_ι` (+1 more)
- [**Definition 440**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-observable) — Quasilocal Observable · `Physicslib4.AQFT.HaagKastler.IsQuasilocalObservable`
- [**Definition 441**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-completeness) — Axiom 4: Quasilocal Completeness · `Physicslib4.AQFT.HaagKastler.ObservableCorrespondence`
- [**Theorem 442**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-algebra-exists) — Existence of a Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.exists_quasilocalAlgebra`
- [**Lemma 443**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embedding) — The Canonical Embeddings into the Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.colimitStarOf` (+1 more)
- [**Lemma 444**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embedding-injective) — The Canonical Embeddings are Injective · `Physicslib4.AQFT.HaagKastler.quasilocalEmbedding_injective`
- [**Lemma 445**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embedding-cocone) — The Canonical Embeddings Form a Cocone · `Physicslib4.AQFT.HaagKastler.quasilocalEmbedding_transitionHom`
- [**Lemma 446**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-colimit-union-of-insertions) — The Colimit is the Union of the Images of its Insertions · `Physicslib4.AQFT.HaagKastler.exists_eq_colimitStarOf`
- [**Lemma 447**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-embeddings-dense) — The Images of the Canonical Embeddings are Dense · `Physicslib4.AQFT.HaagKastler.dense_iUnion_range_quasilocalEmbedding`

</details>

<details markdown="1">
<summary>§10.5.2 The von Neumann Density Theorem (p. 287) — 11 items</summary>

- [**Lemma 448**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:reducing-subspace-projection-commutes) — Reducing Subspaces Give Commuting Projections · `Physicslib4.commute_starProjection_of_invariant`
- [**Lemma 449**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cyclic-subspace-reduces) — Cyclic Subspaces Reduce the Representation · `Physicslib4.starProjection_cyclic_mem_centralizer`
- [**Lemma 450**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bicommutant-single-vector) — The Bicommutant on a Single Vector · `Physicslib4.apply_mem_closure_of_mem_bicommutant`
- [**Definition 451**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:finite-amplification) — Finite Amplification · `Physicslib4.diagAmplification` (+2 more)
- [**Lemma 452**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:finite-amplification-star-hom) — The Finite Amplification is a Unital \*-Homomorphism · `Physicslib4.diagAmplification`
- [**Lemma 453**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:commutant-of-amplification-entries) — Block Entries of the Amplified Commutant · `Physicslib4.blockEntry_mem_centralizer`
- [**Lemma 454**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:amplification-block-expansion) — Block Expansion on the Amplified Space · `Physicslib4.apply_eq_sum_blockEntry`
- [**Lemma 455**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:diagonal-in-amplified-bicommutant) — Diagonal Operators in the Amplified Bicommutant · `Physicslib4.ampDiag_mem_bicommutant`
- [**Lemma 456**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bicommutant-finite-vectors) — The Bicommutant on Finitely Many Vectors · `Physicslib4.exists_forall_norm_sub_lt_of_mem_bicommutant`
- [**Lemma 457**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:strong-neighbourhood-basis) — A Neighbourhood Basis for the Strong Operator Topology · `Physicslib4.AQFT.HaagKastler.hasBasis_nhds_ofFun`
- [**Theorem 458**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-strongly-dense) — Quasilocal Observables are Strongly Dense in the Bicommutant · `Physicslib4.AQFT.HaagKastler.dense_range_in_bicommutant` — the von Neumann density theorem, proved locally from Lemmas 448–457 (see [Formalisation status](./#formalisation-status))

</details>

<details markdown="1">
<summary>§10.5.3 Lorentz Covariance and the Haag–Kastler Net (p. 290) — 2 items</summary>

- [**Definition 459**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentz-covariance) — Axiom 5: Lorentz Covariance · `Physicslib4.AQFT.HaagKastler.LorentzCovariance`
- [**Definition 460**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:haag-kastler-net) — Haag–Kastler Net · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet`

</details>

<details markdown="1">
<summary>§10.5.4 Einstein Causality (p. 291) — 1 item</summary>

- [**Theorem 461**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:einstein-causality) — Einstein Causality in a Representation · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.einstein_causality` (+1 more)

</details>

<details markdown="1">
<summary>§10.5.5 Local von Neumann Algebras (p. 291) — 13 items</summary>

- [**Definition 462**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann) — Local von Neumann Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localOperators` (+1 more)
- [**Lemma 463**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bicommutant-of-selfadjoint-is-von-neumann) — The Bicommutant of a Self-Adjoint Set is a von Neumann Algebra · `Physicslib4.GNS.vonNeumannOfSelfAdjoint`
- [**Definition 464**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-algebra) — $$R(\mathbf{B})$$ as a von Neumann Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra`
- [**Theorem 465**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-microcausality) — Microcausality at the von Neumann Level · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_subset_centralizer`
- [**Theorem 466**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-isotony) — Isotony of the von Neumann Net · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_mono`
- [**Theorem 467**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-bundled-order) — Bundled von Neumann Microcausality and Isotony · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_le_commutant` (+1 more)
- [**Definition 468**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-net) — The Net of von Neumann Algebras · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.vonNeumannNet`
- [**Theorem 469**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence) — Statistical Independence (Schlieder Property) · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_separating` (+1 more)
- [**Theorem 470**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-bundled) — Statistical Independence, bundled · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_separating`
- [**Theorem 471**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:additive-free-locality) — Additive-Free Locality via the Spacelike Complement · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement`
- [**Theorem 472**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-geometric-covariance) — Geometric Covariance of the von Neumann Net · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.lieConj_image_localVonNeumann` (+1 more)
- [**Theorem 473**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-factor-orbit) — Orbit-Invariance of Factoriality · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumann_isFactor_smul`
- [**Theorem 474**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-covariance-iso) — Geometric Covariance as a von Neumann Algebra Isomorphism · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.localVonNeumannEquiv`

</details>

<details markdown="1">
<summary>§10.5.6 Relative Commutants of Nested Local Algebras (p. 294) — 8 items</summary>

- [**Definition 475**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:relative-commutant) — Relative Commutant of a Nested Pair · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.relativeCommutant`
- [**Theorem 476**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-antitone) — Antitonicity of the Commutant · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.commutant_le_commutant_of_le`
- [**Theorem 477**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-le-right) — Relative Commutant Lies in the Larger Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.relativeCommutant_le_right`
- [**Theorem 478**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-coe-commutant) — Relative Commutant Commutes with the Smaller Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.relativeCommutant_coe_subset_commutant`
- [**Theorem 479**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-center) — Relative Commutant Contains the Centre · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.center_le_relativeCommutant`
- [**Definition 480**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-inclusion) — Irreducible Inclusion · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsIrreducibleInclusion`
- [**Theorem 481**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-inclusion-factor) — An Irreducible Inclusion has Factor Ambient · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.isFactor_of_isIrreducibleInclusion`
- [**Theorem 482**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:self-inclusion-factor) — Self-Inclusion is Irreducible iff Factor · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.isIrreducibleInclusion_self_iff_isFactor`

</details>

<details markdown="1">
<summary>§10.5.7 Irreducibility and Schur's Lemma (p. 295) — 23 items</summary>

- [**Definition 483**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-representation) — Irreducible Representation · `Physicslib4.GNS.IsIrreducible`
- [**Theorem 484**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:schur-lemma) — Topological Schur Lemma · `Physicslib4.GNS.eq_smul_one_of_commute_of_cyclic`
- [**Theorem 485**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-scalar-iff) — Commutant Scalar iff Proportional Coefficient · `Physicslib4.GNS.isScalar_iff_coeff_proportional`
- [**Definition 486**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pure-state) — Pure State · `Physicslib4.GNS.IsPure`
- [**Theorem 487**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-implies-irreducible) — Pure Implies Irreducible · `Physicslib4.GNS.isIrreducible_of_isPure`
- [**Theorem 488**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-form-bound) — The GNS Radon–Nikodym Form is Bounded · `Physicslib4.GNS.gns_form_norm_le` (+1 more)
- [**Theorem 489**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-radon-nikodym-operator) — The GNS Radon–Nikodym Operator · `Physicslib4.GNS.rnOp` (+3 more)
- [**Theorem 490**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible) — Pure $$\iff$$ Irreducible · `Physicslib4.GNS.isPure_iff_isIrreducible`
- [**Theorem 491**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-factor) — An Irreducible Representation Generates a Factor · `Physicslib4.GNS.center_gnsVonNeumann_eq_of_isIrreducible`
- [**Theorem 492**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-generates-all) — Irreducibility $$\iff$$ Generating $$\mathcal{B}(H)$$ · `Physicslib4.GNS.isIrreducible_iff_gnsVonNeumann_eq_univ` (+1 more)
- [**Theorem 493**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-generates-all-bundled) — Bundled Density Form of Irreducibility · `Physicslib4.GNS.coe_gnsVonNeumannAlgebra_eq_univ_of_isIrreducible` (+1 more)
- [**Theorem 494**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-factor) — The GNS Representation of a Pure State is a Factor · `Physicslib4.GNS.exists_gns_factor_of_isPure`
- [**Theorem 495**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-generates-all) — The GNS Representation of a Pure State Generates $$\mathcal{B}(H)$$ · `Physicslib4.GNS.exists_gns_generates_all_of_isPure`
- [**Theorem 496**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:norm-positive-functional) — Norm of a Positive Functional · `Physicslib4.GNS.norm_eq_re_apply_one_of_positive`
- [**Definition 497**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:extreme-state) — Extreme Point of the State Space · `Physicslib4.GNS.State.IsExtremePoint`
- [**Theorem 498**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme) — Pure $$\iff$$ Extreme Point · `Physicslib4.GNS.isPure_iff_isExtremePoint`
- [**Theorem 499**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-space-convex-bridge) — State-Space Convexity and the Extreme-Point Bridge · `Physicslib4.GNS.convex_stateSpace` (+1 more)
- [**Definition 500**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:state-pullback) — Pullback of a State · `Physicslib4.GNS.State.comp`
- [**Theorem 501**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-pullback-functorial) — Functoriality of the State Pullback · `Physicslib4.GNS.State.comp_id` (+1 more)
- [**Theorem 502**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-pullback-invariant) — Purity is Invariant under a \*-Isomorphism · `Physicslib4.GNS.isPure_comp_iff`
- [**Theorem 503**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:state-space-weak-compact) — Weak-\* Compactness of the State Space · `Physicslib4.GNS.isCompact_weakStateSet`
- [**Theorem 504**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme-quasilocal) — Pure $$\iff$$ Extreme Point on the Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.pure_iff_extreme`
- [**Theorem 505**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible-quasilocal) — Pure $$\iff$$ Irreducible GNS on the Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.exists_gns_pure_iff_irreducible`

</details>

<details markdown="1">
<summary>§10.5.8 Unitary Equivalence and Superselection (p. 299) — 2 items</summary>

- [**Definition 506**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:unitary-equivalence) — Unitary Equivalence of Representations · `Physicslib4.GNS.UnitaryEquiv`
- [**Theorem 507**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:unitary-equiv-invariants) — Irreducibility and Factoriality are Unitary Invariants · `Physicslib4.GNS.UnitaryEquiv.isIrreducible_iff` (+1 more)

</details>

<details markdown="1">
<summary>§10.5.9 GNS Covariance (p. 299) — 6 items</summary>

- [**Lemma 508**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cyclic-pullback-surjective) — Cyclicity pulls back along a surjective \*-homomorphism · `Physicslib4.GNS.isCyclicVector_comp_of_surjective`
- [**Theorem 509**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance) — GNS covariance under a \*-isomorphism · `Physicslib4.GNS.exists_unitary_of_gns_comp`
- [**Theorem 510**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-unitary-equiv) — The GNS representation of a pullback state · `Physicslib4.GNS.unitaryEquiv_comp_of_gns`
- [**Lemma 511**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-image-invariants) — Pullback along a surjection preserves the image algebra · `Physicslib4.GNS.range_comp_of_surjective` (+2 more)
- [**Theorem 512**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-sector-transport) — Superselection type transports along a \*-isomorphism · `Physicslib4.GNS.isIrreducible_iff_of_gns_comp` (+1 more)
- [**Theorem 513**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-local) — GNS covariance for local algebras · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.unitaryEquiv_gns_covEquiv` (+2 more)

</details>

<details markdown="1">
<summary>§10.5.10 Disjointness and Quasi-Equivalence (p. 301) — 18 items</summary>

- [**Definition 514**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:disjoint-representations) — Disjoint Representations · `Physicslib4.GNS.AreDisjoint`
- [**Definition 515**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasi-equivalence) — Quasi-Equivalence of Representations · `Physicslib4.GNS.QuasiEquiv`
- [**Theorem 516**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-dichotomy) — Schur's Lemma and the Irreducible Dichotomy · `Physicslib4.GNS.UnitaryEquiv.of_intertwines_of_isIrreducible` (+1 more)
- [**Lemma 517**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:schur-multiplicity) — Schur Multiplicity · `Physicslib4.GNS.eq_smul_of_intertwines_of_isIrreducible`
- [**Lemma 518**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:endomorphism-scalar) — Endomorphism Algebra of an Irreducible Representation · `Physicslib4.GNS.intertwines_self_iff_isScalar`
- [**Theorem 519**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-von-neumann) — The commutant (self-intertwiner) von Neumann algebra · `Physicslib4.GNS.commutantVonNeumann` (+2 more)
- [**Theorem 520**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:double-commutant-duality) — Double-Commutant Duality · `Physicslib4.GNS.commutant_gnsVonNeumannAlgebra` (+1 more)
- [**Theorem 521**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:commutant-factor-duality) — A Factor and its Commutant; Triviality Duality · `Physicslib4.GNS.isFactor_gnsVonNeumann_iff_isFactor_commutant` (+1 more)
- [**Lemma 522**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-abelian-self-commuting) — Abelian $$\iff$$ Self-Commuting · `Physicslib4.GNS.isAbelian_iff_le_commutant`
- [**Definition 523**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-center) — Centre of a von Neumann algebra · `Physicslib4.GNS.vonNeumannCenter`
- [**Lemma 524**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-inter-is-von-neumann) — The centre is a von Neumann algebra · `Physicslib4.GNS.bicommutant_inter_commutant_eq`
- [**Lemma 525**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-inter-general) — The intersection of two von Neumann algebras is a von Neumann algebra · `Physicslib4.GNS.bicommutant_inter_eq`
- [**Theorem 526**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-center-abelian) — The centre of a von Neumann algebra is abelian · `Physicslib4.GNS.vonNeumannCenter_isAbelian`
- [**Lemma 527**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:von-neumann-center-eq-self-iff-abelian) — $$R$$ is abelian iff it equals its centre · `Physicslib4.GNS.vonNeumannCenter_eq_self_iff_isAbelian`
- [**Theorem 528**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:factor-abelian-iff-scalars) — A factor is abelian iff it is the scalars · `Physicslib4.GNS.isAbelian_iff_eq_scalars_of_isFactor`
- [**Theorem 529**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:center-eq-commutant-center) — A von Neumann algebra and its commutant share a centre · `Physicslib4.GNS.vonNeumannCenter_eq_commutant`
- [**Theorem 530**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:factor-iff-center-scalars) — A von Neumann algebra is a factor iff its centre is the scalars · `Physicslib4.GNS.isFactor_iff_center_eq_scalars`
- [**Theorem 531**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-state-dichotomy) — The Pure-State Dichotomy · `Physicslib4.GNS.exists_gns_areDisjoint_or_unitaryEquiv_of_isPure`

</details>

<details markdown="1">
<summary>§10.5.11 Direct Sums, Amplification, and Reducibility (p. 303) — 4 items</summary>

- [**Definition 532**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:direct-sum-representation) — Direct-Sum Representation · `Physicslib4.GNS.directSum`
- [**Theorem 533**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:direct-sum-subrepresentation) — Subrepresentations and Commutant of a Direct Sum · `Physicslib4.GNS.intertwines_single` (+1 more)
- [**Definition 534**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:amplification) — Amplification · `Physicslib4.GNS.amplification`
- [**Theorem 535**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:direct-sum-reducible) — Reducibility of a Direct Sum · `Physicslib4.GNS.not_isIrreducible_directSum`

</details>

<details markdown="1">
<summary>§10.5.12 Covariant States and the Covariance Action (p. 304) — 20 items</summary>

- [**Definition 536**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-state-family) — Covariant Family of Local States · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsCovariantFamily`
- [**Lemma 537**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:covariant-state-family-compose) — Composition of Covariance · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsCovariantFamily.comp`
- [**Definition 538**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:quasilocal-lift) — Quasilocal Covariance Automorphism · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.QuasilocalLift`
- [**Lemma 539**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-lift-unique) — Uniqueness of the Quasilocal Lift · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.QuasilocalLift.unique`
- [**Lemma 540**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-covariance-compatible) — Every Quasilocal Algebra is Covariance-Compatible · `Physicslib4.AQFT.HaagKastler.isCovariantQuasilocal`
- [**Theorem 541**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-lift-exists) — Existence of the Quasilocal Lift · `Physicslib4.AQFT.HaagKastler.nonempty_quasilocalLift`
- [**Theorem 542**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:quasilocal-lift-trivial) — Existence for the Trivial Net · `Physicslib4.AQFT.HaagKastler.nonempty_trivialQuasilocalLift`
- [**Definition 543**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-quasilocal-algebra) — Covariant Quasilocal Algebra · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.action`
- [**Lemma 544**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:quasilocal-action-coherence) — Group-Action Coherence of the Covariance Automorphism · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.action_one` (+1 more)
- [**Definition 545**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:invariant-state) — Invariant State · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState`
- [**Theorem 546**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:invariant-state-gns-unitary) — GNS Unitary Implementation of an Invariant State · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState.exists_gns_unitary`
- [**Theorem 547**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-covariant-representation) — Irreducible Covariant Representation of a Pure Invariant State · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsInvariantState.exists_gns_irreducible_covariant`
- [**Definition 548**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:positive-energy) — Positive Energy (bounded-generator scaffold) · `Physicslib4.AQFT.IsPositiveEnergy`
- [**Theorem 549**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:positive-energy-api) — Positive-Energy API · `Physicslib4.AQFT.isPositiveEnergy_const_refl` (+3 more)
- [**Definition 550**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:vacuum-state) — Vacuum State (generator-parameterised scaffold) · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumState`
- [**Theorem 551**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:vacuum-no-stone) — No-Stone Consequences of a Vacuum State · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumState.invariant` (+1 more)
- [**Definition 552**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-timelike-translation) — Future-Timelike Translation Subgroup · `Physicslib4.AQFT.HaagKastler.translationSub` (+3 more)
- [**Definition 553**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:vacuum-state-concrete) — Vacuum State with the Concrete Spectrum Condition · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsVacuumStateConcrete`
- [**Theorem 554**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:purity-covariance-invariant) — Purity is Covariance-Invariant · `Physicslib4.GNS.isPure_precomp_iff` (+1 more)
- [**Theorem 555**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-quasilocal-action) — GNS covariance along the quasilocal action · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.unitaryEquiv_gns_action` (+2 more)

</details>

<details markdown="1">
<summary>§10.5.13 The Separating Vector of a Faithful State (p. 307) — 1 item</summary>

- [**Theorem 556**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:separating-faithful) — Separating Vector of a Faithful State · `Physicslib4.GNS.separating_of_faithful` (+1 more)

</details>

<details markdown="1">
<summary>§10.5.14 The KMS Condition and Thermal Equilibrium (p. 308) — 10 items</summary>

- [**Definition 557**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:one-parameter-aut) — One-Parameter Automorphism Group · `Physicslib4.AQFT.IsOneParameterAut`
- [**Definition 558**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state) — KMS State · `Physicslib4.AQFT.IsKMSState`
- [**Theorem 559**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-convex) — The KMS State Set is Convex · `Physicslib4.AQFT.IsKMSState.convexCombo`
- [**Lemma 560**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:kms-correlation-one) — Boundary Coincidence for $$a = 1$$ · `Physicslib4.AQFT.IsKMSState.correlationOne`
- [**Definition 561**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:strip-liouville) — Strip-Liouville Principle · `Physicslib4.AQFT.StripLiouville`
- [**Theorem 562**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:strip-periodic-extension) — $$i\beta$$-Periodic Entire Extension (Strip Schwarz Reflection) · `Physicslib4.exists_bounded_entire_extension_of_strip_periodic`
- [**Theorem 563**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:strip-liouville-pos) — Strip-Liouville Holds for $$\beta > 0$$ · `Physicslib4.AQFT.stripLiouville_of_pos`
- [**Theorem 564**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-invariance) — KMS States are Invariant · `Physicslib4.AQFT.IsKMSState.invariant_of_pos`
- [**Theorem 565**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:strip-uniqueness) — Uniqueness on the Strip from Boundary Values · `Physicslib4.eqOn_strip_of_eq_boundary`
- [**Theorem 566**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-correlation-unique) — Uniqueness of the KMS Correlation Function · `Physicslib4.AQFT.IsKMSState.correlation_eqOn`

</details>

<details markdown="1">
<summary>§10.5.15 KMS States for the Covariance Flow (p. 309) — 5 items</summary>

- [**Definition 567**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:flow-aut-covariance) — Covariance-Flow Automorphism Family · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.flowAut`
- [**Lemma 568**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:one-parameter-aut-flow-covariance) — A Lorentz One-Parameter Subgroup Induces a One-Parameter Group · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.isOneParameterAut_flowAut`
- [**Definition 569**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state-for-flow-covariance) — KMS State for the Covariance Flow · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsKMSStateForFlow`
- [**Theorem 570**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-convex-for-flow-covariance) — Convexity of the Covariance-Flow KMS States · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsKMSStateForFlow.convexCombo`
- [**Definition 571**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:ground-state-for-flow-covariance) — Ground State for a Covariance Flow · `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsGroundStateForFlow` (+2 more)

</details>


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Spacetime](sec10-4-spacetime.html) · **§10.5 Minkowski** · [§10.6 Curved](sec10-6-curved.html) · [§10.7 Covariance](sec10-7-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.4 Spacetime](sec10-4-spacetime.html) · [§10.6 Curved](sec10-6-curved.html) →
