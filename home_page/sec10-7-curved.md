---
title: "§10.7 Haag–Kastler Axioms in curved spacetime (pp. 327–337)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Stone](sec10-4-stone.html) · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · **§10.7 Curved** · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.8 Covariance](sec10-8-general-covariance.html) →

# §10.7 Haag–Kastler Axioms in curved spacetime (pp. 327–337)

49 items, Definitions 626–674. The axioms are restated for a Lorentzian spacetime: Local Algebras (Definition 626), Isotony (Definition 627, again supplying the family as chosen data with identity and composition laws), Local Commutativity (Definition 628, which now **consumes** the Axiom 2 family rather than choosing its own witnesses), local observables (Definition 629), Local Completeness (Definition 630), and Isometric Covariance (Definition 631, whose coherence condition, as in Minkowski, is stated for the Axiom 2 isotony family), bundled into a `HaagKastlerNet` in curved spacetime (Definition 632). The change to Axioms 2 and 3 has a visible consequence downstream: statements about nested regions have to factor a three-fold inclusion $$\mathbf{B}_1 \subseteq \mathbf{B}_2 \subseteq \mathbf{B}$$ inside a common containing algebra, and that factorisation is now the composition law of Axiom 2, so **the coherence hypotheses that earlier versions carried at each such site are gone**—curved isotony (Theorem 637) and the curved von Neumann net (Definition 639) are unconditional. An explicit hypothesis remains only where the abstract interface genuinely cannot supply it, namely basis-set preservation in Geometric Covariance (Theorem 643), discharged for nets arising from a concrete geometric spacetime; the coherence of the stabiliser action with the isotony embeddings is no longer a hypothesis there, being condition (3) of Axiom 5 transported along $$g \cdot \mathbf{B} = \mathbf{B}$$.

- *§10.7.1 Einstein Causality in Curved Spacetime (p. 329, item 633).* The operator form of local commutativity, expressed in a representation of a common containing local algebra rather than of a global quasilocal algebra (Theorem 633).
- *§10.7.2 Local von Neumann Algebras in Curved Spacetime (p. 329, items 634–645).* The Minkowski development of §10.6.5 mirrored relative to a containing region: the local von Neumann algebra of a subregion and its bundled registration (Definitions 634–635), Microcausality (Theorem 636), unconditional Isotony (Theorem 637), the bundled form (Theorem 638), the net as an order-preserving map on the poset of subregions (Definition 639), Statistical Independence in set-level and bundled forms (Theorems 640–641), additive-free locality (Theorem 642), and Geometric Covariance via the stabiliser GNS representation (Theorem 643) with orbit-invariance of factoriality (Theorem 644) and the upgrade to a \*-algebra isomorphism (Theorem 645).
- *§10.7.3 Relative Commutants of Nested Local Algebras in Curved Spacetime (p. 332, items 646–654).* The curved counterpart of §10.6.6: the relative commutant of a nested pair inside a containing region (Definition 646), its containment in the larger algebra, commutation with the smaller, and containment of the centre (Theorems 647–649), irreducible inclusions (Definition 650) and their consequences (Theorems 651–652), plus the abelian/centre facts specialised to curved local algebras (Theorems 653–654).
- *§10.7.4 Purity of States on Local Algebras in Curved Spacetime (p. 333, items 655–659).* Each local algebra is a unital C\*-algebra with its own state space, so the abstract purity characterisations are registered per region: Pure $$\iff$$ Extreme Point (Theorem 655), Pure $$\iff$$ Irreducible GNS (Theorem 656), the GNS representation of a pure state generates a factor and indeed all of $$\mathcal{B}(H)$$ (Theorem 657), the Irreducible Dichotomy for a curved local algebra (Theorem 658), and GNS covariance for curved local algebras (Theorem 659).
- *§10.7.5 Covariant States in Curved Spacetime (p. 334, items 660–661).* Covariant families of local states in curved spacetime (Definition 660) and their composition law (Lemma 661).
- *§10.7.6 The Stabilizer GNS Unitary in Curved Spacetime (p. 334, items 662–668).* Since no quasilocal algebra exists on a generic Lorentzian spacetime, the covariance action restricts to the stabiliser subgroup $$\mathrm{Stab}(\mathbf{B})$$ of a region, giving automorphisms of the single local algebra $$\mathfrak{U}(\mathbf{B})$$ (Definition 662) that form a genuine group action (Lemma 663). A stabiliser-invariant state carries a unitary GNS representation of $$\mathrm{Stab}(\mathbf{B})$$ (Theorem 664), strongly continuous when the matrix coefficients are continuous (Theorem 665); a state both stabiliser-invariant and pure yields an irreducible covariant representation (Theorem 666); purity is invariant under the stabiliser action (Theorem 667), and GNS data transports along it (Theorem 668).
- *§10.7.7 KMS States for a Killing Flow (p. 336, items 669–674).* Killing flows are identified as one-parameter subgroups of the stabiliser of a region, inducing a one-parameter automorphism group on $$\mathfrak{U}(\mathbf{B})$$ (Definition 669, Lemma 670). KMS states for a Killing flow (Definition 671) are the precise algebraic sense in which the Hartle–Hawking and Gibbons–Hawking states are thermal. Such a state at positive inverse temperature automatically carries a strongly continuous one-parameter unitary group on its GNS Hilbert space implementing the flow, yielding the curved-spacetime thermal representation—the analogue of the Minkowski vacuum representation (Theorem 672); these states form a convex set (Theorem 673), and the corresponding ground state is recorded alongside them (Definition 674).

**Where the Lean lives:** `Physicslib4/AQFT/HaagKastlerCurved/` (`LocalVonNeumann`, `StabilizerAction`, `StabilizerKMS`, `Purity`, `GeometricCovariance`, …)

## Items

Every entry links to its node in the web blueprint and names the principal Lean declaration.


### §10.7 The axioms (p. 327)

- [**Definition 626**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-algebras-in-curved-spacetime) — Axiom 1: Local Algebras · `Physicslib4.AQFT.HaagKastlerCurved.LocalNet`
- [**Definition 627**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isotony-in-curved-spacetime) — Axiom 2: Isotony · `Physicslib4.AQFT.HaagKastlerCurved.Isotony`
- [**Definition 628**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-commutativity-in-curved-spacetime) — Axiom 3: Local Commutativity · `Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity`
- [**Definition 629**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-observable) — Local Observable · `Physicslib4.AQFT.HaagKastlerCurved.IsLocalObservable`
- [**Definition 630**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-completeness-in-curved-spacetime) — Axiom 4: Local Completeness · `Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebra`
- [**Definition 631**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isometric-covariance-in-curved-spacetime) — Axiom 5: Isometric Covariance · `Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance` *(implemented via the explicitly orientation-preserving subgroup — see [Formalisation status](./#formalisation-status))*
- [**Definition 632**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:haag-kastler-net-in-curved-spacetime) — Haag–Kastler Net in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet`

### §10.7.1 Einstein Causality in Curved Spacetime (p. 329)

- [**Theorem 633**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:einstein-causality-in-curved-spacetime) — Einstein Causality in a Representation (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.einstein_causality` (+1 more)

### §10.7.2 Local von Neumann Algebras in Curved Spacetime (p. 329)

- [**Definition 634**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-in-curved-spacetime) — Local von Neumann Algebra in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localOperators` (+1 more)
- [**Definition 635**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:local-von-neumann-algebra-in-curved-spacetime) — $$R(\mathbf{B}')$$ as a von Neumann Algebra (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra`
- [**Theorem 636**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-microcausality-in-curved-spacetime) — Microcausality at the von Neumann Level (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_subset_centralizer`
- [**Theorem 637**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-isotony-in-curved-spacetime) — Isotony of the von Neumann Net (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_mono`
- [**Theorem 638**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-bundled-order-in-curved-spacetime) — Bundled von Neumann Microcausality and Isotony (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_le_commutant` (+1 more)
- [**Definition 639**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:von-neumann-net-in-curved-spacetime) — The Net of von Neumann Algebras in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.vonNeumannNet`
- [**Theorem 640**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-in-curved-spacetime) — Statistical Independence (Schlieder Property) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_separating` (+1 more)
- [**Theorem 641**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:statistical-independence-bundled-in-curved-spacetime) — Statistical Independence, bundled (curved spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_separating`
- [**Theorem 642**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:additive-free-locality-in-curved-spacetime) — Additive-Free Locality via the Spacelike Complement (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric`
- [**Theorem 643**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-geometric-covariance-in-curved-spacetime) — Geometric Covariance of the von Neumann Net (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.lieConj_image_localVonNeumann` (+2 more)
- [**Theorem 644**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-factor-orbit-in-curved-spacetime) — Orbit-Invariance of Factoriality (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumann_isFactor_smul`
- [**Theorem 645**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:von-neumann-covariance-iso-in-curved-spacetime) — Geometric Covariance as a von Neumann Algebra Isomorphism (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannEquiv`

### §10.7.3 Relative Commutants of Nested Local Algebras in Curved Spacetime (p. 332)

- [**Definition 646**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:relative-commutant-in-curved-spacetime) — Relative Commutant of a Nested Pair (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant`
- [**Theorem 647**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-le-right-in-curved-spacetime) — Relative Commutant Lies in the Larger Algebra (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant_le_right`
- [**Theorem 648**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-coe-commutant-in-curved-spacetime) — Relative Commutant Commutes with the Smaller Algebra (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.relativeCommutant_coe_subset_commutant`
- [**Theorem 649**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:relative-commutant-center-in-curved-spacetime) — Relative Commutant Contains the Centre (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.center_le_relativeCommutant`
- [**Definition 650**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:irreducible-inclusion-in-curved-spacetime) — Irreducible Inclusion (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsIrreducibleInclusion`
- [**Theorem 651**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-inclusion-factor-in-curved-spacetime) — An Irreducible Inclusion has Factor Ambient (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isFactor_of_isIrreducibleInclusion`
- [**Theorem 652**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:self-inclusion-factor-in-curved-spacetime) — Self-Inclusion is Irreducible iff Factor (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isIrreducibleInclusion_self_iff_isFactor`
- [**Theorem 653**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:abelian-local-von-neumann-in-curved-spacetime) — Abelian Local von Neumann Algebras (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_center_isAbelian` (+1 more)
- [**Theorem 654**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:center-duality-local-von-neumann-in-curved-spacetime) — Centre Duality for Local von Neumann Algebras (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.localVonNeumannAlgebra_center_eq_commutant` (+1 more)

### §10.7.4 Purity of States on Local Algebras in Curved Spacetime (p. 333)

- [**Theorem 655**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-extreme-in-curved-spacetime) — Pure $$\iff$$ Extreme Point on a Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.pure_iff_extreme`
- [**Theorem 656**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-iff-irreducible-in-curved-spacetime) — Pure $$\iff$$ Irreducible GNS on a Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_pure_iff_irreducible`
- [**Theorem 657**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pure-factor-generates-in-curved-spacetime) — Pure GNS on a Local Algebra is a Factor Generating $$\mathcal{B}(H)$$ · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_factor_of_isPure` (+1 more)
- [**Theorem 658**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-dichotomy-in-curved-spacetime) — The Irreducible Dichotomy for a Curved Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.areDisjoint_or_unitaryEquiv_of_isIrreducible`
- [**Theorem 659**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-local-in-curved-spacetime) — GNS covariance for curved local algebras · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.unitaryEquiv_gns_covEquiv` (+2 more)

### §10.7.5 Covariant States in Curved Spacetime (p. 334)

- [**Definition 660**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:covariant-state-family-in-curved-spacetime) — Covariant Family of Local States in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsCovariantFamily`
- [**Lemma 661**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:covariant-state-family-compose-in-curved-spacetime) — Composition of Covariance in Curved Spacetime · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsCovariantFamily.comp`

### §10.7.6 The Stabiliser GNS Unitary in Curved Spacetime (p. 334)

- [**Definition 662**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:stabilizer-action-in-curved-spacetime) — Stabiliser Action on a Local Algebra · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.stabAut`
- [**Lemma 663**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:stabilizer-action-laws-in-curved-spacetime) — The Stabiliser Action is a Group Action · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.stabAut_one` (+1 more)
- [**Theorem 664**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-unitary-stabilizer-in-curved-spacetime) — GNS Unitary Representation of the Stabiliser · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_unitary_stabilizer`
- [**Theorem 665**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-unitary-stabilizer-strongly-continuous-in-curved-spacetime) — Strongly Continuous Stabiliser GNS Unitary · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_unitary_stabilizer_strongContinuous`
- [**Theorem 666**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:irreducible-covariant-representation-in-curved-spacetime) — Irreducible Covariant Representation of a Pure Invariant State (Curved Spacetime) · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_irreducible_covariant_stabilizer`
- [**Theorem 667**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:purity-covariance-invariant-in-curved-spacetime) — Purity is Invariant under the Stabiliser Action · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isPure_precomp_stabAut_iff`
- [**Theorem 668**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-covariance-stabilizer-action) — GNS covariance along the stabiliser action · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.unitaryEquiv_gns_stabAut` (+2 more)

### §10.7.7 KMS States for a Killing Flow (p. 336)

- [**Definition 669**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:flow-aut-in-curved-spacetime) — Killing-Flow Automorphism Family · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.flowAut`
- [**Lemma 670**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:one-parameter-aut-flow-in-curved-spacetime) — A Killing Flow Induces a One-Parameter Group · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.isOneParameterAut_flowAut`
- [**Definition 671**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kms-state-for-flow-in-curved-spacetime) — KMS State for a Killing Flow · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow`
- [**Theorem 672**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-thermal-representation-in-curved-spacetime) — The Killing-Flow KMS Thermal Representation · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow.exists_gns_unitary_strongContinuous`
- [**Theorem 673**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:kms-convex-for-flow-in-curved-spacetime) — Convexity of the Killing-Flow KMS States · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsKMSStateForFlow.convexCombo`
- [**Definition 674**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:ground-state-for-flow-in-curved-spacetime) — Ground State for a Killing Flow · `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsGroundStateForFlow` (+2 more)


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Stone](sec10-4-stone.html) · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · **§10.7 Curved** · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.8 Covariance](sec10-8-general-covariance.html) →
