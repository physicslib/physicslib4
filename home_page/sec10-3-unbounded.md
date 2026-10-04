---
title: "§10.3 Unbounded Spectral Theorems (pp. 155–247)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · **§10.3 Unbounded** · [§10.4 Stone](sec10-4-stone.html) · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.2 Spectral](sec10-2-spectral.html) · [§10.4 Stone](sec10-4-stone.html) →

# §10.3 Unbounded Spectral Theorems (pp. 155–247)

121 declarations (items 164–286, together with Conventions 211 and 258), extending §10.2 to the Spectral Theorem for Unbounded, Self-Adjoint Operators (Theorem 283) and the functional calculus it supplies. The blueprint motivates this with the few genuinely unbounded self-adjoint operators that arise in AQFT, the momentum operator being the standard example. The section reuses §10.2 without restating it, follows the same Hall presentation, and builds up unbounded operators from scratch. Its single subsection, §10.3.1 Spectral Theorem: Unbounded Self-Adjoint Operators (p. 156), proceeds in six stages.

- *Unbounded operators (pp. 156–180, items 164–210).* Unbounded operators (Definition 164), their adjoints (Definition 168, Propositions 169–170, Lemma 171), symmetric operators, extensions and self-adjointness (Definitions 172–173 and 175, Proposition 174), and closed and closable operators via the graph in $$\mathbf{H} \times \mathbf{H}$$ (Definitions 176 and 179, Proposition 180), with the closure of a symmetric operator symmetric (Lemma 181) and essential self-adjointness defined (Definition 182). Elementary properties follow: symmetric operators are closable (Proposition 184), the adjoint of a closure (Proposition 185), uniqueness of the self-adjoint extension of an essentially self-adjoint operator (Proposition 188), and kernel and range, with the orthogonal complement of the range equal to the kernel of the adjoint (Definitions 189–190, Proposition 193). Next come the resolvent set and spectrum of an unbounded operator (Definition 197), which agree with the bounded notions (Lemma 199) and are real for self-adjoint operators (Theorem 201). The layer closes with criteria for essential self-adjointness: dense range (Theorem 202), and, through Hilbert direct sums and internal orthogonal decompositions (Definitions 203, 205 and 206, Lemmas 204 and 208), direct sums of bounded self-adjoint operators (Propositions 209–210).
- *Integration against a projection-valued measure (p. 181, items 211–238).* Under standing hypotheses (Convention 211), and with sesquilinear and quadratic forms on subspaces (Definitions 214–215) and the needed measure theory (Theorems 218–219, Propositions 220–224, Definition 222), the integral of an unbounded measurable function against a projection-valued measure is constructed on its natural domain (Propositions 230 and 232). It coincides with the bounded integral of §10.2 (Proposition 233), ignores null sets (Lemma 234), is the limit of its truncations (Lemma 235), and is self-adjoint for real-valued functions (Proposition 238).
- *Bounded normal operators (p. 199, items 239–257).* For normal operators (Definition 239) the norm equals the spectral radius (Proposition 244). Spectral subspaces (Definition 245, Propositions 246–247) and almost eigenvectors (Definition 249, Lemmas 248 and 250–254) lead to the two-variable spectral mapping theorem for polynomials in $$A$$ and $$A^*$$ (Theorem 255, Corollary 256), and hence to the continuous functional calculus for a normal operator (Theorem 257). Lemma 251 is stated with a constant uniform over all eigenvalues $$\lvert \lambda \rvert \le R$$, which is what the proof of Theorem 255 consumes; the Lean proof of Theorem 255 itself takes a shorter route through Mathlib's continuous functional calculus (`cfc_map_spectrum`), as a formalization note in the blueprint records, while the almost-eigenvector lemmas are formalised in their own right.
- *From a continuous functional calculus to a projection-valued measure (p. 213, items 258–272).* Under standing hypotheses (Convention 258), an abstract continuous functional calculus (Definition 259) is extended, through its associated measures (Definition 261), to bounded measurable functions (Definition 264). The extension is linear, multiplicative and compatible with conjugation (Lemmas 265 and 269, Proposition 268), and it yields a projection-valued measure (Theorem 270). Combined with the previous stage, this gives the Spectral Theorem for Bounded Normal Operators (Theorem 272).
- *The Cayley transform and the unbounded spectral theorem (pp. 222–231, items 273–283).* Unitary operators are normal, with spectrum on the unit circle (Lemmas 273–274). The Cayley map (Lemma 275) and the Cayley transform of a self-adjoint operator (Theorem 276), with its spectral mapping (Lemma 277), reduce the unbounded self-adjoint case to the bounded normal one: a projection-valued measure is transported along a Borel bijection (Lemma 279), the Cayley transform omits the point $$1$$ (Lemma 280), and the spectral measure is transported through the Cayley transform (Theorem 282). The result is the Spectral Theorem for Unbounded, Self-Adjoint Operators (Theorem 283).
- *The functional calculus of an unbounded self-adjoint operator (p. 234, items 284–286).* Added for §10.4 and not yet formalised. The spectral measure of a self-adjoint operator is named (Definition 284), the functional calculus $$f(A)$$ is the integral of $$f$$ against it (Definition 285), and for bounded $$f$$ it agrees with the bounded calculus of §10.2 (Lemma 286). Earlier in the section, a self-adjoint operator is shown to have no proper symmetric extension (Lemma 187), which §10.4 uses to identify the generator of $$e^{itA}$$ with $$A$$.

**Where the Lean lives:** `Physicslib4/Spectral/Unbounded/` (`Basic`, `Spectrum`, `DirectSum`, `Integral`, `Normal`, `AbstractCalculus`, `Cayley`)

## Items

Each blueprint subsection below is collapsed; click a heading to see its items. Every entry links to its node in the web blueprint and names the principal Lean declaration.

<details markdown="1">
<summary>§10.3.1 · Unbounded Operators › Adjoint and Closure of an Unbounded Operator (p. 156) — 19 items</summary>

- [**Definition 164**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-3.1) — Unbounded Operator · `LinearPMap` (+1 more)
- [**Proposition 165**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:convergence-facts) — Convergence Facts for Sequences and Series · `tendsto_atTop_ciSup` (+6 more)
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

</details>

<details markdown="1">
<summary>§10.3.1 · Unbounded Operators › Elementary Properties of Adjoints and Closed Operators (p. 163) — 14 items</summary>

- [**Definition 183**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:closed-linear-map-on-a-subspace) — Closed Linear Map on a Subspace · `LinearPMap.IsClosed` (+1 more)
- [**Proposition 184**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.8) — Closedness of the Adjoint's Graph; Closability of Symmetric Operators · `Physicslib4.Spectral.Unbounded.isClosable_of_isSymmetric` (+1 more)
- [**Proposition 185**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.10) — The Adjoint of a Closure · `Physicslib4.Spectral.Unbounded.adjoint_closure_eq_adjoint`
- [**Lemma 186**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:extension-reverses-adjoint-domains) — Extension Reverses Adjoint Domains · `Physicslib4.Spectral.Unbounded.adjoint_le_adjoint_of_le`
- [**Lemma 187**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:self-adjoint-maximally-symmetric) — A Self-Adjoint Operator has no Proper Symmetric Extension *(not yet formalised)*
- [**Proposition 188**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.11) — Uniqueness of the Self-Adjoint Extension of an Essentially Self-Adjoint Operator · `Physicslib4.Spectral.Unbounded.existsUnique_isSelfAdjoint_extension` (+1 more)
- [**Definition 189**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:kernel-of-an-unbounded-operator) — Kernel of an Unbounded Operator · `Physicslib4.Spectral.Unbounded.ker`
- [**Definition 190**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:range-of-an-unbounded-operator) — Range of an Unbounded Operator · `Physicslib4.Spectral.Unbounded.range`
- [**Proposition 191**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.49) — Orthogonal Decomposition and the Double Complement · `Physicslib4.Spectral.Unbounded.existsUnique_add_mem_orthogonal` (+1 more)
- [**Corollary 192**](blueprint/chptr-haag-kastler-axioms-blueprint.html#crllr:trivial-complement-characterizes-density) — Trivial Complement Characterizes Density · `Physicslib4.Spectral.Unbounded.dense_iff_orthogonal_eq_bot`
- [**Proposition 193**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.12) — Orthogonal Complement of the Range · `Physicslib4.Spectral.Unbounded.orthogonal_range_eq_ker_adjoint`
- [**Proposition 194**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.13) — Adjoint of a Sum with a Bounded Operator · `Physicslib4.Spectral.Unbounded.adjoint_add_toPMap` (+1 more)
- [**Lemma 195**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:adjoint-of-scalar-multiple-of-identity) — Adjoint of a Scalar Multiple of the Identity · `Physicslib4.Spectral.Unbounded.adjoint_smul_id`
- [**Proposition 196**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.14) — Closedness of the Range from a Lower Bound · `Physicslib4.Spectral.Unbounded.isClosed_range_subSmul`

</details>

<details markdown="1">
<summary>§10.3.1 · Unbounded Operators › The Spectrum of an Unbounded Operator (p. 170) — 5 items</summary>

- [**Definition 197**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-9.16) — Resolvent Set and Spectrum of an Unbounded Operator · `Physicslib4.Spectral.Unbounded.pmapResolventSet` (+2 more)
- [**Lemma 198**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:uniqueness-of-resolvent) — Uniqueness of the Resolvent · `Physicslib4.Spectral.Unbounded.existsUnique_isResolvent`
- [**Lemma 199**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spectrum-notions-agree) — The Two Notions of Spectrum Agree for Bounded Operators · `Physicslib4.Spectral.Unbounded.pmapResolventSet_toPMap_top` (+1 more)
- [**Lemma 200**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:b-squared-inequality-symmetric) — The $$b^2$$ Inequality for Symmetric Operators · `Physicslib4.Spectral.Unbounded.sq_norm_le_of_isSymmetric`
- [**Theorem 201**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-9.17) — Spectrum of a Self-Adjoint Operator is Real · `Physicslib4.Spectral.Unbounded.pmapSpectrum_subset_real`

</details>

<details markdown="1">
<summary>§10.3.1 · Unbounded Operators › Conditions for Self-Adjointness and Essential Self-Adjointness (p. 172) — 9 items</summary>

- [**Theorem 202**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-9.21) — Essential Self-Adjointness via Dense Range · `Physicslib4.Spectral.Unbounded.isEssentiallySelfAdjoint_iff_dense_range`
- [**Definition 203**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-a.45) — Hilbert Space Direct Sum · `lp` (+1 more)
- [**Lemma 204**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:finite-direct-sum-dense) — The Finite Direct Sum is Dense · `Physicslib4.Spectral.Unbounded.dense_setOf_finite_support`
- [**Definition 205**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:unitary-operator) — Unitary Operator · `unitary` (+2 more)
- [**Definition 206**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:internal-orthogonal-decomposition) — Internal Orthogonal Decomposition · `Physicslib4.Spectral.Unbounded.IsInternalOrthogonalDecomposition`
- [**Proposition 207**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:polarization-identity) — Polarization Identity for the Inner Product · `inner_eq_sum_norm_sq_div_four` (+1 more)
- [**Lemma 208**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:internal-decomposition-unitary) — Internal Decompositions are Unitarily External Direct Sums · `Physicslib4.Spectral.Unbounded.hasSum_injective_of_isInternalOrthogonalDecomposition` (+2 more)
- [**Proposition 209**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.26) — Direct Sums of Bounded Self-Adjoint Operators · `Physicslib4.Spectral.Unbounded.isEssentiallySelfAdjoint_of_isDirectSumOperator` (+6 more)
- [**Proposition 210**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-9.26-internal) — Direct Sums of Bounded Self-Adjoint Operators, Internal Form · `Physicslib4.Spectral.Unbounded.isEssentiallySelfAdjoint_of_isInternalDirectSumOperator` (+6 more)

</details>

<details markdown="1">
<summary>§10.3.1 · Integration Against a Projection-Valued Measure (p. 181) — 28 items</summary>

- [**Convention 211**](blueprint/chptr-haag-kastler-axioms-blueprint.html#conv:section-integration) — Standing Hypotheses: Integration against a Projection-Valued Measure *(a standing convention, not a declaration; it carries no Lean annotation)*
- [**Lemma 212**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:associated-measure-total-mass) — The Associated Measure has Total Mass $$\left\| \psi \right\|^2$$ · `Physicslib4.Spectral.Unbounded.assoc_univ_eq` (+1 more)
- [**Lemma 213**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:norm-identity-bounded-integral) — Norm Identity for the Bounded Integral · `Physicslib4.Spectral.Unbounded.norm_sq_integral_apply`
- [**Definition 214**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-sesquilinear-form-on-a-subspace) — Sesquilinear Form on a Subspace · `Physicslib4.Spectral.Unbounded.SesquilinearFormOn`
- [**Definition 215**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-quadratic-form-on-a-subspace) — Quadratic Form on a Subspace · `Physicslib4.Spectral.Unbounded.IsQuadraticFormOn` (+2 more)
- [**Proposition 216**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:quadratic-forms-on-a-subspace-properties) — Properties of Quadratic Forms on a Subspace · `Physicslib4.Spectral.Unbounded.polarizationOn_eq_inner` (+1 more)
- [**Lemma 217**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:restriction-of-quadratic-form) — Restriction of a Quadratic Form to a Subspace · `Physicslib4.Spectral.Unbounded.isQuadraticFormOn_restrict` (+1 more)
- [**Theorem 218**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:monotone-convergence-theorem-for-integrals) — Monotone Convergence Theorem, for Integrals · `MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone` (+1 more)
- [**Theorem 219**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:dominated-convergence-theorem) — Dominated Convergence Theorem · `MeasureTheory.tendsto_integral_of_dominated_convergence` (+3 more)
- [**Proposition 220**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:additivity-of-the-integral-in-the-measure) — Linearity of the Integral in the Measure · `MeasureTheory.lintegral_add_measure` (+3 more)
- [**Proposition 221**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:monotonicity-of-the-integral-in-the-measure) — Monotonicity of the Integral in the Measure · `MeasureTheory.lintegral_mono'` (+1 more)
- [**Definition 222**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-a.46) — $$L^2$$ of a Measure Space · `MeasureTheory.MemLp` (+3 more)
- [**Proposition 223**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:countable-additivity-of-the-integral) — Countable Additivity of the Integral over a Disjoint Cover · `MeasureTheory.lintegral_iUnion` (+1 more)
- [**Proposition 224**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integrals-agree-when-measures-agree) — Integrals Agree when Measures Agree on a Set · `Physicslib4.Spectral.Unbounded.setLIntegral_congr_measure`
- [**Lemma 225**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:range-of-projection-is-kernel) — The Range of a Projection is the Kernel of its Complement · `Physicslib4.Spectral.Unbounded.range_eq_ker_one_sub` (+2 more)
- [**Lemma 226**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:closed-subspace-is-hilbert) — A Closed Subspace is a Separable Hilbert Space · `Physicslib4.Spectral.Unbounded.completeSpace_and_separableSpace_of_isClosed` (+2 more)
- [**Lemma 227**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:range-membership-concentrates-measure) — Range Membership Concentrates the Associated Measure · `Physicslib4.Spectral.Unbounded.assoc_compl_eq_zero` (+1 more)
- [**Lemma 228**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:norm-convergent-decomposition) — Norm-Convergent Decomposition over a Disjoint Cover · `Physicslib4.Spectral.Unbounded.hasSum_apply_of_partition` (+1 more)
- [**Lemma 229**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:l2-implies-l1) — $$L^2$$ Implies $$L^1$$ on a Finite Measure Space · `MeasureTheory.MemLp.integrable` (+1 more)
- [**Proposition 230**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.2) — Properties of the Integral against a Projection-Valued Measure · `Physicslib4.Spectral.Unbounded.integralDomain` (+7 more)
- [**Lemma 231**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bounded-on-set-range-in-domain) — Bounded on a Set Implies the Range Lies in the Domain · `Physicslib4.Spectral.Unbounded.range_subset_integralDomain` (+1 more)
- [**Proposition 232**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.1) — The Integral against a Projection-Valued Measure · `Physicslib4.Spectral.Unbounded.pmapIntegral` (+5 more)
- [**Proposition 233**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:coincidence-with-the-bounded-integral) — Coincidence with the Bounded Integral · `Physicslib4.Spectral.Unbounded.integralDomain_eq_top_of_bddMeasurable` (+1 more)
- [**Lemma 234**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:integral-ignores-null-sets) — The Integral Ignores Null Sets · `Physicslib4.Spectral.Unbounded.integralDomain_congr_of_null` (+1 more)
- [**Lemma 235**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:truncations-converge) — Truncations Converge to the Unbounded Integral · `Physicslib4.Spectral.Unbounded.tendsto_integral_truncation`
- [**Lemma 236**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:associated-measure-of-image) — The Associated Measure of a Bounded-Calculus Image · `Physicslib4.Spectral.Unbounded.assoc_integral_apply` (+1 more)
- [**Lemma 237**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:integral-preserves-spectral-subspaces) — The Integral Preserves Spectral Subspaces on which the Integrand is Bounded · `Physicslib4.Spectral.Unbounded.mapsTo_pmapIntegral_range` (+1 more)
- [**Proposition 238**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.3) — The Integral of a Real-Valued Function is Self-Adjoint · `Physicslib4.Spectral.Unbounded.isSelfAdjoint_pmapIntegral_of_real`

</details>

<details markdown="1">
<summary>§10.3.1 · The Spectral Theorem for Bounded Normal Operators (p. 199) — 6 items</summary>

- [**Definition 239**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.19) — Normal Operator · `IsStarNormal`
- [**Lemma 240**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:self-adjoint-is-normal) — Bounded Self-Adjoint Operators are Normal · `IsSelfAdjoint.isStarNormal`
- [**Lemma 241**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:power-growth-controlled-by-spectral-radius) — Power Growth is Controlled by the Spectral Radius · `Physicslib4.Spectral.Unbounded.tendsto_norm_pow_div_atTop`
- [**Lemma 242**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.22) — Spectral Radius of a Product of Commuting Operators · `Physicslib4.Spectral.Unbounded.spectralRadius_mul_le_of_commute`
- [**Lemma 243**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:adjoint-product-and-involution) — Adjoint of a Product; the Adjoint is an Involution · `ContinuousLinearMap.adjoint_comp` (+1 more)
- [**Proposition 244**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.21) — Norm Equals Spectral Radius for Normal Operators · `IsStarNormal.spectralRadius_eq_nnnorm`

</details>

<details markdown="1">
<summary>§10.3.1 · The Spectral Theorem for Bounded Normal Operators › Spectral Subspaces (p. 203) — 3 items</summary>

- [**Definition 245**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-7.14) — Spectral Subspaces · `Physicslib4.Spectral.Unbounded.spectralSubspace`
- [**Proposition 246**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.15) — Properties of Spectral Subspaces · `Physicslib4.Spectral.Unbounded.pvmOperator` (+3 more)
- [**Proposition 247**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.16) — Commuting Operators Preserve Spectral Subspaces · `Physicslib4.Spectral.Unbounded.commute_borelCalculus` (+1 more)

</details>

<details markdown="1">
<summary>§10.3.1 · The Spectral Theorem for Bounded Normal Operators › Almost Eigenvectors (p. 206) — 7 items</summary>

- [**Lemma 248**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:normality-balances-norms) — Normality Balances the Two Norms · `Physicslib4.Spectral.Unbounded.norm_adjoint_sub_smul_apply`
- [**Definition 249**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.24) — $$\varepsilon$$-Almost Eigenvector · `Physicslib4.Spectral.Unbounded.IsAlmostEigenvector`
- [**Lemma 250**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.25) — Almost Eigenvectors and the Spectrum of a Normal Operator · `Physicslib4.Spectral.Unbounded.isAlmostEigenvector_adjoint` (+1 more)
- [**Lemma 251**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.26) — Polynomials Preserve Almost Eigenvectors · `Physicslib4.Spectral.Unbounded.exists_const_isAlmostEigenvector_mvApply_uniform` (+1 more)
- [**Lemma 252**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:polynomials-in-normal-are-normal) — Polynomials in a Normal Operator are Normal · `Physicslib4.Spectral.Unbounded.mvApply` (+4 more)
- [**Lemma 253**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:restriction-of-normal-operator) — Restriction of a Normal Operator to a Doubly Invariant Subspace · `Physicslib4.Spectral.Unbounded.exists_restrict_isStarNormal`
- [**Lemma 254**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.27) — An Almost-Eigenvector Subspace for a Polynomial in a Normal Operator · `Physicslib4.Spectral.Unbounded.exists_subspace_isAlmostEigenvector`

</details>

<details markdown="1">
<summary>§10.3.1 · The Spectral Theorem for Bounded Normal Operators › The Two-Variable Spectral Mapping Theorem (p. 210) — 2 items</summary>

- [**Theorem 255**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.23) — Spectral Mapping for Polynomials in $$A$$ and $$A^*$$ · `Physicslib4.Spectral.Unbounded.spectrum_mvApply`
- [**Corollary 256**](blueprint/chptr-haag-kastler-axioms-blueprint.html#crllr:norm-of-polynomial-in-a-astar) — Norm of a Polynomial in $$A$$ and $$A^*$$ · `Physicslib4.Spectral.Unbounded.norm_mvApply`

</details>

<details markdown="1">
<summary>§10.3.1 · The Spectral Theorem for Bounded Normal Operators › The Continuous Functional Calculus for a Normal Operator (p. 212) — 1 item</summary>

- [**Theorem 257**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:continuous-functional-calculus-normal) — Continuous Functional Calculus for a Normal Operator · `Physicslib4.Spectral.Unbounded.mvPolyOn` (+9 more)

</details>

<details markdown="1">
<summary>§10.3.1 · From a Continuous Functional Calculus to a Projection-Valued Measure (p. 213) — 14 items</summary>

- [**Convention 258**](blueprint/chptr-haag-kastler-axioms-blueprint.html#conv:section-abstract) — Standing Hypotheses: The Abstract Functional Calculus *(a standing convention, not a declaration; it carries no Lean annotation)*
- [**Definition 259**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:abstract-continuous-functional-calculus) — Abstract Continuous Functional Calculus · `Physicslib4.Spectral.Unbounded.IsAbstractCalculus`
- [**Lemma 260**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-calculus-non-negative) — An Abstract Calculus is Non-Negative · `Physicslib4.Spectral.Unbounded.isSelfAdjoint_of_real` (+2 more)
- [**Definition 261**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:abstract-associated-measures) — The Measures Associated to an Abstract Calculus · `Physicslib4.Spectral.Unbounded.abstractMeasure` (+2 more)
- [**Lemma 262**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-associated-measures-finite) — The Abstract Associated Measures are Finite · `Physicslib4.Spectral.Unbounded.abstractMeasure_univ`
- [**Proposition 263**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:abstract-extended-forms-are-bounded) — The Extended Forms are Bounded Quadratic Forms · `Physicslib4.Spectral.Unbounded.isBoundedQuadraticForm_abstractForm` (+3 more)
- [**Definition 264**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:abstract-extended-calculus) — The Extended Calculus · `Physicslib4.Spectral.Unbounded.extendedCalculus` (+2 more)
- [**Lemma 265**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-extended-linear) — The Extended Calculus is Linear · `Physicslib4.Spectral.Unbounded.extendedCalculus_smul_add`
- [**Lemma 266**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-extended-convergence) — Off-Diagonal Formula and Bounded Convergence for the Extended Calculus · `Physicslib4.Spectral.Unbounded.polarization_abstractForm` (+1 more)
- [**Lemma 267**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-extended-real-self-adjoint) — Real Functions Give Self-Adjoint Operators · `Physicslib4.Spectral.Unbounded.isSelfAdjoint_extendedCalculus_of_real`
- [**Proposition 268**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:abstract-extended-multiplicative) — The Extended Calculus is Multiplicative · `Physicslib4.Spectral.Unbounded.extendedCalculus_mul`
- [**Lemma 269**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:abstract-extended-conjugation) — The Extended Calculus Respects Conjugation · `Physicslib4.Spectral.Unbounded.extendedCalculus_conj`
- [**Theorem 270**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:abstract-calculus-yields-pvm) — A Continuous Functional Calculus Yields a Projection-Valued Measure · `Physicslib4.Spectral.Unbounded.abstractPVM` (+2 more)
- [**Corollary 271**](blueprint/chptr-haag-kastler-axioms-blueprint.html#crllr:abstract-extended-norm-bound) — The Extended Calculus is Norm-Bounded · `Physicslib4.Spectral.Unbounded.norm_extendedCalculus_le`

</details>

<details markdown="1">
<summary>§10.3.1 · From a Continuous Functional Calculus to a Projection-Valued Measure › The Spectral Theorem for Bounded Normal Operators (p. 220) — 1 item</summary>

- [**Theorem 272**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.20) — Spectral Theorem for Bounded Normal Operators · `Physicslib4.Spectral.Unbounded.existsUnique_spectralMeasure_normal` (+1 more)

</details>

<details markdown="1">
<summary>§10.3.1 · The Cayley Transform (p. 222) — 5 items</summary>

- [**Lemma 273**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:unitary-is-normal) — Unitary Operators are Normal · `Physicslib4.Spectral.Unbounded.unitary_mul_adjoint`
- [**Lemma 274**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:unitary-spectrum-circle) — The Spectrum of a Unitary Operator Lies on the Unit Circle · `spectrum.subset_circle_of_unitary` (+1 more)
- [**Lemma 275**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cayley-map) — The Cayley Map and its Inverse · `Physicslib4.Spectral.Unbounded.unitCircleMinusOne` (+9 more)
- [**Theorem 276**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.28) — Cayley Transform · `Physicslib4.Spectral.Unbounded.IsCayleyTransform` (+1 more)
- [**Lemma 277**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cayley-spectral-mapping) — Spectral Mapping for the Cayley Transform · `Physicslib4.Spectral.Unbounded.mem_spectrum_iff_cayleyMap_mem_spectrum` (+1 more)

</details>

<details markdown="1">
<summary>§10.3.1 · Proof of the Spectral Theorem for Unbounded Self-Adjoint Operators (p. 226) — 9 items</summary>

- [**Theorem 278**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:change-of-variables) — Change of Variables for a Pushforward Measure · `MeasureTheory.lintegral_map_equiv` (+1 more)
- [**Lemma 279**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:borel-bijection-transports-pvm) — A Borel Bijection Transports a Projection-Valued Measure · `Physicslib4.Spectral.Unbounded.restrictPVM` (+2 more)
- [**Lemma 280**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cayley-omits-one) — The Cayley Transform Omits the Point $$1$$ · `Physicslib4.Spectral.Unbounded.spectralMeasure_singleton_one_eq_zero`
- [**Proposition 281**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.29) — Spectral Subspaces of the Cayley Transform · `Physicslib4.Spectral.Unbounded.pmapIntegral_cayleyInv_eq`
- [**Theorem 282**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.30) — Transporting the Spectral Measure through the Cayley Transform · `Physicslib4.Spectral.Unbounded.cayleyPVM` (+1 more)
- [**Theorem 283**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.4) — Spectral Theorem for Unbounded, Self-Adjoint Operators · `Physicslib4.Spectral.Unbounded.existsUnique_spectralMeasure_unbounded` (+1 more)
- [**Definition 284**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spectral-measure) — Spectral Measure of a Self-Adjoint Operator *(not yet formalised)*
- [**Definition 285**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.5) — Functional Calculus for an Unbounded Self-Adjoint Operator *(not yet formalised)*
- [**Lemma 286**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:functional-calculus-bounded) — Functional Calculus of a Bounded Function *(not yet formalised)*

</details>


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · **§10.3 Unbounded** · [§10.4 Stone](sec10-4-stone.html) · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.2 Spectral](sec10-2-spectral.html) · [§10.4 Stone](sec10-4-stone.html) →
