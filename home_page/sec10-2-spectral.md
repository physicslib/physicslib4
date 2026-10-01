---
title: "§10.2 Spectral Theorems (pp. 38–155)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · **§10.2 Spectral** · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Spacetime](sec10-4-spacetime.html) · [§10.5 Minkowski](sec10-5-haag-kastler.html) · [§10.6 Curved](sec10-6-curved.html) · [§10.7 Covariance](sec10-7-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.1 GNS](sec10-1-gns.html) · [§10.3 Unbounded](sec10-3-unbounded.html) →

# §10.2 Spectral Theorems (pp. 38–155)

The largest section by declaration count (144 declarations, items 19–163, together with Convention 22), stating and proving the Spectral Theorem for Bounded, Self-Adjoint Operators (Theorem 162), a result the blueprint describes as sitting at the core of much of AQFT. It follows the presentation of Hall's *Quantum Theory for Mathematicians*. Standard results whose proofs lie outside the development — Heine–Borel, Riesz representation, Stone–Weierstrass, bounded convergence and the like — are stated in full but not proved in the prose, and are formalised all the same, usually directly by the corresponding Mathlib declaration. The whole section is a single subsection, §10.2.1 Spectral Theorem: Bounded Self-Adjoint Operators (p. 38), which proceeds in six layers.

- *Elementary properties of bounded operators (pp. 39–45, items 19–37).* Fixes the inner product, the induced norm and the bounded-operator notation (Definitions 19–21), the standing convention that the Hilbert space is non-zero (Convention 22), the identity operator, indicator functions and orthogonal complements (Definitions 23–26), and basic facts about integrals, Cauchy–Schwarz, the reverse triangle inequality and continuity of the norm and inner product (Propositions 27–30). $$\mathcal{B}(\mathbf{H})$$ is a Banach space (Lemma 31); bounded inverses, the resolvent and the spectrum are defined (Definitions 32–33); and the Riesz theorem (Theorem 34) yields the adjoint of a bounded operator (Definition 35), which is bounded (Proposition 36) and has the expected algebraic properties (Lemma 37).
- *Projection-valued measures (p. 45, items 38–67).* Orthogonal projections (Definition 38, Lemma 39) and projection-valued measures (Definition 40), with their associated scalar measures (Theorem 41) and operator-valued integration of bounded measurable functions (Theorem 42). The integral is built from bounded sesquilinear and quadratic forms (Definitions 43–44) and the simple-function approximation theorem (Theorem 45): the quadratic form of a bounded measurable function is bounded (Lemma 46, Propositions 47–49), and a bounded quadratic form determines a unique bounded operator (Propositions 50 and 55, Lemmas 51–54). The section then proves the norm bounds (Propositions 57 and 60, Lemmas 58–59), approximation by integrals of simple functions (Proposition 61), multiplicativity (Propositions 62–66), and compatibility with conjugation and the adjoint (Proposition 67).
- *Stage 1: the continuous functional calculus (p. 80, items 68–104).* The Neumann series (Lemma 70) shows the spectrum is closed, bounded and non-empty (Proposition 73), with holomorphy of the resolvent (Proposition 74). The spectrum of a self-adjoint operator is real (Proposition 78) and compact (Lemma 80). The spectral radius (Definition 81) is at most the operator norm (Corollary 82), is given by Gelfand's formula (Theorem 85), and equals the norm for a self-adjoint operator (Lemma 86). Polynomial spectral mapping (Lemma 89), Stone–Weierstrass (Theorem 92) and the Bounded Linear Transformation Theorem (Theorem 94) then give the continuous functional calculus (Proposition 95), which is multiplicative, produces self-adjoint operators, preserves non-negativity, and satisfies the norm and spectral-mapping identities (Propositions 99–104).
- *Stage 2: an operator-valued Riesz representation theorem (p. 107, items 105–133).* Riesz representation (Theorem 105) attaches measures to a self-adjoint operator (Proposition 106), and hence a bounded quadratic form to every bounded measurable function (Definition 107, Proposition 109). The class of functions with bounded quadratic form (Definition 110) contains the continuous functions (Proposition 115) and is closed under bounded pointwise limits (Proposition 117). A monotone-class argument through the algebra of sets $$\mathcal{L}_0$$ and bump functions (Definitions 119, 122 and 127, Theorems 128–129, Lemmas 121, 130 and 132–133) shows that the class contains every bounded Borel function.
- *The bounded Borel functional calculus and the spectral measure (pp. 127–146, items 134–155).* The bounded Borel functional calculus (Definition 134) sends real functions to self-adjoint operators (Lemma 135) and is multiplicative (Proposition 137, via the classes $$\mathcal{F}_1$$ and $$\mathcal{F}_2$$ of Definition 138 and Propositions 139–142). The spectral projections of Borel sets form the spectral measure of the operator (Theorem 143): each is an orthogonal projection, they multiply to the intersection, and they are countably additive (Propositions 144–147, using the convergence of sums of pairwise orthogonal projections, Lemma 149 and Propositions 150–152). The two bounded functional calculi agree, and the spectral measure integrates to the operator itself (Propositions 153–155).
- *Uniqueness and the spectral theorem (p. 147, items 156–163).* The spectral measure is unique (Theorem 156): two spectral measures of the same operator agree on polynomials, on continuous functions (via complex Stone–Weierstrass, Theorem 159, and Lemma 160) and on bounded measurable functions (Propositions 157, 158 and 161). This gives the Spectral Theorem for Bounded, Self-Adjoint Operators (Theorem 162) and the functional calculus it induces (Definition 163).

**Where the Lean lives:** `Physicslib4/Spectral/` (`Basic`, `Spectrum`, `Forms`, `ProjectionValuedMeasure`, `OperatorIntegral`, `ContinuousCalculus`, `BorelClasses`, `BorelCalculus`, `SpectralTheorem`)

## Items

Each blueprint subsection below is collapsed; click a heading to see its items. Every entry links to its node in the web blueprint and names the principal Lean declaration.

<details markdown="1">
<summary>§10.2.1 · Elementary Properties of Bounded Operators (p. 39) — 4 items</summary>

- [**Definition 19**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:inner-product) — Inner Product · `InnerProductSpace`
- [**Definition 20**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:induced-norm) — Norm Induced by an Inner Product · `norm_eq_sqrt_re_inner`
- [**Definition 21**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-operator-notation) — Bounded Operator Notation · `ContinuousLinearMap.le_opNorm` (+4 more)
- [**Convention 22**](blueprint/chptr-haag-kastler-axioms-blueprint.html#conv:nonzero-hilbert-space) — The Hilbert Space is Non-Zero *(a standing convention, not a declaration; it carries no Lean annotation)*

</details>

<details markdown="1">
<summary>§10.2.1 · Elementary Properties of Bounded Operators › Preliminaries: Notation (p. 40) — 15 items</summary>

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

</details>

<details markdown="1">
<summary>§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › Projection-Valued Measures (p. 45) — 30 items</summary>

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

</details>

<details markdown="1">
<summary>§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › Stage 1: The Continuous Functional Calculus (p. 80) — 37 items</summary>

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

</details>

<details markdown="1">
<summary>§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › Stage 2: An Operator-Valued Riesz Representation Theorem (p. 107) — 29 items</summary>

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

</details>

<details markdown="1">
<summary>§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › The Bounded Borel Functional Calculus (p. 127) — 9 items</summary>

- [**Definition 134**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-8.8) — The Bounded Borel Functional Calculus · `Physicslib4.Spectral.existsUnique_borelCalculus` (+1 more)
- [**Lemma 135**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma-3) — The Operator of a Real-Valued Function is Self-Adjoint · `Physicslib4.Spectral.isSelfAdjoint_borelCalculus`
- [**Proposition 136**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.59) — Polarization Identity · `Physicslib4.Spectral.sesquilinear_polarization`
- [**Proposition 137**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.9) — The Bounded Borel Functional Calculus is Multiplicative · `Physicslib4.Spectral.borelCalculus_mul`
- [**Definition 138**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:F1-F2-classes) — The Classes $$\mathcal{F}_1$$ and $$\mathcal{F}_2$$ · `Physicslib4.Spectral.F1Class` (+1 more)
- [**Proposition 139**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F1-vector-space) — $$\mathcal{F}_1$$ is a Vector Space · `Physicslib4.Spectral.isBorelGenerating_F1Class`
- [**Proposition 140**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:Q-continuous-under-limits) — The Quadratic Form is Continuous under Bounded Pointwise Limits · `Physicslib4.Spectral.tendsto_borelForm`
- [**Proposition 141**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F1-closed-under-limits) — $$\mathcal{F}_1$$ is Closed under Bounded Pointwise Limits · `Physicslib4.Spectral.mem_F1Class_of_tendsto` (+1 more)
- [**Proposition 142**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F2-is-everything) — $$\mathcal{F}_2$$ Contains all Bounded Borel Functions · `Physicslib4.Spectral.isBorelGenerating_F2Class` (+1 more)

</details>

<details markdown="1">
<summary>§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › The Spectral Measure (p. 133) — 13 items</summary>

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

</details>

<details markdown="1">
<summary>§10.2.1 · Spectral Theorem for Bounded Self-Adjoint Operators › The Spectral Theorem › Uniqueness of the Spectral Measure (p. 147) — 8 items</summary>

- [**Theorem 156**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-prblm-8.3.4) — Uniqueness of the Spectral Measure · `Physicslib4.Spectral.pvm_eq_of_integral_id_eq`
- [**Proposition 157**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:pvm-agree-on-polynomials) — Two Spectral Measures Agree on Polynomials · `Physicslib4.Spectral.pvm_integral_polynomial_eq`
- [**Proposition 158**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:pvm-agree-on-continuous) — Two Spectral Measures Agree on Continuous Functions · `Physicslib4.Spectral.pvm_integral_continuous_eq`
- [**Theorem 159**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:stone-weierstrass-complex) — Stone–Weierstrass for Complex Numbers · `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`
- [**Lemma 160**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma-5) — Polynomials are Dense in the Continuous Functions on the Spectrum · `Physicslib4.Spectral.dense_polynomial_spectrum`
- [**Proposition 161**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:pvm-agree-on-measurable) — Two Spectral Measures Agree on Bounded Measurable Functions · `Physicslib4.Spectral.pvm_integral_bddMeasurable_eq`
- [**Theorem 162**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:spectral-theorem-for-bounded-operators) — Spectral Theorem for Bounded, Self-Adjoint Operators · `Physicslib4.Spectral.existsUnique_spectralMeasure`
- [**Definition 163**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:functional-calculus) — Functional Calculus · `Physicslib4.Spectral.functionalCalculus`

</details>


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · **§10.2 Spectral** · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Spacetime](sec10-4-spacetime.html) · [§10.5 Minkowski](sec10-5-haag-kastler.html) · [§10.6 Curved](sec10-6-curved.html) · [§10.7 Covariance](sec10-7-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.1 GNS](sec10-1-gns.html) · [§10.3 Unbounded](sec10-3-unbounded.html) →
