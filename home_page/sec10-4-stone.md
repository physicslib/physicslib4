---
title: "§10.4 Stone's Theorem (pp. 235–247)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · **§10.4 Stone** · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.5 Spacetime](sec10-5-spacetime.html) →

# §10.4 Stone's Theorem (pp. 235–247)

35 declarations (items 287–321), all formalised and proved. The section proves **Stone's Theorem** (Theorem 321): every strongly continuous one-parameter unitary group $$U$$ on a Hilbert space $$\mathbf{H}$$ is $$U(t) = e^{itA}$$ for a unique self-adjoint operator $$A$$, its infinitesimal generator. Together with the converse direction (Proposition 305) this is a one-to-one correspondence between strongly continuous one-parameter unitary groups and self-adjoint operators. In AQFT it is what turns the translation symmetry of a net into an energy–momentum operator, and it is the result the bounded-generator **Restriction** on positive energy (`IsPositiveEnergy`) is waiting on. The section builds on the Spectral Theorem for Unbounded, Self-Adjoint Operators (Theorem 283) and the functional calculus it supplies (Definitions 284–285, Lemma 286), and proceeds in five subsections.

- *One-parameter unitary groups (p. 235, items 287–292).* A one-parameter unitary group (Definition 287), strong continuity and its reduction to continuity at $$0$$ (Lemma 288), the adjoint $$U(t)^* = U(-t)$$ (Lemma 289), and the infinitesimal generator (Definition 290), with its characterisation (Lemma 291) and the symmetry identity it satisfies (Lemma 292).
- *Imported results (p. 237, items 293–297).* Standard analysis stated without proof and linked to Mathlib: the Bochner integral (Theorem 293), smooth approximate identities (Lemma 294), facts about differentiation (Proposition 295) and about convolution (Lemma 297). The scalar equation $$y' = cy$$ (Lemma 296) is proved from them.
- *From a self-adjoint operator to a unitary group (p. 239, items 298–305).* For self-adjoint $$A$$ the bounded functions $$e^{it\lambda}$$ give unitaries (Lemma 298) forming the group $$e^{itA}$$ (Definition 299), which satisfies the group law (Lemma 300) and is strongly continuous by dominated convergence (Lemma 301). A difference-quotient norm identity (Lemmas 302–303) gives the derivative at $$0$$ on the domain of $$A$$ (Lemma 304), and maximal symmetry of a self-adjoint operator identifies the generator with $$A$$ (Proposition 305).
- *Two intermediate results (p. 242, items 306–312).* Orbits $$t \mapsto U(t)\psi$$ are differentiable on the generator's domain (Lemma 306), the group commutes with its generator and preserves its domain (Lemmas 307–308), and averaging an orbit against a smooth bump, written as a convolution (Lemmas 309–311), shows that the generator is densely defined (Lemma 312).
- *Stone's Theorem (p. 244, items 313–321).* An ordinary differential equation along orbits (Lemma 313) and the vanishing of bounded solutions of $$y' = \pm y$$ (Lemma 314) make the deficiency subspaces trivial (Lemma 315), so the generator is essentially self-adjoint (Lemma 316). A norm-preservation argument (Lemmas 317–318) shows that the orbits of $$U$$ and of $$e^{itA}$$ agree on the generator's domain (Lemma 319), hence everywhere by density (Lemma 320), which proves Stone's Theorem (Theorem 321).

The closing Summary of the blueprint section, the bijection between groups and generators, is recorded in prose and is not a separate declaration.

**Where the Lean lives:** `Physicslib4/Spectral/Stone/` (`Basic`: unitary groups and the generator; `Exponential`: $$e^{itA}$$ and Proposition 305; `Density`: averages and Lemma 312; `Theorem`: Stone's Theorem, `Physicslib4.Spectral.Stone.stone`), with the §10.3 functional calculus in `Physicslib4/Spectral/Unbounded/FunctionalCalculus.lean`.

## Items

Each blueprint subsection below is collapsed; click a heading to see its items. Every entry links to its node in the web blueprint and names the principal Lean declaration; the four imported results name the Mathlib declarations that supply them.

<details markdown="1">
<summary>§10.4.1 One-Parameter Unitary Groups (p. 235) — 6 items</summary>

- [**Definition 287**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.11) — One-Parameter Unitary Group · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup` (+1 more)
- [**Lemma 288**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:strongly-continuous-iff-at-zero) — Strong Continuity is Strong Continuity at $$0$$ · `Physicslib4.Spectral.Stone.isStronglyContinuous_iff_tendsto_zero`
- [**Lemma 289**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:unitary-group-inner-adjoint) — The Adjoint of $$U(t)$$ is $$U(-t)$$ · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup.adjoint_eq` (+1 more)
- [**Definition 290**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.13) — Infinitesimal Generator · `Physicslib4.Spectral.Stone.generator` (+2 more)
- [**Lemma 291**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-spec) — Characterization of the Generator · `Physicslib4.Spectral.Stone.exists_generator_eq_iff`
- [**Lemma 292**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-symmetry-identity) — The Generator Satisfies the Symmetry Identity · `Physicslib4.Spectral.Stone.isSymmetric_generator`

</details>

<details markdown="1">
<summary>§10.4.2 Imported Results (p. 237) — 5 items</summary>

- [**Theorem 293**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:bochner-integral) — Bochner Integral · `ContinuousLinearMap.integral_comp_comm` (+1 more)
- [**Lemma 294**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:smooth-approximate-identity) — Smooth Approximate Identity · `ContDiffBump.normed` (+4 more)
- [**Proposition 295**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:calculus-facts) — Facts about Differentiation · `HasDerivAt.inner` (+1 more)
- [**Lemma 296**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:linear-ode-scalar) — The Equation $$y' = cy$$ · `Physicslib4.Spectral.Stone.eq_mul_exp_of_hasDerivAt`
- [**Lemma 297**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:convolution-facts) — Facts about Convolution · `HasCompactSupport.hasDerivAt_convolution_left` (+1 more)

</details>

<details markdown="1">
<summary>§10.4.3 From a Self-Adjoint Operator to a Unitary Group (p. 239) — 8 items</summary>

- [**Lemma 298**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-unitary) — The Bounded Integral of $$e^{it\lambda }$$ is Unitary · `Physicslib4.Spectral.Stone.integral_expFun_mem_unitary`
- [**Definition 299**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:exp-unitary-group) — The Unitary Group $$e^{itA}$$ · `Physicslib4.Spectral.Stone.expFun` (+2 more)
- [**Lemma 300**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-group-law) — The Group Law for $$e^{itA}$$ · `Physicslib4.Spectral.Stone.isOneParameterUnitaryGroup_expUnitary`
- [**Lemma 301**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-strongly-continuous) — $$e^{itA}$$ is Strongly Continuous · `Physicslib4.Spectral.Stone.isStronglyContinuous_expUnitary`
- [**Lemma 302**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:functional-calculus-sub-bounded) — Subtracting from a Bounded Function · `Physicslib4.Spectral.Stone.functionalCalculus_sub_of_bddMeasurable`
- [**Lemma 303**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-quotient-norm-identity) — Norm Identity for the Difference Quotient · `Physicslib4.Spectral.Stone.norm_sq_generatorQuotient_expUnitary_sub`
- [**Lemma 304**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-derivative-at-zero) — The Derivative of $$e^{itA}$$ at $$0$$ · `Physicslib4.Spectral.Stone.tendsto_generatorQuotient_expUnitary`
- [**Proposition 305**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.14) — Exponentiating a Self-Adjoint Operator · `Physicslib4.Spectral.Stone.generator_expUnitary`

</details>

<details markdown="1">
<summary>§10.4.4 Two Intermediate Results (p. 242) — 7 items</summary>

- [**Lemma 306**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbit-hasDerivAt) — Differentiating an Orbit · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup.hasDerivAt_orbit`
- [**Lemma 307**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-commutes) — The Group Commutes with its Generator · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup.generator_apply_comm`
- [**Lemma 308**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.17) — The Group Preserves the Generator's Domain · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup.hasDerivAt_orbit_generator`
- [**Lemma 309**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:averaging-translate) — Averages of an Orbit are Convolutions · `Physicslib4.Spectral.Stone.average_eq_convolution` (+1 more)
- [**Lemma 310**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:averaging-in-generator-domain) — Averages Lie in the Generator's Domain · `Physicslib4.Spectral.Stone.average_mem_generator_domain`
- [**Lemma 311**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:averaging-approximates) — Averages Approximate the Vector · `Physicslib4.Spectral.Stone.tendsto_average_bump`
- [**Lemma 312**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.18) — The Generator is Densely Defined · `Physicslib4.Spectral.Stone.hasDenseDomain_generator`

</details>

<details markdown="1">
<summary>§10.4.5 Stone's Theorem (p. 244) — 9 items</summary>

- [**Lemma 313**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbit-inner-ode) — An Ordinary Differential Equation along Orbits · `Physicslib4.Spectral.Stone.hasDerivAt_inner_orbit`
- [**Lemma 314**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bounded-exp-solution-zero) — Bounded Solutions of $$y' = \pm y$$ Vanish · `Physicslib4.Spectral.Stone.eq_zero_of_hasDerivAt_of_bounded`
- [**Lemma 315**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-ker-adjoint-trivial) — The Deficiency Subspaces of the Generator are Trivial · `Physicslib4.Spectral.Stone.ker_adjoint_generator_subSmul_eq_bot`
- [**Lemma 316**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-essentially-self-adjoint) — The Generator is Essentially Self-Adjoint · `Physicslib4.Spectral.Stone.isEssentiallySelfAdjoint_generator`
- [**Lemma 317**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbit-difference-hasDerivAt) — Differentiating the Difference of the Orbits · `Physicslib4.Spectral.Stone.hasDerivAt_orbit_sub_expUnitary`
- [**Lemma 318**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:norm-const-of-symmetric-derivative) — A Solution of $$w' = iCw$$ with $$C$$ Symmetric Preserves the Norm · `Physicslib4.Spectral.Stone.eq_zero_of_hasDerivAt_of_isSymmetric`
- [**Lemma 319**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbits-agree-on-domain) — The Orbits Agree on the Generator's Domain · `Physicslib4.Spectral.Stone.orbit_eq_expUnitary_closure`
- [**Lemma 320**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:agree-on-dense-subspace) — Bounded Operators Agreeing on a Dense Subspace are Equal · `Physicslib4.Spectral.Stone.eq_of_eqOn_dense`
- [**Theorem 321**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.15) — Stone's Theorem · `Physicslib4.Spectral.Stone.stone`

</details>


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · **§10.4 Stone** · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.5 Spacetime](sec10-5-spacetime.html) →
