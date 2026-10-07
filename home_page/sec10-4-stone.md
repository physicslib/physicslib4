---
title: "§10.4 Stone's Theorem (pp. 235–249)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · **§10.4 Stone** · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.5 Spacetime](sec10-5-spacetime.html) →

# §10.4 Stone's Theorem (pp. 235–249)

41 declarations (items 289–329), all formalised and proved. The section proves **Stone's Theorem** (Theorem 329): every strongly continuous one-parameter unitary group $$U$$ on a Hilbert space $$\mathbf{H}$$ is $$U(t) = e^{itA}$$ for a unique self-adjoint operator $$A$$, its infinitesimal generator. Together with the converse direction (Proposition 313) this is a one-to-one correspondence between strongly continuous one-parameter unitary groups and self-adjoint operators. In AQFT it is what turns the translation symmetry of a net into an energy–momentum operator, and it is what lets positive energy (`IsPositiveEnergy`, §10.6) be stated with a genuine unbounded generator. The section builds on the Spectral Theorem for Unbounded, Self-Adjoint Operators (Theorem 285) and the functional calculus it supplies (Definitions 286–287, Lemma 288), and proceeds in five subsections.

- *One-parameter unitary groups (p. 235, items 289–300).* A one-parameter unitary group (Definition 289), strong continuity and its reduction to continuity at $$0$$ (Lemma 290), the adjoint $$U(t)^* = U(-t)$$ (Lemma 291), and the infinitesimal generator (Definition 292), with its characterisation (Lemma 293) and the symmetry identity it satisfies (Lemma 294). Three generators are computed directly: the trivial group has generator $$0$$ (Lemma 295), conjugating a group by a unitary $$W$$ conjugates its generator (Lemmas 296–297), and for bounded self-adjoint $$P$$ the group $$\exp(itP)$$ has generator $$P$$ (Lemmas 298–300); these feed the positive-energy lemmas of §10.6.
- *Imported results (p. 239, items 301–305).* Standard analysis stated without proof and linked to Mathlib: the Bochner integral (Theorem 301), smooth approximate identities (Lemma 302), facts about differentiation (Proposition 303) and about convolution (Lemma 305). The scalar equation $$y' = cy$$ (Lemma 304) is proved from them.
- *From a self-adjoint operator to a unitary group (p. 241, items 306–313).* For self-adjoint $$A$$ the bounded functions $$e^{it\lambda}$$ give unitaries (Lemma 306) forming the group $$e^{itA}$$ (Definition 307), which satisfies the group law (Lemma 308) and is strongly continuous by dominated convergence (Lemma 309). A difference-quotient norm identity (Lemmas 310–311) gives the derivative at $$0$$ on the domain of $$A$$ (Lemma 312), and maximal symmetry of a self-adjoint operator identifies the generator with $$A$$ (Proposition 313).
- *Two intermediate results (p. 244, items 314–320).* Orbits $$t \mapsto U(t)\psi$$ are differentiable on the generator's domain (Lemma 314), the group commutes with its generator and preserves its domain (Lemmas 315–316), and averaging an orbit against a smooth bump, written as a convolution (Lemmas 317–319), shows that the generator is densely defined (Lemma 320).
- *Stone's Theorem (p. 246, items 321–329).* An ordinary differential equation along orbits (Lemma 321) and the vanishing of bounded solutions of $$y' = \pm y$$ (Lemma 322) make the deficiency subspaces trivial (Lemma 323), so the generator is essentially self-adjoint (Lemma 324). A norm-preservation argument (Lemmas 325–326) shows that the orbits of $$U$$ and of $$e^{itA}$$ agree on the generator's domain (Lemma 327), hence everywhere by density (Lemma 328), which proves Stone's Theorem (Theorem 329).

The closing Summary of the blueprint section, the bijection between groups and generators, is recorded in prose and is not a separate declaration.

**Where the Lean lives:** `Physicslib4/Spectral/Stone/` (`Basic`: unitary groups and the generator; `Exponential`: $$e^{itA}$$ and Proposition 313; `Density`: averages and Lemma 320; `Theorem`: Stone's Theorem, `Physicslib4.Spectral.Stone.stone`), with the §10.3 functional calculus in `Physicslib4/Spectral/Unbounded/FunctionalCalculus.lean`.

## Items

Each blueprint subsection below is collapsed; click a heading to see its items. Every entry links to its node in the web blueprint and names the principal Lean declaration; the four imported results name the Mathlib declarations that supply them.

<details markdown="1">
<summary>§10.4.1 One-Parameter Unitary Groups (p. 235) — 12 items</summary>

- [**Definition 289**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.11) — One-Parameter Unitary Group · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup` (+1 more)
- [**Lemma 290**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:strongly-continuous-iff-at-zero) — Strong Continuity is Strong Continuity at $$0$$ · `Physicslib4.Spectral.Stone.isStronglyContinuous_iff_tendsto_zero`
- [**Lemma 291**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:unitary-group-inner-adjoint) — The Adjoint of $$U(t)$$ is $$U(-t)$$ · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup.adjoint_eq` (+1 more)
- [**Definition 292**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.13) — Infinitesimal Generator · `Physicslib4.Spectral.Stone.generator` (+2 more)
- [**Lemma 293**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-spec) — Characterization of the Generator · `Physicslib4.Spectral.Stone.exists_generator_eq_iff`
- [**Lemma 294**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-symmetry-identity) — The Generator Satisfies the Symmetry Identity · `Physicslib4.Spectral.Stone.isSymmetric_generator`
- [**Lemma 295**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-const) — The Generator of the Trivial Group · `Physicslib4.Spectral.Stone.generator_refl`
- [**Lemma 296**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:conj-unitary-group) — Conjugating a Unitary Group · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup.conj` (+1 more)
- [**Lemma 297**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-conj) — Conjugating a Group Conjugates its Generator · `Physicslib4.Spectral.Stone.mem_generator_conj_domain_iff` (+1 more)
- [**Lemma 298**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-bounded-unitary-group) — $$\exp (itP)$$ is a One-Parameter Unitary Group · `Physicslib4.Spectral.Stone.exists_isOneParameterUnitaryGroup_exp`
- [**Lemma 299**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-bounded-hasDerivAt) — The Derivative of $$\exp (itP)$$ at $$0$$ · `Physicslib4.Spectral.Stone.hasDerivAt_exp_smul_I`
- [**Lemma 300**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-exp-bounded) — The Generator of $$\exp (itP)$$ · `Physicslib4.Spectral.Stone.generator_eq_of_eq_exp`

</details>

<details markdown="1">
<summary>§10.4.2 Imported Results (p. 239) — 5 items</summary>

- [**Theorem 301**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:bochner-integral) — Bochner Integral · `ContinuousLinearMap.integral_comp_comm` (+1 more)
- [**Lemma 302**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:smooth-approximate-identity) — Smooth Approximate Identity · `ContDiffBump.normed` (+4 more)
- [**Proposition 303**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:calculus-facts) — Facts about Differentiation · `HasDerivAt.inner` (+1 more)
- [**Lemma 304**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:linear-ode-scalar) — The Equation $$y' = cy$$ · `Physicslib4.Spectral.Stone.eq_mul_exp_of_hasDerivAt`
- [**Lemma 305**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:convolution-facts) — Facts about Convolution · `HasCompactSupport.hasDerivAt_convolution_left` (+1 more)

</details>

<details markdown="1">
<summary>§10.4.3 From a Self-Adjoint Operator to a Unitary Group (p. 241) — 8 items</summary>

- [**Lemma 306**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-unitary) — The Bounded Integral of $$e^{it\lambda }$$ is Unitary · `Physicslib4.Spectral.Stone.integral_expFun_mem_unitary`
- [**Definition 307**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:exp-unitary-group) — The Unitary Group $$e^{itA}$$ · `Physicslib4.Spectral.Stone.expFun` (+2 more)
- [**Lemma 308**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-group-law) — The Group Law for $$e^{itA}$$ · `Physicslib4.Spectral.Stone.isOneParameterUnitaryGroup_expUnitary`
- [**Lemma 309**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-strongly-continuous) — $$e^{itA}$$ is Strongly Continuous · `Physicslib4.Spectral.Stone.isStronglyContinuous_expUnitary`
- [**Lemma 310**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:functional-calculus-sub-bounded) — Subtracting from a Bounded Function · `Physicslib4.Spectral.Stone.functionalCalculus_sub_of_bddMeasurable`
- [**Lemma 311**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-quotient-norm-identity) — Norm Identity for the Difference Quotient · `Physicslib4.Spectral.Stone.norm_sq_generatorQuotient_expUnitary_sub`
- [**Lemma 312**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-derivative-at-zero) — The Derivative of $$e^{itA}$$ at $$0$$ · `Physicslib4.Spectral.Stone.tendsto_generatorQuotient_expUnitary`
- [**Proposition 313**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.14) — Exponentiating a Self-Adjoint Operator · `Physicslib4.Spectral.Stone.generator_expUnitary`

</details>

<details markdown="1">
<summary>§10.4.4 Two Intermediate Results (p. 244) — 7 items</summary>

- [**Lemma 314**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbit-hasDerivAt) — Differentiating an Orbit · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup.hasDerivAt_orbit`
- [**Lemma 315**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-commutes) — The Group Commutes with its Generator · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup.generator_apply_comm`
- [**Lemma 316**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.17) — The Group Preserves the Generator's Domain · `Physicslib4.Spectral.Stone.IsOneParameterUnitaryGroup.hasDerivAt_orbit_generator`
- [**Lemma 317**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:averaging-translate) — Averages of an Orbit are Convolutions · `Physicslib4.Spectral.Stone.average_eq_convolution` (+1 more)
- [**Lemma 318**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:averaging-in-generator-domain) — Averages Lie in the Generator's Domain · `Physicslib4.Spectral.Stone.average_mem_generator_domain`
- [**Lemma 319**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:averaging-approximates) — Averages Approximate the Vector · `Physicslib4.Spectral.Stone.tendsto_average_bump`
- [**Lemma 320**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.18) — The Generator is Densely Defined · `Physicslib4.Spectral.Stone.hasDenseDomain_generator`

</details>

<details markdown="1">
<summary>§10.4.5 Stone's Theorem (p. 246) — 9 items</summary>

- [**Lemma 321**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbit-inner-ode) — An Ordinary Differential Equation along Orbits · `Physicslib4.Spectral.Stone.hasDerivAt_inner_orbit`
- [**Lemma 322**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bounded-exp-solution-zero) — Bounded Solutions of $$y' = \pm y$$ Vanish · `Physicslib4.Spectral.Stone.eq_zero_of_hasDerivAt_of_bounded`
- [**Lemma 323**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-ker-adjoint-trivial) — The Deficiency Subspaces of the Generator are Trivial · `Physicslib4.Spectral.Stone.ker_adjoint_generator_subSmul_eq_bot`
- [**Lemma 324**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-essentially-self-adjoint) — The Generator is Essentially Self-Adjoint · `Physicslib4.Spectral.Stone.isEssentiallySelfAdjoint_generator`
- [**Lemma 325**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbit-difference-hasDerivAt) — Differentiating the Difference of the Orbits · `Physicslib4.Spectral.Stone.hasDerivAt_orbit_sub_expUnitary`
- [**Lemma 326**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:norm-const-of-symmetric-derivative) — A Solution of $$w' = iCw$$ with $$C$$ Symmetric Preserves the Norm · `Physicslib4.Spectral.Stone.eq_zero_of_hasDerivAt_of_isSymmetric`
- [**Lemma 327**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbits-agree-on-domain) — The Orbits Agree on the Generator's Domain · `Physicslib4.Spectral.Stone.orbit_eq_expUnitary_closure`
- [**Lemma 328**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:agree-on-dense-subspace) — Bounded Operators Agreeing on a Dense Subspace are Equal · `Physicslib4.Spectral.Stone.eq_of_eqOn_dense`
- [**Theorem 329**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.15) — Stone's Theorem · `Physicslib4.Spectral.Stone.stone`

</details>


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · **§10.4 Stone** · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.5 Spacetime](sec10-5-spacetime.html) →
