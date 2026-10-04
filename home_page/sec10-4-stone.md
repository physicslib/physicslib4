---
title: "§10.4 Stone's Theorem (pp. 235–247)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · **§10.4 Stone** · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.5 Spacetime](sec10-5-spacetime.html) →

# §10.4 Stone's Theorem (pp. 235–247)

35 declarations (items 287–321), none of them formalised yet. The section proves **Stone's Theorem** (Theorem 321): every strongly continuous one-parameter unitary group $$U$$ on a Hilbert space $$\mathbf{H}$$ is $$U(t) = e^{itA}$$ for a unique self-adjoint operator $$A$$, its infinitesimal generator. Together with the converse direction (Proposition 305) this is a one-to-one correspondence between strongly continuous one-parameter unitary groups and self-adjoint operators. In AQFT it is what turns the translation symmetry of a net into an energy–momentum operator, and it is the result the bounded-generator **Restriction** on positive energy (`IsPositiveEnergy`) is waiting on. The section builds on the Spectral Theorem for Unbounded, Self-Adjoint Operators (Theorem 283) and the functional calculus it supplies (Definitions 284–285, Lemma 286), and proceeds in five subsections.

- *One-parameter unitary groups (p. 235, items 287–292).* A one-parameter unitary group (Definition 287), strong continuity and its reduction to continuity at $$0$$ (Lemma 288), the adjoint $$U(t)^* = U(-t)$$ (Lemma 289), and the infinitesimal generator (Definition 290), with its characterisation (Lemma 291) and the symmetry identity it satisfies (Lemma 292).
- *Imported results (p. 237, items 293–297).* Standard analysis stated without proof and linked to Mathlib: the Bochner integral (Theorem 293), smooth approximate identities (Lemma 294), facts about differentiation (Proposition 295) and about convolution (Lemma 297). The scalar equation $$y' = cy$$ (Lemma 296) is proved from them.
- *From a self-adjoint operator to a unitary group (p. 239, items 298–305).* For self-adjoint $$A$$ the bounded functions $$e^{it\lambda}$$ give unitaries (Lemma 298) forming the group $$e^{itA}$$ (Definition 299), which satisfies the group law (Lemma 300) and is strongly continuous by dominated convergence (Lemma 301). A difference-quotient norm identity (Lemmas 302–303) gives the derivative at $$0$$ on the domain of $$A$$ (Lemma 304), and maximal symmetry of a self-adjoint operator identifies the generator with $$A$$ (Proposition 305).
- *Two intermediate results (p. 242, items 306–312).* Orbits $$t \mapsto U(t)\psi$$ are differentiable on the generator's domain (Lemma 306), the group commutes with its generator and preserves its domain (Lemmas 307–308), and averaging an orbit against a smooth bump, written as a convolution (Lemmas 309–311), shows that the generator is densely defined (Lemma 312).
- *Stone's Theorem (p. 244, items 313–321).* An ordinary differential equation along orbits (Lemma 313) and the vanishing of bounded solutions of $$y' = \pm y$$ (Lemma 314) make the deficiency subspaces trivial (Lemma 315), so the generator is essentially self-adjoint (Lemma 316). A norm-preservation argument (Lemmas 317–318) shows that the orbits of $$U$$ and of $$e^{itA}$$ agree on the generator's domain (Lemma 319), hence everywhere by density (Lemma 320), which proves Stone's Theorem (Theorem 321).

The closing Summary of the blueprint section, the bijection between groups and generators, is recorded in prose and is not a separate declaration.

**Where the Lean lives:** not yet formalised; the work is planned in stages, starting with the §10.3 additions it depends on (Definitions 284–285, Lemmas 187 and 286).

## Items

Each blueprint subsection below is collapsed; click a heading to see its items. Every entry links to its node in the web blueprint. The four imported results name the Mathlib declarations the blueprint links them to.

<details markdown="1">
<summary>§10.4.1 One-Parameter Unitary Groups (p. 235) — 6 items</summary>

- [**Definition 287**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.11) — One-Parameter Unitary Group *(not yet formalised)*
- [**Lemma 288**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:strongly-continuous-iff-at-zero) — Strong Continuity is Strong Continuity at $$0$$ *(not yet formalised)*
- [**Lemma 289**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:unitary-group-inner-adjoint) — The Adjoint of $$U(t)$$ is $$U(-t)$$ *(not yet formalised)*
- [**Definition 290**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-10.13) — Infinitesimal Generator *(not yet formalised)*
- [**Lemma 291**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-spec) — Characterization of the Generator *(not yet formalised)*
- [**Lemma 292**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-symmetry-identity) — The Generator Satisfies the Symmetry Identity *(not yet formalised)*

</details>

<details markdown="1">
<summary>§10.4.2 Imported Results (p. 237) — 5 items</summary>

- [**Theorem 293**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:bochner-integral) — Bochner Integral · `ContinuousLinearMap.integral_comp_comm` (+1 more) *(imported result; Mathlib link not yet checked)*
- [**Lemma 294**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:smooth-approximate-identity) — Smooth Approximate Identity · `ContDiffBump.normed` (+4 more) *(imported result; Mathlib link not yet checked)*
- [**Proposition 295**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:calculus-facts) — Facts about Differentiation · `HasDerivAt.inner` (+1 more) *(imported result; Mathlib link not yet checked)*
- [**Lemma 296**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:linear-ode-scalar) — The Equation $$y' = cy$$ *(not yet formalised)*
- [**Lemma 297**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:convolution-facts) — Facts about Convolution · `HasCompactSupport.hasDerivAt_convolution_left` (+1 more) *(imported result; Mathlib link not yet checked)*

</details>

<details markdown="1">
<summary>§10.4.3 From a Self-Adjoint Operator to a Unitary Group (p. 239) — 8 items</summary>

- [**Lemma 298**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-unitary) — The Bounded Integral of $$e^{it\lambda }$$ is Unitary *(not yet formalised)*
- [**Definition 299**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:exp-unitary-group) — The Unitary Group $$e^{itA}$$ *(not yet formalised)*
- [**Lemma 300**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-group-law) — The Group Law for $$e^{itA}$$ *(not yet formalised)*
- [**Lemma 301**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-strongly-continuous) — $$e^{itA}$$ is Strongly Continuous *(not yet formalised)*
- [**Lemma 302**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:functional-calculus-sub-bounded) — Subtracting from a Bounded Function *(not yet formalised)*
- [**Lemma 303**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-quotient-norm-identity) — Norm Identity for the Difference Quotient *(not yet formalised)*
- [**Lemma 304**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:exp-derivative-at-zero) — The Derivative of $$e^{itA}$$ at $$0$$ *(not yet formalised)*
- [**Proposition 305**](blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-10.14) — Exponentiating a Self-Adjoint Operator *(not yet formalised)*

</details>

<details markdown="1">
<summary>§10.4.4 Two Intermediate Results (p. 242) — 7 items</summary>

- [**Lemma 306**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbit-hasDerivAt) — Differentiating an Orbit *(not yet formalised)*
- [**Lemma 307**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-commutes) — The Group Commutes with its Generator *(not yet formalised)*
- [**Lemma 308**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.17) — The Group Preserves the Generator's Domain *(not yet formalised)*
- [**Lemma 309**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:averaging-translate) — Averages of an Orbit are Convolutions *(not yet formalised)*
- [**Lemma 310**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:averaging-in-generator-domain) — Averages Lie in the Generator's Domain *(not yet formalised)*
- [**Lemma 311**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:averaging-approximates) — Averages Approximate the Vector *(not yet formalised)*
- [**Lemma 312**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-10.18) — The Generator is Densely Defined *(not yet formalised)*

</details>

<details markdown="1">
<summary>§10.4.5 Stone's Theorem (p. 244) — 9 items</summary>

- [**Lemma 313**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbit-inner-ode) — An Ordinary Differential Equation along Orbits *(not yet formalised)*
- [**Lemma 314**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bounded-exp-solution-zero) — Bounded Solutions of $$y' = \pm y$$ Vanish *(not yet formalised)*
- [**Lemma 315**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-ker-adjoint-trivial) — The Deficiency Subspaces of the Generator are Trivial *(not yet formalised)*
- [**Lemma 316**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:generator-essentially-self-adjoint) — The Generator is Essentially Self-Adjoint *(not yet formalised)*
- [**Lemma 317**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbit-difference-hasDerivAt) — Differentiating the Difference of the Orbits *(not yet formalised)*
- [**Lemma 318**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:norm-const-of-symmetric-derivative) — A Solution of $$w' = iCw$$ with $$C$$ Symmetric Preserves the Norm *(not yet formalised)*
- [**Lemma 319**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:orbits-agree-on-domain) — The Orbits Agree on the Generator's Domain *(not yet formalised)*
- [**Lemma 320**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:agree-on-dense-subspace) — Bounded Operators Agreeing on a Dense Subspace are Equal *(not yet formalised)*
- [**Theorem 321**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-10.15) — Stone's Theorem *(not yet formalised)*

</details>


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · **§10.4 Stone** · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.5 Spacetime](sec10-5-spacetime.html) →
