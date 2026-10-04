---
title: "§10.1 GNS Construction (pp. 29–38)"
usemathjax: true
---

[Home](./) · **§10.1 GNS** · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Stone](sec10-4-stone.html) · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

[§10.2 Spectral](sec10-2-spectral.html) →

# §10.1 GNS Construction (pp. 29–38)

States and proves the GNS Construction Theorem (Theorem 15) in full detail—construction of the GNS Hilbert space, the \*-representation, the cyclic vector, faithfulness of the representation for a faithful state, and uniqueness up to unitary equivalence—since both the theorem and specific steps of its proof are used in the axioms that follow. The two supporting objects are the state (Definition 13) and the cyclic vector (Definition 14); the auxiliary results are the Cauchy–Schwarz inequality for positive functionals (Lemma 16) and the two equivalent descriptions of the GNS left ideal $$\mathcal{N}$$, which is shown to be a closed linear subspace (Lemmas 17–18). §10.1.3 is a prose summary and carries no numbered items.


**Where the Lean lives:** `Physicslib4/GNS/` (`Basic`, `Construction`, `NullSpace`, `CauchySchwarz`)

## Items

Every entry links to its node in the web blueprint and names the principal Lean declaration.


### §10.1.1 GNS Construction Theorem (p. 29)

- [**Definition 13**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:state) — State · `Physicslib4.GNS.State` (+1 more)
- [**Definition 14**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:cyclic-vector) — Cyclic Vector · `Physicslib4.GNS.IsCyclicVector`
- [**Theorem 15**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gns-construction-theorem) — GNS Construction Theorem · `Physicslib4.GNS.gns_construction` (+1 more)

### §10.1.2 Auxiliary Results Used in the Proof (p. 35)

- [**Lemma 16**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cauchy-schwarz-inequality) — Cauchy–Schwarz Inequality · `Physicslib4.GNS.cauchy_schwarz_inequality`
- [**Lemma 17**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lmm1) — The two descriptions of the GNS left ideal $$\mathcal{N}$$ agree · `Physicslib4.GNS.lmm1`
- [**Lemma 18**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lmm2) — $$\mathcal{N}$$ is a closed linear subspace · `Physicslib4.GNS.lmm2`


[Home](./) · **§10.1 GNS** · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Stone](sec10-4-stone.html) · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

[§10.2 Spectral](sec10-2-spectral.html) →
