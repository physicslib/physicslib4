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

In 1964, Rudolf Haag and Daniel Kastler introduced a set of axioms for Algebraic Quantum Field Theory (AQFT) in Minkowski spacetime, proposing a mathematically rigorous, operator-algebraic framework for quantum field theory in terms of nets of C\*-algebras indexed by regions of Minkowski spacetime. This project formalises a "sharpened" version of these axioms in the [Lean Theorem Prover](https://leanprover-community.github.io), following the [original paper by Haag and Kastler](https://doi.org/10.1063/1.1704187). The original axioms, while revolutionary, left several details underspecified. This project clarifies those details and produces definitions, theorems, and axioms amenable to computer-assisted formalisation. In addition, this project formalises these "sharpened" axioms in curved spacetime, and adds a general-covariance postulate relating the nets over diffeomorphism-related backgrounds.

## Overview

The blueprint is 324 pages long and splits cleanly in two.

**Chapters 1–9 are mathematical background and are not formalised in Lean.** They motivate and analyse each of the original Haag–Kastler axioms in turn, and then generalise them to curved spacetime. Along the way they cite twelve supporting results, numbered 1 through 12 — Gelfand–Naimark, the Bounded Linear Transformation Theorem, the existence of a Lorentz metric, and so on. These are quoted from the literature where needed; none of them carries a Lean declaration.

**Chapter 10 collects the formalisation-ready content, and it is the content of Chapter 10 that is formalised in Lean.** Its items are numbered consecutively, running from Definition 13 through Definition 622, and comprise **607 declarations in total: 144 definitions, 153 theorems, 209 lemmas, 97 propositions, and 4 corollaries**, mapped onto **1,069 distinct Lean declarations** (where Mathlib already supplies a result, the blueprint names the Mathlib declaration directly). Three further numbered items — Conventions 22, 210 and 257, standing hypotheses of the two spectral-theory sections — share the numbering but are conventions rather than declarations, and are not counted. Chapter 10 is divided into seven top-level sections, §10.1 through §10.7.

**606 of the 607 are formalised, statements and proofs alike, and the Lean contains no `sorry`.** Of the 463 theorems, lemmas, propositions and corollaries in Chapter 10, 427 carry a written proof in the blueprint; the other 36, all in §10.2 and §10.3, are standard results quoted from the literature (Heine–Borel, Stone–Weierstrass, dominated convergence and the like) that the blueprint states in full but deliberately does not prove. 462 of the 463 proofs are formalised in Lean, including all 36 of the quoted results. The one exception, in both counts, is Lemma 311, which is not yet formalised at all; it is discussed under [Formalisation status](#formalisation-status) below.

At a glance, the 607 declarations break down by top-level section as follows (click a section to see its items):

| Section | Topic | Pages | Definitions | Theorems | Lemmas | Propositions | Corollaries | Total | Formalised |
|---|---|---|---|---|---|---|---|---|---|
| [§10.1](sec10-1-gns.html) | GNS Construction | 29–38 | 2 | 1 | 3 | 0 | 0 | 6 | 6 |
| [§10.2](sec10-2-spectral.html) | Spectral Theorems (bounded) | 38–155 | 25 | 24 | 27 | 67 | 1 | 144 | 144 |
| [§10.3](sec10-3-unbounded.html) | Unbounded Spectral Theorems | 155–233 | 24 | 13 | 47 | 30 | 3 | 117 | 117 |
| [§10.4](sec10-4-spacetime.html) | Spacetime and causal structure | 233–270 | 34 | 17 | 86 | 0 | 0 | 137 | 136 |
| [§10.5](sec10-5-haag-kastler.html) | Haag–Kastler Axioms (Minkowski) | 270–310 | 40 | 69 | 43 | 0 | 0 | 152 | 152 |
| [§10.6](sec10-6-curved.html) | Haag–Kastler Axioms (curved spacetime) | 310–319 | 17 | 29 | 3 | 0 | 0 | 49 | 49 |
| [§10.7](sec10-7-general-covariance.html) | General Covariance | 319–321 | 2 | 0 | 0 | 0 | 0 | 2 | 2 |
| **Total** | | | **144** | **153** | **209** | **97** | **4** | **607** | **606** |

## Explore

- **[Guide to the blueprint](guide.html)** — how the blueprint is organised, Chapters 1–9, and where the Lean lives.
- **[The axioms at a glance](axioms.html)** — the Minkowski and curved-spacetime axioms with their blueprint nodes and Lean declarations.
- **Chapter 10, section by section:**
  - [§10.1 GNS Construction (pp. 29–38)](sec10-1-gns.html)
  - [§10.2 Spectral Theorems (pp. 38–155)](sec10-2-spectral.html)
  - [§10.3 Unbounded Spectral Theorems (pp. 155–233)](sec10-3-unbounded.html)
  - [§10.4 Spacetime and causal structure (pp. 233–270)](sec10-4-spacetime.html)
  - [§10.5 Haag–Kastler Axioms in Minkowski spacetime (pp. 270–310)](sec10-5-haag-kastler.html)
  - [§10.6 Haag–Kastler Axioms in curved spacetime (pp. 310–319)](sec10-6-curved.html)
  - [§10.7 General Covariance: Nets on Pullback-Related Metrics (pp. 319–321)](sec10-7-general-covariance.html)

## Formalisation status

The blueprint annotates every node with the Lean declarations that realise it, so the status of each node is a matter of record rather than of estimate. There is exactly one node in Chapter 10 that is not formalised, and one further place where the Lean is deliberately differently shaped than the prose. Both are flagged in the blueprint text itself; they are collected here so that they are not discovered by surprise. The project contains no `sorry`.

**Not yet formalised (one node).**

- **Lemma 311, "Smoothness of the Inverse Musical Isomorphism."** The node sits in §10.4 (p. 239), in the pseudo-Riemannian layer that precedes the definition of geodesics. It states that the pointwise inverse $$x \mapsto \flat_x^{-1}$$ of the musical isomorphism (Lemma 310) is a smooth section of $$\mathrm{Hom}(T^*M, TM)$$, and the blueprint gives a written proof (in a local trivialisation, inversion of continuous linear equivalences is smooth). It carries no Lean declaration yet. No other node depends on it: the existence and uniqueness of the Levi-Civita connection are formalised without it.

**Recently completed: the von Neumann density theorem.** Theorem 458, "Quasilocal Observables are Strongly Dense in the Bicommutant" (§10.5.2, p. 289), formalised as `Physicslib4.AQFT.HaagKastler.dense_range_in_bicommutant` in `Physicslib4/AQFT/HaagKastler/StrongDensity.lean`, is now proved. Mathlib has the strong operator topology (`PointwiseConvergenceCLM`) and the double commutant property of bundled von Neumann algebras, but not the density theorem itself, so the project proves it locally, following Murphy, Lemma 4.1.4, in the new §10.5.2 (Lemmas 448–457, Definition 451): a closed subspace invariant under an operator and its adjoint has a commuting projection (Lemma 448, in `Physicslib4/Operators/ReducingSubspace.lean`), so the closed cyclic subspace of a vector reduces the representation (Lemma 449) and the one-vector case follows (Lemma 450); a finite amplification $$\pi^\iota$$ on $$\ell^2(\iota; H)$$ (Definition 451, Lemmas 452–455, in `Physicslib4/Operators/DensityTheorem.lean`) carries the bicommutant diagonally into its own bicommutant, which upgrades the one-vector case to finitely many vectors (Lemma 456); and a neighbourhood basis for the strong operator topology (Lemma 457) turns that into density. The Kaplansky density theorem, which would additionally keep approximants self-adjoint and norm-bounded, remains out of scope; nothing in the project needs it.

**Formalised, but the Lean is shaped differently from the prose (one place).** The node below carries Lean declarations and a formalised proof; the caveat is one of presentation, not of coverage or content.

- **Axiom 5 in curved spacetime (Definition 577).** "Isometries connected to the identity" and "identity-component isometries preserving the future orientation" describe the same group, but the inclusion of the former in the latter rests on a Myers–Steenrod-type rigidity result not yet in Mathlib. The Lean therefore intersects the identity component with the explicitly orientation-preserving subgroup. This is an implementation choice and does not alter the mathematical content of the axiom.

## Useful links

- [Blueprint (web)](https://physicslib.github.io/physicslib4/blueprint/)
- [Blueprint (pdf)](https://physicslib.github.io/physicslib4/blueprint.pdf)
- [Dependency graph](https://physicslib.github.io/physicslib4/blueprint/dep_graph_document.html)
- [Documentation pages for this repository](https://physicslib.github.io/physicslib4/docs/)
- [Original Haag–Kastler paper](https://doi.org/10.1063/1.1704187)

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
