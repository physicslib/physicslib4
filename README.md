# physicslib4

**A Lean 4 formalisation of the mathematical foundations of physics**

![Three pictures of a bull in increasing levels of abstraction](/images/readme/picasso.png)

## Goal

This project works towards a formal resolution of **Hilbert's 6th problem** — the axiomatisation of the mathematical foundations of physics — in the [Lean 4 theorem prover](https://leanprover-community.github.io).

Hilbert's 6th problem calls for a rigorous mathematical treatment of the axioms underlying physical theories, analogous to what Euclidean geometry received from Hilbert's own *Grundlagen der Geometrie*. Modern physics has produced candidate axiom systems — operator-algebraic frameworks for quantum mechanics and quantum field theory chief among them — but these have never been subjected to the kind of machine-checked formal scrutiny that Lean makes possible. This project aims to change that.

## Current Focus: AQFT in Minkowski and Lorentzian Spacetime

The current work formalises **Algebraic Quantum Field Theory (AQFT)**, specifically a sharpened version of the [Haag–Kastler axioms (1964)](https://doi.org/10.1063/1.1704187), in both Minkowski and curved (Lorentzian) spacetime. This covers:

- The GNS construction and its role in representing states on C\*-algebras.
- Causal structure: Minkowski and Lorentzian spacetimes, timelike/spacelike/null vectors, chronological and causal futures and pasts, the Alexandrov topology.
- The sharpened Haag–Kastler axioms (Local Algebras, Isotony, Local Commutativity, Quasilocal Algebra, Lorentz/Isometric Covariance) and their curved-spacetime generalisations.
- Local von Neumann algebras, irreducibility, and the equivalence of purity, irreducibility of the GNS representation, and extremality in the state space.
- KMS states, Killing-flow automorphism groups, and thermal representations in curved spacetime.

The blueprint gives full mathematical detail; see the links below.

## Scope

AQFT on fixed Minkowski or Lorentzian spacetime is a significant milestone, but not the end goal. Both settings treat spacetime as a fixed background and do not account for backreaction — the mutual influence between matter and geometry that is central to general relativity. A complete answer to Hilbert's 6th problem will ultimately require going further.

The repository is therefore designed to grow. Future work may include, for example:

- An axiomatisation of quantum mechanics (which would fall squarely within the project's scope).
- Quantum field theory on dynamical spacetimes.
- Connections to semiclassical gravity and beyond.

Contributions in any of these directions are welcome.

## Links

| Resource | Link |
|---|---|
| Landing page | https://physicslib.github.io/physicslib4/ |
| Blueprint (web) | https://physicslib.github.io/physicslib4/blueprint/ |
| Blueprint (PDF) | https://physicslib.github.io/physicslib4/blueprint.pdf |
| Dependency graph | https://physicslib.github.io/physicslib4/blueprint/dep_graph_document.html |
| API documentation | https://physicslib.github.io/physicslib4/docs/ |
| Original Haag–Kastler paper | https://doi.org/10.1063/1.1704187 |

## Getting Started

Requires [Lean 4](https://leanprover-community.github.io/get_started.html) and [Mathlib4](https://github.com/leanprover-community/mathlib4).

```bash
git clone https://github.com/physicslib/physicslib4.git
cd physicslib4
lake exe cache get!   # download prebuilt dependencies
lake build            # build the project
```

## Contributing

Contributions are welcome. The blueprint is the canonical guide to what has been stated, what has been proved, and what remains open.

1. Consult the [blueprint](https://physicslib.github.io/physicslib4/blueprint/) and [dependency graph](https://physicslib.github.io/physicslib4/blueprint/dep_graph_document.html) to find items not yet linked to Lean proofs.
2. Create a new branch and open a pull request against `main`.
3. PRs must pass all status checks, be approved by a reviewer, and have no conflicts with the base branch before merging.

## Acknowledgements

We are grateful to Rudolf Haag and Daniel Kastler for their foundational work, and to the authors of [Entanglement in Algebraic Quantum Field Theories](https://arxiv.org/abs/2410.16599) for their clear presentation of the GNS construction that this blueprint in part follows. We thank the Mathlib maintainers and the broader Lean community for their support, and Project Numina for partially supporting this research.

---

Maintained by [Kelly J Davis](https://github.com/kellyjdavis). Started June 2026.
