---
title: "§10.7 General Covariance: Nets on Pullback-Related Metrics (pp. 319–321)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Spacetime](sec10-4-spacetime.html) · [§10.5 Minkowski](sec10-5-haag-kastler.html) · [§10.6 Curved](sec10-6-curved.html) · **§10.7 Covariance** · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.6 Curved](sec10-6-curved.html)

# §10.7 General Covariance: Nets on Pullback-Related Metrics (pp. 319–321)

Two definitions, and the newest structural addition to the blueprint. The gauge group of general relativity is the full diffeomorphism group of $$M$$, so the physical content of a spacetime is its diffeomorphism-equivalence class and not the pair $$(M, g)$$; the hole argument shows that treating a relabelling as physical would destroy determinism, and Leibniz equivalence resolves it by declaring diffeomorphic models to represent the same physical situation. Accordingly, an equivalence of Haag–Kastler nets is defined (Definition 621) as a chosen family of unital \*-isomorphisms $$\Theta_\mathbf{B} : \mathfrak{U}_1(\mathbf{B}) \to \mathfrak{U}_2(e(\mathbf{B}))$$ along a basis-set-preserving bijection $$e$$ of carriers, natural with respect to the isotony embeddings. The carriers are related by data rather than by a type equality, deliberately: an equality of carrier types cannot be transported along and would force every comparison through a cast. A net theory is then a section assigning a net to every Lorentzian spacetime, and it is generally covariant when the nets over $$L$$ and over its pullback $$\psi^* L$$ are equivalent along $$\psi$$ (Definition 622). In Lean the nets are indexed over the identity-component bridge `toAbstractIdentityComponent`, so Axiom 5 of each net asks only for isometries connected to the identity, as in the blueprint. Four points are worth carrying away: this is a **postulate, not a theorem**—nothing forces the two nets to be isomorphic, and it says nothing about backgrounds that are not diffeomorphism-related; the morphism is specified geometrically rather than causally, because a purely causal morphism would admit the dilations (Theorems 375–376) and thereby demand a scale covariance that is false for a massive theory; the relabelling must be $$\psi$$ and not the identity, since a basis set of one metric is in general not a basis set of the other; and general covariance is a property of the section $$L \mapsto \mathfrak{U}_L$$, not a sixth field of the net structure, so no restriction to diffeomorphisms connected to the identity is needed here.


**Where the Lean lives:** `Physicslib4/AQFT/HaagKastlerCurved/GeneralCovariance.lean`

## Items

Every entry links to its node in the web blueprint and names the principal Lean declaration.


### §10.7 General Covariance: Nets on Pullback-Related Metrics (p. 319)

- [**Definition 621**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:net-equivalence-in-curved-spacetime) — Equivalence of Haag–Kastler Nets · `Physicslib4.AQFT.HaagKastlerCurved.NetEquivalence`
- [**Definition 622**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:general-covariance-in-curved-spacetime) — General Covariance · `Physicslib4.AQFT.HaagKastlerCurved.NetTheory` (+4 more)


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Spacetime](sec10-4-spacetime.html) · [§10.5 Minkowski](sec10-5-haag-kastler.html) · [§10.6 Curved](sec10-6-curved.html) · **§10.7 Covariance** · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.6 Curved](sec10-6-curved.html)
