---
title: "The Axioms at a Glance"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Stone](sec10-4-stone.html) · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

# The axioms at a glance


Axiom 6 (Primitivity) from the original 1964 Haag–Kastler paper is not carried into the sharpened axiom set — see Chapter 8 for the discussion of why it is dropped. The five sharpened axioms in each setting, bundled together as a `HaagKastlerNet`, are what is actually formalised.

**Minkowski spacetime** — bundled as `Physicslib4.AQFT.HaagKastler.HaagKastlerNet` (Definition 508):

| Axiom | Node | Lean |
|---|---|---|
| 1. Local Algebras | Definition 467 | `Physicslib4.AQFT.HaagKastler.LocalNet` |
| 2. Isotony | Definition 468 | `Physicslib4.AQFT.HaagKastler.Isotony` |
| 3. Local Commutativity | Definition 485 | `Physicslib4.AQFT.HaagKastler.LocalCommutativity` |
| 4. Quasilocal Completeness | Definition 489 | `Physicslib4.AQFT.HaagKastler.ObservableCorrespondence` |
| 5. Lorentz Covariance | Definition 507 | `Physicslib4.AQFT.HaagKastler.LorentzCovariance` |

**Curved spacetime** — bundled as `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet` (Definition 633):

| Axiom | Node | Lean |
|---|---|---|
| 1. Local Algebras | Definition 627 | `Physicslib4.AQFT.HaagKastlerCurved.LocalNet` |
| 2. Isotony | Definition 628 | `Physicslib4.AQFT.HaagKastlerCurved.Isotony` |
| 3. Local Commutativity | Definition 629 | `Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity` |
| 4. Local Completeness | Definition 631 | `Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebra` |
| 5. Isometric Covariance | Definition 632 | `Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance` |

**General Covariance (Definition 677, `Physicslib4.AQFT.HaagKastlerCurved.IsGenerallyCovariant`)** is deliberately *not* a sixth axiom. Axioms 1–5 each constrain a single net over a single fixed spacetime, whereas general covariance relates two nets over two spacetimes; it is therefore a property of the section $$L \mapsto \mathfrak{U}_L$$ assigning a net to every Lorentzian spacetime, not an extra field of the net structure.

Three changes to the axioms are worth calling out for readers coming from an earlier version of this blueprint:

- **Isotony now supplies its embeddings as data.** Axiom 2 (Definitions 468 and 628) fixes the family $$i_{\mathbf{B}_1 \mathbf{B}_2}$$ together with identity and composition laws, making $$\mathbf{B} \mapsto \mathfrak{U}(\mathbf{B})$$ a functor on the inclusion order. Axiom 3 consumes that family rather than choosing witnesses of its own, and Axiom 5 (Definitions 507 and 632) now states its coherence condition for the same family, so that covariance-compatibility of a quasilocal algebra is a lemma (Lemma 588) rather than a hypothesis. This is what makes the quasilocal colimit well posed in Minkowski spacetime, and it removes the coherence side-hypotheses that curved-spacetime statements about nested regions previously had to carry.
- **Minkowski Axiom 3 is stated in a common containing diamond.** Definition 485 now requires completely spacelike local algebras to commute in every local algebra $$\mathfrak{U}(\mathbf{B})$$ containing both, through the Axiom 2 isotony maps, exactly as Definition 629 does in curved spacetime; the two differ only in that a containing diamond always exists in Minkowski spacetime. The former statement, commutation in the quasilocal algebra, is now Lemma 487 (`Physicslib4.AQFT.HaagKastler.localCommutativity_iff_exists_commute_ι`), proved equivalent.
- **Axiom 4 has been split.** The mathematical claim that a quasilocal algebra exists is now Theorem 490 (`Physicslib4.AQFT.HaagKastler.exists_quasilocalAlgebra`), proved from the colimit-and-completion chain; what remains as Axiom 4 (Definition 489) is the bridge principle relating physical observables to quasilocal ones, which has — by design — no mathematical consumers.


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Stone](sec10-4-stone.html) · [§10.5 Spacetime](sec10-5-spacetime.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)
