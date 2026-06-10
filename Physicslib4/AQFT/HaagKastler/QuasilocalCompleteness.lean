/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra

/-!
# Axiom 4: Quasilocal Completeness

This file formalises the blueprint declaration
`def:quasilocal-completeness` (Axiom 4 of the "sharpened"
Haag-Kastler axioms, section 9.3 of the AQFT-in-Lean blueprint):

> All "observables" are *quasilocal observables*: the union of the
> images of all local algebras `𝔘(𝐁)` is dense in (and thus
> completes to) the *quasilocal algebra* `𝔘`, which is the
> C*-algebra that "contains all observables of interest".

## Main definitions

* `Physicslib4.AQFT.HaagKastler.QuasilocalCompleteness`: a
  `Prop`-valued predicate on a `LocalNet` asserting Axiom 4.

## Modelling notes

* Following the blueprint, the quasilocal algebra `𝔘` is the
  C*-algebraic *completion* of the set-theoretic union of all
  `𝔘(B)`. The bundled `QuasilocalAlgebra U` structure already
  packages exactly this data — an ambient C*-algebra together with
  faithful unital `*`-monomorphisms whose images have dense union —
  so Axiom 4 collapses to bare nonemptiness:
  `Nonempty (QuasilocalAlgebra U)`.

* In particular, both the *faithfulness* of the embeddings and the
  *density* of the union of their images are part of the
  `QuasilocalAlgebra` structure itself; there is nothing further to
  assert at this level.

* This is closely related to (and refines) the existence statement
  used in `LocalCommutativity`; the two predicates can in principle
  be witnessed by the *same* ambient `QuasilocalAlgebra`, but we
  keep them separate so each axiom can be stated and tested in
  isolation.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/--
**Axiom 4 (Quasilocal Completeness).** A local net `U` satisfies
*quasilocal completeness* if it *admits a quasilocal algebra*,
i.e. `Nonempty (QuasilocalAlgebra U)`.

Unfolding the `QuasilocalAlgebra` structure, this says there exists
a unital ambient C*-algebra `Q.carrier` — the *quasilocal algebra*
`𝔘` — together with unital `*`-monomorphisms
`Q.ι B : U.algebra B →⋆ₐ[ℂ] Q.carrier` for every Alexandrov-basis
set `B`, each injective on Alexandrov-basis sets, and such that the
union `⋃ B, Set.range (Q.ι B)` is *dense* in `Q.carrier`.

This expresses the blueprint's "all observables are quasilocal
observables": every element of `Q.carrier` is the norm-limit of a
sequence of elements of `⋃_B 𝔘(B)`.

Blueprint reference: `def:quasilocal-completeness`.
-/
def QuasilocalCompleteness (U : LocalNet) : Prop :=
  Nonempty (QuasilocalAlgebra U)

end HaagKastler
end AQFT
end Physicslib4
