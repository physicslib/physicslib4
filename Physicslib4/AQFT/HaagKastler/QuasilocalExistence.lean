/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra
import Physicslib4.AQFT.HaagKastler.QuasilocalColimit

/-!
# Existence of a quasilocal algebra

This file formalises the blueprint declaration `thrm:quasilocal-algebra-exists`
(section 10.3 of the AQFT-in-Lean blueprint):

> Every local net satisfying Axiom 2 admits a quasilocal algebra.

It is a *theorem*, not an axiom. The quasilocal algebra is built from the net
alone -- the directed colimit of the local algebras along the Axiom 2 isotony
family, completed -- with no ambient C*-algebra presupposed anywhere.

The file is deliberately thin. Every ingredient is proved in
`Physicslib4/AQFT/HaagKastler/QuasilocalColimit.lean`; all that happens here is
the assembly of those ingredients into the `QuasilocalAlgebra` structure. It is
kept separate from that file so that this assembly does not force a rebuild of
the colimit development, which is instance-heavy and slow to elaborate.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

universe u

/--
**Existence of a quasilocal algebra.** Every local net `U : LocalNet.{u}` satisfying
Axiom 2 (`Isotony`) admits a quasilocal algebra `QuasilocalAlgebra U i`, whose family
of embeddings `ι : 𝔘(𝐁) →⋆ₐ[ℂ] 𝔘` is indexed by the *Alexandrov-basis sets* only.

It is a *theorem*, not an axiom: nothing is assumed -- the ambient C*-algebra `𝔘`
is the completion of the directed colimit of the local algebras
(`lmm:quasilocal-completion-cstar`), and the family, injectivity, density and cocone
condition are exactly `lmm:quasilocal-embedding`, `lmm:quasilocal-embedding-injective`,
`lmm:quasilocal-embeddings-dense` and `lmm:quasilocal-embedding-cocone`.

Blueprint reference: `thrm:quasilocal-algebra-exists`.
-/
theorem exists_quasilocalAlgebra (U : LocalNet.{u}) (i : Isotony U) :
    Nonempty (QuasilocalAlgebra U i) := by
  refine ⟨QuasilocalCompletion U i, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro B hB
    exact quasilocalEmbedding U i ⟨B, hB⟩
  · intro B hB a b h
    apply colimitStarOf_injective U i ⟨B, hB⟩
    apply UniformSpace.Completion.coe_injective
    exact h
  · exact dense_iUnion_range_quasilocalEmbedding U i
  · intro B₁ B₂ hB₁ hB₂ h a
    exact quasilocalEmbedding_transitionHom U i ⟨B₁, hB₁⟩ ⟨B₂, hB₂⟩ h a

end HaagKastler
end AQFT
end Physicslib4
