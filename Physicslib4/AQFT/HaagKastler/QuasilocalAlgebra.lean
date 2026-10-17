/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.AQFT.HaagKastler.Isotony
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Quasilocal Algebra

This file formalises the blueprint declaration
`def:quasilocal-algebra` (section 10.6 of the AQFT-in-Lean blueprint):

> Consider the union of all `𝔘(𝐁)`, taken along the isotony family of
> Axiom 2. This union is a normed *-algebra; taking its completion one
> obtains a C*-algebra denoted `𝔘`, called the *quasilocal algebra*.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra`: a `structure`
  bundling the *data* of a quasilocal algebra for a given
  `LocalNet`: an ambient C*-algebra together with unital
  `*`-monomorphisms from each local algebra `𝔘(B)` whose images
  jointly have dense union.

## Modelling notes

* Mathlib has no C*-algebraic direct-limit or amalgamated-completion
  construction for a family of C*-algebras:
  `Mathlib.Algebra.Colimit.DirectLimit` is purely
  algebraic (it puts no norm or topology on the colimit) and there is
  no C*-completion anywhere in `Mathlib.Analysis.CStarAlgebra`.
  This `structure` therefore packages the *characterising data* of a
  quasilocal algebra rather than naming a canonical one, which is what
  lets Axioms 3-5 be stated against it.

  Note this is an interface, not a claim that no such algebra can be
  built. The blueprint does construct one, from the net alone, by
  taking the algebraic colimit, equipping it with the norm
  `‖mk a‖ = ‖a‖` (well defined because the isotony maps are injective
  and hence isometric), and completing. See the chain from
  `def:completion-standing-hypotheses` to `lmm:quasilocal-completion-cstar`.
  The route realising the algebra inside an ambient C*-algebra is
  deliberately *not* used: it would have to assume such an ambient
  algebra, and there is no physical justification for one.

* A `QuasilocalAlgebra U` consists of:
  - a carrier type `carrier`,
  - a `CStarAlgebra` instance on `carrier`,
  - a family of unital `*`-homomorphisms
    `ι B : U.algebra B →⋆ₐ[ℂ] carrier`, one for each subset `B`
    of Minkowski spacetime,
  - injectivity of `ι B` for every Alexandrov-basis set `B` (so
    that each local algebra embeds faithfully), and
  - the density condition that the set-theoretic union of the
    images `ι B '' (U.algebra B)`, ranging over Alexandrov-basis
    sets `B`, is dense in `carrier`.

* Every `LocalNet` satisfying Axiom 2 admits such a structure: that
  is `exists_quasilocalAlgebra` (`thrm:quasilocal-algebra-exists`),
  which builds one as the completion of the directed colimit of the
  local algebras. So this is an interface onto a canonical object,
  not a hypothesis a net might fail to satisfy.

* The `CStarAlgebra` instance is `attribute [instance]`-marked so
  that downstream code finds the C*-structure on `Q.carrier`
  automatically (mirroring the pattern in `LocalAlgebras.lean`).
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

universe u

/--
A quasilocal algebra of a net: a C*-algebra 𝔘 in which the local algebras embed with dense union.

Take the local algebras 𝔘(B) of all diamonds, identify each element of 𝔘(B₁) with its images under
the isotony maps of Axiom 2, and complete in norm. The result is the C*-algebra 𝔘 of the
quasilocal observables, those approximated in norm by observables of bounded regions. This
structure records what characterises it: a unital C*-algebra 𝔘 with an injective unital
*-homomorphism ι_B : 𝔘(B) → 𝔘 for each diamond B, such that

* ι_B₂ ∘ i(B₁, B₂) = ι_B₁ for B₁ ⊆ B₂ (the embeddings respect isotony), and
* the union of the images ι_B(𝔘(B)) is dense in 𝔘.

Every net satisfying Axiom 2 has one, built as the completion of the directed colimit of its local
algebras (`exists_quasilocalAlgebra`), and `HaagKastlerNet.quasilocal` chooses one for each net. So
the structure describes a constructed object; it is not an extra hypothesis on the net.

Implementation note: Mathlib has no direct limit of C*-algebras, so the construction is carried out
in `QuasilocalColimit.lean` and `QuasilocalExistence.lean`; this structure is the interface that
the rest of the library uses.

Blueprint: def:quasilocal-algebra
-/
structure QuasilocalAlgebra (U : LocalNet.{u}) (i : Isotony U) where
  /-- The quasilocal algebra 𝔘, a type in the universe of the net's local algebras.

  Implementation note: a carrier fixed in `Type 0` could not contain injective copies of local
  algebras in a higher universe, and a free universe could not be inferred and would make the
  quasilocal form of Axiom 3 depend on it. Tying it to the net's universe loses nothing, since
  density makes 𝔘 the closure of the images of the local algebras. -/
  carrier : Type u
  /-- The quasilocal algebra 𝔘 is a unital C*-algebra. -/
  instCStarAlgebra : CStarAlgebra carrier
  /-- The embedding ι_B : 𝔘(B) → 𝔘 of the local algebra of a diamond B, a unital *-homomorphism.

  Implementation note: ι is defined on diamonds only, as `Isotony.map` is. An embedding of the
  algebras of all subsets would make the structure impossible to build for some nets: density
  bounds 𝔘 by the algebras of the diamonds, while a unital *-homomorphism from a large simple
  algebra on some other subset into the nonzero algebra 𝔘 would be injective, so 𝔘 would have to
  be large too (blueprint: thrm:quasilocal-algebra-exists, first design note). -/
  ι : ∀ ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄,
        IsAlexandrovBasisSet B → StarAlgHom ℂ (U.algebra B) carrier
  /-- Each embedding ι_B is injective: every local algebra embeds faithfully in 𝔘. -/
  ι_injective : ∀ ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄
                  (hB : IsAlexandrovBasisSet B), Function.Injective (ι hB)
  /-- The union of the images ι_B(𝔘(B)) over all diamonds B is dense in 𝔘: 𝔘 is the completion of
  the union of the local algebras. -/
  dense_range : Dense (⋃ (B : Set StandardMinkowskiSpacetime.Carrier)
                          (hB : IsAlexandrovBasisSet B),
                          Set.range (ι hB))
  /-- The embeddings respect isotony: ι_B₂ ∘ i(B₁, B₂) = ι_B₁ for B₁ ⊆ B₂, with i the isotony
  family of Axiom 2. An element of 𝔘(B₁) therefore has the same image in 𝔘 whichever larger diamond
  it is viewed in. This is the cocone condition of the directed colimit. -/
  ι_inclusion : ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
                  (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
                  (h : B₁ ⊆ B₂) (a : U.algebra B₁),
                    ι hB₂ (i.map hB₁ hB₂ h a) = ι hB₁ a

attribute [instance] QuasilocalAlgebra.instCStarAlgebra

/-- Each local embedding `Q.ι B` is norm-preserving on Alexandrov-basis sets:
an injective `*`-homomorphism of complex C*-algebras is isometric, so the
local algebra `𝔘(B)` sits inside the quasilocal algebra `𝔘` with its norm
intact. -/
theorem QuasilocalAlgebra.norm_ι {U : LocalNet} {i : Isotony U} (Q : QuasilocalAlgebra U i)
    {B : Set StandardMinkowskiSpacetime.Carrier} (hB : IsAlexandrovBasisSet B)
    (a : U.algebra B) : ‖Q.ι hB a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (Q.ι hB) (Q.ι_injective hB) a

/-- Each local embedding `Q.ι B` is an isometry on Alexandrov-basis sets.
This is the metric form of `QuasilocalAlgebra.norm_ι`. -/
theorem QuasilocalAlgebra.isometry_ι {U : LocalNet} {i : Isotony U} (Q : QuasilocalAlgebra U i)
    {B : Set StandardMinkowskiSpacetime.Carrier} (hB : IsAlexandrovBasisSet B) :
    Isometry (Q.ι hB) :=
  NonUnitalStarAlgHom.isometry (Q.ι hB) (Q.ι_injective hB)

end HaagKastler
end AQFT
end Physicslib4
