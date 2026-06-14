/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Quasilocal Algebra

This file formalises the blueprint declaration
`def:quasilocal-algebra` (section 9.3 of the AQFT-in-Lean blueprint):

> Consider the set-theoretic union of all `𝔘(𝐁)`. As previously
> proven, this set-theoretic union is a normed *-algebra. Also, as
> previously proven, taking its completion one obtains a C*-algebra
> denoted as `𝔘`. This C*-algebra `𝔘` is called the *quasilocal
> algebra*.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra`: a `structure`
  bundling the *data* of a quasilocal algebra for a given
  `LocalNet`: an ambient C*-algebra together with unital
  `*`-monomorphisms from each local algebra `𝔘(B)` whose images
  jointly have dense union.

## Modelling notes

* Mathlib (as of `v4.31.0-rc1`) does not yet have a canonical
  C*-algebraic direct-limit / amalgamated-completion construction
  for a family of C*-algebras. Consequently we cannot construct
  *the* quasilocal algebra of a `LocalNet` as a definite term;
  instead we package its characterising data as a `structure`.

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

* This mirrors exactly the existential content of
  `QuasilocalCompleteness`: a `LocalNet` satisfies that axiom iff
  it admits *some* `QuasilocalAlgebra`. The two are kept separate
  so the axiom can be stated as a `Prop` and the underlying datum
  can be passed around as a `structure`.

* The `CStarAlgebra` instance is `attribute [instance]`-marked so
  that downstream code finds the C*-structure on `Q.carrier`
  automatically (mirroring the pattern in `LocalAlgebras.lean`).
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/--
**Quasilocal Algebra (data).** For a local net `U`, a
`QuasilocalAlgebra U` is the data of an ambient unital C*-algebra
`carrier` — the *quasilocal algebra* `𝔘` — together with a family
of unital `*`-monomorphisms `ι B : U.algebra B →⋆ₐ[ℂ] carrier`,
one for every subset `B` of Minkowski spacetime, such that

* each `ι B` is injective when `B` is an Alexandrov-basis set
  (so the local algebras embed faithfully), and
* the union of the images `Set.range (ι B)` over all
  Alexandrov-basis sets `B` is *dense* in `carrier`.

The density condition encodes the blueprint's "taking the
completion of the set-theoretic union of all `𝔘(B)` one obtains
the C*-algebra `𝔘`": every element of `carrier` is the norm-limit
of a sequence of elements coming from the local algebras.

Blueprint reference: `def:quasilocal-algebra`.
-/
structure QuasilocalAlgebra (U : LocalNet) where
  /-- The underlying type of the quasilocal algebra `𝔘`. -/
  carrier : Type
  /-- The `CStarAlgebra` instance on `carrier`. -/
  instCStarAlgebra : CStarAlgebra carrier
  /-- The family of unital `*`-homomorphisms `ι B : 𝔘(B) →⋆ₐ[ℂ] 𝔘`
  embedding each local algebra into the quasilocal algebra. -/
  ι : ∀ B : Set StandardMinkowskiSpacetime.Carrier,
        StarAlgHom ℂ (U.algebra B) carrier
  /-- Each embedding `ι B` is injective on Alexandrov-basis sets,
  i.e. every local algebra `𝔘(B)` embeds faithfully into `𝔘`. -/
  ι_injective : ∀ ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄,
                  IsAlexandrovBasisSet B → Function.Injective (ι B)
  /-- The union of the images of all local algebras, ranging over
  Alexandrov-basis sets, is dense in the quasilocal algebra. This is
  the blueprint's "completion of the set-theoretic union". -/
  dense_range : Dense (⋃ (B : Set StandardMinkowskiSpacetime.Carrier)
                          (_ : IsAlexandrovBasisSet B),
                          Set.range (ι B))

attribute [instance] QuasilocalAlgebra.instCStarAlgebra

/-- Each local embedding `Q.ι B` is norm-preserving on Alexandrov-basis sets:
an injective `*`-homomorphism of complex C*-algebras is isometric, so the
local algebra `𝔘(B)` sits inside the quasilocal algebra `𝔘` with its norm
intact. -/
theorem QuasilocalAlgebra.norm_ι {U : LocalNet} (Q : QuasilocalAlgebra U)
    {B : Set StandardMinkowskiSpacetime.Carrier} (hB : IsAlexandrovBasisSet B)
    (a : U.algebra B) : ‖Q.ι B a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (Q.ι B) (Q.ι_injective hB) a

/-- Each local embedding `Q.ι B` is an isometry on Alexandrov-basis sets.
This is the metric form of `QuasilocalAlgebra.norm_ι`. -/
theorem QuasilocalAlgebra.isometry_ι {U : LocalNet} (Q : QuasilocalAlgebra U)
    {B : Set StandardMinkowskiSpacetime.Carrier} (hB : IsAlexandrovBasisSet B) :
    Isometry (Q.ι B) :=
  NonUnitalStarAlgHom.isometry (Q.ι B) (Q.ι_injective hB)

end HaagKastler
end AQFT
end Physicslib4
