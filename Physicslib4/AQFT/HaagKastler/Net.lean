/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.AQFT.HaagKastler.Isotony
import Physicslib4.AQFT.HaagKastler.LocalCommutativity
import Physicslib4.AQFT.HaagKastler.QuasilocalCompleteness
import Physicslib4.AQFT.HaagKastler.LorentzCovariance

/-!
# Haag-Kastler nets

This file bundles the data of Axiom 1 (`def:local-algebras`)
together with the propositional content of Axioms 2-5 into a single
`structure HaagKastlerNet`, formalising the blueprint declaration
`def:haag-kastler-net` (section 9.3 of the AQFT-in-Lean blueprint).

## Main definitions

* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet`: a structure
  consisting of a `LocalNet` (the Axiom 1 data) plus proofs of
  `Isotony`, `LocalCommutativity`, `QuasilocalCompleteness`, and
  `LorentzCovariance`.

## Notes

* The structure intentionally does not bundle Axiom 6 (Primitivity)
  or further axioms; those will be added as separate structure
  fields in subsequent files when they are formalised.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4 Spacetime

/--
A *Haag-Kastler net* on (the Alexandrov-basis sets of) Minkowski
spacetime: the data of Axiom 1 (`def:local-algebras`) together with
proofs of Axioms 2-5 (`def:isotony`,
`def:local-commutativity`, `def:quasilocal-completeness`,
`def:lorentz-covariance`).

Blueprint reference: `def:haag-kastler-net`.
-/
structure HaagKastlerNet where
  /-- The underlying assignment `B ↦ 𝔘(B)` (Axiom 1). -/
  U : LocalNet
  /-- *Isotony*: inclusions of Alexandrov-basis sets induce unital
  `*`-monomorphisms of the corresponding local algebras
  (Axiom 2). -/
  isotony : Isotony U
  /-- *Local commutativity*: local algebras of completely-spacelike
  basis sets commute inside the quasilocal algebra (Axiom 3). -/
  localCommutativity : LocalCommutativity U
  /-- *Quasilocal completeness*: the local algebras' images are
  dense in the quasilocal algebra; i.e. all observables are
  quasilocal observables (Axiom 4). -/
  quasilocalCompleteness : QuasilocalCompleteness U
  /-- *Lorentz covariance*: the inhomogeneous Lorentz group acts on
  the net and the action commutes with isotony (Axiom 5). -/
  lorentzCovariance : LorentzCovariance U

/-!
## The trivial net and joint satisfiability of the axioms

The Haag-Kastler axioms are not vacuous: the *trivial net*, assigning the
one-dimensional C*-algebra `ℂ` to every region, satisfies all of Axioms 1-5.
This witnesses `Nonempty HaagKastlerNet`, i.e. the five axioms are jointly
consistent.
-/

/-- The *trivial local net*: every region is assigned the C*-algebra `ℂ`, with
the empty-region normalisation being the identity isomorphism. -/
noncomputable def trivialLocalNet : LocalNet where
  algebra := fun _ => ℂ
  instCStarAlgebra := fun _ => inferInstance
  emptyEquivComplex := StarAlgEquiv.refl

/-- A concrete Alexandrov-basis set of standard Minkowski spacetime
(`I⁺(0) ∩ I⁻(0)`), used as a witness that basis sets exist. -/
def trivialBasisSet : Set StandardMinkowskiSpacetime.Carrier :=
  chronologicalFuture StandardMinkowskiSpacetime standardMinkowskiTimeOrientation 0
    ∩ chronologicalPast StandardMinkowskiSpacetime standardMinkowskiTimeOrientation 0

lemma isAlexandrovBasisSet_trivialBasisSet :
    IsAlexandrovBasisSet trivialBasisSet :=
  ⟨0, 0, rfl⟩

/-- The trivial quasilocal algebra for the trivial net: ambient C*-algebra `ℂ`,
with every local embedding the identity `ℂ →⋆ₐ[ℂ] ℂ`. -/
noncomputable def trivialQuasilocalAlgebra : QuasilocalAlgebra trivialLocalNet where
  carrier := ℂ
  instCStarAlgebra := inferInstance
  ι := fun _ => StarAlgHom.id ℂ ℂ
  ι_injective := fun _ _ _ _ h => h
  dense_range := fun x =>
    subset_closure (Set.mem_iUnion₂.mpr
      ⟨trivialBasisSet, isAlexandrovBasisSet_trivialBasisSet, x, rfl⟩)

theorem trivialLocalNet_isotony : Isotony trivialLocalNet :=
  fun _ _ _ _ _ => ⟨StarAlgHom.id ℂ ℂ, fun _ _ h => h⟩

theorem trivialLocalNet_localCommutativity :
    LocalCommutativity trivialLocalNet :=
  ⟨trivialQuasilocalAlgebra, by
    intro B₁ B₂ _ _ _ a b
    exact @mul_comm ℂ _ (trivialQuasilocalAlgebra.ι B₁ a)
      (trivialQuasilocalAlgebra.ι B₂ b)⟩

theorem trivialLocalNet_quasilocalCompleteness :
    QuasilocalCompleteness trivialLocalNet :=
  ⟨trivialQuasilocalAlgebra⟩

theorem trivialLocalNet_lorentzCovariance :
    LorentzCovariance trivialLocalNet := by
  refine ⟨fun _ _ => StarAlgEquiv.refl, fun _ _ _ _ _ => StarAlgHom.id ℂ ℂ,
    ?_, ?_, ?_, ?_⟩
  · intro B₁ B₂ hB₁ hB₂ h a b hh; exact hh
  · intro _ _; rfl
  · intro _ _ _ _; rfl
  · intro _ _ _ _ _ _ _ _ _ _; rfl

/-- **The Haag-Kastler axioms are jointly satisfiable.** The trivial net (every
region ↦ `ℂ`) is a Haag-Kastler net, so `HaagKastlerNet` is nonempty. -/
theorem nonempty_haagKastlerNet : Nonempty HaagKastlerNet :=
  ⟨{ U := trivialLocalNet
     isotony := trivialLocalNet_isotony
     localCommutativity := trivialLocalNet_localCommutativity
     quasilocalCompleteness := trivialLocalNet_quasilocalCompleteness
     lorentzCovariance := trivialLocalNet_lorentzCovariance }⟩

end HaagKastler
end AQFT
end Physicslib4
