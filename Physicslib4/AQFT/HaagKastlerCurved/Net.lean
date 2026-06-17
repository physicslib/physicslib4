/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.Isotony
import Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity
import Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebra
import Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance

/-!
# Haag-Kastler nets in curved spacetime

This file bundles the data of Axiom 1
(`def:local-algebras-in-curved-spacetime`) together with the
propositional content of Axioms 2-5 into a single structure
`HaagKastlerNet`, formalising the blueprint declaration
`def:haag-kastler-net-in-curved-spacetime` (Chapter 10,
`sections/sec10/10-4_haag-kastler-axioms-in-curved-spacetime`, of the
AQFT-in-Lean blueprint).

## Main definitions

* `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet`: a structure
  consisting of a `LocalNet M` (Axiom 1 data) plus proofs of
  `Isotony`, `LocalCommutativity`, `LocalAlgebra`, and
  `IsometricCovariance`.

## Notes

* As in the Minkowski case, joint satisfiability of the axioms is
  witnessed by the *trivial net* (every region ↦ `ℂ`) over a trivial
  Lorentzian spacetime, giving `Nonempty (Σ M, HaagKastlerNet M)`.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

open scoped Pointwise

/--
A *Haag-Kastler net* on (the Alexandrov-basis sets of) a Lorentzian
spacetime `M`: the data of Axiom 1
(`def:local-algebras-in-curved-spacetime`) together with proofs of
Axioms 2-5.

Blueprint reference: `def:haag-kastler-net-in-curved-spacetime`.
-/
structure HaagKastlerNet (M : LorentzianSpacetime) where
  /-- The underlying assignment `B ↦ 𝔘(B)` (Axiom 1). -/
  U : LocalNet M
  /-- *Isotony*: inclusions of basis sets induce unital
  `*`-monomorphisms (Axiom 2). -/
  isotony : Isotony U
  /-- *Local commutativity*: completely-spacelike basis sets commute
  inside any common containing basis algebra (Axiom 3). -/
  localCommutativity : LocalCommutativity U
  /-- *Local algebra*: all observables are local observables
  (Axiom 4). -/
  localAlgebra : LocalAlgebra U
  /-- *Isometric covariance*: the identity-component isometry group
  acts on the net and commutes with isotony (Axiom 5). -/
  isometricCovariance : IsometricCovariance U

/-!
## The trivial net and joint satisfiability of the axioms

The curved-spacetime Haag-Kastler axioms are not vacuous: over a
trivial Lorentzian spacetime, the *trivial net* assigning `ℂ` to
every region satisfies all of Axioms 1-5.
-/

/-- A *trivial Lorentzian spacetime* used purely to witness joint
satisfiability of the axioms: a one-point carrier, every set a basis
set, trivial spacelike relation, and the trivial isometry group. -/
def trivialSpacetime : LorentzianSpacetime where
  Carrier := Unit
  IsBasisSet := fun _ => True
  IsCompletelySpacelike := fun _ _ => True
  Isom := PUnit
  instGroup := inferInstance
  instAction :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }

/-- The *trivial local net* over **any** abstract Lorentzian spacetime: every
region is assigned the C*-algebra `ℂ`, with the empty-region normalisation the
identity isomorphism. -/
noncomputable def trivialLocalNet (M : LorentzianSpacetime) : LocalNet M where
  algebra := fun _ => ℂ
  instCStarAlgebra := fun _ => inferInstance
  emptyEquivComplex := StarAlgEquiv.refl

theorem trivialLocalNet_isotony (M : LorentzianSpacetime) :
    Isotony (trivialLocalNet M) :=
  fun _ _ _ _ _ => ⟨StarAlgHom.id ℂ ℂ, fun _ _ h => h⟩

theorem trivialLocalNet_localCommutativity (M : LorentzianSpacetime) :
    LocalCommutativity (trivialLocalNet M) := by
  refine ⟨fun _ _ _ _ _ => StarAlgHom.id ℂ ℂ, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ h; exact h
  · intro _ _ _ _ _ _ _ _ _ a b
    exact @mul_comm ℂ _ a b

theorem trivialLocalNet_localAlgebra (M : LorentzianSpacetime) :
    LocalAlgebra (trivialLocalNet M) :=
  localAlgebra_of (trivialLocalNet M)

theorem trivialLocalNet_isometricCovariance (M : LorentzianSpacetime) :
    IsometricCovariance (trivialLocalNet M) := by
  refine ⟨fun _ _ => StarAlgEquiv.refl, fun _ _ _ _ _ => StarAlgHom.id ℂ ℂ,
    ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ h _ _ hh; exact hh
  · intro _ _; rfl
  · intro _ _ _ _; rfl
  · intro _ _ _ _ _ _ _ _ _ _; rfl

/-- The trivial net over any abstract Lorentzian spacetime, bundled as a
Haag-Kastler net. -/
noncomputable def trivialHaagKastlerNet (M : LorentzianSpacetime) :
    HaagKastlerNet M where
  U := trivialLocalNet M
  isotony := trivialLocalNet_isotony M
  localCommutativity := trivialLocalNet_localCommutativity M
  localAlgebra := trivialLocalNet_localAlgebra M
  isometricCovariance := trivialLocalNet_isometricCovariance M

/-- **The curved-spacetime Haag-Kastler axioms are jointly satisfiable over
every Lorentzian spacetime.** The trivial net (every region ↦ `ℂ`) is a
Haag-Kastler net. -/
theorem nonempty_haagKastlerNet (M : LorentzianSpacetime) :
    Nonempty (HaagKastlerNet M) :=
  ⟨trivialHaagKastlerNet M⟩

end HaagKastlerCurved
end AQFT
end Physicslib4
