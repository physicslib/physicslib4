/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.Spacetime
import Physicslib4.AQFT.HaagKastlerCurved.Net
import Physicslib4.AQFT.HaagKastlerCurved.LocalVonNeumann
import Physicslib4.Spacetime.LorentzianSpacetime
import Physicslib4.Spacetime.Isometry
import Physicslib4.Spacetime.CausalComplement

/-!
# Bridging a concrete spacetime to the abstract Haag-Kastler interface

This file connects the concrete blueprint object
`Physicslib4.Spacetime.LorentzianSpacetime` (`def:lorentzian-spacetime`)
to the abstract interface
`Physicslib4.AQFT.HaagKastlerCurved.LorentzianSpacetime` over which
Axioms 1-5 are stated.

## Main definitions

* `Physicslib4.Spacetime.LorentzianSpacetime.toAbstract`: the abstract
  interface induced by a concrete Lorentzian spacetime.

## Modelling notes

The four pieces of the abstract interface are read off the concrete
spacetime:

* `Carrier` is the manifold's point set;
* `IsBasisSet` is membership in the Alexandrov basis of diamonds
  `I⁺(p) ∩ I⁻(q)`;
* `IsCompletelySpacelike` is the spacelike-separation relation of the
  underlying spacetime, with respect to its chosen time orientation;
* `Isom` is `Physicslib4.Spacetime.Isometry` of the underlying
  spacetime, with its `Group` and `MulAction` instances.

This bridge instantiates `Isom` with the *full* metric-preserving
isometry group. The identity-component restriction of Axiom 5
("isometries connected to the identity") is captured by the sibling
bridge `toAbstractIdentityComponent`
(`Physicslib4/AQFT/HaagKastlerCurved/IdentityComponent.lean`), which uses
`Spacetime.Isometry.orientedIdentityComponent` (the topological
`connectedComponentOfOne` intersected with future-orientation
preservation); this full-group bridge is retained for the axioms that
hold under the whole isometry group (e.g. microcausality). One deferred
refinement noted on `Spacetime.Isometry` still applies: the bundled
differential is not yet tied to the manifold derivative.
-/

namespace Physicslib4

namespace Spacetime

namespace LorentzianSpacetime

/--
The abstract Haag-Kastler interface
(`AQFT.HaagKastlerCurved.LorentzianSpacetime`) induced by a concrete
Lorentzian spacetime: carrier, Alexandrov-basis predicate,
complete-spacelike relation, and the isometry group with its action.
-/
noncomputable def toAbstract (L : LorentzianSpacetime) :
    AQFT.HaagKastlerCurved.LorentzianSpacetime where
  Carrier := L.Carrier
  IsBasisSet := L.IsBasisSet
  IsCompletelySpacelike := L.IsCompletelySpacelike
  Isom := Isometry L.toSpacetime
  instGroup := inferInstance
  instAction := inferInstance

@[simp] theorem toAbstract_Carrier (L : LorentzianSpacetime) :
    L.toAbstract.Carrier = L.Carrier := rfl

@[simp] theorem toAbstract_IsBasisSet (L : LorentzianSpacetime) :
    L.toAbstract.IsBasisSet = L.IsBasisSet := rfl

@[simp] theorem toAbstract_IsCompletelySpacelike (L : LorentzianSpacetime) :
    L.toAbstract.IsCompletelySpacelike = L.IsCompletelySpacelike := rfl

end LorentzianSpacetime

end Spacetime

namespace AQFT.HaagKastlerCurved.HaagKastlerNet

/-- **Monotonicity of local commutativity over a concrete spacetime.** The
geometric specialisation of `commute_of_spacelike_mono`: for a Haag-Kastler net
over the abstract interface induced by a concrete Lorentzian spacetime `L`, the
spacelike-monotonicity hypothesis is discharged automatically by
`Spacetime.LorentzianSpacetime.isCompletelySpacelike_mono`. -/
theorem commute_of_spacelike_mono_geometric
    {L : Spacetime.LorentzianSpacetime} (N : HaagKastlerNet L.toAbstract)
    ⦃B₁ B₂ B₁' B₂' B : Set L.toAbstract.Carrier⦄
    (hB₁' : L.toAbstract.IsBasisSet B₁') (hB₂' : L.toAbstract.IsBasisSet B₂')
    (hB : L.toAbstract.IsBasisSet B)
    (hs : L.toAbstract.IsCompletelySpacelike B₁ B₂)
    (hsub₁ : B₁' ⊆ B₁) (hsub₂ : B₂' ⊆ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
    (a : N.algebra B₁') (b : N.algebra B₂') :
    Commute (N.commIsotony hB₁' hB (hsub₁.trans h₁) a)
            (N.commIsotony hB₂' hB (hsub₂.trans h₂) b) :=
  N.commute_of_spacelike_mono
    (fun _ _ _ _ hh₁ hh₂ hh => L.isCompletelySpacelike_mono hh₁ hh₂ hh)
    hB₁' hB₂' hB hs hsub₁ hsub₂ h₁ h₂ a b

/-- **Additive-free locality over a concrete spacetime.** The geometric
specialisation of the curved additive-free locality: for a Haag-Kastler net over a
concrete Lorentzian spacetime `L`, a bounded region `B₁` lying in the spacelike
complement of `B₂` (both inside a common containing basis set `B`) has its local von
Neumann algebra inside the commutant of `R(B₂)`. The Galois bridge
`subset_spacelikeComplement_iff` discharges the spacelike hypothesis; no algebra is
attached to the unbounded complement. -/
theorem localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric
    {L : Spacetime.LorentzianSpacetime} (N : HaagKastlerNet L.toAbstract)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {B : Set L.toAbstract.Carrier} (hB : L.toAbstract.IsBasisSet B)
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set L.toAbstract.Carrier⦄
    (hB₁ : L.toAbstract.IsBasisSet B₁) (hB₂ : L.toAbstract.IsBasisSet B₂)
    (hsub : B₁ ⊆ L.spacelikeComplement B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
    N.localVonNeumannAlgebra π hB₁ hB h₁
      ≤ (N.localVonNeumannAlgebra π hB₂ hB h₂).commutant :=
  N.localVonNeumannAlgebra_le_commutant hB π hB₁ hB₂
    (L.subset_spacelikeComplement_iff.mp hsub) h₁ h₂

end AQFT.HaagKastlerCurved.HaagKastlerNet

end Physicslib4
