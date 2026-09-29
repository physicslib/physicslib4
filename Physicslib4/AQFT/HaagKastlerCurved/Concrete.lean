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
import Physicslib4.Spacetime.IsometryTopology
import Physicslib4.Spacetime.IsometryCausality

/-!
# Bridging a concrete spacetime to the abstract Haag-Kastler interface

This file connects the concrete blueprint object
`Physicslib4.Spacetime.LorentzianSpacetime` (`def:lorentzian-spacetime`)
to the abstract interface
`Physicslib4.AQFT.HaagKastlerCurved.LorentzianSpacetime` over which
Axioms 1-5 are stated.

## Main definitions

* `Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent`: the
  abstract interface induced by a concrete Lorentzian spacetime.

## Modelling notes

The pieces of the abstract interface are read off the concrete spacetime:

* `Carrier` is the manifold's point set;
* `IsBasisSet` is membership in the Alexandrov basis of diamonds
  `I⁺(p) ∩ I⁻(q)`;
* `IsCompletelySpacelike` is the spacelike-separation relation of the
  underlying spacetime, with respect to its chosen time orientation;
* `Isom` is the oriented identity component
  `Spacetime.Isometry.orientedIdentityComponent` (the topological
  `connectedComponentOfOne` intersected with future-orientation preservation),
  matching the blueprint's "isometries connected to the identity" in Axiom 5;
* `isBasisSet_smul` is `Spacetime.LorentzianSpacetime.isBasisSet_smul`: these
  isometries carry Alexandrov diamonds to Alexandrov diamonds.
-/

namespace Physicslib4

namespace Spacetime

namespace LorentzianSpacetime

/--
The abstract Haag-Kastler interface induced by a concrete Lorentzian
spacetime, with the isometry group taken to be the **oriented identity
component** (identity-component isometries that also preserve the future
orientation), as in Axiom 5. For these isometries basis-set preservation is a
theorem (`Spacetime.LorentzianSpacetime.isBasisSet_smul`), which supplies the
interface field `isBasisSet_smul`.
-/
noncomputable def toAbstractIdentityComponent (L : LorentzianSpacetime) :
    AQFT.HaagKastlerCurved.LorentzianSpacetime where
  Carrier := L.Carrier
  IsBasisSet := L.IsBasisSet
  IsCompletelySpacelike := L.IsCompletelySpacelike
  Isom := ↥(Spacetime.Isometry.orientedIdentityComponent L.toSpacetime
    L.timeOrientation)
  instGroup := inferInstance
  instAction := inferInstance
  isBasisSet_smul := fun φ _ hB => L.isBasisSet_smul (↑φ) φ.2 hB

@[simp] theorem toAbstractIdentityComponent_Carrier (L : LorentzianSpacetime) :
    (L.toAbstractIdentityComponent).Carrier = L.Carrier := rfl

@[simp] theorem toAbstractIdentityComponent_IsBasisSet (L : LorentzianSpacetime) :
    (L.toAbstractIdentityComponent).IsBasisSet = L.IsBasisSet := rfl

@[simp] theorem toAbstractIdentityComponent_IsCompletelySpacelike (L : LorentzianSpacetime) :
    (L.toAbstractIdentityComponent).IsCompletelySpacelike = L.IsCompletelySpacelike := rfl

/-- The abstract isometry group of the bridge is, definitionally, the oriented
identity component. Exposed as a `simp` lemma so abstract-interface statements
can be rewritten to the concrete subgroup. -/
@[simp] theorem toAbstractIdentityComponent_Isom (L : LorentzianSpacetime) :
    (L.toAbstractIdentityComponent).Isom
      = ↥(Spacetime.Isometry.orientedIdentityComponent L.toSpacetime
          L.timeOrientation) := rfl

/-- The abstract isometry group of the bridge inherits the subspace topology of the
oriented identity-component subgroup, discharging the `[TopologicalSpace M.Isom]`
hypothesis of the curved covariance/KMS results automatically over a concrete
spacetime. -/
noncomputable instance instTopologicalSpaceToAbstractIdentityComponentIsom
    (L : LorentzianSpacetime) :
    TopologicalSpace (L.toAbstractIdentityComponent).Isom :=
  inferInstanceAs (TopologicalSpace
    ↥(Spacetime.Isometry.orientedIdentityComponent L.toSpacetime L.timeOrientation))

open scoped Pointwise in
/-- **Axiom 5 basis-set preservation, stated over the abstract bridge.** Every
isometry `φ` of the abstract spacetime carries Alexandrov-basis sets to basis
sets: `φ(𝐁) = φ • 𝐁` is again a basis set. This is the interface field
`isBasisSet_smul` of the bridge. -/
theorem toAbstractIdentityComponent_isBasisSet_smul (L : LorentzianSpacetime)
    (φ : (L.toAbstractIdentityComponent).Isom)
    {B : Set (L.toAbstractIdentityComponent).Carrier}
    (hB : (L.toAbstractIdentityComponent).IsBasisSet B) :
    (L.toAbstractIdentityComponent).IsBasisSet (φ • B) :=
  (L.toAbstractIdentityComponent).isBasisSet_smul φ hB

end LorentzianSpacetime

end Spacetime

namespace AQFT.HaagKastlerCurved.HaagKastlerNet

/-- **Monotonicity of local commutativity over a concrete spacetime.** The
geometric specialisation of `commute_of_spacelike_mono`: for a Haag-Kastler net
over the abstract interface induced by a concrete Lorentzian spacetime `L`, the
spacelike-monotonicity hypothesis is discharged automatically by
`Spacetime.LorentzianSpacetime.isCompletelySpacelike_mono`. -/
theorem commute_of_spacelike_mono_geometric
    {L : Spacetime.LorentzianSpacetime} (N : HaagKastlerNet L.toAbstractIdentityComponent)
    ⦃B₁ B₂ B₁' B₂' B : Set L.toAbstractIdentityComponent.Carrier⦄
    (hB₁' : L.toAbstractIdentityComponent.IsBasisSet B₁')
    (hB₂' : L.toAbstractIdentityComponent.IsBasisSet B₂')
    (hB : L.toAbstractIdentityComponent.IsBasisSet B)
    (hs : L.toAbstractIdentityComponent.IsCompletelySpacelike B₁ B₂)
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
    {L : Spacetime.LorentzianSpacetime} (N : HaagKastlerNet L.toAbstractIdentityComponent)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {B : Set L.toAbstractIdentityComponent.Carrier}
    (hB : L.toAbstractIdentityComponent.IsBasisSet B)
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set L.toAbstractIdentityComponent.Carrier⦄
    (hB₁ : L.toAbstractIdentityComponent.IsBasisSet B₁)
    (hB₂ : L.toAbstractIdentityComponent.IsBasisSet B₂)
    (hsub : B₁ ⊆ L.spacelikeComplement B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
    N.localVonNeumannAlgebra π hB₁ hB h₁
      ≤ (N.localVonNeumannAlgebra π hB₂ hB h₂).commutant :=
  N.localVonNeumannAlgebra_le_commutant hB π hB₁ hB₂
    (L.subset_spacelikeComplement_iff.mp hsub) h₁ h₂

end AQFT.HaagKastlerCurved.HaagKastlerNet

end Physicslib4
