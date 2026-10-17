/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.AQFT.HaagKastler.Isotony
import Physicslib4.AQFT.HaagKastler.LocalCommutativity
import Physicslib4.AQFT.HaagKastler.QuasilocalObservable
import Physicslib4.AQFT.HaagKastler.QuasilocalExistence
import Physicslib4.AQFT.HaagKastler.LorentzCovarianceAxiom

/-!
# Haag-Kastler nets

This file bundles the data of Axiom 1 (`def:local-algebras`)
together with the propositional content of Axioms 2, 3 and 5 into a
single `structure HaagKastlerNet`, formalising the blueprint
declaration `def:haag-kastler-net` (section 10.6 of the AQFT-in-Lean
blueprint).

## Main definitions

* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet`: a structure
  consisting of a `LocalNet` (the Axiom 1 data) plus proofs of
  `Isotony`, `LocalCommutativity` and `LorentzCovariance`.

## Supporting lemmas

* `HaagKastlerNet.commute_ι_of_spacelike_symm`: the symmetric restatement of
  `commute_ι_of_spacelike`.
* `HaagKastlerNet.isQuasilocalObservable_of_isSelfAdjoint`,
  `HaagKastlerNet.isQuasilocalObservable_add`,
  `HaagKastlerNet.isQuasilocalObservable_smul`,
  `HaagKastlerNet.isQuasilocalObservable_smul_add_smul`: membership and closure
  API for the net's quasilocal observables, under self-adjointness, addition,
  scaling, and real-linear combinations.

## Notes

* The structure does **not** bundle Axiom 4. The existence of a quasilocal
  algebra is a theorem, `exists_quasilocalAlgebra`
  (`thrm:quasilocal-algebra-exists`), which builds the algebra from the
  net alone; `HaagKastlerNet.quasilocal` is defined from it. Axiom 4
  proper (`def:quasilocal-completeness`) is a *bridge principle*
  relating physical observables to the formalism, with no mathematical
  consumers, and is encoded separately in
  `Physicslib4/AQFT/HaagKastler/ObservableBridge.lean`.

* The structure does not bundle Axiom 6 (Primitivity), which the
  sharpened axioms do not adopt.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4 Spacetime
open scoped Pointwise

universe u

/--
A Haag–Kastler net on Minkowski spacetime: a net of local algebras satisfying Axioms 1, 2, 3 and 5.

The structure bundles the local algebras B ↦ 𝔘(B) of Axiom 1, the isotony family of Axiom 2, and
proofs of local commutativity (Axiom 3) and Lorentz covariance (Axiom 5). Theorems about a theory
take a `HaagKastlerNet` as hypothesis and use each axiom as a field.

Two things are not fields. The quasilocal algebra is constructed from the net, as
`HaagKastlerNet.quasilocal`. Axiom 4, that every physical observable is a quasilocal observable,
relates the formalism to the world rather than constraining the net; it is the separate structure
`ObservableCorrespondence`. Primitivity, the sixth axiom of 1964, is not adopted.
`nonempty_haagKastlerNet` shows that the axioms are consistent.

Blueprint: def:haag-kastler-net
-/
structure HaagKastlerNet where
  /-- The local algebras B ↦ 𝔘(B) (Axiom 1).

  Implementation note: the universe is named, as `LocalNet.{u}`, so that `HaagKastlerNet` takes it
  as a parameter and nets with algebras in any universe are allowed. -/
  U : LocalNet.{u}
  /-- The isotony embeddings i(B₁, B₂) : 𝔘(B₁) → 𝔘(B₂) (Axiom 2). -/
  isotony : Isotony U
  /-- Local commutativity (Axiom 3): for completely spacelike diamonds B₁, B₂ and every diamond
  B ⊇ B₁ ∪ B₂, the images of 𝔘(B₁) and 𝔘(B₂) in 𝔘(B) commute. -/
  localCommutativity : LocalCommutativity U isotony
  /-- Lorentz covariance (Axiom 5): the identity component of the Poincaré group acts on the net,
  compatibly with isotony. -/
  lorentzCovariance : LorentzCovariance U isotony

namespace HaagKastlerNet

variable (N : HaagKastlerNet)

/-- The local algebra `𝔘(B)` assigned by the net to a region `B`
(the Axiom 1 data, via the underlying `LocalNet`). -/
abbrev algebra (B : Set StandardMinkowskiSpacetime.Carrier) :=
  N.U.algebra B

/-- Net-level normalisation `𝔘(∅) ≃⋆ₐ[ℂ] ℂ`. -/
noncomputable def emptyEquivComplex : StarAlgEquiv ℂ (N.algebra ∅) ℂ :=
  N.U.emptyEquivComplex

/-- The empty-region algebra `𝔘(∅)` is commutative. -/
theorem mul_comm_algebra_empty (a b : N.algebra ∅) : a * b = b * a :=
  N.U.mul_comm_algebra_empty a b

/-- The empty-region algebra `𝔘(∅)` is one-dimensional over `ℂ`. -/
theorem finrank_algebra_empty : Module.finrank ℂ (N.algebra ∅) = 1 :=
  N.U.finrank_algebra_empty

/-- **Isotony, reflexivity.** Every Alexandrov-basis set embeds into
itself via the identity unital `*`-monomorphism. -/
theorem isotony_refl {B : Set StandardMinkowskiSpacetime.Carrier} :
    ∃ φ : StarAlgHom ℂ (N.algebra B) (N.algebra B), Function.Injective φ :=
  exists_injective_self N.U

/-- **Isotony, transitivity.** For inclusions `B₁ ⊆ B₂ ⊆ B₃` of
Alexandrov-basis sets, the net's isotony embeddings compose to a unital
`*`-monomorphism `𝔘(B₁) ↪ 𝔘(B₃)`. -/
theorem isotony_trans
    ⦃B₁ B₂ B₃ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hB₃ : IsAlexandrovBasisSet B₃) (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃) :
    ∃ φ : StarAlgHom ℂ (N.algebra B₁) (N.algebra B₃), Function.Injective φ :=
  N.isotony.trans hB₁ hB₂ hB₃ h₁₂ h₂₃

/-- The quasilocal algebra 𝔘 of the net, with its embeddings ι_B : 𝔘(B) → 𝔘.

The algebra is constructed, not assumed: `exists_quasilocalAlgebra` builds one from the local
algebras and isotony alone, as the completion of their directed colimit, and this definition
chooses it. Results about the net's quasilocal observables, representations and states are stated
for this algebra.

Blueprint: thrm:quasilocal-algebra-exists -/
noncomputable def quasilocal : QuasilocalAlgebra N.U N.isotony :=
  Classical.choice (exists_quasilocalAlgebra N.U N.isotony)

/-- Each local algebra `𝔘(B)` of an Alexandrov-basis set embeds
*norm-preservingly* into the canonical quasilocal algebra `𝔘`. -/
theorem norm_ι {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B) (a : N.algebra B) :
    ‖N.quasilocal.ι hB a‖ = ‖a‖ :=
  N.quasilocal.norm_ι hB a

/-- Each local embedding `𝔘(B) ↪ 𝔘` into the canonical quasilocal
algebra is an isometry (the metric form of `norm_ι`). -/
theorem isometry_ι {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B) :
    Isometry (N.quasilocal.ι hB) :=
  N.quasilocal.isometry_ι hB

/-- The *-isomorphism α_L : 𝔘(B) → 𝔘(LB) by which a Poincaré transformation L acts on the net.

Axiom 5 (`lorentzCovariance`) asserts that such a family exists; this definition chooses one.
`covEquiv_one`, `covEquiv_mul` and `covEquiv_isotony` restate the three conditions of the axiom for
it. -/
noncomputable def covEquiv (L : InhomogeneousLorentzGroup)
    (B : Set StandardMinkowskiSpacetime.Carrier) :
    StarAlgEquiv ℂ (N.algebra B) (N.algebra (L • B)) :=
  N.lorentzCovariance.choose L B

/-- **Lorentz invariance of the local dimension.** The local algebras of
a region `B` and of its Lorentz translate `L·B` have the same
`ℂ`-dimension: the covariance equivalence is in particular a
`ℂ`-linear isomorphism `𝔘(B) ≃ₗ[ℂ] 𝔘(L·B)`. -/
theorem finrank_algebra_smul (L : InhomogeneousLorentzGroup)
    (B : Set StandardMinkowskiSpacetime.Carrier) :
    Module.finrank ℂ (N.algebra B) = Module.finrank ℂ (N.algebra (L • B)) :=
  (N.covEquiv L B).toAlgEquiv.toLinearEquiv.finrank_eq

/-- **Lorentz invariance of the local norm.** The covariance equivalence is a
`*`-isomorphism of C*-algebras, hence isometric: `‖α a‖ = ‖a‖`. -/
theorem norm_covEquiv (L : InhomogeneousLorentzGroup)
    {B : Set StandardMinkowskiSpacetime.Carrier} (a : N.algebra B) :
    ‖N.covEquiv L B a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (N.covEquiv L B) (N.covEquiv L B).injective a

/-- **Lorentz transport of commutativity.** Two local elements commute iff
their images under the covariance equivalence commute. -/
theorem commute_covEquiv_iff (L : InhomogeneousLorentzGroup)
    {B : Set StandardMinkowskiSpacetime.Carrier} (a b : N.algebra B) :
    Commute (N.covEquiv L B a) (N.covEquiv L B b) ↔ Commute a b := by
  refine ⟨fun h => ?_, fun h => h.map (N.covEquiv L B)⟩
  simpa using h.map (N.covEquiv L B).symm

/-- **Covariance, identity.** The action of the identity Lorentz
transformation is the identity automorphism (modulo the canonical
identification `𝔘(B) = 𝔘(1·B)` from `one_smul`). -/
theorem covEquiv_one (B : Set StandardMinkowskiSpacetime.Carrier)
    (a : N.algebra B) :
    (N.covEquiv (1 : InhomogeneousLorentzGroup) B :
        N.algebra B → N.algebra ((1 : InhomogeneousLorentzGroup) • B)) a
      = (congrArg N.U.algebra
          (one_smul InhomogeneousLorentzGroup B).symm).mp a :=
  N.lorentzCovariance.choose_spec.1 B a

/-- **Covariance, composition.** The action is multiplicative in the
group element: `α (L'·L) = α L' ∘ α L` (modulo the canonical
identification `𝔘((L'·L)·B) = 𝔘(L'·(L·B))` from `mul_smul`). -/
theorem covEquiv_mul (L L' : InhomogeneousLorentzGroup)
    (B : Set StandardMinkowskiSpacetime.Carrier) (a : N.algebra B) :
    (N.covEquiv (L' * L) B :
        N.algebra B → N.algebra ((L' * L) • B)) a
      = (congrArg N.U.algebra (mul_smul L' L B).symm).mp
          ((N.covEquiv L' (L • B) :
              N.algebra (L • B) → N.algebra (L' • (L • B)))
            ((N.covEquiv L B : N.algebra B → N.algebra (L • B)) a)) :=
  N.lorentzCovariance.choose_spec.2.1 L L' B a

/-- **Covariance commutes with isotony** (Axiom 5 (3)): the covariance
equivalences intertwine the Axiom 2 isotony embeddings,
`α_L ∘ i_{B₁B₂} = i_{L·B₁, L·B₂} ∘ α_L`. -/
theorem covEquiv_isotony (L : InhomogeneousLorentzGroup)
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂)
    (a : N.algebra B₁) :
    N.covEquiv L B₂ (N.isotony.map hB₁ hB₂ h a)
      = N.isotony.map (isAlexandrovBasisSet_smul L hB₁) (isAlexandrovBasisSet_smul L hB₂)
          (Set.smul_set_mono h) (N.covEquiv L B₁ a) :=
  N.lorentzCovariance.choose_spec.2.2 L hB₁ hB₂ h a

/-- **Local commutativity.** The images in the canonical quasilocal algebra
`quasilocal` of two completely-spacelike basis algebras commute. Axiom 3 asserts
commutation in a common containing local algebra; `LocalCommutativity.commute_ι` transfers
it to every quasilocal algebra. -/
theorem commute_ι_of_spacelike ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (a : N.algebra B₁) (b : N.algebra B₂) :
    Commute (N.quasilocal.ι hB₁ a) (N.quasilocal.ι hB₂ b) :=
  N.localCommutativity.commute_ι N.quasilocal hB₁ hB₂ hs a b

/-- **Local commutativity is symmetric.** Commutation of completely-spacelike
local algebras holds in either order. -/
theorem commute_ι_of_spacelike_symm
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (a : N.algebra B₁) (b : N.algebra B₂) :
    Commute (N.quasilocal.ι hB₂ b) (N.quasilocal.ι hB₁ a) :=
  (N.commute_ι_of_spacelike hB₁ hB₂ hs a b).symm

section Observables

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- **Characterisation of the net's quasilocal observables.** An operator on the
GNS Hilbert space is a quasilocal observable iff it is self-adjoint and lies in
the range of the representation `π` of the canonical quasilocal algebra. -/
theorem isQuasilocalObservable_iff {T : H →L[ℂ] H} :
    IsQuasilocalObservable N.quasilocal π T ↔ IsSelfAdjoint T ∧ T ∈ Set.range π :=
  HaagKastler.isQuasilocalObservable_iff

/-- Every self-adjoint operator in the range of `π` is a quasilocal observable
of the net. -/
theorem isQuasilocalObservable_of_isSelfAdjoint (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hmem : T ∈ Set.range π) :
    IsQuasilocalObservable N.quasilocal π T :=
  HaagKastler.isQuasilocalObservable_iff.mpr ⟨hT, hmem⟩

/-- The identity operator is a quasilocal observable of the net. -/
theorem isQuasilocalObservable_one :
    IsQuasilocalObservable N.quasilocal π (1 : H →L[ℂ] H) :=
  HaagKastler.isQuasilocalObservable_one

/-- The net's quasilocal observables are closed under addition. -/
theorem isQuasilocalObservable_add {S T : H →L[ℂ] H}
    (hS : IsQuasilocalObservable N.quasilocal π S)
    (hT : IsQuasilocalObservable N.quasilocal π T) :
    IsQuasilocalObservable N.quasilocal π (S + T) :=
  hS.add hT

/-- The net's quasilocal observables are closed under scaling by a self-adjoint
(i.e. real) complex scalar. -/
theorem isQuasilocalObservable_smul {c : ℂ} {T : H →L[ℂ] H}
    (hT : IsQuasilocalObservable N.quasilocal π T) (hc : IsSelfAdjoint c) :
    IsQuasilocalObservable N.quasilocal π (c • T) :=
  hT.smul hc

/-- *Real-linear combinations* of the net's quasilocal observables are
quasilocal observables. -/
theorem isQuasilocalObservable_smul_add_smul {c d : ℂ} {S T : H →L[ℂ] H}
    (hc : IsSelfAdjoint c) (hd : IsSelfAdjoint d)
    (hS : IsQuasilocalObservable N.quasilocal π S)
    (hT : IsQuasilocalObservable N.quasilocal π T) :
    IsQuasilocalObservable N.quasilocal π (c • S + d • T) :=
  (hS.smul hc).add (hT.smul hd)

end Observables

end HaagKastlerNet

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
  emptyEquivComplex := StarAlgEquiv.refl ℂ ℂ

/-- A concrete Alexandrov-basis set of standard Minkowski spacetime
(`I⁺(0) ∩ I⁻(0)`), used as a witness that basis sets exist. -/
def trivialBasisSet : Set StandardMinkowskiSpacetime.Carrier :=
  chronologicalFuture StandardMinkowskiSpacetime standardMinkowskiTimeOrientation 0
    ∩ chronologicalPast StandardMinkowskiSpacetime standardMinkowskiTimeOrientation 0

lemma isAlexandrovBasisSet_trivialBasisSet :
    IsAlexandrovBasisSet trivialBasisSet :=
  ⟨0, 0, rfl⟩

/-- The trivial net's Axiom 2 data: every local algebra is `ℂ` and every inclusion
is implemented by the identity, which is trivially functorial.

This must precede `trivialQuasilocalAlgebra`, which is indexed by it. -/
def trivialLocalNetIsotony : Isotony trivialLocalNet where
  map := fun _ _ _ _ _ => StarAlgHom.id ℂ ℂ
  injective := by
    intro B₁ B₂ h₁ h₂ h
    change Function.Injective (StarAlgHom.id ℂ ℂ)
    simpa using Function.injective_id
  map_self := by
    intro B h
    rfl
  map_comp := by
    intro B₁ B₂ B₃ h₁ h₂ h₃ h₁₂ h₂₃
    rfl

/-- The trivial quasilocal algebra for the trivial net: ambient C*-algebra `ℂ`,
with every local embedding the identity `ℂ →⋆ₐ[ℂ] ℂ`. The cocone condition
`ι_inclusion` is stated against the Axiom 2 family `trivialLocalNetIsotony`. -/
noncomputable def trivialQuasilocalAlgebra :
    QuasilocalAlgebra trivialLocalNet trivialLocalNetIsotony where
  carrier := ℂ
  instCStarAlgebra := inferInstance
  ι := fun _ _ => StarAlgHom.id ℂ ℂ
  ι_injective := fun _ _ _ _ h => h
  dense_range := fun x =>
    subset_closure (Set.mem_iUnion₂.mpr
      ⟨trivialBasisSet, isAlexandrovBasisSet_trivialBasisSet, x, rfl⟩)
  ι_inclusion := fun _ _ _ _ _ _ => rfl

/-- The trivial local net satisfies Axiom 3 (local commutativity), since `ℂ` is
commutative. -/
theorem trivialLocalNet_localCommutativity :
    LocalCommutativity trivialLocalNet trivialLocalNetIsotony := by
  intro B₁ B₂ B hB₁ hB₂ hB _ h₁ h₂ a b
  exact @mul_comm ℂ _ _ _

/-- The trivial local net satisfies Axiom 5 (Lorentz covariance), realized by the
identity automorphism of `ℂ` at every basis set. -/
theorem trivialLocalNet_lorentzCovariance :
    LorentzCovariance trivialLocalNet trivialLocalNetIsotony := by
  refine ⟨fun _ _ => StarAlgEquiv.refl ℂ ℂ, ?_, ?_, ?_⟩
  · intro _ _; rfl
  · intro _ _ _ _; rfl
  · intro _ _ _ _ _ _ _; rfl

/-- The *trivial Haag-Kastler net*: the trivial local net (every region ↦ `ℂ`)
bundled with proofs of Axioms 2-5. -/
noncomputable def trivialHaagKastlerNet : HaagKastlerNet where
  U := trivialLocalNet
  isotony := trivialLocalNetIsotony
  localCommutativity := trivialLocalNet_localCommutativity
  lorentzCovariance := trivialLocalNet_lorentzCovariance

/-- **The Haag-Kastler axioms are jointly satisfiable.** The trivial net (every
region ↦ `ℂ`) is a Haag-Kastler net, so `HaagKastlerNet` is nonempty.

Stated at universe `0` because the witness is built from `ℂ`, which lives in
`Type`. Consistency of the axioms needs only one model, so nothing is lost; a
witness in an arbitrary universe would come from a `ULift` of this one. -/
theorem nonempty_haagKastlerNet : Nonempty HaagKastlerNet.{0} :=
  ⟨trivialHaagKastlerNet⟩

end HaagKastler
end AQFT
end Physicslib4
