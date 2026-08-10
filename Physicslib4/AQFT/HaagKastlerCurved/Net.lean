/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Hom
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
`sections/sec10/haag-kastler-axioms-in-curved-spacetime`, of the
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
  /-- *Isotony*: the chosen functorial family of unital `*`-monomorphisms
  implementing inclusions of basis sets (Axiom 2). This is data, carrying the
  identity and composition laws. -/
  isotony : Isotony U
  /-- *Local commutativity*: completely-spacelike basis sets commute
  inside any common containing basis algebra (Axiom 3). This *consumes* the
  Axiom 2 family rather than introducing its own: it asserts only the
  commutation condition. -/
  localCommutativity : LocalCommutativity U isotony
  /-- *Local algebra*: all observables are local observables
  (Axiom 4). -/
  localAlgebra : LocalAlgebra U
  /-- *Isometric covariance*: the identity-component isometry group
  acts on the net and commutes with isotony (Axiom 5). -/
  isometricCovariance : IsometricCovariance U

namespace HaagKastlerNet

variable {M : LorentzianSpacetime} (N : HaagKastlerNet M)

/-- The local algebra `𝔘(B)` assigned by the net to a region `B`
(the Axiom 1 data, via the underlying `LocalNet M`). -/
abbrev algebra (B : Set M.Carrier) :=
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
theorem isotony_refl {B : Set M.Carrier} :
    ∃ φ : StarAlgHom ℂ (N.algebra B) (N.algebra B), Function.Injective φ :=
  exists_injective_self N.U

/-- **Isotony, transitivity.** For inclusions `B₁ ⊆ B₂ ⊆ B₃` of
Alexandrov-basis sets, the net's isotony embeddings compose to a unital
`*`-monomorphism `𝔘(B₁) ↪ 𝔘(B₃)`. -/
theorem isotony_trans ⦃B₁ B₂ B₃ : Set M.Carrier⦄
    (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂) (hB₃ : M.IsBasisSet B₃)
    (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃) :
    ∃ φ : StarAlgHom ℂ (N.algebra B₁) (N.algebra B₃), Function.Injective φ :=
  N.isotony.trans hB₁ hB₂ hB₃ h₁₂ h₂₃

/-- The *covariance equivalence* `𝔘(B) ≃⋆ₐ[ℂ] 𝔘(φ·B)` implementing the
action of an identity-component isometry `φ` on the net, chosen from the
existence witness provided by Axiom 5 (`isometricCovariance`). -/
noncomputable def covEquiv (φ : M.Isom) (B : Set M.Carrier) :
    StarAlgEquiv ℂ (N.algebra B) (N.algebra (φ • B)) :=
  N.isometricCovariance.choose φ B

/-- **Isometry invariance of the local dimension.** The local algebras
of a region `B` and of its isometric image `φ·B` have the same
`ℂ`-dimension: the covariance equivalence is in particular a `ℂ`-linear
isomorphism `𝔘(B) ≃ₗ[ℂ] 𝔘(φ·B)`. -/
theorem finrank_algebra_smul (φ : M.Isom) (B : Set M.Carrier) :
    Module.finrank ℂ (N.algebra B) = Module.finrank ℂ (N.algebra (φ • B)) :=
  (N.covEquiv φ B).toAlgEquiv.toLinearEquiv.finrank_eq

/-- **Isometry invariance of the local norm.** The covariance equivalence is a
`*`-isomorphism of C*-algebras, hence isometric: `‖α a‖ = ‖a‖`. -/
theorem norm_covEquiv (φ : M.Isom) {B : Set M.Carrier} (a : N.algebra B) :
    ‖N.covEquiv φ B a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (N.covEquiv φ B) (N.covEquiv φ B).injective a

/-- **Isometric transport of commutativity.** Two local elements commute iff
their images under the covariance equivalence commute. -/
theorem commute_covEquiv_iff (φ : M.Isom) {B : Set M.Carrier}
    (a b : N.algebra B) :
    Commute (N.covEquiv φ B a) (N.covEquiv φ B b) ↔ Commute a b := by
  refine ⟨fun h => ?_, fun h => h.map (N.covEquiv φ B)⟩
  simpa using h.map (N.covEquiv φ B).symm

/-- **Covariance, identity.** The action of the identity isometry is the
identity automorphism (modulo the canonical identification
`𝔘(B) = 𝔘(1·B)` from `one_smul`). -/
theorem covEquiv_one (B : Set M.Carrier) (a : N.algebra B) :
    (N.covEquiv (1 : M.Isom) B :
        N.algebra B → N.algebra ((1 : M.Isom) • B)) a
      = (congrArg N.U.algebra (one_smul M.Isom B).symm).mp a :=
  N.isometricCovariance.choose_spec.choose_spec.2.1 B a

/-- **Covariance, composition.** The action is multiplicative in the
group element: `α (φ'·φ) = α φ' ∘ α φ` (modulo the canonical
identification `𝔘((φ'·φ)·B) = 𝔘(φ'·(φ·B))` from `mul_smul`). -/
theorem covEquiv_mul (φ φ' : M.Isom) (B : Set M.Carrier) (a : N.algebra B) :
    (N.covEquiv (φ' * φ) B :
        N.algebra B → N.algebra ((φ' * φ) • B)) a
      = (congrArg N.U.algebra (mul_smul φ' φ B).symm).mp
          ((N.covEquiv φ' (φ • B) :
              N.algebra (φ • B) → N.algebra (φ' • (φ • B)))
            ((N.covEquiv φ B : N.algebra B → N.algebra (φ • B)) a)) :=
  N.isometricCovariance.choose_spec.choose_spec.2.2.1 φ φ' B a

/-- The *isotony embeddings* of the net: the chosen family supplied by Axiom 2
(`isotony`).

Previously this was `Classical.choose`n from the Axiom 3 existence witness, which
is why it carried no composition law and every consumer factoring a three-fold
inclusion had to assume coherence separately. It is now literally the Axiom 2
family, so `commIsotony_self` and `commIsotony_comp` below hold for every net. -/
noncomputable def commIsotony ⦃B₁ B₂ : Set M.Carrier⦄
    (h₁ : M.IsBasisSet B₁) (h₂ : M.IsBasisSet B₂) (h : B₁ ⊆ B₂) :
    StarAlgHom ℂ (N.U.algebra B₁) (N.U.algebra B₂) :=
  N.isotony.map h₁ h₂ h

/-- Each chosen isotony embedding is injective. -/
theorem commIsotony_injective ⦃B₁ B₂ : Set M.Carrier⦄
    (h₁ : M.IsBasisSet B₁) (h₂ : M.IsBasisSet B₂) (h : B₁ ⊆ B₂) :
    Function.Injective (N.commIsotony h₁ h₂ h) :=
  N.isotony.injective h₁ h₂ h

/-- **Identity law** for the isotony embeddings, from Axiom 2. -/
theorem commIsotony_self ⦃B : Set M.Carrier⦄ (h : M.IsBasisSet B) :
    N.commIsotony h h (subset_refl B) = StarAlgHom.id ℂ (N.U.algebra B) :=
  N.isotony.map_self h

/-- **Composition law** for the isotony embeddings, from Axiom 2: the embedding
along `B₁ ⊆ B₃` factors through any intermediate `B₂`.

This is the coherence that was previously carried as an ad hoc hypothesis at
every site factoring a three-fold inclusion `B₁ ⊆ B₂ ⊆ B`; it now holds for
every net, including the trivial one. -/
theorem commIsotony_comp ⦃B₁ B₂ B₃ : Set M.Carrier⦄
    (h₁ : M.IsBasisSet B₁) (h₂ : M.IsBasisSet B₂) (h₃ : M.IsBasisSet B₃)
    (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃) :
    (N.commIsotony h₂ h₃ h₂₃).comp (N.commIsotony h₁ h₂ h₁₂)
      = N.commIsotony h₁ h₃ (h₁₂.trans h₂₃) :=
  N.isotony.map_comp h₁ h₂ h₃ h₁₂ h₂₃

/-- **Local commutativity.** If basis sets `B₁`, `B₂` are completely spacelike
and both contained in a common basis set `B`, their images in `𝔘(B)` under the
isotony embeddings commute. -/
theorem commute_of_spacelike ⦃B₁ B₂ B : Set M.Carrier⦄
    (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂) (hB : M.IsBasisSet B)
    (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
    (a : N.algebra B₁) (b : N.algebra B₂) :
    Commute (N.commIsotony hB₁ hB h₁ a) (N.commIsotony hB₂ hB h₂ b) :=
  N.localCommutativity hB₁ hB₂ hB hs h₁ h₂ a b

/-- **Local commutativity is symmetric.** Commutation of completely-spacelike
local algebras inside a common containing basis algebra holds in either order. -/
theorem commute_of_spacelike_symm ⦃B₁ B₂ B : Set M.Carrier⦄
    (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂) (hB : M.IsBasisSet B)
    (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
    (a : N.algebra B₁) (b : N.algebra B₂) :
    Commute (N.commIsotony hB₂ hB h₂ b) (N.commIsotony hB₁ hB h₁ a) :=
  (N.commute_of_spacelike hB₁ hB₂ hB hs h₁ h₂ a b).symm

/-- **Monotonicity of local commutativity.** Commutation of completely-spacelike
basis algebras is inherited by sub-basis-sets: if `B₁`, `B₂` are completely
spacelike and contained in a common basis set `B`, and `B₁' ⊆ B₁`, `B₂' ⊆ B₂`
are basis sets, then the images of `𝔘(B₁')` and `𝔘(B₂')` in `𝔘(B)` commute.

The first argument `mono` is the monotonicity of the spacelike-separation
relation. On the abstract `LorentzianSpacetime` interface this is a hypothesis;
for a net over a geometric spacetime it is discharged by
`Spacetime.LorentzianSpacetime.isCompletelySpacelike_mono`. -/
theorem commute_of_spacelike_mono
    (mono : ∀ ⦃O₁ O₁' O₂ O₂' : Set M.Carrier⦄, O₁' ⊆ O₁ → O₂' ⊆ O₂ →
      M.IsCompletelySpacelike O₁ O₂ → M.IsCompletelySpacelike O₁' O₂')
    ⦃B₁ B₂ B₁' B₂' B : Set M.Carrier⦄
    (hB₁' : M.IsBasisSet B₁') (hB₂' : M.IsBasisSet B₂') (hB : M.IsBasisSet B)
    (hs : M.IsCompletelySpacelike B₁ B₂)
    (hsub₁ : B₁' ⊆ B₁) (hsub₂ : B₂' ⊆ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
    (a : N.algebra B₁') (b : N.algebra B₂') :
    Commute (N.commIsotony hB₁' hB (hsub₁.trans h₁) a)
            (N.commIsotony hB₂' hB (hsub₂.trans h₂) b) :=
  N.commute_of_spacelike hB₁' hB₂' hB (mono hsub₁ hsub₂ hs)
    (hsub₁.trans h₁) (hsub₂.trans h₂) a b

section Observables

variable {B : Set M.Carrier} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- **Net-level Axiom 4 (Local Algebra).** In every GNS representation `π`
of a local algebra `𝔘(B)` of the net (over an Alexandrov-basis set `B`),
every self-adjoint operator in the range of `π` is a local observable.
This applies the net's `localAlgebra` field. -/
theorem isLocalObservable_of_isSelfAdjoint (hB : M.IsBasisSet B)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hmem : T ∈ Set.range π) :
    IsLocalObservable π T :=
  N.localAlgebra hB π T hT hmem

/-- The identity operator is a local observable of the net. -/
theorem isLocalObservable_one : IsLocalObservable π (1 : H →L[ℂ] H) :=
  HaagKastlerCurved.isLocalObservable_one

/-- The net's local observables are closed under addition. -/
theorem isLocalObservable_add {S T : H →L[ℂ] H}
    (hS : IsLocalObservable π S) (hT : IsLocalObservable π T) :
    IsLocalObservable π (S + T) :=
  hS.add hT

/-- The net's local observables are closed under scaling by a self-adjoint
(i.e. real) complex scalar. -/
theorem isLocalObservable_smul {c : ℂ} {T : H →L[ℂ] H}
    (hT : IsLocalObservable π T) (hc : IsSelfAdjoint c) :
    IsLocalObservable π (c • T) :=
  hT.smul hc

/-- *Real-linear combinations* of the net's local observables are local
observables. -/
theorem isLocalObservable_smul_add_smul {c d : ℂ} {S T : H →L[ℂ] H}
    (hc : IsSelfAdjoint c) (hd : IsSelfAdjoint d)
    (hS : IsLocalObservable π S) (hT : IsLocalObservable π T) :
    IsLocalObservable π (c • S + d • T) :=
  (hS.smul hc).add (hT.smul hd)

end Observables

end HaagKastlerNet

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
  emptyEquivComplex := StarAlgEquiv.refl ℂ ℂ

/-- The trivial net's Axiom 2 data: every local algebra is `ℂ` and every
inclusion is implemented by the identity, which is trivially functorial. -/
def trivialLocalNet_isotony (M : LorentzianSpacetime) :
    Isotony (trivialLocalNet M) where
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

theorem trivialLocalNet_localCommutativity (M : LorentzianSpacetime) :
    LocalCommutativity (trivialLocalNet M) (trivialLocalNet_isotony M) := by
  intro B₁ B₂ B hB₁ hB₂ hB hs h₁ h₂ a b
  change (StarAlgHom.id ℂ ℂ a) * (StarAlgHom.id ℂ ℂ b)
      = (StarAlgHom.id ℂ ℂ b) * (StarAlgHom.id ℂ ℂ a)
  exact mul_comm _ _

theorem trivialLocalNet_localAlgebra (M : LorentzianSpacetime) :
    LocalAlgebra (trivialLocalNet M) :=
  localAlgebra_of (trivialLocalNet M)

theorem trivialLocalNet_isometricCovariance (M : LorentzianSpacetime) :
    IsometricCovariance (trivialLocalNet M) := by
  refine ⟨fun _ _ => StarAlgEquiv.refl ℂ ℂ, fun _ _ _ _ _ => StarAlgHom.id ℂ ℂ,
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
