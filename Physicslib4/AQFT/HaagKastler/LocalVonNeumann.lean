/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.EinsteinCausality
import Physicslib4.GNS.Irreducibility
import Physicslib4.Spacetime.CausalComplement
import Physicslib4.Operators.Conjugation

/-!
# Local von Neumann algebras and spacelike commutation

In a representation `π` of the quasilocal algebra, the *local von Neumann algebra*
of a region `B` is the bicommutant `R(B) = π(𝔘(B))''` of the local observable
operators. Mathlib models the commutant by `Set.centralizer`, so `R(B)` is the
double centralizer.

The headline result is **microcausality at the von Neumann level**: for completely
spacelike-separated regions `B₁, B₂`, the local algebras commute,
`R(B₁) ⊆ R(B₂)'`. It is the von Neumann form of Einstein causality
(`einstein_causality`): elementwise commutation of the local operators, pushed
through the centralizer.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler
namespace HaagKastlerNet

open Physicslib4.GNS

variable (N : HaagKastlerNet)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The local observable operators of a region `B` in a representation `π`: the
image `π(𝔘(B))` of the local algebra. -/
def localOperators (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) : Set (H →L[ℂ] H) :=
  Set.range fun a : N.U.algebra B => π (N.commAlgebra.ι B a)

/-- The **local von Neumann algebra** `R(B) = π(𝔘(B))''`, the bicommutant of the
local observable operators (the commutant being `Set.centralizer`). -/
def localVonNeumann (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) : Set (H →L[ℂ] H) :=
  Set.centralizer (Set.centralizer (N.localOperators π B))

/-- **Microcausality at the von Neumann level.** For completely spacelike-separated
basis regions `B₁, B₂`, the local von Neumann algebras commute:
`R(B₁) ⊆ R(B₂)'`. This is the von Neumann form of Einstein causality. -/
theorem localVonNeumann_subset_centralizer
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂) :
    N.localVonNeumann π B₁ ⊆ Set.centralizer (N.localVonNeumann π B₂) := by
  have hcomm : N.localOperators π B₂ ⊆ Set.centralizer (N.localOperators π B₁) := by
    rintro y ⟨b, rfl⟩
    rw [Set.mem_centralizer_iff]
    rintro x ⟨a, rfl⟩
    exact N.einstein_causality π hB₁ hB₂ hs a b
  have h1 : N.localVonNeumann π B₁ ⊆ Set.centralizer (N.localOperators π B₂) :=
    Set.centralizer_subset hcomm
  change N.localVonNeumann π B₁
    ⊆ Set.centralizer (Set.centralizer (Set.centralizer (N.localOperators π B₂)))
  rwa [Set.centralizer_centralizer_centralizer]

/-- **Isotony of the net of von Neumann algebras.** For basis regions `B₁ ⊆ B₂`,
the local von Neumann algebras are nested: `R(B₁) ⊆ R(B₂)`. The local observables
of `B₁` embed into those of `B₂` via the quasilocal isotony coherence
(`ι_inclusion`), and the double commutant is monotone. -/
theorem localVonNeumann_mono
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) :
    N.localVonNeumann π B₁ ⊆ N.localVonNeumann π B₂ := by
  have hsub : N.localOperators π B₁ ⊆ N.localOperators π B₂ := by
    rintro x ⟨a, rfl⟩
    exact ⟨N.commAlgebra.inclusion hB₁ hB₂ h a,
      congrArg π (N.commAlgebra.ι_inclusion hB₁ hB₂ h a)⟩
  exact Set.centralizer_subset (Set.centralizer_subset hsub)

omit [CompleteSpace H] in
/-- **Statistical independence (abstract form).** If `Ω` is cyclic for a set `S` of
operators (the vectors `T Ω`, `T ∈ S`, are dense), then any operator `R` commuting
with every element of `S` and annihilating `Ω` is zero. -/
theorem eq_zero_of_commute_of_cyclic {S : Set (H →L[ℂ] H)} {Ω : H}
    (hcyc : Dense ((fun T => T Ω) '' S)) {R : H →L[ℂ] H}
    (hcomm : ∀ T ∈ S, R * T = T * R) (hRΩ : R Ω = 0) : R = 0 := by
  have hzero : Set.EqOn (⇑R) (fun _ => (0 : H)) ((fun T => T Ω) '' S) := by
    rintro _ ⟨T, hT, rfl⟩
    change R (T Ω) = 0
    rw [← mul_apply_eq_comp, hcomm T hT, mul_apply_eq_comp, hRΩ,
      map_zero]
  have hRx : (⇑R) = fun _ => (0 : H) :=
    Continuous.ext_on hcyc R.continuous continuous_const hzero
  exact ContinuousLinearMap.ext fun x =>
    (congrFun hRx x).trans (zero_apply x).symm

/-- **Statistical independence (Schlieder property), Minkowski spacetime.** If `Ω`
is cyclic for the local observables of `B₁` - in Minkowski spacetime this
cyclicity is supplied by the Reeh-Schlieder theorem - then a nonzero element of the
spacelike-separated local von Neumann algebra `R(B₂)` cannot annihilate `Ω`:
`R Ω = 0 ⟹ R = 0`. So `Ω` is separating for `R(B₂)`. The cyclicity hypothesis is
the Reeh-Schlieder input (which rests on the spectrum condition); the implication
itself is elementary. -/
theorem localVonNeumann_separating
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂) {Ω : H}
    (hcyc : Dense ((fun T => T Ω) '' N.localOperators π B₁))
    {R : H →L[ℂ] H} (hR : R ∈ N.localVonNeumann π B₂) (hRΩ : R Ω = 0) :
    R = 0 := by
  refine eq_zero_of_commute_of_cyclic hcyc (fun A hA => ?_) hRΩ
  have hA' : A ∈ Set.centralizer (N.localVonNeumann π B₂) :=
    N.localVonNeumann_subset_centralizer π hB₁ hB₂ hs (Set.subset_centralizer_centralizer hA)
  exact (Set.mem_centralizer_iff.mp hA') R hR

/-- The local observable operators `π(𝔘(B))` form a self-adjoint set: `π` and the
quasilocal embedding `ι` are `*`-homomorphisms, so `star (π (ι B a)) = π (ι B (star a))`. -/
theorem localOperators_selfAdjoint (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) :
    ∀ x ∈ N.localOperators π B, star x ∈ N.localOperators π B := by
  rintro x ⟨a, rfl⟩
  exact ⟨star a, by simp only [map_star]⟩

/-- The **local von Neumann algebra** `R(B)` as a genuine `VonNeumannAlgebra`: the
bicommutant of the self-adjoint set of local observable operators. Its underlying
set is `localVonNeumann π B`. -/
noncomputable def localVonNeumannAlgebra (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) : VonNeumannAlgebra H :=
  vonNeumannOfSelfAdjoint (N.localOperators π B) (N.localOperators_selfAdjoint π B)

@[simp] theorem coe_localVonNeumannAlgebra (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) :
    (N.localVonNeumannAlgebra π B : Set (H →L[ℂ] H)) = N.localVonNeumann π B :=
  coe_vonNeumannOfSelfAdjoint _ _

/-- **Microcausality, bundled (Minkowski).** For completely spacelike-separated
regions, `R(B₁) ≤ R(B₂)'` as von Neumann algebras (`VonNeumannAlgebra.commutant`). -/
theorem localVonNeumannAlgebra_le_commutant
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂) :
    N.localVonNeumannAlgebra π B₁ ≤ (N.localVonNeumannAlgebra π B₂).commutant := by
  rw [← SetLike.coe_subset_coe]
  simp only [coe_localVonNeumannAlgebra, VonNeumannAlgebra.coe_commutant]
  exact N.localVonNeumann_subset_centralizer π hB₁ hB₂ hs

/-- **Additive-free locality (Minkowski).** A bounded region lying in the spacelike
complement of `B` has its local algebra inside the commutant of `R(B)`: for basis
sets `B' ⊆ B^⊥`, `R(B') ≤ R(B)'`. This repackages microcausality through the
spacelike complement, keeping strictly to bounded (diamond) regions — no algebra is
attached to the unbounded complement. -/
theorem localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B B' : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB : IsAlexandrovBasisSet B) (hB' : IsAlexandrovBasisSet B')
    (hsub : B' ⊆ Spacetime.spacelikeComplement StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B) :
    N.localVonNeumannAlgebra π B' ≤ (N.localVonNeumannAlgebra π B).commutant :=
  N.localVonNeumannAlgebra_le_commutant π hB' hB
    ((Spacetime.subset_spacelikeComplement_iff _ _).mp hsub)

/-- **Isotony, bundled (Minkowski).** `B₁ ⊆ B₂ ⟹ R(B₁) ≤ R(B₂)` as von Neumann
algebras. -/
theorem localVonNeumannAlgebra_mono
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) :
    N.localVonNeumannAlgebra π B₁ ≤ N.localVonNeumannAlgebra π B₂ := by
  rw [← SetLike.coe_subset_coe]
  simp only [coe_localVonNeumannAlgebra]
  exact N.localVonNeumann_mono π hB₁ hB₂ h

/-- **Statistical independence, bundled (Minkowski).** If `Ω` is cyclic for the local
observables of `B₁` (the Reeh-Schlieder input), then `Ω` is separating for the bundled
local von Neumann algebra `R(B₂)` of a spacelike-separated region: any `R ∈ R(B₂)` with
`R Ω = 0` is zero. -/
theorem localVonNeumannAlgebra_separating
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂) {Ω : H}
    (hcyc : Dense ((fun T => T Ω) '' N.localOperators π B₁))
    {R : H →L[ℂ] H} (hR : R ∈ N.localVonNeumannAlgebra π B₂) (hRΩ : R Ω = 0) :
    R = 0 := by
  refine N.localVonNeumann_separating π hB₁ hB₂ hs hcyc ?_ hRΩ
  rwa [← SetLike.mem_coe, coe_localVonNeumannAlgebra] at hR

/-- **The net of von Neumann algebras as an order-preserving map.** Packaging
isotony, the assignment `B ↦ R(B)` is a monotone map from the poset of basis
regions (ordered by inclusion) to the von Neumann algebras of `B(H)`. This is the
statement that the local net is a functor on the inclusion poset: containment of
regions is sent to containment of algebras. -/
noncomputable def vonNeumannNet (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    {B : Set StandardMinkowskiSpacetime.Carrier // IsAlexandrovBasisSet B} →o
      VonNeumannAlgebra H where
  toFun B := N.localVonNeumannAlgebra π B.1
  monotone' B₁ B₂ h := N.localVonNeumannAlgebra_mono π B₁.2 B₂.2 h

/-- **Antitonicity of the commutant.** For bundled von Neumann algebras
`M₁ ≤ M₂` on `H`, the commutants reverse the inclusion: `M₂' ≤ M₁'`. -/
theorem commutant_le_commutant_of_le {M₁ M₂ : VonNeumannAlgebra H} (h : M₁ ≤ M₂) :
    M₂.commutant ≤ M₁.commutant := by
  rw [← SetLike.coe_subset_coe]
  simp only [VonNeumannAlgebra.coe_commutant]
  rw [← SetLike.coe_subset_coe] at h
  exact Set.centralizer_subset h

/-- The **relative commutant** of a nested pair `R(B₁) ⊆ R(B₂)`: the von Neumann
algebra `R(B₁)' ∩ R(B₂)`, built as the meet of the star-subalgebras of the
commutant of `R(B₁)` and of `R(B₂)`. Its underlying set is `R(B₁)' ∩ R(B₂)`. This
is the basic object of the theory of local-algebra inclusions. -/
noncomputable def relativeCommutant (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier) : VonNeumannAlgebra H where
  toStarSubalgebra :=
    (N.localVonNeumannAlgebra π B₁).commutant.toStarSubalgebra ⊓
      (N.localVonNeumannAlgebra π B₂).toStarSubalgebra
  centralizer_centralizer' := by
    -- Compute the carrier of the meet as the intersection of the two factors
    have hcarrier : ((N.localVonNeumannAlgebra π B₁).commutant.toStarSubalgebra ⊓
        (N.localVonNeumannAlgebra π B₂).toStarSubalgebra).carrier =
      Set.centralizer (N.localVonNeumann π B₁) ∩ N.localVonNeumann π B₂ := by
      ext x; simp [coe_localVonNeumannAlgebra]
    -- Both factors are centralizers, so the intersection is `centralizer (_ ∪ _)`,
    -- hence commutant-closed by the triple centralizer theorem.
    rw [hcarrier,
      show N.localVonNeumann π B₂
          = Set.centralizer (Set.centralizer (N.localOperators π B₂)) from rfl,
      ← Set.centralizer_union, Set.centralizer_centralizer_centralizer]

/-- The underlying set of the relative commutant is `R(B₁)' ∩ R(B₂)`. -/
@[simp] theorem coe_relativeCommutant (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier) :
    (N.relativeCommutant π B₁ B₂ : Set (H →L[ℂ] H))
      = Set.centralizer (N.localVonNeumann π B₁) ∩ N.localVonNeumann π B₂ := by
  simp [relativeCommutant, VonNeumannAlgebra.coe_commutant, coe_localVonNeumannAlgebra,
    StarSubalgebra.coe_inf]

/-- **The relative commutant lies in the larger algebra:** `R(B₁)' ∩ R(B₂) ≤ R(B₂)`. -/
theorem relativeCommutant_le_right (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier) :
    N.relativeCommutant π B₁ B₂ ≤ N.localVonNeumannAlgebra π B₂ := by
  rw [← SetLike.coe_subset_coe]
  simp only [coe_relativeCommutant, coe_localVonNeumannAlgebra]
  exact Set.inter_subset_right

/-- **The relative commutant commutes with the smaller algebra:** its underlying
set is contained in `R(B₁)'`. -/
theorem relativeCommutant_coe_subset_commutant
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier) :
    (N.relativeCommutant π B₁ B₂ : Set (H →L[ℂ] H))
      ⊆ Set.centralizer (N.localVonNeumann π B₁) := by
  rw [coe_relativeCommutant]
  exact Set.inter_subset_left

/-- **The relative commutant contains the center of the ambient algebra.** For
`B₁ ⊆ B₂`, the center `R(B₂) ∩ R(B₂)'` is contained in `R(B₁)' ∩ R(B₂)`. Via
isotony `R(B₁) ≤ R(B₂)` and antitonicity of the commutant. -/
theorem center_le_relativeCommutant
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) :
    N.localVonNeumann π B₂ ∩ Set.centralizer (N.localVonNeumann π B₂)
      ⊆ (N.relativeCommutant π B₁ B₂ : Set (H →L[ℂ] H)) := by
  rw [coe_relativeCommutant]
  rintro x ⟨hx1, hx2⟩
  exact ⟨Set.centralizer_subset (N.localVonNeumann_mono π hB₁ hB₂ h) hx2, hx1⟩

/-- The inclusion `R(B₁) ⊆ R(B₂)` is **irreducible** when its relative commutant is
trivial: `R(B₁)' ∩ R(B₂) = ℂ·1`. This is the subfactor-theoretic notion of an
irreducible inclusion. -/
def IsIrreducibleInclusion (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier) : Prop :=
  (N.relativeCommutant π B₁ B₂ : Set (H →L[ℂ] H)) = scalarOperators H

/-- **An irreducible inclusion forces the ambient algebra to be a factor.** If
`B₁ ⊆ B₂` and the inclusion `R(B₁) ⊆ R(B₂)` is irreducible, then `R(B₂)` is a factor
(trivial center). The center `R(B₂) ∩ R(B₂)'` lies inside the relative commutant
(`center_le_relativeCommutant`), which is the scalars by hypothesis; and the scalars
are always central, giving equality. -/
theorem isFactor_of_isIrreducibleInclusion
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂)
    (hirr : N.IsIrreducibleInclusion π B₁ B₂) :
    IsFactor (N.localVonNeumann π B₂) := by
  sorry

end HaagKastlerNet
end HaagKastler
end AQFT
end Physicslib4
