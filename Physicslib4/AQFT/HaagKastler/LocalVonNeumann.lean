/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.EinsteinCausality
import Physicslib4.GNS.Irreducibility

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
    rw [← ContinuousLinearMap.mul_apply, hcomm T hT, ContinuousLinearMap.mul_apply, hRΩ,
      map_zero]
  have hRx : (⇑R) = fun _ => (0 : H) :=
    Continuous.ext_on hcyc R.continuous continuous_const hzero
  exact ContinuousLinearMap.ext fun x =>
    (congrFun hRx x).trans (ContinuousLinearMap.zero_apply x).symm

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

end HaagKastlerNet
end HaagKastler
end AQFT
end Physicslib4
