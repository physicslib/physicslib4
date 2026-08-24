/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Construction
import Physicslib4.GNS.ExtremeState
import Physicslib4.GNS.UnitaryEquiv

/-!
# GNS covariance under a `*`-isomorphism

The GNS data transports covariantly along an isomorphism of the algebras. Let
`Φ : A ≃⋆ₐ[ℂ] B` be a `*`-isomorphism of unital C*-algebras and `ω` a state on
`B`. Then the GNS representation of the pullback state `ω ∘ Φ` (`State.comp`) is
unitarily equivalent to `π_ω ∘ Φ`.

The mechanism is GNS uniqueness. Because `Φ` is surjective, the pulled-back
representation `π_ω ∘ Φ` of `A` on the *same* Hilbert space `H_ω` has the *same*
cyclic vector `Ω_ω` (the two orbits coincide as sets), and it reproduces `ω ∘ Φ`
by the defining equation of the pullback state. So `(H_ω, π_ω ∘ Φ, Ω_ω)` and any
GNS triple of `ω ∘ Φ` are two cyclic representations of `A` attached to the one
state `ω ∘ Φ`, and `gns_unique` supplies the intertwining unitary.

Combined with the invariance of irreducibility and factoriality under unitary
equivalence, this is the mechanism by which superselection sectors transport
along an isomorphism of the observable algebra.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A]
variable {B : Type*} [CStarAlgebra B]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Cyclicity pulls back along a surjective `*`-homomorphism.** If `Ω` is cyclic
for `π : B →⋆ₐ[ℂ] (H →L[ℂ] H)` and `Φ : A →⋆ₐ[ℂ] B` is surjective, then `Ω` is
cyclic for the composite representation `π ∘ Φ` of `A`: surjectivity makes the two
orbits `{π (Φ a) Ω}` and `{π b Ω}` coincide as sets, so density transfers. -/
theorem isCyclicVector_comp_of_surjective {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) {Φ : A →⋆ₐ[ℂ] B} (hsurj : Function.Surjective Φ) :
    IsCyclicVector (π.comp Φ) Ω := by
  unfold IsCyclicVector at *
  have h : (Set.range fun a : A => (π.comp Φ) a Ω) = (Set.range fun b : B => π b Ω) := by
    calc
      Set.range (fun a : A => (π.comp Φ) a Ω) = Set.range ((fun b : B => π b Ω) ∘ Φ) := by
        ext a; simp
      _ = Set.range (fun b : B => π b Ω) := hsurj.range_comp (fun b : B => π b Ω)
  rw [h]
  exact hcyc

/-- **GNS covariance under a `*`-isomorphism.** For `Φ : A ≃⋆ₐ[ℂ] B` and a state
`ω` on `B`: any cyclic representation `(H₁, π₁, Ω₁)` of `A` reproducing the pullback
state `ω ∘ Φ`, and any cyclic representation `(H₂, π₂, Ω₂)` of `B` reproducing `ω`,
are linked by a unitary `U : H₁ ≃ₗᵢ[ℂ] H₂` with `U Ω₁ = Ω₂` intertwining the
representations *along* `Φ`: `U (π₁ a x) = π₂ (Φ a) (U x)`. -/
theorem exists_unitary_of_gns_comp (Φ : A ≃⋆ₐ[ℂ] B) (ω : State B)
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (Ω₁ : H₁)
    (hcyc₁ : IsCyclicVector π₁ Ω₁)
    (hrep₁ : ∀ a : A, ((ω.comp Φ.toStarAlgHom) a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ)
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (π₂ : B →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) (Ω₂ : H₂)
    (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hrep₂ : ∀ b : B, (ω b : ℂ) = ⟪Ω₂, π₂ b Ω₂⟫_ℂ) :
    ∃ U : H₁ ≃ₗᵢ[ℂ] H₂,
      U Ω₁ = Ω₂ ∧ ∀ (a : A) (x : H₁), U (π₁ a x) = π₂ (Φ a) (U x) :=
  gns_unique (ω.comp Φ.toStarAlgHom) π₁ Ω₁ hcyc₁ hrep₁ (π₂.comp Φ.toStarAlgHom) Ω₂
    (isCyclicVector_comp_of_surjective hcyc₂ Φ.surjective) fun a => hrep₂ (Φ a)

/-- **The GNS representation of a pullback state.** Restated in the language of
unitary equivalence: the GNS representation of `ω ∘ Φ` is unitarily equivalent to
`π_ω ∘ Φ`. -/
theorem unitaryEquiv_comp_of_gns (Φ : A ≃⋆ₐ[ℂ] B) (ω : State B)
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (Ω₁ : H₁)
    (hcyc₁ : IsCyclicVector π₁ Ω₁)
    (hrep₁ : ∀ a : A, ((ω.comp Φ.toStarAlgHom) a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ)
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (π₂ : B →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) (Ω₂ : H₂)
    (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hrep₂ : ∀ b : B, (ω b : ℂ) = ⟪Ω₂, π₂ b Ω₂⟫_ℂ) :
    UnitaryEquiv π₁ (π₂.comp Φ.toStarAlgHom) := by
  obtain ⟨U, _, hUint⟩ :=
    exists_unitary_of_gns_comp Φ ω π₁ Ω₁ hcyc₁ hrep₁ π₂ Ω₂ hcyc₂ hrep₂
  refine ⟨U, fun a x => ?_⟩
  simpa [StarAlgHom.comp_apply] using hUint a x

/-! ### Transport of the representation type along a surjection -/

/-- **Pullback along a surjection preserves the image.** For surjective
`Φ : A →⋆ₐ[ℂ] B`, the composite `π ∘ Φ` has the same image as `π`. -/
theorem range_comp_of_surjective (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) {Φ : A →⋆ₐ[ℂ] B}
    (hsurj : Function.Surjective Φ) :
    Set.range (π.comp Φ) = Set.range π := by
  calc
    Set.range (π.comp Φ) = Set.range (⇑π ∘ ⇑Φ) := by
      ext a; simp
    _ = Set.range π := hsurj.range_comp (⇑π)

/-- **Irreducibility is unchanged by pullback along a surjection.** Irreducibility is
triviality of the commutant of the image, and the image is unchanged, so `π ∘ Φ` is
irreducible exactly when `π` is. -/
theorem isIrreducible_comp_iff {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)} {Φ : A →⋆ₐ[ℂ] B}
    (hsurj : Function.Surjective Φ) :
    IsIrreducible (π.comp Φ) ↔ IsIrreducible π := by
  rw [isIrreducible_iff_centralizer, isIrreducible_iff_centralizer,
    range_comp_of_surjective π hsurj]

/-- **The generated von Neumann algebra is unchanged by pullback along a surjection.**
Both are the double commutant of the same image: `(π ∘ Φ)(A)'' = π(B)''`. -/
theorem gnsVonNeumann_comp_of_surjective (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) {Φ : A →⋆ₐ[ℂ] B}
    (hsurj : Function.Surjective Φ) :
    gnsVonNeumann (π.comp Φ) = gnsVonNeumann π := by
  calc
    gnsVonNeumann (π.comp Φ) = Set.centralizer (Set.centralizer (Set.range (π.comp Φ))) := rfl
    _ = Set.centralizer (Set.centralizer (Set.range π)) := by
      rw [range_comp_of_surjective π hsurj]
    _ = gnsVonNeumann π := rfl

/-- **Irreducibility transports along a `*`-isomorphism.** With the GNS hypotheses of
`exists_unitary_of_gns_comp`, the GNS representation of the pullback state `ω ∘ Φ` is
irreducible exactly when the GNS representation of `ω` is. -/
theorem isIrreducible_iff_of_gns_comp (Φ : A ≃⋆ₐ[ℂ] B) (ω : State B)
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (Ω₁ : H₁)
    (hcyc₁ : IsCyclicVector π₁ Ω₁)
    (hrep₁ : ∀ a : A, ((ω.comp Φ.toStarAlgHom) a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ)
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (π₂ : B →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) (Ω₂ : H₂)
    (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hrep₂ : ∀ b : B, (ω b : ℂ) = ⟪Ω₂, π₂ b Ω₂⟫_ℂ) :
    IsIrreducible π₁ ↔ IsIrreducible π₂ :=
  ((unitaryEquiv_comp_of_gns Φ ω π₁ Ω₁ hcyc₁ hrep₁ π₂ Ω₂ hcyc₂ hrep₂).isIrreducible_iff).trans
    (isIrreducible_comp_iff (Φ := Φ.toStarAlgHom) Φ.surjective)

/-- **Factoriality transports along a `*`-isomorphism.** With the GNS hypotheses of
`exists_unitary_of_gns_comp`, `π₁(A)''` is a factor exactly when `π₂(B)''` is. So an
isomorphism of the observable algebra preserves the type of the superselection sector. -/
theorem isFactor_iff_of_gns_comp (Φ : A ≃⋆ₐ[ℂ] B) (ω : State B)
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (Ω₁ : H₁)
    (hcyc₁ : IsCyclicVector π₁ Ω₁)
    (hrep₁ : ∀ a : A, ((ω.comp Φ.toStarAlgHom) a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ)
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (π₂ : B →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) (Ω₂ : H₂)
    (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hrep₂ : ∀ b : B, (ω b : ℂ) = ⟪Ω₂, π₂ b Ω₂⟫_ℂ) :
    IsFactor (gnsVonNeumann π₁) ↔ IsFactor (gnsVonNeumann π₂) := by
  have h := (unitaryEquiv_comp_of_gns Φ ω π₁ Ω₁ hcyc₁ hrep₁ π₂ Ω₂ hcyc₂ hrep₂).isFactor_iff
  rwa [gnsVonNeumann_comp_of_surjective π₂ (Φ := Φ.toStarAlgHom) Φ.surjective] at h

end GNS
end Physicslib4
