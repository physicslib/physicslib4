/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Basic

/-!
# The GNS Construction Theorem

This file states the GNS Construction Theorem from the AQFT-in-Lean blueprint
(section 10.1, label `thrm:gns-construction-theorem`).

Given a state `ω` over a unital C*-algebra `A`, the theorem asserts the
existence of a complex Hilbert space `H_ω`, a *-representation
`π_ω : A →⋆ₐ[ℂ] (H_ω →L[ℂ] H_ω)`, and a cyclic vector `Ω ∈ H_ω` for `π_ω`
such that
* `ω a = ⟪Ω, π_ω a Ω⟫` for every `a : A`, and
* if `ω` is faithful, then `π_ω` is injective.

The triple is also unique up to unitary equivalence, which we state as a
separate theorem `gns_unique` because expressing the uniqueness clause as a
conjunct inside the existence statement above is awkward (the two Hilbert
spaces being compared live in different types).

## Main statements

* `Physicslib4.GNS.gns_construction`: existence of the GNS triple `(H, π, Ω)`,
  with the cyclicity, reproducing-formula, and faithfulness clauses bundled
  inside a single existential.
* `Physicslib4.GNS.gns_unique`: uniqueness of the GNS triple up to a unitary
  equivalence intertwining the representations and sending the cyclic vector
  to the cyclic vector.

## Notes

The Hilbert space `H` is existentially quantified in `Type` (rather than
`Type*`) to avoid the usual universe-polymorphism issues that arise when
existentially quantifying over a type variable. In practice the GNS Hilbert
space is constructed as a completion of a quotient of `A`, so this is not
a real restriction provided one is willing to work universe-polymorphically
in `A`'s universe; the precise universe placement is left to the eventual
proof.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder
open scoped InnerProductSpace

/-- Repackaging of `State` as a `PositiveLinearMap`, for use with Mathlib's GNS
infrastructure. -/
private noncomputable def State.toPositiveLinearMap
    {A : Type*} [CStarAlgebra A]
    (ω : State A) [PartialOrder A] [StarOrderedRing A] :
    A →ₚ[ℂ] ℂ where
  toFun := ω.toContinuousLinearMap
  map_add' := by intro x y; exact map_add ω.toContinuousLinearMap x y
  map_smul' := by intro c x; exact map_smul ω.toContinuousLinearMap c x
  monotone' := by
    intro a b hab
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hba
    have h_pos : 0 ≤ ω.toContinuousLinearMap (b - a) := by
      rw [hy]; exact ω.isPositive y
    have hsub : ω.toContinuousLinearMap (b - a)
        = ω.toContinuousLinearMap b - ω.toContinuousLinearMap a := by
      simp [map_sub]
    rw [hsub] at h_pos
    exact sub_nonneg.mp h_pos

/--
**GNS Construction Theorem** (blueprint label `thrm:gns-construction-theorem`).

Let `ω` be a state over a unital C*-algebra `A`. Then there exist a complex
Hilbert space `H`, a *-representation `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)`, and a
cyclic vector `Ω : H` for `π`, such that the reproducing formula
`ω a = ⟪Ω, π a Ω⟫_ℂ` holds for every `a : A`. Moreover, if `ω` is faithful
then `π` is injective.

The Hilbert space `H` lives in the same universe as `A`, which is the
universe `f.GNS` lands in for `f : A →ₚ[ℂ] ℂ`.

Uniqueness up to unitary equivalence is stated separately as `gns_unique`.
-/
theorem gns_construction.{u} {A : Type u} [CStarAlgebra A] (ω : State A) :
    ∃ (H : Type u)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (ω.IsFaithful → Function.Injective π) := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  haveI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set f : A →ₚ[ℂ] ℂ := ω.toPositiveLinearMap with hf
  refine ⟨f.GNS, inferInstance, inferInstance, inferInstance, f.gnsStarAlgHom,
    ((f.toPreGNS 1 : f.PreGNS) : f.GNS), ?cyclic, ?rep, ?inj⟩
  case cyclic =>
    unfold IsCyclicVector
    have hkey : ∀ a : A,
        f.gnsStarAlgHom a ((f.toPreGNS 1 : f.PreGNS) : f.GNS)
          = ((f.toPreGNS a : f.PreGNS) : f.GNS) := by
      intro a
      simp [PositiveLinearMap.gnsStarAlgHom_apply,
            PositiveLinearMap.gnsNonUnitalStarAlgHom_apply,
            ContinuousLinearMap.completion_apply_coe,
            PositiveLinearMap.leftMulMapPreGNS_apply,
            PositiveLinearMap.ofPreGNS, PositiveLinearMap.toPreGNS]
    rw [show (Set.range fun a : A => f.gnsStarAlgHom a
              ((f.toPreGNS 1 : f.PreGNS) : f.GNS))
            = Set.range (fun a : A => ((f.toPreGNS a : f.PreGNS) : f.GNS)) by
              ext y
              refine ⟨fun ⟨a, ha⟩ => ⟨a, ?_⟩, fun ⟨a, ha⟩ => ⟨a, ?_⟩⟩
              · simp only at ha; rw [← ha]; exact (hkey a).symm
              · simp only at ha; rw [← ha]; exact (hkey a)]
    have h_range_eq : Set.range (fun a : A => ((f.toPreGNS a : f.PreGNS) : f.GNS))
        = Set.range ((↑) : f.PreGNS → f.GNS) := by
      ext y; constructor
      · rintro ⟨a, rfl⟩; exact ⟨f.toPreGNS a, rfl⟩
      · rintro ⟨p, rfl⟩
        refine ⟨f.ofPreGNS p, ?_⟩
        change ((f.toPreGNS (f.ofPreGNS p) : f.PreGNS) : f.GNS) = (p : f.GNS)
        rw [show f.toPreGNS (f.ofPreGNS p) = p from f.toPreGNS.apply_symm_apply p]
    rw [h_range_eq]
    exact UniformSpace.Completion.denseRange_coe
  case rep =>
    intro a
    have hkey : f.gnsStarAlgHom a ((f.toPreGNS 1 : f.PreGNS) : f.GNS)
        = ((f.toPreGNS a : f.PreGNS) : f.GNS) := by
      simp [PositiveLinearMap.gnsStarAlgHom_apply,
            PositiveLinearMap.gnsNonUnitalStarAlgHom_apply,
            ContinuousLinearMap.completion_apply_coe,
            PositiveLinearMap.leftMulMapPreGNS_apply,
            PositiveLinearMap.ofPreGNS, PositiveLinearMap.toPreGNS]
    rw [hkey, UniformSpace.Completion.inner_coe,
        PositiveLinearMap.preGNS_inner_def]
    change (ω a : ℂ) = f (star (f.ofPreGNS (f.toPreGNS 1)) * f.ofPreGNS (f.toPreGNS a))
    have h1 : f.ofPreGNS (f.toPreGNS 1) = 1 := f.toPreGNS.symm_apply_apply 1
    have h2 : f.ofPreGNS (f.toPreGNS a) = a := f.toPreGNS.symm_apply_apply a
    rw [h1, h2, star_one, one_mul]
    rfl
  case inj =>
    intro hfaith a b hab
    have hsub : f.gnsStarAlgHom (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have hkey : ∀ c : A, f.gnsStarAlgHom c ((f.toPreGNS 1 : f.PreGNS) : f.GNS)
        = ((f.toPreGNS c : f.PreGNS) : f.GNS) := by
      intro c
      simp [PositiveLinearMap.gnsStarAlgHom_apply,
            PositiveLinearMap.gnsNonUnitalStarAlgHom_apply,
            ContinuousLinearMap.completion_apply_coe,
            PositiveLinearMap.leftMulMapPreGNS_apply,
            PositiveLinearMap.ofPreGNS, PositiveLinearMap.toPreGNS]
    have happ : f.gnsStarAlgHom (a - b) ((f.toPreGNS 1 : f.PreGNS) : f.GNS) = 0 := by
      rw [hsub]; rfl
    rw [hkey] at happ
    have hinner : (⟪((f.toPreGNS (a-b) : f.PreGNS) : f.GNS),
                    ((f.toPreGNS (a-b) : f.PreGNS) : f.GNS)⟫_ℂ) = 0 := by
      rw [happ, inner_zero_right]
    rw [UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def] at hinner
    have hab_eq : f.ofPreGNS (f.toPreGNS (a - b)) = a - b :=
      f.toPreGNS.symm_apply_apply (a - b)
    rw [hab_eq] at hinner
    have h_omega : ω (star (a - b) * (a - b)) = 0 := hinner
    by_contra hne
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hfaith (a - b) hne'
    rw [h_omega] at hpos
    exact lt_irrefl _ hpos

/--
**Uniqueness of the GNS triple, up to unitary equivalence**
(blueprint label `thrm:gns-construction-theorem`, uniqueness clause).

Suppose two GNS-type triples `(H₁, π₁, Ω₁)` and `(H₂, π₂, Ω₂)` are both
associated to the same state `ω` on the unital C*-algebra `A`, in the sense
that each is a cyclic *-representation reproducing `ω` via its inner
product. Then there exists a unitary (linear isometric) equivalence
`U : H₁ ≃ₗᵢ[ℂ] H₂` intertwining the representations
(`U (π₁ a x) = π₂ a (U x)` for all `a` and `x`) and sending `Ω₁` to `Ω₂`.
-/
theorem gns_unique {A : Type*} [CStarAlgebra A] (ω : State A)
    {H₁ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (Ω₁ : H₁)
    (hcyc₁ : IsCyclicVector π₁ Ω₁)
    (hrep₁ : ∀ a : A, (ω a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ)
    {H₂ : Type*}
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) (Ω₂ : H₂)
    (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hrep₂ : ∀ a : A, (ω a : ℂ) = ⟪Ω₂, π₂ a Ω₂⟫_ℂ) :
    ∃ U : H₁ ≃ₗᵢ[ℂ] H₂,
      U Ω₁ = Ω₂ ∧ ∀ (a : A) (x : H₁), U (π₁ a x) = π₂ a (U x) := by
  let e₁ : A →ₗ[ℂ] H₁ :=
    { toFun := fun a => π₁ a Ω₁
      map_add' := fun a b => by simp [map_add, add_apply]
      map_smul' := fun c a => by simp [map_smul, smul_apply] }
  let e₂ : A →ₗ[ℂ] H₂ :=
    { toFun := fun a => π₂ a Ω₂
      map_add' := fun a b => by simp [map_add, add_apply]
      map_smul' := fun c a => by simp [map_smul, smul_apply] }
  have hdense₁ : DenseRange e₁ := hcyc₁
  have hdense₂ : DenseRange e₂ := hcyc₂
  have hinner_eq : ∀ a b : A, ⟪e₁ a, e₁ b⟫_ℂ = ⟪e₂ a, e₂ b⟫_ℂ := by
    intro a b
    change ⟪π₁ a Ω₁, π₁ b Ω₁⟫_ℂ = ⟪π₂ a Ω₂, π₂ b Ω₂⟫_ℂ
    have h1 : ⟪π₁ a Ω₁, π₁ b Ω₁⟫_ℂ = ⟪Ω₁, π₁ (star a * b) Ω₁⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right,
          ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
      rw [map_mul, mul_apply_eq_comp]
    have h2 : ⟪π₂ a Ω₂, π₂ b Ω₂⟫_ℂ = ⟪Ω₂, π₂ (star a * b) Ω₂⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right,
          ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
      rw [map_mul, mul_apply_eq_comp]
    rw [h1, h2, ← hrep₁, ← hrep₂]
  have hnorm : ∀ a : A, ‖e₂ a‖ = ‖e₁ a‖ := by
    intro a
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg (e₁ a))]
    congr 1
    rw [← @inner_self_eq_norm_sq ℂ _ _ _ _ (e₂ a),
        ← @inner_self_eq_norm_sq ℂ _ _ _ _ (e₁ a)]
    exact congrArg Complex.re (hinner_eq a a).symm
  let f : A ≃ₗ[ℂ] A := LinearEquiv.refl ℂ A
  have hnorm_f : ∀ a : A, ‖e₂ (f a)‖ = ‖e₁ a‖ := fun a => by
    change ‖e₂ a‖ = ‖e₁ a‖; exact hnorm a
  refine ⟨f.extendOfIsometry e₁ e₂ hdense₁ hdense₂ hnorm_f, ?_, ?_⟩
  · have hΩ₁ : Ω₁ = e₁ 1 := by
      change Ω₁ = π₁ 1 Ω₁
      rw [map_one]; rfl
    have hΩ₂ : Ω₂ = e₂ 1 := by
      change Ω₂ = π₂ 1 Ω₂
      rw [map_one]; rfl
    rw [hΩ₁, hΩ₂, LinearEquiv.extendOfIsometry_eq]
    rfl
  · intro a x
    set U := f.extendOfIsometry e₁ e₂ hdense₁ hdense₂ hnorm_f
    have hkey : ∀ b : A, U (π₁ a (π₁ b Ω₁)) = π₂ a (U (π₁ b Ω₁)) := by
      intro b
      have h1 : π₁ a (π₁ b Ω₁) = e₁ (a * b) := by
        change π₁ a (π₁ b Ω₁) = π₁ (a * b) Ω₁
        rw [map_mul]; rfl
      have h2 : π₁ b Ω₁ = e₁ b := rfl
      rw [h1, h2, LinearEquiv.extendOfIsometry_eq, LinearEquiv.extendOfIsometry_eq]
      change e₂ (a * b) = π₂ a (e₂ b)
      change π₂ (a * b) Ω₂ = π₂ a (π₂ b Ω₂)
      rw [map_mul]; rfl
    have hcont : Continuous (fun x : H₁ => U (π₁ a x)) := by
      have : Continuous (π₁ a) := (π₁ a).continuous
      exact U.continuous.comp this
    have hcont' : Continuous (fun x : H₁ => π₂ a (U x)) := by
      have : Continuous (π₂ a) := (π₂ a).continuous
      exact this.comp U.continuous
    have hset : ∀ y ∈ Set.range (fun b : A => π₁ b Ω₁),
        U (π₁ a y) = π₂ a (U y) := by
      rintro y ⟨b, rfl⟩
      exact hkey b
    have heq_set : {x : H₁ | U (π₁ a x) = π₂ a (U x)} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      have hclosed : IsClosed {x : H₁ | U (π₁ a x) = π₂ a (U x)} :=
        isClosed_eq hcont hcont'
      have hsub : Set.range (fun b : A => π₁ b Ω₁) ⊆ {x | U (π₁ a x) = π₂ a (U x)} := hset
      have hdense_set : Dense {x : H₁ | U (π₁ a x) = π₂ a (U x)} :=
        hcyc₁.mono hsub
      exact (hclosed.closure_eq ▸ hdense_set.closure_eq ▸ Set.mem_univ x : _)
    have : x ∈ {x : H₁ | U (π₁ a x) = π₂ a (U x)} := by
      rw [heq_set]; trivial
    exact this

end GNS
end Physicslib4
