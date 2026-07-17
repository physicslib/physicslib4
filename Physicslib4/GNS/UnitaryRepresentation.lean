/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Construction
import Physicslib4.Analysis.StrongContinuity
import Mathlib.Analysis.Real.Sqrt

/-!
# GNS unitary representation of an invariant automorphism action

This file isolates the analytic core behind the GNS implementation of a
covariance action as a *standalone, algebra-agnostic* result: given any unital
C*-algebra `A`, a state `ω` on `A`, and a family of `*`-automorphisms
`γ : G → (A ≃⋆ₐ[ℂ] A)` (indexed by a monoid `G`) that *leaves `ω` invariant*,
the action is implemented on the GNS Hilbert space of `ω` by a unitary
representation `U : G → (H ≃ₗᵢ[ℂ] H)`.

## Main result

* `Physicslib4.GNS.exists_gns_unitary_of_invariant`: existence of the GNS triple
  `(H, π, Ω)` and the unitary representation `U` with `U g (π a Ω) = π (γ g a) Ω`,
  `U g Ω = Ω`, `U (g' * g) = U g' ∘ U g`, and `U 1 = id`.

## Design notes

This is the *local-state analogue* of the Minkowski quasilocal GNS unitary
(`IsInvariantState.exists_gns_unitary`): it depends only on a single C*-algebra
with an invariant automorphism family, not on a global quasilocal algebra. In
particular it applies directly to a *local* algebra `𝔘(B)` of a Haag-Kastler
net (in flat *or* curved spacetime) whenever the symmetry group acts on `𝔘(B)`
by automorphisms (e.g. the stabilizer subgroup of the region `B`), and the
Minkowski quasilocal version is recovered as the special case `A = 𝔘` with
`γ = β` the quasilocal covariance action.

The construction is the dense extension of the isometry `π a Ω ↦ π (γ g a) Ω`
(isometric because `ω (γ g a)⋆ (γ g b) = ω a⋆ b`, a consequence of invariance)
via `LinearEquiv.extendOfIsometry`. The representation laws follow from the
multiplicativity of `γ` by dense agreement on the cyclic vectors.
-/

namespace Physicslib4
namespace GNS

open scoped InnerProductSpace

/-- **Operator covariance of a GNS implementation.** If a family of unitaries
`U g` implements the action `γ` on the cyclic vector (`U g (π a Ω) = π (γ g a) Ω`)
and the vectors `π a Ω` are dense, then the implementation holds at the operator
level: `U g · π(a) · U(g)⁻¹ = π(γ g a)` on all of `H`. (No group structure on the
index `G` is needed; the inverse is the inverse of the unitary `U g`.) -/
theorem gns_operator_covariance {A : Type*} [CStarAlgebra A] {G : Type*}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H} {γ : G → (A ≃⋆ₐ[ℂ] A)}
    {U : G → (H ≃ₗᵢ[ℂ] H)}
    (hcyc : DenseRange fun a => π a Ω)
    (himpl : ∀ (g : G) (a : A), U g (π a Ω) = π (γ g a) Ω)
    (g : G) (a : A) (x : H) :
    U g (π a ((U g).symm x)) = π (γ g a) x := by
  have hint : (fun y => U g (π a y)) = fun y => π (γ g a) (U g y) := by
    refine Continuous.ext_on hcyc ((U g).continuous.comp (π a).continuous)
      ((π (γ g a)).continuous.comp (U g).continuous) ?_
    rintro _ ⟨b, rfl⟩
    change U g (π a (π b Ω)) = π (γ g a) (U g (π b Ω))
    have e1 : (π a) (π b Ω) = π (a * b) Ω := by
      rw [← mul_apply_eq_comp, ← map_mul]
    have e2 : (π (γ g a)) (π (γ g b) Ω) = π (γ g a * γ g b) Ω := by
      rw [← mul_apply_eq_comp, ← map_mul]
    rw [e1, himpl g (a * b), map_mul (γ g), himpl g b, e2]
  rw [show U g (π a ((U g).symm x)) = π (γ g a) (U g ((U g).symm x)) from
        congrFun hint ((U g).symm x), (U g).apply_symm_apply]

/-- **GNS unitary representation of an invariant automorphism action.**

For a unital C*-algebra `A`, a state `ω`, and a monoid-indexed family of
`*`-automorphisms `γ g : A ≃⋆ₐ[ℂ] A` leaving `ω` invariant (`ω (γ g a) = ω a`),
the action is implemented on the GNS space of `ω` by a unitary representation:
there is a GNS triple `(H, π, Ω)` and unitaries `U g` with
`U g (π a Ω) = π (γ g a) Ω`, `U g Ω = Ω`, `U (g' * g) = U g' ∘ U g`, and
`U 1 = id`. -/
theorem exists_gns_unitary_of_invariant.{u} {A : Type u} [CStarAlgebra A]
    {G : Type*} [Monoid G]
    (γ : G → (A ≃⋆ₐ[ℂ] A)) (ω : State A)
    (hinv : ∀ (g : G) (a : A), ω (γ g a) = ω a)
    (hmul : ∀ (g g' : G) (a : A), γ (g' * g) a = γ g' (γ g a))
    (hone : ∀ a : A, γ (1 : G) a = a) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : G → (H ≃ₗᵢ[ℂ] H)),
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (g : G) (a : A), U g (π a Ω) = π (γ g a) Ω) ∧
        (∀ g : G, U g Ω = Ω) ∧
        (∀ g g' : G, U (g' * g) = (U g).trans (U g')) ∧
        U 1 = LinearIsometryEquiv.refl ℂ H ∧
        (∀ (g : G) (a : A) (x : H), U g (π a ((U g).symm x)) = π (γ g a) x) ∧
        IsCyclicVector π Ω := by
  obtain ⟨H, _, _, _, π, Ω, hcyc, hrepro, _⟩ := gns_construction ω
  let cyc : A →ₗ[ℂ] H :=
    { toFun := fun a => π a Ω
      map_add' := fun a b => by rw [map_add, add_apply]
      map_smul' := fun c a => by rw [map_smul, smul_apply]; rfl }
  have hcycdense : DenseRange (cyc : A → H) := hcyc
  have q : ∀ x, (ω (star x * x) : ℂ) = ⟪π x Ω, π x Ω⟫_ℂ := by
    intro x
    rw [hrepro (star x * x), map_mul, map_star, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hinner : ∀ (g : G) (a b : A), ω (star (γ g a) * γ g b) = ω (star a * b) := by
    intro g a b
    rw [← map_star (γ g) a, ← map_mul (γ g)]
    exact hinv g (star a * b)
  have hnorm : ∀ (g : G) (a : A),
      ‖cyc ((γ g).toAlgEquiv.toLinearEquiv a)‖ = ‖cyc a‖ := by
    intro g a
    change ‖π (γ g a) Ω‖ = ‖π a Ω‖
    have key : ⟪π (γ g a) Ω, π (γ g a) Ω⟫_ℂ = ⟪π a Ω, π a Ω⟫_ℂ := by
      rw [← q (γ g a), ← q a]; exact hinner g a a
    have h2 : ‖π (γ g a) Ω‖ ^ 2 = ‖π a Ω‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact congrArg RCLike.re key
    rw [← Real.sqrt_sq (norm_nonneg (π (γ g a) Ω)),
      ← Real.sqrt_sq (norm_nonneg (π a Ω)), h2]
  let U : G → (H ≃ₗᵢ[ℂ] H) := fun g =>
    (γ g).toAlgEquiv.toLinearEquiv.extendOfIsometry cyc cyc hcycdense hcycdense (hnorm g)
  have hUcyc : ∀ (g : G) (a : A), U g (cyc a) = cyc (γ g a) := fun g a =>
    (γ g).toAlgEquiv.toLinearEquiv.extendOfIsometry_eq cyc cyc hcycdense hcycdense (hnorm g) a
  refine ⟨H, inferInstance, inferInstance, inferInstance, π, Ω, U, hrepro, ?_, ?_, ?_, ?_, ?_, hcyc⟩
  · intro g a
    exact (γ g).toAlgEquiv.toLinearEquiv.extendOfIsometry_eq cyc cyc hcycdense hcycdense
      (hnorm g) a
  · intro g
    have hΩ : cyc (1 : A) = Ω := by
      change π 1 Ω = Ω
      rw [map_one, one_apply_eq_self]
    have hone' : cyc ((γ g).toAlgEquiv.toLinearEquiv (1 : A)) = Ω := by
      change π (γ g 1) Ω = Ω
      rw [map_one (γ g)]
      change π 1 Ω = Ω
      rw [map_one, one_apply_eq_self]
    calc U g Ω = U g (cyc 1) := by rw [hΩ]
      _ = cyc ((γ g).toAlgEquiv.toLinearEquiv 1) :=
          (γ g).toAlgEquiv.toLinearEquiv.extendOfIsometry_eq cyc cyc hcycdense hcycdense
            (hnorm g) 1
      _ = Ω := hone'
  · intro g g'
    have hfun : (U (g' * g) : H → H) = fun x => U g' (U g x) := by
      refine Continuous.ext_on hcycdense (U (g' * g)).continuous
        ((U g').continuous.comp (U g).continuous) ?_
      rintro _ ⟨a, rfl⟩
      change U (g' * g) (cyc a) = U g' (U g (cyc a))
      rw [hUcyc, hUcyc, hUcyc, hmul g g' a]
    apply LinearIsometryEquiv.ext
    intro x
    rw [LinearIsometryEquiv.trans_apply]
    exact congrFun hfun x
  · have hfun : (U (1 : G) : H → H) = id := by
      refine Continuous.ext_on hcycdense (U 1).continuous continuous_id ?_
      rintro _ ⟨a, rfl⟩
      rw [hUcyc, hone, id_eq]
    apply LinearIsometryEquiv.ext
    intro x
    change U 1 x = x
    exact congrFun hfun x
  · exact fun g a x => gns_operator_covariance hcycdense hUcyc g a x

/-- **Bundled GNS unitary representation of an invariant action.** The bundled form
of `exists_gns_unitary_of_invariant`: the action enters as a group homomorphism
`γ : G →* (A ≃⋆ₐ[ℂ] A)`, and the implementing unitaries are returned as a bundled
group homomorphism `U : G →* (H ≃ₗᵢ[ℂ] H)` — a genuine unitary representation.

The group laws `U (g' * g) = U g' * U g` and `U 1 = 1` are now carried by `U`
itself (`map_mul`/`map_one`), so they no longer appear as separate hypotheses on
`γ` or clauses on `U`. What remains are the geometric clauses: the reproducing
formula, the implementation `U g (π a Ω) = π (γ g a) Ω`, vacuum invariance
`U g Ω = Ω`, operator covariance, and cyclicity. Both group structures use the
composition convention `f * g = g.trans f` (`StarAlgEquiv.aut`,
`LinearIsometryEquiv.instGroup`). -/
theorem exists_gns_unitaryRep_of_invariant.{u} {A : Type u} [CStarAlgebra A]
    {G : Type*} [Monoid G] (γ : G →* (A ≃⋆ₐ[ℂ] A)) (ω : State A)
    (hinv : ∀ (g : G) (a : A), ω (γ g a) = ω a) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : G →* (H ≃ₗᵢ[ℂ] H)),
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (g : G) (a : A), U g (π a Ω) = π (γ g a) Ω) ∧
        (∀ g : G, U g Ω = Ω) ∧
        (∀ (g : G) (a : A) (x : H), U g (π a ((U g).symm x)) = π (γ g a) x) ∧
        IsCyclicVector π Ω := by
  obtain ⟨H, _, _, _, π, Ω, U, hrepro, himpl, hΩ, hmulU, honeU, hopcov, hcyc⟩ :=
    exists_gns_unitary_of_invariant (fun g => γ g) ω hinv
      (fun g g' a => by rw [map_mul]; rfl) (fun a => by rw [map_one]; rfl)
  exact ⟨H, inferInstance, inferInstance, inferInstance, π, Ω,
    { toFun := U, map_one' := honeU, map_mul' := fun a b => hmulU b a },
    hrepro, himpl, hΩ, hopcov, hcyc⟩

/-- **Strongly continuous GNS unitary representation of an invariant action.**

Strengthening of `exists_gns_unitary_of_invariant`: if, in addition, the index
`G` carries a topology and the matrix coefficients `g ↦ ω(a⋆ · γ g b)` are
continuous for all `a, b : A` (the weak-continuity hypothesis), then the
implementing unitary representation `U` is *strongly continuous*:
`g ↦ U g ψ` is continuous for every vector `ψ`.

The proof feeds the analytic core `strongContinuous_of_weak`: the cyclic
vectors `π a Ω` are dense, and the matrix coefficient `g ↦ ⟪π a Ω, U g (π b Ω)⟫`
equals `g ↦ ω(a⋆ · γ g b)` (by the implementation property and the reproducing
formula), which is continuous by hypothesis. -/
theorem exists_gns_unitary_of_invariant_strongContinuous.{u} {A : Type u}
    [CStarAlgebra A] {G : Type*} [Monoid G] [TopologicalSpace G]
    (γ : G → (A ≃⋆ₐ[ℂ] A)) (ω : State A)
    (hinv : ∀ (g : G) (a : A), ω (γ g a) = ω a)
    (hmul : ∀ (g g' : G) (a : A), γ (g' * g) a = γ g' (γ g a))
    (hone : ∀ a : A, γ (1 : G) a = a)
    (hwc : ∀ a b : A, Continuous fun g : G => (ω (star a * γ g b) : ℂ)) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : G → (H ≃ₗᵢ[ℂ] H)),
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (g : G) (a : A), U g (π a Ω) = π (γ g a) Ω) ∧
        (∀ g : G, U g Ω = Ω) ∧
        (∀ g g' : G, U (g' * g) = (U g).trans (U g')) ∧
        U 1 = LinearIsometryEquiv.refl ℂ H ∧
        (∀ ψ : H, Continuous fun g : G => U g ψ) ∧
        (∀ (g : G) (a : A) (x : H), U g (π a ((U g).symm x)) = π (γ g a) x) := by
  obtain ⟨H, _, _, _, π, Ω, hcyc, hrepro, _⟩ := gns_construction ω
  let cyc : A →ₗ[ℂ] H :=
    { toFun := fun a => π a Ω
      map_add' := fun a b => by rw [map_add, add_apply]
      map_smul' := fun c a => by rw [map_smul, smul_apply]; rfl }
  have hcycdense : DenseRange (cyc : A → H) := hcyc
  have qq : ∀ a c : A, (ω (star a * c) : ℂ) = ⟪π a Ω, π c Ω⟫_ℂ := by
    intro a c
    rw [hrepro (star a * c), map_mul, map_star, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hinner : ∀ (g : G) (a b : A), ω (star (γ g a) * γ g b) = ω (star a * b) := by
    intro g a b
    rw [← map_star (γ g) a, ← map_mul (γ g)]
    exact hinv g (star a * b)
  have hnorm : ∀ (g : G) (a : A),
      ‖cyc ((γ g).toAlgEquiv.toLinearEquiv a)‖ = ‖cyc a‖ := by
    intro g a
    change ‖π (γ g a) Ω‖ = ‖π a Ω‖
    have key : ⟪π (γ g a) Ω, π (γ g a) Ω⟫_ℂ = ⟪π a Ω, π a Ω⟫_ℂ := by
      rw [← qq (γ g a) (γ g a), ← qq a a]; exact hinner g a a
    have h2 : ‖π (γ g a) Ω‖ ^ 2 = ‖π a Ω‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact congrArg RCLike.re key
    rw [← Real.sqrt_sq (norm_nonneg (π (γ g a) Ω)),
      ← Real.sqrt_sq (norm_nonneg (π a Ω)), h2]
  let U : G → (H ≃ₗᵢ[ℂ] H) := fun g =>
    (γ g).toAlgEquiv.toLinearEquiv.extendOfIsometry cyc cyc hcycdense hcycdense (hnorm g)
  have hUcyc : ∀ (g : G) (a : A), U g (cyc a) = cyc (γ g a) := fun g a =>
    (γ g).toAlgEquiv.toLinearEquiv.extendOfIsometry_eq cyc cyc hcycdense hcycdense (hnorm g) a
  refine ⟨H, inferInstance, inferInstance, inferInstance, π, Ω, U, hrepro,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g a
    exact (γ g).toAlgEquiv.toLinearEquiv.extendOfIsometry_eq cyc cyc hcycdense hcycdense
      (hnorm g) a
  · intro g
    have hΩ : cyc (1 : A) = Ω := by
      change π 1 Ω = Ω
      rw [map_one, one_apply_eq_self]
    have hone' : cyc ((γ g).toAlgEquiv.toLinearEquiv (1 : A)) = Ω := by
      change π (γ g 1) Ω = Ω
      rw [map_one (γ g)]
      change π 1 Ω = Ω
      rw [map_one, one_apply_eq_self]
    calc U g Ω = U g (cyc 1) := by rw [hΩ]
      _ = cyc ((γ g).toAlgEquiv.toLinearEquiv 1) :=
          (γ g).toAlgEquiv.toLinearEquiv.extendOfIsometry_eq cyc cyc hcycdense hcycdense
            (hnorm g) 1
      _ = Ω := hone'
  · intro g g'
    have hfun : (U (g' * g) : H → H) = fun x => U g' (U g x) := by
      refine Continuous.ext_on hcycdense (U (g' * g)).continuous
        ((U g').continuous.comp (U g).continuous) ?_
      rintro _ ⟨a, rfl⟩
      change U (g' * g) (cyc a) = U g' (U g (cyc a))
      rw [hUcyc, hUcyc, hUcyc, hmul g g' a]
    apply LinearIsometryEquiv.ext
    intro x
    rw [LinearIsometryEquiv.trans_apply]
    exact congrFun hfun x
  · have hfun : (U (1 : G) : H → H) = id := by
      refine Continuous.ext_on hcycdense (U 1).continuous continuous_id ?_
      rintro _ ⟨a, rfl⟩
      rw [hUcyc, hone, id_eq]
    apply LinearIsometryEquiv.ext
    intro x
    change U 1 x = x
    exact congrFun hfun x
  · -- strong continuity, via `strongContinuous_of_weak`
    refine Physicslib4.strongContinuous_of_weak U hcycdense ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have heq : (fun g : G => ⟪cyc a, U g (cyc b)⟫_ℂ)
        = fun g : G => (ω (star a * γ g b) : ℂ) := by
      funext g
      rw [hUcyc g b]
      change ⟪π a Ω, π (γ g b) Ω⟫_ℂ = (ω (star a * γ g b) : ℂ)
      rw [qq a (γ g b)]
    rw [heq]
    exact hwc a b
  · exact fun g a x => gns_operator_covariance hcycdense hUcyc g a x

/-- **Bundled strongly continuous GNS unitary representation.** The bundled form of
`exists_gns_unitary_of_invariant_strongContinuous`: the action enters as a group
homomorphism `γ : G →* (A ≃⋆ₐ[ℂ] A)` and the strongly continuous implementing
unitaries are returned as a bundled group homomorphism `U : G →* (H ≃ₗᵢ[ℂ] H)`. The
group laws are carried by `U`; the strong-continuity clause `g ↦ U g ψ` continuous
and the geometric clauses remain. -/
theorem exists_gns_unitaryRep_of_invariant_strongContinuous.{u} {A : Type u}
    [CStarAlgebra A] {G : Type*} [Monoid G] [TopologicalSpace G]
    (γ : G →* (A ≃⋆ₐ[ℂ] A)) (ω : State A)
    (hinv : ∀ (g : G) (a : A), ω (γ g a) = ω a)
    (hwc : ∀ a b : A, Continuous fun g : G => (ω (star a * γ g b) : ℂ)) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : G →* (H ≃ₗᵢ[ℂ] H)),
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (g : G) (a : A), U g (π a Ω) = π (γ g a) Ω) ∧
        (∀ g : G, U g Ω = Ω) ∧
        (∀ ψ : H, Continuous fun g : G => U g ψ) ∧
        (∀ (g : G) (a : A) (x : H), U g (π a ((U g).symm x)) = π (γ g a) x) := by
  obtain ⟨H, _, _, _, π, Ω, U, hrepro, himpl, hΩ, hmulU, honeU, hsc, hopcov⟩ :=
    exists_gns_unitary_of_invariant_strongContinuous (fun g => γ g) ω hinv
      (fun g g' a => by rw [map_mul]; rfl) (fun a => by rw [map_one]; rfl) hwc
  exact ⟨H, inferInstance, inferInstance, inferInstance, π, Ω,
    { toFun := U, map_one' := honeU, map_mul' := fun a b => hmulU b a },
    hrepro, himpl, hΩ, hsc, hopcov⟩

end GNS
end Physicslib4
