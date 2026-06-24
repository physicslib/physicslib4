/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Construction
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Irreducibility of representations and Schur's lemma

A `*`-representation `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)` is *irreducible* when its
commutant is trivial: the only bounded operators commuting with every `π a` are
the scalar multiples of the identity. This is the von Neumann (commutant) form of
irreducibility, the operator-algebra counterpart of "no nontrivial closed
invariant subspace".

The central analytic fact is the **topological Schur lemma** for a cyclic
representation: if `T` commutes with all `π a` and its diagonal GNS coefficient
`a ↦ ⟪Ω, T (π a Ω)⟫` is proportional to `a ↦ ⟪Ω, π a Ω⟫`, then `T` is the
corresponding scalar. The proof is pure Hilbert-space analysis: the off-diagonal
coefficients `⟪π b Ω, (T - c) (π a Ω)⟫` all vanish (using the `*`-representation
property and the commutation relation), so `(T - c)` annihilates the dense cyclic
orbit and is therefore zero.

This is the bridge between the commutant and the GNS state: a commutant operator
is a scalar exactly when its GNS coefficient is proportional to the state.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A `*`-representation `π` of `A` on `H` is **irreducible** when its commutant is
trivial: every bounded operator `T` commuting with all `π a` is a scalar multiple
of the identity. -/
def IsIrreducible (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ T : H →L[ℂ] H, (∀ a : A, π a * T = T * π a) → ∃ c : ℂ, T = c • 1

/-- **Topological Schur lemma (proportional coefficient ⟹ scalar).** Let `Ω` be a
cyclic vector for `π`. If `T` commutes with every `π a` and the diagonal GNS
coefficient `a ↦ ⟪Ω, T (π a Ω)⟫` equals `c` times `a ↦ ⟪Ω, π a Ω⟫`, then
`T = c • 1`. The key step is that all off-diagonal coefficients
`⟪π b Ω, (T - c) (π a Ω)⟫` vanish, so `(T - c)` kills the dense cyclic orbit. -/
theorem eq_smul_one_of_commute_of_cyclic
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H} (hcyc : IsCyclicVector π Ω)
    {T : H →L[ℂ] H} (hT : ∀ a : A, π a * T = T * π a)
    {c : ℂ} (hprop : ∀ a : A, ⟪Ω, T (π a Ω)⟫_ℂ = c * ⟪Ω, π a Ω⟫_ℂ) :
    T = c • 1 := by
  have hcycdense : DenseRange (fun a : A => π a Ω) := hcyc
  -- The adjoint of `π b` is `π (star b)` (since `π` is a `*`-homomorphism).
  have hop : ∀ b : A, ContinuousLinearMap.adjoint (π b) = π (star b) := fun b => by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_star]
  -- Move `π b` to the other slot of the inner product via the adjoint.
  have hadj : ∀ (b : A) (w : H), ⟪(π b) Ω, w⟫_ℂ = ⟪Ω, π (star b) w⟫_ℂ := fun b w => by
    rw [← hop b, ContinuousLinearMap.adjoint_inner_right]
  -- `T` agrees with `c • ·` on the cyclic orbit.
  have hkey : ∀ a : A, T (π a Ω) = c • (π a Ω) := by
    intro a
    have hzero : ∀ b : A, ⟪π b Ω, T (π a Ω) - c • (π a Ω)⟫_ℂ = 0 := by
      intro b
      rw [inner_sub_right, inner_smul_right]
      have e1 : ⟪(π b) Ω, T (π a Ω)⟫_ℂ = ⟪Ω, T (π (star b * a) Ω)⟫_ℂ := by
        rw [hadj b (T (π a Ω))]
        congr 1
        have h1 : (π (star b)) (T (π a Ω)) = T ((π (star b)) (π a Ω)) :=
          calc (π (star b)) (T (π a Ω))
              = (π (star b) * T) (π a Ω) := by rw [ContinuousLinearMap.mul_apply]
            _ = (T * π (star b)) (π a Ω) := by rw [hT (star b)]
            _ = T ((π (star b)) (π a Ω)) := by rw [ContinuousLinearMap.mul_apply]
        rw [h1]
        congr 1
        rw [← ContinuousLinearMap.mul_apply, ← map_mul]
      have e2 : ⟪(π b) Ω, π a Ω⟫_ℂ = ⟪Ω, π (star b * a) Ω⟫_ℂ := by
        rw [hadj b (π a Ω)]
        congr 1
        rw [← ContinuousLinearMap.mul_apply, ← map_mul]
      rw [e1, e2, hprop (star b * a)]
      ring
    have hw0 : T (π a Ω) - c • (π a Ω) = 0 := by
      have hcont : Continuous (fun y : H => ⟪y, T (π a Ω) - c • (π a Ω)⟫_ℂ) :=
        continuous_id.inner continuous_const
      have heqon : Set.EqOn (fun y : H => ⟪y, T (π a Ω) - c • (π a Ω)⟫_ℂ)
          (fun _ => (0 : ℂ)) (Set.range fun a' : A => π a' Ω) := by
        rintro _ ⟨b, rfl⟩; exact hzero b
      have hzeroall := congrFun
        (Continuous.ext_on hcycdense hcont continuous_const heqon)
        (T (π a Ω) - c • (π a Ω))
      exact inner_self_eq_zero.mp hzeroall
    exact sub_eq_zero.mp hw0
  -- Density + continuity upgrade the agreement to all of `H`.
  have hall : (fun x => T x) = (fun x : H => c • x) :=
    Continuous.ext_on hcycdense T.continuous (continuous_const.smul continuous_id)
      (by rintro _ ⟨a, rfl⟩; exact hkey a)
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  exact congrFun hall x

/-- **A commutant operator is a scalar iff its GNS coefficient is proportional to
the state.** In a cyclic representation reproducing `ω`, an operator `T` commuting
with all `π a` is a scalar multiple of the identity exactly when its diagonal
coefficient `a ↦ ⟪Ω, T (π a Ω)⟫` is a scalar multiple of `ω`. This is the precise
operator-theoretic bridge between irreducibility and purity: it is the forward
(easy) direction together with the topological Schur lemma. -/
theorem isScalar_iff_coeff_proportional
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H} (hcyc : IsCyclicVector π Ω)
    {ω : State A} (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {T : H →L[ℂ] H} (hT : ∀ a : A, π a * T = T * π a) :
    (∃ c : ℂ, T = c • 1) ↔ ∃ t : ℂ, ∀ a : A, ⟪Ω, T (π a Ω)⟫_ℂ = t * (ω a : ℂ) := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, fun a => ?_⟩
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right,
      ← hrep a]
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    apply eq_smul_one_of_commute_of_cyclic hcyc hT
    intro a
    rw [ht a, hrep a]

/-- A state `ω` is **pure** if every positive linear functional `ψ` dominated by
`ω` (i.e. `0 ≤ ψ(a* a) ≤ ω(a* a)`) is a scalar multiple of `ω`. This is the
order-theoretic characterization of purity (extreme point of the state space),
phrased so that no convex-combination/normalization bookkeeping is needed. -/
def IsPure (ω : State A) : Prop :=
  ∀ ψ : A →L[ℂ] ℂ, (∀ a : A, 0 ≤ ψ (star a * a)) →
    (∀ a : A, ψ (star a * a) ≤ ω (star a * a)) →
      ∃ t : ℂ, ∀ a : A, ψ a = t * (ω a : ℂ)

end GNS
end Physicslib4
