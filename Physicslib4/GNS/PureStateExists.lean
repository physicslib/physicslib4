/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.ExtremeState
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Weak-* compactness of the state space

The state space of a unital C*-algebra, viewed inside the weak-* dual `WeakDual ℂ A`, is
**weak-* compact** (Banach-Alaoglu): it is a weak-* closed subset of the unit ball, being
the intersection of the (weak-* closed) positivity conditions `0 ≤ φ (star a * a)` and the
normalization `φ 1 = 1`. This is the first step toward the existence of pure states via
Krein-Milman.

## Main results

* `Physicslib4.GNS.weakStateSet` — the state space realized in `WeakDual ℂ A`.
* `Physicslib4.GNS.isClosed_weakStateSet` — it is weak-* closed.
* `Physicslib4.GNS.isCompact_weakStateSet` — it is weak-* compact.

## Note on pure-state existence

Concluding the *existence of a pure state* by Krein-Milman needs
`LocallyConvexSpace ℝ (WeakDual ℂ A)`, which in turn requires the scalar-tower instance
`IsScalarTower ℝ ℂ (A →L[ℂ] ℂ)`; the latter does not resolve in the current Mathlib due to
a real/complex module diamond on the dual space. The extreme-point-to-state transfer also
needs weak-* coercion-algebra lemmas (`(t • φ + (1-t) • ψ) a = t • φ a + (1-t) • ψ a`)
which Mathlib does not provide for `WeakDual`. Both are recorded as follow-ups; the
compactness result below is the reusable substance.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

/-- The state space realized inside the weak-* dual `WeakDual ℂ A`: the positive,
normalized (`φ 1 = 1`) continuous functionals. For a positive functional, `φ 1 = 1` is
equivalent to `‖φ‖ = 1`, so this is exactly the set of states. -/
def weakStateSet : Set (WeakDual ℂ A) :=
  {φ | (∀ a : A, (0 : ℂ) ≤ φ (star a * a)) ∧ φ 1 = 1}

/-- A state, viewed as an element of the weak-* dual. -/
noncomputable def State.toWeakDual (ω : State A) : WeakDual ℂ A :=
  StrongDual.toWeakDual ω.toContinuousLinearMap

@[simp] theorem State.toWeakDual_apply (ω : State A) (a : A) :
    ω.toWeakDual a = ω a := rfl

theorem State.toWeakDual_mem_weakStateSet (ω : State A) :
    ω.toWeakDual ∈ weakStateSet := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [State.toWeakDual_apply]; exact ω.isPositive a
  · rw [State.toWeakDual_apply]; exact ω.apply_one

/-- The nonnegative reals inside `ℂ` form a closed set. -/
theorem isClosed_complex_nonneg : IsClosed {z : ℂ | (0 : ℂ) ≤ z} := by
  have hset : {z : ℂ | (0 : ℂ) ≤ z}
      = (Complex.re ⁻¹' Set.Ici 0) ∩ (Complex.im ⁻¹' {0}) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici,
      Set.mem_singleton_iff, Complex.le_def, Complex.zero_re, Complex.zero_im]
    tauto
  rw [hset]
  exact (isClosed_Ici.preimage Complex.continuous_re).inter
    (isClosed_singleton.preimage Complex.continuous_im)

theorem isClosed_weakStateSet : IsClosed (weakStateSet : Set (WeakDual ℂ A)) := by
  have h1 : IsClosed {φ : WeakDual ℂ A | ∀ a : A, (0 : ℂ) ≤ φ (star a * a)} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun a =>
      isClosed_complex_nonneg.preimage (WeakDual.eval_continuous (star a * a))
  have h2 : IsClosed {φ : WeakDual ℂ A | φ 1 = 1} :=
    isClosed_singleton.preimage (WeakDual.eval_continuous 1)
  exact h1.inter h2

theorem isCompact_weakStateSet [Nontrivial A] :
    IsCompact (weakStateSet : Set (WeakDual ℂ A)) := by
  refine (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).of_isClosed_subset
    isClosed_weakStateSet ?_
  intro φ hφ
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  have hpos : ∀ a : A, 0 ≤ (WeakDual.toStrongDual φ) (star a * a) := by
    intro a; rw [WeakDual.toStrongDual_apply]; exact hφ.1 a
  rw [norm_eq_re_apply_one_of_positive hpos, WeakDual.toStrongDual_apply, hφ.2]
  simp

end GNS
end Physicslib4
