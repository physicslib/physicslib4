/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Minkowski

/-!
# Causal precedence in standard Minkowski spacetime

This file shows that causal precedence `p ≺ q` in standard Minkowski spacetime, for the standard
time orientation `∂₀`, places the displacement `q - p` in the closed forward cone
`V̄₊ = {v | η(v, v) ≤ 0, v⁰ ≥ 0}`. It derives a coordinate criterion for (complete) spacelike
separation: `p¹ - q¹ > |p⁰| + |q⁰|` forces `p` and `q` to be spacelike related.

The closed forward cone is not a new definition. It is written `closedV₊`, a local notation for
the set `{v : SpacetimeModel | minkowskiForm v v ≤ 0 ∧ 0 ≤ v 0}`, and the Euclidean norm of the
spatial part `(v¹, v², v³)` is written explicitly as `√((v¹)² + (v²)² + (v³)²)`.

## Main statements

* `standardMinkowski_causallyPrecedes_sub_mem_closedForwardCone`: `p ≺ q` implies `q - p ∈ V̄₊`.
* `standardMinkowski_isSpacelikeRelated_of_coord`: the coordinate criterion for spacelike
  separation.
* `standardMinkowski_isCompletelySpacelike_of_coord`: its version for sets.
-/

namespace Physicslib4

open scoped Manifold

/-- The closed forward cone `V̄₊ = {v ∈ ℝ⁴ | η(v, v) ≤ 0, v⁰ ≥ 0}` of standard Minkowski
spacetime, written as an explicit set. -/
local notation "closedV₊" =>
  Set.ofPred fun v : SpacetimeModel => minkowskiForm v v ≤ 0 ∧ 0 ≤ v 0

/-- A tangent vector of standard Minkowski spacetime that is future-pointing for the standard
time orientation lies in the closed forward cone: `η(v, v) ≤ 0` and `v⁰ ≥ 0`.

Blueprint: lmm:minkowski-future-pointing-closed-cone -/
theorem standardMinkowski_futurePointing_mem_closedForwardCone (x v : SpacetimeModel)
    (hv : StandardMinkowskiSpacetime.IsFuturePointing standardMinkowskiTimeOrientation
      (x := x) v) :
    v ∈ closedV₊ := by
  sorry

/-- The closed forward cone in norm form: `v ∈ V̄₊` if and only if `‖v⃗‖ ≤ v⁰`, where
`‖v⃗‖ = √((v¹)² + (v²)² + (v³)²)`. In particular every `v ∈ V̄₊` satisfies `|vⁱ| ≤ v⁰` for the
spatial indices `i = 1, 2, 3`.

Blueprint: lmm:closed-forward-cone-iff-norm -/
theorem mem_closedForwardCone_iff_sqrt_le (v : SpacetimeModel) :
    (v ∈ closedV₊ ↔ Real.sqrt ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) ≤ v 0) ∧
      (v ∈ closedV₊ → ∀ i : Fin 4, i ≠ 0 → |v i| ≤ v 0) := by
  sorry

/-- The closed forward cone is a closed convex cone: it is closed in `ℝ⁴`, contains `0`, and is
closed under addition and under multiplication by nonnegative scalars.

Blueprint: lmm:closed-forward-cone-closed-convex -/
theorem closedForwardCone_isClosed_convexCone :
    IsClosed closedV₊ ∧ (0 : SpacetimeModel) ∈ closedV₊ ∧
      (∀ v ∈ closedV₊, ∀ w ∈ closedV₊, v + w ∈ closedV₊) ∧
      ∀ c : ℝ, 0 ≤ c → ∀ v ∈ closedV₊, c • v ∈ closedV₊ := by
  sorry

/-- If `f : ℝ → ℝ⁴` is continuous on `[a, b]`, `a ≤ b`, and takes values in the closed forward
cone there, then `∫_a^b f(s) ds` lies in the closed forward cone.

Blueprint: lmm:interval-integral-closed-forward-cone -/
theorem intervalIntegral_mem_closedForwardCone {f : ℝ → SpacetimeModel} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hmem : ∀ s ∈ Set.Icc a b, f s ∈ closedV₊) :
    (∫ s in a..b, f s) ∈ closedV₊ := by
  sorry

/-- A causal trip segment `c` of standard Minkowski spacetime from `p` to `q` has a
representative smooth path `μ` with parameter space `[a, b]`, `a < b`, such that `μ(a) = p`,
`μ(b) = q`, the tangent `μ̇` is continuous on `[a, b]` and future-pointing at every
`s ∈ [a, b]`, and `q - p = ∫_a^b μ̇(s) ds`.

Blueprint: lmm:causal-trip-segment-displacement -/
theorem standardMinkowski_causalTripSegment_displacement {p q : SpacetimeModel}
    {c : StandardMinkowskiSpacetime.SmoothCurve}
    (hc : Spacetime.IsCausalTripSegment StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation p q c) :
    ∃ (μ : StandardMinkowskiSpacetime.SmoothPath) (a b : ℝ),
      c = Spacetime.SmoothCurve.ofPath StandardMinkowskiSpacetime μ ∧
      a < b ∧ μ.parameterSpace = Set.Icc a b ∧ μ.toFun a = p ∧ μ.toFun b = q ∧
      ContinuousOn
        (fun s => mfderivWithin (modelWithCornersSelf ℝ ℝ) StandardMinkowskiSpacetime.model
          μ.toFun μ.parameterSpace s (1 : ℝ))
        (Set.Icc a b) ∧
      (∀ s ∈ Set.Icc a b,
        StandardMinkowskiSpacetime.IsFuturePointing standardMinkowskiTimeOrientation
          (μ.tangent s)) ∧
      (q - p : SpacetimeModel) = ∫ s in a..b,
        mfderivWithin (modelWithCornersSelf ℝ ℝ) StandardMinkowskiSpacetime.model
          μ.toFun μ.parameterSpace s (1 : ℝ) := by
  sorry

/-- If a causal trip segment of standard Minkowski spacetime runs from `p` to `q`, then `q - p`
lies in the closed forward cone.

Blueprint: lmm:causal-trip-segment-closed-cone -/
theorem standardMinkowski_causalTripSegment_sub_mem_closedForwardCone {p q : SpacetimeModel}
    {c : StandardMinkowskiSpacetime.SmoothCurve}
    (hc : Spacetime.IsCausalTripSegment StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation p q c) :
    (q - p : SpacetimeModel) ∈ closedV₊ := by
  sorry

/-- Causal precedence `p ≺ q` in standard Minkowski spacetime, for the standard time orientation,
places `q - p` in the closed forward cone.

Blueprint: lmm:causal-precedence-closed-forward-cone -/
theorem standardMinkowski_causallyPrecedes_sub_mem_closedForwardCone {p q : SpacetimeModel}
    (hpq : Spacetime.CausallyPrecedes StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation p q) :
    (q - p : SpacetimeModel) ∈ closedV₊ := by
  sorry

/-- A coordinate criterion for spacelike separation: if `p¹ - q¹ > |p⁰| + |q⁰|`, then `p` and `q`
are spacelike related for the standard time orientation, that is, neither `p ≺ q` nor `q ≺ p`.

Blueprint: lmm:spacelike-of-coordinate-separation -/
theorem standardMinkowski_isSpacelikeRelated_of_coord {p q : SpacetimeModel}
    (hpq : |p 0| + |q 0| < p 1 - q 1) :
    Spacetime.IsSpacelikeRelated StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation p q := by
  sorry

/-- A coordinate criterion for complete spacelike separation: if `p¹ - q¹ > |p⁰| + |q⁰|` for
every `p ∈ O₁` and every `q ∈ O₂`, then `O₁` and `O₂` are completely spacelike for the standard
time orientation.

Blueprint: crllr:completely-spacelike-of-coordinate-separation -/
theorem standardMinkowski_isCompletelySpacelike_of_coord {O₁ O₂ : Set SpacetimeModel}
    (h : ∀ p ∈ O₁, ∀ q ∈ O₂, |p 0| + |q 0| < p 1 - q 1) :
    Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation O₁ O₂ := by
  sorry

end Physicslib4
