/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Minkowski

/-!
# Dilations are causal automorphisms but not isometries (Zeeman-lite)

A **dilation** `x ↦ λ x` (with `λ > 0`) of standard Minkowski spacetime preserves
the entire causal structure — the chronological order, the Alexandrov diamonds, and
hence complete spacelike separation — yet it is **not** an isometry: it scales the
Minkowski metric by `λ²`. This is the elementary core of Zeeman's theorem (the causal
automorphism group of Minkowski is strictly larger than the isometry group, the extra
generators being exactly the dilations), and it concretely exhibits the gap between
"causal automorphism" and "isometry".

The workhorse is that a positive dilation preserves the forward Minkowski cone: scaling
multiplies the defining quadratic form by `λ² > 0` and the time-order by `λ > 0`, so
membership is unchanged. Basis-set (diamond) preservation follows via the cone
characterization of the chronological future/past on standard Minkowski. Non-isometry
is the identity `g(λv, λw) = λ² g(v,w)`, which differs from `g(v,w)` whenever `λ² ≠ 1`.
-/

namespace Physicslib4

/-- **Dilations preserve the forward Minkowski cone.** For `λ > 0`,
`λ q ∈ I⁺(λ p) ↔ q ∈ I⁺(p)`: scaling multiplies the defining quadratic form by
`λ² > 0` and the time-order difference by `λ > 0`, so neither strict inequality
changes. -/
theorem minkowskiForwardCone_smul (lam : ℝ) (hlam : 0 < lam) (p q : SpacetimeModel) :
    lam • q ∈ minkowskiForwardCone (lam • p) ↔ q ∈ minkowskiForwardCone p := by
  sorry

/-- **Dilations preserve the backward Minkowski cone.** For `λ > 0`,
`λ p ∈ I⁻(λ q) ↔ p ∈ I⁻(q)`. -/
theorem minkowskiBackwardCone_smul (lam : ℝ) (hlam : 0 < lam) (p q : SpacetimeModel) :
    lam • p ∈ minkowskiBackwardCone (lam • q) ↔ p ∈ minkowskiBackwardCone q := by
  rw [minkowskiBackwardCone_eq, minkowskiBackwardCone_eq q]
  simp only [Set.mem_setOf_eq]
  exact minkowskiForwardCone_smul lam hlam p q

/-- **A positive dilation is a causal automorphism: it preserves the Alexandrov basis.**
For `λ > 0`, the image of a diamond `I⁺(p) ∩ I⁻(q)` under the dilation `x ↦ λ x` is
again a diamond, namely `I⁺(λ p) ∩ I⁻(λ q)`. Since the Alexandrov basis is the family
of such diamonds, the dilation carries basis sets to basis sets. -/
theorem alexandrovBasis_image_smul (lam : ℝ) (hlam : 0 < lam)
    {B : Set SpacetimeModel}
    (hB : B ∈ Spacetime.alexandrovBasis StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation) :
    (fun x => lam • x) '' B ∈ Spacetime.alexandrovBasis StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation := by
  sorry

/-- **The Minkowski metric scales by `λ²` under a dilation:**
`g(λ v, λ w) = λ² g(v, w)`. -/
theorem minkowskiForm_smul (lam : ℝ) (v w : SpacetimeModel) :
    minkowskiForm (lam • v) (lam • w) = lam ^ 2 * minkowskiForm v w := by
  simp [minkowskiForm_apply]; ring

/-- **Dilations are not isometries.** Whenever `λ² ≠ 1`, the dilation `x ↦ λ x` fails
to preserve the Minkowski form: taking the timelike unit vector `e₀`, one has
`g(λ e₀, λ e₀) = -λ² ≠ -1 = g(e₀, e₀)`. Combined with `alexandrovBasis_image_smul`,
this shows a positive dilation with `λ ≠ 1` is a causal automorphism that is not an
isometry. -/
theorem exists_minkowskiForm_smul_ne (lam : ℝ) (hlam : lam ^ 2 ≠ 1) :
    ∃ v w : SpacetimeModel,
      minkowskiForm (lam • v) (lam • w) ≠ minkowskiForm v w := by
  set e₀ : SpacetimeModel := EuclideanSpace.single (0 : Fin 4) (1 : ℝ) with he₀
  have h_e₀_form : minkowskiForm e₀ e₀ = -1 := by
    simp [minkowskiForm_apply, he₀]
  refine ⟨e₀, e₀, ?_⟩
  rw [minkowskiForm_smul lam e₀ e₀, h_e₀_form]
  intro h
  apply hlam
  linarith

end Physicslib4
