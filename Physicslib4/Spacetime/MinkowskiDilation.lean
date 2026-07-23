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
  rw [mem_minkowskiForwardCone, mem_minkowskiForwardCone]
  have hp0 : (lam • p) 0 = lam * p 0 := by simp
  have hp1 : (lam • p) 1 = lam * p 1 := by simp
  have hp2 : (lam • p) 2 = lam * p 2 := by simp
  have hp3 : (lam • p) 3 = lam * p 3 := by simp
  have hq0 : (lam • q) 0 = lam * q 0 := by simp
  have hq1 : (lam • q) 1 = lam * q 1 := by simp
  have hq2 : (lam • q) 2 = lam * q 2 := by simp
  have hq3 : (lam • q) 3 = lam * q 3 := by simp
  rw [hp0, hp1, hp2, hp3, hq0, hq1, hq2, hq3]
  have hsqpos : 0 < lam ^ 2 := pow_pos hlam 2
  constructor
  · rintro ⟨h_time, h_quad⟩
    constructor
    · nlinarith
    · have h_quad' : -(lam * q 0 - lam * p 0) ^ 2 + (lam * q 1 - lam * p 1) ^ 2 +
        (lam * q 2 - lam * p 2) ^ 2 + (lam * q 3 - lam * p 3) ^ 2
        = lam ^ 2 * (-(q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 + (q 2 - p 2) ^ 2 + (q 3 - p 3) ^ 2) := by
        ring
      rw [h_quad'] at h_quad
      nlinarith
  · rintro ⟨h_time, h_quad⟩
    constructor
    · nlinarith
    · have h_quad' : -(lam * q 0 - lam * p 0) ^ 2 + (lam * q 1 - lam * p 1) ^ 2 +
        (lam * q 2 - lam * p 2) ^ 2 + (lam * q 3 - lam * p 3) ^ 2
        = lam ^ 2 * (-(q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 + (q 2 - p 2) ^ 2 + (q 3 - p 3) ^ 2) := by
        ring
      rw [h_quad']
      nlinarith

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
  simp only [Spacetime.alexandrovBasis, Set.mem_setOf_eq] at hB ⊢
  obtain ⟨p, q, rfl⟩ := hB
  refine ⟨lam • p, lam • q, ?_⟩
  ext y
  simp only [Set.mem_image, Set.mem_inter_iff]
  rw [chronologicalFuture_standardMinkowski (p : SpacetimeModel),
    chronologicalPast_standardMinkowski (q : SpacetimeModel),
    chronologicalFuture_standardMinkowski (lam • (p : SpacetimeModel)),
    chronologicalPast_standardMinkowski (lam • (q : SpacetimeModel))]
  constructor
  · rintro ⟨x, ⟨hxF, hxB⟩, rfl⟩
    exact ⟨(minkowskiForwardCone_smul lam hlam _ x).mpr hxF,
      (minkowskiBackwardCone_smul lam hlam x _).mpr hxB⟩
  · rintro ⟨hyF, hyB⟩
    refine ⟨lam⁻¹ • y, ⟨?_, ?_⟩, smul_inv_smul₀ hlam.ne' y⟩
    · have hcalc : lam • (lam⁻¹ • (y : SpacetimeModel)) = (y : SpacetimeModel) := by
        simp [smul_smul, hlam.ne']
      have htemp : lam • (lam⁻¹ • y : SpacetimeModel) ∈ minkowskiForwardCone
          (lam • (p : SpacetimeModel)) := by
        rw [hcalc]
        exact hyF
      exact (minkowskiForwardCone_smul lam hlam (p : SpacetimeModel)
        (lam⁻¹ • y : SpacetimeModel)).mp htemp
    · have hcalc : lam • (lam⁻¹ • (y : SpacetimeModel)) = (y : SpacetimeModel) := by
        simp [smul_smul, hlam.ne']
      have htemp : lam • (lam⁻¹ • y : SpacetimeModel) ∈ minkowskiBackwardCone
          (lam • (q : SpacetimeModel)) := by
        rw [hcalc]
        exact hyB
      exact (minkowskiBackwardCone_smul lam hlam (lam⁻¹ • y : SpacetimeModel)
        (q : SpacetimeModel)).mp htemp

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
