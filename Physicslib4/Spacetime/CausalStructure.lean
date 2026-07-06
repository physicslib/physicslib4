/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.Basic

/-!
# Causal structure on a spacetime

This file formalises the pointwise causal structure attached to a spacetime,
following section 10.2 of the AQFT-in-Lean blueprint.

## Main definitions

* `Physicslib4.Spacetime.IsTimelike`, `IsSpacelike`, `IsNull`: classification of
  tangent vectors by the sign of `g x v v`.
* `Physicslib4.Spacetime.TimeOrientation`: a smooth non-vanishing global
  timelike vector field, presented as a section of the tangent bundle.
* `Physicslib4.Spacetime.IsTimeOrientable`: existence of a time orientation.
* `Physicslib4.Spacetime.IsFuturePointing` / `IsPastPointing`: the classification
  of timelike (and null, by a limit construction) tangent vectors against a
  chosen time orientation.

## Modelling notes

Mathlib does not currently package "smooth vector field" as a single named type.
We use the obvious unbundled form: a function `t : ∀ x, TangentSpace M.model x`
together with two pointwise predicates (non-vanishing and timelike) and an
unbundled smoothness statement carried as a `Prop` field. Smoothness of a
section of the tangent bundle is captured exactly as in `Spacetime.smooth_in_charts`:
by writing the chart-local expression and requiring `ContDiffWithinAt`.

For the null future/past-pointing case we follow the blueprint and define
future-pointing null vectors as the closure (in the obvious tangent space
topology coming from `TangentSpace M.model x ≃ ℝ⁴`) of the set of
future-pointing timelike vectors. We capture this with the existence of a
sequence of future-pointing timelike vectors tending to `n`. The underlying
topology on each tangent space is inherited from Mathlib's tangent space
typeclass instances.
-/

namespace Physicslib4

namespace Spacetime

variable (M : Spacetime)

attribute [instance] Spacetime.topology Spacetime.hausdorff Spacetime.connected
  Spacetime.chartedSpace Spacetime.isManifold Spacetime.tangent_findim

/-! ### Classification of tangent vectors -/

/-- A tangent vector `v ∈ T_pM` is *timelike* if `g|_p(v,v) < 0`. -/
def IsTimelike {x : M.Carrier} (v : TangentSpace M.model x) : Prop :=
  M.val x v v < 0

/-- A tangent vector `v ∈ T_pM` is *spacelike* if `g|_p(v,v) > 0`. -/
def IsSpacelike {x : M.Carrier} (v : TangentSpace M.model x) : Prop :=
  0 < M.val x v v

/-- A tangent vector `v ∈ T_pM` is *null* if `g|_p(v,v) = 0`. -/
def IsNull {x : M.Carrier} (v : TangentSpace M.model x) : Prop :=
  M.val x v v = 0

/-! ### Basic classification lemmas

Every tangent vector falls into exactly one of the three classes, fixed by the
sign of `g|_p(v,v)`. -/

/-- Causal trichotomy: every tangent vector is timelike, null, or spacelike. -/
theorem isTimelike_or_isNull_or_isSpacelike {x : M.Carrier}
    (v : TangentSpace M.model x) :
    M.IsTimelike v ∨ M.IsNull v ∨ M.IsSpacelike v :=
  lt_trichotomy (M.val x v v) 0

/-- A timelike vector is not spacelike. -/
theorem not_isSpacelike_of_isTimelike {x : M.Carrier}
    {v : TangentSpace M.model x} (h : M.IsTimelike v) : ¬ M.IsSpacelike v :=
  fun hs => lt_asymm h hs

/-- A spacelike vector is not timelike. -/
theorem not_isTimelike_of_isSpacelike {x : M.Carrier}
    {v : TangentSpace M.model x} (h : M.IsSpacelike v) : ¬ M.IsTimelike v :=
  fun ht => lt_asymm ht h

/-- A timelike vector is not null. -/
theorem not_isNull_of_isTimelike {x : M.Carrier}
    {v : TangentSpace M.model x} (h : M.IsTimelike v) : ¬ M.IsNull v :=
  ne_of_lt h

/-- A spacelike vector is not null. -/
theorem not_isNull_of_isSpacelike {x : M.Carrier}
    {v : TangentSpace M.model x} (h : M.IsSpacelike v) : ¬ M.IsNull v :=
  ne_of_gt h

/-- The zero tangent vector is null. -/
theorem isNull_zero {x : M.Carrier} : M.IsNull (0 : TangentSpace M.model x) := by
  simp [IsNull]

/-! ### Scaling invariance of the causal classification

The causal type of a tangent vector depends only on the sign of `g(v,v)`, which
scales quadratically under `v ↦ c • v`. Hence for `c ≠ 0` the timelike / null /
spacelike classification is invariant under scaling — the algebraic fact behind
reparametrisation-invariance of the causal type of a curve. -/

/-- The metric square scales quadratically: `g(c•v, c•v) = c² · g(v,v)`. -/
theorem val_smul_smul {x : M.Carrier} (c : ℝ) (v : TangentSpace M.model x) :
    M.val x (c • v) (c • v) = c ^ 2 * M.val x v v := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Scaling invariance of timelikeness.** For `c ≠ 0`, `c • v` is timelike iff
`v` is. -/
theorem isTimelike_smul_iff {x : M.Carrier} {c : ℝ} (hc : c ≠ 0)
    (v : TangentSpace M.model x) : M.IsTimelike (c • v) ↔ M.IsTimelike v := by
  have hc2 : 0 < c ^ 2 := by positivity
  simp only [IsTimelike, val_smul_smul]
  constructor <;> intro h <;> nlinarith [hc2]

/-- **Scaling invariance of nullness.** For `c ≠ 0`, `c • v` is null iff `v` is. -/
theorem isNull_smul_iff {x : M.Carrier} {c : ℝ} (hc : c ≠ 0)
    (v : TangentSpace M.model x) : M.IsNull (c • v) ↔ M.IsNull v := by
  have hc2 : ¬ (c ^ 2 = 0) := pow_ne_zero 2 hc
  simp only [IsNull, val_smul_smul, mul_eq_zero]
  tauto

/-- **Scaling invariance of spacelikeness.** For `c ≠ 0`, `c • v` is spacelike iff
`v` is. -/
theorem isSpacelike_smul_iff {x : M.Carrier} {c : ℝ} (hc : c ≠ 0)
    (v : TangentSpace M.model x) : M.IsSpacelike (c • v) ↔ M.IsSpacelike v := by
  have hc2 : 0 < c ^ 2 := by positivity
  simp only [IsSpacelike, val_smul_smul]
  constructor <;> intro h <;> nlinarith [hc2]

/-! ### Time orientation -/

/--
A *time orientation* on a spacetime `M` is a smooth, non-vanishing,
everywhere-timelike vector field on `M`.

We unbundle the data as:
* `field : ∀ x, T_xM`, the pointwise tangent vector;
* `nonvanishing`: `field x ≠ 0` for all `x`;
* `timelike_at`: `field x` is timelike at every `x`;
* `smooth`: smoothness of the section in any extended chart, expressed via
  the chart-local form of the field. This is a genuine `Prop` field of the
  structure (a `ContDiffWithinAt` condition on the chart-local
  representative), discharged for concrete time orientations — see
  `standardMinkowskiTimeOrientation` in `Minkowski.lean`.
-/
structure TimeOrientation where
  /-- The underlying tangent vector field. -/
  field : ∀ x : M.Carrier, TangentSpace M.model x
  /-- The field is everywhere non-zero. -/
  nonvanishing : ∀ x : M.Carrier, field x ≠ 0
  /-- The field is timelike at every point. -/
  timelike_at : ∀ x : M.Carrier, M.IsTimelike (field x)
  /-- The field is smooth as a section of the tangent bundle. We express this
  via smoothness of its chart-local representative; see `Spacetime.smooth_in_charts`
  for the analogous condition for the metric. -/
  smooth : ∀ (x₀ : M.Carrier),
    let e := extChartAt M.model x₀
    ContDiffWithinAt ℝ ⊤
      (fun y => mfderiv M.model M.model (e.symm) y
                  (mfderiv M.model M.model e (e.symm y) (field (e.symm y))))
      e.target (e x₀)

/-- A spacetime `M` is *time-orientable* if it admits a time orientation. -/
def IsTimeOrientable : Prop := Nonempty M.TimeOrientation

/-! ### Future and past pointing vectors -/

/-- A timelike tangent vector `v` is *future-pointing* with respect to a time
orientation `t` if `g|_p(t,v) < 0`. The blueprint also extends this notion to
null vectors by taking limits of timelike future-pointing vectors. -/
def IsFuturePointing (t : M.TimeOrientation) {x : M.Carrier}
    (v : TangentSpace M.model x) : Prop :=
  (M.IsTimelike v ∧ M.val x (t.field x) v < 0) ∨
  (M.IsNull v ∧
    ∃ vs : ℕ → TangentSpace M.model x,
      (∀ n, M.IsTimelike (vs n) ∧ M.val x (t.field x) (vs n) < 0) ∧
      Filter.Tendsto vs Filter.atTop (nhds v))

/-- A timelike tangent vector `v` is *past-pointing* with respect to a time
orientation `t` if `g|_p(t,v) > 0`. The blueprint also extends this notion to
null vectors by taking limits of timelike past-pointing vectors. -/
def IsPastPointing (t : M.TimeOrientation) {x : M.Carrier}
    (v : TangentSpace M.model x) : Prop :=
  (M.IsTimelike v ∧ 0 < M.val x (t.field x) v) ∨
  (M.IsNull v ∧
    ∃ vs : ℕ → TangentSpace M.model x,
      (∀ n, M.IsTimelike (vs n) ∧ 0 < M.val x (t.field x) (vs n)) ∧
      Filter.Tendsto vs Filter.atTop (nhds v))

/-! ### Future/past-pointing classification lemmas -/

/-- A future-pointing vector is either timelike or null. -/
theorem isTimelike_or_isNull_of_isFuturePointing (t : M.TimeOrientation)
    {x : M.Carrier} {v : TangentSpace M.model x}
    (h : M.IsFuturePointing t v) : M.IsTimelike v ∨ M.IsNull v :=
  h.imp And.left And.left

/-- A past-pointing vector is either timelike or null. -/
theorem isTimelike_or_isNull_of_isPastPointing (t : M.TimeOrientation)
    {x : M.Carrier} {v : TangentSpace M.model x}
    (h : M.IsPastPointing t v) : M.IsTimelike v ∨ M.IsNull v :=
  h.imp And.left And.left

/-- A timelike vector cannot be both future-pointing and past-pointing with
respect to a fixed time orientation. -/
theorem not_isFuturePointing_and_isPastPointing_of_isTimelike
    (t : M.TimeOrientation) {x : M.Carrier} {v : TangentSpace M.model x}
    (hv : M.IsTimelike v) :
    ¬ (M.IsFuturePointing t v ∧ M.IsPastPointing t v) := by
  rintro ⟨hf, hp⟩
  have hft : M.val x (t.field x) v < 0 := by
    rcases hf with ⟨_, h⟩ | ⟨hn, _⟩
    · exact h
    · exact absurd hn (M.not_isNull_of_isTimelike hv)
  have hpt : 0 < M.val x (t.field x) v := by
    rcases hp with ⟨_, h⟩ | ⟨hn, _⟩
    · exact h
    · exact absurd hn (M.not_isNull_of_isTimelike hv)
  exact lt_asymm hft hpt

/-! ### Positive-scaling invariance of orientation

Unlike the causal *type* (invariant under any non-zero scaling), future/past-
pointing is preserved only under scaling by a **positive** scalar — scaling by a
negative one swaps the two. This is the algebraic fact behind the
reparametrisation-invariance of the *orientation* of a curve under
orientation-preserving reparametrisations. -/

/-- Linearity of the metric in the second argument: `g(t, c • v) = c · g(t, v)`. -/
theorem val_field_smul (t : M.TimeOrientation) {x : M.Carrier} (c : ℝ)
    (v : TangentSpace M.model x) :
    M.val x (t.field x) (c • v) = c * M.val x (t.field x) v := by
  simp only [map_smul, smul_eq_mul]

/-- **Positive scaling preserves future-pointing** (forward direction). -/
theorem isFuturePointing_smul_of (t : M.TimeOrientation) {x : M.Carrier} {c : ℝ}
    (hc : 0 < c) {v : TangentSpace M.model x} (h : M.IsFuturePointing t v) :
    M.IsFuturePointing t (c • v) := by
  rcases h with ⟨htl, hlt⟩ | ⟨hnull, vs, hvs, htends⟩
  · exact Or.inl ⟨(M.isTimelike_smul_iff hc.ne' v).mpr htl, by
      rw [val_field_smul]; exact mul_neg_of_pos_of_neg hc hlt⟩
  · refine Or.inr ⟨(M.isNull_smul_iff hc.ne' v).mpr hnull,
      fun n => c • vs n, fun n => ⟨?_, ?_⟩, htends.const_smul c⟩
    · exact (M.isTimelike_smul_iff hc.ne' (vs n)).mpr (hvs n).1
    · rw [val_field_smul]; exact mul_neg_of_pos_of_neg hc (hvs n).2

/-- **Positive-scaling invariance of future-pointing.** For `c > 0`, `c • v` is
future-pointing iff `v` is. -/
theorem isFuturePointing_smul_iff (t : M.TimeOrientation) {x : M.Carrier} {c : ℝ}
    (hc : 0 < c) (v : TangentSpace M.model x) :
    M.IsFuturePointing t (c • v) ↔ M.IsFuturePointing t v := by
  refine ⟨fun h => ?_, M.isFuturePointing_smul_of t hc⟩
  have h' := M.isFuturePointing_smul_of t (inv_pos.mpr hc) h
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h'

/-- **Positive scaling preserves past-pointing** (forward direction). -/
theorem isPastPointing_smul_of (t : M.TimeOrientation) {x : M.Carrier} {c : ℝ}
    (hc : 0 < c) {v : TangentSpace M.model x} (h : M.IsPastPointing t v) :
    M.IsPastPointing t (c • v) := by
  rcases h with ⟨htl, hgt⟩ | ⟨hnull, vs, hvs, htends⟩
  · exact Or.inl ⟨(M.isTimelike_smul_iff hc.ne' v).mpr htl, by
      rw [val_field_smul]; exact mul_pos hc hgt⟩
  · refine Or.inr ⟨(M.isNull_smul_iff hc.ne' v).mpr hnull,
      fun n => c • vs n, fun n => ⟨?_, ?_⟩, htends.const_smul c⟩
    · exact (M.isTimelike_smul_iff hc.ne' (vs n)).mpr (hvs n).1
    · rw [val_field_smul]; exact mul_pos hc (hvs n).2

/-- **Positive-scaling invariance of past-pointing.** For `c > 0`, `c • v` is
past-pointing iff `v` is. -/
theorem isPastPointing_smul_iff (t : M.TimeOrientation) {x : M.Carrier} {c : ℝ}
    (hc : 0 < c) (v : TangentSpace M.model x) :
    M.IsPastPointing t (c • v) ↔ M.IsPastPointing t v := by
  refine ⟨fun h => ?_, M.isPastPointing_smul_of t hc⟩
  have h' := M.isPastPointing_smul_of t (inv_pos.mpr hc) h
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h'

end Spacetime

end Physicslib4
