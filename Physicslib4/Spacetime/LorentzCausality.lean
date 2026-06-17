/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LorentzCovariance

/-!
# Lorentz invariance of the causal structure on Minkowski spacetime

This file proves that the inhomogeneous Lorentz group acts on the causal
vocabulary of standard Minkowski spacetime: a Lorentz transformation maps
causal trips to causal trips, hence preserves causal precedence `≺`, and
therefore preserves spacelike-relatedness and complete spacelikeness.

## Strategy

The Lorentz action `g • x = g.linear x + g.translation` is *affine* with
`Lorentz` (metric-preserving), orthochronous linear part. Pushing a smooth
path `μ` forward by `g` (`lorentzPath`) replaces its tangent vector at every
parameter point by the image under `g.linear` (`lorentzPath_mfderivWithin`),
because the constant translation drops out of the derivative and standard
Minkowski spacetime is modelled on its own tangent space. Since `g.linear`

* preserves the Minkowski form (so timelike/null tangents stay timelike/null),
  giving `lorentzPath_isCausal`; and
* is orthochronous (so the future cone is preserved, via
  `isOrthochronous_pos_time_of_timelike`), giving `lorentzPath_isFutureOriented`,

the pushed-forward path is again a future-oriented causal geodesic with the
transported endpoints. This yields `causallyPrecedes_smul(_iff)`, and the
abstract lemmas `isSpacelikeRelated_congr` / `isCompletelySpacelike_image`
conclude invariance of `IsSpacelikeRelated` and `IsCompletelySpacelike`.

## Main results

* `Physicslib4.Spacetime.isSpacelikeRelated_congr`,
  `Physicslib4.Spacetime.isCompletelySpacelike_image`: the abstract logical
  core (any precedence-preserving map preserves the spacelike vocabulary).
* `Physicslib4.lorentzPath`: the Lorentz pushforward of a smooth path.
* `Physicslib4.causallyPrecedes_smul_iff`: causal precedence is Lorentz
  invariant.
* `Physicslib4.isSpacelikeRelated_smul_iff`,
  `Physicslib4.isCompletelySpacelike_smul_iff`: invariance of
  spacelike-relatedness and complete spacelikeness under the Lorentz action.
-/

namespace Physicslib4

namespace Spacetime

variable (M : Spacetime)

attribute [instance] Spacetime.topology Spacetime.hausdorff Spacetime.connected
  Spacetime.chartedSpace Spacetime.isManifold Spacetime.tangent_findim

/-- **Spacelike-relatedness is invariant under a precedence-preserving map.**
If `g` preserves causal precedence in both directions (for a fixed time
orientation `t`), then `g p₁` and `g p₂` are spacelike related iff `p₁` and
`p₂` are. -/
theorem isSpacelikeRelated_congr (t : M.TimeOrientation)
    (g : M.Carrier → M.Carrier)
    (hg : ∀ p q, CausallyPrecedes M t (g p) (g q) ↔ CausallyPrecedes M t p q)
    (p₁ p₂ : M.Carrier) :
    IsSpacelikeRelated M t (g p₁) (g p₂) ↔ IsSpacelikeRelated M t p₁ p₂ := by
  simp only [IsSpacelikeRelated, Set.mem_union, causalFuture, causalPast,
    Set.mem_setOf_eq, not_or, hg]

/-- **Complete spacelikeness is invariant under taking images by a
precedence-preserving map.** If `g` preserves causal precedence in both
directions, then the images `g '' O₁` and `g '' O₂` are completely spacelike
iff `O₁` and `O₂` are. -/
theorem isCompletelySpacelike_image (t : M.TimeOrientation)
    (g : M.Carrier → M.Carrier)
    (hg : ∀ p q, CausallyPrecedes M t (g p) (g q) ↔ CausallyPrecedes M t p q)
    (O₁ O₂ : Set M.Carrier) :
    IsCompletelySpacelike M t (g '' O₁) (g '' O₂)
      ↔ IsCompletelySpacelike M t O₁ O₂ := by
  constructor
  · intro h p₁ hp₁ p₂ hp₂
    have := h (g p₁) ⟨p₁, hp₁, rfl⟩ (g p₂) ⟨p₂, hp₂, rfl⟩
    exact (isSpacelikeRelated_congr M t g hg p₁ p₂).mp this
  · rintro h a ⟨p₁, hp₁, rfl⟩ b ⟨p₂, hp₂, rfl⟩
    exact (isSpacelikeRelated_congr M t g hg p₁ p₂).mpr (h p₁ hp₁ p₂ hp₂)

/-- The parameter space of a smooth path (a closed, connected, non-singleton
subset of `ℝ`) has the unique-differential property at each of its points: it
is a convex set with non-empty interior. -/
theorem SmoothPath.uniqueDiffWithinAt {M : Spacetime} (μ : M.SmoothPath)
    {s : ℝ} (hs : s ∈ μ.parameterSpace) :
    UniqueDiffWithinAt ℝ μ.parameterSpace s := by
  have hord : μ.parameterSpace.OrdConnected :=
    μ.isConnected.isPreconnected.ordConnected
  have hconv : Convex ℝ μ.parameterSpace := convex_iff_ordConnected.mpr hord
  obtain ⟨a, b, ha, hb, hab⟩ := μ.nontrivial
  have key : ∀ x y, x ∈ μ.parameterSpace → y ∈ μ.parameterSpace → x < y →
      (interior μ.parameterSpace).Nonempty := by
    intro x y hx hy hxy
    have hsub : Set.Ioo x y ⊆ interior μ.parameterSpace :=
      interior_maximal (Set.Ioo_subset_Icc_self.trans (hord.out hx hy)) isOpen_Ioo
    exact ⟨(x + y) / 2, hsub ⟨by linarith, by linarith⟩⟩
  have hint : (interior μ.parameterSpace).Nonempty := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b ha hb h
    · exact key b a hb ha h
  exact uniqueDiffOn_convex hconv hint s hs

end Spacetime

/-! ### The Lorentz pushforward of a smooth path -/

open Spacetime
open AQFT.HaagKastler
open scoped Pointwise

/-- `StandardMinkowskiSpacetime.Carrier` is definitionally `SpacetimeModel`
(`= EuclideanSpace ℝ (Fin 4)`); expose its normed/finite-dimensional structure
so that the Fréchet-derivative and continuity API applies to the affine
Lorentz action directly. -/
noncomputable instance : NormedAddCommGroup StandardMinkowskiSpacetime.Carrier :=
  inferInstanceAs (NormedAddCommGroup SpacetimeModel)

noncomputable instance : NormedSpace ℝ StandardMinkowskiSpacetime.Carrier :=
  inferInstanceAs (NormedSpace ℝ SpacetimeModel)

instance : FiniteDimensional ℝ StandardMinkowskiSpacetime.Carrier :=
  inferInstanceAs (FiniteDimensional ℝ SpacetimeModel)

/-- For a smooth path `μ` on standard Minkowski spacetime, the manifold
derivative of its Lorentz pushforward `s ↦ g.linear (μ s) + g.translation`
equals `g.linear` applied to the derivative of `μ`. The constant translation
drops out, and on the self-modelled manifold the manifold derivative reduces
to the Fréchet derivative, for which the chain rule with the continuous linear
map `g.linear` applies. -/
theorem lorentzPath_mfderivWithin (g : InhomogeneousLorentzGroup)
    (μ : StandardMinkowskiSpacetime.SmoothPath) {s : ℝ}
    (hs : s ∈ μ.parameterSpace) :
    mfderivWithin (modelWithCornersSelf ℝ ℝ) StandardMinkowskiSpacetime.model
        (fun u => g.linear (μ.toFun u) + g.translation) μ.parameterSpace s (1 : ℝ)
      = g.linear (mfderivWithin (modelWithCornersSelf ℝ ℝ)
          StandardMinkowskiSpacetime.model μ.toFun μ.parameterSpace s (1 : ℝ)) := by
  -- Reduce each manifold derivative to a Fréchet derivative as a *term*, so the
  -- model stays as `StandardMinkowskiSpacetime.model` (whose space is `Carrier`)
  -- and the underlying functions remain type-correct (no `rw` unfolding that
  -- would mismatch `Carrier` with `SpacetimeModel`).
  have hclmF : mfderivWithin (modelWithCornersSelf ℝ ℝ)
        StandardMinkowskiSpacetime.model
        (fun u => g.linear (μ.toFun u) + g.translation) μ.parameterSpace s
      = fderivWithin ℝ (fun u => g.linear (μ.toFun u) + g.translation)
          μ.parameterSpace s := mfderivWithin_eq_fderivWithin
  have hclmμ : mfderivWithin (modelWithCornersSelf ℝ ℝ)
        StandardMinkowskiSpacetime.model μ.toFun μ.parameterSpace s
      = fderivWithin ℝ μ.toFun μ.parameterSpace s := mfderivWithin_eq_fderivWithin
  rw [hclmF, hclmμ]
  set L : StandardMinkowskiSpacetime.Carrier →L[ℝ] StandardMinkowskiSpacetime.Carrier :=
    LinearMap.toContinuousLinearMap g.linear.toLinearMap with hLdef
  have hcd : ContDiffOn ℝ ⊤ μ.toFun μ.parameterSpace :=
    contMDiffOn_iff_contDiffOn.mp μ.smoothOn
  have hdiff : DifferentiableWithinAt ℝ μ.toFun μ.parameterSpace s :=
    hcd.differentiableOn (by norm_num) s hs
  have hμ : HasFDerivWithinAt μ.toFun
      (fderivWithin ℝ μ.toFun μ.parameterSpace s) μ.parameterSpace s :=
    hdiff.hasFDerivWithinAt
  have hcomp : HasFDerivWithinAt (fun u => L (μ.toFun u))
      (L.comp (fderivWithin ℝ μ.toFun μ.parameterSpace s)) μ.parameterSpace s :=
    L.hasFDerivAt.comp_hasFDerivWithinAt s hμ
  have hcomp2 : HasFDerivWithinAt (fun u => L (μ.toFun u) + g.translation)
      (L.comp (fderivWithin ℝ μ.toFun μ.parameterSpace s)) μ.parameterSpace s :=
    hcomp.add_const g.translation
  have hu : UniqueDiffWithinAt ℝ μ.parameterSpace s :=
    SmoothPath.uniqueDiffWithinAt μ hs
  have hgoalfun : (fun u => g.linear (μ.toFun u) + g.translation)
      = (fun u => L (μ.toFun u) + g.translation) := rfl
  rw [hgoalfun, hcomp2.fderivWithin hu]
  rfl

/-- The **Lorentz pushforward** of a smooth path on standard Minkowski
spacetime: `g` acts on each point of the path by the affine map
`x ↦ g.linear x + g.translation`. The parameter space is unchanged; the new
path is smooth (affine composition) with non-vanishing derivative (`g.linear`
is injective). -/
noncomputable def lorentzPath (g : InhomogeneousLorentzGroup)
    (μ : StandardMinkowskiSpacetime.SmoothPath) :
    StandardMinkowskiSpacetime.SmoothPath where
  parameterSpace := μ.parameterSpace
  isClosed := μ.isClosed
  isConnected := μ.isConnected
  nontrivial := μ.nontrivial
  toFun := fun s => g.linear (μ.toFun s) + g.translation
  continuousOn := by
    have hcont : Continuous
        (fun w : StandardMinkowskiSpacetime.Carrier => g.linear w) :=
      g.linear.toLinearMap.continuous_of_finiteDimensional
    exact (hcont.comp_continuousOn μ.continuousOn).add continuousOn_const
  smoothOn := by
    have hcd : ContDiffOn ℝ ⊤ μ.toFun μ.parameterSpace :=
      contMDiffOn_iff_contDiffOn.mp μ.smoothOn
    have hL : ContDiff ℝ (⊤ : WithTop ℕ∞)
        (fun w : StandardMinkowskiSpacetime.Carrier => g.linear w) :=
      (LinearMap.toContinuousLinearMap g.linear.toLinearMap).contDiff
    have hcomp : ContDiffOn ℝ ⊤
        (fun s => g.linear (μ.toFun s) + g.translation) μ.parameterSpace :=
      (hL.comp_contDiffOn hcd).add contDiffOn_const
    exact contMDiffOn_iff_contDiffOn.mpr hcomp
  nonvanishing := by
    intro s hs
    rw [lorentzPath_mfderivWithin g μ hs]
    exact fun hzero =>
      μ.nonvanishing s hs ((LinearEquiv.map_eq_zero_iff g.linear).mp hzero)

/-! ### Preservation of the causal predicates -/

/-- `g.linear` preserves the timelike condition: it is a Minkowski isometry,
so `⟨g v, g v⟩ = ⟨v, v⟩`. Stated at the level of the underlying model space to
sidestep tangent-space defeq friction. -/
theorem isTimelike_linear (g : InhomogeneousLorentzGroup) {w : SpacetimeModel}
    (h : minkowskiForm w w < 0) :
    minkowskiForm (g.linear w) (g.linear w) < 0 :=
  lt_of_eq_of_lt (g.isLorentz w w) h

/-- `g.linear` preserves the null condition (it is a Minkowski isometry). -/
theorem isNull_linear (g : InhomogeneousLorentzGroup) {w : SpacetimeModel}
    (h : minkowskiForm w w = 0) :
    minkowskiForm (g.linear w) (g.linear w) = 0 :=
  (g.isLorentz w w).trans h

/-- `g.linear` maps a future-pointing timelike vector to a future-pointing
timelike vector. The Minkowski square is preserved (isometry) and the time
component stays positive because `g.linear` is orthochronous
(`isOrthochronous_pos_time_of_timelike`). -/
theorem minkowskiForm_linear_future (g : InhomogeneousLorentzGroup)
    {w : SpacetimeModel}
    (hww : minkowskiForm w w < 0)
    (hfut : minkowskiForm (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) w < 0) :
    minkowskiForm (g.linear w) (g.linear w) < 0 ∧
      minkowskiForm (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) (g.linear w) < 0 := by
  have hval : minkowskiForm (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) w
      = -(w.ofLp 0) := minkowskiForm_single_zero_left w
  have hpos : 0 < w.ofLp 0 := by rw [hval] at hfut; linarith
  have hLpos : 0 < (g.linear w).ofLp 0 :=
    isOrthochronous_pos_time_of_timelike g.isLorentz g.isOrthochronous hww hpos
  exact ⟨lt_of_eq_of_lt (g.isLorentz w w) hww,
    lt_of_eq_of_lt (minkowskiForm_single_zero_left (g.linear w)) (by linarith)⟩

/-- The Lorentz pushforward of a causal path is causal. -/
theorem lorentzPath_isCausal (g : InhomogeneousLorentzGroup)
    (μ : StandardMinkowskiSpacetime.SmoothPath)
    (h : SmoothPath.IsCausal StandardMinkowskiSpacetime μ) :
    SmoothPath.IsCausal StandardMinkowskiSpacetime (lorentzPath g μ) := by
  intro s hs
  have hsμ : s ∈ μ.parameterSpace := hs
  change IsTimelike StandardMinkowskiSpacetime
        (mfderivWithin (modelWithCornersSelf ℝ ℝ) StandardMinkowskiSpacetime.model
          (fun u => g.linear (μ.toFun u) + g.translation) μ.parameterSpace s (1 : ℝ)) ∨
      IsNull StandardMinkowskiSpacetime
        (mfderivWithin (modelWithCornersSelf ℝ ℝ) StandardMinkowskiSpacetime.model
          (fun u => g.linear (μ.toFun u) + g.translation) μ.parameterSpace s (1 : ℝ))
  rw [lorentzPath_mfderivWithin g μ hsμ]
  rcases h s hsμ with htl | hnull
  · exact Or.inl (isTimelike_linear g htl)
  · exact Or.inr (isNull_linear g hnull)

/-- The Lorentz pushforward of a future-oriented path is future-oriented. -/
theorem lorentzPath_isFutureOriented (g : InhomogeneousLorentzGroup)
    (μ : StandardMinkowskiSpacetime.SmoothPath)
    (h : SmoothPath.IsFutureOriented StandardMinkowskiSpacetime μ
          standardMinkowskiTimeOrientation) :
    SmoothPath.IsFutureOriented StandardMinkowskiSpacetime (lorentzPath g μ)
      standardMinkowskiTimeOrientation := by
  intro s hs
  have hsμ : s ∈ μ.parameterSpace := hs
  have hcont : Continuous
      (fun w : StandardMinkowskiSpacetime.Carrier => g.linear w) :=
    g.linear.toLinearMap.continuous_of_finiteDimensional
  change IsFuturePointing StandardMinkowskiSpacetime standardMinkowskiTimeOrientation
      (mfderivWithin (modelWithCornersSelf ℝ ℝ) StandardMinkowskiSpacetime.model
        (fun u => g.linear (μ.toFun u) + g.translation) μ.parameterSpace s (1 : ℝ))
  rw [lorentzPath_mfderivWithin g μ hsμ]
  rcases h s hsμ with ⟨htl, hfut⟩ | ⟨hnull, vs, hvs, htend⟩
  · exact Or.inl (minkowskiForm_linear_future g htl hfut)
  · exact Or.inr ⟨isNull_linear g hnull, fun n => g.linear (vs n),
      fun n => minkowskiForm_linear_future g (hvs n).1 (hvs n).2,
      (hcont.tendsto _).comp htend⟩

/-- The Lorentz pushforward sends the past endpoint `p` to `g • p`. -/
theorem lorentzPath_isPastEndpoint (g : InhomogeneousLorentzGroup)
    (μ : StandardMinkowskiSpacetime.SmoothPath)
    {p : StandardMinkowskiSpacetime.Carrier}
    (h : IsPastEndpoint StandardMinkowskiSpacetime μ p) :
    IsPastEndpoint StandardMinkowskiSpacetime (lorentzPath g μ) (g • p) := by
  obtain ⟨s, hs, hsp, hmin⟩ := h
  refine ⟨s, hs, ?_, hmin⟩
  change g.linear (μ.toFun s) + g.translation = g • p
  rw [hsp]; rfl

/-- The Lorentz pushforward sends the future endpoint `q` to `g • q`. -/
theorem lorentzPath_isFutureEndpoint (g : InhomogeneousLorentzGroup)
    (μ : StandardMinkowskiSpacetime.SmoothPath)
    {q : StandardMinkowskiSpacetime.Carrier}
    (h : IsFutureEndpoint StandardMinkowskiSpacetime μ q) :
    IsFutureEndpoint StandardMinkowskiSpacetime (lorentzPath g μ) (g • q) := by
  obtain ⟨s, hs, hsq, hmax⟩ := h
  refine ⟨s, hs, ?_, hmax⟩
  change g.linear (μ.toFun s) + g.translation = g • q
  rw [hsq]; rfl

/-! ### Lorentz invariance of causal precedence and spacelikeness -/

/-- **A Lorentz transformation maps causal trips to causal trips**, hence
preserves causal precedence: if `p ≺ q` then `g • p ≺ g • q`. -/
theorem causallyPrecedes_smul (g : InhomogeneousLorentzGroup)
    {p q : StandardMinkowskiSpacetime.Carrier}
    (h : CausallyPrecedes StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation p q) :
    CausallyPrecedes StandardMinkowskiSpacetime standardMinkowskiTimeOrientation
      (g • p) (g • q) := by
  obtain ⟨c, rep, hc, hcausal, hfut, hgeo, hpast, hfuture⟩ := h
  exact ⟨SmoothCurve.ofPath StandardMinkowskiSpacetime (lorentzPath g rep),
    lorentzPath g rep, rfl,
    lorentzPath_isCausal g rep hcausal,
    lorentzPath_isFutureOriented g rep hfut,
    trivial,
    lorentzPath_isPastEndpoint g rep hpast,
    lorentzPath_isFutureEndpoint g rep hfuture⟩

/-- **Causal precedence is Lorentz invariant.** -/
theorem causallyPrecedes_smul_iff (g : InhomogeneousLorentzGroup)
    (p q : StandardMinkowskiSpacetime.Carrier) :
    CausallyPrecedes StandardMinkowskiSpacetime standardMinkowskiTimeOrientation
        (g • p) (g • q)
      ↔ CausallyPrecedes StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation p q := by
  constructor
  · intro h
    have h2 := causallyPrecedes_smul g⁻¹ h
    rwa [inv_smul_smul, inv_smul_smul] at h2
  · exact causallyPrecedes_smul g

/-- **Spacelike-relatedness is Lorentz invariant.** -/
theorem isSpacelikeRelated_smul_iff (g : InhomogeneousLorentzGroup)
    (p₁ p₂ : StandardMinkowskiSpacetime.Carrier) :
    IsSpacelikeRelated StandardMinkowskiSpacetime standardMinkowskiTimeOrientation
        (g • p₁) (g • p₂)
      ↔ IsSpacelikeRelated StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation p₁ p₂ :=
  isSpacelikeRelated_congr StandardMinkowskiSpacetime
    standardMinkowskiTimeOrientation (fun x => g • x)
    (fun p q => causallyPrecedes_smul_iff g p q) p₁ p₂

/-- **Complete spacelikeness of two regions is Lorentz invariant.** -/
theorem isCompletelySpacelike_smul_iff (g : InhomogeneousLorentzGroup)
    (O₁ O₂ : Set StandardMinkowskiSpacetime.Carrier) :
    IsCompletelySpacelike StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation
        ((fun x => g • x) '' O₁) ((fun x => g • x) '' O₂)
      ↔ IsCompletelySpacelike StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation O₁ O₂ :=
  isCompletelySpacelike_image StandardMinkowskiSpacetime
    standardMinkowskiTimeOrientation (fun x => g • x)
    (fun p q => causallyPrecedes_smul_iff g p q) O₁ O₂

/-! ### Lorentz invariance of chronological precedence and Alexandrov-basis sets

These results feed the Haag-Kastler axioms. `LorentzCovariance`
(`AQFT/HaagKastler/LorentzCovariance.lean`) carries explicit hypotheses
`IsAlexandrovBasisSet (L • B)`, and `LocalCommutativity` is phrased over
completely-spacelike Alexandrov-basis pairs. The lemmas below show those
geometric hypotheses are stable under the Lorentz action, so they can be
discharged from the un-transformed data. -/

/-- The Lorentz pushforward of a timelike path is timelike. -/
theorem lorentzPath_isTimelike (g : InhomogeneousLorentzGroup)
    (μ : StandardMinkowskiSpacetime.SmoothPath)
    (h : SmoothPath.IsTimelike StandardMinkowskiSpacetime μ) :
    SmoothPath.IsTimelike StandardMinkowskiSpacetime (lorentzPath g μ) := by
  intro s hs
  have hsμ : s ∈ μ.parameterSpace := hs
  change IsTimelike StandardMinkowskiSpacetime
      (mfderivWithin (modelWithCornersSelf ℝ ℝ) StandardMinkowskiSpacetime.model
        (fun u => g.linear (μ.toFun u) + g.translation) μ.parameterSpace s (1 : ℝ))
  rw [lorentzPath_mfderivWithin g μ hsμ]
  exact isTimelike_linear g (h s hsμ)

/-- **A Lorentz transformation maps trips to trips**, hence preserves
chronological precedence: if `p ≪ q` then `g • p ≪ g • q`. -/
theorem chronologicallyPrecedes_smul (g : InhomogeneousLorentzGroup)
    {p q : StandardMinkowskiSpacetime.Carrier}
    (h : ChronologicallyPrecedes StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation p q) :
    ChronologicallyPrecedes StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation (g • p) (g • q) := by
  obtain ⟨c, rep, hc, htimelike, hfut, hgeo, hpast, hfuture⟩ := h
  exact ⟨SmoothCurve.ofPath StandardMinkowskiSpacetime (lorentzPath g rep),
    lorentzPath g rep, rfl,
    lorentzPath_isTimelike g rep htimelike,
    lorentzPath_isFutureOriented g rep hfut,
    trivial,
    lorentzPath_isPastEndpoint g rep hpast,
    lorentzPath_isFutureEndpoint g rep hfuture⟩

/-- **Chronological precedence is Lorentz invariant.** -/
theorem chronologicallyPrecedes_smul_iff (g : InhomogeneousLorentzGroup)
    (p q : StandardMinkowskiSpacetime.Carrier) :
    ChronologicallyPrecedes StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation (g • p) (g • q)
      ↔ ChronologicallyPrecedes StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation p q := by
  constructor
  · intro h
    have h2 := chronologicallyPrecedes_smul g⁻¹ h
    rwa [inv_smul_smul, inv_smul_smul] at h2
  · exact chronologicallyPrecedes_smul g

/-- **The Lorentz action preserves Alexandrov-basis sets.** Since `g` is a
chronological-precedence automorphism, it carries `I⁺(p) ∩ I⁻(q)` onto
`I⁺(g • p) ∩ I⁻(g • q)`. This discharges the `IsAlexandrovBasisSet (L • B)`
hypotheses in `LorentzCovariance`. -/
theorem isAlexandrovBasisSet_smul (g : InhomogeneousLorentzGroup)
    {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B) :
    IsAlexandrovBasisSet (g • B) := by
  simp only [IsAlexandrovBasisSet, Spacetime.alexandrovBasis, Set.mem_setOf_eq] at hB ⊢
  obtain ⟨p, q, rfl⟩ := hB
  refine ⟨g • p, g • q, ?_⟩
  ext y
  simp only [Set.mem_smul_set, Set.mem_inter_iff, chronologicalFuture, chronologicalPast,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨hxF, hxP⟩, rfl⟩
    exact ⟨(chronologicallyPrecedes_smul_iff g p x).mpr hxF,
      (chronologicallyPrecedes_smul_iff g x q).mpr hxP⟩
  · rintro ⟨hyF, hyP⟩
    refine ⟨g⁻¹ • y, ⟨?_, ?_⟩, by rw [smul_inv_smul]⟩
    · have h := (chronologicallyPrecedes_smul_iff g p (g⁻¹ • y)).mp
      rw [smul_inv_smul] at h
      exact h hyF
    · have h := (chronologicallyPrecedes_smul_iff g (g⁻¹ • y) q).mp
      rw [smul_inv_smul] at h
      exact h hyP

/-- **Complete spacelikeness is preserved by the Lorentz action** (in the
`g • O` set-action form used by the Haag-Kastler axioms). Together with
`isAlexandrovBasisSet_smul` this shows the entire hypothesis of
`LocalCommutativity` transports under a Lorentz transformation. -/
theorem isCompletelySpacelike_smul (g : InhomogeneousLorentzGroup)
    {O₁ O₂ : Set StandardMinkowskiSpacetime.Carrier}
    (h : IsCompletelySpacelike StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation O₁ O₂) :
    IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation (g • O₁) (g • O₂) := by
  have hF₁ : (g • O₁ : Set StandardMinkowskiSpacetime.Carrier)
      = (fun x => g • x) '' O₁ := rfl
  have hF₂ : (g • O₂ : Set StandardMinkowskiSpacetime.Carrier)
      = (fun x => g • x) '' O₂ := rfl
  rw [hF₁, hF₂]
  exact (isCompletelySpacelike_smul_iff g O₁ O₂).mpr h

end Physicslib4
