/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Curves
import Physicslib4.Spacetime.Causality
import Physicslib4.Spacetime.Isometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Isometries and the causal structure of curves

This file begins the basis-set-preservation chain for Axiom 5
(`def:isometric-covariance-in-curved-spacetime`): an isometry should carry
trips to trips, hence chronological precedence forward, hence chronological
futures forward.

The first step is the **pushforward of a smooth path** `g ∘ μ` under an
isometry `g`, together with the chain-rule description of its tangent vector.

## Main definitions

* `Physicslib4.Spacetime.Isometry.pushforwardPath`.
-/

namespace Physicslib4

namespace Spacetime

namespace Isometry

variable {M : Spacetime}

/-- Chain rule for the tangent vector of `g ∘ μ` along the parameter space:
the derivative of the composite is the differential of the isometry applied
to the derivative of `μ`. -/
theorem mfderivWithin_comp_diffeo (g : Isometry M) (μ : M.SmoothPath)
    {s : ℝ} (hs : s ∈ μ.parameterSpace) :
    mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model
        ((g.toDiffeo : M.Carrier → M.Carrier) ∘ μ.toFun) μ.parameterSpace s (1 : ℝ)
      = mfderiv M.model M.model g.toDiffeo (μ.toFun s)
          (mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model
            μ.toFun μ.parameterSpace s (1 : ℝ)) := by
  have huniq : UniqueMDiffWithinAt (modelWithCornersSelf ℝ ℝ) μ.parameterSpace s :=
    (Path.uniqueDiffOn_parameterSpace M μ.toPath s hs).uniqueMDiffWithinAt
  have hf : MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ) M.model
      μ.toFun μ.parameterSpace s :=
    (μ.smoothOn s hs).mdifferentiableWithinAt (by simp)
  have hg : MDifferentiableWithinAt M.model M.model
      (g.toDiffeo : M.Carrier → M.Carrier) Set.univ (μ.toFun s) :=
    (g.toDiffeo.mdifferentiable (by simp) (μ.toFun s)).mdifferentiableWithinAt
  have hcomp := mfderivWithin_comp s hg hf (by simp) huniq
  rw [mfderivWithin_univ] at hcomp
  rw [hcomp]
  rfl

/--
The **pushforward of a smooth path** `μ` under an isometry `g`: the composite
`g ∘ μ` on the same parameter space. Smoothness is inherited from the
composition of the smooth path with the (smooth) isometry, and the tangent
vector is non-vanishing because the differential of an isometry is a linear
isomorphism.
-/
noncomputable def pushforwardPath (g : Isometry M) (μ : M.SmoothPath) :
    M.SmoothPath where
  parameterSpace := μ.parameterSpace
  isClosed := μ.isClosed
  isConnected := μ.isConnected
  nontrivial := μ.nontrivial
  toFun := (g.toDiffeo : M.Carrier → M.Carrier) ∘ μ.toFun
  continuousOn := g.toDiffeo.continuous.comp_continuousOn μ.continuousOn
  smoothOn := g.toDiffeo.contMDiff.comp_contMDiffOn μ.smoothOn
  nonvanishing := by
    intro s hs
    rw [mfderivWithin_comp_diffeo g μ hs,
      ← g.toDiffeo.mfderivToContinuousLinearEquiv_coe (by simp),
      ContinuousLinearEquiv.coe_coe]
    exact fun h => μ.nonvanishing s hs
      ((g.toDiffeo.mfderivToContinuousLinearEquiv (by simp) (μ.toFun s)).injective
        (h.trans (map_zero _).symm))

@[simp] theorem pushforwardPath_parameterSpace (g : Isometry M) (μ : M.SmoothPath) :
    (g.pushforwardPath μ).parameterSpace = μ.parameterSpace := rfl

@[simp] theorem pushforwardPath_toFun (g : Isometry M) (μ : M.SmoothPath) :
    (g.pushforwardPath μ).toFun = (g.toDiffeo : M.Carrier → M.Carrier) ∘ μ.toFun := rfl

/-- The tangent vector of the pushforward path is the differential of the
isometry applied to the tangent vector of `μ`. -/
theorem pushforwardPath_tangent (g : Isometry M) (μ : M.SmoothPath)
    {s : ℝ} (hs : s ∈ μ.parameterSpace) :
    mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model (g.pushforwardPath μ).toFun
        (g.pushforwardPath μ).parameterSpace s (1 : ℝ)
      = mfderiv M.model M.model g.toDiffeo (μ.toFun s)
          (mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model
            μ.toFun μ.parameterSpace s (1 : ℝ)) :=
  mfderivWithin_comp_diffeo g μ hs

/-- The pushforward of a timelike path is timelike: isometries preserve the
timelike condition along a path. -/
theorem pushforwardPath_isTimelike (g : Isometry M) (μ : M.SmoothPath)
    (h : SmoothPath.IsTimelike M μ) :
    SmoothPath.IsTimelike M (g.pushforwardPath μ) := by
  intro s hs
  simp only [pushforwardPath_tangent g μ hs]
  exact (isTimelike_mfderiv_iff g (μ.toFun s) _).mpr (h s hs)

/-- The pushforward of a causal path is causal. -/
theorem pushforwardPath_isCausal (g : Isometry M) (μ : M.SmoothPath)
    (h : SmoothPath.IsCausal M μ) :
    SmoothPath.IsCausal M (g.pushforwardPath μ) := by
  intro s hs
  simp only [pushforwardPath_tangent g μ hs]
  rcases h s hs with ht | hn
  · exact Or.inl ((isTimelike_mfderiv_iff g (μ.toFun s) _).mpr ht)
  · exact Or.inr ((isNull_mfderiv_iff g (μ.toFun s) _).mpr hn)

/-- A past endpoint of `μ` is carried by `g` to a past endpoint of the
pushforward path. -/
theorem pushforwardPath_isPastEndpoint (g : Isometry M) (μ : M.SmoothPath)
    {p : M.Carrier} (h : IsPastEndpoint M μ p) :
    IsPastEndpoint M (g.pushforwardPath μ) (g.toDiffeo p) := by
  obtain ⟨s, hs, hsp, hmin⟩ := h
  exact ⟨s, hs, by simp only [pushforwardPath_toFun, Function.comp_apply, hsp], hmin⟩

/-- A future endpoint of `μ` is carried by `g` to a future endpoint of the
pushforward path. -/
theorem pushforwardPath_isFutureEndpoint (g : Isometry M) (μ : M.SmoothPath)
    {p : M.Carrier} (h : IsFutureEndpoint M μ p) :
    IsFutureEndpoint M (g.pushforwardPath μ) (g.toDiffeo p) := by
  obtain ⟨s, hs, hsp, hmax⟩ := h
  exact ⟨s, hs, by simp only [pushforwardPath_toFun, Function.comp_apply, hsp], hmax⟩

/-! ### Preservation of future orientation, trips and chronological precedence

A general isometry preserves the metric and hence the timelike/null/spacelike
classification, but it need not preserve the chosen time orientation `t`. We
isolate the property that it preserves *future-pointing-ness* and show that,
under this hypothesis, the pushforward carries trips to trips and therefore
chronological precedence forward. The remaining step toward Axiom 5 is to show
that identity-component isometries satisfy this property (a connectedness
argument), which is recorded as future work. -/

/-- An isometry `g` *preserves the future orientation* `t` if its differential
sends future-pointing tangent vectors to future-pointing tangent vectors. -/
def PreservesFutureOrientation (g : Isometry M) (t : M.TimeOrientation) : Prop :=
  ∀ (x : M.Carrier) (v : TangentSpace M.model x),
    M.IsFuturePointing t v →
      M.IsFuturePointing t (mfderiv M.model M.model g.toDiffeo x v)

/-- The identity isometry preserves the future orientation. -/
theorem preservesFutureOrientation_one (t : M.TimeOrientation) :
    (1 : Isometry M).PreservesFutureOrientation t := by
  intro x v hv
  have h : mfderiv M.model M.model (1 : Isometry M).toDiffeo x v = v := by
    have hid : mfderiv M.model M.model (1 : Isometry M).toDiffeo x
        = ContinuousLinearMap.id ℝ (TangentSpace M.model x) := by
      rw [show ((1 : Isometry M).toDiffeo) = Diffeomorph.refl M.model M.Carrier ⊤ from rfl,
        Diffeomorph.coe_refl, mfderiv_id]
    rw [hid]; rfl
  rw [← h] at hv
  exact hv

/-- Future-orientation preservation is closed under composition. -/
theorem preservesFutureOrientation_mul {g h : Isometry M} {t : M.TimeOrientation}
    (hg : g.PreservesFutureOrientation t) (hh : h.PreservesFutureOrientation t) :
    (g * h).PreservesFutureOrientation t := by
  intro x v hv
  have hcomp := mfderiv_comp_apply (I := M.model) (I' := M.model) (I'' := M.model)
    (f := (h.toDiffeo : M.Carrier → M.Carrier))
    (g := (g.toDiffeo : M.Carrier → M.Carrier)) (x := x)
    ((g.toDiffeo.mdifferentiable (by simp)) (h.toDiffeo x))
    ((h.toDiffeo.mdifferentiable (by simp)) x) v
  rw [← Diffeomorph.coe_trans] at hcomp
  have key : M.IsFuturePointing t
      (mfderiv M.model M.model g.toDiffeo (h.toDiffeo x)
        (mfderiv M.model M.model h.toDiffeo x v)) :=
    hg (h.toDiffeo x) _ (hh x v hv)
  rw [← hcomp] at key
  exact key

/-- Under future-orientation preservation, the pushforward of a future-oriented
path is future-oriented. -/
theorem pushforwardPath_isFutureOriented (g : Isometry M) (μ : M.SmoothPath)
    (t : M.TimeOrientation) (hg : g.PreservesFutureOrientation t)
    (h : SmoothPath.IsFutureOriented M μ t) :
    SmoothPath.IsFutureOriented M (g.pushforwardPath μ) t := by
  intro s hs
  simp only [pushforwardPath_tangent g μ hs]
  exact hg (μ.toFun s) _ (h s hs)

/-- Under future-orientation preservation, an isometry carries chronological
precedence forward: `p ≪ q` implies `g p ≪ g q`. -/
theorem chronologicallyPrecedes_pushforward (g : Isometry M) (t : M.TimeOrientation)
    (hg : g.PreservesFutureOrientation t) {p q : M.Carrier}
    (h : ChronologicallyPrecedes M t p q) :
    ChronologicallyPrecedes M t (g.toDiffeo p) (g.toDiffeo q) := by
  obtain ⟨c, rep, hc, htl, hfo, hgeo, hpe, hfe⟩ := h
  exact ⟨SmoothCurve.ofPath M (g.pushforwardPath rep), g.pushforwardPath rep, rfl,
    g.pushforwardPath_isTimelike rep htl,
    g.pushforwardPath_isFutureOriented rep t hg hfo,
    trivial,
    g.pushforwardPath_isPastEndpoint rep hpe,
    g.pushforwardPath_isFutureEndpoint rep hfe⟩

/-- Under future-orientation preservation, the image of a chronological future
is contained in the chronological future of the image point. -/
theorem chronologicalFuture_image_subset (g : Isometry M) (t : M.TimeOrientation)
    (hg : g.PreservesFutureOrientation t) (p : M.Carrier) :
    g.toDiffeo '' chronologicalFuture M t p
      ⊆ chronologicalFuture M t (g.toDiffeo p) := by
  rintro _ ⟨q, hq, rfl⟩
  exact chronologicallyPrecedes_pushforward g t hg hq

/-- The underlying map of `g` cancels that of `g⁻¹`. -/
theorem toDiffeo_inv_apply (g : Isometry M) (x : M.Carrier) :
    g.toDiffeo (g⁻¹.toDiffeo x) = x := by
  have : ((g : Isometry M) • ((g⁻¹ : Isometry M) • x) : M.Carrier) = x := by
    rw [← mul_smul, mul_inv_cancel, one_smul]
  simpa only [Isometry.smul_def] using this

/-- The underlying map of `g⁻¹` cancels that of `g`. -/
theorem inv_toDiffeo_apply (g : Isometry M) (x : M.Carrier) :
    g⁻¹.toDiffeo (g.toDiffeo x) = x := by
  have : ((g⁻¹ : Isometry M) • ((g : Isometry M) • x) : M.Carrier) = x := by
    rw [← mul_smul, inv_mul_cancel, one_smul]
  simpa only [Isometry.smul_def] using this

/-- When both `g` and `g⁻¹` preserve the future orientation, the image of a
chronological future is exactly the chronological future of the image point:
`g(I⁺(p)) = I⁺(g p)`. -/
theorem chronologicalFuture_image (g : Isometry M) (t : M.TimeOrientation)
    (hg : g.PreservesFutureOrientation t) (hg' : g⁻¹.PreservesFutureOrientation t)
    (p : M.Carrier) :
    g.toDiffeo '' chronologicalFuture M t p
      = chronologicalFuture M t (g.toDiffeo p) := by
  refine Set.Subset.antisymm (chronologicalFuture_image_subset g t hg p) ?_
  intro r hr
  have hstep := chronologicallyPrecedes_pushforward g⁻¹ t hg' hr
  rw [inv_toDiffeo_apply] at hstep
  exact ⟨g⁻¹.toDiffeo r, hstep, g.toDiffeo_inv_apply r⟩

/-- Under future-orientation preservation, the image of a chronological past is
contained in the chronological past of the image point. -/
theorem chronologicalPast_image_subset (g : Isometry M) (t : M.TimeOrientation)
    (hg : g.PreservesFutureOrientation t) (p : M.Carrier) :
    g.toDiffeo '' chronologicalPast M t p
      ⊆ chronologicalPast M t (g.toDiffeo p) := by
  rintro _ ⟨q, hq, rfl⟩
  exact chronologicallyPrecedes_pushforward g t hg hq

/-- When both `g` and `g⁻¹` preserve the future orientation, the image of a
chronological past is exactly the chronological past of the image point:
`g(I⁻(p)) = I⁻(g p)`. -/
theorem chronologicalPast_image (g : Isometry M) (t : M.TimeOrientation)
    (hg : g.PreservesFutureOrientation t) (hg' : g⁻¹.PreservesFutureOrientation t)
    (p : M.Carrier) :
    g.toDiffeo '' chronologicalPast M t p
      = chronologicalPast M t (g.toDiffeo p) := by
  refine Set.Subset.antisymm (chronologicalPast_image_subset g t hg p) ?_
  intro r hr
  have hstep := chronologicallyPrecedes_pushforward g⁻¹ t hg' hr
  rw [inv_toDiffeo_apply] at hstep
  exact ⟨g⁻¹.toDiffeo r, hstep, g.toDiffeo_inv_apply r⟩

/-- **Basis-set preservation.** When both `g` and `g⁻¹` preserve the future
orientation, the isometry carries Alexandrov-basis sets to Alexandrov-basis
sets: `g(I⁺(p) ∩ I⁻(q)) = I⁺(g p) ∩ I⁻(g q)`. This is the geometric content
behind Axiom 5's action `𝔘(𝐁) → 𝔘(φ(𝐁))`. -/
theorem alexandrovBasis_image (g : Isometry M) (t : M.TimeOrientation)
    (hg : g.PreservesFutureOrientation t) (hg' : g⁻¹.PreservesFutureOrientation t)
    {B : Set M.Carrier} (hB : B ∈ alexandrovBasis M t) :
    g.toDiffeo '' B ∈ alexandrovBasis M t := by
  obtain ⟨p, q, rfl⟩ := hB
  refine ⟨g.toDiffeo p, g.toDiffeo q, ?_⟩
  have hinj : Function.Injective (g.toDiffeo : M.Carrier → M.Carrier) :=
    Function.LeftInverse.injective (g := g⁻¹.toDiffeo) (fun x => g.inv_toDiffeo_apply x)
  rw [Set.image_inter hinj, chronologicalFuture_image g t hg hg' p,
    chronologicalPast_image g t hg hg' q]

end Isometry

end Spacetime

end Physicslib4
