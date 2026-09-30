/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Curves
import Physicslib4.Spacetime.Causality
import Physicslib4.Spacetime.AlongPath
import Physicslib4.Spacetime.DiffeoPath
import Physicslib4.Spacetime.Isometry
import Physicslib4.Spacetime.IsometryTopology
import Physicslib4.Spacetime.LorentzianSpacetime
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

open scoped Pointwise ContDiff

namespace Physicslib4

namespace Spacetime

namespace Isometry

variable {M : Spacetime}

/-- Chain rule for the tangent vector of `g ∘ μ` along the parameter space:
the derivative of the composite is the differential of the isometry applied
to the derivative of `μ`.

Metric preservation plays no role, so this is the instance `ψ := g.toDiffeo` of
`Spacetime.mfderivWithin_comp_diffeo`
(`lmm:cross-metric-pushforward-path-tangent`). -/
theorem mfderivWithin_comp_diffeo (g : Isometry M) (μ : M.SmoothPath)
    {s : ℝ} (hs : s ∈ μ.parameterSpace) :
    mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model
        ((g.toDiffeo : M.Carrier → M.Carrier) ∘ μ.toFun) μ.parameterSpace s (1 : ℝ)
      = mfderiv M.model M.model g.toDiffeo (μ.toFun s)
          (mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model
            μ.toFun μ.parameterSpace s (1 : ℝ)) :=
  Spacetime.mfderivWithin_comp_diffeo g.toDiffeo μ hs

/--
The **pushforward of a smooth path** `μ` under an isometry `g`: the composite
`g ∘ μ` on the same parameter space.

None of the data of the pushforward path depends on the metric, so this is by
definition the instance `ψ := g.toDiffeo` of `Spacetime.pushforwardPath`
(`lmm:cross-metric-pushforward-path`) rather than a second copy of the same
construction; in particular the accessors below remain `rfl`.
-/
noncomputable def pushforwardPath (g : Isometry M) (μ : M.SmoothPath) :
    M.SmoothPath :=
  Spacetime.pushforwardPath g.toDiffeo μ

@[simp] theorem pushforwardPath_parameterSpace (g : Isometry M) (μ : M.SmoothPath) :
    (g.pushforwardPath μ).parameterSpace = μ.parameterSpace := rfl

@[simp] theorem pushforwardPath_toFun (g : Isometry M) (μ : M.SmoothPath) :
    (g.pushforwardPath μ).toFun = (g.toDiffeo : M.Carrier → M.Carrier) ∘ μ.toFun := rfl

/-- The tangent vector of the pushforward path is the differential of the
isometry applied to the tangent vector of `μ`. -/
theorem pushforwardPath_tangent (g : Isometry M) (μ : M.SmoothPath)
    {s : ℝ} (hs : s ∈ μ.parameterSpace) :
    (g.pushforwardPath μ).tangent s
      = mfderiv M.model M.model g.toDiffeo (μ.toFun s) (μ.tangent s) :=
  Spacetime.pushforwardPath_tangent g.toDiffeo μ hs

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
    {p : M.Carrier} (h : IsPastEndpoint M μ.toPath p) :
    IsPastEndpoint M (g.pushforwardPath μ).toPath (g.toDiffeo p) :=
  Spacetime.pushforwardPath_isPastEndpoint g.toDiffeo μ h

/-- A future endpoint of `μ` is carried by `g` to a future endpoint of the
pushforward path. -/
theorem pushforwardPath_isFutureEndpoint (g : Isometry M) (μ : M.SmoothPath)
    {p : M.Carrier} (h : IsFutureEndpoint M μ.toPath p) :
    IsFutureEndpoint M (g.pushforwardPath μ).toPath (g.toDiffeo p) :=
  Spacetime.pushforwardPath_isFutureEndpoint g.toDiffeo μ h

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
      rw [show ((1 : Isometry M).toDiffeo) = Diffeomorph.refl M.model M.Carrier ∞ from rfl,
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

/-- The **future-orientation-preserving isometries**: those `g` for which both
`g` and `g⁻¹` preserve the future orientation `t`. Bundling the inverse makes
this a genuine subgroup using only the identity and composition lemmas, with no
appeal to the (C⁰) group topology. This is the group over which Axiom 5's
isometric covariance is intended to range. -/
noncomputable def futureOrientationPreserving (M : Spacetime) (t : M.TimeOrientation) :
    Subgroup (Isometry M) where
  carrier := {g | g.PreservesFutureOrientation t ∧ g⁻¹.PreservesFutureOrientation t}
  one_mem' := by
    refine ⟨preservesFutureOrientation_one t, ?_⟩
    rw [inv_one]; exact preservesFutureOrientation_one t
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨preservesFutureOrientation_mul ha hb, ?_⟩
    rw [mul_inv_rev]; exact preservesFutureOrientation_mul hb' ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

@[simp] theorem mem_futureOrientationPreserving {g : Isometry M}
    {t : M.TimeOrientation} :
    g ∈ futureOrientationPreserving M t ↔
      g.PreservesFutureOrientation t ∧ g⁻¹.PreservesFutureOrientation t :=
  Iff.rfl

/-- The **oriented identity component**: the identity-component isometries that
also preserve the future orientation. This folds orientation-preservation into
the identity-component group of Axiom 5, sidestepping the (unprovable with the
current C⁰ topology) statement that every identity-component isometry preserves
orientation. -/
noncomputable def orientedIdentityComponent (M : Spacetime) (t : M.TimeOrientation) :
    Subgroup (Isometry M) :=
  Isometry.identityComponent M ⊓ futureOrientationPreserving M t

/-- The Axiom-5 isometry subgroups act **continuously** on spacetime points: both
the identity component and the oriented identity component inherit
`ContinuousSMul … M.Carrier` automatically from the full isometry group's
`ContinuousSMul` (`IsometryTopology`) via the subgroup action. Recorded here as a
confirmation, since these are the concrete `M.Isom` supplied to the curved
Haag-Kastler bridge. -/
example (M : Spacetime) (t : M.TimeOrientation) : True := by
  have _ : ContinuousSMul ↥(identityComponent M) M.Carrier := inferInstance
  have _ : ContinuousSMul ↥(orientedIdentityComponent M t) M.Carrier := inferInstance
  trivial

/-- Under future-orientation preservation, the pushforward of a future-oriented
path is future-oriented. -/
theorem pushforwardPath_isFutureOriented (g : Isometry M) (μ : M.SmoothPath)
    (t : M.TimeOrientation) (hg : g.PreservesFutureOrientation t)
    (h : SmoothPath.IsFutureOriented M μ t) :
    SmoothPath.IsFutureOriented M (g.pushforwardPath μ) t := by
  intro s hs
  simp only [pushforwardPath_tangent g μ hs]
  exact hg (μ.toFun s) _ (h s hs)

section Geodesic

open Bundle VectorField Filter
open scoped Manifold Topology

/-- The differential of an isometry `g` undoes the pullback of a vector field along `g`. -/
theorem mfderiv_mpullback (g : Isometry M) (V : Π x : M.Carrier, TangentSpace M.model x)
    (x : M.Carrier) :
    mfderiv M.model M.model g.toDiffeo x (mpullback M.model M.model g.toDiffeo V x)
      = V (g.toDiffeo x) := by
  rw [mpullback_apply, (g.toDiffeo.isInvertible_mfderiv (x := x) (by simp)).self_apply_inverse]

/-- The metric pairing of pullbacks along an isometry is the pullback of the pairing. -/
theorem val_mpullback (g : Isometry M) (V W : Π x : M.Carrier, TangentSpace M.model x)
    (x : M.Carrier) :
    M.toPseudoRiemannianMetric.val x (mpullback M.model M.model g.toDiffeo V x)
        (mpullback M.model M.model g.toDiffeo W x)
      = M.toPseudoRiemannianMetric.val (g.toDiffeo x) (V (g.toDiffeo x)) (W (g.toDiffeo x)) := by
  rw [← mfderiv_mpullback g V x, ← mfderiv_mpullback g W x]
  exact (g.preserves x _ _).symm

/-- Chain rule for the metric pairing of pulled-back vector fields along an isometry. -/
theorem mfderiv_val_mpullback (g : Isometry M) {A B C : Π x : M.Carrier, TangentSpace M.model x}
    {x : M.Carrier}
    (hB : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% B) (g.toDiffeo x))
    (hC : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% C) (g.toDiffeo x)) :
    (show ℝ from mfderiv M.model 𝓘(ℝ, ℝ) (fun y ↦ M.toPseudoRiemannianMetric.val y
        (mpullback M.model M.model g.toDiffeo B y) (mpullback M.model M.model g.toDiffeo C y)) x
        (mpullback M.model M.model g.toDiffeo A x))
      = (show ℝ from mfderiv M.model 𝓘(ℝ, ℝ)
          (fun z ↦ M.toPseudoRiemannianMetric.val z (B z) (C z)) (g.toDiffeo x)
          (A (g.toDiffeo x))) := by
  have hfun : (fun y ↦ M.toPseudoRiemannianMetric.val y
      (mpullback M.model M.model g.toDiffeo B y) (mpullback M.model M.model g.toDiffeo C y))
      = (fun z ↦ M.toPseudoRiemannianMetric.val z (B z) (C z)) ∘ g.toDiffeo :=
    funext fun y ↦ val_mpullback g B C y
  rw [hfun]
  exact (congrArg (fun L ↦ L (mpullback M.model M.model g.toDiffeo A x))
    (mfderiv_comp x (M.toPseudoRiemannianMetric.mdifferentiableAt_val_apply hB hC)
      (g.toDiffeo.mdifferentiable (by simp) x))).trans
    (by rw [ContinuousLinearMap.comp_apply, mfderiv_mpullback])

/-- Naturality of the Lie bracket under an isometry, paired with the metric. -/
theorem val_mlieBracket_mpullback (g : Isometry M)
    {A B C : Π x : M.Carrier, TangentSpace M.model x} {x : M.Carrier}
    (hA : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% A) (g.toDiffeo x))
    (hC : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% C) (g.toDiffeo x)) :
    M.toPseudoRiemannianMetric.val x (mpullback M.model M.model g.toDiffeo B x)
        (mlieBracket M.model (mpullback M.model M.model g.toDiffeo A)
          (mpullback M.model M.model g.toDiffeo C) x)
      = M.toPseudoRiemannianMetric.val (g.toDiffeo x) (B (g.toDiffeo x))
          (mlieBracket M.model A C (g.toDiffeo x)) := by
  have : IsManifold M.model (minSmoothness ℝ 2) M.Carrier := IsManifold.of_le (n := ∞) (by simp)
  rw [← mpullback_mlieBracket hA hC (g.toDiffeo.contMDiff x) (by simp)]
  exact val_mpullback g B (mlieBracket M.model A C) x

/-- **An isometry preserves the Levi-Civita connection**: `dg(∇_{g^*A} g^*B) = ∇_A B ∘ g`.

Blueprint reference: `lmm:isometry-preserves-levi-civita`. -/
theorem mfderiv_leviCivita_mpullback (g : Isometry M)
    {A B : Π x : M.Carrier, TangentSpace M.model x} {x : M.Carrier}
    (hA : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% A) (g.toDiffeo x))
    (hB : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% B) (g.toDiffeo x)) :
    mfderiv M.model M.model g.toDiffeo x
        (M.toPseudoRiemannianMetric.leviCivita (mpullback M.model M.model g.toDiffeo B) x
          (mpullback M.model M.model g.toDiffeo A x))
      = M.toPseudoRiemannianMetric.leviCivita B (g.toDiffeo x) (A (g.toDiffeo x)) := by
  set L := M.toPseudoRiemannianMetric
  have hpb : ∀ {V : Π x : M.Carrier, TangentSpace M.model x},
      MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% V) (g.toDiffeo x) →
      MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel))
        (T% (mpullback M.model M.model g.toDiffeo V)) x := fun hV ↦
    hV.mpullback_vectorField (g.toDiffeo.contMDiff x)
      (g.toDiffeo.isInvertible_mfderiv (by simp)) (by simp)
  apply L.eq_of_forall_val_apply_eq
  intro C hC
  have hL := L.isLeviCivitaFor_leviCivita
  have h1 := hL.koszul (hpb hA) (hpb hB) (hpb hC)
  have h2 := hL.koszul hA hB hC
  rw [mfderiv_val_mpullback g hB hC, mfderiv_val_mpullback g hC hA,
    mfderiv_val_mpullback g hA hB, val_mlieBracket_mpullback g hA hC,
    val_mlieBracket_mpullback g hB hA, val_mlieBracket_mpullback g hC hB] at h1
  have e : L.val (g.toDiffeo x) (mfderiv M.model M.model g.toDiffeo x
      (L.leviCivita (mpullback M.model M.model g.toDiffeo B) x
        (mpullback M.model M.model g.toDiffeo A x))) (C (g.toDiffeo x))
      = L.val x (L.leviCivita (mpullback M.model M.model g.toDiffeo B) x
        (mpullback M.model M.model g.toDiffeo A x)) (mpullback M.model M.model g.toDiffeo C x) := by
    rw [← mfderiv_mpullback g C x]
    exact g.preserves x _ _
  rw [e]
  linarith

/-- **Isometries map geodesics to geodesics.** An isometry `φ` preserves the Levi-Civita
connection (`lmm:isometry-preserves-levi-civita`), so it carries a vector field extending the
velocity of `μ` to one extending the velocity of `φ ∘ μ`, and the geodesic condition transfers.

Blueprint reference: `lmm:isometry-preserves-geodesics`. -/
theorem pushforwardPath_isGeodesic (g : Isometry M) (μ : M.SmoothPath)
    (h : IsGeodesic M μ) : IsGeodesic M (g.pushforwardPath μ) := by
  intro s hs X hX hXt
  have hinv (y : M.Carrier) : (mfderiv M.model M.model g.toDiffeo y).IsInvertible :=
    g.toDiffeo.isInvertible_mfderiv (by simp)
  have hY : ContMDiff M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) ∞
      (T% (mpullback M.model M.model g.toDiffeo X)) :=
    hX.mpullback_vectorField g.toDiffeo.contMDiff hinv (by simp)
  have hYt : ∀ᶠ t in 𝓝 s, mpullback M.model M.model g.toDiffeo X (μ.toFun t) = μ.tangent t := by
    filter_upwards [hXt, mem_interior_iff_mem_nhds.mp hs] with t ht htP
    rw [mpullback_apply]
    change X (g.toDiffeo (μ.toFun t)) = _ at ht
    rw [ht, pushforwardPath_tangent g μ htP, (hinv _).inverse_apply_self]
  have hXd : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel))
      (T% X) (g.toDiffeo (μ.toFun s)) :=
    (hX _).mdifferentiableAt (by simp)
  change M.toPseudoRiemannianMetric.leviCivita X (g.toDiffeo (μ.toFun s))
    (X (g.toDiffeo (μ.toFun s))) = 0
  rw [← mfderiv_leviCivita_mpullback g hXd hXd, h s hs _ hY hYt, map_zero]

end Geodesic

/-- Under future-orientation preservation, an isometry carries a single
trip segment forward. -/
theorem segmentPrecedes_pushforward (g : Isometry M) (t : M.TimeOrientation)
    (hg : g.PreservesFutureOrientation t) {p q : M.Carrier}
    (h : SegmentPrecedes M t p q) :
    SegmentPrecedes M t (g.toDiffeo p) (g.toDiffeo q) := by
  obtain ⟨c, rep, hc, htl, hfo, hgeo, hpe, hfe⟩ := h
  exact ⟨SmoothCurve.ofPath M (g.pushforwardPath rep), g.pushforwardPath rep, rfl,
    g.pushforwardPath_isTimelike rep htl,
    g.pushforwardPath_isFutureOriented rep t hg hfo,
    g.pushforwardPath_isGeodesic rep hgeo,
    g.pushforwardPath_isPastEndpoint rep hpe,
    g.pushforwardPath_isFutureEndpoint rep hfe⟩

/-- Under future-orientation preservation, an isometry carries chronological
precedence forward: `p ≪ q` implies `g p ≪ g q`. A trip is a finite chain of
trip segments, so this lifts `segmentPrecedes_pushforward` along the transitive
closure (`Relation.TransGen.lift`). -/
theorem chronologicallyPrecedes_pushforward (g : Isometry M) (t : M.TimeOrientation)
    (hg : g.PreservesFutureOrientation t) {p q : M.Carrier}
    (h : ChronologicallyPrecedes M t p q) :
    ChronologicallyPrecedes M t (g.toDiffeo p) (g.toDiffeo q) := by
  -- `ChronologicallyPrecedes` is `Relation.TransGen` of `SegmentPrecedes`.
  -- `TransGen.lift` lifts a relation `r ≤ p ∘ (f, f)` to `TransGen r ≤ TransGen p ∘ (f, f)`.
  exact Relation.TransGen.lift (f := g.toDiffeo)
    (r := Spacetime.SegmentPrecedes M t) (p := Spacetime.SegmentPrecedes M t)
    (fun a b hs => segmentPrecedes_pushforward g t hg hs) _ _ h

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

/-- **Unconditional basis-set preservation** for a future-orientation-preserving
isometry: it carries Alexandrov-basis sets to Alexandrov-basis sets. -/
theorem alexandrovBasis_image_of_mem (g : Isometry M) (t : M.TimeOrientation)
    (hg : g ∈ futureOrientationPreserving M t) {B : Set M.Carrier}
    (hB : B ∈ alexandrovBasis M t) : g.toDiffeo '' B ∈ alexandrovBasis M t :=
  alexandrovBasis_image g t (mem_futureOrientationPreserving.mp hg).1
    (mem_futureOrientationPreserving.mp hg).2 hB

/-- **Basis-set preservation for the oriented identity component.** Every
isometry in the oriented identity component carries Alexandrov-basis sets to
Alexandrov-basis sets - the geometric input behind Axiom 5's action
`𝔘(𝐁) → 𝔘(φ(𝐁))`, now unconditional. -/
theorem alexandrovBasis_image_of_mem_orientedIdentityComponent (g : Isometry M)
    (t : M.TimeOrientation) (hg : g ∈ orientedIdentityComponent M t)
    {B : Set M.Carrier} (hB : B ∈ alexandrovBasis M t) :
    g.toDiffeo '' B ∈ alexandrovBasis M t :=
  alexandrovBasis_image_of_mem g t (Subgroup.mem_inf.mp hg).2 hB

/-- The pointwise action of an isometry on a set is the image under its
underlying map: `g • B = g(B)`. -/
theorem smul_set_eq_image (g : Isometry M) (B : Set M.Carrier) :
    g • B = g.toDiffeo '' B := by
  rw [← Set.image_smul]
  rfl

/-- Basis-set preservation in pointwise-action form: a future-orientation-
preserving isometry sends Alexandrov-basis sets to basis sets, with the action
written as `g • B`. -/
theorem alexandrovBasis_smul_of_mem (g : Isometry M) (t : M.TimeOrientation)
    (hg : g ∈ futureOrientationPreserving M t) {B : Set M.Carrier}
    (hB : B ∈ alexandrovBasis M t) : g • B ∈ alexandrovBasis M t := by
  rw [smul_set_eq_image]
  exact alexandrovBasis_image_of_mem g t hg hB

end Isometry

namespace LorentzianSpacetime

variable (L : LorentzianSpacetime)

/-- **Basis-set preservation on a Lorentzian spacetime (image form).** An
isometry of `L.toSpacetime` in the oriented identity component carries
`IsBasisSet` sets to `IsBasisSet` sets. -/
theorem isBasisSet_image (g : Isometry L.toSpacetime)
    (hg : g ∈ Isometry.orientedIdentityComponent L.toSpacetime L.timeOrientation)
    {B : Set L.Carrier} (hB : L.IsBasisSet B) :
    L.IsBasisSet (g.toDiffeo '' B) :=
  Isometry.alexandrovBasis_image_of_mem_orientedIdentityComponent g
    L.timeOrientation hg hB

/-- **Basis-set preservation on a Lorentzian spacetime (pointwise-action form).**
The same statement written with the pointwise action `g • B`, as used by the
abstract Axiom 5 interface. -/
theorem isBasisSet_smul (g : Isometry L.toSpacetime)
    (hg : g ∈ Isometry.orientedIdentityComponent L.toSpacetime L.timeOrientation)
    {B : Set L.Carrier} (hB : L.IsBasisSet B) :
    L.IsBasisSet (g • B) := by
  rw [Isometry.smul_set_eq_image]
  exact L.isBasisSet_image g hg hB

end LorentzianSpacetime

end Spacetime

end Physicslib4
