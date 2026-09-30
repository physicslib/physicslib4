/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Physicslib4.Spacetime.Curves
import Physicslib4.Geometry.PseudoRiemannian.LeviCivita
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Vector fields and covariant derivatives along smooth paths

Two facts make the chart-free geodesic condition (`def:geodesic`) well defined and
non-vacuous:

* `SmoothPath.covDeriv_eq_of_eventuallyEq`: `(∇_{μ'(s)} Y)(μ s)` depends only on the values of
  `Y` along `μ` near `s`;
* `SmoothPath.exists_vectorField_eq_tangent`: near an interior parameter, the velocity of a
  smooth path extends to a smooth vector field on the spacetime.

Blueprint reference: `lmm:derivative-vanishes-along-path`,
`lmm:covariant-derivative-along-curve-local`, `lmm:local-vector-field-globalises`,
`lmm:path-local-left-inverse`, `lmm:velocity-extends`.
-/

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace Physicslib4

namespace Spacetime

attribute [local instance] Spacetime.topology Spacetime.hausdorff Spacetime.chartedSpace
  Spacetime.isManifold Spacetime.tangent_findim Spacetime.boundaryless

variable {M : Spacetime}

/-- **A function vanishing along a path has zero derivative along it.** If `f` is
differentiable at `μ s` and `f ∘ μ` vanishes on the parameter space near `s`, then
`df(μ'(s)) = 0`.

Blueprint reference: `lmm:derivative-vanishes-along-path`. -/
theorem SmoothPath.mfderiv_apply_tangent_eq_zero (μ : M.SmoothPath) {s : ℝ}
    (hs : s ∈ μ.parameterSpace) {f : M.Carrier → ℝ}
    (hf : MDifferentiableAt M.model 𝓘(ℝ, ℝ) f (μ.toFun s))
    (h0 : ∀ᶠ t in 𝓝[μ.parameterSpace] s, f (μ.toFun t) = 0) :
    (show ℝ from mfderiv M.model 𝓘(ℝ, ℝ) f (μ.toFun s) (μ.tangent s)) = 0 := by
  have hμ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) M.model μ.toFun μ.parameterSpace s :=
    (μ.smoothOn s hs).mdifferentiableWithinAt (by simp)
  have hu := (Path.uniqueDiffOn_parameterSpace M μ.toPath s hs).uniqueMDiffWithinAt
  have h1 := hf.hasMFDerivAt.comp_hasMFDerivWithinAt s hμ.hasMFDerivWithinAt
  have h2 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ μ.toFun) μ.parameterSpace s 0 :=
    (hasMFDerivWithinAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (0 : ℝ) _ s).congr_of_eventuallyEq
      h0 (h0.self_of_nhdsWithin hs)
  exact congrArg (fun L => L (1 : ℝ)) (hu.eq h1 h2)

/-- A covariant derivative on the tangent bundle commutes with finite sums of sections that are
differentiable at the base point. -/
private theorem covDeriv_finsetSum
    (cov : _root_.CovariantDerivative M.model SpacetimeModel
      (TangentSpace M.model : M.Carrier → Type _))
    {ι : Type*} (S : Finset ι) (σ : ι → Π x : M.Carrier, TangentSpace M.model x) {p : M.Carrier}
    (hσ : ∀ i ∈ S,
      MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% (σ i)) p) :
    cov (fun x ↦ ∑ i ∈ S, σ i x) p = ∑ i ∈ S, cov (σ i) p := by
  classical
  induction S using Finset.induction_on with
  | empty => exact cov.isCovariantDerivativeOnUniv.zero (x := p)
  | insert a S ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
    simp only [Finset.sum_insert ha, ← ih hσ.2]
    exact cov.isCovariantDerivativeOnUniv.add hσ.1 (.sum_section hσ.2)

/-- A section vanishing along a path near `s` has vanishing covariant derivative in the direction
of the path's velocity at `s`. -/
private theorem covDeriv_apply_eq_zero_of_eventually_eq_zero
    (cov : _root_.CovariantDerivative M.model SpacetimeModel
      (TangentSpace M.model : M.Carrier → Type _))
    (μ : M.SmoothPath) {s : ℝ} (hs : s ∈ μ.parameterSpace)
    {W : Π x : M.Carrier, TangentSpace M.model x}
    (hW : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% W) (μ.toFun s))
    (h0 : ∀ᶠ t in 𝓝[μ.parameterSpace] s, W (μ.toFun t) = 0) :
    cov W (μ.toFun s) (μ.tangent s) = 0 := by
  set p := μ.toFun s
  let t := trivializationAt SpacetimeModel (TangentSpace M.model : M.Carrier → Type _) p
  have hp : p ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  let b := Module.Basis.ofVectorSpace ℝ SpacetimeModel
  let e := t.localFrame b
  let c := t.localFrameCoeff M.model b
  have he (i) : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% (e i)) p :=
    (contMDiffAt_localFrame_of_mem 1 _ b i hp).mdifferentiableAt (by simp)
  have hc (i) : MDifferentiableAt M.model 𝓘(ℝ, ℝ) (LinearMap.piApply (c i) W) p :=
    mdifferentiableAt_localFrameCoeff b hp hW i
  have hW0 : W p = 0 := h0.self_of_nhdsWithin hs
  have hterm (i) : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel))
      (T% (LinearMap.piApply (c i) W • e i)) p := (hc i).smul_section (he i)
  have hsum : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel))
      (T% (fun x ↦ ∑ i, (LinearMap.piApply (c i) W • e i) x)) p :=
    .sum_section fun i _ ↦ hterm i
  rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq hW hsum Filter.univ_mem
      (t.eventually_eq_localFrame_sum_coeff_smul b hp),
    covDeriv_finsetSum cov _ _ fun i _ ↦ hterm i, sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [cov.isCovariantDerivativeOnUniv.leibniz (he i) (hc i)]
  have hd : mfderiv M.model 𝓘(ℝ, ℝ) (LinearMap.piApply (c i) W) p (μ.tangent s) = 0 :=
    μ.mfderiv_apply_tangent_eq_zero hs (hc i)
      (h0.mono fun t ht ↦ by simp [ht])
  simp only [mvfderiv]
  rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, hd, map_zero, zero_smul, add_zero]
  simp [hW0]

/-- **The covariant derivative along a path is local.** For a covariant derivative `∇` on the
tangent bundle, `(∇_{μ'(s)} Y)(μ s)` depends only on the values of `Y` along `μ` near `s`.

Blueprint reference: `lmm:covariant-derivative-along-curve-local`. -/
theorem SmoothPath.covDeriv_eq_of_eventuallyEq
    (cov : _root_.CovariantDerivative M.model SpacetimeModel
      (TangentSpace M.model : M.Carrier → Type _))
    (μ : M.SmoothPath) {s : ℝ} (hs : s ∈ μ.parameterSpace)
    {Y Y' : Π x : M.Carrier, TangentSpace M.model x}
    (hY : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% Y) (μ.toFun s))
    (hY' : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% Y') (μ.toFun s))
    (h : ∀ᶠ t in 𝓝[μ.parameterSpace] s, Y (μ.toFun t) = Y' (μ.toFun t)) :
    cov Y (μ.toFun s) (μ.tangent s) = cov Y' (μ.toFun s) (μ.tangent s) := by
  set W : Π x : M.Carrier, TangentSpace M.model x := Y + (-1 : ℝ) • Y'
  have hW : MDifferentiableAt M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) (T% W) (μ.toFun s) :=
    mdifferentiableAt_add_section hY hY'.smul_const_section
  have hYW : Y = Y' + W := by
    funext x; simp [W]
  have h0 : ∀ᶠ t in 𝓝[μ.parameterSpace] s, W (μ.toFun t) = 0 :=
    h.mono fun t ht ↦ by simp [W, ht]
  rw [hYW, cov.isCovariantDerivativeOn.add hY' hW, add_apply,
    covDeriv_apply_eq_zero_of_eventually_eq_zero cov μ hs hW h0, add_zero]

/-- **Local vector fields globalise.** A vector field smooth on an open neighbourhood of `p`
agrees near `p` with a smooth vector field on the whole spacetime.

Blueprint reference: `lmm:local-vector-field-globalises`. -/
theorem exists_contMDiff_vectorField_eventuallyEq {p : M.Carrier} {U : Set M.Carrier}
    (hU : IsOpen U) (hp : p ∈ U) {X₀ : Π x : M.Carrier, TangentSpace M.model x}
    (hX₀ : ContMDiffOn M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) ∞ (T% X₀) U) :
    ∃ X : Π x : M.Carrier, TangentSpace M.model x,
      ContMDiff M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) ∞ (T% X) ∧ X =ᶠ[𝓝 p] X₀ := by
  obtain ⟨f, -, hf⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := M.model) p).mem_iff.1 (hU.mem_nhds hp)
  refine ⟨(f : M.Carrier → ℝ) • X₀,
    ContMDiffOn.smul_section_of_tsupport f.contMDiff.contMDiffOn hU hf hX₀, ?_⟩
  filter_upwards [f.eventuallyEq_one] with x hx
  rw [Pi.smul_apply', hx, Pi.one_apply, one_smul]

/-- One-dimensional inverse function theorem with smooth inverse near the image point: a real
function smooth near `s` with non-zero derivative at `s` has a left inverse near `s` that is
smooth near `h s`. -/
private theorem exists_smooth_localLeftInverse_real {h : ℝ → ℝ} {s : ℝ}
    (hh : ∀ᶠ t in 𝓝 s, ContDiffAt ℝ ∞ h t) (hd : deriv h s ≠ 0) :
    ∃ σ : ℝ → ℝ, (∀ᶠ a in 𝓝 (h s), ContDiffAt ℝ ∞ σ a) ∧ ∀ᶠ t in 𝓝 s, σ (h t) = t := by
  obtain ⟨V, hVh, hVo, hsV⟩ := eventually_nhds_iff.mp hh
  have hVd : ContinuousOn (deriv h) V :=
    ContDiffOn.continuousOn_deriv_of_isOpen (fun t ht ↦ (hVh t ht).contDiffWithinAt) hVo
      (by simp)
  have hW : ∀ᶠ t in 𝓝 s, t ∈ V ∧ deriv h t ≠ 0 :=
    Filter.Eventually.and (hVo.mem_nhds hsV)
      ((hVd.continuousAt (hVo.mem_nhds hsV)).eventually_ne hd)
  have hdiff : ∀ t ∈ V, HasDerivAt h (deriv h t) t :=
    fun t ht ↦ ((hVh t ht).differentiableAt (by simp)).hasDerivAt
  have hs' := (hdiff s hsV).hasFDerivAt_equiv hd
  set F := (hVh s hsV).toOpenPartialHomeomorph h hs' (by simp)
  have hsF : s ∈ F.source := (hVh s hsV).mem_toOpenPartialHomeomorph_source hs' (by simp)
  have hF : ∀ t, F t = h t := fun _ ↦ rfl
  have hhs : h s ∈ F.target := (hVh s hsV).image_mem_toOpenPartialHomeomorph_target hs' (by simp)
  have hsymm : ∀ᶠ a in 𝓝 (h s), F.symm a ∈ V ∧ deriv h (F.symm a) ≠ 0 := by
    have := F.continuousAt_symm hhs
    rw [ContinuousAt, ← hF s, F.left_inv hsF] at this
    exact this.eventually hW
  refine ⟨F.symm, ?_, ?_⟩
  · filter_upwards [hsymm, F.open_target.mem_nhds hhs] with a ha haT
    exact F.contDiffAt_symm_deriv ha.2 haT (hdiff _ ha.1) (hVh _ ha.1)
  · filter_upwards [F.open_source.mem_nhds hsF] with t ht
    exact F.left_inv ht

/-- In the chart at `μ s`, a smooth path is smooth near an interior parameter `s`. -/
private theorem SmoothPath.eventually_contDiffAt_chart (μ : M.SmoothPath) {s : ℝ}
    (hs : s ∈ interior μ.parameterSpace) :
    ∀ᶠ t in 𝓝 s, ContDiffAt ℝ ∞ (extChartAt M.model (μ.toFun s) ∘ μ.toFun) t := by
  have hint : ∀ᶠ t in 𝓝 s, t ∈ interior μ.parameterSpace := isOpen_interior.mem_nhds hs
  have hcont : ContinuousAt μ.toFun s :=
    μ.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hs)
  have hsrc : ∀ᶠ t in 𝓝 s, μ.toFun t ∈ (chartAt SpacetimeModel (μ.toFun s)).source :=
    hcont.preimage_mem_nhds ((chartAt SpacetimeModel (μ.toFun s)).open_source.mem_nhds
      (mem_chart_source _ _))
  filter_upwards [hint, hsrc] with t ht htc
  have hμt : ContMDiffAt 𝓘(ℝ, ℝ) M.model ∞ μ.toFun t :=
    μ.smoothOn.contMDiffAt (mem_interior_iff_mem_nhds.mp ht)
  exact contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' htc).comp t hμt)

/-- In the chart at `μ s`, the velocity of a smooth path at an interior parameter `s` is
non-zero. -/
private theorem SmoothPath.deriv_chart_ne_zero (μ : M.SmoothPath) {s : ℝ}
    (hs : s ∈ interior μ.parameterSpace) :
    deriv (extChartAt M.model (μ.toFun s) ∘ μ.toFun) s ≠ 0 := by
  have hsn : μ.parameterSpace ∈ 𝓝 s := mem_interior_iff_mem_nhds.mp hs
  have hμ : MDifferentiableAt 𝓘(ℝ, ℝ) M.model μ.toFun s :=
    (μ.smoothOn.contMDiffAt hsn).mdifferentiableAt (by simp)
  have h := μ.tangent_ne_zero (interior_subset hs)
  rw [SmoothPath.tangent_def, mfderivWithin_of_mem_nhds hsn, hμ.mfderiv] at h
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, modelWithCornersSelf_coe,
    Set.range_id, fderivWithin_univ, PartialEquiv.refl_coe, PartialEquiv.refl_symm,
    Function.comp_id, id_eq] at h
  exact h

/-- **Local left inverse of a smooth path.** Near an interior parameter `s`, there is a
function `τ`, smooth near `μ s`, with `τ (μ t) = t` for `t` near `s`.

Blueprint reference: `lmm:path-local-left-inverse`. -/
theorem SmoothPath.exists_localLeftInverse (μ : M.SmoothPath) {s : ℝ}
    (hs : s ∈ interior μ.parameterSpace) :
    ∃ τ : M.Carrier → ℝ, (∀ᶠ y in 𝓝 (μ.toFun s), ContMDiffAt M.model 𝓘(ℝ, ℝ) ∞ τ y) ∧
      ∀ᶠ t in 𝓝 s, τ (μ.toFun t) = t := by
  set φ := extChartAt M.model (μ.toFun s)
  have hcd := μ.eventually_contDiffAt_chart hs
  have hv := μ.deriv_chart_ne_zero hs
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : SpacetimeModel →L[ℝ] ℝ, ℓ (deriv (φ ∘ μ.toFun) s) = 1 :=
    ⟨(‖deriv (φ ∘ μ.toFun) s‖ ^ 2)⁻¹ • innerSL ℝ (deriv (φ ∘ μ.toFun) s), by
      simp only [smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
        smul_eq_mul]
      exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))⟩
  have hcs : DifferentiableAt ℝ (φ ∘ μ.toFun) s := (hcd.self_of_nhds).differentiableAt (by simp)
  have hd : deriv (ℓ ∘ φ ∘ μ.toFun) s ≠ 0 := by
    rw [(ℓ.hasFDerivAt.comp_hasDerivAt s hcs.hasDerivAt).deriv]
    simp [hℓ]
  obtain ⟨σ, hσ, hστ⟩ := exists_smooth_localLeftInverse_real
    (hcd.mono fun t ht ↦ ℓ.contDiff.contDiffAt.comp t ht) hd
  refine ⟨σ ∘ ℓ ∘ φ, ?_, ?_⟩
  · have hℓφ : ContinuousAt (ℓ ∘ φ) (μ.toFun s) :=
      ℓ.continuous.continuousAt.comp (continuousAt_extChartAt _)
    have h1 : ∀ᶠ y in 𝓝 (μ.toFun s), ContDiffAt ℝ ∞ σ (ℓ (φ y)) := hℓφ.eventually hσ
    have h2 : ∀ᶠ y in 𝓝 (μ.toFun s), y ∈ (chartAt SpacetimeModel (μ.toFun s)).source :=
      (chartAt SpacetimeModel (μ.toFun s)).open_source.mem_nhds (mem_chart_source _ _)
    filter_upwards [h1, h2] with y hy1 hy2
    exact hy1.contMDiffAt.comp y
      (ℓ.contDiff.contMDiff.contMDiffAt.comp y (contMDiffAt_extChartAt' hy2))
  · exact hστ

/-- The chart expression `φ ∘ μ` of a path in the chart at `p` has derivative the tangent
vector `μ'(t)` written in that chart. -/
private theorem SmoothPath.hasDerivAt_extChartAt_comp (μ : M.SmoothPath) {t : ℝ}
    {p : M.Carrier} (ht : μ.parameterSpace ∈ 𝓝 t)
    (hsrc : μ.toFun t ∈ (chartAt SpacetimeModel p).source) :
    HasDerivAt (extChartAt M.model p ∘ μ.toFun)
      (tangentCoordChange M.model (μ.toFun t) p (μ.toFun t) (μ.tangent t)) t := by
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) M.model μ.toFun t :=
    (μ.smoothOn.contMDiffAt ht).mdifferentiableAt (by simp)
  have htan : μ.tangent t = mfderiv 𝓘(ℝ, ℝ) M.model μ.toFun t (1 : ℝ) := by
    rw [SmoothPath.tangent_def, mfderivWithin_of_mem_nhds ht]
  have h := hasMFDerivAt_iff_hasFDerivAt.mp (HasMFDerivAt.comp t
    (hasMFDerivAt_extChartAt (I := M.model) hsrc) hd.hasMFDerivAt)
  refine hasDerivAt_iff_hasFDerivAt.mpr (h.congr_fderiv ?_)
  refine ContinuousLinearMap.ext_ring ?_
  exact (DFunLike.congr_fun (mfderiv_chartAt_eq_tangentCoordChange hsrc) _).trans
    ((congrArg _ htan.symm).trans (one_smul ℝ _).symm)

/-- **The velocity of a smooth path extends to a vector field.** Near an interior parameter
`s`, there is a smooth vector field `X` on the spacetime with `X (μ t) = μ'(t)` for `t` near
`s`.

Blueprint reference: `lmm:velocity-extends`. -/
theorem SmoothPath.exists_vectorField_eq_tangent (μ : M.SmoothPath) {s : ℝ}
    (hs : s ∈ interior μ.parameterSpace) :
    ∃ X : Π x : M.Carrier, TangentSpace M.model x,
      ContMDiff M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) ∞ (T% X) ∧
        ∀ᶠ t in 𝓝 s, X (μ.toFun t) = μ.tangent t := by
  obtain ⟨τ, hτ, hτμ⟩ := μ.exists_localLeftInverse hs
  set p := μ.toFun s
  have hPS : μ.parameterSpace ∈ 𝓝 s := mem_interior_iff_mem_nhds.mp hs
  have hμc : ContinuousAt μ.toFun s := (μ.smoothOn.contMDiffAt hPS).continuousAt
  set c : ℝ → SpacetimeModel := extChartAt M.model p ∘ μ.toFun
  set J := interior μ.parameterSpace ∩ μ.toFun ⁻¹' (chartAt SpacetimeModel p).source
  have hJ : IsOpen J := (μ.continuousOn.mono interior_subset).isOpen_inter_preimage
    isOpen_interior (chartAt SpacetimeModel p).open_source
  have hsJ : s ∈ J := ⟨hs, mem_chart_source _ _⟩
  have hc : ContDiffOn ℝ ∞ c J := by
    refine contMDiffOn_iff_contDiffOn.mp ?_
    exact (contMDiffOn_extChartAt (I := M.model)).comp (μ.smoothOn.mono
      (interior_subset.trans' Set.inter_subset_left)) (fun t ht ↦ ht.2)
  have hc' : ContDiffOn ℝ ∞ (deriv c) J :=
    ContDiffOn.clm_apply (ContDiffOn.fderiv_of_isOpen hc hJ (by simp)) contDiffOn_const
  have hderiv : ∀ t ∈ J, deriv c t =
      tangentCoordChange M.model (μ.toFun t) p (μ.toFun t) (μ.tangent t) := fun t ht ↦
    (μ.hasDerivAt_extChartAt_comp (interior_mem_nhds.mp (isOpen_interior.mem_nhds ht.1))
      ht.2).deriv
  have hτp : τ p = s := hτμ.self_of_nhds
  have hU : {y | y ∈ (chartAt SpacetimeModel p).source ∧
      ContMDiffAt M.model 𝓘(ℝ, ℝ) ∞ τ y ∧ τ y ∈ J} ∈ 𝓝 p := by
    refine Filter.inter_mem (chart_source_mem_nhds _ _) (Filter.inter_mem hτ ?_)
    exact hτ.self_of_nhds.continuousAt.preimage_mem_nhds (hτp ▸ hJ.mem_nhds hsJ)
  obtain ⟨U, hUsub, hUo, hpU⟩ := mem_nhds_iff.mp hU
  let X₀ : Π x : M.Carrier, TangentSpace M.model x :=
    fun y ↦ tangentCoordChange M.model p y y (deriv c (τ y))
  have hX₀ : ContMDiffOn M.model (M.model.prod 𝓘(ℝ, SpacetimeModel)) ∞ (T% X₀) U := by
    rw [(trivializationAt SpacetimeModel (TangentSpace M.model) p).contMDiffOn_section_iff
      hUo (fun y hy ↦ (hUsub hy).1)]
    intro y hy
    obtain ⟨-, h2, h3⟩ := hUsub hy
    have hw : ContMDiffAt M.model 𝓘(ℝ, SpacetimeModel) ∞ (fun y ↦ deriv c (τ y)) y :=
      ((hc'.contDiffAt (hJ.mem_nhds h3)).contMDiffAt).comp y h2
    have key : ∀ z ∈ U,
        (trivializationAt SpacetimeModel (TangentSpace M.model) p ⟨z, X₀ z⟩).2 =
          deriv c (τ z) := fun z hz ↦ by
      have hzp : z ∈ (extChartAt M.model p).source := by
        rw [extChartAt_source]; exact (hUsub hz).1
      change tangentCoordChange M.model z p z (tangentCoordChange M.model p z z _) = _
      exact (tangentCoordChange_comp ⟨⟨hzp, mem_extChartAt_source _⟩, hzp⟩).trans
        (tangentCoordChange_self hzp)
    exact hw.contMDiffWithinAt.congr key (key y hy)
  obtain ⟨X, hX, hXeq⟩ := exists_contMDiff_vectorField_eventuallyEq hUo hpU hX₀
  refine ⟨X, hX, ?_⟩
  filter_upwards [hμc.eventually hXeq, hJ.mem_nhds hsJ, hτμ] with t h1 h2 h3
  rw [h1]
  change tangentCoordChange M.model p (μ.toFun t) (μ.toFun t) (deriv c (τ (μ.toFun t))) = _
  rw [h3, hderiv t h2]
  have hq : μ.toFun t ∈ (extChartAt M.model p).source := by
    rw [extChartAt_source]; exact h2.2
  have hqq := mem_extChartAt_source (I := M.model) (μ.toFun t)
  exact (tangentCoordChange_comp ⟨⟨hqq, hq⟩, hqq⟩).trans (tangentCoordChange_self hqq)

end Spacetime

end Physicslib4
