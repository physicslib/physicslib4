/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Diffeo
import Physicslib4.Spacetime.Curves
import Physicslib4.Spacetime.Causality
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Pushforward of a smooth path along a diffeomorphism

The pushforward `ψ ∘ μ` of a smooth path along a `C^⊤` diffeomorphism of the
underlying manifolds, its tangent vector (the chain rule along the parameter
space) and the transport of past and future endpoints.

**No metric appears anywhere in this file**, which is why it sits below
`Physicslib4/Spacetime/IsometryCausality.lean` in the import graph: the
single-metric pushforward `Isometry.pushforwardPath` there is the instance
`N := M` of `pushforwardPath` at `ψ := g.toDiffeo` and is defined as such,
rather than being a second copy of the same construction. The cross-metric
consumers live in `Physicslib4/Spacetime/CrossMetricIsometry.lean`.

## Main definitions

* `Physicslib4.Spacetime.pushforwardPath` (`lmm:cross-metric-pushforward-path`).
-/

namespace Physicslib4

namespace Spacetime

open scoped Manifold

variable {M N : Spacetime}

/-- **The tangent chain rule along a path**
(`lmm:cross-metric-pushforward-path-tangent`):
`d/ds (ψ ∘ μ)(s) = dψ_{μ s}(μ̇ s)`, the derivatives being taken within the
parameter space. The identity is about the differential of `ψ` alone and
mentions no metric. -/
theorem mfderivWithin_comp_diffeo (ψ : Diffeo M N) (μ : M.SmoothPath)
    {s : ℝ} (hs : s ∈ μ.parameterSpace) :
    mfderivWithin (modelWithCornersSelf ℝ ℝ) N.model
        ((ψ : M.Carrier → N.Carrier) ∘ μ.toFun) μ.parameterSpace s (1 : ℝ)
      = mfderiv M.model N.model ψ (μ.toFun s)
          (mfderivWithin (modelWithCornersSelf ℝ ℝ) M.model
            μ.toFun μ.parameterSpace s (1 : ℝ)) := by
  have huniq : UniqueMDiffWithinAt (modelWithCornersSelf ℝ ℝ) μ.parameterSpace s :=
    (Path.uniqueDiffOn_parameterSpace M μ.toPath s hs).uniqueMDiffWithinAt
  have hf : MDifferentiableWithinAt (modelWithCornersSelf ℝ ℝ) M.model
      μ.toFun μ.parameterSpace s :=
    (μ.smoothOn s hs).mdifferentiableWithinAt (by simp)
  have hg : MDifferentiableWithinAt M.model N.model
      (ψ : M.Carrier → N.Carrier) Set.univ (μ.toFun s) :=
    (ψ.mdifferentiable (by simp) (μ.toFun s)).mdifferentiableWithinAt
  have hcomp := mfderivWithin_comp s hg hf (by simp) huniq
  rw [mfderivWithin_univ] at hcomp
  rw [hcomp]
  rfl

/-- **Pushforward of a path along a diffeomorphism**
(`lmm:cross-metric-pushforward-path`): `ψ ∘ μ` on the same parameter space, with
the same closedness, connectedness and non-triviality data. The only real
obligation is non-vanishing of the tangent vector, which follows from injectivity
of `dψ_{μ s}` (`mfderivEquiv`). -/
noncomputable def pushforwardPath (ψ : Diffeo M N) (μ : M.SmoothPath) : N.SmoothPath where
  parameterSpace := μ.parameterSpace
  isClosed := μ.isClosed
  isConnected := μ.isConnected
  nontrivial := μ.nontrivial
  toFun := (ψ : M.Carrier → N.Carrier) ∘ μ.toFun
  continuousOn := ψ.continuous.comp_continuousOn μ.continuousOn
  smoothOn := ψ.contMDiff.comp_contMDiffOn μ.smoothOn
  nonvanishing := by
    intro s hs
    rw [mfderivWithin_comp_diffeo ψ μ hs,
      ← ψ.mfderivToContinuousLinearEquiv_coe (by simp),
      ContinuousLinearEquiv.coe_coe]
    exact fun h => μ.nonvanishing s hs
      ((ψ.mfderivToContinuousLinearEquiv (by simp) (μ.toFun s)).injective
        (h.trans (map_zero _).symm))

@[simp] theorem pushforwardPath_parameterSpace (ψ : Diffeo M N) (μ : M.SmoothPath) :
    (pushforwardPath ψ μ).parameterSpace = μ.parameterSpace := rfl

@[simp] theorem pushforwardPath_toFun (ψ : Diffeo M N) (μ : M.SmoothPath) :
    (pushforwardPath ψ μ).toFun = (ψ : M.Carrier → N.Carrier) ∘ μ.toFun := rfl

/-- The tangent vector of the pushforward path is `dψ` applied to the tangent
vector of `μ` (`lmm:cross-metric-pushforward-path-tangent`). -/
theorem pushforwardPath_tangent (ψ : Diffeo M N) (μ : M.SmoothPath)
    {s : ℝ} (hs : s ∈ μ.parameterSpace) :
    (pushforwardPath ψ μ).tangent s
      = mfderiv M.model N.model ψ (μ.toFun s) (μ.tangent s) :=
  mfderivWithin_comp_diffeo ψ μ hs

/-- **The pushforward transports past endpoints**
(`lmm:cross-metric-pushforward-path-endpoints`). No metric or causal input is
used: the same parameter witnesses the condition. -/
theorem pushforwardPath_isPastEndpoint (ψ : Diffeo M N) (μ : M.SmoothPath)
    {p : M.Carrier} (h : IsPastEndpoint M μ p) :
    IsPastEndpoint N (pushforwardPath ψ μ) (ψ p) := by
  obtain ⟨s, hs, hsp, hmin⟩ := h
  exact ⟨s, hs, by simp only [pushforwardPath_toFun, Function.comp_apply, hsp], hmin⟩

/-- **The pushforward transports future endpoints**
(`lmm:cross-metric-pushforward-path-endpoints`). -/
theorem pushforwardPath_isFutureEndpoint (ψ : Diffeo M N) (μ : M.SmoothPath)
    {p : M.Carrier} (h : IsFutureEndpoint M μ p) :
    IsFutureEndpoint N (pushforwardPath ψ μ) (ψ p) := by
  obtain ⟨s, hs, hsp, hmax⟩ := h
  exact ⟨s, hs, by simp only [pushforwardPath_toFun, Function.comp_apply, hsp], hmax⟩

end Spacetime

end Physicslib4
