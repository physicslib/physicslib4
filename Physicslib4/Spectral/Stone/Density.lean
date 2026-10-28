/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Stone.Basic

/-!
# The generator of a strongly continuous unitary group is densely defined

For a strongly continuous one-parameter unitary group `U`, the averages
`B_f ψ = ∫ f(τ) U(τ) ψ dτ` against smooth compactly supported `f` lie in the domain of the
generator, and averaging against an approximate identity recovers `ψ`; so the generator's
domain is dense (blueprint §10.4.4, Lemma `lmm:hall-10.18`). Averages are written as
convolutions `f ⋆ g_ψ` with `g_ψ(x) = U(-x) ψ`, to use Mathlib's convolution calculus.

## Main definitions

* `average U f ψ` — the average `B_f ψ = ∫ f(τ) U(τ) ψ dτ`.

## Main statements

* `average_eq_convolution` — `U(t) B_f ψ = (f ⋆ g_ψ)(-t)`.
* `average_mem_generator_domain` — `B_f ψ ∈ Dom(A)` for `C¹` compactly supported `f`.
* `tendsto_average_bump` — averages against bumps shrinking to `0` tend to `ψ`.
* `hasDenseDomain_generator` — the generator is densely defined.
-/

namespace Physicslib4
namespace Spectral
namespace Stone

open scoped InnerProductSpace LinearPMap Topology Convolution
open Filter MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/--
The average B_f ψ = ∫ f(τ) U(τ)ψ dτ of the orbit of a vector ψ against a real weight function
f.

Averaging the orbit τ ↦ U(τ)ψ against a smooth bump f smooths it in the group parameter: the
average lies in the domain of the generator when f is continuously differentiable with compact
support (`average_mem_generator_domain`), and it tends to ψ as f concentrates at τ = 0
(`tendsto_average_bump`). These two facts give density of the generator's domain
(`hasDenseDomain_generator`). This is the one-parameter case of Gårding's smoothing argument.

Implementation note: the integral is Mathlib's Bochner integral for Lebesgue measure on ℝ,
which is 0 when the integrand is not integrable or H is not complete. The results that use the
average assume U strongly continuous and f a compactly supported C¹ weight or a bump function.
To use Mathlib's convolution calculus, the average is rewritten as a convolution f ⋆ g_ψ with
g_ψ(x) = U(−x)ψ (`average_eq_convolution`, which holds for every f).

Blueprint: lmm:averaging-translate
-/
noncomputable def average (U : ℝ → (H ≃ₗᵢ[ℂ] H)) (f : ℝ → ℝ) (ψ : H) : H :=
  ∫ τ, f τ • U τ ψ

/--
Averages are convolutions: with `g_ψ(x) = U(-x) ψ`, `U(t) B_f ψ = (f ⋆ g_ψ)(-t)`; in
particular `B_f ψ = (f ⋆ g_ψ)(0)`. The blueprint takes `f` continuous with compact support
and `U` strongly continuous, to make the integrals Bochner integrable; the identity holds for
every `f`, both sides being Bochner integrals of the same function up to the unitary `U(t)`,
so those hypotheses are omitted.

Blueprint reference: `lmm:averaging-translate`.
-/
theorem average_eq_convolution {U : ℝ → (H ≃ₗᵢ[ℂ] H)} (hU : IsOneParameterUnitaryGroup U)
    (f : ℝ → ℝ) (ψ : H) (t : ℝ) :
    U t (average U f ψ) = (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ] fun x => U (-x) ψ) (-t) := by
  have h := (U t).toContinuousLinearEquiv.integral_comp_comm (μ := volume)
    (fun τ : ℝ => f τ • U τ ψ)
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h
  rw [convolution_lsmul, average, ← h]
  congr 1
  ext τ
  rw [LinearMapClass.map_smul_of_tower, ← hU.map_add, neg_sub, sub_neg_eq_add, add_comm]

/--
Averages against continuously differentiable compactly supported weights lie in the domain of
the generator.

Blueprint reference: `lmm:averaging-in-generator-domain`.
-/
theorem average_mem_generator_domain {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (hc : IsStronglyContinuous U) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f) (ψ : H) :
    average U f ψ ∈ (generator U).domain := by
  set F := f ⋆[ContinuousLinearMap.lsmul ℝ ℝ] fun x => U (-x) ψ
  have hF := hfs.hasDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := volume) hf ((hc ψ).comp continuous_neg).locallyIntegrable (-0)
  refine ⟨_, ((hasDerivAt_iff_tendsto_slope_zero.mp (hF.scomp 0 (hasDerivAt_neg 0))).const_smul
    Complex.I⁻¹).congr fun t => ?_⟩
  have hav (s : ℝ) : F (-s) = U s (average U f ψ) :=
    (average_eq_convolution hU f ψ s).symm
  change Complex.I⁻¹ • t⁻¹ • (F (-(0 + t)) - F (-0)) = _
  rw [generatorQuotient, zero_add, hav, hav, hU.map_zero, mul_inv, mul_comm, mul_smul,
    ← Complex.ofReal_inv, Complex.coe_smul, smul_comm]

/--
Averages against an approximate identity recover the vector: if `φ i` are bump functions at
`0` whose outer radii tend to `0` along `l`, the averages of `ψ` against their normalisations
tend to `ψ`. The blueprint's `f_n`, with outer radius `1/n`, is the case `l = atTop`.

Blueprint reference: `lmm:averaging-approximates`.
-/
theorem tendsto_average_bump [CompleteSpace H] {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U)
    (hc : IsStronglyContinuous U) {ι : Type*} {φ : ι → ContDiffBump (0 : ℝ)} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (ψ : H) :
    Tendsto (fun i => average U ((φ i).normed volume) ψ) l (𝓝 ψ) := by
  have hg : Continuous fun x : ℝ => U (-x) ψ := (hc ψ).comp continuous_neg
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hg 0
  rw [neg_zero, hU.map_zero] at h
  refine h.congr fun i => ?_
  have := average_eq_convolution hU ((φ i).normed volume) ψ 0
  rwa [hU.map_zero, neg_zero, eq_comm] at this

/--
The infinitesimal generator of a strongly continuous one-parameter unitary group has dense
domain.

Density is what makes the generator A an unbounded operator in the usual sense
(`Unbounded.HasDenseDomain`), with a well-defined adjoint A\*; the proof of Stone's theorem
uses it to show that A is essentially self-adjoint (`isEssentiallySelfAdjoint_generator`). The
proof here approximates any ψ by averages B_f ψ of its orbit against narrow bump functions f:
each average lies in Dom(A), and the averages tend to ψ as the bumps shrink to τ = 0.

Implementation note: H is assumed complete, so that the Bochner integrals defining the averages
are not the junk value 0. The bumps are Mathlib's normalised `ContDiffBump` functions at 0 with
inner radius 1/(2(n + 1)) and outer radius 1/(n + 1), the blueprint's f_n reindexed from 0. The
average in Dom(A) is `average_mem_generator_domain`, via the derivative of a convolution; the
approximation is `tendsto_average_bump`, via
`ContDiffBump.convolution_tendsto_right_of_continuous`.

Blueprint: lmm:hall-10.18
-/
theorem hasDenseDomain_generator [CompleteSpace H] {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U)
    (hc : IsStronglyContinuous U) : Unbounded.HasDenseDomain (generator U) := by
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨1 / (2 * (n + 1)), 1 / (n + 1), by positivity, by gcongr; linarith⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine fun ψ => mem_closure_of_tendsto (tendsto_average_bump hU hc hφ ψ)
    (Eventually.of_forall fun n => ?_)
  exact average_mem_generator_domain hU hc ((φ n).contDiff_normed (n := 1))
    (φ n).hasCompactSupport_normed ψ

end Stone
end Spectral
end Physicslib4
