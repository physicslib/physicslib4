/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Unbounded.FunctionalCalculus

/-!
# Composition in the unbounded functional calculus

For a projection-valued measure `μ` and measurable functions `f, g`, this file states the
composition law `f(μ) g(μ) ⊆ (fg)(μ)` with its domain identity, together with the facts it
rests on: dominated convergence for the spectral integral, composition with a bounded function on
the left, the associated measure `μ_{h(μ)ψ} = |h|² μ_ψ` for unbounded `h`, and the commutation of
`h(μ)` with the spectral projections. For a self-adjoint `A` and a real measurable `f`, it states
that `f(A)` is self-adjoint and closed, and that `Dom A ∩ Dom f(A)` is a core for `f(A)`.

Throughout, `h(μ)` is `pmapIntegral μ h`, with domain `W_h = integralDomain μ h`, and for bounded
`u` the bounded operator `u(μ)` is `μ.integral u`.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap ENNReal NNReal
open Filter Topology ContinuousLinearMap MeasureTheory

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : ProjectionValuedMeasure X H)

private theorem fc_mul_bdd {u v : X → ℂ} (hu : u ∈ BddMeasurable X) (hv : v ∈ BddMeasurable X) :
    u * v ∈ BddMeasurable X :=
  let ⟨hu, Cu, hCu⟩ := hu
  let ⟨hv, Cv, hCv⟩ := hv
  ⟨hu.mul hv, Cu * Cv, fun x => by
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hCu x) (hCv x) (norm_nonneg _) ((norm_nonneg _).trans (hCu x))⟩

/-- `(∫ u) ψ - (∫ v) ψ = (∫ (u - v)) ψ` for bounded `u, v`. -/
private theorem fc_integral_sub_apply {u v : X → ℂ} (hu : u ∈ BddMeasurable X)
    (hv : v ∈ BddMeasurable X) (ψ : H) :
    μ.integral u ψ - μ.integral v ψ = μ.integral (u - v) ψ := by
  rw [← sub_add_cancel u v, μ.integral_add ((BddMeasurable X).sub_mem hu hv) hv, sub_add_cancel,
    add_apply, add_sub_cancel_right]

/-- `W_h ⊆ W_{uh}` for bounded `u`. -/
private theorem fc_mem_mul_bdd {u h : X → ℂ} (hu : u ∈ BddMeasurable X) (hh : Measurable h)
    {ψ : H} (hψ : ψ ∈ integralDomain μ h) : ψ ∈ integralDomain μ (u * h) := by
  obtain ⟨hum, C, hC⟩ := hu
  refine MemLp.of_le (hψ.const_mul (C : ℂ)) (hum.mul hh).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Pi.mul_apply, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C)) (norm_nonneg _)

private theorem fc_indicator_bdd {E : Set X} (hE : MeasurableSet E) :
    E.indicator (1 : X → ℂ) ∈ BddMeasurable X :=
  ⟨measurable_const.indicator hE, 1, fun x => by by_cases hx : x ∈ E <;> simp [hx]⟩

private theorem fc_memLp_two_iff {F : X → ℂ} (hF : Measurable F) (ν : Measure X) :
    MemLp F 2 ν ↔ ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂ν < ∞ :=
  ⟨fun h => lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top h,
    fun h => (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        hF.aestronglyMeasurable).2 h⟩

private theorem fc_pmap_congr {f f' : X → ℂ} (e : f = f') {x : H}
    (hx : x ∈ integralDomain μ f) (hx' : x ∈ integralDomain μ f') :
    pmapIntegral μ f ⟨x, hx⟩ = pmapIntegral μ f' ⟨x, hx'⟩ := by
  subst e; rfl

private theorem fc_pmap_congr_pt {f : X → ℂ} {x x' : H} (e : x = x')
    (hx : x ∈ integralDomain μ f) (hx' : x' ∈ integralDomain μ f) :
    pmapIntegral μ f ⟨x, hx⟩ = pmapIntegral μ f ⟨x', hx'⟩ := by
  subst e; rfl

private theorem fc_pmap_bdd {u : X → ℂ} (hu : u ∈ BddMeasurable X) (w : H)
    (hw : w ∈ integralDomain μ u) : pmapIntegral μ u ⟨w, hw⟩ = μ.integral u w := by
  obtain ⟨-, hext⟩ := LinearPMap.ext_iff.mp (pmapIntegral_of_bddMeasurable μ hu)
  rw [@hext w hw Submodule.mem_top]
  rfl

private theorem fc_pmap_one (w : H) (hw : w ∈ integralDomain μ (1 : X → ℂ)) :
    pmapIntegral μ 1 ⟨w, hw⟩ = w := by
  have h1 : (1 : X → ℂ) ∈ BddMeasurable X := ⟨measurable_const, 1, fun x => by simp⟩
  obtain ⟨-, hext⟩ := LinearPMap.ext_iff.mp (pmapIntegral_of_bddMeasurable μ h1)
  rw [@hext w hw Submodule.mem_top]
  change μ.integral 1 w = w
  rw [μ.integral_one]
  rfl

/--
Let `h` be measurable, `ψ ∈ W_h`, and let `hₙ` be bounded measurable functions with `hₙ → h`
pointwise and `|hₙ| ≤ |h|`. With the truncations `tₙ = h · 1_{|h| < n}`, the distance
`‖hₙ(μ)ψ - tₙ(μ)ψ‖` tends to `0`.

Blueprint: lmm:fc-difference-to-truncation
-/
theorem tendsto_norm_integral_sub_truncation {h : X → ℂ} (hh : Measurable h)
    (ψ : integralDomain μ h) {hn : ℕ → X → ℂ} (hbdd : ∀ n, hn n ∈ BddMeasurable X)
    (hlim : ∀ x, Tendsto (fun n => hn n x) atTop (𝓝 (h x)))
    (hle : ∀ n x, ‖hn n x‖ ≤ ‖h x‖) :
    Tendsto (fun n : ℕ => ‖μ.integral (hn n) (ψ : H) -
      μ.integral ({x | ‖h x‖ < n}.indicator h) (ψ : H)‖) atTop (𝓝 0) := by
  set t : ℕ → X → ℂ := fun n => {x | ‖h x‖ < n}.indicator h
  have ht := indicator_lt_mem_bddMeasurable hh
  have htlim : ∀ x, Tendsto (fun n => t n x) atTop (𝓝 (h x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ⌈‖h x‖⌉₊] with n hn
    have : ‖h x‖ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    simp [t, Set.indicator_of_mem (show x ∈ {x | ‖h x‖ < (n : ℝ)} from this)]
  have htle : ∀ n x, ‖t n x‖ ≤ ‖h x‖ := fun n x => by
    by_cases hx : x ∈ {x | ‖h x‖ < (n : ℝ)} <;> simp [t, hx]
  have hint : Integrable (fun x => ‖h x‖ ^ 2) (μ.assoc (ψ : H)) :=
    ψ.2.integrable_norm_pow two_ne_zero
  have hsq : Tendsto (fun n => ‖μ.integral (hn n) (ψ : H) - μ.integral (t n) ψ‖ ^ 2) atTop
      (𝓝 0) := by
    have heq : ∀ n, ‖μ.integral (hn n) (ψ : H) - μ.integral (t n) ψ‖ ^ 2 =
        ∫ x, ‖(hn n - t n) x‖ ^ 2 ∂(μ.assoc (ψ : H)) := fun n => by
      rw [fc_integral_sub_apply μ (hbdd n) (ht n),
        norm_sq_integral_apply μ ((BddMeasurable X).sub_mem (hbdd n) (ht n))]
    simp_rw [heq]
    have := tendsto_integral_of_dominated_convergence (μ := μ.assoc (ψ : H))
      (F := fun n x => ‖(hn n - t n) x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => 4 * ‖h x‖ ^ 2)
      (fun n => (((hbdd n).1.sub (ht n).1).norm.pow_const 2).aestronglyMeasurable)
      (hint.const_mul 4)
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : ‖(hn n - t n) x‖ ≤ 2 * ‖h x‖ := by
          rw [Pi.sub_apply]
          exact (norm_sub_le _ _).trans (by linarith [hle n x, htle n x])
        nlinarith [norm_nonneg ((hn n - t n) x), norm_nonneg (h x)])
      (ae_of_all _ fun x => by
        have := ((hlim x).sub (htlim x)).norm.pow 2
        simpa using this)
    simpa using this
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/--
Dominated convergence for the spectral integral: let `h` be measurable, `ψ ∈ W_h`, and let `hₙ`
be bounded measurable functions with `hₙ → h` pointwise and `|hₙ| ≤ |h|`. Then
`hₙ(μ)ψ → h(μ)ψ`.

Blueprint: lmm:fc-dominated-convergence
-/
theorem tendsto_integral_apply_of_dominated {h : X → ℂ} (hh : Measurable h)
    (ψ : integralDomain μ h) {hn : ℕ → X → ℂ} (hbdd : ∀ n, hn n ∈ BddMeasurable X)
    (hlim : ∀ x, Tendsto (fun n => hn n x) atTop (𝓝 (h x)))
    (hle : ∀ n x, ‖hn n x‖ ≤ ‖h x‖) :
    Tendsto (fun n => μ.integral (hn n) (ψ : H)) atTop (𝓝 (pmapIntegral μ h ψ)) := by
  have := (tendsto_integral_truncation μ hh ψ).add (tendsto_iff_norm_sub_tendsto_zero.mpr
    (by simpa using tendsto_norm_integral_sub_truncation μ hh ψ hbdd hlim hle) :
      Tendsto (fun n : ℕ => μ.integral (hn n) (ψ : H) -
        μ.integral ({x | ‖h x‖ < n}.indicator h) (ψ : H)) atTop (𝓝 0))
  rw [add_zero] at this
  exact this.congr fun n => add_sub_cancel _ _

/-- Bounded-left composition with the membership proof supplied by `fc_mem_mul_bdd`. -/
private theorem fc_integral_pmapIntegral {u h : X → ℂ} (hu : u ∈ BddMeasurable X)
    (hh : Measurable h) (ψ : integralDomain μ h) :
    μ.integral u (pmapIntegral μ h ψ) =
      pmapIntegral μ (u * h) ⟨ψ, fc_mem_mul_bdd μ hu hh ψ.2⟩ := by
  set t : ℕ → X → ℂ := fun n => {x | ‖h x‖ < n}.indicator h
  have ht := indicator_lt_mem_bddMeasurable hh
  have h1 : Tendsto (fun n => μ.integral u (μ.integral (t n) (ψ : H))) atTop
      (𝓝 (μ.integral u (pmapIntegral μ h ψ))) :=
    ((μ.integral u).continuous.tendsto _).comp (tendsto_integral_truncation μ hh ψ)
  refine tendsto_nhds_unique h1 ?_
  have h2 := tendsto_integral_apply_of_dominated μ (hu.1.mul hh)
    ⟨ψ, fc_mem_mul_bdd μ hu hh ψ.2⟩
    (hn := fun n => u * t n) (fun n => fc_mul_bdd hu (ht n))
    (fun x => by
      refine (tendsto_const_nhds (x := u x)).mul (tendsto_const_nhds.congr' ?_)
      filter_upwards [eventually_gt_atTop ⌈‖h x‖⌉₊] with n hn
      have : ‖h x‖ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
      simp [t, Set.indicator_of_mem (show x ∈ {x | ‖h x‖ < (n : ℝ)} from this)])
    (fun n x => by
      rw [Pi.mul_apply, Pi.mul_apply, norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      by_cases hx : x ∈ {x | ‖h x‖ < (n : ℝ)} <;> simp [t, hx])
  refine h2.congr fun n => ?_
  rw [μ.integral_mul hu (ht n)]
  rfl

/--
Composition with a bounded function on the left: for bounded measurable `u`, measurable `h` and
`ψ ∈ W_h`, the vector `ψ` lies in `W_{uh}` and `u(μ) h(μ) ψ = (uh)(μ) ψ`.

Blueprint: lmm:fc-bounded-left-composition
-/
theorem integral_apply_pmapIntegral {u h : X → ℂ} (hu : u ∈ BddMeasurable X)
    (hh : Measurable h) (ψ : integralDomain μ h) :
    ∃ hψ : (ψ : H) ∈ integralDomain μ (u * h),
      μ.integral u (pmapIntegral μ h ψ) = pmapIntegral μ (u * h) ⟨ψ, hψ⟩ :=
  ⟨_, fc_integral_pmapIntegral μ hu hh ψ⟩

/-- `μ_{h(μ)ψ}(E) = ∫_E |h|² dμ_ψ` for measurable `E`. -/
private theorem fc_assoc_pmapIntegral {h : X → ℂ} (hh : Measurable h) (ψ : integralDomain μ h)
    {E : Set X} (hE : MeasurableSet E) :
    (μ.assoc (pmapIntegral μ h ψ)) E = ∫⁻ x in E, (‖h x‖₊ : ℝ≥0∞) ^ 2 ∂(μ.assoc (ψ : H)) := by
  have hind := fc_indicator_bdd hE
  have hn := norm_sq_pmapIntegral μ ((hind.1).mul hh) ⟨ψ, fc_mem_mul_bdd μ hind hh ψ.2⟩
  rw [assoc_apply_eq_norm_sq, ← μ.integral_indicator hE, fc_integral_pmapIntegral μ hind hh]
  on_goal 2 => exact hE
  erw [hn]
  rw [ofReal_integral_eq_lintegral_ofReal
      ((fc_mem_mul_bdd μ hind hh ψ.2).integrable_norm_pow two_ne_zero)
      (ae_of_all _ fun x => by positivity), ← lintegral_indicator hE]
  congr 1
  funext x
  by_cases hx : x ∈ E <;> simp [hx, enorm_eq_nnnorm]

/--
The associated measure of `h(μ)ψ`, for measurable and not necessarily bounded `h` and
`ψ ∈ W_h`, is the measure with density `|h|²` with respect to `μ_ψ`: for every measurable `E`,
`μ_{h(μ)ψ}(E) = ∫_E |h|² dμ_ψ`.

Implementation note: the statement is the equality of measures with `Measure.withDensity`; the
per-set form follows from `MeasureTheory.withDensity_apply`.

Blueprint: lmm:fc-associated-measure
-/
theorem assoc_pmapIntegral {h : X → ℂ} (hh : Measurable h) (ψ : integralDomain μ h) :
    μ.assoc (pmapIntegral μ h ψ) =
      (μ.assoc (ψ : H)).withDensity fun x => (‖h x‖₊ : ℝ≥0∞) ^ 2 :=
  Measure.ext fun E hE => by rw [withDensity_apply _ hE, fc_assoc_pmapIntegral μ hh ψ hE]

/--
For measurable `f, g` and `ψ ∈ W_g`, the vector `g(μ)ψ` lies in `W_f` if and only if `ψ` lies
in `W_{fg}`.

Blueprint: lmm:fc-composition-domain
-/
theorem pmapIntegral_mem_integralDomain_iff {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) (ψ : integralDomain μ g) :
    pmapIntegral μ g ψ ∈ integralDomain μ f ↔ (ψ : H) ∈ integralDomain μ (f * g) := by
  rw [mem_integralDomain, mem_integralDomain, assoc_pmapIntegral μ hg ψ,
    fc_memLp_two_iff hf, fc_memLp_two_iff (hf.mul hg),
    lintegral_withDensity_eq_lintegral_mul _
      (hg.nnnorm.coe_nnreal_ennreal.pow_const 2) (hf.enorm.pow_const _)]
  refine Iff.of_eq (congrArg (· < ∞) (lintegral_congr fun x => ?_))
  simp only [Pi.mul_apply, ENNReal.rpow_two, enorm_eq_nnnorm]
  rw [nnnorm_mul, ENNReal.coe_mul]
  ring

/-- `μ({|f| < n}) w → w`. -/
private theorem fc_tendsto_indicator {f : X → ℂ} (hf : Measurable f) (w : H) :
    Tendsto (fun n : ℕ => μ.integral ({x | ‖f x‖ < n}.indicator 1) w) atTop (𝓝 w) := by
  have h1 : (1 : X → ℂ) ∈ BddMeasurable X := ⟨measurable_const, 1, fun x => by simp⟩
  have hw : w ∈ integralDomain μ (1 : X → ℂ) := by
    rw [integralDomain_eq_top_of_bddMeasurable μ h1]
    trivial
  have := tendsto_integral_apply_of_dominated μ (h := (1 : X → ℂ)) h1.1 ⟨w, hw⟩
    (hn := fun n : ℕ => {x | ‖f x‖ < n}.indicator 1)
    (fun n => fc_indicator_bdd (measurableSet_lt hf.norm measurable_const))
    (fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop ⌈‖f x‖⌉₊] with n hn
      have : ‖f x‖ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
      simp [Set.indicator_of_mem (show x ∈ {x | ‖f x‖ < (n : ℝ)} from this)])
    (fun n x => by
      by_cases hx : x ∈ {x | ‖f x‖ < (n : ℝ)} <;> simp [Set.indicator, hx])
  convert this using 2
  exact (fc_pmap_one μ w hw).symm

/-- The composition law `f(μ) g(μ) ⊆ (fg)(μ)`. -/
private theorem fc_comp {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (ψ : integralDomain μ g) (hy : pmapIntegral μ g ψ ∈ integralDomain μ f) :
    ∃ hfg : (ψ : H) ∈ integralDomain μ (f * g),
      pmapIntegral μ (f * g) ⟨ψ, hfg⟩ = pmapIntegral μ f ⟨_, hy⟩ := by
  have hfg := (pmapIntegral_mem_integralDomain_iff μ hf hg ψ).1 hy
  refine ⟨hfg, tendsto_nhds_unique ?_ (tendsto_integral_truncation μ hf ⟨_, hy⟩)⟩
  set E : ℕ → Set X := fun n => {x | ‖f x‖ < n}
  have hE : ∀ n, MeasurableSet (E n) := fun n => measurableSet_lt hf.norm measurable_const
  refine (fc_tendsto_indicator μ hf (pmapIntegral μ (f * g) ⟨ψ, hfg⟩)).congr fun n => ?_
  have h1 := fc_integral_pmapIntegral μ (fc_indicator_bdd (hE n)) (hf.mul hg) ⟨ψ, hfg⟩
  have h2 := fc_integral_pmapIntegral μ (indicator_lt_mem_bddMeasurable hf n) hg ψ
  refine h1.trans ((fc_pmap_congr μ ?_ _ _).trans h2.symm)
  funext x
  by_cases hx : x ∈ E n <;> simp [E, Set.indicator, hx] at *

/--
The composition law: for measurable `f, g`, the operator `(fg)(μ)` extends `f(μ) g(μ)`, and the
domain of `f(μ) g(μ)` is `W_g ∩ W_{fg}`.

Implementation note: the product `f(μ) g(μ)` is not a bundled operator here. Its domain is the
set of `ψ ∈ W_g` with `g(μ)ψ ∈ W_f`, and the first conjunct identifies this set with
`W_g ∩ W_{fg}`. The second conjunct is the extension property: on that domain, `ψ ∈ W_{fg}` and
`(fg)(μ)ψ = f(μ)(g(μ)ψ)`. For a self-adjoint `A` this gives `f(A) g(A) ⊆ (fg)(A)` through
`functionalCalculus`, which is `pmapIntegral` of the spectral measure.

Blueprint: thrm:fc-composition
-/
theorem pmapIntegral_comp {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g) :
    {ψ : H | ∃ hψ : ψ ∈ integralDomain μ g, pmapIntegral μ g ⟨ψ, hψ⟩ ∈ integralDomain μ f} =
        ((integralDomain μ g : Submodule ℂ H) : Set H) ∩ (integralDomain μ (f * g) : Set H) ∧
      ∀ (ψ : integralDomain μ g) (hy : pmapIntegral μ g ψ ∈ integralDomain μ f),
        ∃ hfg : (ψ : H) ∈ integralDomain μ (f * g),
          pmapIntegral μ (f * g) ⟨ψ, hfg⟩ = pmapIntegral μ f ⟨_, hy⟩ := by
  refine ⟨Set.ext fun ψ => ⟨fun ⟨hψ, hy⟩ => ⟨hψ,
    (pmapIntegral_mem_integralDomain_iff μ hf hg ⟨ψ, hψ⟩).1 hy⟩,
    fun ⟨hψ, hfg⟩ => ⟨hψ, (pmapIntegral_mem_integralDomain_iff μ hf hg ⟨ψ, hψ⟩).2 hfg⟩⟩,
    fc_comp μ hf hg⟩

/--
The spectral projections commute with `h(μ)`: for measurable `h`, `ψ ∈ W_h` and measurable `E`,
the vector `μ(E)ψ` lies in `W_h` and `h(μ) μ(E) ψ = μ(E) h(μ) ψ`.

Blueprint: lmm:fc-commutes-with-projections
-/
theorem pmapIntegral_apply_projection {h : X → ℂ} (hh : Measurable h) (ψ : integralDomain μ h)
    {E : Set X} (hE : MeasurableSet E) :
    ∃ hn : μ E ψ ∈ integralDomain μ h,
      pmapIntegral μ h ⟨_, hn⟩ = μ E (pmapIntegral μ h ψ) := by
  have hind := fc_indicator_bdd hE
  have htop : (ψ : H) ∈ integralDomain μ (E.indicator (1 : X → ℂ)) := by
    rw [integralDomain_eq_top_of_bddMeasurable μ hind]; trivial
  set ψ' : integralDomain μ (E.indicator (1 : X → ℂ)) := ⟨ψ, htop⟩
  have hval : pmapIntegral μ (E.indicator 1) ψ' = μ E ψ :=
    (fc_pmap_bdd μ hind ψ htop).trans (by rw [μ.integral_indicator hE])
  have hmem : (ψ : H) ∈ integralDomain μ (h * E.indicator 1) :=
    mul_comm h (E.indicator (1 : X → ℂ)) ▸ fc_mem_mul_bdd μ hind hh ψ.2
  have hy := (pmapIntegral_mem_integralDomain_iff μ hh hind.1 ψ').2 hmem
  obtain ⟨hfg, hcomp⟩ := fc_comp μ hh hind.1 ψ' hy
  have hn : μ E ψ ∈ integralDomain μ h := by rw [← hval]; exact hy
  refine ⟨hn, ?_⟩
  calc pmapIntegral μ h ⟨_, hn⟩ = pmapIntegral μ h ⟨_, hy⟩ := fc_pmap_congr_pt μ hval.symm _ _
    _ = pmapIntegral μ (h * E.indicator 1) ⟨ψ, hfg⟩ := hcomp.symm
    _ = pmapIntegral μ (E.indicator 1 * h) ⟨ψ, fc_mem_mul_bdd μ hind hh ψ.2⟩ :=
        fc_pmap_congr μ (mul_comm _ _) _ _
    _ = μ.integral (E.indicator 1) (pmapIntegral μ h ψ) :=
        (fc_integral_pmapIntegral μ hind hh ψ).symm
    _ = μ E (pmapIntegral μ h ψ) := by rw [μ.integral_indicator hE]

variable {A : H →ₗ.[ℂ] H}

/--
For a self-adjoint `A` and a measurable real-valued `f : ℝ → ℝ`, the operator `f(A)` is
self-adjoint, hence closed.

Implementation note: `f(A)` is `functionalCalculus hA` applied to `f` composed with the
inclusion `ℝ → ℂ`.

Blueprint: lmm:fc-real-closed
-/
theorem isSelfAdjoint_functionalCalculus_of_real (hA : IsSelfAdjoint A) {f : ℝ → ℝ}
    (hf : Measurable f) :
    IsSelfAdjoint (functionalCalculus hA fun x => (f x : ℂ)) ∧
      (functionalCalculus hA fun x => (f x : ℂ)).IsClosed := by
  have h : IsSelfAdjoint (functionalCalculus hA fun x => (f x : ℂ)) :=
    isSelfAdjoint_pmapIntegral_of_real _ (Complex.measurable_ofReal.comp hf)
      fun _ => Complex.ofReal_im _
  exact ⟨h, h.isClosed⟩

/--
For a self-adjoint `A` and a measurable real-valued `f : ℝ → ℝ`, the subspace
`Dom(A) ∩ Dom(f(A))` is a core for the closed operator `f(A)`. More precisely, for
`ψ ∈ Dom(f(A))` and `Eₙ = {λ | |λ| < n}`, the vectors `μ^A(Eₙ)ψ` lie in `Dom(A) ∩ Dom(f(A))`,
`μ^A(Eₙ)ψ → ψ` and `f(A) μ^A(Eₙ)ψ → f(A)ψ`.

Implementation note: the core property is Mathlib's `LinearPMap.HasCore`, which says that the
closure of the restriction of `f(A)` to the subspace is `f(A)`; the blueprint's notion of a core
(`def:core`) is not given a separate Lean definition. The intersection `Dom(A) ∩ Dom(f(A))` is
the submodule infimum `A.domain ⊓ (functionalCalculus hA _).domain`.

Blueprint: lmm:fc-core
-/
theorem hasCore_functionalCalculus (hA : IsSelfAdjoint A) {f : ℝ → ℝ} (hf : Measurable f) :
    (functionalCalculus hA fun x => (f x : ℂ)).HasCore
        (A.domain ⊓ (functionalCalculus hA fun x => (f x : ℂ)).domain) ∧
      ∀ ψ : (functionalCalculus hA fun x => (f x : ℂ)).domain,
        ∃ hn : ∀ n : ℕ, spectralMeasure hA {x | |x| < n} (ψ : H) ∈
            A.domain ⊓ (functionalCalculus hA fun x => (f x : ℂ)).domain,
          Tendsto (fun n : ℕ => spectralMeasure hA {x | |x| < n} (ψ : H)) atTop (𝓝 ψ) ∧
          Tendsto (fun n : ℕ => functionalCalculus hA (fun x => (f x : ℂ))
              ⟨_, (hn n).2⟩) atTop
            (𝓝 (functionalCalculus hA (fun x => (f x : ℂ)) ψ)) := by
  have hh : Measurable fun x : ℝ => (f x : ℂ) := Complex.measurable_ofReal.comp hf
  have hk : Measurable fun x : ℝ => (x : ℂ) := Complex.measurable_ofReal
  have hE : ∀ n : ℕ, MeasurableSet {x : ℝ | |x| < n} := fun n =>
    measurableSet_lt continuous_abs.measurable measurable_const
  have hset : ∀ n : ℕ, {x : ℝ | ‖(x : ℂ)‖ < (n : ℝ)} = {x : ℝ | |x| < (n : ℝ)} := fun n => by
    ext; simp
  have hconv : ∀ w : H, Tendsto (fun n : ℕ => spectralMeasure hA {x | |x| < n} w) atTop
      (𝓝 w) := fun w => by
    simpa only [hset, (spectralMeasure hA).integral_indicator (hE _)] using
      fc_tendsto_indicator (spectralMeasure hA) hk w
  have hmem : ∀ (ψ : (functionalCalculus hA fun x => (f x : ℂ)).domain) (n : ℕ),
      spectralMeasure hA {x | |x| < n} (ψ : H) ∈
        A.domain ⊓ (functionalCalculus hA fun x => (f x : ℂ)).domain := fun ψ n => by
    refine ⟨?_, (pmapIntegral_apply_projection (spectralMeasure hA) hh ψ (hE n)).1⟩
    rw [domain_eq_integralDomain_spectralMeasure hA]
    exact range_subset_integralDomain (spectralMeasure hA) hk (hE n) (c := n)
      (fun x hx => by simpa using hx.le) ⟨ψ, rfl⟩
  have key : ∀ ψ : (functionalCalculus hA fun x => (f x : ℂ)).domain,
      Tendsto (fun n : ℕ => functionalCalculus hA (fun x => (f x : ℂ)) ⟨_, (hmem ψ n).2⟩)
        atTop (𝓝 (functionalCalculus hA (fun x => (f x : ℂ)) ψ)) := fun ψ =>
    (hconv _).congr fun n =>
      (pmapIntegral_apply_projection (spectralMeasure hA) hh ψ (hE n)).2.symm
  refine ⟨⟨inf_le_right, ?_⟩, fun ψ => ⟨hmem ψ, hconv _, key ψ⟩⟩
  have hcl := (isSelfAdjoint_functionalCalculus_of_real hA hf).2
  have hle : (functionalCalculus hA fun x => (f x : ℂ)).domRestrict
      (A.domain ⊓ (functionalCalculus hA fun x => (f x : ℂ)).domain) ≤
        functionalCalculus hA fun x => (f x : ℂ) := LinearPMap.domRestrict_le
  refine LinearPMap.eq_of_eq_graph ?_
  rw [← (hcl.isClosable.leIsClosable hle).graph_closure_eq_closure_graph]
  refine le_antisymm (Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hle) hcl)
    fun p hp => ?_
  obtain ⟨ψ, h1, h2⟩ := (LinearPMap.mem_graph_iff _).mp hp
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, ← Prod.mk.eta (p := p), ← h1, ← h2]
  exact mem_closure_of_tendsto ((hconv ψ).prodMk_nhds (key ψ))
    (Eventually.of_forall fun n => (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨_, hmem ψ n, (hmem ψ n).2⟩, rfl, rfl⟩)

end Unbounded
end Spectral
end Physicslib4
