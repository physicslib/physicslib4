/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Topology.UrysohnsLemma
import Physicslib4.Spectral.Basic

/-!
# Bootstrapping from continuous to bounded Borel functions

The blueprint extends the continuous functional calculus to bounded Borel functions
by a monotone-class argument: any class of bounded measurable functions which is a
complex subspace, contains the continuous real functions, and is closed under
uniformly bounded pointwise limits, already contains *all* bounded Borel functions.

This file records that argument's ingredients: bump functions, the monotone class
theorem, the class `L₀` of sets whose indicator is a bounded pointwise limit of
continuous functions, and the class `𝒞` of the bootstrap itself.

## Main definitions

* `Physicslib4.Spectral.IsBumpFunction`.
* `Physicslib4.Spectral.IsMonotoneClass`.
* `Physicslib4.Spectral.L0` — the blueprint's `𝓛₀`.
* `Physicslib4.Spectral.IsBorelGenerating` — the blueprint's hypotheses on `𝒞`.

## Main statements

* `Physicslib4.Spectral.exists_isBumpFunction` — Urysohn-type existence of bump
  functions on a normal space.
* `Physicslib4.Spectral.generateFrom_subset_of_isMonotoneClass` — the monotone class
  theorem.
* `Physicslib4.Spectral.empty_mem_L0`, `Physicslib4.Spectral.compl_mem_L0`,
  `Physicslib4.Spectral.union_mem_L0`, `Physicslib4.Spectral.isClosed_mem_L0` — the
  closure properties of `𝓛₀`. Only the last needs the metric; the `variable` blocks
  below are split accordingly.
* `Physicslib4.Spectral.isSetAlgebra_L0` — `𝓛₀` is an algebra of sets containing the
  open sets, derived from the four preceding statements.
* `Physicslib4.Spectral.IsBorelGenerating.indicator_mem` — `𝒞` contains the
  indicator of every Borel set. Together with
  `Physicslib4.Spectral.IsBorelGenerating.eq_bddMeasurable` this is the only place
  the compact metric Borel context is needed; `IsBorelGenerating` itself is stated
  for an arbitrary topological measurable space.
* `Physicslib4.Spectral.IsBorelGenerating.eq_bddMeasurable` — `𝒞` is exactly the set
  of bounded Borel functions.

## Implementation notes

The blueprint's `def:algebra-of-sets` is Mathlib's `MeasureTheory.IsSetAlgebra`.
-/

namespace Physicslib4
namespace Spectral

open Filter Topology MeasureTheory

/-!
### Bump functions
-/

/--
A *bump function* for a closed set `E` supported in an open set `U ⊇ E`: a
continuous function with values in `[0, 1]`, equal to `1` on `E`, and supported in
`U`.

Blueprint reference: `def:bump-function`.
-/
structure IsBumpFunction {X : Type*} [TopologicalSpace X] (E U : Set X) (f : C(X, ℝ)) :
    Prop where
  /-- The function takes values in `[0, 1]`. -/
  mem_Icc : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1
  /-- The function is `1` on `E`. -/
  eq_one : ∀ x ∈ E, f x = 1
  /-- The function is supported in `U`. -/
  support_subset : Function.support f ⊆ U

/--
On a normal topological space, every closed set has a bump function supported in any
given open neighbourhood of it.

Blueprint reference: `thrm:existence-of-bump-functions`.
-/
theorem exists_isBumpFunction {X : Type*} [TopologicalSpace X] [NormalSpace X] {E U : Set X}
    (hE : IsClosed E) (hU : IsOpen U) (hEU : E ⊆ U) :
    ∃ f : C(X, ℝ), IsBumpFunction E U f := by
  obtain ⟨f, hf0, hf1, hfIcc⟩ :=
    exists_continuous_zero_one_of_isClosed hU.isClosed_compl hE
      (Set.disjoint_compl_left_iff_subset.mpr hEU)
  refine ⟨f, hfIcc, fun x hx => hf1 hx, fun x hx => ?_⟩
  by_contra hxU
  exact hx (hf0 hxU)

/-!
### The monotone class theorem
-/

/--
A *monotone class* on `X` is a family of subsets closed under countable increasing
unions and countable decreasing intersections.
-/
structure IsMonotoneClass {X : Type*} (ℳ : Set (Set X)) : Prop where
  /-- Closure under countable increasing unions. -/
  iUnion_mem : ∀ f : ℕ → Set X, Monotone f → (∀ n, f n ∈ ℳ) → (⋃ n, f n) ∈ ℳ
  /-- Closure under countable decreasing intersections. -/
  iInter_mem : ∀ f : ℕ → Set X, Antitone f → (∀ n, f n ∈ ℳ) → (⋂ n, f n) ∈ ℳ

/--
**Monotone class theorem.** A monotone class containing an algebra of sets contains
the `σ`-algebra it generates.

Blueprint reference: `thrm:monotone-class-theorem`.
-/
theorem generateFrom_subset_of_isMonotoneClass {X : Type*} {𝒜 ℳ : Set (Set X)}
    (h𝒜 : IsSetAlgebra 𝒜) (hℳ : IsMonotoneClass ℳ) (h : 𝒜 ⊆ ℳ) :
    {s : Set X | MeasurableSet[MeasurableSpace.generateFrom 𝒜] s} ⊆ ℳ := by
  -- 𝒦 is the smallest monotone class containing 𝒜.
  let 𝒦 : Set (Set X) := fun s => ∀ 𝓜 : Set (Set X), IsMonotoneClass 𝓜 → 𝒜 ⊆ 𝓜 → s ∈ 𝓜
  have h𝒜𝒦 : 𝒜 ⊆ 𝒦 := by
    intro s hs 𝓜 _h𝓜 h𝒜𝓜
    exact h𝒜𝓜 hs
  have h𝒦ℳ : 𝒦 ⊆ ℳ := by
    intro s hs
    exact hs ℳ hℳ h
  have h𝒦_mono : IsMonotoneClass 𝒦 := by
    refine ⟨?_, ?_⟩
    · intro f hf hf𝒦 𝓜 h𝓜 h𝒜𝓜
      exact h𝓜.iUnion_mem f hf (fun n => hf𝒦 n 𝓜 h𝓜 h𝒜𝓜)
    · intro f hf hf𝒦 𝓜 h𝓜 h𝒜𝓜
      exact h𝓜.iInter_mem f hf (fun n => hf𝒦 n 𝓜 h𝓜 h𝒜𝓜)
  have hempty : (∅ : Set X) ∈ 𝒦 := h𝒜𝒦 h𝒜.empty_mem
  -- 𝒦 is closed under complement.
  have hcompl : ∀ s : Set X, s ∈ 𝒦 → sᶜ ∈ 𝒦 := by
    intro s hs
    let 𝒦c : Set (Set X) := fun t => tᶜ ∈ 𝒦
    have h𝒦c_mono : IsMonotoneClass 𝒦c := by
      refine ⟨?_, ?_⟩
      · intro f hf hf𝒦c
        change (⋃ n, f n)ᶜ ∈ 𝒦
        rw [Set.compl_iUnion]
        exact h𝒦_mono.iInter_mem (fun n => (f n)ᶜ)
          (fun i j hij => Set.compl_subset_compl.mpr (hf hij)) hf𝒦c
      · intro f hf hf𝒦c
        change (⋂ n, f n)ᶜ ∈ 𝒦
        rw [Set.compl_iInter]
        exact h𝒦_mono.iUnion_mem (fun n => (f n)ᶜ)
          (fun i j hij => Set.compl_subset_compl.mpr (hf hij)) hf𝒦c
    have h𝒜𝒦c : 𝒜 ⊆ 𝒦c := by
      intro a ha
      change aᶜ ∈ 𝒦
      exact h𝒜𝒦 (h𝒜.compl_mem ha)
    exact hs 𝒦c h𝒦c_mono h𝒜𝒦c
  -- 𝒦 is closed under union with an element of 𝒜.
  have hunion_mem_algebra : ∀ a ∈ 𝒜, ∀ u, u ∈ 𝒦 → a ∪ u ∈ 𝒦 := by
    intro a ha u hu
    let 𝒦a : Set (Set X) := fun v => a ∪ v ∈ 𝒦
    have h𝒦a_mono : IsMonotoneClass 𝒦a := by
      refine ⟨?_, ?_⟩
      · intro f hf hf𝒦a
        change a ∪ (⋃ n, f n) ∈ 𝒦
        rw [Set.union_iUnion]
        exact h𝒦_mono.iUnion_mem (fun n => a ∪ f n)
          (fun i j hij => Set.union_subset_union subset_rfl (hf hij)) hf𝒦a
      · intro f hf hf𝒦a
        change a ∪ (⋂ n, f n) ∈ 𝒦
        rw [Set.union_iInter]
        exact h𝒦_mono.iInter_mem (fun n => a ∪ f n)
          (fun i j hij => Set.union_subset_union subset_rfl (hf hij)) hf𝒦a
    have h𝒜𝒦a : 𝒜 ⊆ 𝒦a := by
      intro b hb
      change a ∪ b ∈ 𝒦
      exact h𝒜𝒦 (h𝒜.union_mem ha hb)
    exact hu 𝒦a h𝒦a_mono h𝒜𝒦a
  -- 𝒦 is closed under finite unions.
  have hunion : ∀ u v, u ∈ 𝒦 → v ∈ 𝒦 → u ∪ v ∈ 𝒦 := by
    intro u v hu hv
    let 𝒦u : Set (Set X) := fun w => u ∪ w ∈ 𝒦
    have h𝒦u_mono : IsMonotoneClass 𝒦u := by
      refine ⟨?_, ?_⟩
      · intro f hf hf𝒦u
        change u ∪ (⋃ n, f n) ∈ 𝒦
        rw [Set.union_iUnion]
        exact h𝒦_mono.iUnion_mem (fun n => u ∪ f n)
          (fun i j hij => Set.union_subset_union subset_rfl (hf hij)) hf𝒦u
      · intro f hf hf𝒦u
        change u ∪ (⋂ n, f n) ∈ 𝒦
        rw [Set.union_iInter]
        exact h𝒦_mono.iInter_mem (fun n => u ∪ f n)
          (fun i j hij => Set.union_subset_union subset_rfl (hf hij)) hf𝒦u
    have h𝒜𝒦u : 𝒜 ⊆ 𝒦u := by
      intro a ha
      change u ∪ a ∈ 𝒦
      rw [Set.union_comm]
      exact hunion_mem_algebra a ha u hu
    exact hv 𝒦u h𝒦u_mono h𝒜𝒦u
  -- 𝒦 is closed under countable unions.
  have hcountable : ∀ f : ℕ → Set X, (∀ n, f n ∈ 𝒦) → (⋃ n, f n) ∈ 𝒦 := by
    intro f hf
    let g : ℕ → Set X := Nat.rec (∅ : Set X) (fun n u => u ∪ f n)
    have hgsucc : ∀ n, g (n + 1) = g n ∪ f n := by
      intro n
      rfl
    have hg_mono : Monotone g := by
      refine monotone_nat_of_le_succ ?_
      intro n
      rw [hgsucc]
      exact Set.subset_union_left
    have hg𝒦 : ∀ n, g n ∈ 𝒦 := by
      intro n
      induction n with
      | zero => simpa [g] using hempty
      | succ n ih =>
        rw [hgsucc]
        exact hunion (g n) (f n) ih (hf n)
    have hg_eq : (⋃ n, g n) = ⋃ n, f n := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨k, hxk⟩
        suffices hmain : ∀ k, x ∈ g k → x ∈ ⋃ n, f n from hmain k hxk
        intro k
        induction k with
        | zero =>
          intro hxk0
          simp [g] at hxk0
        | succ k ih =>
          intro hxk
          rw [hgsucc] at hxk
          rcases hxk with hxk | hxk
          · exact ih hxk
          · rw [Set.mem_iUnion]
            exact ⟨k, hxk⟩
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨k, hxk⟩
        rw [Set.mem_iUnion]
        refine ⟨k + 1, ?_⟩
        rw [hgsucc]
        exact Or.inr hxk
    rw [← hg_eq]
    exact h𝒦_mono.iUnion_mem g hg_mono hg𝒦
  -- The σ-algebra generated by 𝒜 is contained in 𝒦 (π-λ induction on the π-system 𝒜).
  have h𝒦_induct : ∀ s : Set X, MeasurableSet[MeasurableSpace.generateFrom 𝒜] s → s ∈ 𝒦 := by
    intro s hs
    exact MeasurableSpace.induction_on_inter (m := MeasurableSpace.generateFrom 𝒜)
      (C := fun t _ => t ∈ 𝒦) (s := 𝒜) rfl
      (by
        intro a ha b hb _hne
        exact h𝒜.inter_mem ha hb)
      hempty
      (fun t ht => h𝒜𝒦 ht)
      (fun t _htm htk => hcompl t htk)
      (fun f _hfd _hfm hfi => hcountable f hfi)
      s hs
  intro s hs
  exact h𝒦ℳ (h𝒦_induct s hs)

/-!
### The class `𝓛₀`
-/

/--
The blueprint's class `𝓛₀`: the sets whose indicator function is the *pointwise*
limit of a uniformly bounded sequence of continuous real-valued functions.

The dependence of the rate of convergence on the point is essential: uniform
convergence would force the indicator to be continuous.

The blueprint also asks that `E` be measurable. That is not recorded here: under
`[BorelSpace X]` an indicator which is a pointwise limit of continuous functions is
automatically measurable, hence so is `E` (see `measurableSet_of_mem_L0`), and
carrying the conjunct would make every membership proof discharge a derivable
obligation.

Blueprint reference: `def:L0-class`.
-/
def L0 (X : Type*) [TopologicalSpace X] [MeasurableSpace X] : Set (Set X) :=
  {E | ∃ (f : ℕ → C(X, ℝ)) (C : ℝ), (∀ n x, ‖f n x‖ ≤ C) ∧
    ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (E.indicator (1 : X → ℝ) x))}

section Topological

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/--
The empty set lies in `𝓛₀`, witnessed by the constant sequence `0`.

Blueprint reference: `prpstn:L0-contains-empty`.
-/
theorem empty_mem_L0 : (∅ : Set X) ∈ L0 X :=
  ⟨fun _ => 0, 0, by simp, by simp⟩

/--
`𝓛₀` is closed under complements, witnessed by `1 - fₙ`.

Blueprint reference: `prpstn:L0-complement`.
-/
theorem compl_mem_L0 {E : Set X} (hE : E ∈ L0 X) : Eᶜ ∈ L0 X := by
  rcases hE with ⟨f, C, hf_bound, hf_tendsto⟩
  refine ⟨fun n => (1 : C(X, ℝ)) - f n, C + 1, ?_, ?_⟩
  · intro n x
    have hnorm : ‖(1 : ℝ) - f n x‖ ≤ C + 1 := by
      calc
        ‖(1 : ℝ) - f n x‖ ≤ ‖(1 : ℝ)‖ + ‖f n x‖ := norm_sub_le _ _
        _ = 1 + ‖f n x‖ := by simp
        _ ≤ C + 1 := by linarith [hf_bound n x]
    simpa using hnorm
  · intro x
    have hcomp : (Eᶜ).indicator (1 : X → ℝ) x = 1 - E.indicator (1 : X → ℝ) x := by
      by_cases hx : x ∈ E
      · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
      · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    simpa [hcomp] using (hf_tendsto x).const_sub (1 : ℝ)

/--
`𝓛₀` is closed under finite unions, witnessed by `fₙ + gₙ - fₙ gₙ`.

Blueprint reference: `prpstn:L0-union`.
-/
theorem union_mem_L0 {E F : Set X} (hE : E ∈ L0 X) (hF : F ∈ L0 X) : E ∪ F ∈ L0 X := by
  rcases hE with ⟨f, Cf, hfB, hfT⟩
  rcases hF with ⟨g, Cg, hgB, hgT⟩
  refine ⟨fun n => f n + g n - f n * g n, Cf + Cg + Cf * Cg, ?_, ?_⟩
  · intro n x
    have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg (f n x)) (hfB n x)
    have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (g n x)) (hgB n x)
    have hsub : ‖f n x + g n x - f n x * g n x‖ ≤ ‖f n x + g n x‖ + ‖f n x * g n x‖ :=
      norm_sub_le (f n x + g n x) (f n x * g n x)
    have h1 : ‖f n x + g n x‖ ≤ Cf + Cg :=
      le_trans (norm_add_le (f n x) (g n x)) (add_le_add (hfB n x) (hgB n x))
    have h2 : ‖f n x * g n x‖ ≤ Cf * Cg := by
      calc
        ‖f n x * g n x‖ ≤ ‖f n x‖ * ‖g n x‖ := norm_mul_le (f n x) (g n x)
        _ ≤ Cf * ‖g n x‖ := mul_le_mul_of_nonneg_right (hfB n x) (norm_nonneg (g n x))
        _ ≤ Cf * Cg := mul_le_mul_of_nonneg_left (hgB n x) hCf0
    exact le_trans hsub (add_le_add h1 h2)
  · intro x
    have hsum : Tendsto (fun n => f n x + g n x) atTop
        (𝓝 (E.indicator (1 : X → ℝ) x + F.indicator (1 : X → ℝ) x)) :=
      Tendsto.add (hfT x) (hgT x)
    have hprod : Tendsto (fun n => f n x * g n x) atTop
        (𝓝 (E.indicator (1 : X → ℝ) x * F.indicator (1 : X → ℝ) x)) :=
      Tendsto.mul (hfT x) (hgT x)
    have hlim : Tendsto (fun n => f n x + g n x - f n x * g n x) atTop
        (𝓝 (E.indicator (1 : X → ℝ) x + F.indicator (1 : X → ℝ) x -
          E.indicator (1 : X → ℝ) x * F.indicator (1 : X → ℝ) x)) :=
      Tendsto.sub hsum hprod
    have hind : (E ∪ F).indicator (1 : X → ℝ) x =
        E.indicator (1 : X → ℝ) x + F.indicator (1 : X → ℝ) x -
          E.indicator (1 : X → ℝ) x * F.indicator (1 : X → ℝ) x := by
      by_cases hx : x ∈ E <;> by_cases hy : x ∈ F <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy]
    simpa [hind] using hlim

end Topological

section Borel

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/--
A member of `𝓛₀` is measurable: its indicator is a pointwise limit of continuous,
hence measurable, functions.
-/
theorem measurableSet_of_mem_L0 {E : Set X} (hE : E ∈ L0 X) : MeasurableSet E := by
  rcases hE with ⟨f, -, -, hTendsto⟩
  have hf_meas : ∀ n, Measurable (f n : X → ℝ) := fun n => (f n).continuous.measurable
  have h_ind_meas : Measurable (E.indicator (1 : X → ℝ)) :=
    measurable_of_tendsto_metrizable hf_meas (tendsto_pi_nhds.mpr hTendsto)
  have hE_eq : E = (E.indicator (1 : X → ℝ)) ⁻¹' ({1} : Set ℝ) := by
    ext x
    simp [Set.indicator_eq_one_iff_mem]
  rw [hE_eq]
  exact h_ind_meas (MeasurableSet.singleton (1 : ℝ))

end Borel

/-!
### The bootstrap class `𝒞`

The hypotheses on `𝒞` mention only bounded measurable functions, continuous
real-valued functions and pointwise limits, so the definition is stated with no
assumption on `X` beyond a topology and a `σ`-algebra. The compact metric Borel
context is imposed on `IsBorelGenerating.indicator_mem` and
`IsBorelGenerating.eq_bddMeasurable` below, which are the statements that really
need it (through `isClosed_mem_L0`, hence through the bump functions).
-/

/--
The blueprint's hypotheses on the class `𝒞` used to bootstrap from continuous to
bounded Borel functions: `𝒞` consists of bounded measurable complex-valued
functions, is a complex subspace, contains the continuous real-valued functions, and
is closed under pointwise limits of uniformly bounded sequences.

Blueprint reference: the hypotheses (1)–(3) of `lmm:hall-prblm-8.3.3b`.
-/
structure IsBorelGenerating {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (𝒞 : Set (X → ℂ)) : Prop where
  /-- Every member is bounded and measurable. -/
  bddMeasurable : 𝒞 ⊆ (BddMeasurable X : Set (X → ℂ))
  /-- `𝒞` is a complex subspace. -/
  smul_add_mem : ∀ (α β : ℂ) (f g : X → ℂ), f ∈ 𝒞 → g ∈ 𝒞 → α • f + β • g ∈ 𝒞
  /-- `𝒞` contains the continuous real-valued functions. -/
  continuous_mem : ∀ f : C(X, ℝ), (fun x => ((f x : ℝ) : ℂ)) ∈ 𝒞
  /-- `𝒞` is closed under uniformly bounded pointwise limits. -/
  tendsto_mem : ∀ (f : ℕ → X → ℂ) (g : X → ℂ) (M : ℝ), (∀ n, f n ∈ 𝒞) →
    BoundedPointwiseLimit f g (fun _ => M) → g ∈ 𝒞

section Compact

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] [BorelSpace X] in
/--
Every closed subset of `X` lies in `𝓛₀`. This is the one closure property of `𝓛₀`
that needs the metric (indeed, the bump functions of
`Physicslib4.Spectral.exists_isBumpFunction`).

Blueprint reference: `prpstn:L0-contains-closed`.
-/
theorem isClosed_mem_L0 {E : Set X} (hE : IsClosed E) : E ∈ L0 X := by
  let U : ℕ → Set X := fun n => Metric.thickening (1 / (n + 1 : ℝ)) E
  have hU_open : ∀ n, IsOpen (U n) := fun _ => Metric.isOpen_thickening
  have hE_subset : ∀ n, E ⊆ U n := by
    intro n x hx
    rw [Metric.mem_thickening_iff]
    exact ⟨x, hx, by simpa using (by positivity : (0 : ℝ) < 1 / (n + 1))⟩
  let f : ℕ → C(X, ℝ) := fun n => (exists_isBumpFunction hE (hU_open n) (hE_subset n)).choose
  have hf : ∀ n, IsBumpFunction E (U n) (f n) := fun n =>
    (exists_isBumpFunction hE (hU_open n) (hE_subset n)).choose_spec
  refine ⟨f, 1, ?_, ?_⟩
  · intro n x
    have hnonneg : 0 ≤ f n x := (hf n).mem_Icc x |>.1
    have hle : f n x ≤ 1 := (hf n).mem_Icc x |>.2
    simp [Real.norm_eq_abs, abs_of_nonneg hnonneg, hle]
  · intro x
    by_cases hxE : x ∈ E
    · have heq : (fun n => f n x) = fun _ : ℕ => (1 : ℝ) := by
        funext n
        exact (hf n).eq_one x hxE
      rw [heq]
      simp [hxE]
    · have hxclosure : x ∉ closure E := by
        intro hcl
        exact hxE (by simpa [hE.closure_eq] using hcl)
      have h_eps : ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ E, ε ≤ dist x y := by
        have hnot : ¬ ∀ ε : ℝ, 0 < ε → ∃ y ∈ E, dist x y < ε := by
          intro h
          exact hxclosure ((Metric.mem_closure_iff).mpr h)
        push Not at hnot
        exact hnot
      obtain ⟨ε, hε_pos, hε_dist⟩ := h_eps
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε_pos
      have hnotU : ∀ n, N ≤ n → x ∉ U n := by
        intro n hn hxU
        obtain ⟨z, hzE, hzx⟩ := Metric.mem_thickening_iff.mp hxU
        have hle : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
          rw [one_div, one_div]
          exact (inv_le_inv₀ (by positivity : 0 < (n + 1 : ℝ))
            (by positivity : 0 < (N + 1 : ℝ))).2 (by exact_mod_cast Nat.succ_le_succ hn)
        have hlt : (1 : ℝ) / (n + 1) < dist x z :=
          lt_of_le_of_lt hle (lt_of_lt_of_le hN (hε_dist z hzE))
        exact (not_lt_of_ge hlt.le) hzx
      have hzero : ∀ n, N ≤ n → f n x = 0 := by
        intro n hn
        have hsupp : x ∉ Function.support (f n) := fun hxs =>
          hnotU n hn ((hf n).support_subset hxs)
        by_contra h
        exact hsupp (by simpa [Function.support] using h)
      have ht : Tendsto (fun n => f n x) atTop (𝓝 (0 : ℝ)) := by
        exact tendsto_atTop_of_eventually_const (u := fun n => f n x) (i₀ := N)
          (x := (0 : ℝ)) hzero
      simpa [hxE] using ht

/--
`𝓛₀` is an algebra of sets and contains every open subset of `X`.

This blueprint node is exactly the conjunction of `empty_mem_L0`, `compl_mem_L0`,
`union_mem_L0` and `isClosed_mem_L0`, so it is proved from them rather than restated.

Blueprint reference: `lmm:hall-prblm-8.3.3a`.
-/
theorem isSetAlgebra_L0 : IsSetAlgebra (L0 X) ∧ ∀ U : Set X, IsOpen U → U ∈ L0 X :=
  ⟨⟨empty_mem_L0, fun {_} h => compl_mem_L0 h, fun {_ _} h h' => union_mem_L0 h h'⟩,
    fun _U hU => by
      simpa using compl_mem_L0 (isClosed_mem_L0 hU.isClosed_compl)⟩

/--
The class `𝓛₁` of sets whose indicator lies in `𝒞` contains every Borel set.

Blueprint reference: `lmm:hall-prblm-8.3.3b`.
-/
theorem IsBorelGenerating.indicator_mem {𝒞 : Set (X → ℂ)} (h𝒞 : IsBorelGenerating 𝒞)
    {E : Set X} (hE : MeasurableSet E) : E.indicator (1 : X → ℂ) ∈ 𝒞 := by
  let ℒ : Set (Set X) := {E | E.indicator (1 : X → ℂ) ∈ 𝒞}
  have hℒ_subset : (L0 X) ⊆ ℒ := by
    intro E hE0
    rcases hE0 with ⟨f, C, hb, ht⟩
    refine h𝒞.tendsto_mem (fun n => fun x => ((f n x : ℝ) : ℂ))
      (E.indicator (1 : X → ℂ)) (max C 1) ?hmem ?hbpl
    · intro n
      exact h𝒞.continuous_mem (f n)
    · refine ⟨?_, ?_⟩
      · intro n x
        calc
          ‖((f n x : ℝ) : ℂ)‖ = ‖f n x‖ := by simp
          _ ≤ C := hb n x
          _ ≤ max C 1 := le_max_left C (1 : ℝ)
      · intro x
        have hcont : Continuous (fun r : ℝ => (r : ℂ)) := Complex.continuous_ofReal
        have hcv : Tendsto (fun n => ((f n x : ℝ) : ℂ)) atTop
            (𝓝 ((E.indicator (1 : X → ℝ) x : ℝ) : ℂ)) :=
          (hcont.tendsto (E.indicator (1 : X → ℝ) x)).comp (ht x)
        have hsame : (E.indicator (1 : X → ℂ) x) = ((E.indicator (1 : X → ℝ) x : ℝ) : ℂ) := by
          by_cases hx : x ∈ E
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
        simpa [hsame] using hcv
  have hℒ_mono : IsMonotoneClass ℒ := by
    refine ⟨?_, ?_⟩
    · intro f hfmon hf
      refine h𝒞.tendsto_mem (fun n => fun x => (f n).indicator (1 : X → ℂ) x)
        ((⋃ n, f n).indicator (1 : X → ℂ)) (1 : ℝ) (fun n => hf n) ⟨?_, ?_⟩
      · intro n x
        by_cases hx : x ∈ f n
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]
      · intro x
        by_cases hx : x ∈ ⋃ n, f n
        · rcases (Set.mem_iUnion.mp hx) with ⟨n₀, hn₀⟩
          have hconst : (fun _ : ℕ => (1 : ℂ)) =ᶠ[atTop]
              fun n => (f n).indicator (1 : X → ℂ) x := by
            refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
            have hxn : x ∈ f n := (hfmon hn) hn₀
            simp [Set.indicator_of_mem hxn]
          simpa [Set.indicator_of_mem hx] using
            Tendsto.congr' hconst (tendsto_const_nhds (x := (1 : ℂ)))
        · have hxn : ∀ n, x ∉ f n := by
            intro n
            exact fun hn => hx (Set.mem_iUnion.mpr ⟨n, hn⟩)
          have hconst : (fun _ : ℕ => (0 : ℂ)) =ᶠ[atTop]
              fun n => (f n).indicator (1 : X → ℂ) x := by
            refine Eventually.of_forall fun n => ?_
            simp [Set.indicator_of_notMem (hxn n)]
          simpa [Set.indicator_of_notMem hx] using
            Tendsto.congr' hconst (tendsto_const_nhds (x := (0 : ℂ)))
    · intro f hfant hf
      refine h𝒞.tendsto_mem (fun n => fun x => (f n).indicator (1 : X → ℂ) x)
        ((⋂ n, f n).indicator (1 : X → ℂ)) (1 : ℝ) (fun n => hf n) ⟨?_, ?_⟩
      · intro n x
        by_cases hx : x ∈ f n
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]
      · intro x
        by_cases hx : x ∈ ⋂ n, f n
        · have hconst : (fun _ : ℕ => (1 : ℂ)) =ᶠ[atTop]
              fun n => (f n).indicator (1 : X → ℂ) x := by
            refine Eventually.of_forall fun n => ?_
            have hxn : x ∈ f n := (Set.mem_iInter.mp hx) n
            simp [Set.indicator_of_mem hxn]
          simpa [Set.indicator_of_mem hx] using
            Tendsto.congr' hconst (tendsto_const_nhds (x := (1 : ℂ)))
        · have hxnot : ¬ ∀ n : ℕ, x ∈ f n := by
            intro h
            exact hx (Set.mem_iInter.mpr h)
          rcases not_forall.mp hxnot with ⟨n₀, hn₀⟩
          have hconst : (fun _ : ℕ => (0 : ℂ)) =ᶠ[atTop]
              fun n => (f n).indicator (1 : X → ℂ) x := by
            refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
            have hxn : x ∉ f n := fun hxn => hn₀ (hfant hn hxn)
            simp [Set.indicator_of_notMem hxn]
          simpa [Set.indicator_of_notMem hx] using
            Tendsto.congr' hconst (tendsto_const_nhds (x := (0 : ℂ)))
  have hMCT := generateFrom_subset_of_isMonotoneClass (𝒜 := L0 X) (ℳ := ℒ)
    isSetAlgebra_L0.1 hℒ_mono hℒ_subset
  have hle : borel X ≤ MeasurableSpace.generateFrom (L0 X) := by
    change MeasurableSpace.generateFrom {s : Set X | IsOpen s} ≤
      MeasurableSpace.generateFrom (L0 X)
    exact MeasurableSpace.generateFrom_mono (fun U hU => isSetAlgebra_L0.2 U hU)
  have hborel : MeasurableSet[borel X] E := by
    rw [← BorelSpace.measurable_eq]
    exact hE
  have hEgen : MeasurableSet[MeasurableSpace.generateFrom (L0 X)] E := by
    exact hle E hborel
  change E ∈ ℒ
  exact hMCT hEgen

/--
`𝒞` is exactly the set of bounded Borel-measurable complex-valued functions on `X`.

Blueprint reference: `lmm:hall-prblm-8.3.3c`.
-/
theorem IsBorelGenerating.eq_bddMeasurable {𝒞 : Set (X → ℂ)} (h𝒞 : IsBorelGenerating 𝒞) :
    𝒞 = (BddMeasurable X : Set (X → ℂ)) := by
  classical
  refine le_antisymm ?_ ?_
  · intro f hf
    exact h𝒞.bddMeasurable hf
  · rintro f hf
    /- `𝒞` contains the zero function, scalar multiples of its elements, and finite
    sums of its elements (all derived from the binary `smul_add_mem`). -/
    have hzero : (fun _ : X => (0 : ℂ)) ∈ 𝒞 := by
      simpa using h𝒞.continuous_mem (0 : C(X, ℝ))
    have hsmul : ∀ (α : ℂ) (g : X → ℂ), g ∈ 𝒞 → (fun x => α • g x) ∈ 𝒞 := by
      intro α g hg
      have h := h𝒞.smul_add_mem α 0 g g hg hg
      convert h using 1
      funext x
      simp
    have hsum_mem : ∀ (t : Finset ℂ) (u : ℂ → X → ℂ),
        (∀ c ∈ t, u c ∈ 𝒞) → (fun x => t.sum (fun c => u c x)) ∈ 𝒞 := by
      intro t u hu
      induction t using Finset.induction with
      | empty =>
          simpa using hzero
      | insert c rest hc ih =>
          have hc' : u c ∈ 𝒞 := hu c (Finset.mem_insert_self c rest)
          have hrest : (fun x => rest.sum (fun c' : ℂ => u c' x)) ∈ 𝒞 :=
            ih (fun c' hc' => hu c' (Finset.mem_insert_of_mem hc'))
          have hstep :=
            h𝒞.smul_add_mem (1 : ℂ) (1 : ℂ) (u c)
              (fun x => rest.sum (fun c' : ℂ => u c' x)) hc' hrest
          convert hstep using 1
          funext x
          simp [Finset.sum_insert hc]
    /- Every simple function lies in `𝒞`: it is the finite sum over its range of the
    scalar multiples of the indicators of its fibres. -/
    have hsimple : ∀ s : MeasureTheory.SimpleFunc X ℂ, (fun x => s x) ∈ 𝒞 := by
      intro s
      have hdecomp : ∀ x : X,
          s x = s.range.sum (fun c : ℂ => c * (s ⁻¹' {c}).indicator (1 : X → ℂ) x) := by
        intro x
        calc
          s x = s x * (s ⁻¹' {s x}).indicator (1 : X → ℂ) x := by
            have hx : x ∈ s ⁻¹' {s x} := by simp [Set.mem_preimage]
            simp [hx]
          _ = s.range.sum (fun c : ℂ => c * (s ⁻¹' {c}).indicator (1 : X → ℂ) x) := by
            exact (Finset.sum_eq_single_of_mem
              (s := s.range)
              (f := fun c : ℂ => c * (s ⁻¹' {c}).indicator (1 : X → ℂ) x)
              (s x) (s.mem_range_self x) (by
                intro b hb hbne
                have hxnot : x ∉ s ⁻¹' {b} := by
                  intro hxb
                  have hsb : s x = b := by simpa [Set.mem_preimage] using hxb
                  exact hbne hsb.symm
                simp [Set.indicator_of_notMem hxnot])).symm
      have hsummand : ∀ c ∈ s.range,
          (fun x => c * (s ⁻¹' {c}).indicator (1 : X → ℂ) x) ∈ 𝒞 := by
        intro c hc
        exact hsmul c ((s ⁻¹' {c}).indicator (1 : X → ℂ))
          (h𝒞.indicator_mem (s.measurableSet_fiber c))
      have htot := hsum_mem s.range (fun c x => c * (s ⁻¹' {c}).indicator (1 : X → ℂ) x)
        hsummand
      have heq : (fun x : X => s x) =
          fun x : X => s.range.sum (fun c : ℂ => c * (s ⁻¹' {c}).indicator (1 : X → ℂ) x) := by
        funext x
        exact hdecomp x
      rw [heq]
      exact htot
    /- Approximate `f` uniformly by simple functions. -/
    rcases exists_simpleFunc_tendstoUniformly hf with ⟨s, hs⟩
    have hs_mem : ∀ n : ℕ, (fun x : X => s n x) ∈ 𝒞 := fun n => hsimple (s n)
    /- The approximating sequence is uniformly bounded. -/
    rcases hf with ⟨_hfmeas, C, hC⟩
    let B : ℝ := max C 0
    have hB : ∀ x : X, ‖f x‖ ≤ B := fun x => le_trans (hC x) (le_max_left C 0)
    have hB0 : 0 ≤ B := le_max_right C 0
    have hε1 : ∀ᶠ n : ℕ in atTop, ∀ x : X, ‖s n x - f x‖ ≤ 1 := by
      have hd : ∀ᶠ n : ℕ in atTop, ∀ x : X, dist (s n x) (f x) < (1 : ℝ) := by
        simpa [dist_comm] using (Metric.tendstoUniformly_iff.mp hs) (1 : ℝ) (by norm_num)
      filter_upwards [hd] with n hn
      intro x
      have hlt : ‖s n x - f x‖ < 1 := by simpa [dist_eq_norm] using hn x
      exact le_of_lt hlt
    rcases Filter.eventually_atTop.mp hε1 with ⟨N, hN⟩
    let m : ℕ → ℝ := fun n => max (Classical.choose ((s n).exists_forall_norm_le)) 0
    have hm (n : ℕ) (x : X) : ‖s n x‖ ≤ m n := by
      have h := Classical.choose_spec ((s n).exists_forall_norm_le) x
      exact le_trans h (le_max_left _ 0)
    have hm_nonneg (n : ℕ) : 0 ≤ m n := le_max_right _ 0
    let M : ℝ := (B + 1) + (Finset.range N).sum m
    have hsum_nonneg : 0 ≤ (Finset.range N).sum m :=
      Finset.sum_nonneg fun n _ => hm_nonneg n
    have hM : ∀ (n : ℕ) (x : X), ‖s n x‖ ≤ M := by
      intro n x
      by_cases hn : n < N
      · have hmem : n ∈ Finset.range N := by
          simpa using hn
        have hsingle : m n ≤ (Finset.range N).sum m :=
          Finset.single_le_sum (fun i _ => hm_nonneg i) hmem
        nlinarith [hm n x, hsingle, hsum_nonneg, hB0]
      · have hnN : N ≤ n := le_of_not_gt hn
        have hbnd : ‖s n x‖ ≤ B + 1 := by
          calc
            ‖s n x‖ ≤ ‖s n x - f x‖ + ‖f x‖ := by
              calc
                ‖s n x‖ = ‖(s n x - f x) + f x‖ := by rw [sub_add_cancel]
                _ ≤ ‖s n x - f x‖ + ‖f x‖ := norm_add_le _ _
            _ ≤ 1 + B := add_le_add (hN n hnN x) (hB x)
            _ = B + 1 := by ring
        nlinarith [hbnd, hsum_nonneg]
    /- and converges to `f` pointwise, because uniform convergence is stronger. -/
    have hpt : ∀ x : X, Tendsto (fun n : ℕ => s n x) atTop (𝓝 (f x)) := by
      intro x
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hev : ∀ᶠ n : ℕ in atTop, dist (s n x) (f x) < ε := by
        filter_upwards [(Metric.tendstoUniformly_iff.mp hs) ε hε] with n hn
        simpa [dist_comm] using hn x
      rcases Filter.eventually_atTop.mp hev with ⟨N0, hN0⟩
      exact ⟨N0, hN0⟩
    exact h𝒞.tendsto_mem (fun n : ℕ => fun x : X => s n x) f M hs_mem ⟨hM, hpt⟩

end Compact

end Spectral
end Physicslib4
