/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Analysis.HorizontalLineRemovable
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Vanishing on an edge

A function continuous on the closed upper half-plane, holomorphic on the open upper half-plane,
and zero on a nonempty open interval of the real axis vanishes identically
(`eq_zero_of_eq_zero_on_Ioo`). The proof reflects the function across the interval: the
reflected function g(z) = f(z) for Im z ≥ 0 and g(z) = conj(f(conj z)) for Im z < 0 is
holomorphic on the reflection domain D = {Im z ≠ 0} ∪ I, which is open and connected, and the
identity theorem applies there. This is the uniqueness step of the Reeh–Schlieder theorem.

## Main results

* `isOpen_im_ne_zero_union_image_ofReal` — the reflection domain is open.
* `isConnected_im_ne_zero_union_image_ofReal` — the reflection domain is connected.
* `continuousOn_schwarzReflection_of_eq_zero` — the reflected function is continuous on it.
* `differentiableOn_schwarzReflection_of_eq_zero` — the reflected function is holomorphic on it.
* `eq_zero_of_eq_zero_on_Ioo` — vanishing on an edge.

Throughout, I is a set `I : Set ℝ`. Openness and holomorphy of the reflection need only
`IsOpen I`; continuity needs only that f vanishes on I, and connectedness only that I is
nonempty. The blueprint's open interval is a special case of each. The reflection domain is
written `{z : ℂ | z.im ≠ 0} ∪ Complex.ofReal '' I`, and the
reflected function is written inline as `fun z => if 0 ≤ z.im then f z else conj (f (conj z))`.
-/

namespace Physicslib4

open Complex ComplexConjugate

/--
For an open set I ⊆ ℝ, the reflection domain D = {Im z ≠ 0} ∪ I is open in ℂ.

Its complement is ℝ \ I, which is closed in ℝ and therefore in ℂ.

Implementation note: the blueprint's open interval I is a special case of the open set here.

Blueprint: lmm:reflection-domain-open
-/
theorem isOpen_im_ne_zero_union_image_ofReal {I : Set ℝ} (hI : IsOpen I) :
    IsOpen ({z : ℂ | z.im ≠ 0} ∪ Complex.ofReal '' I) := by
  have h : {z : ℂ | z.im ≠ 0} ∪ Complex.ofReal '' I = (Complex.ofReal '' Iᶜ)ᶜ := by
    ext z
    by_cases hz : z.im = 0
    · have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [hz])
      rw [hz']
      simp [Complex.ofReal_injective.eq_iff]
    · simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image]
      exact ⟨fun _ ⟨x, _, hx⟩ => hz (hx ▸ Complex.ofReal_im x), fun _ => Or.inl hz⟩
  rw [h]
  exact (Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ hI.isClosed_compl).isOpen_compl

/--
For a nonempty set I ⊆ ℝ, the reflection domain D = {Im z ≠ 0} ∪ I is connected.

D is the union of {Im z > 0} ∪ I and {Im z < 0} ∪ I. Each lies between an open half-plane and its
closure, hence is preconnected, and the two share the nonempty set I.

Implementation note: the blueprint's nonempty open interval I is a special case; connectedness is
Mathlib's `IsConnected`, which includes nonemptiness.

Blueprint: lmm:reflection-domain-connected
-/
theorem isConnected_im_ne_zero_union_image_ofReal {I : Set ℝ} (hne : I.Nonempty) :
    IsConnected ({z : ℂ | z.im ≠ 0} ∪ Complex.ofReal '' I) := by
  obtain ⟨x, hx⟩ := hne
  have hxI : (x : ℂ) ∈ Complex.ofReal '' I := ⟨x, hx, rfl⟩
  have hup : IsPreconnected ({z : ℂ | 0 < z.im} ∪ Complex.ofReal '' I) :=
    (convex_halfSpace_im_gt 0).isPreconnected.subset_closure Set.subset_union_left <| by
      rw [closure_setOfPred_lt_im]
      rintro z (hz | ⟨r, -, rfl⟩) <;> simp_all [le_of_lt]
  have hlo : IsPreconnected ({z : ℂ | z.im < 0} ∪ Complex.ofReal '' I) :=
    (convex_halfSpace_im_lt 0).isPreconnected.subset_closure Set.subset_union_left <| by
      rw [closure_setOfPred_im_lt]
      rintro z (hz | ⟨r, -, rfl⟩) <;> simp_all [le_of_lt]
  have heq : {z : ℂ | z.im ≠ 0} ∪ Complex.ofReal '' I =
      ({z : ℂ | 0 < z.im} ∪ Complex.ofReal '' I) ∪ ({z : ℂ | z.im < 0} ∪ Complex.ofReal '' I) := by
    ext z; simp only [Set.mem_union, Set.mem_ofPred_eq, ne_iff_lt_or_gt]; tauto
  rw [heq]
  exact ⟨⟨x, Or.inl (Or.inr hxI)⟩, hup.union (x : ℂ) (Or.inr hxI) (Or.inr hxI) hlo⟩

/--
If f is continuous on the closed upper half-plane and zero on a set I ⊆ ℝ, the
reflected function g, equal to f on {Im z ≥ 0} and to z ↦ conj(f(conj z)) on {Im z < 0}, is
continuous on the reflection domain D = {Im z ≠ 0} ∪ I.

On D ∩ {Im z ≥ 0} the function g is f, and on D ∩ {Im z ≤ 0} it agrees with the continuous
function z ↦ conj(f(conj z)), since both vanish on I; the two pieces are relatively closed and
cover D.

Implementation note: the blueprint's open interval I is a special case of the set here.

Blueprint: lmm:schwarz-reflection-continuous
-/
theorem continuousOn_schwarzReflection_of_eq_zero {f : ℂ → ℂ} {I : Set ℝ}
    (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hzero : ∀ x ∈ I, f x = 0) :
    ContinuousOn (fun z : ℂ => if 0 ≤ z.im then f z else conj (f (conj z)))
      ({z : ℂ | z.im ≠ 0} ∪ Complex.ofReal '' I) := by
  refine ContinuousOn.if (fun z ⟨hz, hzf⟩ => ?_) ?_ ?_
  · rw [Complex.frontier_setOfPred_le_im, Set.mem_ofPred_eq] at hzf
    obtain ⟨x, hx, rfl⟩ := hz.resolve_left (not_not.2 hzf)
    simp [hzero x hx]
  · exact hf.mono fun z hz =>
      (isClosed_le continuous_const Complex.continuous_im).closure_subset hz.2
  · refine (Complex.continuous_conj.comp_continuousOn
      (hf.comp Complex.continuous_conj.continuousOn fun z hz => ?_)).mono fun z hz => hz.2
    simp only [not_le, Complex.closure_setOfPred_im_lt, Set.mem_ofPred_eq] at hz ⊢
    simpa using hz

/--
**Schwarz reflection across a zero interval.** If f is continuous on the closed upper
half-plane, holomorphic on the open upper half-plane, and zero on an open set I ⊆ ℝ, the
reflected function g, equal to f on {Im z ≥ 0} and to z ↦ conj(f(conj z)) on {Im z < 0}, is
holomorphic on the reflection domain D = {Im z ≠ 0} ∪ I.

Off the real axis g is holomorphic, being f or the conjugate reflection of f. It is continuous
on the open set D (`continuousOn_schwarzReflection_of_eq_zero`,
`isOpen_im_ne_zero_union_image_ofReal`), so the horizontal line Im z = 0 is removable
(`differentiableOn_of_continuousOn_off_horizontal_line`).

Implementation note: the blueprint's open interval I is a special case of the open set here.

Blueprint: lmm:schwarz-reflection-zero
-/
theorem differentiableOn_schwarzReflection_of_eq_zero {f : ℂ → ℂ} {I : Set ℝ}
    (hI : IsOpen I) (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hf' : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (hzero : ∀ x ∈ I, f x = 0) :
    DifferentiableOn ℂ (fun z : ℂ => if 0 ≤ z.im then f z else conj (f (conj z)))
      ({z : ℂ | z.im ≠ 0} ∪ Complex.ofReal '' I) := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  refine differentiableOn_of_continuousOn_off_horizontal_line
    (isOpen_im_ne_zero_union_image_ofReal hI) 0 _
    (continuousOn_schwarzReflection_of_eq_zero hf hzero) fun z hz => ?_
  refine DifferentiableAt.differentiableWithinAt ?_
  rcases (show z.im ≠ 0 from hz.2).lt_or_gt with h | h
  · have hc := DifferentiableAt.conj_conj
      (hf'.differentiableAt (hU.mem_nhds (show 0 < (conj z).im by simpa using h)))
    rw [Complex.conj_conj] at hc
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds h] with w hw
    simp [not_le.2 hw]
  · refine (hf'.differentiableAt (hU.mem_nhds h)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds h] with w hw
    simp [hw.le]

/--
**Vanishing on an edge.** A function continuous on the closed upper half-plane, holomorphic on
the open upper half-plane, and zero on a nonempty open interval (a, b) of the real axis vanishes
on the whole closed upper half-plane.

The reflected function of `differentiableOn_schwarzReflection_of_eq_zero` is analytic on the
open connected reflection domain and vanishes on (a, b), so it vanishes on the domain by the
identity theorem; continuity extends the vanishing of f to the real axis.

Blueprint: lmm:edge-vanishing
-/
theorem eq_zero_of_eq_zero_on_Ioo {f : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im}) (hf' : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hzero : ∀ x ∈ Set.Ioo a b, f x = 0) :
    ∀ z : ℂ, 0 ≤ z.im → f z = 0 := by
  set g : ℂ → ℂ := fun z => if 0 ≤ z.im then f z else conj (f (conj z))
  set m : ℝ := (a + b) / 2
  have hm : m ∈ Set.Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hD := isOpen_im_ne_zero_union_image_ofReal (isOpen_Ioo (a := a) (b := b))
  have hfr : ∃ᶠ z in nhdsWithin (m : ℂ) {(m : ℂ)}ᶜ, g z = 0 := by
    have ht : Filter.Tendsto Complex.ofReal (nhdsWithin m {m}ᶜ) (nhdsWithin (m : ℂ) {(m : ℂ)}ᶜ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.tendsto' _ _ rfl |>.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun x hx => by simpa using hx)
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Ioo_mem_nhds hm.1 hm.2)] with x hx
    simp [g, hzero x hx]
  have hgz := ((differentiableOn_schwarzReflection_of_eq_zero isOpen_Ioo hf hf'
    hzero).analyticOnNhd hD).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isConnected_im_ne_zero_union_image_ofReal ⟨m, hm⟩).isPreconnected (Or.inr ⟨m, hm, rfl⟩) hfr
  have hpos : Set.EqOn f 0 {z : ℂ | 0 < z.im} := fun z (hz : 0 < z.im) => by
    simpa [g, hz.le] using hgz (Or.inl (ne_of_gt hz))
  intro z hz
  refine Set.EqOn.of_subset_closure hpos hf continuousOn_const
    (fun w (hw : 0 < w.im) => hw.le) ?_ hz
  rw [closure_setOfPred_lt_im]

end Physicslib4
