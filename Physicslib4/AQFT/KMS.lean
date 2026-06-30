/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Basic
import Physicslib4.GNS.ExtremeState
import Physicslib4.Analysis.StripPeriodicExtension
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Liouville

/-!
# The KMS (analyticity) condition for a one-parameter automorphism group

This file defines the Kubo-Martin-Schwinger (KMS) condition for a state on a
unital C*-algebra `A` with respect to a one-parameter group of `*`-automorphisms
`α : ℝ → (A ≃⋆ₐ[ℂ] A)`. The KMS condition is the algebraic characterization of
thermal equilibrium; crucially, it is phrased purely as an *analyticity*
statement about correlation functions and so needs no unbounded-operator theory
(no Stone theorem, no spectral measures).

## Main definitions

* `Physicslib4.AQFT.kmsStrip`, `kmsStripInterior`: the closed/open horizontal
  strip `0 ≤ Im z ≤ β` (resp. `0 < Im z < β`) in `ℂ`.
* `Physicslib4.AQFT.IsOneParameterAut`: the predicate that `α` is a one-parameter
  group of automorphisms (`α 0 = id`, `α (s+t) = α s ∘ α t`).
* `Physicslib4.AQFT.IsKMSState`: a state `ω` is `(α, β)`-KMS if for every
  `a, b ∈ A` the function `t ↦ ω(a · α_t b)` is the boundary value of a function
  holomorphic on the open strip and continuous on its closure, whose other
  boundary value is `t ↦ ω(α_t b · a)`.

## Notes

This is the analytic form of the KMS condition (Bratteli-Robinson): at inverse
temperature `β > 0`, `ω` is KMS iff for all `a, b` there is `F` continuous on the
strip `{0 ≤ Im z ≤ β}`, holomorphic in the interior, with `F(t) = ω(a α_t b)`
and `F(t + iβ) = ω(α_t b · a)`. KMS states are automatically `α`-invariant; that
and other consequences are left for later development.
-/

namespace Physicslib4
namespace AQFT

open Physicslib4.GNS

variable {A : Type*} [CStarAlgebra A]

/-- The closed KMS strip `{z : ℂ | 0 ≤ Im z ≤ β}`. -/
def kmsStrip (β : ℝ) : Set ℂ := {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}

/-- The open KMS strip `{z : ℂ | 0 < Im z < β}` (the interior of `kmsStrip β`). -/
def kmsStripInterior (β : ℝ) : Set ℂ := {z : ℂ | 0 < z.im ∧ z.im < β}

/-- A family `α : ℝ → (A ≃⋆ₐ[ℂ] A)` is a *one-parameter group of automorphisms*
if it sends `0` to the identity and is additive in the parameter:
`α 0 = id` and `α (s + t) = α s ∘ α t`. -/
def IsOneParameterAut (α : ℝ → (A ≃⋆ₐ[ℂ] A)) : Prop :=
  (∀ a : A, α 0 a = a) ∧ (∀ (s t : ℝ) (a : A), α (s + t) a = α s (α t a))

/-- **The KMS condition.** A state `ω` on `A` is `(α, β)`-KMS for a one-parameter
automorphism group `α` at inverse temperature `β` if, for every `a, b : A`, the
correlation function `t ↦ ω(a · α_t b)` extends to a function `F` on the closed
strip `0 ≤ Im z ≤ β` that is continuous there, holomorphic on the open strip,
and whose boundary value on `Im z = β` is `t ↦ ω(α_t b · a)`. -/
def IsKMSState (α : ℝ → (A ≃⋆ₐ[ℂ] A)) (β : ℝ) (ω : State A) : Prop :=
  ∀ a b : A, ∃ F : ℂ → ℂ,
    ContinuousOn F (kmsStrip β) ∧
    DifferentiableOn ℂ F (kmsStripInterior β) ∧
    (∃ C : ℝ, ∀ z ∈ kmsStrip β, ‖F z‖ ≤ C) ∧
    (∀ t : ℝ, F (t : ℂ) = (ω (a * α t b) : ℂ)) ∧
    (∀ t : ℝ, F ((t : ℂ) + (β : ℂ) * Complex.I) = (ω (α t b * a) : ℂ))

/-- **The strip-Liouville principle.** A function `F` that is continuous and
bounded on the closed strip `0 ≤ Im z ≤ β`, holomorphic on the open strip, and
has equal boundary values `F(t) = F(t + iβ)` for all real `t`, is constant along
the real axis: `F(t) = F(0)`.

Mathematically this is a standard consequence of the Schwarz reflection
principle (the equal boundary values let `F` extend to an `iβ`-periodic entire
function, bounded, hence constant by Liouville). Mathlib provides Liouville
(`Differentiable.apply_eq_apply_of_bounded`) and Phragmén-Lindelöf for strips,
but not the holomorphic gluing across a line that the periodic extension needs,
so this principle is isolated here as an explicit hypothesis rather than proved.
-/
def StripLiouville (β : ℝ) : Prop :=
  ∀ F : ℂ → ℂ, ContinuousOn F (kmsStrip β) → DifferentiableOn ℂ F (kmsStripInterior β) →
    (∃ C : ℝ, ∀ z ∈ kmsStrip β, ‖F z‖ ≤ C) →
    (∀ t : ℝ, F (t : ℂ) = F ((t : ℂ) + (β : ℂ) * Complex.I)) →
    ∀ t : ℝ, F (t : ℂ) = F 0

/-- **Liouville endgame for the strip-Liouville principle.** A function `F` is
constant along the real axis as soon as it admits a *bounded entire extension*
`H` agreeing with it on `ℝ`. This is the Liouville half of the strip-Liouville
principle, fully discharged: a bounded entire function is constant
(`Differentiable.apply_eq_apply_of_bounded`), so `F t = H t = H 0 = F 0`.

It isolates the other half of `StripLiouville` - the *construction* of the
bounded entire extension `H` from the periodic boundary values - which is the
horizontal-line Schwarz reflection. Mathlib does not package that reflection,
so it is built in `StripPeriodicExtension.lean`
(`exists_bounded_entire_extension_of_strip_periodic`); together with this
endgame it discharges `StripLiouville` for `β > 0` (`stripLiouville_of_pos`). -/
theorem stripLiouville_of_entire_extension {F : ℂ → ℂ}
    (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hbdd : Bornology.IsBounded (Set.range H))
    (hagree : ∀ t : ℝ, H (t : ℂ) = F (t : ℂ)) :
    ∀ t : ℝ, F (t : ℂ) = F 0 := by
  intro t
  have h0 : H 0 = F 0 := by have := hagree 0; rwa [Complex.ofReal_zero] at this
  have hconst : H (t : ℂ) = H 0 := hH.apply_eq_apply_of_bounded hbdd _ _
  rw [← hagree t, hconst, h0]

/-- **The strip-Liouville principle holds for `β > 0`.** This discharges the
`StripLiouville β` hypothesis unconditionally for positive inverse temperature:
the equal boundary values let `F` extend to a bounded `iβ`-periodic *entire*
function (`Physicslib4.exists_bounded_entire_extension_of_strip_periodic`, the
horizontal-line Schwarz reflection), which is then constant on `ℝ` by the
Liouville endgame `stripLiouville_of_entire_extension`. -/
theorem stripLiouville_of_pos {β : ℝ} (hβ : 0 < β) : StripLiouville β := by
  intro F hcont hdiff hbdd hper t
  obtain ⟨H, hHdiff, hHbdd, hHagree⟩ :=
    Physicslib4.exists_bounded_entire_extension_of_strip_periodic hβ hcont hdiff hper hbdd
  exact stripLiouville_of_entire_extension H hHdiff hHbdd hHagree t

/-- **The KMS state set is convex.** A convex combination `s·ω₁ + (1-s)·ω₂`
(`0 ≤ s ≤ 1`) of two `(α, β)`-KMS states is again `(α, β)`-KMS: for each pair
`(a, b)` the analytic interpolant is the corresponding convex combination
`s·F₁ + (1-s)·F₂` of the two interpolants, which is continuous, bounded, and
holomorphic on the strip, and whose boundary values add. Physically the
equilibrium (KMS) states at fixed temperature form a convex set. -/
theorem IsKMSState.convexCombo {α : ℝ → (A ≃⋆ₐ[ℂ] A)} {β : ℝ} {ω₁ ω₂ : State A}
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h₁ : IsKMSState α β ω₁) (h₂ : IsKMSState α β ω₂) :
    IsKMSState α β (ω₁.convexCombo ω₂ s hs0 hs1) := by
  intro a b
  obtain ⟨F₁, hF1c, hF1d, ⟨C₁, hC1⟩, hF1lo, hF1hi⟩ := h₁ a b
  obtain ⟨F₂, hF2c, hF2d, ⟨C₂, hC2⟩, hF2lo, hF2hi⟩ := h₂ a b
  refine ⟨fun z => (s : ℂ) * F₁ z + ((1 - s : ℝ) : ℂ) * F₂ z, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuousOn_const.mul hF1c).add (continuousOn_const.mul hF2c)
  · exact (hF1d.const_mul _).add (hF2d.const_mul _)
  · refine ⟨‖(s : ℂ)‖ * C₁ + ‖((1 - s : ℝ) : ℂ)‖ * C₂, fun z hz => ?_⟩
    calc ‖(s : ℂ) * F₁ z + ((1 - s : ℝ) : ℂ) * F₂ z‖
        ≤ ‖(s : ℂ) * F₁ z‖ + ‖((1 - s : ℝ) : ℂ) * F₂ z‖ := norm_add_le _ _
      _ = ‖(s : ℂ)‖ * ‖F₁ z‖ + ‖((1 - s : ℝ) : ℂ)‖ * ‖F₂ z‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖(s : ℂ)‖ * C₁ + ‖((1 - s : ℝ) : ℂ)‖ * C₂ := by
          gcongr
          · exact hC1 z hz
          · exact hC2 z hz
  · intro t
    simp only [State.convexCombo_apply]
    rw [hF1lo t, hF2lo t]
  · intro t
    simp only [State.convexCombo_apply]
    rw [hF1hi t, hF2hi t]

/-- **Boundary coincidence for the diagonal `a = 1`.** For a KMS state, the
correlation function of the pair `(1, a)` has its two boundary values *equal* -
both are `t ↦ ω(α_t a)`. This is the algebraic heart of the invariance argument
(it follows directly from the KMS condition with `a := 1`). -/
theorem IsKMSState.correlationOne {α : ℝ → (A ≃⋆ₐ[ℂ] A)} {β : ℝ} {ω : State A}
    (h : IsKMSState α β ω) (a : A) :
    ∃ F : ℂ → ℂ,
      ContinuousOn F (kmsStrip β) ∧
      DifferentiableOn ℂ F (kmsStripInterior β) ∧
      (∃ C : ℝ, ∀ z ∈ kmsStrip β, ‖F z‖ ≤ C) ∧
      (∀ t : ℝ, F (t : ℂ) = (ω (α t a) : ℂ)) ∧
      (∀ t : ℝ, F ((t : ℂ) + (β : ℂ) * Complex.I) = (ω (α t a) : ℂ)) := by
  obtain ⟨F, hcont, hdiff, hbdd, hbot, htop⟩ := h 1 a
  refine ⟨F, hcont, hdiff, hbdd, fun t => ?_, fun t => ?_⟩
  · rw [hbot t, one_mul]
  · rw [htop t, mul_one]

/-- **Uniqueness of the KMS correlation function.** For `β > 0`, any two functions
satisfying the KMS analytic data for the same pair `(a, b)` - continuous and
bounded on the strip, holomorphic on the interior, with the prescribed boundary
values `t ↦ ω(a · α_t b)` and `t ↦ ω(α_t b · a)` - agree on the whole strip. The
analytic completion in the KMS condition is therefore unique.

The proof is the strip machinery: the difference of two such functions has
vanishing boundary values, so it vanishes on the strip by the `iβ`-periodic
extension plus Liouville (`eqOn_strip_of_eq_boundary`). The hypothesis `β > 0`
is the same one that makes the extension entire. -/
theorem IsKMSState.correlation_eqOn {α : ℝ → (A ≃⋆ₐ[ℂ] A)} {β : ℝ} {ω : State A}
    (hβ : 0 < β) {a b : A} {F G : ℂ → ℂ}
    (hFc : ContinuousOn F (kmsStrip β)) (hFd : DifferentiableOn ℂ F (kmsStripInterior β))
    (hFb : ∃ C : ℝ, ∀ z ∈ kmsStrip β, ‖F z‖ ≤ C)
    (hFbot : ∀ t : ℝ, F (t : ℂ) = (ω (a * α t b) : ℂ))
    (hFtop : ∀ t : ℝ, F ((t : ℂ) + (β : ℂ) * Complex.I) = (ω (α t b * a) : ℂ))
    (hGc : ContinuousOn G (kmsStrip β)) (hGd : DifferentiableOn ℂ G (kmsStripInterior β))
    (hGb : ∃ C : ℝ, ∀ z ∈ kmsStrip β, ‖G z‖ ≤ C)
    (hGbot : ∀ t : ℝ, G (t : ℂ) = (ω (a * α t b) : ℂ))
    (hGtop : ∀ t : ℝ, G ((t : ℂ) + (β : ℂ) * Complex.I) = (ω (α t b * a) : ℂ))
    {z : ℂ} (hz0 : 0 ≤ z.im) (hzβ : z.im ≤ β) : F z = G z :=
  Physicslib4.eqOn_strip_of_eq_boundary hβ hFc hFd hFb hGc hGd hGb
    (fun t => by rw [hFbot t, hGbot t]) (fun t => by rw [hFtop t, hGtop t]) hz0 hzβ

/-- **A KMS state is invariant under its one-parameter automorphism group.**
Given the strip-Liouville principle (`StripLiouville β`, the standard analytic
fact isolated above), every `(α, β)`-KMS state `ω` is `α`-invariant:
`ω(α_t a) = ω(a)` for all `t` and `a`.

The proof: by `correlationOne`, the correlation function `F` of `(1, a)` has
equal boundary values `F(t) = F(t+iβ) = ω(α_t a)`; the strip-Liouville principle
forces `F(t) = F(0)`, and `F(0) = ω(α_0 a) = ω(a)`. -/
theorem IsKMSState.invariant {α : ℝ → (A ≃⋆ₐ[ℂ] A)} {β : ℝ} {ω : State A}
    (h : IsKMSState α β ω) (hα : IsOneParameterAut α) (hSL : StripLiouville β)
    (a : A) (t : ℝ) :
    (ω (α t a) : ℂ) = (ω a : ℂ) := by
  obtain ⟨F, hcont, hdiff, hbdd, hbot, htop⟩ := h.correlationOne a
  have hper : ∀ s : ℝ, F (s : ℂ) = F ((s : ℂ) + (β : ℂ) * Complex.I) := fun s => by
    rw [hbot s, htop s]
  have hconst : ∀ s : ℝ, F (s : ℂ) = F 0 := hSL F hcont hdiff hbdd hper
  have h0 : F (0 : ℂ) = (ω (α 0 a) : ℂ) := by
    have := hbot 0; rwa [Complex.ofReal_zero] at this
  calc (ω (α t a) : ℂ) = F (t : ℂ) := (hbot t).symm
    _ = F 0 := hconst t
    _ = (ω (α 0 a) : ℂ) := h0
    _ = (ω a : ℂ) := by rw [hα.1 a]

/-- **A KMS state at positive inverse temperature is `α`-invariant**, with no
external analytic hypothesis: the strip-Liouville principle is now a theorem
(`stripLiouville_of_pos`) for `β > 0`. -/
theorem IsKMSState.invariant_of_pos {α : ℝ → (A ≃⋆ₐ[ℂ] A)} {β : ℝ} {ω : State A}
    (h : IsKMSState α β ω) (hα : IsOneParameterAut α) (hβ : 0 < β) (a : A) (t : ℝ) :
    (ω (α t a) : ℂ) = (ω a : ℂ) :=
  h.invariant hα (stripLiouville_of_pos hβ) a t

end AQFT
end Physicslib4
