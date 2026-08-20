/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.UniformRing

/-!
# Completion of a C*-normed `*`-algebra

This file completes a normed `*`-algebra satisfying the C*-inequality to a
C*-algebra. It is stated for an arbitrary such algebra; the quasilocal colimit of
`Physicslib4/AQFT/HaagKastler/QuasilocalColimit.lean` is only one instance, and
nothing here mentions the quasilocal setting.

Blueprint references: `def:completion-standing-hypotheses`, `def:completion-star`,
`lmm:star-extends-to-completion`, `lmm:completion-normed-algebra`,
`lmm:completion-cstar-identity`, `lmm:completion-of-cstar-normed-star-algebra`.

## Why this development exists

There is **no C*-completion construction anywhere in Mathlib**: no enveloping
C*-algebra, no universal C*-algebra of a `*`-algebra, no full or reduced group
C*-algebra. `Unitization` is the only C*-norm construction present and is not a
usable template, since it builds its norm from the left regular representation
rather than completing a given C*-norm.

The compensation is that each obligation is short. The recurring move is
`UniformSpace.Completion.induction_on` together with `isClosed_eq` or
`isClosed_le`, pushing the claim through `norm_coe`, `coe_mul`, `coe_add` and
`coe_smul` to the corresponding law on `A`.

## What is free and what is not

Free: the ring and norm structure on the completion (`Completion.ring`,
`Completion.algebra`, and the anonymous `NormedRing`/`NormedSpace`/
`NormedAddCommGroup` instances), `CompleteSpace`, and — once `CStarRing` is in
place — isometry of the involution, via `CStarRing.to_normedStarGroup`.

Not free, and the substance of this file:

* the **involution**. Mathlib puts no `Star`, `InvolutiveStar` or `StarRing` on
  `UniformSpace.Completion` at all, so it must be built with
  `UniformSpace.Completion.map`. Note `mapRingHom` is the *wrong* tool: `star` is
  anti-multiplicative, so it is not a ring homomorphism `A → A`.
* the **`NormedAlgebra ℂ` instance**. Mathlib's instance for a completion
  (`Analysis/Normed/Module/Completion.lean`) is gated on `SeminormedCommRing`, so
  it does **not** fire for a noncommutative C*-algebra and must be supplied here.
-/

namespace Physicslib4

open UniformSpace

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
  [StarModule ℂ A] [CStarRing A]

/-- **The standing hypotheses of this file, and the notation `Â`**
(`def:completion-standing-hypotheses`).

`CStarCompletion A` is the completion of a type `A` carrying a `NormedRing`, a
`StarRing`, a `NormedAlgebra ℂ`, a `StarModule ℂ` and a `CStarRing` structure.
Every result below is stated under exactly these five hypotheses, so this
abbreviation *is* the blueprint's standing-hypotheses node: it names the setting
and introduces the notation `Â` for the completion, whose canonical map has dense
range by `UniformSpace.Completion.denseRange_coe`.

Two remarks on the hypothesis list. No isometry hypothesis is imposed on `star`:
`‖a⋆‖ = ‖a‖` follows from the C*-inequality, since `CStarRing.to_normedStarGroup`
produces the `NormedStarGroup A` instance. And `StarModule ℂ A` and
`NormedAlgebra ℂ A` are listed because they are genuinely used and are not
consequences of the others — the former is what `star_smul` on the completion
reduces to on the dense range, and the latter is what `NormedAlgebra` needs to
complete. -/
abbrev CStarCompletion (A : Type*) [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
    [StarModule ℂ A] [CStarRing A] : Type _ :=
  UniformSpace.Completion A

/-- **The involution on a completion** (`def:completion-star`).

`star` on `A` is an isometry — not assumed, but obtained from the C*-inequality
through `CStarRing.to_normedStarGroup` — hence uniformly continuous, so
`UniformSpace.Completion.map` lifts it to the completion. -/
noncomputable instance instStarCompletion : Star (Completion A) where
  star := Completion.map star

omit [NormedAlgebra ℂ A] [StarModule ℂ A] in
/-- The involution on the completion agrees with the involution on `A` along the
canonical map. This is the characterisation every proof below runs through. -/
@[simp] theorem star_completion_coe (a : A) :
    star (a : Completion A) = ((star a : A) : Completion A) := by
  exact Completion.map_coe (Isometry.uniformContinuous (star_isometry (E := A))) a

/-- **The involution extends to the completion** (`lmm:star-extends-to-completion`),
`StarRing` half: the operation is involutive, additive and anti-multiplicative.

All the laws share one skeleton — `Completion.induction_on` plus `isClosed_eq`
plus `star_completion_coe` — and differ only in which coercion lemma and which
component law of `A` are cited at the end. -/
noncomputable instance instStarRingCompletion : StarRing (Completion A) where
  star_involutive := by
    intro x
    have h : Continuous (star : Completion A → Completion A) :=
      UniformSpace.Completion.continuous_map
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · apply isClosed_eq
      · exact h.comp h
      · exact continuous_id
    · intro a
      rw [star_completion_coe, star_completion_coe]
      simp [star_star]
  star_mul := by
    intro x y
    have h : Continuous (star : Completion A → Completion A) :=
      UniformSpace.Completion.continuous_map
    refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
    · apply isClosed_eq
      · exact h.comp (Continuous.mul continuous_fst continuous_snd)
      · exact Continuous.mul (h.comp continuous_snd) (h.comp continuous_fst)
    · intro a b
      rw [← Completion.coe_mul, star_completion_coe, star_completion_coe,
        star_completion_coe, ← Completion.coe_mul]
      rw [star_mul]
  star_add := by
    intro x y
    have h : Continuous (star : Completion A → Completion A) :=
      UniformSpace.Completion.continuous_map
    refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
    · apply isClosed_eq
      · exact h.comp (Continuous.add continuous_fst continuous_snd)
      · exact Continuous.add (h.comp continuous_fst) (h.comp continuous_snd)
    · intro a b
      rw [← Completion.coe_add, star_completion_coe, star_completion_coe,
        star_completion_coe, ← Completion.coe_add]
      rw [star_add]

/-- **The involution extends to the completion** (`lmm:star-extends-to-completion`),
`StarModule` half: conjugate-linearity `(c • x)⋆ = conj c • x⋆`.

On the dense range of the canonical map this reduces to `star_smul` in `A`, which
is exactly the `StarModule ℂ A` hypothesis. -/
noncomputable instance instStarModuleCompletion : StarModule ℂ (Completion A) where
  star_smul := by
    intro c x
    have h : Continuous (star : Completion A → Completion A) :=
      UniformSpace.Completion.continuous_map
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · apply isClosed_eq
      · exact h.comp (Continuous.const_smul continuous_id c)
      · exact Continuous.const_smul h (star c)
    · intro a
      rw [← Completion.coe_smul, star_completion_coe, star_completion_coe,
        ← Completion.coe_smul, star_smul]

/-- **The completion is a normed algebra over `ℂ`**
(`lmm:completion-normed-algebra`).

This instance exists to work around a real trap: Mathlib's `NormedAlgebra`
instance for a completion is gated on `SeminormedCommRing`, so it does not fire
for a noncommutative C*-algebra. The body is nevertheless the same as Mathlib's,
since that proof never uses commutativity — it borrows the `NormedSpace` instance
and supplies `norm_smul_le`. -/
noncomputable instance instNormedAlgebraCompletion :
    NormedAlgebra ℂ (Completion A) where
  norm_smul_le := by
    intro r x
    exact norm_smul_le r x

/-- **The C*-inequality passes to the completion**
(`lmm:completion-cstar-identity`).

`CStarRing` is a `Prop` class with the single field
`norm_mul_self_le : ∀ x, ‖x‖ * ‖x‖ ≤ ‖x⋆ * x‖`, a non-strict inequality between
continuous functions of `x`, so it transports by `isClosed_le` plus
`Completion.induction_on` in a few lines.

Two consequences worth recording: isometry of the involution on the completion is
*not* a separate obligation, since `CStarRing.to_normedStarGroup` supplies it; and
`CStarRing` itself does not require completeness. -/
instance instCStarRingCompletion : CStarRing (Completion A) where
  norm_mul_self_le := by
    intro x
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · -- closedness: {x | ‖x‖ * ‖x‖ ≤ ‖x⋆ * x‖} since both sides are continuous
      haveI : UniformContinuous (star : A → A) := star_isometry.uniformContinuous
      have hstar : Continuous (star : Completion A → Completion A) := by
        exact Completion.continuous_map
      exact isClosed_le (by fun_prop) (by fun_prop)
    · intro a
      simpa only [star_completion_coe, Completion.norm_coe, ← Completion.coe_mul] using
        (CStarRing.norm_mul_self_le a : ‖a‖ * ‖a‖ ≤ ‖star a * a‖)

/-- **The completion of a C*-normed `*`-algebra is a C*-algebra**
(`lmm:completion-of-cstar-normed-star-algebra`).

Assembly only: `CStarAlgebra` extends `NormedRing`, `StarRing`, `CompleteSpace`,
`CStarRing`, `NormedAlgebra ℂ` and `StarModule ℂ` with no additional fields, and
every parent is now in place — completeness being the ambient `CompleteSpace`
instance on a completion rather than anything to prove. -/
noncomputable instance instCStarAlgebraCompletion : CStarAlgebra (Completion A) where

/-- **The completion coercion as a bundled `*`-algebra homomorphism**
(`lmm:completion-coe-star-alg-hom`).

The canonical map `η : A → Â` is a unital `*`-algebra homomorphism over `ℂ`,
bundled as a `StarAlgHom`. This is a node rather than a citation because Mathlib
supplies the coercion only as a *ring* homomorphism,
`UniformSpace.Completion.coeRingHom`; there is no bundled `AlgHom` or `StarAlgHom`
version of the completion coercion anywhere, so the assembly must be done by hand.
The ring laws come from `coeRingHom`, the `AlgHom` scalar law `commutes'` reduces
by `rfl` from `UniformSpace.Completion.algebraMap_def`, and `map_star'` is
`star_completion_coe` in reverse. Its consumer is `lmm:quasilocal-embedding`, which
needs a bundled morphism. -/
noncomputable def coeStarAlgHom : A →⋆ₐ[ℂ] CStarCompletion A :=
  { toAlgHom :=
      { toRingHom := UniformSpace.Completion.coeRingHom
        commutes' := fun _r => rfl }
    map_star' := fun a => (star_completion_coe a).symm }

@[simp] theorem coe_coeStarAlgHom :
    ⇑(coeStarAlgHom : A →⋆ₐ[ℂ] CStarCompletion A) =
      ((↑) : A → UniformSpace.Completion A) := rfl

end Physicslib4
