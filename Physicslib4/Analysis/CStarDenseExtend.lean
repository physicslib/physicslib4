/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Algebra.Star.Subalgebra

/-!
# Extending a `*`-homomorphism from a dense `*`-subalgebra

This file proves the analytic core needed to lift fiberwise actions to a
quasilocal C*-algebra: a *uniformly continuous* `*`-homomorphism defined on a
*dense* `*`-subalgebra `S` of a C*-algebra `A`, valued in a (complete)
C*-algebra `B`, extends to a `*`-homomorphism on all of `A`.

## Main results

* `Physicslib4.exists_starAlgHom_extend_of_dense`: existence of the extension
  `F : A →⋆ₐ[ℂ] B` agreeing with `f` on `S`.

The construction uses the uniform-space extension of a uniformly continuous map
to a complete codomain (`uniformContinuous_uniformly_extend`); all algebraic
structure (`+`, `*`, `1`, `0`, `ℂ`-scaling, `star`) is transported to the
extension by continuity and agreement on the dense subalgebra.
-/

namespace Physicslib4

open Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A uniformly continuous `*`-homomorphism from a dense `*`-subalgebra `S` of a
C*-algebra `A` into a C*-algebra `B` extends to a `*`-homomorphism on all of
`A`, agreeing with the original on `S`. -/
theorem exists_starAlgHom_extend_of_dense
    (S : StarSubalgebra ℂ A) (hS : Dense (S : Set A))
    (f : S →⋆ₐ[ℂ] B) (hf : UniformContinuous (f : S → B)) :
    ∃ F : A →⋆ₐ[ℂ] B, Continuous F ∧ ∀ x : S, F (x : A) = f x := by
  have hue : IsUniformInducing ((↑) : S → A) := isUniformInducing_val (S : Set A)
  have hdr : DenseRange ((↑) : S → A) := by
    simpa only [DenseRange, Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq] using hS
  set F₀ : A → B := (hue.isDenseInducing hdr).extend (f : S → B) with hF₀def
  have hcont : Continuous F₀ :=
    (uniformContinuous_uniformly_extend hue hdr hf).continuous
  have heq : ∀ x : S, F₀ (x : A) = f x := fun x =>
    uniformly_extend_of_ind hue hdr hf x
  -- additive / multiplicative structure, by density on `S ×ˢ S`
  have hadd : ∀ x y : A, F₀ (x + y) = F₀ x + F₀ y := by
    have h : (fun p : A × A => F₀ (p.1 + p.2)) = fun p => F₀ p.1 + F₀ p.2 := by
      refine Continuous.ext_on (hS.prod hS) (hcont.comp continuous_add)
        ((hcont.comp continuous_fst).add (hcont.comp continuous_snd)) ?_
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      lift x to S using hx with a
      lift y to S using hy with b
      have hc : ((a : A) + b) = ((a + b : S) : A) := by simp
      rw [hc, heq, heq, heq]
      exact map_add f a b
    exact fun x y => congrFun h (x, y)
  have hmul : ∀ x y : A, F₀ (x * y) = F₀ x * F₀ y := by
    have h : (fun p : A × A => F₀ (p.1 * p.2)) = fun p => F₀ p.1 * F₀ p.2 := by
      refine Continuous.ext_on (hS.prod hS) (hcont.comp continuous_mul)
        ((hcont.comp continuous_fst).mul (hcont.comp continuous_snd)) ?_
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      lift x to S using hx with a
      lift y to S using hy with b
      have hc : ((a : A) * b) = ((a * b : S) : A) := by simp
      rw [hc, heq, heq, heq]
      exact map_mul f a b
    exact fun x y => congrFun h (x, y)
  have hone : F₀ 1 = 1 := by
    have hc : (1 : A) = ((1 : S) : A) := by simp
    rw [hc, heq]; exact map_one f
  have hzero : F₀ 0 = 0 := by
    have hc : (0 : A) = ((0 : S) : A) := by simp
    rw [hc, heq]; exact map_zero f
  have hsmul : ∀ (c : ℂ) (x : A), F₀ (c • x) = c • F₀ x := by
    intro c
    have h : (fun x : A => F₀ (c • x)) = fun x => c • F₀ x := by
      refine Continuous.ext_on hS (hcont.comp (continuous_const_smul c))
        ((continuous_const_smul c).comp hcont) ?_
      intro x hx
      lift x to S using hx with a
      have hc : (c • (a : A)) = ((c • a : S) : A) := by simp
      rw [hc, heq, heq]
      exact map_smul f c a
    exact fun x => congrFun h x
  have hstar : ∀ x : A, F₀ (star x) = star (F₀ x) := by
    have h : (fun x : A => F₀ (star x)) = fun x => star (F₀ x) := by
      refine Continuous.ext_on hS (hcont.comp continuous_star)
        (continuous_star.comp hcont) ?_
      intro x hx
      lift x to S using hx with a
      have hc : (star (a : A)) = ((star a : S) : A) := by simp
      rw [hc, heq, heq]
      exact map_star f a
    exact fun x => congrFun h x
  -- bundle into a `StarAlgHom`
  let Fring : A →+* B :=
    { toFun := F₀
      map_one' := hone
      map_mul' := hmul
      map_zero' := hzero
      map_add' := hadd }
  refine ⟨{ AlgHom.mk' Fring hsmul with map_star' := hstar }, hcont, fun x => heq x⟩

end Physicslib4
