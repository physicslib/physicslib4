/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Stone.Bounded
import Physicslib4.Spectral.Stone.Theorem
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positive energy of a one-parameter unitary group

The **positive-energy** (spectrum) condition for a one-parameter unitary group on a Hilbert
space: the group is strongly continuous and its infinitesimal generator is a positive
operator. By Stone's theorem the generator is then self-adjoint and `V(t) = e^{itA}`
(`isPositiveEnergy_iff_exists_exp`). This is spacetime-agnostic: it is shared by the
Minkowski (translation) and curved (Killing-flow) spectrum conditions.

## Main results

* `Physicslib4.AQFT.IsPositiveEnergy` — the positive-energy condition.
* `isPositiveEnergy_const_refl` — the trivial group has positive energy.
* `generator_eq_of_eq_expUnitary` — the generator is the unique `B` with `V(t) = e^{itB}`.
* `IsPositiveEnergy.conj` — positive energy is a unitary invariant.
* `IsPositiveEnergy.strongContinuous` — a positive-energy group is strongly continuous.
* `isPositiveEnergy_exp` — the bounded case `V(t) = exp(itP)`, `P ≥ 0`.
* `isPositiveEnergy_iff_exists_exp` — the exponential form, via Stone's theorem.

## Supporting lemmas

* `exp_generator_unique` — the bounded special case of `generator_eq_of_eq_expUnitary`:
  a bounded, self-adjoint, nonnegative generator is determined by `V(t) = exp(itP)`.
-/

namespace Physicslib4
namespace AQFT

open scoped InnerProductSpace
open Spectral.Stone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
A one-parameter unitary group has positive energy when it is strongly continuous and its
generator is a positive operator.

For a family V(t), t ∈ ℝ, of unitaries on H this asks three things: V(0) = 𝟙 and
V(s + t) = V(s)V(t); t ↦ V(t)ψ is continuous for every ψ; and the infinitesimal generator A
is positive. Here Aψ is the limit of (V(t)ψ − ψ)/(it) as t → 0, defined on the vectors ψ for
which the limit exists, and positive means symmetric with ⟨ψ, Aψ⟩ ≥ 0 for every ψ in Dom(A).
The generator is in general unbounded, and the condition is imposed on it directly. By
Stone's theorem A is then densely defined and self-adjoint and V(t) = e^(itA), so positive
energy says exactly that V(t) = e^(itA) with A positive and self-adjoint
(`isPositiveEnergy_iff_exists_exp`). For the unitaries of time translations,
U(t) = e^(itĤ) in the convention U(a) = e^(−iP·a), where P·a = −P⁰a⁰ + P⃗·a⃗ uses the
signature (−,+,+,+) and P⁰ = Ĥ (the inverse of the Schrödinger evolution e^(−itĤ)). Then A
is the Hamiltonian Ĥ, and the condition says that the energy is bounded below by 0.

This is the form in which the library states the spectrum condition. A vacuum state
(`HaagKastlerNet.IsVacuumState`) asks that t ↦ U(γ(t)) have positive energy for every
future-timelike translation subgroup γ, and a ground state for a flow
(`HaagKastlerNet.IsGroundStateForFlow`, for a flow of Poincaré transformations in Minkowski
spacetime or of isometries in curved spacetime) asks it of the unitary group implementing the
flow. The definition refers to no spacetime.

Implementation note: unitaries are `H ≃ₗᵢ[ℂ] H`, and the generator is `generator V`, an
`H →ₗ.[ℂ] H`; positivity is `Spectral.Unbounded.IsPositive`, stated as 0 ≤ Re⟨ψ, Aψ⟩. The
three conditions are the three fields, so each is available by projection.

Blueprint: def:positive-energy
-/
structure IsPositiveEnergy (V : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop where
  /-- `V` is a one-parameter unitary group. -/
  isOneParameterUnitaryGroup : IsOneParameterUnitaryGroup V
  /-- `V` is strongly continuous. -/
  isStronglyContinuous : IsStronglyContinuous V
  /-- The infinitesimal generator of `V` is a positive operator. -/
  isPositive_generator : Spectral.Unbounded.IsPositive (generator V)

omit [CompleteSpace H] in
/--
The trivial unitary group, V(t) = 𝟙 for every t, has positive energy.

Its generator is the zero operator on all of H (`generator_refl`), which is positive. This is
the simplest example of the condition, the unitary group of a theory with no dynamics.

Implementation note: the identity unitary is `LinearIsometryEquiv.refl ℂ H`. The lemma does
not need H to be complete.

Blueprint: lmm:positive-energy-const
-/
theorem isPositiveEnergy_const_refl :
    IsPositiveEnergy (fun _ : ℝ => LinearIsometryEquiv.refl ℂ H) := by
  refine ⟨isOneParameterUnitaryGroup_refl, isStronglyContinuous_refl, ?_⟩
  rw [generator_refl]
  refine ⟨fun x y => ?_, fun ψ => ?_⟩ <;> simp

/-- **Uniqueness of a bounded generator.** If two bounded operators induce the same
one-parameter unitary group — `exp(i t P) = exp(i t Q)` for all `t` — they are equal.
Differentiating at `t = 0` gives `i P = i Q`, hence `P = Q`. The unbounded form is
`generator_eq_of_eq_expUnitary`.

Blueprint reference: the bounded special case of `lmm:exp-generator-unique`. -/
theorem exp_generator_unique {P Q : H →L[ℂ] H}
    (h : ∀ (t : ℝ) (x : H),
      NormedSpace.exp (((t : ℂ) * Complex.I) • P) x
        = NormedSpace.exp (((t : ℂ) * Complex.I) • Q) x) :
    P = Q := by
  have hfun : (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • P))
      = (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • Q)) := by
    funext t; exact ContinuousLinearMap.ext (h t)
  have hderiv : ∀ R : H →L[ℂ] H,
      HasDerivAt (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • R))
        (Complex.I • R) 0 := by
    intro R
    have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • R) (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hc
    have hfeq : (fun u : ℝ => NormedSpace.exp (u • (Complex.I • R)))
        = (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • R)) := by
      funext u; rw [← Complex.coe_smul, smul_smul]
    rwa [hfeq] at hc
  have hP := hderiv P
  have hQ := hderiv Q
  rw [hfun] at hP
  have key : Complex.I • P = Complex.I • Q := hP.unique hQ
  exact smul_right_injective (H →L[ℂ] H) Complex.I_ne_zero key

/--
If V(t) = e^(itB) for every t, with B self-adjoint, then B is the generator of V.

The equality is of unbounded operators, so the domains agree as well. A unitary group therefore
determines the self-adjoint operator that exponentiates to it, and in particular the positive
self-adjoint operator in `isPositiveEnergy_iff_exists_exp` is unique. Positivity plays no role.
The proof is the statement of `generator_expUnitary` that the generator of t ↦ e^(itB) is B.

Implementation note: e^(itB) is `expUnitary hB t`, which takes the proof `hB` of
self-adjointness, and the equality V(t) = e^(itB) is in `H ≃ₗᵢ[ℂ] H`. The bounded special case
is `exp_generator_unique`.

Blueprint: lmm:exp-generator-unique
-/
theorem generator_eq_of_eq_expUnitary {V : ℝ → (H ≃ₗᵢ[ℂ] H)} {B : H →ₗ.[ℂ] H}
    (hB : IsSelfAdjoint B) (h : ∀ t, V t = expUnitary hB t) : generator V = B := by
  obtain rfl : V = expUnitary hB := funext h
  exact (generator_expUnitary hB).2.2

omit [CompleteSpace H] in
/--
If V has positive energy and W is unitary, then t ↦ W V(t) W⁻¹ has positive energy.

If A is the generator of V, the generator of the conjugated group is W A W⁻¹, with domain
W Dom(A) (`mem_generator_conj_domain_iff`, `generator_conj_apply`), and conjugation by a unitary
preserves positivity (`Spectral.Unbounded.IsPositive.of_conj`). Physically, the spectrum
condition does not depend on the choice of unitary frame: unitarily equivalent descriptions of
the same system agree on whether its energy is positive.

Implementation note: W V(t) W⁻¹ is written `(W.symm.trans (V t)).trans W`, since `trans`
composes left to right. The statement gives only the positive-energy conclusion; the form of
the generator is in the two lemmas cited above. The lemma does not need H to be complete.

Blueprint: lmm:positive-energy-conj
-/
theorem IsPositiveEnergy.conj (W : H ≃ₗᵢ[ℂ] H) {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) :
    IsPositiveEnergy (fun t => (W.symm.trans (V t)).trans W) :=
  ⟨hV.isOneParameterUnitaryGroup.conj W, hV.isStronglyContinuous.conj W,
    hV.isPositive_generator.of_conj W (mem_generator_conj_domain_iff V W)
      (generator_conj_apply V W)⟩

omit [CompleteSpace H] in
/--
A unitary group with positive energy is strongly continuous: t ↦ V(t)x is continuous for every
x in H.

Strong continuity is one of the three conditions of positive energy, so this only unpacks the
definition. It is stated separately for results on ground states that use only strong
continuity, such as `HaagKastlerNet.IsGroundStateForFlow.exists_strongContinuous_unitary`.

Implementation note: the proof is the field `isStronglyContinuous` applied to x. The lemma does
not need H to be complete.

Blueprint: lmm:positive-energy-strong-continuous
-/
theorem IsPositiveEnergy.strongContinuous {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) (x : H) : Continuous (fun t : ℝ => V t x) :=
  hV.isStronglyContinuous x

/--
If P is a bounded positive operator and V(t) = exp(itP) for every t, then V has positive energy.

Here exp(itP) is the norm-convergent power series, so no spectral theorem is needed. A bounded
positive operator is self-adjoint, so V is a one-parameter unitary group
(`exists_isOneParameterUnitaryGroup_exp`); it is strongly continuous; and its generator is P
on all of H (`generator_eq_of_eq_exp`), which is positive. An example is the group of time
translations e^(itĤ) of a Hamiltonian Ĥ with nonnegative spectrum on a finite-dimensional space.

Implementation note: the exponential is `NormedSpace.exp (((t : ℂ) * Complex.I) • P)`, the
hypothesis on V is stated vector by vector, and positivity of P is Mathlib's
`ContinuousLinearMap.IsPositive`. The unbounded form is `isPositiveEnergy_iff_exists_exp`.

Blueprint: lmm:positive-energy-exp-bounded
-/
theorem isPositiveEnergy_exp {P : H →L[ℂ] H} (hP : P.IsPositive) {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : ∀ (t : ℝ) (x : H), V t x = NormedSpace.exp (((t : ℂ) * Complex.I) • P) x) :
    IsPositiveEnergy V := by
  obtain ⟨V', hV', hgrp⟩ := exists_isOneParameterUnitaryGroup_exp hP.isSelfAdjoint
  obtain rfl : V = V' :=
    funext fun t => LinearIsometryEquiv.ext fun x => (hV t x).trans (hV' t x).symm
  exact ⟨hgrp, isStronglyContinuous_of_eq_exp hV,
    (generator_eq_of_eq_exp hV) ▸ (Spectral.Unbounded.isPositive_toPMap_iff P).mpr hP⟩

/--
A family V of unitaries has positive energy if and only if V(t) = e^(itA) for every t, for some
positive self-adjoint operator A.

This is the textbook form of the condition: for time translations, e^(itĤ), it says that the
Hamiltonian Ĥ is self-adjoint with nonnegative spectrum, here phrased as ⟨ψ, Aψ⟩ ≥ 0 on
Dom(A). The operator A may be unbounded, and e^(itA) is defined by the spectral theorem.
Forward, Stone's theorem (`stone`) makes the generator self-adjoint with V(t) = e^(itA), and it
is positive by hypothesis. Backward, the group t ↦ e^(itA) is strongly continuous with generator A
(`generator_expUnitary`). The operator A is unique (`generator_eq_of_eq_expUnitary`).

Implementation note: since `expUnitary` takes a proof of self-adjointness, the right-hand side
reads `∃ A, ∃ hA : IsSelfAdjoint A, Spectral.Unbounded.IsPositive A ∧ ∀ t, V t = expUnitary hA t`.

Blueprint: thrm:positive-energy-iff-exp
-/
theorem isPositiveEnergy_iff_exists_exp {V : ℝ → (H ≃ₗᵢ[ℂ] H)} :
    IsPositiveEnergy V ↔ ∃ (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A),
      Spectral.Unbounded.IsPositive A ∧ ∀ t, V t = expUnitary hA t := by
  refine ⟨fun hV => ?_, fun ⟨A, hA, hpos, h⟩ => ?_⟩
  · obtain ⟨hA, -, hexp, -⟩ := stone hV.isOneParameterUnitaryGroup hV.isStronglyContinuous
    exact ⟨generator V, hA, hV.isPositive_generator, hexp⟩
  · obtain rfl : V = expUnitary hA := funext h
    obtain ⟨hgrp, hc, hgen⟩ := generator_expUnitary hA
    exact ⟨hgrp, hc, hgen.symm ▸ hpos⟩

end AQFT
end Physicslib4
