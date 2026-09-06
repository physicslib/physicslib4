/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Physicslib4.Spectral.SpectralTheorem
import Physicslib4.Spectral.Unbounded.Integral

/-!
# Bounded normal operators

The Cayley transform turns an unbounded self-adjoint operator into a bounded operator
that is normal but not self-adjoint, so the spectral theorem is needed for bounded
*normal* operators. This file carries out the first stage: the continuous functional
calculus for a bounded normal operator, built through a two-variable spectral mapping
theorem for polynomials in `A` and `A*`.

A normal operator is Mathlib's `IsStarNormal`. A polynomial in two variables is an
`MvPolynomial (Fin 2) ℂ`; substituting `A` for the first variable and `A*` for the second
is `mvApply`, defined coefficientwise (so no commutativity of the target algebra is
required), and the corresponding scalar function `λ ↦ p(λ, conj λ)` is `mvEvalConj`.

## Main definitions

* `mvApply`, `mvEvalConj`, `mvPolyOn` — polynomials in `A` and `A*`.
* `spectralSubspace` — the range of a spectral projection.
* `IsAlmostEigenvector` — the blueprint's `ε`-almost eigenvector.
* `normalCalculus` — the continuous functional calculus of a normal operator.

## Main statements

* `tendsto_norm_pow_div_atTop`, `spectralRadius_mul_le_of_commute` — power growth and the
  spectral radius of a commuting product.
* `mapsTo_pvmOperator_spectralSubspace`, `norm_sub_smul_le_of_mem_spectralSubspace`,
  `spectralSubspace_ne_bot` — properties of spectral subspaces.
* `commute_borelCalculus`, `mapsTo_spectralSubspace_of_commute` — commuting operators
  preserve spectral subspaces.
* `norm_adjoint_sub_smul_apply`, `isAlmostEigenvector_adjoint`,
  `mem_spectrum_iff_forall_isAlmostEigenvector` — almost eigenvectors.
* `spectrum_mvApply` — the two-variable spectral mapping theorem.
* `norm_mvApply` — the norm of a polynomial in `A` and `A*`.
* `existsUnique_normalCalculus` and the property lemmas — the continuous functional
  calculus for a normal operator.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### Polynomials in `A` and `A*`
-/

/--
Substitution of `A` for `λ` and `A*` for `conj λ` in a two-variable polynomial. It is
defined coefficientwise, so it needs no commutativity in `𝓑(H)`; the point of normality
is that this assignment is then multiplicative, which is
`normalCalculus_mul` below.

Blueprint reference: the substitution `p ↦ p(A, A*)` of `lmm:polynomials-in-normal-are-normal`.
-/
noncomputable def mvApply (A : H →L[ℂ] H) (p : MvPolynomial (Fin 2) ℂ) : H →L[ℂ] H :=
  ∑ d ∈ p.support, MvPolynomial.coeff d p • (A ^ d 0 * (ContinuousLinearMap.adjoint A) ^ d 1)

/--
The scalar function `λ ↦ p(λ, conj λ)` attached to a two-variable polynomial.
-/
noncomputable def mvEvalConj (p : MvPolynomial (Fin 2) ℂ) (lam : ℂ) : ℂ :=
  ∑ d ∈ p.support, MvPolynomial.coeff d p * lam ^ d 0 * (starRingEnd ℂ lam) ^ d 1

/-!
### Norm and spectral radius
-/

/--
Powers of a bounded operator grow no faster than the spectral radius allows: if
`R(A) < T` then `‖Aᵐ‖ / Tᵐ → 0`.

The blueprint's standing hypothesis `H ≠ {0}`, needed there for `σ(A)` to be non-empty and
hence `R(A)` to be a supremum over a non-empty set, is `Nontrivial H`.

Blueprint reference: `lmm:power-growth-controlled-by-spectral-radius`.
-/
theorem tendsto_norm_pow_div_atTop [Nontrivial H] (A : H →L[ℂ] H) {T : ℝ} (hT : 0 < T)
    (hRT : spectralRadius ℂ A < ENNReal.ofReal T) :
    Tendsto (fun m : ℕ => ‖A ^ m‖ / T ^ m) atTop (𝓝 0) := by
  sorry

/--
The spectral radius is submultiplicative on commuting operators.

Blueprint reference: `lmm:hall-10.22`.
-/
theorem spectralRadius_mul_le_of_commute [Nontrivial H] {A B : H →L[ℂ] H} (h : Commute A B) :
    spectralRadius ℂ (A * B) ≤ spectralRadius ℂ A * spectralRadius ℂ B := by
  sorry

/-!
### Spectral subspaces
-/

section SpectralSubspace

variable {X : Type*} [MeasurableSpace X]

/--
The spectral subspace attached to a measurable set `E` by a projection-valued measure: the
range of the projection `μ E`. It is a closed subspace of `H`
(`isClosed_range_of_isStarProjection`), hence itself a Hilbert space.

Blueprint reference: `def:hall-7.14`.
-/
def spectralSubspace (μ : ProjectionValuedMeasure X H) (E : Set X) : Submodule ℂ H :=
  LinearMap.range ((μ E : H →L[ℂ] H) : H →ₗ[ℂ] H)

end SpectralSubspace

/--
The bounded operator `∫ ι dμ` attached to a projection-valued measure on a compact subset
`Y ⊆ ℂ`, where `ι` is the inclusion `Y ↪ ℂ`.

Blueprint reference: `prpstn:hall-7.15`.
-/
noncomputable def pvmOperator {Y : Set ℂ} (μ : ProjectionValuedMeasure Y H) : H →L[ℂ] H :=
  μ.integral fun y : Y => (y : ℂ)

/--
Each spectral subspace is invariant under `∫ ι dμ`.

Blueprint reference: `prpstn:hall-7.15` (Part 1).
-/
theorem mapsTo_pvmOperator_spectralSubspace {Y : Set ℂ} (hY : IsCompact Y)
    (μ : ProjectionValuedMeasure Y H) (E : Set Y) (ψ : H) (hψ : ψ ∈ spectralSubspace μ E) :
    pvmOperator μ ψ ∈ spectralSubspace μ E := by
  sorry

/--
If `E` sits in the closed `ε`-disc about `λ₀`, then `‖(A - λ₀ 1) ψ‖ ≤ ε ‖ψ‖` on the
corresponding spectral subspace.

Blueprint reference: `prpstn:hall-7.15` (Part 2).
-/
theorem norm_sub_smul_le_of_mem_spectralSubspace {Y : Set ℂ} (hY : IsCompact Y)
    (μ : ProjectionValuedMeasure Y H) {E : Set Y} {lam₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hE : ∀ y ∈ E, ‖(y : ℂ) - lam₀‖ ≤ ε) {ψ : H} (hψ : ψ ∈ spectralSubspace μ E) :
    ‖(pvmOperator μ - lam₀ • (1 : H →L[ℂ] H)) ψ‖ ≤ ε * ‖ψ‖ := by
  sorry

/--
Spectral subspaces attached to neighbourhoods of a spectral point are non-trivial.

Blueprint reference: `prpstn:hall-7.15` (Part 3).
-/
theorem spectralSubspace_ne_bot {Y : Set ℂ} (hY : IsCompact Y)
    (μ : ProjectionValuedMeasure Y H) {lam₀ : ℂ} (hlam : lam₀ ∈ spectrum ℂ (pvmOperator μ))
    {U : Set ℂ} (hU : IsOpen U) (hlamU : lam₀ ∈ U) :
    spectralSubspace μ {y : Y | (y : ℂ) ∈ U} ≠ ⊥ := by
  sorry

/--
An operator commuting with a bounded self-adjoint `A` commutes with the whole bounded
Borel functional calculus of `A`.

Blueprint reference: `prpstn:hall-7.16` (Part 1).
-/
theorem commute_borelCalculus [Nontrivial H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    {B : H →L[ℂ] H} (hB : Commute A B) {f : spectrum ℝ A → ℂ}
    (hf : f ∈ BddMeasurable (spectrum ℝ A)) : Commute (borelCalculus hA f) B := by
  sorry

/--
Consequently every spectral subspace of `A` is invariant under `B`.

Blueprint reference: `prpstn:hall-7.16` (Part 2).
-/
theorem mapsTo_spectralSubspace_of_commute [Nontrivial H] {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) {B : H →L[ℂ] H} (hB : Commute A B) (E : Set (spectrum ℝ A))
    (ψ : H) (hψ : ψ ∈ spectralSubspace (spectralMeasure hA) E) :
    B ψ ∈ spectralSubspace (spectralMeasure hA) E := by
  sorry

/-!
### Almost eigenvectors
-/

/--
For a normal `A`, the operators `A - λ 1` and `A* - conj λ 1` have the same action on
norms.

Blueprint reference: `lmm:normality-balances-norms`.
-/
theorem norm_adjoint_sub_smul_apply {A : H →L[ℂ] H} [IsStarNormal A] (lam : ℂ) (ψ : H) :
    ‖(ContinuousLinearMap.adjoint A - (starRingEnd ℂ lam) • (1 : H →L[ℂ] H)) ψ‖ =
      ‖(A - lam • (1 : H →L[ℂ] H)) ψ‖ := by
  sorry

/--
An `ε`-almost eigenvector for `A` with eigenvalue `λ`: a nonzero `ψ` with
`‖(A - λ 1) ψ‖ < ε ‖ψ‖`.

Blueprint reference: `def:hall-10.24`.
-/
structure IsAlmostEigenvector (A : H →L[ℂ] H) (lam : ℂ) (ε : ℝ) (ψ : H) : Prop where
  /-- Almost eigenvectors are nonzero. -/
  ne_zero : ψ ≠ 0
  /-- The defining strict inequality. -/
  norm_lt : ‖(A - lam • (1 : H →L[ℂ] H)) ψ‖ < ε * ‖ψ‖

/--
An almost eigenvector of a normal `A` with eigenvalue `λ` is one for `A*` with eigenvalue
`conj λ`.

Blueprint reference: `lmm:hall-10.25` (Part 1).
-/
theorem isAlmostEigenvector_adjoint {A : H →L[ℂ] H} [IsStarNormal A] {lam : ℂ} {ε : ℝ}
    {ψ : H} (h : IsAlmostEigenvector A lam ε ψ) :
    IsAlmostEigenvector (ContinuousLinearMap.adjoint A) (starRingEnd ℂ lam) ε ψ := by
  sorry

/--
For a normal operator, the spectrum is exactly the set of `λ` admitting `ε`-almost
eigenvectors for every `ε > 0`.

Blueprint reference: `lmm:hall-10.25` (Part 2).
-/
theorem mem_spectrum_iff_forall_isAlmostEigenvector {A : H →L[ℂ] H} [IsStarNormal A]
    (lam : ℂ) :
    lam ∈ spectrum ℂ A ↔ ∀ ε : ℝ, 0 < ε → ∃ ψ : H, IsAlmostEigenvector A lam ε ψ := by
  sorry

/--
Polynomials in `A` and `A*` turn `ε`-almost eigenvectors into `(C ε)`-almost eigenvectors,
with `C` independent of `ε` and `ψ`.

Blueprint reference: `lmm:hall-10.26`.
-/
theorem exists_const_isAlmostEigenvector_mvApply {A : H →L[ℂ] H} [IsStarNormal A]
    (p : MvPolynomial (Fin 2) ℂ) (lam : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (ψ : H), IsAlmostEigenvector A lam ε ψ →
      IsAlmostEigenvector (mvApply A p) (mvEvalConj p lam) (C * ε) ψ := by
  sorry

/--
The adjoint of `p(A, A*)` is obtained by conjugating the coefficients and swapping the two
exponents.

Blueprint reference: `lmm:polynomials-in-normal-are-normal`.
-/
theorem adjoint_mvApply {A : H →L[ℂ] H} [IsStarNormal A] (p : MvPolynomial (Fin 2) ℂ) :
    ContinuousLinearMap.adjoint (mvApply A p) =
      ∑ d ∈ p.support, (starRingEnd ℂ (MvPolynomial.coeff d p)) •
        (A ^ d 1 * (ContinuousLinearMap.adjoint A) ^ d 0) := by
  sorry

/--
`p(A, A*)` is again normal.

Blueprint reference: `lmm:polynomials-in-normal-are-normal`.
-/
theorem isStarNormal_mvApply {A : H →L[ℂ] H} [IsStarNormal A] (p : MvPolynomial (Fin 2) ℂ) :
    IsStarNormal (mvApply A p) := by
  sorry

/--
`p(A, A*)` and its adjoint commute with `A` and with `A*`.

Blueprint reference: `lmm:polynomials-in-normal-are-normal`.
-/
theorem commute_mvApply {A : H →L[ℂ] H} [IsStarNormal A] (p : MvPolynomial (Fin 2) ℂ) :
    Commute (mvApply A p) A ∧ Commute (mvApply A p) (ContinuousLinearMap.adjoint A) ∧
      Commute (ContinuousLinearMap.adjoint (mvApply A p)) A ∧
      Commute (ContinuousLinearMap.adjoint (mvApply A p)) (ContinuousLinearMap.adjoint A) := by
  sorry

/--
A normal operator restricted to a nonzero closed subspace invariant under both `A` and
`A*` is again normal, with adjoint the restriction of `A*` and norm at most `‖A‖`.

Blueprint reference: `lmm:restriction-of-normal-operator`.
-/
theorem exists_restrict_isStarNormal {A : H →L[ℂ] H} [IsStarNormal A] {W : Submodule ℂ H}
    (hW : IsClosed (W : Set H)) [CompleteSpace W] (hne : W ≠ ⊥)
    (hAW : ∀ ψ ∈ W, A ψ ∈ W)
    (hA'W : ∀ ψ ∈ W, ContinuousLinearMap.adjoint A ψ ∈ W) :
    ∃ B : W →L[ℂ] W, (∀ ψ : W, ((B ψ : W) : H) = A (ψ : H)) ∧ IsStarNormal B ∧
      (∀ ψ : W, ((ContinuousLinearMap.adjoint B ψ : W) : H) =
        ContinuousLinearMap.adjoint A (ψ : H)) ∧ ‖B‖ ≤ ‖A‖ := by
  sorry

/--
For `ν` in the spectrum of `p(A, A*)` there is, for every `ε > 0`, a nonzero closed
subspace invariant under `A` and `A*` all of whose nonzero vectors are `ε`-almost
eigenvectors for `p(A, A*)` with eigenvalue `ν`.

Blueprint reference: `lmm:hall-10.27`.
-/
theorem exists_subspace_isAlmostEigenvector [Nontrivial H] {A : H →L[ℂ] H} [IsStarNormal A]
    (p : MvPolynomial (Fin 2) ℂ) {ν : ℂ} (hν : ν ∈ spectrum ℂ (mvApply A p)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ W : Submodule ℂ H, W ≠ ⊥ ∧ IsClosed (W : Set H) ∧
      (∀ ψ ∈ W, A ψ ∈ W) ∧ (∀ ψ ∈ W, ContinuousLinearMap.adjoint A ψ ∈ W) ∧
      ∀ ψ ∈ W, ψ ≠ 0 → IsAlmostEigenvector (mvApply A p) ν ε ψ := by
  sorry

/-!
### The two-variable spectral mapping theorem
-/

/--
**Spectral mapping for polynomials in `A` and `A*`.**

Blueprint reference: `thrm:hall-10.23`.
-/
theorem spectrum_mvApply [Nontrivial H] {A : H →L[ℂ] H} [IsStarNormal A]
    (p : MvPolynomial (Fin 2) ℂ) :
    spectrum ℂ (mvApply A p) = mvEvalConj p '' spectrum ℂ A := by
  sorry

/--
The norm of a polynomial in `A` and `A*` is the supremum of `|p(λ, conj λ)|` over the
spectrum.

Blueprint reference: `crllr:norm-of-polynomial-in-a-astar`.
-/
theorem norm_mvApply [Nontrivial H] {A : H →L[ℂ] H} [IsStarNormal A]
    (p : MvPolynomial (Fin 2) ℂ) :
    ‖mvApply A p‖ = sSup ((fun lam => ‖mvEvalConj p lam‖) '' spectrum ℂ A) := by
  sorry

/-!
### The continuous functional calculus for a normal operator
-/

/--
A two-variable polynomial restricted to `σ(A)`, as a continuous complex-valued function.
-/
noncomputable def mvPolyOn (A : H →L[ℂ] H) (p : MvPolynomial (Fin 2) ℂ) :
    C(spectrum ℂ A, ℂ) :=
  ⟨fun lam => mvEvalConj p (lam : ℂ), by sorry⟩

/--
The continuous functional calculus `f ↦ f(A)` of a bounded normal operator: Mathlib's
`cfcHom` for the predicate `IsStarNormal`, available because
`Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap` makes `H →L[ℂ] H` a C⋆-algebra.

Blueprint reference: `thrm:continuous-functional-calculus-normal`.
-/
noncomputable def normalCalculus {A : H →L[ℂ] H} (hA : IsStarNormal A) :
    C(spectrum ℂ A, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  cfcHom hA

/--
`normalCalculus` extends `p ↦ p(A, A*)`.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (the defining property).
-/
theorem normalCalculus_mvPolyOn {A : H →L[ℂ] H} (hA : IsStarNormal A)
    (p : MvPolynomial (Fin 2) ℂ) : normalCalculus hA (mvPolyOn A p) = mvApply A p := by
  sorry

/--
**The continuous functional calculus for a normal operator.** There is a unique bounded
`ℂ`-linear map `C⁰(σ(A); ℂ) → 𝓑(H)` sending `p` to `p(A, A*)`.

Blueprint reference: `thrm:continuous-functional-calculus-normal`.
-/
theorem existsUnique_normalCalculus [Nontrivial H] {A : H →L[ℂ] H} (hA : IsStarNormal A) :
    ∃! T : C(spectrum ℂ A, ℂ) →L[ℂ] (H →L[ℂ] H),
      ∀ p : MvPolynomial (Fin 2) ℂ, T (mvPolyOn A p) = mvApply A p := by
  sorry

/--
Multiplicativity of the normal functional calculus.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (Property 2).
-/
theorem normalCalculus_mul {A : H →L[ℂ] H} (hA : IsStarNormal A)
    (f g : C(spectrum ℂ A, ℂ)) :
    normalCalculus hA (f * g) = normalCalculus hA f * normalCalculus hA g :=
  map_mul (normalCalculus hA) f g

/--
The calculus intertwines complex conjugation with the adjoint.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (Property 3).
-/
theorem normalCalculus_star {A : H →L[ℂ] H} (hA : IsStarNormal A) (f : C(spectrum ℂ A, ℂ)) :
    normalCalculus hA (star f) = star (normalCalculus hA f) :=
  map_star (normalCalculus hA) f

/--
The calculus is isometric.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (Property 4).
-/
theorem norm_normalCalculus {A : H →L[ℂ] H} (hA : IsStarNormal A) (f : C(spectrum ℂ A, ℂ)) :
    ‖normalCalculus hA f‖ = ‖f‖ :=
  norm_cfcHom A f hA

/--
The calculus sends the constant `1` to `1` and the identity function to `A`.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (Property 5).
-/
theorem normalCalculus_one_and_id {A : H →L[ℂ] H} (hA : IsStarNormal A) :
    normalCalculus hA 1 = 1 ∧
      normalCalculus hA ⟨fun lam => (lam : ℂ), continuous_subtype_val⟩ = A := by
  sorry

/--
A real-valued `f` gives a self-adjoint operator, and every `f` gives a normal one.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (final paragraph).
-/
theorem isSelfAdjoint_normalCalculus_of_real {A : H →L[ℂ] H} (hA : IsStarNormal A)
    {f : C(spectrum ℂ A, ℂ)} (hf : ∀ lam, (f lam).im = 0) :
    IsSelfAdjoint (normalCalculus hA f) := by
  sorry

/--
Every value of the calculus is normal.

Blueprint reference: `thrm:continuous-functional-calculus-normal` (final paragraph).
-/
theorem isStarNormal_normalCalculus {A : H →L[ℂ] H} (hA : IsStarNormal A)
    (f : C(spectrum ℂ A, ℂ)) : IsStarNormal (normalCalculus hA f) := by
  sorry

end Unbounded
end Spectral
end Physicslib4
