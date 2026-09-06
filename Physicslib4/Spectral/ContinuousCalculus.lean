/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Physicslib4.Spectral.Spectrum

/-!
# The real-valued continuous functional calculus

For a self-adjoint `A ∈ 𝓑(H)` the blueprint builds a bounded linear map
`C⁰(σ(A); ℝ) → 𝓑(H)`, `f ↦ f(A)`, extending `p ↦ p(A)` on real polynomials, and
then represents each `ψ ↦ ⟪ψ, f(A) ψ⟫` as an integral against a finite positive
measure `μ_ψ` on `σ(A)`.

## Implementation notes

The blueprint's `σ(A)` is a subset of `ℂ` which, for self-adjoint `A`, is contained
in `ℝ` (`Physicslib4.Spectral.spectrum_subset_real`). We use Mathlib's real spectrum
`spectrum ℝ A` throughout this file, which is the canonical Lean shape (it is the
index type of Mathlib's `cfcHom`) and is homeomorphic to the blueprint's `σ(A)` via
`Complex.ofReal`.

## Main definitions

* `Physicslib4.Spectral.polyOn` — a real polynomial restricted to `σ(A)`.
* `Physicslib4.Spectral.realCalculus` — the real-valued continuous functional
  calculus `f ↦ f(A)`. This is Mathlib's `cfcHom`: `H →L[ℂ] H` is a C⋆-algebra, so
  the continuous functional calculus is already available and there is no reason to
  rebuild it. Its `StarAlgHom` type also carries the multiplicativity and
  `*`-compatibility that the blueprint's `prpstn:hall-8.4` asserts separately.
* `Physicslib4.Spectral.assocMeasure` — the finite positive measure `μ_ψ` on `σ(A)`.

## Main statements

* `Physicslib4.Spectral.existsUnique_realCalculus` — existence and uniqueness of the
  functional calculus.
* `Physicslib4.Spectral.realCalculus_properties` — multiplicativity,
  self-adjointness, positivity, the norm identity and the spectral mapping theorem.
* `Physicslib4.Spectral.existsUnique_assocMeasure` — the Riesz representation of
  `f ↦ ⟪ψ, f(A) ψ⟫`.
-/

namespace Physicslib4
namespace Spectral

open scoped InnerProductSpace
open Filter Topology ContinuousLinearMap MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### Prerequisites
-/

/--
**Riesz representation theorem.** A positive linear functional on the continuous
real-valued functions on a compact metric space is integration against a unique
finite positive Borel measure.

Blueprint reference: `thrm:riesz-representation`.
-/
theorem existsUnique_measure_of_positive_linear {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (Λ : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Λ f) :
    ∃! ν : Measure X, IsFiniteMeasure ν ∧ ∀ f : C(X, ℝ), ∫ x, f x ∂ν = Λ f := by
  let Λc : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ :=
    { toFun := fun f => Λ f.toContinuousMap
      monotone' := by
        intro f g hfg
        have hpos : 0 ≤ Λ (g.toContinuousMap - f.toContinuousMap) :=
          hΛ (g.toContinuousMap - f.toContinuousMap) (fun x => sub_nonneg.mpr (hfg x))
        rw [map_sub] at hpos
        exact sub_nonneg.mp hpos
      map_add' := by
        intro f g
        change Λ (f + g).toContinuousMap = Λ f.toContinuousMap + Λ g.toContinuousMap
        rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap from rfl]
        exact map_add Λ _ _
      map_smul' := by
        intro c f
        change Λ (c • f).toContinuousMap = c • Λ f.toContinuousMap
        rw [show (c • f).toContinuousMap = c • f.toContinuousMap from rfl]
        exact map_smul Λ c _ }
  let ν : Measure X := RealRMK.rieszMeasure Λc
  have hintegral : ∀ f : C(X, ℝ), ∫ x, f x ∂ν = Λ f := by
    intro f
    calc
      ∫ x, f x ∂ν = ∫ x, (CompactlySupportedContinuousMap.continuousMapEquiv f :
          CompactlySupportedContinuousMap X ℝ) x ∂ν := by
        simp [CompactlySupportedContinuousMap.continuousMapEquiv_apply_toFun]
      _ = Λc (CompactlySupportedContinuousMap.continuousMapEquiv f) :=
        RealRMK.integral_rieszMeasure (Λ := Λc)
          (f := CompactlySupportedContinuousMap.continuousMapEquiv f)
      _ = Λ f := by
        change Λ (CompactlySupportedContinuousMap.continuousMapEquiv f).toContinuousMap = Λ f
        congr 1
  refine ⟨ν, ⟨inferInstance, hintegral⟩, ?_⟩
  intro ν' hν'
  rcases hν' with ⟨hν'_fin, hν'_int⟩
  letI : IsFiniteMeasure ν' := hν'_fin
  exact Measure.ext_of_integral_eq_on_compactlySupported (μ := ν') (ν := ν) (by
    intro f
    calc
      ∫ x, (f : X → ℝ) x ∂ν' = Λ f.toContinuousMap := by simpa using hν'_int f.toContinuousMap
      _ = ∫ x, (f : X → ℝ) x ∂ν := by simpa using (hintegral f.toContinuousMap).symm)

/--
**Bounded linear transformation theorem.** A bounded linear map defined on a dense
subspace of a normed space, with values in a Banach space, extends uniquely to a
bounded linear map of the same norm.

This is Mathlib's `LinearMap.extendOfNorm` together with its API
(`LinearMap.extendOfNorm_eq`, `LinearMap.opNorm_extendOfNorm_le`).

Blueprint reference: `thrm:bounded-linear-transformation-theorem`.
-/
theorem existsUnique_extension_of_dense {V₁ V₂ : Type*} [NormedAddCommGroup V₁]
    [NormedSpace ℂ V₁] [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [CompleteSpace V₂]
    (W : Submodule ℂ V₁) (hW : Dense (W : Set V₁)) (T : W →L[ℂ] V₂) :
    ∃! S : V₁ →L[ℂ] V₂, (∀ w : W, S (w : V₁) = T w) ∧ ‖S‖ = ‖T‖ := by
  have hdense : DenseRange (W.subtype : W →ₗ[ℂ] V₁) := by
    simpa [DenseRange, Submodule.range_subtype] using hW
  have hbound : ∀ w : W, ‖(T : W →ₗ[ℂ] V₂) w‖ ≤ ‖T‖ * ‖W.subtype w‖ := by
    intro w; simpa using T.le_opNorm w
  set S := (T : W →ₗ[ℂ] V₂).extendOfNorm W.subtype with hS
  have hSeq : ∀ w : W, S (w : V₁) = T w := fun w =>
    LinearMap.extendOfNorm_eq hdense ⟨‖T‖, hbound⟩ w
  have hSle : ‖S‖ ≤ ‖T‖ :=
    LinearMap.opNorm_extendOfNorm_le hdense (norm_nonneg T) hbound
  have hTle : ‖T‖ ≤ ‖S‖ := by
    refine T.opNorm_le_bound (norm_nonneg S) fun w => ?_
    rw [← hSeq w]
    simpa using S.le_opNorm (w : V₁)
  refine ⟨S, ⟨hSeq, le_antisymm hSle hTle⟩, ?_⟩
  rintro S' ⟨hS', -⟩
  have hfun : (S' : V₁ → V₂) = (S : V₁ → V₂) :=
    Continuous.ext_on hW S'.continuous S.continuous fun x hx => by
      rw [show x = ((⟨x, hx⟩ : W) : V₁) from rfl, hS' ⟨x, hx⟩, hSeq ⟨x, hx⟩]
  exact ContinuousLinearMap.ext fun x => congrFun hfun x

/--
The complex polynomials are dense in the continuous complex-valued functions on the
real spectrum of a bounded operator, for the supremum norm.

Self-adjointness of `A` is not needed: this is Stone–Weierstrass for the compact
subset `spectrum ℝ A` of `ℝ`, and holds for every `A`. The blueprint states it for
self-adjoint `A` only because that is where it is applied.

Blueprint reference: `lmm:lemma-5`.
-/
theorem dense_polynomial_spectrum (A : H →L[ℂ] H) :
    Dense {f : C(spectrum ℝ A, ℂ) |
      ∃ p : Polynomial ℂ, ∀ l : spectrum ℝ A, f l = p.eval ((l : ℝ) : ℂ)} := by
  classical
  -- The complex polynomials, restricted to the (real) spectrum, as a subset of the
  -- continuous complex-valued functions.
  let S : Set C(spectrum ℝ A, ℂ) :=
    {f : C(spectrum ℝ A, ℂ) |
      ∃ p : Polynomial ℂ, ∀ l : spectrum ℝ A, f l = p.eval ((l : ℝ) : ℂ)}
  -- The coordinate function on the (real) spectrum, viewed as a complex-valued map.
  let x₀ : C(spectrum ℝ A, ℂ) := ⟨fun l => ((l : ℝ) : ℂ), by fun_prop⟩
  have hx₀_selfAdjoint : star x₀ = x₀ := by
    ext l
    simp [x₀]
  -- The complex star-subalgebra generated by `x₀`; since `x₀` is self-adjoint this is
  -- exactly the (complex) polynomials in `x₀`, i.e. the set `S` above.
  let T : StarSubalgebra ℂ C(spectrum ℝ A, ℂ) :=
    StarAlgebra.adjoin ℂ ({x₀} : Set C(spectrum ℝ A, ℂ))
  have hT_carrier : (T : Set C(spectrum ℝ A, ℂ)) =
      ((Algebra.adjoin ℂ ({x₀} : Set C(spectrum ℝ A, ℂ)) :
        Subalgebra ℂ C(spectrum ℝ A, ℂ)) : Set C(spectrum ℝ A, ℂ)) := by
    change (T.toSubalgebra : Set C(spectrum ℝ A, ℂ)) = _
    congr 1
    rw [StarAlgebra.adjoin_toSubalgebra]
    congr 1
    ext f
    constructor
    · intro hf
      rcases hf with hf | hf
      · simpa using hf
      · simpa [hx₀_selfAdjoint] using congrArg star hf
    · intro hf
      exact Or.inl hf
  have hT_sub : (T : Set C(spectrum ℝ A, ℂ)) ⊆ S := by
    intro f hf
    rw [hT_carrier] at hf
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hf
    rcases hf with ⟨p, hp⟩
    refine ⟨p, fun l => ?_⟩
    rw [← hp]
    simp [x₀]
  have hT_sep : T.SeparatesPoints := by
    rw [Subalgebra.SeparatesPoints, Set.SeparatesPoints]
    intro l₁ l₂ hne
    refine ⟨(x₀ : spectrum ℝ A → ℂ), ?_, ?_⟩
    · refine ⟨x₀, ?_, rfl⟩
      exact StarAlgebra.self_mem_adjoin_singleton ℂ x₀
    · intro h
      exact hne (Subtype.ext (Complex.ofReal_injective h))
  have hT_top : T.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints T hT_sep
  have hT_dense : Dense (T : Set C(spectrum ℝ A, ℂ)) :=by
    rw [Dense, ← StarSubalgebra.topologicalClosure_coe, hT_top]
    simp
  intro f
  exact closure_mono hT_sub (hT_dense f)

/-!
### The functional calculus
-/

/--
A real polynomial restricted to the spectrum of `A`, as a continuous real-valued
function on `σ(A)`.
-/
noncomputable def polyOn (A : H →L[ℂ] H) (p : Polynomial ℝ) : C(spectrum ℝ A, ℝ) :=
  ⟨fun l => p.eval (l : ℝ), p.continuous.comp continuous_subtype_val⟩

/--
The real-valued continuous functional calculus `f ↦ f(A)` of a self-adjoint
operator: Mathlib's `cfcHom`, which is available because
`Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap` makes `H →L[ℂ] H` a C⋆-algebra.

Using `cfcHom` rather than extracting a map from `existsUnique_realCalculus` keeps
the definition independent of any unproved statement, and records the fact — part
of the blueprint's `prpstn:hall-8.4` — that `f ↦ f(A)` is a `*`-algebra
homomorphism, not merely an `ℝ`-linear map.
-/
noncomputable def realCalculus {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H) :=
  cfcHom hA

/--
`realCalculus` extends the evaluation of real polynomials at `A`: this is the
defining property of the map whose existence and uniqueness
`existsUnique_realCalculus` asserts.

Blueprint reference: `prpstn:hall-8.3` (the defining property).
-/
theorem realCalculus_polyOn {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (p : Polynomial ℝ) :
    realCalculus hA (polyOn A p) = Polynomial.aeval A p := by
  rw [← cfc_polynomial (R := ℝ) p A hA, cfc_apply (R := ℝ) (fun x => Polynomial.eval x p) A hA]
  rfl

/--
**The real-valued functional calculus.** For self-adjoint `A` there is a unique
bounded `ℝ`-linear map `C⁰(σ(A); ℝ) → 𝓑(H)` which sends a real polynomial `p` to
`p(A)`.

Existence is `realCalculus`, i.e. `cfcHom hA`, made continuous by the isometry
`norm_cfcHom`; uniqueness is Stone–Weierstrass, in the form
`polynomialFunctions.topologicalClosure`.

Blueprint reference: `prpstn:hall-8.3`.
-/
theorem existsUnique_realCalculus {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    ∃! T : C(spectrum ℝ A, ℝ) →L[ℝ] (H →L[ℂ] H),
      ∀ p : Polynomial ℝ, T (polyOn A p) = Polynomial.aeval A p := by
  classical
  refine ⟨LinearMap.mkContinuous (cfcHom hA).toLinearMap 1
      (fun f => by simpa using (norm_cfcHom A f hA).le), fun p => realCalculus_polyOn hA p, ?_⟩
  intro T hT
  have hdense : Dense ((polynomialFunctions (spectrum ℝ A) : Set C(spectrum ℝ A, ℝ))) := by
    rw [Dense, ← Subalgebra.topologicalClosure_coe,
      polynomialFunctions.topologicalClosure (spectrum ℝ A)]
    simp
  refine ContinuousLinearMap.ext fun f => ?_
  refine congrFun (Continuous.ext_on hdense T.continuous (by fun_prop) fun g hg => ?_) f
  obtain ⟨p, -, rfl⟩ := hg
  change T (polyOn A p) = cfcHom hA (polyOn A p)
  exact (hT p).trans (realCalculus_polyOn hA p).symm

/--
Multiplicativity of the real-valued functional calculus.

Blueprint reference: `prpstn:cfc-multiplicative`.
-/
theorem realCalculus_mul {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (f g : C(spectrum ℝ A, ℝ)) :
    realCalculus hA (f * g) = realCalculus hA f * realCalculus hA g :=
  map_mul (realCalculus hA) f g

/--
The functional calculus of a real-valued continuous function is self-adjoint.

Blueprint reference: `prpstn:cfc-self-adjoint`.
-/
theorem isSelfAdjoint_realCalculus {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (f : C(spectrum ℝ A, ℝ)) : IsSelfAdjoint (realCalculus hA f) :=
  isSelfAdjoint_map (realCalculus hA) f

/--
The functional calculus of a non-negative continuous function is a non-negative
bounded operator.

Blueprint reference: `prpstn:cfc-non-negative`.
-/
theorem isPositive_realCalculus {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (f : C(spectrum ℝ A, ℝ)) (hf : ∀ l, 0 ≤ f l) : (realCalculus hA f).IsPositive := by
  rw [← ContinuousLinearMap.nonneg_iff_isPositive]
  exact (cfcHom_nonneg_iff hA).mpr fun l => hf l

/--
The functional calculus is isometric for the supremum norm.

Blueprint reference: `prpstn:cfc-norm`.
-/
theorem norm_realCalculus {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (f : C(spectrum ℝ A, ℝ)) :
    ‖realCalculus hA f‖ = ‖f‖ :=
  norm_cfcHom A f hA

/--
The spectral mapping theorem for the continuous functional calculus.

Blueprint reference: `prpstn:cfc-spectral-mapping`.
-/
theorem spectrum_realCalculus {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (f : C(spectrum ℝ A, ℝ)) :
    spectrum ℝ (realCalculus hA f) = Set.range f :=
  cfcHom_map_spectrum hA f

/--
The four properties of the real-valued functional calculus: multiplicativity,
self-adjointness, non-negativity, and the norm and spectrum identities.

This blueprint node is exactly the conjunction of the five statements above, so it
is proved from them rather than restated.

Blueprint reference: `prpstn:hall-8.4`.
-/
theorem realCalculus_properties {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    (∀ f g : C(spectrum ℝ A, ℝ),
        realCalculus hA (f * g) = realCalculus hA f * realCalculus hA g) ∧
      (∀ f : C(spectrum ℝ A, ℝ), IsSelfAdjoint (realCalculus hA f)) ∧
        (∀ f : C(spectrum ℝ A, ℝ), (∀ l, 0 ≤ f l) → (realCalculus hA f).IsPositive) ∧
          (∀ f : C(spectrum ℝ A, ℝ), ‖realCalculus hA f‖ = ‖f‖) ∧
            ∀ f : C(spectrum ℝ A, ℝ), spectrum ℝ (realCalculus hA f) = Set.range f :=
  ⟨realCalculus_mul hA, isSelfAdjoint_realCalculus hA, isPositive_realCalculus hA,
    norm_realCalculus hA, spectrum_realCalculus hA⟩

/-!
### The associated scalar measures
-/

/--
The positive linear functional `f ↦ ⟪ψ, f(A) ψ⟫` on the compactly supported
continuous real functions on `σ(A)` — every continuous function on the compact space
`σ(A)` is compactly supported, so this is all of `C⁰(σ(A); ℝ)`.

Positivity is `isPositive_realCalculus`, and the values are real because `f(A)` is
self-adjoint.
-/
noncomputable def assocFunctional {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H) :
    CompactlySupportedContinuousMap (spectrum ℝ A) ℝ →ₚ[ℝ] ℝ where
  toFun f := (⟪ψ, realCalculus hA f.toContinuousMap ψ⟫_ℂ).re
  monotone' f g hfg := by
    have hpos := isPositive_realCalculus hA (g.toContinuousMap - f.toContinuousMap)
      (fun l => sub_nonneg.mpr (hfg l))
    have h := (Complex.le_def.mp (hpos.inner_nonneg_right (x := ψ))).1
    rw [map_sub] at h
    simpa [sub_apply, inner_sub_right, sub_nonneg] using h
  map_add' f g := by
    have : (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap := rfl
    simp [this, map_add, inner_add_right, Complex.add_re]
  map_smul' c f := by
    have hc : (c • f).toContinuousMap = c • f.toContinuousMap := rfl
    rw [hc, map_smul]
    change (⟪ψ, c • (realCalculus hA f.toContinuousMap ψ)⟫_ℂ).re =
      c • (⟪ψ, realCalculus hA f.toContinuousMap ψ⟫_ℂ).re
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_right, Complex.smul_re]

/--
The finite positive measure `μ_ψ` on `σ(A)` associated with a self-adjoint operator
and a vector; this is the measure entering the blueprint's `Q_f`.

It is the Riesz–Markov–Kakutani measure of `assocFunctional hA ψ`, so it does not
depend on the unproved `existsUnique_assocMeasure` below.
-/
noncomputable def assocMeasure {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H) :
    Measure (spectrum ℝ A) :=
  RealRMK.rieszMeasure (assocFunctional hA ψ)

instance {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H) : IsFiniteMeasure (assocMeasure hA ψ) :=
  RealRMK.instIsFiniteMeasureRieszMeasure _

theorem integral_assocMeasure {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H)
    (f : C(spectrum ℝ A, ℝ)) :
    ⟪ψ, realCalculus hA f ψ⟫_ℂ = ((∫ l, f l ∂(assocMeasure hA ψ) : ℝ) : ℂ) := by
  have hre_val : ⟪ψ, realCalculus hA f ψ⟫_ℂ = ((⟪ψ, realCalculus hA f ψ⟫_ℂ).re : ℂ) := by
    have hconj : star ⟪ψ, realCalculus hA f ψ⟫_ℂ = ⟪ψ, realCalculus hA f ψ⟫_ℂ := by
      calc
        star ⟪ψ, realCalculus hA f ψ⟫_ℂ = ⟪realCalculus hA f ψ, ψ⟫_ℂ :=
          inner_conj_symm (x := realCalculus hA f ψ) (y := ψ)
        _ = ⟪ψ, realCalculus hA f ψ⟫_ℂ :=
          (isSelfAdjoint_realCalculus hA f).isSymmetric ψ ψ
    exact ((Complex.conj_eq_iff_re).mp hconj).symm
  have hint : (∫ l, f l ∂(assocMeasure hA ψ) : ℝ) = (⟪ψ, realCalculus hA f ψ⟫_ℂ).re := by
    letI : CompactlySupportedContinuousMapClass C(spectrum ℝ A, ℝ) (spectrum ℝ A) ℝ :=
      CompactlySupportedContinuousMapClass.of_compactSpace C(spectrum ℝ A, ℝ)
    let g : CompactlySupportedContinuousMap (spectrum ℝ A) ℝ := f
    have hg : g.toContinuousMap = f := by
      ext x
      rfl
    calc
      (∫ l, f l ∂(assocMeasure hA ψ) : ℝ)
          = ∫ x, g x ∂(assocMeasure hA ψ) := by
              rfl
      _ = (assocFunctional hA ψ) g := by
              simp [assocMeasure]
      _ = (⟪ψ, realCalculus hA f ψ⟫_ℂ).re := by
              change (assocFunctional hA ψ).toFun g = (⟪ψ, realCalculus hA f ψ⟫_ℂ).re
              simp [assocFunctional, hg]
  calc
    ⟪ψ, realCalculus hA f ψ⟫_ℂ = ((⟪ψ, realCalculus hA f ψ⟫_ℂ).re : ℂ) := hre_val
    _ = ((∫ l, f l ∂(assocMeasure hA ψ) : ℝ) : ℂ) := by
      rw [hint]

/--
For self-adjoint `A` and every `ψ ∈ H` there is a unique finite positive Borel
measure `μ_ψ` on `σ(A)` with `⟪ψ, f(A) ψ⟫ = ∫ f dμ_ψ` for all continuous real `f`.

Existence is `assocMeasure` together with `integral_assocMeasure`; only uniqueness —
which is the regularity half of Riesz–Markov–Kakutani — is left open.

Blueprint reference: `prpstn:associated-measures-self-adjoint`.
-/
theorem existsUnique_assocMeasure {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H) :
    ∃! ν : Measure (spectrum ℝ A), IsFiniteMeasure ν ∧
      ∀ f : C(spectrum ℝ A, ℝ),
        ⟪ψ, realCalculus hA f ψ⟫_ℂ = ((∫ l, f l ∂ν : ℝ) : ℂ) := by
  refine ⟨assocMeasure hA ψ, ⟨?_, fun f => integral_assocMeasure hA ψ f⟩, ?_⟩
  · infer_instance
  · rintro ν ⟨hνfin, hνint⟩
    letI : IsFiniteMeasure ν := hνfin
    let μ : Measure (spectrum ℝ A) := assocMeasure hA ψ
    have hμint : ∀ f : C(spectrum ℝ A, ℝ),
        ⟪ψ, realCalculus hA f ψ⟫_ℂ = ((∫ l, f l ∂μ : ℝ) : ℂ) := fun f =>
          integral_assocMeasure hA ψ f
    have hInts : ∀ f : C(spectrum ℝ A, ℝ), (∫ l, f l ∂ν : ℝ) = ∫ l, f l ∂μ := by
      intro f
      exact Complex.ofReal_injective ((hνint f).symm.trans (hμint f))
    letI : CompactlySupportedContinuousMapClass C(spectrum ℝ A, ℝ) (spectrum ℝ A) ℝ :=
      CompactlySupportedContinuousMapClass.of_compactSpace C(spectrum ℝ A, ℝ)
    refine MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported (μ := ν) (ν := μ) ?_
    intro g
    simpa using hInts g.toContinuousMap

/--
The total mass of `μ_ψ` is `‖ψ‖²`; in particular `μ_ψ` is a finite measure.

Blueprint reference: `lmm:associated-measures-are-finite`.
-/
theorem assocMeasure_univ {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H) :
    (assocMeasure hA ψ) Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  have hre : (assocMeasure hA ψ).real Set.univ = ‖ψ‖ ^ 2 := by
    have hmain := integral_assocMeasure hA ψ (1 : C(spectrum ℝ A, ℝ))
    rw [map_one] at hmain
    simp at hmain
    exact_mod_cast hmain.symm
  calc
    (assocMeasure hA ψ) Set.univ =
        ENNReal.ofReal ((assocMeasure hA ψ) Set.univ).toReal := by
      rw [ENNReal.ofReal_toReal (measure_ne_top (assocMeasure hA ψ) Set.univ)]
    _ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
      have hdef : ((assocMeasure hA ψ) Set.univ).toReal = (assocMeasure hA ψ).real Set.univ := rfl
      rw [hdef, hre]

end Spectral
end Physicslib4
