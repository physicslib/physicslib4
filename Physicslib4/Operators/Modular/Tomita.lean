/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.Antiunitary
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The Tomita operator

Stage 1 of the Tomita–Takesaki section of the blueprint: the reference conjugation `C`, the
von Neumann algebra setting with the project's commutant convention (`Set.centralizer`), cyclic
and separating vectors, the Tomita pre-operators `S₀`, `F₀`, the linearized pre-operator
`S₀′ = C ∘ S₀`, and the Tomita operator `S = C ∘ closure S₀′`.

## Representation

* **Setting.** A von Neumann algebra is a set `M : Set (H →L[ℂ] H)` satisfying
  `IsVonNeumannSet M`: self-adjoint and equal to `Set.centralizer (Set.centralizer M)`.
* **Antilinear partial maps.** Mathlib's `LinearPMap` is semilinear (`E →ₛₗ.[σ] F`), but its
  graph, `Submodule.toLinearPMap`, `closure`, `IsClosable` and `adjoint` exist only for linear
  partial maps; this is why closure and adjoint are taken of the linear `S₀′ = C ∘ S₀`. The
  pre-operator `S₀` is a domain `D : Submodule ℂ H` together with a function `D → H`, defined
  without `C` from a classically chosen representative.
  `S₀` is `tomitaPre M Ω` on `tomitaPreDomain M Ω`, and `F₀` is
  `tomitaPre (Set.centralizer M) Ω` on `tomitaPreDomain (Set.centralizer M) Ω`.
* **Conjugation.** Lemmas take an arbitrary antiunitary `C : H ≃ₗᵢ⋆[ℂ] H`, with the
  involution hypothesis `∀ x, C (C x) = x` where it is used. The reference conjugation
  `referenceConjugation b` of a Hilbert basis `b` is one such `C`; statements about an
  arbitrary `C` cover independence of the choice.
* **Linearization.** `S₀′ = linearizedTomitaPre M Ω C : H →ₗ.[ℂ] H` is defined from its graph
  `{(aΩ, C(a⋆Ω)) | a ∈ span M}`, which is a `ℂ`-submodule of `H × H`, via
  `Submodule.toLinearPMap`. The Tomita operator is `tomitaOperator M Ω C`, the function
  `x ↦ C (S₀′.closure x)` on the domain of the closure.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The reference conjugation -/

/-- The reference conjugation of a Hilbert basis `b`: the map conjugating coordinates,
`C (∑ cᵢ eᵢ) = ∑ conj cᵢ eᵢ`, realised as `b.repr⁻¹ ∘ star ∘ b.repr` with `star` the
coordinatewise conjugation on `ℓ²(ι, ℂ)`. It is antilinear and isometric by its type.
Blueprint: def:reference-conjugation -/
noncomputable def referenceConjugation {ι : Type*} (b : HilbertBasis ι ℂ H) :
    H ≃ₗᵢ⋆[ℂ] H :=
  (b.repr.trans (starₗᵢ ℂ)).trans b.repr.symm

omit [CompleteSpace H] in
/-- The reference conjugation is an involution and conjugates inner products; antilinearity,
isometry and bijectivity hold by its type `H ≃ₗᵢ⋆[ℂ] H`, so it is an antiunitary involution.
Blueprint: lmm:reference-conjugation-properties -/
theorem referenceConjugation_properties {ι : Type*} (b : HilbertBasis ι ℂ H) :
    (∀ x, referenceConjugation b (referenceConjugation b x) = x) ∧
      ∀ x y, ⟪referenceConjugation b x, referenceConjugation b y⟫_ℂ = conj ⟪x, y⟫_ℂ :=
  ⟨fun x => by simp [referenceConjugation],
    inner_map_map_of_conjLinearIsometry (referenceConjugation b).toLinearIsometry⟩

/-! ### Von Neumann algebras, cyclic and separating vectors -/

/-- A von Neumann algebra on `H`, as a set of bounded operators: `M` is self-adjoint and equals
its bicommutant `M''`, where the commutant is `Set.centralizer`.
Blueprint: def:von-neumann-algebra-commutant-convention -/
def IsVonNeumannSet (M : Set (H →L[ℂ] H)) : Prop :=
  (∀ a ∈ M, star a ∈ M) ∧ Set.centralizer (Set.centralizer M) = M

/-- The commutant `M'` of a von Neumann algebra `M` is a von Neumann algebra with `M'' = M`, and
both `M` and `M'` are the carriers of unital `*`-subalgebras of `B(H)`.
Blueprint: lmm:commutant-von-neumann-algebra -/
theorem isVonNeumannSet_centralizer {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) :
    IsVonNeumannSet (Set.centralizer M) ∧ Set.centralizer (Set.centralizer M) = M ∧
      (∃ A : StarSubalgebra ℂ (H →L[ℂ] H), (A : Set (H →L[ℂ] H)) = M) ∧
      ∃ A : StarSubalgebra ℂ (H →L[ℂ] H), (A : Set (H →L[ℂ] H)) = Set.centralizer M := by
  have hstar : ∀ {S : Set (H →L[ℂ] H)}, (∀ a ∈ S, star a ∈ S) → S ∪ star S = S :=
    fun hS => Set.union_eq_left.mpr fun a ha => by simpa using hS _ ha
  have hA : (StarSubalgebra.centralizer ℂ M : Set (H →L[ℂ] H)) = Set.centralizer M := by
    rw [StarSubalgebra.coe_centralizer, hstar hM.1]
  have hB : (StarSubalgebra.centralizer ℂ (Set.centralizer M) : Set (H →L[ℂ] H)) = M := by
    rw [StarSubalgebra.coe_centralizer, ← hA,
      hstar fun a ha => star_mem (s := StarSubalgebra.centralizer ℂ M) ha, hA, hM.2]
  refine ⟨⟨fun a ha => ?_, Set.centralizer_centralizer_centralizer M⟩, hM.2,
    ⟨_, hB⟩, ⟨_, hA⟩⟩
  rw [← hA] at ha ⊢
  exact star_mem ha

/-- A vector `Ω` is separating for a set `S` of bounded operators if `a ∈ S` and `a Ω = 0`
imply `a = 0`.
Blueprint: def:separating-vector -/
def IsSeparatingVector (S : Set (H →L[ℂ] H)) (Ω : H) : Prop :=
  ∀ a ∈ S, a Ω = 0 → a = 0

/-- A vector `Ω` is cyclic and separating for `M` if it is cyclic for `M` and for its
commutant `M'`: the vectors `a Ω`, `a ∈ M`, and `b Ω`, `b ∈ M'`, are dense. Cyclicity for a set
of operators is stated as density of the image, the form used by `localVonNeumann_separating`.
Blueprint: def:cyclic-separating-vector -/
def IsCyclicSeparatingVector (M : Set (H →L[ℂ] H)) (Ω : H) : Prop :=
  Dense ((fun a => a Ω) '' M) ∧ Dense ((fun b => b Ω) '' Set.centralizer M)

omit [CompleteSpace H] in
/-- A cyclic and separating vector for `M` is separating for `M` and for `M'`.
Blueprint: lmm:cyclic-commutant-separating -/
theorem isSeparatingVector_of_isCyclicSeparatingVector {M : Set (H →L[ℂ] H)} {Ω : H}
    (hΩ : IsCyclicSeparatingVector M Ω) :
    IsSeparatingVector M Ω ∧ IsSeparatingVector (Set.centralizer M) Ω := by
  have key : ∀ S : Set (H →L[ℂ] H), Dense ((fun T => T Ω) '' S) →
      ∀ R : H →L[ℂ] H, (∀ T ∈ S, R * T = T * R) → R Ω = 0 → R = 0 := by
    intro S hS R hc hR
    have h : Set.EqOn (⇑R) (fun _ => (0 : H)) ((fun T => T Ω) '' S) := by
      rintro _ ⟨T, hT, rfl⟩
      change R (T Ω) = 0
      rw [← mul_apply_eq_comp, hc T hT, mul_apply_eq_comp, hR, map_zero]
    ext x
    exact congrFun (Continuous.ext_on hS R.continuous continuous_const h) x
  exact ⟨fun a ha => key _ hΩ.2 a fun T hT => Set.mem_centralizer_iff.mp hT a ha,
    fun b hb => key _ hΩ.1 b fun T hT => (Set.mem_centralizer_iff.mp hb T hT).symm⟩

/-! ### The Tomita pre-operators -/

/-- The vectors `a Ω` with `a` in a von Neumann algebra `M` and `b Ω` with `b ∈ M'` determine
`a⋆ Ω` and `b⋆ Ω`.
Blueprint: lmm:tomita-pre-operators-well-defined -/
theorem tomitaPre_wellDefined {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) :
    (∀ a ∈ M, ∀ b ∈ M, a Ω = b Ω → star a Ω = star b Ω) ∧
      ∀ a ∈ Set.centralizer M, ∀ b ∈ Set.centralizer M, a Ω = b Ω → star a Ω = star b Ω := by
  obtain ⟨-, -, ⟨A, hA⟩, B, hB⟩ := isVonNeumannSet_centralizer hM
  obtain ⟨h1, h2⟩ := isSeparatingVector_of_isCyclicSeparatingVector hΩ
  have key : ∀ A : StarSubalgebra ℂ (H →L[ℂ] H), IsSeparatingVector A Ω →
      ∀ a ∈ A, ∀ b ∈ A, a Ω = b Ω → star a Ω = star b Ω := fun A hs a ha b hb h => by
    rw [sub_eq_zero.mp (hs _ (sub_mem ha hb) (by rw [sub_apply, h, sub_self]))]
  rw [← hB] at h2 ⊢
  rw [← hA] at h1 ⊢
  exact ⟨key A h1, key B h2⟩

/-- For a von Neumann algebra `M` the linear span of `M` is `M` itself, since `M = M''` is a
centralizer and hence a `ℂ`-submodule.
Blueprint: lmm:tomita-pre-operators-apply -/
theorem span_eq_of_isVonNeumannSet {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) :
    (Submodule.span ℂ M : Set (H →L[ℂ] H)) = M := by
  have hc : ((Subalgebra.centralizer ℂ (Set.centralizer M)).toSubmodule : Set (H →L[ℂ] H)) = M :=
    hM.2
  exact subset_antisymm (Set.Subset.trans (Submodule.span_le.2 hc.symm.subset) hc.subset)
    Submodule.subset_span

/-- The domain `MΩ` of the Tomita pre-operator, as a submodule: the image of `span ℂ M` under
evaluation at `Ω`. For a von Neumann algebra `M` the span is `M` itself, so this is `MΩ`.
Blueprint: def:tomita-pre-operators -/
noncomputable def tomitaPreDomain (M : Set (H →L[ℂ] H)) (Ω : H) : Submodule ℂ H :=
  (Submodule.span ℂ M).map (ContinuousLinearMap.apply ℂ H Ω).toLinearMap

/-- The Tomita pre-operator `S₀ = tomitaPre M Ω` on `tomitaPreDomain M Ω`, sending `a Ω` to
`a⋆ Ω` for `a ∈ span M`; `F₀` is `tomitaPre (Set.centralizer M) Ω`. The representative `a` is
chosen classically; for a cyclic and separating vector the value does not depend on the choice
(`tomitaPre_wellDefined`) and the map is antilinear.
Blueprint: def:tomita-pre-operators -/
noncomputable def tomitaPre (M : Set (H →L[ℂ] H)) (Ω : H) : tomitaPreDomain M Ω → H :=
  fun x => (star (Classical.choose (Submodule.mem_map.mp x.2) : H →L[ℂ] H)) Ω

/-- The pre-operators act as intended on representatives: `S₀ (a Ω) = a⋆ Ω` for `a ∈ M` and
`F₀ (b Ω) = b⋆ Ω` for `b ∈ M′`.
Blueprint: lmm:tomita-pre-operators-apply -/
theorem tomitaPre_apply {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) :
    (∀ a (ha : a ∈ M), tomitaPre M Ω
        ⟨a Ω, Submodule.mem_map_of_mem (Submodule.subset_span ha)⟩ = star a Ω) ∧
      ∀ b (hb : b ∈ Set.centralizer M), tomitaPre (Set.centralizer M) Ω
        ⟨b Ω, Submodule.mem_map_of_mem (Submodule.subset_span hb)⟩ = star b Ω := by
  have key : ∀ N : Set (H →L[ℂ] H), IsVonNeumannSet N →
      (∀ a ∈ N, ∀ b ∈ N, a Ω = b Ω → star a Ω = star b Ω) → ∀ a (ha : a ∈ N),
        tomitaPre N Ω ⟨a Ω, Submodule.mem_map_of_mem (Submodule.subset_span ha)⟩ =
          star a Ω := by
    intro N hN hw a ha
    obtain ⟨hc, he⟩ := Classical.choose_spec (Submodule.mem_map.mp
      (Submodule.mem_map_of_mem (f := (ContinuousLinearMap.apply ℂ H Ω).toLinearMap)
        (Submodule.subset_span ha)))
    have hc' : _ ∈ N := (span_eq_of_isVonNeumannSet hN).subset (SetLike.mem_coe.mpr hc)
    exact hw _ hc' a ha he
  exact ⟨key M hM (tomitaPre_wellDefined hM hΩ).1,
    key _ (isVonNeumannSet_centralizer hM).1 (tomitaPre_wellDefined hM hΩ).2⟩

/-- `Dom S₀ = MΩ` and `Dom F₀ = M'Ω` are dense, and `S₀`, `F₀` map their domains into themselves
with `S₀ S₀ x = x` and `F₀ F₀ y = y`, so each maps its domain onto itself.
Blueprint: lmm:tomita-pre-operators-dense-involutive -/
theorem tomitaPre_dense_involutive {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) :
    Dense (tomitaPreDomain M Ω : Set H) ∧ Dense (tomitaPreDomain (Set.centralizer M) Ω : Set H) ∧
      (∀ x : tomitaPreDomain M Ω, ∃ h : tomitaPre M Ω x ∈ tomitaPreDomain M Ω,
        tomitaPre M Ω ⟨_, h⟩ = x) ∧
      ∀ y : tomitaPreDomain (Set.centralizer M) Ω,
        ∃ h : tomitaPre (Set.centralizer M) Ω y ∈ tomitaPreDomain (Set.centralizer M) Ω,
          tomitaPre (Set.centralizer M) Ω ⟨_, h⟩ = y := by
  have hd : ∀ N : Set (H →L[ℂ] H), Dense ((fun a => a Ω) '' N) →
      Dense (tomitaPreDomain N Ω : Set H) := fun N hN =>
    hN.mono (by
      rintro _ ⟨a, ha, rfl⟩
      exact Submodule.mem_map_of_mem (Submodule.subset_span ha))
  have hi : ∀ N : Set (H →L[ℂ] H), IsVonNeumannSet N →
      (∀ a (ha : a ∈ N), tomitaPre N Ω
        ⟨a Ω, Submodule.mem_map_of_mem (Submodule.subset_span ha)⟩ = star a Ω) →
      ∀ x : tomitaPreDomain N Ω, ∃ h : tomitaPre N Ω x ∈ tomitaPreDomain N Ω,
        tomitaPre N Ω ⟨_, h⟩ = x := by
    intro N hN happ x
    obtain ⟨a, ha, hx⟩ := Submodule.mem_map.mp x.2
    have ha' : a ∈ N := span_eq_of_isVonNeumannSet hN ▸ ha
    obtain rfl : x = ⟨a Ω, Submodule.mem_map_of_mem (Submodule.subset_span ha')⟩ :=
      Subtype.ext hx.symm
    rw [happ a ha']
    exact ⟨_, (happ (star a) (hN.1 a ha')).trans (by rw [star_star])⟩
  exact ⟨hd M hΩ.1, hd _ hΩ.2, hi M hM (tomitaPre_apply hM hΩ).1,
    hi _ (isVonNeumannSet_centralizer hM).1 (tomitaPre_apply hM hΩ).2⟩

/-- The adjoint relation `⟪y, S₀ x⟫ = ⟪x, F₀ y⟫` for `x ∈ Dom S₀`, `y ∈ Dom F₀`.
Blueprint: lmm:tomita-adjoint-relation -/
theorem tomitaPre_adjoint_relation {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (x : tomitaPreDomain M Ω)
    (y : tomitaPreDomain (Set.centralizer M) Ω) :
    ⟪(y : H), tomitaPre M Ω x⟫_ℂ = ⟪(x : H), tomitaPre (Set.centralizer M) Ω y⟫_ℂ := by
  obtain ⟨hc, hcx⟩ := Classical.choose_spec (Submodule.mem_map.mp x.2)
  obtain ⟨hd, hdy⟩ := Classical.choose_spec (Submodule.mem_map.mp y.2)
  have hc' := (span_eq_of_isVonNeumannSet hM).subset hc
  have hd' := (span_eq_of_isVonNeumannSet (isVonNeumannSet_centralizer hM).1).subset hd
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply] at hcx hdy
  have key : ∀ c ∈ M, ∀ d ∈ Set.centralizer M, ⟪d Ω, star c Ω⟫_ℂ = ⟪c Ω, star d Ω⟫_ℂ := by
    intro c hc' d hd'
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
      ← mul_apply_eq_comp, ← mul_apply_eq_comp, Set.mem_centralizer_iff.mp hd' _ hc']
  convert key _ hc' _ hd' using 2 <;> first | rfl | exact hdy.symm | exact hcx.symm

/-! ### The linearized pre-operator -/

/-- The linearized Tomita pre-operator `S₀′ = C ∘ S₀ : H →ₗ.[ℂ] H`, defined by its graph
`{(a Ω, C (a⋆ Ω)) | a ∈ span M}`. The map `a ↦ (a Ω, C (a⋆ Ω))` is `ℂ`-linear (a composite of
two antilinear maps in the second coordinate), so the graph is a submodule of `H × H`, turned
into a partial linear map by `Submodule.toLinearPMap`. Its domain is `tomitaPreDomain M Ω`.
Blueprint: def:linearized-tomita-pre-operator -/
noncomputable def linearizedTomitaPre (M : Set (H →L[ℂ] H)) (Ω : H) (C : H ≃ₗᵢ⋆[ℂ] H) :
    H →ₗ.[ℂ] H :=
  ((Submodule.span ℂ M).map
    ((ContinuousLinearMap.apply ℂ H Ω).toLinearMap.prod
      (C.toLinearEquiv.toLinearMap.comp
        ((ContinuousLinearMap.apply ℂ H Ω).toLinearMap.comp
          (starLinearEquiv ℂ (A := H →L[ℂ] H)).toLinearMap)))).toLinearPMap

/-- The domain of the linearized pre-operator is the domain of `S₀`: `Dom S₀′ = Dom S₀`.
Blueprint: lmm:tomita-pre-operators-apply -/
theorem linearizedTomitaPre_domain (M : Set (H →L[ℂ] H)) (Ω : H) (C : H ≃ₗᵢ⋆[ℂ] H) :
    (linearizedTomitaPre M Ω C).domain = tomitaPreDomain M Ω := by
  rw [linearizedTomitaPre, Submodule.toLinearPMap_domain, ← Submodule.map_comp]
  rfl

/-- The linearized pre-operator is `C ∘ S₀`: `S₀′ x = C (S₀ x)` for `x ∈ Dom S₀`.
Blueprint: lmm:tomita-pre-operators-apply -/
theorem linearizedTomitaPre_apply {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H) (x : tomitaPreDomain M Ω) :
    linearizedTomitaPre M Ω C ⟨x, by rw [linearizedTomitaPre_domain]; exact x.2⟩ =
      C (tomitaPre M Ω x) := by
  have hg : ∀ (p : H × H) (_ : p ∈ (Submodule.span ℂ M).map
      ((ContinuousLinearMap.apply ℂ H Ω).toLinearMap.prod
        (C.toLinearEquiv.toLinearMap.comp ((ContinuousLinearMap.apply ℂ H Ω).toLinearMap.comp
          (starLinearEquiv ℂ (A := H →L[ℂ] H)).toLinearMap)))) (_ : p.1 = 0), p.2 = 0 := by
    rintro _ ⟨a, ha, rfl⟩ h
    have ha' : a ∈ M := span_eq_of_isVonNeumannSet hM ▸ ha
    change C (star a Ω) = 0
    rw [(isSeparatingVector_of_isCyclicSeparatingVector hΩ).1 a ha' h, star_zero, zero_apply,
      map_zero]
  obtain ⟨hs, hx⟩ := Classical.choose_spec (Submodule.mem_map.mp x.2)
  have h1 := Submodule.mem_graph_toLinearPMap hg
    ⟨x, (by rw [linearizedTomitaPre_domain]; exact x.2 :
      (x : H) ∈ (linearizedTomitaPre M Ω C).domain)⟩
  have h2 := Submodule.sub_mem _ h1 (Submodule.mem_map_of_mem hs)
  have h3 := hg _ h2 (sub_eq_zero.mpr hx.symm)
  exact sub_eq_zero.mp h3

/-- `C (M′Ω)` lies in the domain of `(S₀′)⋆`, with `(S₀′)⋆ (C y) = F₀ y` for `y ∈ M′Ω`, and
`(S₀′)⋆` is densely defined.
Blueprint: lmm:linearized-adjoint-extends -/
theorem linearizedTomitaPre_adjoint_extends {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H) :
    (∀ y : tomitaPreDomain (Set.centralizer M) Ω,
      ∃ h : C y ∈ (linearizedTomitaPre M Ω C).adjoint.domain,
        (linearizedTomitaPre M Ω C).adjoint ⟨C y, h⟩ = tomitaPre (Set.centralizer M) Ω y) ∧
      Dense ((linearizedTomitaPre M Ω C).adjoint.domain : Set H) := by
  have hT : Dense ((linearizedTomitaPre M Ω C).domain : Set H) := by
    rw [linearizedTomitaPre_domain]; exact (tomitaPre_dense_involutive hM hΩ).1
  have key : ∀ (y : tomitaPreDomain (Set.centralizer M) Ω)
      (x : (linearizedTomitaPre M Ω C).domain),
      ⟪tomitaPre (Set.centralizer M) Ω y, (x : H)⟫_ℂ =
        ⟪C y, linearizedTomitaPre M Ω C x⟫_ℂ := by
    intro y x
    have hx : (x : H) ∈ tomitaPreDomain M Ω := linearizedTomitaPre_domain M Ω C ▸ x.2
    have h := linearizedTomitaPre_apply hM hΩ C ⟨x, hx⟩
    simp only [Subtype.coe_eta] at h
    rw [h, show ⟪C y, C (tomitaPre M Ω ⟨x, hx⟩)⟫_ℂ = _ from
      inner_map_map_of_conjLinearIsometry C.toLinearIsometry _ _,
      tomitaPre_adjoint_relation hM ⟨x, hx⟩ y, inner_conj_symm]
  have hmem : ∀ y : tomitaPreDomain (Set.centralizer M) Ω,
      C y ∈ (linearizedTomitaPre M Ω C).adjoint.domain := fun y =>
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key y⟩
  refine ⟨fun y => ⟨hmem y, LinearPMap.adjoint_apply_eq hT _ (key y)⟩, ?_⟩
  refine Dense.mono ?_ (C.surjective.denseRange.dense_image C.continuous
    (tomitaPre_dense_involutive hM hΩ).2.1)
  · rintro _ ⟨y, hy, rfl⟩
    exact hmem ⟨y, hy⟩

/-- The linearized pre-operator `S₀′` is closable.
Blueprint: crllr:linearized-tomita-closable -/
theorem linearizedTomitaPre_isClosable {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H) :
    (linearizedTomitaPre M Ω C).IsClosable :=
  isClosable_of_dense_adjoint
    (by rw [linearizedTomitaPre_domain]; exact (tomitaPre_dense_involutive hM hΩ).1)
    (linearizedTomitaPre_adjoint_extends hM hΩ C).2

/-! ### The Tomita operator -/

/-- The Tomita operator `S = C ∘ S′` on `Dom S = Dom S′`, where `S′` is the closure of the
linearized pre-operator `S₀′`. As an antilinear partial map it is a function on the domain
of `S′`.
Blueprint: def:tomita-operator -/
noncomputable def tomitaOperator (M : Set (H →L[ℂ] H)) (Ω : H) (C : H ≃ₗᵢ⋆[ℂ] H) :
    (linearizedTomitaPre M Ω C).closure.domain → H :=
  fun x => C ((linearizedTomitaPre M Ω C).closure x)

/-- The graph of `S` is the closure in `H × H` of the graph of `S₀`. Since the right side does
not involve `C`, the Tomita operator and its domain are independent of the antiunitary
involution `C`.
Blueprint: lmm:tomita-operator-independent-of-c -/
theorem tomitaOperator_graph_eq_closure {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    Set.range (fun x : (linearizedTomitaPre M Ω C).closure.domain =>
      ((x : H), tomitaOperator M Ω C x)) =
      closure (Set.range (fun x : tomitaPreDomain M Ω => ((x : H), tomitaPre M Ω x))) := by
  set T := linearizedTomitaPre M Ω C
  let Φ : H × H ≃ₜ H × H := (Homeomorph.refl H).prodCongr C.toHomeomorph
  have h1 : Set.range (fun x : T.closure.domain => ((x : H), tomitaOperator M Ω C x)) =
      Φ '' (T.closure.graph : Set (H × H)) := by
    ext p
    simp only [Set.mem_range, Set.mem_image, SetLike.mem_coe, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨((x : H), T.closure x), ⟨x, rfl, rfl⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨x, rfl, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  have h2 : Φ '' (T.graph : Set (H × H)) =
      Set.range (fun x : tomitaPreDomain M Ω => ((x : H), tomitaPre M Ω x)) := by
    ext p
    simp only [Set.mem_range, Set.mem_image, SetLike.mem_coe, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨x, rfl, rfl⟩, rfl⟩
      have hx : (x : H) ∈ tomitaPreDomain M Ω := linearizedTomitaPre_domain M Ω C ▸ x.2
      have h := linearizedTomitaPre_apply hM hΩ C ⟨x, hx⟩
      simp only [Subtype.coe_eta] at h
      refine ⟨⟨x, hx⟩, Prod.ext rfl ?_⟩
      change tomitaPre M Ω ⟨x, hx⟩ = C (T x)
      rw [show T x = _ from h, hC]
    · rintro ⟨x, rfl⟩
      have h := linearizedTomitaPre_apply hM hΩ C x
      refine ⟨((x : H), T _), ⟨⟨x, by rw [linearizedTomitaPre_domain]; exact x.2⟩, rfl, rfl⟩,
        Prod.ext rfl ?_⟩
      change C (T _) = _
      rw [h, hC]
  have h3 : (T.closure.graph : Set (H × H)) = closure (T.graph : Set (H × H)) := by
    rw [← (linearizedTomitaPre_isClosable hM hΩ C).graph_closure_eq_closure_graph,
      Submodule.topologicalClosure_coe]
  rw [h1, h3, Φ.image_closure, h2]

/-- The graph of the Tomita operator is invariant under swapping coordinates:
`(φ, ψ) ∈ Γ(S)` implies `(ψ, φ) ∈ Γ(S)`.
Blueprint: lmm:tomita-graph-flip -/
theorem tomitaOperator_graph_swap {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    ∀ p ∈ Set.range (fun x : (linearizedTomitaPre M Ω C).closure.domain =>
      ((x : H), tomitaOperator M Ω C x)),
      p.swap ∈ Set.range (fun x : (linearizedTomitaPre M Ω C).closure.domain =>
      ((x : H), tomitaOperator M Ω C x)) := by
  rw [tomitaOperator_graph_eq_closure hM hΩ C hC]
  intro p hp
  have hsub : Prod.swap '' Set.range (fun x : tomitaPreDomain M Ω => ((x : H), tomitaPre M Ω x))
      ⊆ Set.range (fun x : tomitaPreDomain M Ω => ((x : H), tomitaPre M Ω x)) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨h, hx⟩ := (tomitaPre_dense_involutive hM hΩ).2.2.1 x
    exact ⟨⟨_, h⟩, Prod.ext rfl hx⟩
  exact closure_mono hsub (image_closure_subset_closure_image continuous_swap ⟨p, hp, rfl⟩)

/-- The Tomita operator is an involution: `S` is injective, maps `Dom S` into itself with
`S S φ = φ` (hence onto `Dom S`), and its domain and range are dense.
Blueprint: thrm:tomita-operator-involution -/
theorem tomitaOperator_involution {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    Function.Injective (tomitaOperator M Ω C) ∧
      (∀ x, ∃ h : tomitaOperator M Ω C x ∈ (linearizedTomitaPre M Ω C).closure.domain,
        tomitaOperator M Ω C ⟨_, h⟩ = x) ∧
      Dense ((linearizedTomitaPre M Ω C).closure.domain : Set H) ∧
      Dense (Set.range (tomitaOperator M Ω C)) := by
  have hS : ∀ x, ∃ h : tomitaOperator M Ω C x ∈ (linearizedTomitaPre M Ω C).closure.domain,
      tomitaOperator M Ω C ⟨_, h⟩ = x := by
    intro x
    obtain ⟨z, hz⟩ := tomitaOperator_graph_swap hM hΩ C hC _ ⟨x, rfl⟩
    have e1 : (z : H) = tomitaOperator M Ω C x := congrArg Prod.fst hz
    have e2 : tomitaOperator M Ω C z = x := congrArg Prod.snd hz
    refine ⟨e1 ▸ z.2, ?_⟩
    rw [← e2]
    exact congrArg _ (Subtype.ext e1.symm)
  have hD : Dense ((linearizedTomitaPre M Ω C).closure.domain : Set H) :=
    (tomitaPre_dense_involutive hM hΩ).1.mono fun x hx =>
      (LinearPMap.le_closure _).1 (by rw [linearizedTomitaPre_domain]; exact hx)
  refine ⟨fun x y hxy => ?_, hS, hD, hD.mono fun x hx => ?_⟩
  · obtain ⟨hx, ex⟩ := hS x
    obtain ⟨hy, ey⟩ := hS y
    have e : (⟨_, hx⟩ : (linearizedTomitaPre M Ω C).closure.domain) = ⟨_, hy⟩ := Subtype.ext hxy
    exact Subtype.ext (by rw [← ex, ← ey, e])
  · obtain ⟨h, e⟩ := hS ⟨x, hx⟩
    exact ⟨_, e⟩

/-- The closure `S′` of the linearized pre-operator is closed, densely defined and injective,
with dense range.
Blueprint: crllr:linearized-tomita-properties -/
theorem linearizedTomita_closure_properties {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (linearizedTomitaPre M Ω C).closure.IsClosed ∧
      Dense ((linearizedTomitaPre M Ω C).closure.domain : Set H) ∧
      Function.Injective (linearizedTomitaPre M Ω C).closure ∧
      Dense (Set.range (linearizedTomitaPre M Ω C).closure) := by
  obtain ⟨hinj, -, hD, hR⟩ := tomitaOperator_involution hM hΩ C hC
  refine ⟨(linearizedTomitaPre_isClosable hM hΩ C).closure_isClosed, hD,
    fun x y hxy => hinj (congrArg C hxy), ?_⟩
  refine Dense.mono ?_ (C.surjective.denseRange.dense_image C.continuous hR)
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨x, (hC _).symm⟩

end Physicslib4.Modular
