/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Physicslib4.Spectral.Unbounded.Spectrum

/-!
# Hilbert space direct sums and componentwise self-adjoint operators

The blueprint's external Hilbert space direct sum `⨁ⱼ Hⱼ` is Mathlib's `lp G 2`, and the
internal notion — a family of pairwise orthogonal closed subspaces of `H` summing to `H`
— is recorded here as `IsInternalOrthogonalDecomposition`, identified with the external
one through Mathlib's `IsHilbertSum`.

The payoff is the pair of propositions saying that an operator acting componentwise by a
family of *bounded* self-adjoint operators, defined at least on the finite direct sum, is
essentially self-adjoint with closure given by the same componentwise formula on the
maximal domain.

## Main definitions

* `Physicslib4.Spectral.Unbounded.IsInternalOrthogonalDecomposition`
* `Physicslib4.Spectral.Unbounded.IsDirectSumOperator`,
  `Physicslib4.Spectral.Unbounded.directSumDomain` (external form)
* `Physicslib4.Spectral.Unbounded.IsInternalDirectSumOperator`,
  `Physicslib4.Spectral.Unbounded.internalDomain` (internal form)

## Main statements

* `dense_setOf_finite_support` — the finite direct sum is dense.
* `isHilbertSum_of_isInternalOrthogonalDecomposition` — an internal decomposition is
  unitarily the external direct sum of its summands.
* `isEssentiallySelfAdjoint_of_isDirectSumOperator` and companions — the external form of
  the blueprint's Proposition 9.26.
* `isEssentiallySelfAdjoint_of_isInternalDirectSumOperator` and companions — its internal
  form.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### The external Hilbert space direct sum

The blueprint's `⨁ⱼ Hⱼ` — square-summable sequences with the componentwise inner product
— is Mathlib's `lp G 2` together with `lp.instInnerProductSpace`.
-/

section External

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
variable [∀ i, InnerProductSpace ℂ (G i)]

omit [∀ i, InnerProductSpace ℂ (G i)] in
/--
The finite direct sum — the elements of `⨁ᵢ Gᵢ` with only finitely many non-zero entries
— is dense. (That it is a subspace is immediate, a linear combination of two
finitely-supported families again being finitely supported.)

Blueprint reference: `lmm:finite-direct-sum-dense`.
-/
theorem dense_setOf_finite_support :
    Dense {f : lp G 2 | {i : ι | f i ≠ 0}.Finite} := by
  classical
  exact fun f => mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top f)
    (Eventually.of_forall fun s => s.finite_toSet.subset fun i hi => by
      by_contra hs
      simp only [lp.coeFn_sum, lp.coeFn_single, Set.mem_setOf_eq, Finset.sum_apply] at hi
      exact hi (Finset.sum_eq_zero fun j hj =>
        Pi.single_eq_of_ne (fun h : i = j => hs (h ▸ hj)) _))

end External

/-!
### Internal orthogonal decompositions
-/

/--
A sequence `K` of closed subspaces of `H` is an *internal orthogonal decomposition* of
`H` if the subspaces are pairwise orthogonal and every vector of `H` is the sum of a
norm-convergent series with `n`-th term in `K n`.

Blueprint reference: `def:internal-orthogonal-decomposition`.
-/
structure IsInternalOrthogonalDecomposition (K : ℕ → Submodule ℂ H) : Prop where
  /-- Each summand is closed. -/
  isClosed : ∀ n, IsClosed ((K n : Set H))
  /-- The summands are pairwise orthogonal. -/
  orthogonal : ∀ {n m : ℕ}, n ≠ m → ∀ η ∈ K n, ∀ ζ ∈ K m, ⟪η, ζ⟫_ℂ = 0
  /-- Every vector decomposes as a norm-convergent series with terms in the summands. -/
  exists_hasSum : ∀ ψ : H, ∃ f : ∀ n, K n, HasSum (fun n => (f n : H)) ψ

omit [CompleteSpace H] in
/-- The summands of an internal orthogonal decomposition form an orthogonal family. -/
private theorem orthogonalFamily_of_isInternalOrthogonalDecomposition
    {K : ℕ → Submodule ℂ H} (h : IsInternalOrthogonalDecomposition K) :
    OrthogonalFamily ℂ (fun n => (K n : Type _)) (fun n => (K n).subtypeₗᵢ) :=
  orthogonalFamily_iff_pairwise.mpr fun _ _ hnm _ hη =>
    (Submodule.mem_orthogonal _ _).mpr fun _ hζ => h.orthogonal (Ne.symm hnm) _ hζ _ hη

/-- Pythagoras along an internal orthogonal decomposition (auxiliary form). -/
private theorem hasSum_norm_sq_aux {K : ℕ → Submodule ℂ H}
    (h : IsInternalOrthogonalDecomposition K) {ψ : H} {f : ∀ n, K n}
    (hf : HasSum (fun n => (f n : H)) ψ) :
    HasSum (fun n => ‖(f n : H)‖ ^ 2) (‖ψ‖ ^ 2) := by
  have hV := orthogonalFamily_of_isInternalOrthogonalDecomposition h
  have hs := (hV.summable_iff_norm_sq_summable f).mp hf.summable
  let F : lp (fun n => (K n : Type _)) 2 := ⟨f, memℓp_gen (by simpa using hs)⟩
  have hψ : hV.linearIsometry F = ψ := (hV.hasSum_linearIsometry F).unique hf
  simpa [← hψ, F] using lp.hasSum_norm (p := 2) (by norm_num) F

/--
The decomposition of a vector along an internal orthogonal decomposition is unique.

Blueprint reference: `lmm:internal-decomposition-unitary` (Part 1).
-/
theorem hasSum_injective_of_isInternalOrthogonalDecomposition {K : ℕ → Submodule ℂ H}
    (h : IsInternalOrthogonalDecomposition K) {ψ : H} {f g : ∀ n, K n}
    (hf : HasSum (fun n => (f n : H)) ψ) (hg : HasSum (fun n => (g n : H)) ψ) : f = g := by
  have hd := hasSum_norm_sq_aux h (f := f - g) (by
    simpa using hf.sub hg)
  have h0 := (hasSum_zero_iff_of_nonneg (f := fun n => ‖((f - g) n : H)‖ ^ 2)
    (fun n => by positivity)).mp (by simpa using hd)
  funext n
  simpa [sub_eq_zero] using congrFun h0 n

/--
Pythagoras for an internal orthogonal decomposition: `‖ψ‖² = ∑ₙ ‖ψₙ‖²`.

Blueprint reference: `lmm:internal-decomposition-unitary` (Part 2).
-/
theorem hasSum_norm_sq_of_isInternalOrthogonalDecomposition {K : ℕ → Submodule ℂ H}
    (h : IsInternalOrthogonalDecomposition K) {ψ : H} {f : ∀ n, K n}
    (hf : HasSum (fun n => (f n : H)) ψ) :
    HasSum (fun n => ‖(f n : H)‖ ^ 2) (‖ψ‖ ^ 2) :=
  hasSum_norm_sq_aux h hf

/--
An internal orthogonal decomposition exhibits `H` as the external direct sum of its
summands; the identifying map `ψ ↦ (ψ₁, ψ₂, …)` is unitary. In Lean this is Mathlib's
`IsHilbertSum` for the inclusions `(K n).subtypeₗᵢ`, and the unitary map is
`IsHilbertSum.linearIsometryEquiv`.

Blueprint reference: `lmm:internal-decomposition-unitary` (Part 3).
-/
theorem isHilbertSum_of_isInternalOrthogonalDecomposition {K : ℕ → Submodule ℂ H}
    (h : IsInternalOrthogonalDecomposition K) :
    IsHilbertSum ℂ (fun n => (K n : Type _)) (fun n => (K n).subtypeₗᵢ) := by
  have : ∀ n, CompleteSpace (K n) := fun n => (h.isClosed n).completeSpace_coe
  refine IsHilbertSum.mkInternal _ (orthogonalFamily_of_isInternalOrthogonalDecomposition h)
    fun ψ _ => ?_
  obtain ⟨f, hf⟩ := h.exists_hasSum ψ
  exact mem_closure_of_tendsto hf.tendsto_sum_nat (Eventually.of_forall fun N =>
    Submodule.sum_mem _ fun n _ => Submodule.mem_iSup_of_mem n (f n).2)

/-!
### Componentwise self-adjoint operators, external form
-/

section DirectSumOperator

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
variable [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

/--
The maximal domain `V` for the componentwise operator determined by a family `A` of
bounded operators: the vectors whose components and images have square-summable norms.

Blueprint reference: `prpstn:hall-9.26`.
-/
def directSumDomain (A : ∀ i, G i →L[ℂ] G i) : Set (lp G 2) :=
  {ψ | Summable fun i => ‖ψ i‖ ^ 2 + ‖A i (ψ i)‖ ^ 2}

/--
`T` is *the componentwise operator determined by the family `A`*: it is symmetric, its
domain contains the finite direct sum, and it acts by `A` componentwise there.

Blueprint reference: `prpstn:hall-9.26`.
-/
structure IsDirectSumOperator (A : ∀ i, G i →L[ℂ] G i) (T : lp G 2 →ₗ.[ℂ] lp G 2) :
    Prop where
  /-- `T` is symmetric. -/
  isSymmetric : IsSymmetric T
  /-- The finite direct sum lies in `Dom(T)`. -/
  memDomain : ∀ f : lp G 2, {i : ι | f i ≠ 0}.Finite → f ∈ T.domain
  /-- On the finite direct sum, `T` acts componentwise by `A`. -/
  apply_eq : ∀ (f : lp G 2) (hf : {i : ι | f i ≠ 0}.Finite) (i : ι),
    (T ⟨f, memDomain f hf⟩) i = A i (f i)

variable {A : ∀ i, G i →L[ℂ] G i} {T : lp G 2 →ₗ.[ℂ] lp G 2}

omit [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)] in
/-- The squared component norms of a vector of `⨁ᵢ Gᵢ` are summable. -/
private theorem summable_norm_sq_lp (f : lp G 2) : Summable fun i => ‖f i‖ ^ 2 := by
  have := (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  simpa using this

omit [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)] in
/-- A family with square-summable norms is a vector of `⨁ᵢ Gᵢ`. -/
private theorem memℓp_two_of_summable {f : ∀ i, G i} (hf : Summable fun i => ‖f i‖ ^ 2) :
    Memℓp f 2 :=
  memℓp_gen (by simpa using hf)

omit [∀ i, CompleteSpace (G i)] in
/-- A submodule of `⨁ᵢ Gᵢ` containing every `lp.single 2 i η` is dense. -/
private theorem dense_of_single_mem [DecidableEq ι] (S : Submodule ℂ (lp G 2))
    (h : ∀ i η, lp.single 2 i η ∈ S) : Dense (S : Set (lp G 2)) := fun f =>
  mem_closure_of_tendsto (lp.hasSum_single (by norm_num) f)
    (Eventually.of_forall fun s => S.sum_mem fun i _ => h i (f i))

omit [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)] in
/-- `lp.single 2 i η` is finitely supported. -/
private theorem finite_support_single [DecidableEq ι] (i : ι) (η : G i) :
    {j : ι | lp.single 2 i η j ≠ 0}.Finite :=
  (Set.finite_singleton i).subset fun j hj => by
    by_contra hji
    exact hj (lp.single_apply_ne 2 i η hji)

omit [∀ i, CompleteSpace (G i)] in
/-- A componentwise operator maps `lp.single 2 i η` to `lp.single 2 i (A i η)`. -/
private theorem apply_single_of_isDirectSumOperator [DecidableEq ι]
    (hT : IsDirectSumOperator A T) (i : ι) (η : G i) :
    T ⟨lp.single 2 i η, hT.memDomain _ (finite_support_single i η)⟩ =
      lp.single 2 i (A i η) := by
  ext j
  rw [hT.apply_eq _ (finite_support_single i η), lp.single_apply, lp.single_apply,
    Pi.apply_single (fun j => A j) (by simp)]

omit [∀ i, CompleteSpace (G i)] in
/-- A componentwise operator is densely defined. -/
private theorem hasDenseDomain_of_isDirectSumOperator (hT : IsDirectSumOperator A T) :
    HasDenseDomain T := by
  classical
  exact dense_of_single_mem T.domain fun i η => hT.memDomain _ (finite_support_single i η)

/-- For `B` bounded self-adjoint and `c` non-real, `B - c 1` is surjective. -/
private theorem exists_sub_smul_eq_of_isSelfAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {B : E →L[ℂ] E} (hB : IsSelfAdjoint B)
    {c : ℂ} (hc : c.im ≠ 0) (η : E) : ∃ ξ : E, B ξ - c • ξ = η := by
  have hns : c ∉ spectrum ℂ B := fun h => hc (by rw [hB.mem_spectrum_eq_re h]; simp)
  obtain ⟨u, hu⟩ := spectrum.notMem_iff.mp hns
  refine ⟨-((↑u⁻¹ : E →L[ℂ] E) η), ?_⟩
  rw [map_neg, smul_neg, sub_neg_eq_add, neg_add_eq_sub]
  simpa [hu, Algebra.algebraMap_eq_smul_one] using
    congrArg (fun L : E →L[ℂ] E => L η) u.mul_inv

/-- The range of `T - c 1` contains `lp.single 2 i η` for non-real `c`. -/
private theorem single_mem_range_subSmul [DecidableEq ι] (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) {c : ℂ} (hc : c.im ≠ 0) (i : ι) (η : G i) :
    lp.single 2 i η ∈ range (subSmul T c) := by
  obtain ⟨ξ, hξ⟩ := exists_sub_smul_eq_of_isSelfAdjoint (hA i) hc η
  refine mem_range.mpr ⟨⟨lp.single 2 i ξ, hT.memDomain _ (finite_support_single i ξ)⟩, ?_⟩
  rw [subSmul_apply]
  erw [apply_single_of_isDirectSumOperator hT i ξ]
  rw [← hξ, ← lp.single_smul, ← lp.single_sub]

/-- The adjoint of a componentwise operator acts componentwise by `A`. -/
private theorem adjoint_apply_component (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) (φ : (T†).domain) (i : ι) :
    (T† φ) i = A i ((φ : lp G 2) i) := by
  classical
  refine ext_inner_right ℂ fun η => ?_
  have hd := hasDenseDomain_of_isDirectSumOperator hT
  let x : T.domain := ⟨lp.single 2 i η, hT.memDomain _ (finite_support_single i η)⟩
  have h : ⟪T† φ, (x : lp G 2)⟫_ℂ = ⟪(φ : lp G 2), T x⟫_ℂ :=
    LinearPMap.adjoint_isFormalAdjoint hd φ x
  have hx : T x = lp.single 2 i (A i η) := apply_single_of_isDirectSumOperator hT i η
  rw [hx, lp.inner_single_right, lp.inner_single_right] at h
  rw [h, ← ContinuousLinearMap.adjoint_inner_left, (hA i).adjoint_eq]

/-- The domain of the adjoint of a componentwise operator lies in `V`. -/
private theorem mem_directSumDomain_of_mem_adjoint (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) {φ : lp G 2} (hφ : φ ∈ (T†).domain) :
    φ ∈ directSumDomain A :=
  (summable_norm_sq_lp φ).add ((summable_norm_sq_lp (T† ⟨φ, hφ⟩)).congr fun i => by
    rw [adjoint_apply_component hA hT ⟨φ, hφ⟩ i])

omit [∀ i, CompleteSpace (G i)] in
/-- The graph of a componentwise operator contains the finite sums of pairs
`(lp.single 2 i (η i), lp.single 2 i (A i (η i)))`. -/
private theorem sum_single_mem_graph [DecidableEq ι] (hT : IsDirectSumOperator A T)
    (s : Finset ι) (η : ∀ i, G i) :
    (∑ i ∈ s, lp.single 2 i (η i), ∑ i ∈ s, lp.single 2 i (A i (η i))) ∈ T.graph := by
  have h := T.graph.sum_mem (t := s) fun i _ => by
    have := T.mem_graph ⟨lp.single 2 i (η i), hT.memDomain _ (finite_support_single i (η i))⟩
    erw [apply_single_of_isDirectSumOperator hT i (η i)] at this
    exact this
  convert h using 1
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

/-- `V` lies in the domain of the adjoint of a componentwise operator: `T†` is closed and
extends `T`, whose graph approximates `(φ, (A i (φ i))ᵢ)`. -/
private theorem mem_adjoint_of_mem_directSumDomain (hT : IsDirectSumOperator A T)
    {φ : lp G 2} (hφ : φ ∈ directSumDomain A) : φ ∈ (T†).domain := by
  classical
  have hd := hasDenseDomain_of_isDirectSumOperator hT
  have hsum : Summable fun i => ‖A i (φ i)‖ ^ 2 :=
    hφ.of_nonneg_of_le (fun _ => by positivity) fun i => le_add_of_nonneg_left (by positivity)
  let χ : lp G 2 := ⟨fun i => A i (φ i), memℓp_two_of_summable hsum⟩
  have hle : T ≤ T† := (isSymmetric_iff_le_adjoint hd).mp hT.isSymmetric
  have hmem : (φ, χ) ∈ T†.graph :=
    (LinearPMap.adjoint_isClosed hd).mem_of_tendsto
      ((lp.hasSum_single (by norm_num) φ).prodMk_nhds (lp.hasSum_single (by norm_num) χ))
      (Eventually.of_forall fun s => LinearPMap.le_graph_of_le hle (sum_single_mem_graph hT s φ))
  exact LinearPMap.mem_domain_of_mem_graph hmem

/--
A componentwise operator built from bounded self-adjoint pieces is essentially
self-adjoint.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem isEssentiallySelfAdjoint_of_isDirectSumOperator (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) : IsEssentiallySelfAdjoint T := by
  classical
  exact (isEssentiallySelfAdjoint_iff_dense_range (hasDenseDomain_of_isDirectSumOperator hT)
    hT.isSymmetric).mpr
    ⟨dense_of_single_mem _ (single_mem_range_subSmul hA hT (by simp)),
      dense_of_single_mem _ (single_mem_range_subSmul hA hT (by simp))⟩

/-- The closure of a componentwise operator is its adjoint. -/
private theorem closure_eq_adjoint_of_isDirectSumOperator (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) : T.closure = T† := by
  have h := isEssentiallySelfAdjoint_of_isDirectSumOperator hA hT
  rw [← adjoint_closure_eq_adjoint (hasDenseDomain_of_isDirectSumOperator hT) h.isClosable]
  exact (LinearPMap.isSelfAdjoint_def.mp h.isSelfAdjoint_closure).symm

/--
The domain of the closure is the maximal domain `V`.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem domain_closure_eq_directSumDomain (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) :
    (T.closure.domain : Set (lp G 2)) = directSumDomain A := by
  rw [closure_eq_adjoint_of_isDirectSumOperator hA hT]
  exact Set.ext fun _ => ⟨mem_directSumDomain_of_mem_adjoint hA hT,
    mem_adjoint_of_mem_directSumDomain hT⟩

/--
The domain of the adjoint is the maximal domain `V`.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem domain_adjoint_eq_directSumDomain (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) :
    ((T†).domain : Set (lp G 2)) = directSumDomain A :=
  Set.ext fun _ => ⟨mem_directSumDomain_of_mem_adjoint hA hT,
    mem_adjoint_of_mem_directSumDomain hT⟩

/--
On `V`, the closure acts componentwise by `A`.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem closure_apply_eq_of_isDirectSumOperator (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) (ψ : T.closure.domain) (i : ι) :
    (T.closure ψ) i = A i ((ψ : lp G 2) i) := by
  have key : ∀ S : lp G 2 →ₗ.[ℂ] lp G 2, S = T† → ∀ ψ : S.domain,
      (S ψ) i = A i ((ψ : lp G 2) i) := by
    rintro S rfl ψ
    exact adjoint_apply_component hA hT ψ i
  exact key _ (closure_eq_adjoint_of_isDirectSumOperator hA hT) ψ

/--
On `V`, the adjoint acts componentwise by `A`.

Blueprint reference: `prpstn:hall-9.26`.
-/
theorem adjoint_apply_eq_of_isDirectSumOperator (hA : ∀ i, IsSelfAdjoint (A i))
    (hT : IsDirectSumOperator A T) (ψ : (T†).domain) (i : ι) :
    (T† ψ) i = A i ((ψ : lp G 2) i) :=
  adjoint_apply_component hA hT ψ i

end DirectSumOperator

/-!
### Componentwise self-adjoint operators, internal form
-/

section InternalDirectSumOperator

variable {K : ℕ → Submodule ℂ H} [∀ n, CompleteSpace (K n)]

/--
The maximal domain for the internal componentwise operator determined by a family `A` of
bounded operators on the summands.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
def internalDomain (K : ℕ → Submodule ℂ H) (A : ∀ n, (K n) →L[ℂ] (K n)) : Set H :=
  {ψ | ∃ f : ∀ n, K n, HasSum (fun n => (f n : H)) ψ ∧
    Summable fun n => ‖(f n : H)‖ ^ 2 + ‖(A n (f n) : H)‖ ^ 2}

/--
`T` is the internal componentwise operator determined by `A`: symmetric, defined at least
on the algebraic span `W₀` of the summands, and acting there by `A` summandwise.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
structure IsInternalDirectSumOperator (A : ∀ n, (K n) →L[ℂ] (K n))
    (T : H →ₗ.[ℂ] H) : Prop where
  /-- `T` is symmetric. -/
  isSymmetric : IsSymmetric T
  /-- Every finite sum of elements of the summands lies in `Dom(T)`. -/
  memDomain : ∀ (N : ℕ) (η : ∀ n, K n), (∑ n ∈ Finset.range N, (η n : H)) ∈ T.domain
  /-- On such a finite sum, `T` acts summandwise by `A`. -/
  apply_eq : ∀ (N : ℕ) (η : ∀ n, K n),
    T ⟨∑ n ∈ Finset.range N, (η n : H), memDomain N η⟩ =
      ∑ n ∈ Finset.range N, (A n (η n) : H)

variable {A : ∀ n, (K n) →L[ℂ] (K n)} {T : H →ₗ.[ℂ] H}

omit [CompleteSpace H] [∀ n, CompleteSpace (K n)] in
/-- A vector of the summand `K m` is the finite sum of the family `Pi.single m η`. -/
private theorem sum_range_single_eq (m : ℕ) (η : K m) :
    ∑ n ∈ Finset.range (m + 1), (((Pi.single m η : ∀ n, K n) n : K n) : H) = η := by
  rw [Finset.sum_eq_single m (fun n _ hn => by simp [Pi.single_eq_of_ne hn])
    (fun h => absurd (Finset.self_mem_range_succ m) h), Pi.single_eq_same]

omit [CompleteSpace H] [∀ n, CompleteSpace (K n)] in
/-- Each summand lies in the domain of an internal componentwise operator. -/
private theorem mem_domain_of_mem_summand (hT : IsInternalDirectSumOperator A T) (m : ℕ)
    (η : K m) : (η : H) ∈ T.domain :=
  sum_range_single_eq m η ▸ hT.memDomain _ _

omit [CompleteSpace H] [∀ n, CompleteSpace (K n)] in
/-- An internal componentwise operator acts on the summand `K m` by `A m`. -/
private theorem apply_of_mem_summand (hT : IsInternalDirectSumOperator A T) (m : ℕ)
    (η : K m) : T ⟨η, mem_domain_of_mem_summand hT m η⟩ = A m η := by
  have h : (⟨η, mem_domain_of_mem_summand hT m η⟩ : T.domain) =
      ⟨_, hT.memDomain (m + 1) (Pi.single m η)⟩ := Subtype.ext (sum_range_single_eq m η).symm
  rw [h, hT.apply_eq, ← sum_range_single_eq m (A m η)]
  exact Finset.sum_congr rfl fun n _ => by rw [Pi.apply_single (fun n => A n) (by simp)]

omit [CompleteSpace H] [∀ n, CompleteSpace (K n)] in
/-- A submodule of `H` containing every summand is dense. -/
private theorem dense_of_summand_mem (hK : IsInternalOrthogonalDecomposition K)
    (S : Submodule ℂ H) (h : ∀ m (η : K m), (η : H) ∈ S) : Dense (S : Set H) := fun ψ => by
  obtain ⟨f, hf⟩ := hK.exists_hasSum ψ
  exact mem_closure_of_tendsto hf.tendsto_sum_nat
    (Eventually.of_forall fun N => S.sum_mem fun n _ => h n (f n))

omit [CompleteSpace H] [∀ n, CompleteSpace (K n)] in
/-- An internal componentwise operator is densely defined. -/
private theorem hasDenseDomain_of_isInternalDirectSumOperator
    (hK : IsInternalOrthogonalDecomposition K) (hT : IsInternalDirectSumOperator A T) :
    HasDenseDomain T :=
  dense_of_summand_mem hK T.domain (mem_domain_of_mem_summand hT)

omit [CompleteSpace H] in
/-- The range of `T - c 1` contains every summand for non-real `c`. -/
private theorem summand_mem_range_subSmul (hA : ∀ n, IsSelfAdjoint (A n))
    (hT : IsInternalDirectSumOperator A T) {c : ℂ} (hc : c.im ≠ 0) (m : ℕ) (η : K m) :
    (η : H) ∈ range (subSmul T c) := by
  obtain ⟨ξ, hξ⟩ := exists_sub_smul_eq_of_isSelfAdjoint (hA m) hc η
  refine mem_range.mpr ⟨⟨ξ, mem_domain_of_mem_summand hT m ξ⟩, ?_⟩
  rw [subSmul_apply]
  erw [apply_of_mem_summand hT m ξ]
  simp [← hξ]

omit [CompleteSpace H] [∀ n, CompleteSpace (K n)] in
/-- Inner products with a vector of `K m` only see the `m`-th component. -/
private theorem inner_eq_inner_component (hK : IsInternalOrthogonalDecomposition K) {x : H}
    {g : ∀ n, K n} (hg : HasSum (fun n => (g n : H)) x) (m : ℕ) (η : K m) :
    ⟪x, (η : H)⟫_ℂ = ⟪(g m : H), η⟫_ℂ := by
  rw [← inner_conj_symm, ← inner_conj_symm (g m : H)]
  congr 1
  refine (hg.mapL (innerSL ℂ (η : H))).unique ?_
  simpa using hasSum_single (f := fun n => ⟪(η : H), (g n : H)⟫_ℂ) m
    fun n hn => hK.orthogonal (Ne.symm hn) _ η.2 _ (g n).2

/-- The components of `T† φ` are `A n` applied to the components of `φ`. -/
private theorem adjoint_component_eq (hK : IsInternalOrthogonalDecomposition K)
    (hA : ∀ n, IsSelfAdjoint (A n)) (hT : IsInternalDirectSumOperator A T)
    (φ : (T†).domain) {f g : ∀ n, K n} (hf : HasSum (fun n => (f n : H)) (φ : H))
    (hg : HasSum (fun n => (g n : H)) (T† φ)) : g = fun n => A n (f n) := by
  have hd := hasDenseDomain_of_isInternalDirectSumOperator hK hT
  funext m
  refine ext_inner_right ℂ fun η => ?_
  have h : ⟪T† φ, (η : H)⟫_ℂ = ⟪(φ : H), T ⟨η, mem_domain_of_mem_summand hT m η⟩⟫_ℂ :=
    LinearPMap.adjoint_isFormalAdjoint hd φ ⟨η, _⟩
  rw [apply_of_mem_summand hT, inner_eq_inner_component hK hg,
    inner_eq_inner_component hK hf] at h
  rw [Submodule.coe_inner, h, ← Submodule.coe_inner, ← ContinuousLinearMap.adjoint_inner_left,
    (hA m).adjoint_eq]

/-- The adjoint of an internal componentwise operator is `∑ₙ Aₙ φₙ`. -/
private theorem hasSum_adjoint_apply_aux (hK : IsInternalOrthogonalDecomposition K)
    (hA : ∀ n, IsSelfAdjoint (A n)) (hT : IsInternalDirectSumOperator A T)
    (φ : (T†).domain) {f : ∀ n, K n} (hf : HasSum (fun n => (f n : H)) (φ : H)) :
    HasSum (fun n => (A n (f n) : H)) (T† φ) := by
  obtain ⟨g, hg⟩ := hK.exists_hasSum (T† φ)
  rwa [adjoint_component_eq hK hA hT φ hf hg] at hg

/-- The domain of the adjoint of an internal componentwise operator lies in `V`. -/
private theorem mem_internalDomain_of_mem_adjoint (hK : IsInternalOrthogonalDecomposition K)
    (hA : ∀ n, IsSelfAdjoint (A n)) (hT : IsInternalDirectSumOperator A T) {φ : H}
    (hφ : φ ∈ (T†).domain) : φ ∈ internalDomain K A := by
  obtain ⟨f, hf⟩ := hK.exists_hasSum φ
  exact ⟨f, hf, (hasSum_norm_sq_of_isInternalOrthogonalDecomposition hK hf).summable.add
    (hasSum_norm_sq_of_isInternalOrthogonalDecomposition hK
      (hasSum_adjoint_apply_aux hK hA hT ⟨φ, hφ⟩ hf)).summable⟩

omit [∀ n, CompleteSpace (K n)] in
/-- `V` lies in the domain of the adjoint: `T†` is closed and extends `T`, whose graph
approximates `(ψ, ∑ₙ Aₙ ψₙ)`. -/
private theorem mem_adjoint_of_mem_internalDomain (hK : IsInternalOrthogonalDecomposition K)
    (hT : IsInternalDirectSumOperator A T) {ψ : H} (hψ : ψ ∈ internalDomain K A) :
    ψ ∈ (T†).domain := by
  obtain ⟨f, hf, hs⟩ := hψ
  have hd := hasDenseDomain_of_isInternalDirectSumOperator hK hT
  have hsum : Summable fun n => ‖(A n (f n) : H)‖ ^ 2 :=
    hs.of_nonneg_of_le (fun _ => by positivity) fun n => le_add_of_nonneg_left (by positivity)
  have hχ : Summable fun n => (A n (f n) : H) :=
    ((orthogonalFamily_of_isInternalOrthogonalDecomposition hK).summable_iff_norm_sq_summable
      _).mpr (by simpa using hsum)
  have hle : T ≤ T† := (isSymmetric_iff_le_adjoint hd).mp hT.isSymmetric
  have hmem : (ψ, ∑' n, (A n (f n) : H)) ∈ T†.graph :=
    (LinearPMap.adjoint_isClosed hd).mem_of_tendsto
      (hf.tendsto_sum_nat.prodMk_nhds hχ.hasSum.tendsto_sum_nat)
      (Eventually.of_forall fun N => LinearPMap.le_graph_of_le hle (by
        have := T.mem_graph ⟨_, hT.memDomain N f⟩
        rwa [hT.apply_eq] at this))
  exact LinearPMap.mem_domain_of_mem_graph hmem

/--
The internal form of `prpstn:hall-9.26`: essential self-adjointness.

Remark: the instance `[∀ n, CompleteSpace (K n)]` (needed for `IsSelfAdjoint (A n)`, which
uses the Hilbert adjoint on `K n →L[ℂ] K n`) is not a restriction: it follows from `hK.isClosed`
via `IsClosed.completeSpace_coe`, so a caller can always supply it with `haveI`.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem isEssentiallySelfAdjoint_of_isInternalDirectSumOperator
    (hK : IsInternalOrthogonalDecomposition K) (hA : ∀ n, IsSelfAdjoint (A n))
    (hT : IsInternalDirectSumOperator A T) : IsEssentiallySelfAdjoint T :=
  (isEssentiallySelfAdjoint_iff_dense_range (hasDenseDomain_of_isInternalDirectSumOperator hK hT)
    hT.isSymmetric).mpr
    ⟨dense_of_summand_mem hK _ (summand_mem_range_subSmul hA hT (by simp)),
      dense_of_summand_mem hK _ (summand_mem_range_subSmul hA hT (by simp))⟩

/-- The closure of an internal componentwise operator is its adjoint. -/
private theorem closure_eq_adjoint_of_isInternalDirectSumOperator
    (hK : IsInternalOrthogonalDecomposition K) (hA : ∀ n, IsSelfAdjoint (A n))
    (hT : IsInternalDirectSumOperator A T) : T.closure = T† := by
  have h := isEssentiallySelfAdjoint_of_isInternalDirectSumOperator hK hA hT
  rw [← adjoint_closure_eq_adjoint (hasDenseDomain_of_isInternalDirectSumOperator hK hT)
    h.isClosable]
  exact (LinearPMap.isSelfAdjoint_def.mp h.isSelfAdjoint_closure).symm

/--
The domain of the closure is the maximal internal domain.

Remark: the instance `[∀ n, CompleteSpace (K n)]` (needed for `IsSelfAdjoint (A n)`, which
uses the Hilbert adjoint on `K n →L[ℂ] K n`) is not a restriction: it follows from `hK.isClosed`
via `IsClosed.completeSpace_coe`, so a caller can always supply it with `haveI`.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem domain_closure_eq_internalDomain (hK : IsInternalOrthogonalDecomposition K)
    (hA : ∀ n, IsSelfAdjoint (A n)) (hT : IsInternalDirectSumOperator A T) :
    (T.closure.domain : Set H) = internalDomain K A := by
  rw [closure_eq_adjoint_of_isInternalDirectSumOperator hK hA hT]
  exact Set.ext fun _ => ⟨mem_internalDomain_of_mem_adjoint hK hA hT,
    mem_adjoint_of_mem_internalDomain hK hT⟩

/--
The domain of the adjoint is the maximal internal domain.

Remark: the instance `[∀ n, CompleteSpace (K n)]` (needed for `IsSelfAdjoint (A n)`, which
uses the Hilbert adjoint on `K n →L[ℂ] K n`) is not a restriction: it follows from `hK.isClosed`
via `IsClosed.completeSpace_coe`, so a caller can always supply it with `haveI`.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem domain_adjoint_eq_internalDomain (hK : IsInternalOrthogonalDecomposition K)
    (hA : ∀ n, IsSelfAdjoint (A n)) (hT : IsInternalDirectSumOperator A T) :
    ((T†).domain : Set H) = internalDomain K A :=
  Set.ext fun _ => ⟨mem_internalDomain_of_mem_adjoint hK hA hT,
    mem_adjoint_of_mem_internalDomain hK hT⟩

/--
On the maximal internal domain, the closure is given by the norm-convergent sum
`∑ₙ Aₙ ψₙ`.

Remark: the instance `[∀ n, CompleteSpace (K n)]` (needed for `IsSelfAdjoint (A n)`, which
uses the Hilbert adjoint on `K n →L[ℂ] K n`) is not a restriction: it follows from `hK.isClosed`
via `IsClosed.completeSpace_coe`, so a caller can always supply it with `haveI`.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem hasSum_closure_apply_of_isInternalDirectSumOperator
    (hK : IsInternalOrthogonalDecomposition K) (hA : ∀ n, IsSelfAdjoint (A n))
    (hT : IsInternalDirectSumOperator A T) (ψ : T.closure.domain) {f : ∀ n, K n}
    (hf : HasSum (fun n => (f n : H)) (ψ : H)) :
    HasSum (fun n => (A n (f n) : H)) (T.closure ψ) := by
  have key : ∀ S : H →ₗ.[ℂ] H, S = T† → ∀ ψ : S.domain,
      HasSum (fun n => (f n : H)) (ψ : H) → HasSum (fun n => (A n (f n) : H)) (S ψ) := by
    rintro S rfl ψ hf
    exact hasSum_adjoint_apply_aux hK hA hT ψ hf
  exact key _ (closure_eq_adjoint_of_isInternalDirectSumOperator hK hA hT) ψ hf

/--
The same formula for the adjoint.

Remark: the instance `[∀ n, CompleteSpace (K n)]` (needed for `IsSelfAdjoint (A n)`, which
uses the Hilbert adjoint on `K n →L[ℂ] K n`) is not a restriction: it follows from `hK.isClosed`
via `IsClosed.completeSpace_coe`, so a caller can always supply it with `haveI`.

Blueprint reference: `prpstn:hall-9.26-internal`.
-/
theorem hasSum_adjoint_apply_of_isInternalDirectSumOperator
    (hK : IsInternalOrthogonalDecomposition K) (hA : ∀ n, IsSelfAdjoint (A n))
    (hT : IsInternalDirectSumOperator A T) (ψ : (T†).domain) {f : ∀ n, K n}
    (hf : HasSum (fun n => (f n : H)) (ψ : H)) :
    HasSum (fun n => (A n (f n) : H)) (T† ψ) :=
  hasSum_adjoint_apply_aux hK hA hT ψ hf

end InternalDirectSumOperator

end Unbounded
end Spectral
end Physicslib4
