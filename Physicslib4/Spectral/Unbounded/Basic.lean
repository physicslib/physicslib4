/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap
import Physicslib4.Spectral.Basic

/-!
# Unbounded operators: adjoint, symmetry, self-adjointness and closure

This file formalizes the first part of the blueprint section on unbounded spectral
theorems: the basic theory of an *unbounded operator* on a separable complex Hilbert
space `H`.

The blueprint's unbounded operator `A : Dom(A) → H`, with `Dom(A)` a dense subspace of
`H`, is Mathlib's partially defined linear map `T : H →ₗ.[ℂ] H` together with the
hypothesis `HasDenseDomain T`. Its adjoint is Mathlib's `LinearPMap.adjoint` (notation
`T†`), "`A` is an extension of `B`" is `B ≤ T`, and closedness/closability/closure are
Mathlib's `LinearPMap.IsClosed`, `LinearPMap.IsClosable` and `LinearPMap.closure`.
Self-adjointness is `_root_.IsSelfAdjoint` for the `Star` instance on `H →ₗ.[ℂ] H`,
which is `T† = T`.

## Main definitions

* `Physicslib4.Spectral.Unbounded.HasDenseDomain` — the blueprint's standing hypothesis
  on an unbounded operator.
* `Physicslib4.Spectral.Unbounded.IsSymmetric` — `⟪φ, T ψ⟫ = ⟪T φ, ψ⟫` on `Dom(T)`.
* `Physicslib4.Spectral.Unbounded.IsEssentiallySelfAdjoint` — symmetric, closable, with
  self-adjoint closure.
* `Physicslib4.Spectral.Unbounded.ker`, `Physicslib4.Spectral.Unbounded.range` — kernel
  and range of an unbounded operator, as subspaces of `H`.
* `Physicslib4.Spectral.Unbounded.subSmul` — the operator `T - λ 1` with domain `Dom(T)`.

## Main statements

* `existsUnique_adjoint_apply` — the adjoint is well defined.
* `mem_adjoint_domain_iff_exists`, `adjoint_apply_eq_of_forall_inner` — membership in
  `Dom(T*)` via an exact representation.
* `isSymmetric_iff_le_adjoint` — `T` is symmetric iff `T*` extends `T`.
* `mem_domain_closure_iff`, `closure_apply_eq_of_tendsto`, `closure_le_of_isClosed` —
  the sequential description of the closure, and its minimality.
* `isClosable_of_isSymmetric`, `adjoint_closure_eq_adjoint`,
  `adjoint_le_adjoint_of_le`, `existsUnique_isSelfAdjoint_extension`,
  `eq_closure_of_isSelfAdjoint_of_le`.
* `orthogonal_range_eq_ker_adjoint` — `Range(T)ᗮ = Ker(T*)`.
* `adjoint_add_toPMap`, `isSelfAdjoint_add_of_isSelfAdjoint` — adjoint of a sum with a
  bounded operator.
* `isClosed_range_subSmul` — a uniform lower bound forces `Range(T - λ 1)` to be closed.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
The blueprint's *unbounded operator* on `H` is a linear map defined on a dense subspace
of `H`. In Lean the underlying partial linear map is `T : H →ₗ.[ℂ] H`, and the density
requirement on its domain is this predicate, carried as an explicit hypothesis wherever
the blueprint's `Dom(A)` is required to be dense.

Note that "unbounded" means "not necessarily bounded": the everywhere-defined bounded
case is included.

Blueprint reference: `def:hall-3.1`.
-/
def HasDenseDomain (T : H →ₗ.[ℂ] H) : Prop := Dense (T.domain : Set H)

/-!
### The adjoint

The blueprint's `Dom(A*)` is the set of `φ` for which `ψ ↦ ⟪φ, A ψ⟫` is bounded on
`Dom(A)`; this is Mathlib's `LinearPMap.adjointDomain`, phrased there as continuity of
that functional, and `A*` itself is `LinearPMap.adjoint`, written `T†`.
-/

/--
The adjoint is well defined: for `φ` in `Dom(T*)` there is exactly one vector `χ` with
`⟪φ, T ψ⟫ = ⟪χ, ψ⟫` for all `ψ ∈ Dom(T)`.

Blueprint reference: `prpstn:adjoint-well-defined`.
-/
theorem existsUnique_adjoint_apply {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) {φ : H}
    (hφ : φ ∈ (T†).domain) :
    ∃! χ : H, ∀ ψ : T.domain, ⟪φ, T ψ⟫_ℂ = ⟪χ, (ψ : H)⟫_ℂ :=
  ⟨T† ⟨φ, hφ⟩, fun ψ => (LinearPMap.adjoint_isFormalAdjoint hT ⟨φ, hφ⟩ ψ).symm,
    fun _ hχ' => (LinearPMap.adjoint_apply_eq hT ⟨φ, hφ⟩ fun x => (hχ' x).symm).symm⟩

/--
A linear combination of vectors in `Dom(T*)` again lies in `Dom(T*)`.

Together with `adjoint_smul_add` this is the blueprint's linearity of the adjoint; in
Lean it is already carried by the fact that `T†` is a `LinearPMap`, whose domain is a
submodule and whose action is linear.

Blueprint reference: `prpstn:hall-linearity-of-the-adjoint`.
-/
theorem smul_add_mem_adjoint_domain {T : H →ₗ.[ℂ] H} (α β : ℂ) {φ₁ φ₂ : H}
    (h₁ : φ₁ ∈ (T†).domain) (h₂ : φ₂ ∈ (T†).domain) : α • φ₁ + β • φ₂ ∈ (T†).domain :=
  add_mem (Submodule.smul_mem _ α h₁) (Submodule.smul_mem _ β h₂)

/--
The adjoint acts linearly on its domain.

Blueprint reference: `prpstn:hall-linearity-of-the-adjoint`.
-/
theorem adjoint_smul_add {T : H →ₗ.[ℂ] H} (α β : ℂ) (φ₁ φ₂ : (T†).domain)
    (h : α • (φ₁ : H) + β • (φ₂ : H) ∈ (T†).domain) :
    T† ⟨α • (φ₁ : H) + β • (φ₂ : H), h⟩ = α • T† φ₁ + β • T† φ₂ := by
  change T† (α • φ₁ + β • φ₂) = _
  rw [LinearPMap.map_add, LinearPMap.map_smul, LinearPMap.map_smul]

/--
A vector `ψ` lies in `Dom(T*)` exactly when the functional `χ ↦ ⟪ψ, T χ⟫` is *exactly*
represented by some vector `φ`; boundedness need not be checked directly.

Blueprint reference: `lmm:characterizing-adjoint-domain-membership`.
-/
theorem mem_adjoint_domain_iff_exists {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (ψ : H) :
    ψ ∈ (T†).domain ↔ ∃ φ : H, ∀ χ : T.domain, ⟪ψ, T χ⟫_ℂ = ⟪φ, (χ : H)⟫_ℂ :=
  ⟨fun hψ => ⟨T† ⟨ψ, hψ⟩, fun χ => (LinearPMap.adjoint_isFormalAdjoint hT ⟨ψ, hψ⟩ χ).symm⟩,
    fun ⟨φ, hφ⟩ => LinearPMap.mem_adjoint_domain_of_exists ψ ⟨φ, fun χ => (hφ χ).symm⟩⟩

/--
The representing vector in `mem_adjoint_domain_iff_exists` is `T* ψ`.

Blueprint reference: `lmm:characterizing-adjoint-domain-membership`.
-/
theorem adjoint_apply_eq_of_forall_inner {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) {ψ : H}
    (hψ : ψ ∈ (T†).domain) {φ : H}
    (h : ∀ χ : T.domain, ⟪ψ, T χ⟫_ℂ = ⟪φ, (χ : H)⟫_ℂ) : T† ⟨ψ, hψ⟩ = φ :=
  LinearPMap.adjoint_apply_eq hT ⟨ψ, hψ⟩ fun χ => (h χ).symm

/-- `φ` represents `χ ↦ ⟪ψ, T χ⟫` exactly when `ψ ∈ Dom(T*)` and `T* ψ = φ`. -/
private theorem forall_inner_iff_adjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) {ψ φ : H} :
    (∀ χ : T.domain, ⟪ψ, T χ⟫_ℂ = ⟪φ, (χ : H)⟫_ℂ) ↔ ∃ hψ : ψ ∈ T†.domain, T† ⟨ψ, hψ⟩ = φ :=
  ⟨fun h => ⟨_, adjoint_apply_eq_of_forall_inner hT
      ((mem_adjoint_domain_iff_exists hT ψ).mpr ⟨φ, h⟩) h⟩,
    fun ⟨hψ, e⟩ χ => e ▸ (LinearPMap.adjoint_isFormalAdjoint hT ⟨ψ, hψ⟩ χ).symm⟩

/-- To identify `S*` with `A` it suffices that `φ` represents `χ ↦ ⟪ψ, S χ⟫` exactly when
`ψ ∈ Dom(A)` and `A ψ = φ`. -/
private theorem adjoint_eq_of_forall_inner_iff {S A : H →ₗ.[ℂ] H} (hS : HasDenseDomain S)
    (h : ∀ ψ φ : H, (∀ χ : S.domain, ⟪ψ, S χ⟫_ℂ = ⟪φ, (χ : H)⟫_ℂ) ↔
      ∃ hψ : ψ ∈ A.domain, A ⟨ψ, hψ⟩ = φ) :
    S† = A := by
  have e : ∀ ψ φ, (∃ hψ : ψ ∈ S†.domain, S† ⟨ψ, hψ⟩ = φ) ↔ ∃ hψ : ψ ∈ A.domain, A ⟨ψ, hψ⟩ = φ :=
    fun ψ φ => (forall_inner_iff_adjoint hS).symm.trans (h ψ φ)
  refine LinearPMap.ext (Submodule.ext fun ψ =>
    ⟨fun hψ => ((e ψ _).mp ⟨hψ, rfl⟩).1, fun hψ => ((e ψ _).mpr ⟨hψ, rfl⟩).1⟩)
    fun x _ hx => ((e x _).mpr ⟨hx, rfl⟩).2

/-!
### Symmetric, self-adjoint and essentially self-adjoint operators
-/

/--
An unbounded operator `T` is *symmetric* if `⟪φ, T ψ⟫ = ⟪T φ, ψ⟫` for all `φ, ψ` in
`Dom(T)`.

Blueprint reference: `def:hall-9.2`.
-/
def IsSymmetric (T : H →ₗ.[ℂ] H) : Prop :=
  ∀ φ ψ : T.domain, ⟪(φ : H), T ψ⟫_ℂ = ⟪T φ, (ψ : H)⟫_ℂ

omit [CompleteSpace H] in
/--
Symmetry in the sense of `IsSymmetric` is Mathlib's `LinearPMap.IsFormalAdjoint` of `T`
with itself.

Blueprint reference: `def:hall-9.2`.
-/
theorem isSymmetric_iff_isFormalAdjoint {T : H →ₗ.[ℂ] H} :
    IsSymmetric T ↔ T.IsFormalAdjoint T := by
  constructor <;> intro h x y <;> exact (h x y).symm

/--
An unbounded operator is symmetric if and only if its adjoint is an extension of it.

Blueprint reference: `prpstn:hall-9.4`.
-/
theorem isSymmetric_iff_le_adjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) :
    IsSymmetric T ↔ T ≤ T† := by
  refine ⟨fun hsym => (isSymmetric_iff_isFormalAdjoint.mp hsym).le_adjoint hT,
    fun hle φ ψ => ?_⟩
  rw [LinearPMap.apply_comp_inclusion hle φ]
  exact (LinearPMap.adjoint_isFormalAdjoint hT (Submodule.inclusion hle.1 φ) ψ).symm

/-!
### The closure of an unbounded operator

The blueprint's graph `Γ(A) ⊂ H × H` is Mathlib's `LinearPMap.graph`, closedness and
closability are `LinearPMap.IsClosed` and `LinearPMap.IsClosable`, and `A^cl` is
`LinearPMap.closure`.
-/

omit [CompleteSpace H] in
/--
Sequential description of closedness for a linear map on a (not necessarily dense)
subspace: `T` is closed (Mathlib's `LinearPMap.IsClosed`, i.e. its graph is closed in
`H × H`) iff whenever `ψ n ∈ Dom(T)` with `ψ n → ψ` and `T ψ n → φ`, then `ψ ∈ Dom(T)` and
`T ψ = φ`. No density of `Dom(T)` is assumed.

Blueprint reference: `def:closed-linear-map-on-a-subspace`.
-/
theorem isClosed_iff_forall_tendsto {T : H →ₗ.[ℂ] H} :
    T.IsClosed ↔
      ∀ (χ : ℕ → T.domain) (ψ φ : H), Tendsto (fun n => (χ n : H)) atTop (𝓝 ψ) →
        Tendsto (fun n => T (χ n)) atTop (𝓝 φ) → ∃ hψ : ψ ∈ T.domain, T ⟨ψ, hψ⟩ = φ := by
  refine ⟨fun h χ ψ φ hχ hTχ => ?_, fun h => isSeqClosed_iff_isClosed.mp fun {u p} hu hp => ?_⟩
  · obtain ⟨⟨y, hy⟩, rfl, rfl⟩ := T.mem_graph_iff.mp <| h.mem_of_tendsto (hχ.prodMk_nhds hTχ)
      (Eventually.of_forall fun n => T.mem_graph (χ n))
    exact ⟨hy, rfl⟩
  · choose χ hχ₁ hχ₂ using fun n => T.mem_graph_iff.mp (hu n)
    obtain ⟨hψ, e⟩ := h χ p.1 p.2
      (by simpa only [hχ₁] using hp.fst_nhds) (by simpa only [hχ₂] using hp.snd_nhds)
    exact T.mem_graph_iff.mpr ⟨⟨p.1, hψ⟩, rfl, e⟩

omit [CompleteSpace H] in
/--
The closure of a densely defined closable operator again has dense domain, so it is
again an unbounded operator in the blueprint's sense.

Blueprint reference: `prpstn:closure-linearity-and-sequential-description` (Part 1).
-/
theorem hasDenseDomain_closure {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (_hc : T.IsClosable) : HasDenseDomain T.closure :=
  Dense.mono (SetLike.coe_subset_coe.mpr (T.le_closure).1) hT

omit [CompleteSpace H] in
/-- The graph of `T^cl` is the closure of the graph of `T`, as a set. -/
private theorem coe_graph_closure {T : H →ₗ.[ℂ] H} (hc : T.IsClosable) :
    (T.closure.graph : Set (H × H)) = closure (T.graph : Set (H × H)) := by
  rw [← hc.graph_closure_eq_closure_graph, Submodule.topologicalClosure_coe]

omit [CompleteSpace H] in
/-- A limit of graph points `(χ n, T χ n)` lies in the closure of the graph of `T`. -/
private theorem mem_closure_graph_of_tendsto {T : H →ₗ.[ℂ] H} {ξ η : H} {χ : ℕ → T.domain}
    (hχ : Tendsto (fun n => (χ n : H)) atTop (𝓝 ξ))
    (hTχ : Tendsto (fun n => T (χ n)) atTop (𝓝 η)) :
    (ξ, η) ∈ closure (T.graph : Set (H × H)) :=
  mem_closure_of_tendsto (hχ.prodMk_nhds hTχ) (Eventually.of_forall fun n => T.mem_graph (χ n))

omit [CompleteSpace H] in
/-- A closed condition on `H × H` that holds on the graph of `T` holds on the graph of
`T^cl`. -/
private theorem closure_graph_induction {T : H →ₗ.[ℂ] H} (hc : T.IsClosable)
    {P : H × H → Prop} (hP : IsClosed {p | P p}) (h : ∀ χ : T.domain, P ((χ : H), T χ))
    (ξ : T.closure.domain) : P ((ξ : H), T.closure ξ) := by
  refine closure_minimal (s := (T.graph : Set (H × H))) ?_ hP ?_
  · rintro ⟨a, b⟩ hp
    obtain ⟨χ, rfl, rfl⟩ := T.mem_graph_iff.mp hp
    exact h χ
  · rw [← coe_graph_closure hc]
    exact T.closure.mem_graph ξ

omit [CompleteSpace H] in
/--
Sequential description of the domain of the closure: `ξ ∈ Dom(T^cl)` exactly when there
is a sequence in `Dom(T)` converging to `ξ` whose image under `T` also converges.

Blueprint reference: `prpstn:closure-linearity-and-sequential-description` (Part 2).
-/
theorem mem_domain_closure_iff {T : H →ₗ.[ℂ] H} (hc : T.IsClosable) (ξ : H) :
    ξ ∈ T.closure.domain ↔
      ∃ (χ : ℕ → T.domain) (η : H),
        Tendsto (fun n => (χ n : H)) atTop (𝓝 ξ) ∧ Tendsto (fun n => T (χ n)) atTop (𝓝 η) := by
  constructor
  · intro hξ
    have h1 : (ξ, T.closure ⟨ξ, hξ⟩) ∈ closure (T.graph : Set (H × H)) := by
      rw [← coe_graph_closure hc]
      exact T.closure.mem_graph ⟨ξ, hξ⟩
    obtain ⟨s, hs, hstend⟩ := mem_closure_iff_seq_limit.mp h1
    choose χ hχ1 hχ2 using fun n => (T.mem_graph_iff).mp (hs n)
    obtain ⟨hfst, hsnd⟩ := (Prod.tendsto_iff s _).mp hstend
    exact ⟨χ, _, by simpa only [hχ1] using hfst, by simpa only [hχ2] using hsnd⟩
  · rintro ⟨χ, η, hχ, hTχ⟩
    refine LinearPMap.mem_domain_iff.mpr ⟨η, ?_⟩
    rw [← SetLike.mem_coe, coe_graph_closure hc]
    exact mem_closure_graph_of_tendsto hχ hTχ

omit [CompleteSpace H] in
/--
In the situation of `mem_domain_closure_iff`, the limit of `T χ n` is `T^cl ξ`.

Blueprint reference: `prpstn:closure-linearity-and-sequential-description` (Part 2).
-/
theorem closure_apply_eq_of_tendsto {T : H →ₗ.[ℂ] H} (hc : T.IsClosable) {ξ η : H}
    {χ : ℕ → T.domain} (hχ : Tendsto (fun n => (χ n : H)) atTop (𝓝 ξ))
    (hTχ : Tendsto (fun n => T (χ n)) atTop (𝓝 η)) (hξ : ξ ∈ T.closure.domain) :
    T.closure ⟨ξ, hξ⟩ = η := by
  have h2 : (ξ, η) ∈ T.closure.graph := by
    rw [← SetLike.mem_coe, coe_graph_closure hc]
    exact mem_closure_graph_of_tendsto hχ hTχ
  exact T.closure.mem_graph_snd_inj (T.closure.mem_graph ⟨ξ, hξ⟩) h2 rfl

omit [CompleteSpace H] in
/--
`T^cl` is the smallest closed extension of `T`: any closed extension of `T` is an
extension of `T^cl`. (That `T^cl` is itself a closed extension of `T` is Mathlib's
`LinearPMap.le_closure` and `LinearPMap.IsClosable.closure_isClosed`.)

Blueprint reference: `prpstn:closure-linearity-and-sequential-description` (Part 3).
-/
theorem closure_le_of_isClosed {T B : H →ₗ.[ℂ] H} (hc : T.IsClosable) (hTB : T ≤ B)
    (hB : B.IsClosed) : T.closure ≤ B := by
  apply LinearPMap.le_of_le_graph
  calc
    T.closure.graph = T.graph.topologicalClosure := hc.graph_closure_eq_closure_graph.symm
    _ ≤ B.graph.topologicalClosure :=
      Submodule.topologicalClosure_mono (LinearPMap.le_graph_of_le hTB)
    _ = B.graph := IsClosed.submodule_topologicalClosure_eq hB

omit [CompleteSpace H] in
/--
The closure of a symmetric closable operator is symmetric.

Blueprint reference: `lmm:closure-of-symmetric-is-symmetric`.
-/
theorem isSymmetric_closure {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T) (hc : T.IsClosable) :
    IsSymmetric T.closure := by
  -- Pass to the closure in `ψ`, then in `φ`; both identities are closed conditions.
  have step1 (φ : T.domain) (ψ : T.closure.domain) :
      ⟪(φ : H), T.closure ψ⟫_ℂ = ⟪T φ, (ψ : H)⟫_ℂ :=
    closure_graph_induction hc (P := fun p => ⟪(φ : H), p.2⟫_ℂ = ⟪T φ, p.1⟫_ℂ)
      (isClosed_eq (continuous_const.inner continuous_snd)
        (continuous_const.inner continuous_fst)) (hsym φ) ψ
  intro φ ψ
  exact closure_graph_induction hc (P := fun p => ⟪p.1, T.closure ψ⟫_ℂ = ⟪p.2, (ψ : H)⟫_ℂ)
    (isClosed_eq (continuous_fst.inner continuous_const)
      (continuous_snd.inner continuous_const)) (fun χ => step1 χ ψ) φ

/--
An unbounded operator is *essentially self-adjoint* if it is symmetric and closable with
self-adjoint closure.

Blueprint reference: `def:hall-9.7`.
-/
structure IsEssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop where
  /-- `T` is symmetric. -/
  isSymmetric : IsSymmetric T
  /-- `T` is closable. -/
  isClosable : T.IsClosable
  /-- The closure of `T` is self-adjoint. -/
  isSelfAdjoint_closure : IsSelfAdjoint T.closure

/-!
### Elementary properties of adjoints and closed operators
-/

/--
A symmetric operator is always closable.

(Part 1 of the blueprint statement — that the graph of `T*` is closed, with no hypothesis
on `T` beyond dense domain — is Mathlib's `LinearPMap.adjoint_isClosed`.)

Blueprint reference: `prpstn:hall-9.8` (Part 2).
-/
theorem isClosable_of_isSymmetric {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hsym : IsSymmetric T) : T.IsClosable :=
  (LinearPMap.adjoint_isClosed hT).isClosable.leIsClosable ((isSymmetric_iff_le_adjoint hT).mp hsym)

/--
The adjoint of the closure of a closable operator coincides with the adjoint of the
operator itself.

Blueprint reference: `prpstn:hall-9.10`.
-/
theorem adjoint_closure_eq_adjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hc : T.IsClosable) : (T.closure)† = T† := by
  refine adjoint_eq_of_forall_inner_iff (hasDenseDomain_closure hT hc) fun ψ φ =>
    Iff.trans ⟨fun h χ => ?_, fun h => ?_⟩ (forall_inner_iff_adjoint hT)
  · rw [LinearPMap.apply_comp_inclusion T.le_closure χ]
    exact h _
  · exact closure_graph_induction hc (P := fun p => ⟪ψ, p.2⟫_ℂ = ⟪φ, p.1⟫_ℂ)
      (isClosed_eq (continuous_const.inner continuous_snd)
        (continuous_const.inner continuous_fst)) h

/--
Taking adjoints reverses extension: if `C₁` extends `C₂` then `C₂*` extends `C₁*`, i.e.
`Dom(C₁*) ⊆ Dom(C₂*)` and `C₁*`, `C₂*` agree on `Dom(C₁*)`.

The density hypothesis on `Dom(C₂)` (which forces density of `Dom(C₁) ⊇ Dom(C₂)`) is the
blueprint's standing assumption that both are unbounded operators. It cannot be dropped:
Mathlib's `LinearPMap.adjoint` is `0` on all of `H` when the domain is not dense, so for
`C₂` with non-dense domain and `C₁` densely defined the conclusion would say `C₁† ≤ 0`.

Blueprint reference: `lmm:extension-reverses-adjoint-domains`.
-/
theorem adjoint_le_adjoint_of_le {C₁ C₂ : H →ₗ.[ℂ] H} (hC₂ : HasDenseDomain C₂)
    (h : C₂ ≤ C₁) : C₁† ≤ C₂† := by
  have hC₁ : HasDenseDomain C₁ := Dense.mono (SetLike.coe_subset_coe.mpr h.1) hC₂
  have key (x : C₁†.domain) : ∃ hx : (x : H) ∈ C₂†.domain, C₂† ⟨x, hx⟩ = C₁† x :=
    (forall_inner_iff_adjoint hC₂).mp fun χ => by
      rw [LinearPMap.apply_comp_inclusion h χ]
      exact (LinearPMap.adjoint_isFormalAdjoint hC₁ x _).symm
  refine ⟨fun x hx => (key ⟨x, hx⟩).1, fun x y hxy => ?_⟩
  obtain ⟨_, e⟩ := key x
  rw [← e]
  exact congrArg _ (Subtype.ext hxy)

/--
Every self-adjoint extension of an essentially self-adjoint operator `T` is `T^cl`.

Blueprint reference: `prpstn:hall-9.11`.
-/
theorem eq_closure_of_isSelfAdjoint_of_le {T B : H →ₗ.[ℂ] H}
    (h : IsEssentiallySelfAdjoint T) (hB : IsSelfAdjoint B) (hTB : T ≤ B) :
    B = T.closure := by
  have hcl : T.closure ≤ B := closure_le_of_isClosed h.isClosable hTB hB.isClosed
  have hadj := adjoint_le_adjoint_of_le h.isSelfAdjoint_closure.dense_domain hcl
  rw [LinearPMap.isSelfAdjoint_def.mp hB,
    LinearPMap.isSelfAdjoint_def.mp h.isSelfAdjoint_closure] at hadj
  exact le_antisymm hadj hcl

/--
If `T` is essentially self-adjoint, then `T^cl` is the *unique* self-adjoint extension
of `T`. The identification of the witness is `eq_closure_of_isSelfAdjoint_of_le`.

Blueprint reference: `prpstn:hall-9.11`.
-/
theorem existsUnique_isSelfAdjoint_extension {T : H →ₗ.[ℂ] H}
    (h : IsEssentiallySelfAdjoint T) : ∃! B : H →ₗ.[ℂ] H, IsSelfAdjoint B ∧ T ≤ B :=
  ⟨T.closure, ⟨h.isSelfAdjoint_closure, T.le_closure⟩,
    fun _ hB => eq_closure_of_isSelfAdjoint_of_le h hB.1 hB.2⟩

/-!
### Orthogonal complements and density

Part 2 of `prpstn:hall-a.49`, `(Vᗮ)ᗮ = closure V`, is Mathlib's
`Submodule.orthogonal_orthogonal_eq_closure`.
-/

/--
Orthogonal decomposition: if `V` is a closed subspace of `H`, every `ψ` decomposes uniquely
as `ψ = ψ₁ + ψ₂` with `ψ₁ ∈ V` and `ψ₂ ∈ Vᗮ`.

Blueprint reference: `prpstn:hall-a.49` (Part 1).
-/
theorem existsUnique_add_mem_orthogonal {V : Submodule ℂ H} (hV : IsClosed (V : Set H))
    (ψ : H) : ∃! p : H × H, p.1 ∈ V ∧ p.2 ∈ Vᗮ ∧ ψ = p.1 + p.2 := by
  haveI : CompleteSpace V := hV.completeSpace_coe
  refine ⟨(V.starProjection ψ, ψ - V.starProjection ψ),
    ⟨V.starProjection_apply_mem ψ, V.sub_starProjection_mem_orthogonal ψ, by simp⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb, hψ⟩
  have hmem : a - V.starProjection ψ ∈ V ⊓ Vᗮ := by
    refine ⟨V.sub_mem ha (V.starProjection_apply_mem ψ), ?_⟩
    have : a - V.starProjection ψ = (ψ - V.starProjection ψ) - b := by
      rw [hψ]; abel
    rw [this]
    exact Vᗮ.sub_mem (V.sub_starProjection_mem_orthogonal ψ) hb
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
  simp only [Prod.mk.injEq, hmem, true_and]
  rw [← hmem, hψ]; simp

/--
A subspace `V` of `H` is dense if and only if `Vᗮ = {0}`.

Blueprint reference: `crllr:trivial-complement-characterizes-density`.
-/
theorem dense_iff_orthogonal_eq_bot {V : Submodule ℂ H} : Dense (V : Set H) ↔ Vᗮ = ⊥ :=
  V.dense_iff_topologicalClosure_eq_top.trans V.topologicalClosure_eq_top_iff

/--
The adjoint of the bounded operator `λ 1` is `λ̄ 1`.

Blueprint reference: `lmm:adjoint-of-scalar-multiple-of-identity`.
-/
theorem adjoint_smul_id (lam : ℂ) :
    ContinuousLinearMap.adjoint (lam • ContinuousLinearMap.id ℂ H) =
      (starRingEnd ℂ lam) • ContinuousLinearMap.id ℂ H := by
  rw [map_smulₛₗ, ContinuousLinearMap.adjoint_id]

/-!
### Kernel and range
-/

/--
The kernel of an unbounded operator, as a subspace of `H`. A vector outside `Dom(T)` is
never in `Ker(T)`.

Blueprint reference: `def:kernel-of-an-unbounded-operator`.
-/
def ker (T : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (LinearMap.ker T.toFun).map T.domain.subtype

omit [CompleteSpace H] in
@[simp]
theorem mem_ker {T : H →ₗ.[ℂ] H} {ψ : H} :
    ψ ∈ ker T ↔ ∃ h : ψ ∈ T.domain, T ⟨ψ, h⟩ = 0 :=
  ⟨fun ⟨⟨_, hx⟩, hk, he⟩ => he ▸ ⟨hx, hk⟩, fun ⟨h, h0⟩ => ⟨⟨ψ, h⟩, h0, rfl⟩⟩

/--
The range of an unbounded operator, as a subspace of `H`; the image of `Dom(T)`.

Blueprint reference: `def:range-of-an-unbounded-operator`.
-/
def range (T : H →ₗ.[ℂ] H) : Submodule ℂ H := LinearMap.range T.toFun

omit [CompleteSpace H] in
@[simp]
theorem mem_range {T : H →ₗ.[ℂ] H} {φ : H} : φ ∈ range T ↔ ∃ ψ : T.domain, T ψ = φ :=
  Iff.rfl

/--
The orthogonal complement of the range of `T` is the kernel of `T*`.

Blueprint reference: `prpstn:hall-9.12`.
-/
theorem orthogonal_range_eq_ker_adjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) :
    (range T)ᗮ = ker (T†) := by
  ext φ
  rw [Submodule.mem_orthogonal', mem_ker, ← forall_inner_iff_adjoint hT]
  simp only [mem_range, inner_zero_left, forall_exists_index, forall_apply_eq_imp_iff]

/-!
### Sums with a bounded operator, and `T - λ 1`
-/

/--
The adjoint of `T + B`, for `B` a bounded operator defined on all of `H`, has the same
domain as `T*` and acts as `T* + B*` there. (The right-hand side has domain
`Dom(T*) ⊓ ⊤`; the equality includes the equality of domains.)

Blueprint reference: `prpstn:hall-9.13`.
-/
theorem adjoint_add_toPMap {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (B : H →L[ℂ] H) :
    (T + (B : H →ₗ[ℂ] H).toPMap ⊤)† =
      T† + ((ContinuousLinearMap.adjoint B : H →ₗ[ℂ] H).toPMap ⊤) := by
  have hS : HasDenseDomain (T + (B : H →ₗ[ℂ] H).toPMap ⊤) :=
    Dense.mono (fun _ hx => ⟨hx, trivial⟩) hT
  refine adjoint_eq_of_forall_inner_iff hS fun ψ φ => ?_
  -- `φ` represents `T + B` at `ψ` exactly when `φ - B* ψ` represents `T` at `ψ`.
  have key : (∀ χ : (T + (B : H →ₗ[ℂ] H).toPMap ⊤).domain,
      ⟪ψ, (T + (B : H →ₗ[ℂ] H).toPMap ⊤) χ⟫_ℂ = ⟪φ, (χ : H)⟫_ℂ) ↔
      ∀ χ : T.domain, ⟪ψ, T χ⟫_ℂ = ⟪φ - ContinuousLinearMap.adjoint B ψ, (χ : H)⟫_ℂ := by
    simp only [LinearPMap.add_apply, LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe,
      inner_add_right, inner_sub_left, ContinuousLinearMap.adjoint_inner_left, eq_sub_iff_add_eq]
    exact ⟨fun h χ => h ⟨χ, χ.2, trivial⟩, fun h χ => h ⟨χ, χ.2.1⟩⟩
  refine key.trans <| (forall_inner_iff_adjoint hT).trans ⟨?_, ?_⟩
  · rintro ⟨hψ, e⟩
    exact ⟨⟨hψ, trivial⟩, eq_sub_iff_add_eq.mp e⟩
  · rintro ⟨hψ, e⟩
    exact ⟨hψ.1, eq_sub_iff_add_eq.mpr e⟩

/--
The sum of an unbounded self-adjoint operator and a bounded self-adjoint operator defined
on all of `H` is self-adjoint on the domain of the unbounded one.

Blueprint reference: `prpstn:hall-9.13`.
-/
theorem isSelfAdjoint_add_of_isSelfAdjoint {T : H →ₗ.[ℂ] H}
    (hTsa : IsSelfAdjoint T) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (T + (B : H →ₗ[ℂ] H).toPMap ⊤) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_add_toPMap hTsa.dense_domain,
    LinearPMap.isSelfAdjoint_def.mp hTsa, hB.adjoint_eq]

/--
The operator `T - λ 1`, with domain `Dom(T)`.

Blueprint reference: the convention fixed after `def:hall-3.1`.
-/
def subSmul (T : H →ₗ.[ℂ] H) (lam : ℂ) : H →ₗ.[ℂ] H where
  domain := T.domain
  toFun := T.toFun - lam • T.domain.subtype

omit [CompleteSpace H] in
@[simp]
theorem subSmul_domain (T : H →ₗ.[ℂ] H) (lam : ℂ) : (subSmul T lam).domain = T.domain := rfl

omit [CompleteSpace H] in
@[simp]
theorem subSmul_apply (T : H →ₗ.[ℂ] H) (lam : ℂ) (ψ : (subSmul T lam).domain) :
    subSmul T lam ψ = T ψ - lam • (ψ : H) := rfl

/--
If `T` is closed and `‖(T - λ 1) ψ‖` is bounded below by `ε ‖ψ‖` for some `ε > 0`, then
the range of `T - λ 1` is a closed subspace of `H`.

Blueprint reference: `prpstn:hall-9.14`.
-/
theorem isClosed_range_subSmul {T : H →ₗ.[ℂ] H} (hcl : T.IsClosed) (lam : ℂ) {ε : ℝ}
    (hε : 0 < ε) (hbound : ∀ ψ : T.domain, ε * ‖(ψ : H)‖ ≤ ‖T ψ - lam • (ψ : H)‖) :
    IsClosed ((range (subSmul T lam) : Submodule ℂ H) : Set H) := by
  refine isSeqClosed_iff_isClosed.mp fun {u φ} hu hφ => ?_
  have hex : ∀ n, ∃ x : T.domain, T x - lam • (x : H) = u n := fun n => mem_range.mp (hu n)
  choose ψ hψ using hex
  -- The lower bound makes `ψ n` Cauchy since `u n` is.
  have hc : CauchySeq fun n => (ψ n : H) := by
    refine Metric.cauchySeq_iff.mpr fun δ hδ => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hφ.cauchySeq (ε * δ) (mul_pos hε hδ)
    refine ⟨N, fun m hm n hn => lt_of_mul_lt_mul_left ?_ hε.le⟩
    have h := hbound (ψ m - ψ n)
    rw [T.map_sub, Submodule.coe_sub, smul_sub, sub_sub_sub_comm, hψ, hψ, ← dist_eq_norm,
      ← dist_eq_norm] at h
    exact h.trans_lt (hN m hm n hn)
  obtain ⟨ξ, hξ⟩ := cauchySeq_tendsto_of_complete hc
  have hT : Tendsto (fun n => T (ψ n)) atTop (𝓝 (φ + lam • ξ)) :=
    (hφ.add (hξ.const_smul lam)).congr fun n => by rw [← hψ, sub_add_cancel]
  obtain ⟨y, hy1, hy2⟩ := T.mem_graph_iff.mp <|
    hcl.mem_of_tendsto (hξ.prodMk_nhds hT) (Eventually.of_forall fun n => T.mem_graph (ψ n))
  refine mem_range.mpr ⟨y, ?_⟩
  simp only at hy1 hy2
  rw [subSmul_apply, hy2, hy1, add_sub_cancel_right]

/--
The adjoint of `T - λ 1` is `T* - λ̄ 1`, including equality of domains.

Blueprint reference: `prpstn:hall-9.13` with `lmm:adjoint-of-scalar-multiple-of-identity`.
-/
theorem adjoint_subSmul {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (lam : ℂ) :
    (subSmul T lam)† = subSmul (T†) (starRingEnd ℂ lam) := by
  refine adjoint_eq_of_forall_inner_iff hT fun ψ φ => ?_
  have key : (∀ χ : (subSmul T lam).domain, ⟪ψ, subSmul T lam χ⟫_ℂ = ⟪φ, (χ : H)⟫_ℂ) ↔
      ∀ χ : T.domain, ⟪ψ, T χ⟫_ℂ = ⟪φ + starRingEnd ℂ lam • ψ, (χ : H)⟫_ℂ := by
    simp only [subSmul_apply, inner_sub_right, inner_smul_right, inner_add_left, inner_smul_left,
      Complex.conj_conj, sub_eq_iff_eq_add]
    rfl
  refine key.trans <| (forall_inner_iff_adjoint hT).trans ⟨?_, ?_⟩
  · rintro ⟨hψ, e⟩
    exact ⟨hψ, by rw [subSmul_apply]; exact sub_eq_of_eq_add e⟩
  · rintro ⟨hψ, e⟩
    exact ⟨hψ, eq_add_of_sub_eq e⟩

/--
The orthogonal complement of the range of `T - λ 1` is the kernel of `T* - λ̄ 1`.

Blueprint reference: `prpstn:hall-9.12` applied to `T - λ 1`.
-/
theorem orthogonal_range_subSmul {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (lam : ℂ) :
    (range (subSmul T lam))ᗮ = ker (subSmul (T†) (starRingEnd ℂ lam)) := by
  rw [orthogonal_range_eq_ker_adjoint (T := subSmul T lam) hT, adjoint_subSmul hT]

end Unbounded
end Spectral
end Physicslib4
