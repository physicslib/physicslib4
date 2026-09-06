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
  `adjoint_le_adjoint_of_le`, `existsUnique_isSelfAdjoint_extension`.
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
    ∃! χ : H, ∀ ψ : T.domain, ⟪φ, T ψ⟫_ℂ = ⟪χ, (ψ : H)⟫_ℂ := by
  sorry

/--
A linear combination of vectors in `Dom(T*)` again lies in `Dom(T*)`.

Together with `adjoint_smul_add` this is the blueprint's linearity of the adjoint; in
Lean it is already carried by the fact that `T†` is a `LinearPMap`, whose domain is a
submodule and whose action is linear.

Blueprint reference: `prpstn:hall-linearity-of-the-adjoint`.
-/
theorem smul_add_mem_adjoint_domain {T : H →ₗ.[ℂ] H} (α β : ℂ) {φ₁ φ₂ : H}
    (h₁ : φ₁ ∈ (T†).domain) (h₂ : φ₂ ∈ (T†).domain) : α • φ₁ + β • φ₂ ∈ (T†).domain := by
  sorry

/--
The adjoint acts linearly on its domain.

Blueprint reference: `prpstn:hall-linearity-of-the-adjoint`.
-/
theorem adjoint_smul_add {T : H →ₗ.[ℂ] H} (α β : ℂ) (φ₁ φ₂ : (T†).domain)
    (h : α • (φ₁ : H) + β • (φ₂ : H) ∈ (T†).domain) :
    T† ⟨α • (φ₁ : H) + β • (φ₂ : H), h⟩ = α • T† φ₁ + β • T† φ₂ := by
  sorry

/--
A vector `ψ` lies in `Dom(T*)` exactly when the functional `χ ↦ ⟪ψ, T χ⟫` is *exactly*
represented by some vector `φ`; boundedness need not be checked directly.

Blueprint reference: `lmm:characterizing-adjoint-domain-membership`.
-/
theorem mem_adjoint_domain_iff_exists {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (ψ : H) :
    ψ ∈ (T†).domain ↔ ∃ φ : H, ∀ χ : T.domain, ⟪ψ, T χ⟫_ℂ = ⟪φ, (χ : H)⟫_ℂ := by
  sorry

/--
The representing vector in `mem_adjoint_domain_iff_exists` is `T* ψ`.

Blueprint reference: `lmm:characterizing-adjoint-domain-membership`.
-/
theorem adjoint_apply_eq_of_forall_inner {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) {ψ : H}
    (hψ : ψ ∈ (T†).domain) {φ : H}
    (h : ∀ χ : T.domain, ⟪ψ, T χ⟫_ℂ = ⟪φ, (χ : H)⟫_ℂ) : T† ⟨ψ, hψ⟩ = φ := by
  sorry

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

/--
Symmetry in the sense of `IsSymmetric` is Mathlib's `LinearPMap.IsFormalAdjoint` of `T`
with itself.

Blueprint reference: `def:hall-9.2`.
-/
theorem isSymmetric_iff_isFormalAdjoint {T : H →ₗ.[ℂ] H} :
    IsSymmetric T ↔ T.IsFormalAdjoint T := by
  sorry

/--
An unbounded operator is symmetric if and only if its adjoint is an extension of it.

Blueprint reference: `prpstn:hall-9.4`.
-/
theorem isSymmetric_iff_le_adjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) :
    IsSymmetric T ↔ T ≤ T† := by
  sorry

/-!
### The closure of an unbounded operator

The blueprint's graph `Γ(A) ⊂ H × H` is Mathlib's `LinearPMap.graph`, closedness and
closability are `LinearPMap.IsClosed` and `LinearPMap.IsClosable`, and `A^cl` is
`LinearPMap.closure`.
-/

/--
The closure of a densely defined closable operator again has dense domain, so it is
again an unbounded operator in the blueprint's sense.

Blueprint reference: `prpstn:closure-linearity-and-sequential-description` (Part 1).
-/
theorem hasDenseDomain_closure {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hc : T.IsClosable) : HasDenseDomain T.closure := by
  sorry

/--
Sequential description of the domain of the closure: `ξ ∈ Dom(T^cl)` exactly when there
is a sequence in `Dom(T)` converging to `ξ` whose image under `T` also converges.

Blueprint reference: `prpstn:closure-linearity-and-sequential-description` (Part 2).
-/
theorem mem_domain_closure_iff {T : H →ₗ.[ℂ] H} (hc : T.IsClosable) (ξ : H) :
    ξ ∈ T.closure.domain ↔
      ∃ (χ : ℕ → T.domain) (η : H),
        Tendsto (fun n => (χ n : H)) atTop (𝓝 ξ) ∧ Tendsto (fun n => T (χ n)) atTop (𝓝 η) := by
  sorry

/--
In the situation of `mem_domain_closure_iff`, the limit of `T χ n` is `T^cl ξ`.

Blueprint reference: `prpstn:closure-linearity-and-sequential-description` (Part 2).
-/
theorem closure_apply_eq_of_tendsto {T : H →ₗ.[ℂ] H} (hc : T.IsClosable) {ξ η : H}
    {χ : ℕ → T.domain} (hχ : Tendsto (fun n => (χ n : H)) atTop (𝓝 ξ))
    (hTχ : Tendsto (fun n => T (χ n)) atTop (𝓝 η)) (hξ : ξ ∈ T.closure.domain) :
    T.closure ⟨ξ, hξ⟩ = η := by
  sorry

/--
`T^cl` is the smallest closed extension of `T`: any closed extension of `T` is an
extension of `T^cl`. (That `T^cl` is itself a closed extension of `T` is Mathlib's
`LinearPMap.le_closure` and `LinearPMap.IsClosable.closure_isClosed`.)

Blueprint reference: `prpstn:closure-linearity-and-sequential-description` (Part 3).
-/
theorem closure_le_of_isClosed {T B : H →ₗ.[ℂ] H} (hc : T.IsClosable) (hTB : T ≤ B)
    (hB : B.IsClosed) : T.closure ≤ B := by
  sorry

/--
The closure of a symmetric closable operator is symmetric.

Blueprint reference: `lmm:closure-of-symmetric-is-symmetric`.
-/
theorem isSymmetric_closure {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T) (hc : T.IsClosable) :
    IsSymmetric T.closure := by
  sorry

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
    (hsym : IsSymmetric T) : T.IsClosable := by
  sorry

/--
The adjoint of the closure of a closable operator coincides with the adjoint of the
operator itself.

Blueprint reference: `prpstn:hall-9.10`.
-/
theorem adjoint_closure_eq_adjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hc : T.IsClosable) : (T.closure)† = T† := by
  sorry

/--
Taking adjoints reverses extension: if `C₁` extends `C₂` then `C₂*` extends `C₁*`.

Blueprint reference: `lmm:extension-reverses-adjoint-domains`.
-/
theorem adjoint_le_adjoint_of_le {C₁ C₂ : H →ₗ.[ℂ] H} (h : C₂ ≤ C₁) : C₁† ≤ C₂† := by
  sorry

/--
If `T` is essentially self-adjoint, then `T^cl` is the *unique* self-adjoint extension
of `T`.

Blueprint reference: `prpstn:hall-9.11`.
-/
theorem existsUnique_isSelfAdjoint_extension {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (h : IsEssentiallySelfAdjoint T) : ∃! B : H →ₗ.[ℂ] H, IsSelfAdjoint B ∧ T ≤ B := by
  sorry

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

@[simp]
theorem mem_ker {T : H →ₗ.[ℂ] H} {ψ : H} :
    ψ ∈ ker T ↔ ∃ h : ψ ∈ T.domain, T ⟨ψ, h⟩ = 0 := by
  sorry

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
  sorry

/-!
### Sums with a bounded operator, and `T - λ 1`
-/

/--
The adjoint of `T + B`, for `B` a bounded operator defined on all of `H`, has the same
domain as `T*` and acts as `T* + B*` there. (Both sides are `LinearPMap`s whose domain is
`Dom(T*) ⊓ ⊤`.)

Blueprint reference: `prpstn:hall-9.13`.
-/
theorem adjoint_add_toPMap {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (B : H →L[ℂ] H) :
    (T + (B : H →ₗ[ℂ] H).toPMap ⊤)† =
      T† + ((ContinuousLinearMap.adjoint B : H →ₗ[ℂ] H).toPMap ⊤) := by
  sorry

/--
The sum of an unbounded self-adjoint operator and a bounded self-adjoint operator defined
on all of `H` is self-adjoint on the domain of the unbounded one.

Blueprint reference: `prpstn:hall-9.13`.
-/
theorem isSelfAdjoint_add_of_isSelfAdjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hTsa : IsSelfAdjoint T) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (T + (B : H →ₗ[ℂ] H).toPMap ⊤) := by
  sorry

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
  sorry

end Unbounded
end Spectral
end Physicslib4
