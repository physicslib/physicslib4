/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Spectrum
import Physicslib4.Spectral.Unbounded.Basic

/-!
# The spectrum of an unbounded operator

For an unbounded operator `T`, a scalar `λ` lies in the resolvent set when `T - λ 1` has
a *bounded two-sided inverse defined on all of `H` and landing in `Dom(T)`*; the spectrum
is the complement. Since `T - λ 1` is only defined on `Dom(T)`, this is spelled out as a
structure `IsResolvent` rather than as invertibility in a ring, so the names here are
`pmapResolventSet` and `pmapSpectrum` to keep them apart from Mathlib's `resolventSet`
and `spectrum` for bounded operators; `pmapResolventSet_toPMap_top` shows the two notions
agree on bounded operators.

## Main statements

* `existsUnique_isResolvent` — the inverse is unique when it exists.
* `pmapResolventSet_toPMap_top`, `pmapSpectrum_toPMap_top` — the two notions of spectrum
  agree for a bounded operator.
* `sq_norm_le_of_isSymmetric` — the `b²` inequality for a symmetric unbounded operator.
* `pmapSpectrum_subset_real` — the spectrum of an unbounded self-adjoint operator is real.
* `isEssentiallySelfAdjoint_iff_dense_range` — essential self-adjointness via dense range.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
`B` is a bounded two-sided inverse of `T - λ 1`: it maps all of `H` into `Dom(T)`,
inverts `T - λ 1` on the right everywhere, and on the left on `Dom(T)`.

Blueprint reference: `def:hall-9.16`.
-/
structure IsResolvent (T : H →ₗ.[ℂ] H) (lam : ℂ) (B : H →L[ℂ] H) : Prop where
  /-- `B` lands in `Dom(T)`. -/
  mem_domain : ∀ ψ : H, B ψ ∈ T.domain
  /-- `(T - λ 1) B ψ = ψ` for all `ψ ∈ H`. -/
  rightInverse : ∀ ψ : H, T ⟨B ψ, mem_domain ψ⟩ - lam • B ψ = ψ
  /-- `B (T - λ 1) ψ = ψ` for all `ψ ∈ Dom(T)`. -/
  leftInverse : ∀ ψ : T.domain, B (T ψ - lam • (ψ : H)) = (ψ : H)

/--
The resolvent set of an unbounded operator.

Blueprint reference: `def:hall-9.16`.
-/
def pmapResolventSet (T : H →ₗ.[ℂ] H) : Set ℂ := {lam | ∃ B : H →L[ℂ] H, IsResolvent T lam B}

/--
The spectrum of an unbounded operator: the complement of its resolvent set.

Blueprint reference: `def:hall-9.16`.
-/
def pmapSpectrum (T : H →ₗ.[ℂ] H) : Set ℂ := (pmapResolventSet T)ᶜ

/--
The bounded inverse of `T - λ 1` is unique when it exists; this is what licenses the
notation `(T - λ 1)⁻¹`.

Blueprint reference: `lmm:uniqueness-of-resolvent`.
-/
theorem existsUnique_isResolvent {T : H →ₗ.[ℂ] H} {lam : ℂ} (h : lam ∈ pmapResolventSet T) :
    ∃! B : H →L[ℂ] H, IsResolvent T lam B := by
  sorry

/--
For a bounded operator, regarded as an unbounded operator with domain all of `H`, the
unbounded resolvent set agrees with Mathlib's `resolventSet`.

Blueprint reference: `lmm:spectrum-notions-agree`.
-/
theorem pmapResolventSet_toPMap_top (A : H →L[ℂ] H) :
    pmapResolventSet ((A : H →ₗ[ℂ] H).toPMap ⊤) = resolventSet ℂ A := by
  sorry

/--
Consequently the two notions of spectrum agree for a bounded operator.

Blueprint reference: `lmm:spectrum-notions-agree`.
-/
theorem pmapSpectrum_toPMap_top (A : H →L[ℂ] H) :
    pmapSpectrum ((A : H →ₗ[ℂ] H).toPMap ⊤) = spectrum ℂ A := by
  sorry

/--
The `b²` inequality for a symmetric unbounded operator: for `λ = a + i b` with `a, b`
real, `b² ‖ψ‖² ≤ ‖(T - λ 1) ψ‖²` for every `ψ ∈ Dom(T)`.

This is the unbounded, merely-symmetric counterpart of `lmm:hall-7.8`
(`Physicslib4.Spectral.sq_norm_sub_smul_apply_le`).

Blueprint reference: `lmm:b-squared-inequality-symmetric`.
-/
theorem sq_norm_le_of_isSymmetric {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T) (a b : ℝ)
    (ψ : T.domain) :
    b ^ 2 * ‖(ψ : H)‖ ^ 2 ≤ ‖T ψ - ((a : ℂ) + (b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 := by
  sorry

/--
The spectrum of an unbounded self-adjoint operator is contained in the real line.

Blueprint reference: `thrm:hall-9.17`.
-/
theorem pmapSpectrum_subset_real {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hsa : IsSelfAdjoint T) : pmapSpectrum T ⊆ {z : ℂ | z.im = 0} := by
  sorry

/--
A symmetric operator is essentially self-adjoint if and only if the ranges of `T - i 1`
and `T + i 1` are both dense in `H`. (Here `T + i 1` is `subSmul T (-i)`.)

Blueprint reference: `thrm:hall-9.21`.
-/
theorem isEssentiallySelfAdjoint_iff_dense_range {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hsym : IsSymmetric T) :
    IsEssentiallySelfAdjoint T ↔
      Dense ((range (subSmul T Complex.I) : Submodule ℂ H) : Set H) ∧
        Dense ((range (subSmul T (-Complex.I)) : Submodule ℂ H) : Set H) := by
  sorry

end Unbounded
end Spectral
end Physicslib4
