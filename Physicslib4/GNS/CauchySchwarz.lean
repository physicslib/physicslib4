/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Star.Module

/-!
# Cauchy-Schwarz inequality for positive linear functionals on a *-algebra

This file states the Cauchy-Schwarz inequality for positive linear functionals
on an arbitrary (not necessarily unital, not necessarily normed) *-algebra over
`ℂ`, following the AQFT-in-Lean blueprint section 9.1, label
`lmm:cauchy-schwarz-inequality`.

The hypothesis is **weaker than `Physicslib4.GNS.State`**: we only require a
`ℂ`-linear functional `ω : A →ₗ[ℂ] ℂ` together with positivity
`0 ≤ ω (star a * a)` for all `a`. Continuity and normalisation are *not*
assumed.

## Main statements

* `Physicslib4.GNS.omega_star_swap_conj`: for a positive linear functional `ω`
  on a *-algebra `A`, `ω (star a * b) = star (ω (star b * a))` for all
  `a, b : A`.
* `Physicslib4.GNS.cauchy_schwarz_inequality`: under the same hypotheses,
  `Complex.normSq (ω (star a * b)) ≤ (ω (star a * a)).re * (ω (star b * b)).re`
  for all `a, b : A`.

Both conclusions of the blueprint lemma are recorded; the primary entry-point
is `cauchy_schwarz_inequality`.

## Typeclass setup

The blueprint says "*-algebra"; the minimal Mathlib shape needed to state
the lemma is a complex `*`-ring, i.e. `[NonUnitalNonAssocRing A] [StarRing A]
[Module ℂ A]`. Continuity of `ω` and normalisation are not required.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable {A : Type*} [NonUnitalNonAssocRing A] [StarRing A] [Module ℂ A]

/--
**Hermitian symmetry for positive linear functionals on a `*`-algebra**
(part 1 of `lmm:cauchy-schwarz-inequality`).

If `ω : A →ₗ[ℂ] ℂ` satisfies `0 ≤ ω (star a * a)` for every `a : A`, then
`ω (star a * b) = star (ω (star b * a))` for all `a, b : A`, i.e.
`ω(a*b) = conj(ω(b*a))`.
-/
theorem omega_star_swap_conj
    (ω : A →ₗ[ℂ] ℂ) (hω : ∀ a : A, 0 ≤ ω (star a * a)) (a b : A) :
    ω (star a * b) = star (ω (star b * a)) := by
  sorry

/--
**Cauchy-Schwarz inequality for positive linear functionals on a `*`-algebra**
(`lmm:cauchy-schwarz-inequality`, primary entry point).

Let `A` be a complex `*`-algebra (here packaged as a `NonUnitalNonAssocRing`
with a compatible `StarRing` structure and `Module ℂ A`). If
`ω : A →ₗ[ℂ] ℂ` satisfies `0 ≤ ω (star a * a)` for every `a : A`, then for
all `a, b : A` we have
`|ω(a*b)|² ≤ ω(a*a) · ω(b*b)`.

Because `ω (star a * a)` and `ω (star b * b)` are non-negative reals (by the
positivity hypothesis), the inequality is stated using the real parts of
these complex numbers and `Complex.normSq` for the left-hand side.
-/
theorem cauchy_schwarz_inequality
    (ω : A →ₗ[ℂ] ℂ) (hω : ∀ a : A, 0 ≤ ω (star a * a)) (a b : A) :
    Complex.normSq (ω (star a * b))
      ≤ (ω (star a * a)).re * (ω (star b * b)).re := by
  sorry

end GNS
end Physicslib4
