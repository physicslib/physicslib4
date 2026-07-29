/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Basic

/-!
# The GNS triple as a bundled object

A *GNS triple* for a state `ω` on a unital C*-algebra `A` is the data of a
`*`-representation `π` on a Hilbert space `H`, a cyclic vector `Ω`, and the
reproducing property `ω a = ⟪Ω, π a Ω⟫`. Throughout the library this data has
been carried as four separate arguments (`π`, `Ω`, plus the two hypotheses),
which makes the statements that quantify over *two* triples — GNS uniqueness,
GNS covariance, superselection-type transport — carry a ten-argument preamble
that is repeated verbatim at seventeen call sites.

`GNSTriple` bundles exactly those four components.

## Design: a deliberate hybrid

The Hilbert space `H` and its instances (`NormedAddCommGroup`,
`InnerProductSpace ℂ`, `CompleteSpace`) are **left as ordinary binders** —
they are parameters of the structure, not fields. This is deliberate:

* Mathlib keeps these instances unbundled everywhere (the binder list here is
  character-identical to `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`), and
  bundling them into fields would break instance resolution and interoperability
  with every Mathlib lemma that expects them unbundled.
* It would also not pay for itself. Unused `variable`s are not included in a
  declaration, so idle instance binders cost nothing; the elaboration cost in
  this area comes from *using* `H →L[ℂ] H` (synthesising `Ring` / `Algebra ℂ`
  / `SMulCommClass` on it), which bundling cannot avoid and would only add
  projection overhead to.

So this file bundles *data and properties* — which Mathlib does freely
(`OrthonormalBasis`, `IsHilbertSum`) — and leaves *instances* alone.
-/

namespace Physicslib4
namespace GNS

open scoped InnerProductSpace

/-- A **GNS triple** for a state `ω` on `A`, on the Hilbert space `H`: a
`*`-representation `π` together with a cyclic vector `Ω` reproducing `ω`.

The Hilbert space and its instances are parameters rather than fields, so the
structure interoperates with Mathlib's unbundled conventions (see the module
docstring). -/
structure GNSTriple {A : Type*} [CStarAlgebra A] (ω : State A)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The `*`-representation of `A` on `H`. -/
  π : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  /-- The cyclic vector. -/
  Ω : H
  /-- `Ω` is cyclic for `π`: the orbit `{π a Ω}` is dense in `H`. -/
  cyclic : IsCyclicVector π Ω
  /-- `π` and `Ω` reproduce the state: `ω a = ⟪Ω, π a Ω⟫`. -/
  reproducing : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ

end GNS
end Physicslib4
