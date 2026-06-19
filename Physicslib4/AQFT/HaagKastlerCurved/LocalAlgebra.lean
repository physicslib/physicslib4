/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebras
import Physicslib4.GNS.Construction

/-!
# Axiom 4 (Local Algebra) and local observables, curved spacetime

This file formalises the blueprint declarations
`def:local-observable` and
`def:local-completeness-in-curved-spacetime` (Axiom 4 of the
Haag-Kastler axioms on a Lorentzian spacetime, Chapter 10
(`sections/sec10/10-4_haag-kastler-axioms-in-curved-spacetime`) of the
AQFT-in-Lean blueprint):

> **Local Observable.** The image `π_ω(a)` of a self-adjoint member
> `a` of a local algebra `𝔘(𝐁)` under the GNS `*`-homomorphism
> `π_ω` of a state `ω` on `𝔘(𝐁)` is self-adjoint and corresponds to
> an observable, called a *local observable*.
>
> **Axiom 4 (Local Algebra).** All "observables" are local
> observables.

## Main definitions

* `Physicslib4.AQFT.HaagKastlerCurved.IsLocalObservable`
  (`def:local-observable`).
* `Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebra` (Axiom 4,
  `def:local-completeness-in-curved-spacetime`).

## Modelling notes

* On a generic Lorentzian spacetime there is **no** quasilocal
  algebra (see Axiom 3), so — unlike the Minkowski Axiom 4
  (`QuasilocalCompleteness`, which collapses to the nonemptiness of
  a quasilocal algebra) — "all observables are local observables"
  cannot be phrased through one ambient algebra.

* We therefore relativise the statement to the *local* GNS
  representations that the framework actually provides: Axiom 4
  asserts that in **every** GNS representation `π` of **every** local
  algebra `𝔘(B)`, every self-adjoint operator lying in the range of
  `π` is a local observable. This is the faithful curved reading of
  "all observables are local observables", and (like the Minkowski
  axioms for the trivial net) it is satisfiable — see
  `localAlgebra_of` below, which proves it holds for *every* net.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

open Physicslib4 Physicslib4.GNS

variable {M : LorentzianSpacetime}

/--
**Local Observable** (blueprint `def:local-observable`).

Fix a local net `U`, an Alexandrov-basis set `B`, and a GNS
`*`-representation `π : 𝔘(B) →⋆ₐ[ℂ] (H →L[ℂ] H)` of the local
algebra `𝔘(B) = U.algebra B` on a complex Hilbert space `H` (in
practice obtained from `gns_construction` applied to a state `ω` on
`𝔘(B)`). A bounded operator `T : H →L[ℂ] H` is a *local observable*
if it is the image `T = π a` of some self-adjoint element `a` of the
local algebra.

Blueprint reference: `def:local-observable`.
-/
def IsLocalObservable {U : LocalNet M} {B : Set M.Carrier}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : U.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∃ a : U.algebra B, IsSelfAdjoint a ∧ T = π a

/-- Every local observable is self-adjoint: it is the image of a
self-adjoint element of the local algebra under a `*`-homomorphism.
This is the self-adjointness clause of `def:local-observable`. -/
theorem IsLocalObservable.isSelfAdjoint {U : LocalNet M} {B : Set M.Carrier}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : U.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (hT : IsLocalObservable π T) : IsSelfAdjoint T := by
  obtain ⟨a, ha, rfl⟩ := hT
  change star (π a) = π a
  rw [← map_star, ha.star_eq]

/-- For any state `ω` on a local algebra `𝔘(B)` and any self-adjoint
element `a` of it, the GNS construction provides a `*`-representation
in which `π a` is a local observable. This is the existence content of
`def:local-observable`, tying together `thrm:gns-construction-theorem`
and `def:state`. -/
theorem exists_isLocalObservable {U : LocalNet M} {B : Set M.Carrier}
    (ω : State (U.algebra B)) {a : U.algebra B} (ha : IsSelfAdjoint a) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : U.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)),
        IsLocalObservable π (π a) ∧ IsSelfAdjoint (π a) := by
  obtain ⟨H, hng, hip, hcs, π, _, _, _, _⟩ := gns_construction ω
  exact ⟨H, hng, hip, hcs, π, ⟨a, ha, rfl⟩,
    IsLocalObservable.isSelfAdjoint ⟨a, ha, rfl⟩⟩

/--
**Axiom 4 (Local Algebra), curved spacetime.** A local net `U` on a
Lorentzian spacetime `M` satisfies the *local algebra* axiom if, in
every GNS representation `π` of every local algebra `𝔘(B)`, every
self-adjoint operator in the range of `π` is a local observable.

This is the curved reading of "all observables are local
observables": the observables of the theory are exactly the images
of self-adjoint local elements.

Blueprint reference: `def:local-completeness-in-curved-spacetime`.
-/
def LocalAlgebra (U : LocalNet M) : Prop :=
  ∀ ⦃B : Set M.Carrier⦄, M.IsBasisSet B →
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : U.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H),
        IsSelfAdjoint T → T ∈ Set.range π → IsLocalObservable π T

/-- **Axiom 4 holds for every local net.** Given a self-adjoint
operator `T = π b` in the range of a GNS representation, replacing `b`
by its self-adjoint part `2⁻¹ • (b + star b)` (which `π` still sends
to `T`) exhibits `T` as a local observable. In particular the axiom is
satisfiable. -/
theorem localAlgebra_of (U : LocalNet M) : LocalAlgebra U := by
  intro B _ H _ _ _ π T hT hmem
  obtain ⟨b, rfl⟩ := hmem
  have hsa : IsSelfAdjoint (b + star b) := by
    rw [IsSelfAdjoint, star_add, star_star, add_comm]
  have hc : IsSelfAdjoint (2⁻¹ : ℂ) := by
    change star (2⁻¹ : ℂ) = 2⁻¹; rw [star_inv₀]; norm_num
  refine ⟨(2⁻¹ : ℂ) • (b + star b), hc.smul hsa, ?_⟩
  rw [map_smul, map_add, map_star, hT.star_eq, ← two_smul ℂ (π b), smul_smul,
    inv_mul_cancel₀ (two_ne_zero), one_smul]

section Observables

variable {U : LocalNet M} {B : Set M.Carrier} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : U.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- The identity operator on the GNS Hilbert space is a local observable:
it is the image `π 1` of the (self-adjoint) unit of the local algebra. -/
theorem isLocalObservable_one : IsLocalObservable π (1 : H →L[ℂ] H) :=
  ⟨1, IsSelfAdjoint.one (U.algebra B), (map_one π).symm⟩

/-- Local observables are closed under addition: the sum of the images of two
self-adjoint elements is the image of their (self-adjoint) sum. -/
theorem IsLocalObservable.add {S T : H →L[ℂ] H}
    (hS : IsLocalObservable π S) (hT : IsLocalObservable π T) :
    IsLocalObservable π (S + T) := by
  obtain ⟨a, ha, rfl⟩ := hS
  obtain ⟨b, hb, rfl⟩ := hT
  exact ⟨a + b, ha.add hb, (map_add π a b).symm⟩

/-- Local observables are closed under scaling by a *self-adjoint* complex
scalar (equivalently, a real scalar): self-adjointness of `c • a` requires
`star c = c`. -/
theorem IsLocalObservable.smul {c : ℂ} {T : H →L[ℂ] H}
    (hT : IsLocalObservable π T) (hc : IsSelfAdjoint c) :
    IsLocalObservable π (c • T) := by
  obtain ⟨a, ha, rfl⟩ := hT
  exact ⟨c • a, hc.smul ha, (map_smul π c a).symm⟩

/-- *Real-linear combinations* of local observables are local observables. The
scalars are taken self-adjoint in `ℂ`, i.e. real, which is exactly the
condition under which the combination stays self-adjoint. -/
theorem IsLocalObservable.smul_add_smul {c d : ℂ} {S T : H →L[ℂ] H}
    (hc : IsSelfAdjoint c) (hd : IsSelfAdjoint d)
    (hS : IsLocalObservable π S) (hT : IsLocalObservable π T) :
    IsLocalObservable π (c • S + d • T) :=
  (hS.smul hc).add (hT.smul hd)

/-- **Characterisation of local observables.** An operator `T` on the GNS
Hilbert space is a local observable precisely when it is self-adjoint and lies
in the range of the representation `π`. The forward direction is
`IsLocalObservable.isSelfAdjoint`; the converse holds even when `π` is not
injective, by replacing a preimage `b` with its self-adjoint part
`2⁻¹ • (b + star b)`, which `π` still sends to `T`. -/
theorem isLocalObservable_iff {T : H →L[ℂ] H} :
    IsLocalObservable π T ↔ IsSelfAdjoint T ∧ T ∈ Set.range π := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨IsLocalObservable.isSelfAdjoint ⟨a, ha, rfl⟩, a, rfl⟩
  · rintro ⟨hT, b, rfl⟩
    have hsa : IsSelfAdjoint (b + star b) := by
      rw [IsSelfAdjoint, star_add, star_star, add_comm]
    have hc : IsSelfAdjoint (2⁻¹ : ℂ) := by
      change star (2⁻¹ : ℂ) = 2⁻¹; rw [star_inv₀]; norm_num
    refine ⟨(2⁻¹ : ℂ) • (b + star b), hc.smul hsa, ?_⟩
    rw [map_smul, map_add, map_star, hT.star_eq, ← two_smul ℂ (π b), smul_smul,
      inv_mul_cancel₀ (two_ne_zero), one_smul]

end Observables

/-- The set of *local observables* on the GNS Hilbert space `H` for the
representation `π`: all bounded operators of the form `π a` with `a` a
self-adjoint element of the local algebra. -/
def localObservables {U : LocalNet M} {B : Set M.Carrier} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : U.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {T | IsLocalObservable π T}

/-- The local observables are exactly the self-adjoint elements lying in the
range of the representation `π`. -/
theorem localObservables_eq {U : LocalNet M} {B : Set M.Carrier} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : U.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    localObservables π
      = (selfAdjoint (H →L[ℂ] H) : Set (H →L[ℂ] H)) ∩ Set.range π := by
  ext T
  simp only [localObservables, Set.mem_setOf_eq, isLocalObservable_iff,
    Set.mem_inter_iff, SetLike.mem_coe, selfAdjoint.mem_iff, isSelfAdjoint_iff]

section ObservablesSet

variable {U : LocalNet M} {B : Set M.Carrier} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : U.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The identity operator is a local observable. -/
theorem one_mem_localObservables :
    (1 : H →L[ℂ] H) ∈ localObservables π :=
  isLocalObservable_one

/-- The local observables are closed under addition. -/
theorem add_mem_localObservables {S T : H →L[ℂ] H}
    (hS : S ∈ localObservables π) (hT : T ∈ localObservables π) :
    S + T ∈ localObservables π :=
  IsLocalObservable.add hS hT

/-- The local observables are closed under scaling by a self-adjoint
(i.e. real) complex scalar. -/
theorem smul_mem_localObservables {c : ℂ} {T : H →L[ℂ] H}
    (hT : T ∈ localObservables π) (hc : IsSelfAdjoint c) :
    c • T ∈ localObservables π :=
  IsLocalObservable.smul hT hc

end ObservablesSet

end HaagKastlerCurved
end AQFT
end Physicslib4
