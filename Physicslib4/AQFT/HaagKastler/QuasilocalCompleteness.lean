/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra
import Physicslib4.GNS.Construction

/-!
# Axiom 4: Quasilocal Completeness

This file formalises the blueprint declaration
`def:quasilocal-completeness` (Axiom 4 of the "sharpened"
Haag-Kastler axioms, section 9.3 of the AQFT-in-Lean blueprint):

> All "observables" are *quasilocal observables*: the union of the
> images of all local algebras `𝔘(𝐁)` is dense in (and thus
> completes to) the *quasilocal algebra* `𝔘`, which is the
> C*-algebra that "contains all observables of interest".

## Main definitions

* `Physicslib4.AQFT.HaagKastler.QuasilocalCompleteness`: a
  `Prop`-valued predicate on a `LocalNet` asserting Axiom 4.
* `Physicslib4.AQFT.HaagKastler.IsQuasilocalObservable`: a
  `Prop`-valued predicate (blueprint `def:quasilocal-observable`)
  saying a bounded operator on the GNS Hilbert space is the image
  `π a` of a self-adjoint element `a` of the quasilocal algebra
  under a GNS `*`-representation `π`.

## Modelling notes

* Following the blueprint, the quasilocal algebra `𝔘` is the
  C*-algebraic *completion* of the set-theoretic union of all
  `𝔘(B)`. The bundled `QuasilocalAlgebra U` structure already
  packages exactly this data — an ambient C*-algebra together with
  faithful unital `*`-monomorphisms whose images have dense union —
  so Axiom 4 collapses to bare nonemptiness:
  `Nonempty (QuasilocalAlgebra U)`.

* In particular, both the *faithfulness* of the embeddings and the
  *density* of the union of their images are part of the
  `QuasilocalAlgebra` structure itself; there is nothing further to
  assert at this level.

* This is closely related to (and refines) the existence statement
  used in `LocalCommutativity`; the two predicates can in principle
  be witnessed by the *same* ambient `QuasilocalAlgebra`, but we
  keep them separate so each axiom can be stated and tested in
  isolation.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4
open Physicslib4.GNS

/--
**Axiom 4 (Quasilocal Completeness).** A local net `U` satisfies
*quasilocal completeness* if it *admits a quasilocal algebra*,
i.e. `Nonempty (QuasilocalAlgebra U)`.

Unfolding the `QuasilocalAlgebra` structure, this says there exists
a unital ambient C*-algebra `Q.carrier` — the *quasilocal algebra*
`𝔘` — together with unital `*`-monomorphisms
`Q.ι B : U.algebra B →⋆ₐ[ℂ] Q.carrier` for every Alexandrov-basis
set `B`, each injective on Alexandrov-basis sets, and such that the
union `⋃ B, Set.range (Q.ι B)` is *dense* in `Q.carrier`.

This expresses the blueprint's "all observables are quasilocal
observables": every element of `Q.carrier` is the norm-limit of a
sequence of elements of `⋃_B 𝔘(B)`.

Blueprint reference: `def:quasilocal-completeness`.
-/
def QuasilocalCompleteness (U : LocalNet) : Prop :=
  Nonempty (QuasilocalAlgebra U)

/--
**Quasilocal Observable** (blueprint label `def:quasilocal-observable`).

Fix a quasilocal algebra `Q` for a local net `U` and a GNS
`*`-representation `π : Q.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)` of the
quasilocal algebra `𝔘 = Q.carrier` on a complex Hilbert space `H`
(in practice obtained from `Physicslib4.GNS.gns_construction`
applied to a state `ω` on `Q.carrier`). A bounded operator
`T : H →L[ℂ] H` is a *quasilocal observable* if it is the image
`T = π a` of some *self-adjoint* element `a` of the quasilocal
algebra.

By `IsQuasilocalObservable.isSelfAdjoint`, every quasilocal
observable is self-adjoint, matching the blueprint's "the image
`π_ω(a)` of a self-adjoint member `a` of the quasilocal algebra
`𝔘` ... is self-adjoint and thus corresponds to an observable".

Blueprint reference: `def:quasilocal-observable`.
-/
def IsQuasilocalObservable {U : LocalNet} (Q : QuasilocalAlgebra U)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Q.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∃ a : Q.carrier, IsSelfAdjoint a ∧ T = π a

/-- Every quasilocal observable is self-adjoint: it is the image of a
self-adjoint element of the quasilocal algebra under a `*`-homomorphism.
This is the self-adjointness clause of `def:quasilocal-observable`. -/
theorem IsQuasilocalObservable.isSelfAdjoint {U : LocalNet}
    {Q : QuasilocalAlgebra U}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : Q.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (hT : IsQuasilocalObservable Q π T) : IsSelfAdjoint T := by
  obtain ⟨a, ha, rfl⟩ := hT
  change star (π a) = π a
  rw [← map_star, ha.star_eq]

/-- For any state `ω` on the quasilocal algebra and any self-adjoint
element `a` of it, the GNS construction provides a `*`-representation
in which `π a` is a quasilocal observable (and is self-adjoint). This is
the existence content of `def:quasilocal-observable`, tying together
`thrm:gns-construction-theorem` and `def:state`. -/
theorem exists_isQuasilocalObservable {U : LocalNet} (Q : QuasilocalAlgebra U)
    (ω : State Q.carrier) {a : Q.carrier} (ha : IsSelfAdjoint a) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : Q.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)),
        IsQuasilocalObservable Q π (π a) ∧ IsSelfAdjoint (π a) := by
  obtain ⟨H, hng, hip, hcs, π, _, _, _, _⟩ := gns_construction ω
  refine ⟨H, hng, hip, hcs, π, ⟨a, ha, rfl⟩, ?_⟩
  change star (π a) = π a
  rw [← map_star, ha.star_eq]

section Observables

variable {U : LocalNet} {Q : QuasilocalAlgebra U} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : Q.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- The identity operator on the GNS Hilbert space is a quasilocal observable:
it is the image `π 1` of the (self-adjoint) unit of the quasilocal algebra. -/
theorem isQuasilocalObservable_one : IsQuasilocalObservable Q π 1 :=
  ⟨1, IsSelfAdjoint.one Q.carrier, (map_one π).symm⟩

/-- Quasilocal observables are closed under addition: the sum of the images of
two self-adjoint elements is the image of their (self-adjoint) sum. -/
theorem IsQuasilocalObservable.add {S T : H →L[ℂ] H}
    (hS : IsQuasilocalObservable Q π S) (hT : IsQuasilocalObservable Q π T) :
    IsQuasilocalObservable Q π (S + T) := by
  obtain ⟨a, ha, rfl⟩ := hS
  obtain ⟨b, hb, rfl⟩ := hT
  exact ⟨a + b, ha.add hb, (map_add π a b).symm⟩

/-- Quasilocal observables are closed under scaling by a *self-adjoint* complex
scalar (equivalently, a real scalar): self-adjointness of `c • a` requires
`star c = c`. -/
theorem IsQuasilocalObservable.smul {c : ℂ} {T : H →L[ℂ] H}
    (hT : IsQuasilocalObservable Q π T) (hc : IsSelfAdjoint c) :
    IsQuasilocalObservable Q π (c • T) := by
  obtain ⟨a, ha, rfl⟩ := hT
  exact ⟨c • a, hc.smul ha, (map_smul π c a).symm⟩

/-- *Real-linear combinations* of quasilocal observables are quasilocal
observables. The scalars are taken self-adjoint in `ℂ`, i.e. real, which is
exactly the condition under which the combination stays self-adjoint. -/
theorem IsQuasilocalObservable.smul_add_smul {c d : ℂ} {S T : H →L[ℂ] H}
    (hc : IsSelfAdjoint c) (hd : IsSelfAdjoint d)
    (hS : IsQuasilocalObservable Q π S) (hT : IsQuasilocalObservable Q π T) :
    IsQuasilocalObservable Q π (c • S + d • T) :=
  (hS.smul hc).add (hT.smul hd)

/-- **Characterisation of quasilocal observables.** An operator `T` on the GNS
Hilbert space is a quasilocal observable precisely when it is self-adjoint and
lies in the range of the representation `π`. The forward direction is
`IsQuasilocalObservable.isSelfAdjoint`; the converse holds even when `π` is not
injective, by replacing a preimage `b` with its self-adjoint part
`2⁻¹ • (b + star b)`, which `π` still sends to `T`. -/
theorem isQuasilocalObservable_iff {T : H →L[ℂ] H} :
    IsQuasilocalObservable Q π T ↔ IsSelfAdjoint T ∧ T ∈ Set.range π := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨IsQuasilocalObservable.isSelfAdjoint ⟨a, ha, rfl⟩, a, rfl⟩
  · rintro ⟨hT, b, rfl⟩
    have hsa : IsSelfAdjoint (b + star b) := by
      rw [IsSelfAdjoint, star_add, star_star, add_comm]
    have hc : IsSelfAdjoint (2⁻¹ : ℂ) := by
      change star (2⁻¹ : ℂ) = 2⁻¹; rw [star_inv₀]; norm_num
    refine ⟨(2⁻¹ : ℂ) • (b + star b), hc.smul hsa, ?_⟩
    rw [map_smul, map_add, map_star, hT.star_eq, ← two_smul ℂ (π b), smul_smul,
      inv_mul_cancel₀ (two_ne_zero), one_smul]

end Observables

/-- The set of *quasilocal observables* on the GNS Hilbert space `H` for the
representation `π`: all bounded operators of the form `π a` with `a` a
self-adjoint element of the quasilocal algebra. -/
def quasilocalObservables {U : LocalNet} (Q : QuasilocalAlgebra U) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Q.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {T | IsQuasilocalObservable Q π T}

/-- The quasilocal observables are exactly the self-adjoint elements lying in
the range of the representation `π`. -/
theorem quasilocalObservables_eq {U : LocalNet} (Q : QuasilocalAlgebra U)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Q.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    quasilocalObservables Q π
      = (selfAdjoint (H →L[ℂ] H) : Set (H →L[ℂ] H)) ∩ Set.range π := by
  ext T
  simp only [quasilocalObservables, Set.mem_setOf_eq, isQuasilocalObservable_iff,
    Set.mem_inter_iff, SetLike.mem_coe, selfAdjoint.mem_iff, isSelfAdjoint_iff]

section ObservablesSet

variable {U : LocalNet} (Q : QuasilocalAlgebra U) {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : Q.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The identity operator is a quasilocal observable. -/
theorem one_mem_quasilocalObservables :
    (1 : H →L[ℂ] H) ∈ quasilocalObservables Q π :=
  isQuasilocalObservable_one

/-- The quasilocal observables are closed under addition. -/
theorem add_mem_quasilocalObservables {S T : H →L[ℂ] H}
    (hS : S ∈ quasilocalObservables Q π) (hT : T ∈ quasilocalObservables Q π) :
    S + T ∈ quasilocalObservables Q π :=
  IsQuasilocalObservable.add hS hT

/-- The quasilocal observables are closed under scaling by a self-adjoint
(i.e. real) complex scalar. -/
theorem smul_mem_quasilocalObservables {c : ℂ} {T : H →L[ℂ] H}
    (hT : T ∈ quasilocalObservables Q π) (hc : IsSelfAdjoint c) :
    c • T ∈ quasilocalObservables Q π :=
  IsQuasilocalObservable.smul hT hc

end ObservablesSet

end HaagKastler
end AQFT
end Physicslib4
