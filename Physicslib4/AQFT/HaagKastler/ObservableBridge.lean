/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.QuasilocalCompleteness

/-!
# Axiom 4 as a bridge principle

This file encodes the blueprint declaration `def:quasilocal-completeness`
(Axiom 4, section 10.3 of the AQFT-in-Lean blueprint):

> All "observables" are quasilocal observables.

## What is being encoded, and why it looks unusual

Axioms 1, 2, 3 and 5 are mathematical conditions on a net: each says something
checkable about the assignment `B ↦ 𝔘(B)` and its structure maps. Axiom 4 is of a
different kind. It is a *bridge principle* -- the one point in the axiom list at
which physical reality is joined to the formalism. One of its two sides, the
physical "observable", is not a mathematical object at all: it is a quantity a
physicist can measure, an equivalence class of measurement procedures. Nothing in
the formalism fixes what happens in a laboratory, so nothing here can define it.

The encoding therefore takes the physical observables as an *abstract primitive* --
an uninterpreted type together with a map into the formalism -- exactly as Axiom 1
(`def:local-algebras`) takes the assignment `algebra` as abstract data rather than
constructing it. The axiom is then the assertion that this map lands among the
quasilocal observables.

## Two consequences worth stating plainly

* **This structure has no mathematical consumers, and that is correct.** A theorem
  that appears to need Axiom 4 in fact needs the mathematics that was historically
  conflated with it, namely the existence of the quasilocal algebra
  (`thrm:quasilocal-algebra-exists`, formalized as `exists_quasilocalAlgebra`), not
  the physical correspondence. Accordingly `HaagKastlerNet` does *not* bundle this
  structure as a field.

* **The correspondence is deliberately not surjective.** Axiom 4 asserts a one-way
  inclusion, and which way it runs is what the name "Completeness" records: the
  formalism is *not too small*, nothing measurable lies outside the quasilocal
  observables. The converse -- that every self-adjoint element of `𝔘` is realised
  by some actual measurement -- is a separate and strictly stronger assertion which
  the blueprint explicitly declines to make. So `measure` below must not be
  strengthened to an equivalence, and the fact that the structure is cheaply
  inhabited (`ObservableCorrespondence.maximal`, or indeed `Observable := Empty`) is
  the correct behaviour of a bridge principle rather than a weakness of the
  encoding.

## The representation-independent reading

A quasilocal observable is defined by `def:quasilocal-observable` as an operator
`π_ω(a)` in a GNS representation, which is representation-*dependent*: read
literally, whether a physical observable corresponds to a quasilocal one would
depend on which state was chosen. That is unsatisfactory for a physical primitive,
so the correspondence here lands in the self-adjoint part of the quasilocal algebra
`𝔘` itself. Being a quasilocal observable *in every representation* is then a
theorem (`isQuasilocalObservable_measure`) rather than an axiom schema.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4
open Physicslib4.GNS

universe u v

/--
**Axiom 4 (Quasilocal Completeness), as a bridge principle.**

An `ObservableCorrespondence` for a quasilocal algebra `Q` is the data of

* `Observable`, the type of physical observables -- an uninterpreted primitive,
  standing for the quantities a physicist can actually measure;
* `measure`, assigning to each physical observable the element of the quasilocal
  algebra `𝔘` that answers it;

subject to the single condition that every value of `measure` is self-adjoint,
which is what it means for it to be a quasilocal observable at the algebra level.

Nothing here is proved about the world, which is as it should be for a bridge
principle: the content of Axiom 4 is precisely that such a correspondence exists
for the physical observables, and that is an interpretive postulate, not a theorem.

Blueprint reference: `def:quasilocal-completeness`.
-/
structure ObservableCorrespondence {U : LocalNet.{u}} {i : Isotony U}
    (Q : QuasilocalAlgebra U i) where
  /-- The physical observables, taken as an abstract primitive. -/
  Observable : Type v
  /-- The correspondence: the element of `𝔘` answering a physical observable. -/
  measure : Observable → Q.carrier
  /-- *Axiom 4.* Every physical observable corresponds to a quasilocal
  observable. At the algebra level this is self-adjointness of its image; that it
  is then a quasilocal observable in the sense of `def:quasilocal-observable`, in
  *every* representation, is `isQuasilocalObservable_measure`. -/
  isSelfAdjoint_measure : ∀ o : Observable, IsSelfAdjoint (measure o)

/--
**Landing the correspondence in the algebra makes completeness
representation-independent.**

`C.measure o` is a self-adjoint element of the quasilocal algebra `𝔘`, and
therefore, for *any* `*`-representation `π` of `𝔘` on a Hilbert space, its image
`π (C.measure o)` is a quasilocal observable in the sense of
`def:quasilocal-observable` (definitionally, `IsQuasilocalObservable`). So what
would otherwise need to be asserted as an axiom schema indexed by a choice of
state is a *single theorem*: being a quasilocal observable holds in every
representation at once.

The proof is by definition: `IsQuasilocalObservable Q π T` asks for a self-adjoint
element `a` of `𝔘` with `T = π a`, and `C.measure o` is the required witness.

The image operator `π (C.measure o)` is self-adjoint, via
`IsQuasilocalObservable.isSelfAdjoint`.

Blueprint reference: `def:quasilocal-completeness`.
-/
theorem isQuasilocalObservable_measure {U : LocalNet.{u}} {i : Isotony U}
    {Q : QuasilocalAlgebra U i} (C : ObservableCorrespondence Q)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Q.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (o : C.Observable) :
    IsQuasilocalObservable Q π (π (C.measure o)) :=
  ⟨C.measure o, C.isSelfAdjoint_measure o, rfl⟩

/--
**The correspondence is inhabited.** This is an *example* establishing that
`ObservableCorrespondence` is not empty, and nothing more: the physical
observables here are the self-adjoint elements of `𝔘`, with `measure` the
inclusion.

It is **not** a claim that the correspondence is surjective. Axiom 4 asserts a
one-way inclusion -- the formalism is *not too small*: nothing a physicist can
measure lies outside the quasilocal observables. The converse, that every
self-adjoint element of `𝔘` is realised by an actual physical measurement, is a
separate and strictly stronger assertion which the blueprint explicitly declines
to make. Cheap inhabitation is therefore the correct behaviour of a bridge
principle, not a defect.

Blueprint reference: `def:quasilocal-completeness`.
-/
def ObservableCorrespondence.maximal {U : LocalNet.{u}} {i : Isotony U}
    (Q : QuasilocalAlgebra U i) : ObservableCorrespondence Q :=
  { Observable := {a : Q.carrier // IsSelfAdjoint a}
    measure := fun a => a.1
    isSelfAdjoint_measure := fun a => a.2 }

end HaagKastler
end AQFT
end Physicslib4
