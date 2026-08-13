/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.Isotony
import Physicslib4.Spacetime.MinkowskiDirected
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The quasilocal colimit: index type and directed system

This file begins the construction of the quasilocal algebra *from the net alone*,
as the directed colimit of the local algebras along the Axiom 2 isotony family,
later completed. It supplies the two foundational ingredients that everything
downstream needs:

* the index type of Alexandrov diamonds, ordered by inclusion, together with the
  fact that it is directed (blueprint `lmm:alexandrov-diamonds-isDirected`);
* the isotony family as a `DirectedSystem` in Mathlib's sense
  (blueprint `lmm:isotony-directed-system`).

## Modelling notes

Mathlib's `DirectLimit` API is indexed by a `Preorder` and takes the transition
maps in the shape `f : ∀ i j (h : i ≤ j), T h`, where `T h` is a `FunLike` type.
`Isotony.map` is indexed instead by *subsets together with a proof* of
`IsAlexandrovBasisSet`, so the index is packaged here as the subtype `Diamond`,
whose order is the inclusion order inherited from `Set`. `IsAlexandrovBasisSet B`
is by definition `B ∈ Spacetime.alexandrovBasis ..`, so the geometry proved in
`Physicslib4/Spacetime/MinkowskiDirected.lean` applies to it unchanged.

The transition maps are kept as `StarAlgHom`s rather than bare functions, since
`StarAlgHom` is `FunLike` and satisfies the `RingHomClass`/`StarHomClass`/
`AlgHomClass`/`LinearMapClass` hypotheses under which `DirectLimit` carries its
`Ring`, `StarRing`, `Algebra` and `StarModule` structures.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/-- The **Alexandrov diamonds** of standard Minkowski spacetime, as a type,
ordered by inclusion. This is the index type of the directed system of local
algebras.

Blueprint reference: `lmm:alexandrov-diamonds-isDirected`. -/
abbrev Diamond : Type :=
  {B : Set StandardMinkowskiSpacetime.Carrier // IsAlexandrovBasisSet B}

/-- **The Alexandrov diamonds are directed under inclusion** (set-level form):
any two basis diamonds are contained in a common one. This is the order-theoretic
repackaging of `Physicslib4.Spacetime.alexandrovBasis_directed`.

Blueprint reference: `lmm:alexandrov-diamonds-isDirected`. -/
theorem directedOn_alexandrovBasis :
    DirectedOn (· ⊆ ·)
      (Spacetime.alexandrovBasis StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation) := by
  intro B₁ h₁ B₂ h₂
  exact Spacetime.alexandrovBasis_directed h₁ h₂

/-- **The Alexandrov diamonds are directed under inclusion** (subtype form).
This is the instance the colimit construction consumes, so that downstream nodes
can cite an instance rather than restate a `∀∃` statement.

Blueprint reference: `lmm:alexandrov-diamonds-isDirected`. -/
instance instIsDirectedOrderDiamond : IsDirectedOrder Diamond := by
  constructor
  intro D₁ D₂
  obtain ⟨B, hB, h₁, h₂⟩ :=
    Spacetime.alexandrovBasis_directed D₁.2 D₂.2
  refine ⟨⟨B, hB⟩, h₁, h₂⟩

/-- The transition maps of the directed system of local algebras, in the shape
Mathlib's `DirectLimit` expects: explicit index binders, with the map itself a
`StarAlgHom` (hence `FunLike`). -/
def transitionHom (U : LocalNet) (i : Isotony U) (D₁ D₂ : Diamond) (h : D₁ ≤ D₂) :
    StarAlgHom ℂ (U.algebra D₁.1) (U.algebra D₂.1) :=
  i.map D₁.2 D₂.2 h

/-- **The isotony family is a directed system.** Mathlib's `DirectedSystem` is a
two-field class whose fields are exactly Axiom 2's identity and composition laws,
so the instance is built by supplying `Isotony.map_self` and `Isotony.map_comp`.

Blueprint reference: `lmm:isotony-directed-system`. -/
instance instDirectedSystemIsotony (U : LocalNet) (i : Isotony U) :
    DirectedSystem (fun D : Diamond => U.algebra D.1)
      (fun D₁ D₂ h => transitionHom U i D₁ D₂ h) where
  map_self := by
    intro D x
    change i.map D.2 D.2 (subset_refl D.1) x = x
    rw [i.map_self D.2]
    rfl
  map_map := by
    intro Dₖ Dⱼ Dᵢ hij hjk x
    change ((i.map Dⱼ.2 Dₖ.2 hjk).comp (i.map Dᵢ.2 Dⱼ.2 hij)) x =
      i.map Dᵢ.2 Dₖ.2 (hij.trans hjk) x
    rw [i.map_comp Dᵢ.2 Dⱼ.2 Dₖ.2 hij hjk]

end HaagKastler
end AQFT
end Physicslib4
