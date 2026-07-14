/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.LorentzianSpacetime
import Mathlib.Order.Closure

/-!
# The causal (spacelike) complement of a region

The **spacelike complement** `B^⊥` of a region `B` in a Lorentzian spacetime is the
set of points completely spacelike-separated from all of `B`:
`B^⊥ = { x | {x} is completely spacelike to B }`.

This is the geometric substrate of locality and Haag duality in algebraic quantum
field theory. We record its order structure:

* `spacelikeComplement_antitone` — `B₁ ⊆ B₂ ⇒ B₂^⊥ ⊆ B₁^⊥`;
* `subset_spacelikeComplement_spacelikeComplement` — `B ⊆ B^⊥⊥`;
* `spacelikeComplement_spacelikeComplement_spacelikeComplement` — `B^⊥⊥⊥ = B^⊥`;
* `subset_spacelikeComplement_iff` — the Galois-type bridge
  `B₁ ⊆ B₂^⊥ ↔ B₁, B₂ completely spacelike`.
-/

namespace Physicslib4
namespace Spacetime

section SpacetimeLevel
variable (M : Spacetime) (t : M.TimeOrientation)

/-- The **spacelike complement** `B^⊥` of a region `B`, with respect to a time
orientation `t`: the points completely spacelike-separated from all of `B`. -/
def spacelikeComplement (B : Set M.Carrier) : Set M.Carrier :=
  {x | Spacetime.IsCompletelySpacelike M t {x} B}

@[simp] theorem mem_spacelikeComplement {B : Set M.Carrier} {x : M.Carrier} :
    x ∈ Spacetime.spacelikeComplement M t B ↔ Spacetime.IsCompletelySpacelike M t {x} B :=
  Iff.rfl

/-- **Galois bridge.** A region lies in the complement of another exactly when the
two are completely spacelike-separated. -/
theorem subset_spacelikeComplement_iff {B₁ B₂ : Set M.Carrier} :
    B₁ ⊆ Spacetime.spacelikeComplement M t B₂ ↔ Spacetime.IsCompletelySpacelike M t B₁ B₂ := by
  constructor
  · intro h p hp q hq
    exact (h hp) p rfl q hq
  · intro h x hx
    rw [mem_spacelikeComplement]
    intro p hp q hq
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact h p hx q hq

end SpacetimeLevel

namespace LorentzianSpacetime

variable (M : LorentzianSpacetime)

/-- The **spacelike complement** `B^⊥` of a region `B`: the points completely
spacelike-separated from all of `B`. -/
def spacelikeComplement (B : Set M.Carrier) : Set M.Carrier :=
  {x | M.IsCompletelySpacelike {x} B}

@[simp] theorem mem_spacelikeComplement {B : Set M.Carrier} {x : M.Carrier} :
    x ∈ M.spacelikeComplement B ↔ M.IsCompletelySpacelike {x} B :=
  Iff.rfl

/-- Complete spacelike separation of a singleton from a region is pointwise. -/
theorem isCompletelySpacelike_singleton_left_iff {x : M.Carrier} {O : Set M.Carrier} :
    M.IsCompletelySpacelike {x} O ↔ ∀ y ∈ O, M.IsCompletelySpacelike {x} {y} := by
  refine ⟨fun h y hy =>
    M.isCompletelySpacelike_mono (subset_refl _) (Set.singleton_subset_iff.mpr hy) h, fun h => ?_⟩
  intro p hp q hq
  exact h q hq p hp q rfl

/-- The spacelike complement is **antitone**: enlarging a region shrinks its
complement. -/
theorem spacelikeComplement_antitone {B₁ B₂ : Set M.Carrier} (h : B₁ ⊆ B₂) :
    M.spacelikeComplement B₂ ⊆ M.spacelikeComplement B₁ := by
  intro x hx
  rw [mem_spacelikeComplement] at hx ⊢
  exact M.isCompletelySpacelike_mono (subset_refl _) h hx

/-- A region is contained in its **double complement**: `B ⊆ B^⊥⊥`. -/
theorem subset_spacelikeComplement_spacelikeComplement (B : Set M.Carrier) :
    B ⊆ M.spacelikeComplement (M.spacelikeComplement B) := by
  intro y hy
  rw [mem_spacelikeComplement, isCompletelySpacelike_singleton_left_iff]
  intro x hx
  rw [mem_spacelikeComplement] at hx
  rw [M.isCompletelySpacelike_comm]
  exact M.isCompletelySpacelike_mono (subset_refl _) (Set.singleton_subset_iff.mpr hy) hx

/-- The **triple complement equals the complement**: `B^⊥⊥⊥ = B^⊥`. -/
theorem spacelikeComplement_spacelikeComplement_spacelikeComplement (B : Set M.Carrier) :
    M.spacelikeComplement (M.spacelikeComplement (M.spacelikeComplement B))
      = M.spacelikeComplement B :=
  Set.Subset.antisymm
    (M.spacelikeComplement_antitone (M.subset_spacelikeComplement_spacelikeComplement B))
    (M.subset_spacelikeComplement_spacelikeComplement (M.spacelikeComplement B))

/-- The complement of the empty region is everything. -/
@[simp] theorem spacelikeComplement_empty :
    M.spacelikeComplement (∅ : Set M.Carrier) = Set.univ := by
  ext x
  simp

/-- **Galois bridge.** A region lies in the complement of another exactly when the
two are completely spacelike-separated. -/
theorem subset_spacelikeComplement_iff {B₁ B₂ : Set M.Carrier} :
    B₁ ⊆ M.spacelikeComplement B₂ ↔ M.IsCompletelySpacelike B₁ B₂ := by
  constructor
  · intro h p hp q hq
    exact (h hp) p rfl q hq
  · intro h x hx
    rw [mem_spacelikeComplement]
    intro p hp q hq
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact h p hx q hq

/-! ### Causally complete regions and the causal closure operator

The double complement `B ↦ B^⊥⊥` is a **closure operator** on the regions of a
Lorentzian spacetime. Its fixed points — the **causally complete** regions — are
the natural regions of algebraic QFT, and they form a complete lattice on which
the spacelike complement `^⊥` acts as an order-reversing involution.

A caveat on orthocomplementation: the spacelike-separation relation used here is
*irreflexive-causality* based (a point is spacelike to itself, since there is no
degenerate closed causal trip), so `B ∩ B^⊥` need not be empty and the full
orthocomplement law `B ⊓ B^⊥ = ⊥` does **not** hold at this generality. What does
hold is the complete lattice with an order-reversing involution (a De Morgan
structure). -/

/-- The **causal closure operator** `B ↦ B^⊥⊥` on the regions of `M`: monotone,
extensive (`B ⊆ B^⊥⊥`), and idempotent (`B^⊥⊥⊥⊥ = B^⊥⊥`). -/
noncomputable def causalClosure : ClosureOperator (Set M.Carrier) :=
  ClosureOperator.mk'
    (fun B => M.spacelikeComplement (M.spacelikeComplement B))
    (fun _ _ h => M.spacelikeComplement_antitone (M.spacelikeComplement_antitone h))
    (fun B => M.subset_spacelikeComplement_spacelikeComplement B)
    (fun B => (M.spacelikeComplement_spacelikeComplement_spacelikeComplement
                (M.spacelikeComplement B)).le)

@[simp] theorem causalClosure_apply (B : Set M.Carrier) :
    M.causalClosure B = M.spacelikeComplement (M.spacelikeComplement B) := rfl

/-- A region is **causally complete** if it equals its own double complement,
`B^⊥⊥ = B` (equivalently, it is a closed element of `causalClosure`). -/
def IsCausallyComplete (B : Set M.Carrier) : Prop :=
  M.spacelikeComplement (M.spacelikeComplement B) = B

theorem isCausallyComplete_iff_isClosed {B : Set M.Carrier} :
    M.IsCausallyComplete B ↔ M.causalClosure.IsClosed B := by
  rw [ClosureOperator.isClosed_iff]
  rfl

/-- The **spacelike complement of any region is causally complete**: `B^⊥⊥⊥ = B^⊥`. -/
theorem isCausallyComplete_spacelikeComplement (B : Set M.Carrier) :
    M.IsCausallyComplete (M.spacelikeComplement B) :=
  M.spacelikeComplement_spacelikeComplement_spacelikeComplement B

/-- The causal closure `B^⊥⊥` of any region is causally complete. -/
theorem isCausallyComplete_causalClosure (B : Set M.Carrier) :
    M.IsCausallyComplete (M.causalClosure B) :=
  M.isCausallyComplete_spacelikeComplement (M.spacelikeComplement B)

/-- On causally complete regions the spacelike complement is an **involution**:
`B^⊥⊥ = B`. -/
theorem spacelikeComplement_spacelikeComplement_of_isCausallyComplete
    {B : Set M.Carrier} (h : M.IsCausallyComplete B) :
    M.spacelikeComplement (M.spacelikeComplement B) = B := h

/-- **The causally complete regions are closed under intersection** (the lattice
meet): `B₁^⊥⊥ = B₁` and `B₂^⊥⊥ = B₂` imply `(B₁ ∩ B₂)^⊥⊥ = B₁ ∩ B₂`. -/
theorem isCausallyComplete_inter {B₁ B₂ : Set M.Carrier}
    (h₁ : M.IsCausallyComplete B₁) (h₂ : M.IsCausallyComplete B₂) :
    M.IsCausallyComplete (B₁ ∩ B₂) := by
  have key : ∀ {A C : Set M.Carrier}, A ⊆ C → M.IsCausallyComplete C →
      M.spacelikeComplement (M.spacelikeComplement A) ⊆ C := by
    intro A C hAC hC
    calc M.spacelikeComplement (M.spacelikeComplement A)
        ⊆ M.spacelikeComplement (M.spacelikeComplement C) :=
          M.spacelikeComplement_antitone (M.spacelikeComplement_antitone hAC)
      _ = C := hC
  exact Set.Subset.antisymm
    (Set.subset_inter (key Set.inter_subset_left h₁) (key Set.inter_subset_right h₂))
    (M.subset_spacelikeComplement_spacelikeComplement _)

/-- The **causally complete regions**, i.e. the closed elements of the causal
closure operator (`B^⊥⊥ = B`). Ordered by inclusion. -/
abbrev CausallyCompleteRegion : Type _ := M.causalClosure.Closeds

/-- The causally complete regions form a **complete lattice** (meets are
intersections; joins are causal closures of unions), transported from the causal
closure operator via its Galois insertion. -/
noncomputable instance : CompleteLattice M.CausallyCompleteRegion :=
  M.causalClosure.gi.liftCompleteLattice

/-- The spacelike complement as an **order-reversing involution** on the complete
lattice of causally complete regions (the causal complement). -/
def causalComplement (B : M.CausallyCompleteRegion) : M.CausallyCompleteRegion :=
  ⟨M.spacelikeComplement B.1,
    M.isCausallyComplete_iff_isClosed.mp (M.isCausallyComplete_spacelikeComplement B.1)⟩

@[simp] theorem causalComplement_coe (B : M.CausallyCompleteRegion) :
    (M.causalComplement B).1 = M.spacelikeComplement B.1 := rfl

/-- Causal complementation is an **involution**: `B^⊥⊥ = B` on causally complete
regions. -/
theorem causalComplement_causalComplement (B : M.CausallyCompleteRegion) :
    M.causalComplement (M.causalComplement B) = B := by
  apply Subtype.ext
  exact M.isCausallyComplete_iff_isClosed.mpr B.2

end LorentzianSpacetime
end Spacetime
end Physicslib4
