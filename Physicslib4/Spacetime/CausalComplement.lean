/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.LorentzianSpacetime

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

end LorentzianSpacetime
end Spacetime
end Physicslib4
