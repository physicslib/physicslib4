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

/-- **The spacelike complement is causally convex.** If `p` and `r` are spacelike to
all of `B` and `p ≺ q ≺ r`, then `q` is spacelike to all of `B`, by transitivity of
causal precedence. -/
theorem spacelikeComplement_isCausallyConvex (B : Set M.Carrier) :
    IsCausallyConvex M t (Spacetime.spacelikeComplement M t B) := by
  intro p q r hp hr hpq hqr
  rw [mem_spacelikeComplement]
  intro a ha b hb
  rw [Set.mem_singleton_iff] at ha
  subst ha
  rw [mem_spacelikeComplement] at hp hr
  have hp_pb : IsSpacelikeRelated M t p b := hp p (by simp) b hb
  have hr_rb : IsSpacelikeRelated M t r b := hr r (by simp) b hb
  unfold IsSpacelikeRelated at hp_pb hr_rb
  simp only [Set.mem_union, causalFuture, causalPast, Set.mem_setOf_eq, not_or] at hp_pb hr_rb
  rcases hp_pb with ⟨hpb_not, hbp_not⟩
  rcases hr_rb with ⟨hrb_not, hbr_not⟩
  unfold IsSpacelikeRelated
  simp only [Set.mem_union, causalFuture, causalPast, Set.mem_setOf_eq, not_or]
  constructor
  · intro hqb
    apply hpb_not
    exact causallyPrecedes_trans M t hpq hqb
  · intro hbq
    apply hbr_not
    exact causallyPrecedes_trans M t hbq hqr

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

/-- Arbitrary intersections of causally complete sets are causally complete. -/
theorem isCausallyComplete_iInter {ι : Sort*} (B : ι → Set M.Carrier)
    (h : ∀ i, M.IsCausallyComplete (B i)) : M.IsCausallyComplete (⋂ i, B i) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iInter]
    intro i
    have hxi : x ∈ M.spacelikeComplement (M.spacelikeComplement (⋂ i, B i)) := hx
    have h_sub : ⋂ i, B i ⊆ B i := Set.iInter_subset B i
    have h_comp : M.spacelikeComplement (B i) ⊆ M.spacelikeComplement (⋂ i, B i) :=
      M.spacelikeComplement_antitone h_sub
    have h_double_comp : M.spacelikeComplement (M.spacelikeComplement (⋂ i, B i))
        ⊆ M.spacelikeComplement (M.spacelikeComplement (B i)) :=
      M.spacelikeComplement_antitone h_comp
    have hxBi : x ∈ M.spacelikeComplement (M.spacelikeComplement (B i)) := h_double_comp hxi
    rw [h i] at hxBi
    exact hxBi
  · exact M.subset_spacelikeComplement_spacelikeComplement (⋂ i, B i)

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

/-! ### De Morgan laws for the spacelike complement -/

/-- **Binary De Morgan (set level).** The spacelike complement turns a union into
an intersection: `(B₁ ∪ B₂)^⊥ = B₁^⊥ ∩ B₂^⊥`. -/
theorem spacelikeComplement_union (B₁ B₂ : Set M.Carrier) :
    M.spacelikeComplement (B₁ ∪ B₂)
      = M.spacelikeComplement B₁ ∩ M.spacelikeComplement B₂ := by
  ext x
  simp_rw [mem_spacelikeComplement, Set.mem_inter_iff]
  exact M.isCompletelySpacelike_union_right {x} B₁ B₂

/-- **Infinitary De Morgan (set level).** The spacelike complement turns an
indexed union into an intersection: `(⋃ i, B i)^⊥ = ⋂ i, (B i)^⊥`. -/
theorem spacelikeComplement_iUnion {ι : Sort*} (B : ι → Set M.Carrier) :
    M.spacelikeComplement (⋃ i, B i) = ⋂ i, M.spacelikeComplement (B i) := by
  ext x
  simp_rw [mem_spacelikeComplement, Set.mem_iInter]
  constructor
  · intro h i
    exact M.isCompletelySpacelike_mono (subset_refl _) (Set.subset_iUnion B i) h
  · intro h
    rw [isCompletelySpacelike_singleton_left_iff]
    intro y hy
    rcases Set.mem_iUnion.1 hy with ⟨i, hy⟩
    have hxBi : M.IsCompletelySpacelike {x} (B i) := h i
    rw [isCompletelySpacelike_singleton_left_iff] at hxBi
    exact hxBi y hy

/-! ### De Morgan laws for the causal complement

On the complete lattice of causally complete regions the causal complement is an
order-reversing involution, hence satisfies the full De Morgan laws. The lattice
is not linearly ordered, so the equalities below rely on the involution
(`causalComplement_causalComplement`), not on antitonicity alone. -/

/-- The causal complement is **antitone** (order-reversing) on the lattice of
causally complete regions. -/
private theorem coe_inf (B₁ B₂ : M.CausallyCompleteRegion) : (B₁ ⊓ B₂).1 = B₁.1 ∩ B₂.1 := by
  rfl

private theorem coe_sup (B₁ B₂ : M.CausallyCompleteRegion) :
    (B₁ ⊔ B₂).1 = M.causalClosure (B₁.1 ∪ B₂.1) := by
  rfl

private theorem coe_top : (⊤ : M.CausallyCompleteRegion).1 = (Set.univ : Set M.Carrier) := by
  rfl

private theorem coe_bot :
    (⊥ : M.CausallyCompleteRegion).1 = M.causalClosure (∅ : Set M.Carrier) := by
  rfl

private theorem coe_iSup {ι : Sort*} (B : ι → M.CausallyCompleteRegion) :
    (⨆ i, B i).1 = M.causalClosure (⋃ i, (B i).1) := by
  have h := (GaloisInsertion.l_iSup_u M.causalClosure.gi B)
  have h' := congrArg Subtype.val h.symm
  have h'' : (M.causalClosure.toCloseds (⨆ i, (B i).1)).1 = M.causalClosure (⨆ i, (B i).1) := rfl
  rw [h''] at h'
  rw [Set.iSup_eq_iUnion] at h'
  exact h'

private theorem coe_iInf {ι : Sort*} (B : ι → M.CausallyCompleteRegion) :
    (⨅ i, B i).1 = M.causalClosure (⋂ i, (B i).1) := by
  have h := (GaloisInsertion.l_iInf_u M.causalClosure.gi B)
  have h' := congrArg Subtype.val h.symm
  have h'' : (M.causalClosure.toCloseds (⨅ i, (B i).1)).1 = M.causalClosure (⨅ i, (B i).1) := rfl
  rw [h''] at h'
  rw [Set.iInf_eq_iInter] at h'
  exact h'

theorem causalComplement_antitone : Antitone M.causalComplement := by
  intro B₁ B₂ h
  rw [← Subtype.coe_le_coe]
  have h' : B₁.1 ⊆ B₂.1 := h
  rw [causalComplement_coe, causalComplement_coe]
  exact M.spacelikeComplement_antitone h'

/-- `⊥^⊥ = ⊤`: the complement of the least region is the greatest. -/
theorem causalComplement_bot :
    M.causalComplement (⊥ : M.CausallyCompleteRegion) = ⊤ := by
  apply Subtype.ext
  calc
    (M.causalComplement (⊥ : M.CausallyCompleteRegion)).1
        = M.spacelikeComplement (⊥ : M.CausallyCompleteRegion).1 := rfl
    _ = M.spacelikeComplement (M.causalClosure (∅ : Set M.Carrier)) := by rw [coe_bot]
    _ = M.spacelikeComplement
          (M.spacelikeComplement (M.spacelikeComplement (∅ : Set M.Carrier))) := rfl
    _ = M.spacelikeComplement (∅ : Set M.Carrier) := by
      rw [M.spacelikeComplement_spacelikeComplement_spacelikeComplement]
    _ = Set.univ := by rw [M.spacelikeComplement_empty]
    _ = (⊤ : M.CausallyCompleteRegion).1 := by rw [coe_top]

/-- `⊤^⊥ = ⊥`: the complement of the greatest region is the least. -/
theorem causalComplement_top :
    M.causalComplement (⊤ : M.CausallyCompleteRegion) = ⊥ := by
  apply Subtype.ext
  calc
    (M.causalComplement (⊤ : M.CausallyCompleteRegion)).1
        = M.spacelikeComplement (⊤ : M.CausallyCompleteRegion).1 := rfl
    _ = M.spacelikeComplement (Set.univ : Set M.Carrier) := by rw [coe_top]
    _ = M.spacelikeComplement (M.spacelikeComplement (∅ : Set M.Carrier)) := by
      rw [M.spacelikeComplement_empty]
    _ = M.causalClosure (∅ : Set M.Carrier) := rfl
    _ = (⊥ : M.CausallyCompleteRegion).1 := by rw [coe_bot]

/-- **Binary De Morgan (join).** `(B₁ ⊔ B₂)^⊥ = B₁^⊥ ⊓ B₂^⊥`. -/
theorem causalComplement_sup (B₁ B₂ : M.CausallyCompleteRegion) :
    M.causalComplement (B₁ ⊔ B₂) = M.causalComplement B₁ ⊓ M.causalComplement B₂ := by
  apply Subtype.ext
  calc
    (M.causalComplement (B₁ ⊔ B₂)).1 = M.spacelikeComplement ((B₁ ⊔ B₂).1) := rfl
    _ = M.spacelikeComplement (M.causalClosure (B₁.1 ∪ B₂.1)) := by rw [coe_sup]
    _ = M.spacelikeComplement (M.spacelikeComplement (M.spacelikeComplement (B₁.1 ∪ B₂.1))) := rfl
    _ = M.spacelikeComplement (B₁.1 ∪ B₂.1) := by
      rw [M.spacelikeComplement_spacelikeComplement_spacelikeComplement]
    _ = M.spacelikeComplement B₁.1 ∩ M.spacelikeComplement B₂.1 := by
      rw [M.spacelikeComplement_union]
    _ = (M.causalComplement B₁).1 ∩ (M.causalComplement B₂).1 := rfl
    _ = ((M.causalComplement B₁) ⊓ (M.causalComplement B₂)).1 := by rw [coe_inf]

/-- **Binary De Morgan (meet).** `(B₁ ⊓ B₂)^⊥ = B₁^⊥ ⊔ B₂^⊥`. -/
theorem causalComplement_inf (B₁ B₂ : M.CausallyCompleteRegion) :
    M.causalComplement (B₁ ⊓ B₂) = M.causalComplement B₁ ⊔ M.causalComplement B₂ := by
  apply Subtype.ext
  have h₁ : M.spacelikeComplement (M.spacelikeComplement B₁.1) = B₁.1 :=
    M.isCausallyComplete_iff_isClosed.mpr B₁.2
  have h₂ : M.spacelikeComplement (M.spacelikeComplement B₂.1) = B₂.1 :=
    M.isCausallyComplete_iff_isClosed.mpr B₂.2
  calc
    (M.causalComplement (B₁ ⊓ B₂)).1 = M.spacelikeComplement ((B₁ ⊓ B₂).1) := rfl
    _ = M.spacelikeComplement (B₁.1 ∩ B₂.1) := by rw [coe_inf]
    _ = M.spacelikeComplement (M.spacelikeComplement (M.spacelikeComplement B₁.1)
        ∩ M.spacelikeComplement (M.spacelikeComplement B₂.1)) := by
      rw [h₁, h₂]
    _ = M.spacelikeComplement (M.spacelikeComplement (M.spacelikeComplement B₁.1
        ∪ M.spacelikeComplement B₂.1)) := by
      rw [M.spacelikeComplement_union]
    _ = M.causalClosure (M.spacelikeComplement B₁.1 ∪ M.spacelikeComplement B₂.1) := rfl
    _ = ((M.causalComplement B₁) ⊔ (M.causalComplement B₂)).1 := by
      rw [coe_sup, causalComplement_coe, causalComplement_coe]

/-- **Infinitary De Morgan (join).** `(⨆ i, B i)^⊥ = ⨅ i, (B i)^⊥`. -/
theorem causalComplement_iSup {ι : Sort*} (B : ι → M.CausallyCompleteRegion) :
    M.causalComplement (⨆ i, B i) = ⨅ i, M.causalComplement (B i) := by
  apply Subtype.ext
  calc
    (M.causalComplement (⨆ i, B i)).1 = M.spacelikeComplement ((⨆ i, B i).1) := rfl
    _ = M.spacelikeComplement (M.causalClosure (⋃ i, (B i).1)) := by rw [coe_iSup]
    _ = M.spacelikeComplement (M.spacelikeComplement (M.spacelikeComplement (⋃ i, (B i).1))) := rfl
    _ = M.spacelikeComplement (⋃ i, (B i).1) := by
      rw [M.spacelikeComplement_spacelikeComplement_spacelikeComplement]
    _ = ⋂ i, M.spacelikeComplement ((B i).1) := by rw [M.spacelikeComplement_iUnion]
    _ = ⋂ i, (M.causalComplement (B i)).1 := by simp_rw [causalComplement_coe]
    _ = M.causalClosure (⋂ i, (M.causalComplement (B i)).1) := by
      have hclosed : M.IsCausallyComplete (⋂ i, (M.causalComplement (B i)).1) :=
        isCausallyComplete_iInter M (fun i => (M.causalComplement (B i)).1) fun i => by
          exact (M.causalComplement (B i)).2
      have hclosed' : M.causalClosure (⋂ i, (M.causalComplement (B i)).1)
          = ⋂ i, (M.causalComplement (B i)).1 := by
        rw [M.causalClosure_apply, hclosed]
      rw [hclosed']
    _ = (⨅ i, M.causalComplement (B i)).1 := by rw [coe_iInf]

/-- **Infinitary De Morgan (meet).** `(⨅ i, B i)^⊥ = ⨆ i, (B i)^⊥`. -/
theorem causalComplement_iInf {ι : Sort*} (B : ι → M.CausallyCompleteRegion) :
    M.causalComplement (⨅ i, B i) = ⨆ i, M.causalComplement (B i) := by
  apply Subtype.ext
  have hclosed (i : ι) : M.spacelikeComplement (M.spacelikeComplement ((B i).1)) = (B i).1 :=
    M.isCausallyComplete_iff_isClosed.mpr (B i).2
  calc
    (M.causalComplement (⨅ i, B i)).1 = M.spacelikeComplement ((⨅ i, B i).1) := rfl
    _ = M.spacelikeComplement (M.causalClosure (⋂ i, (B i).1)) := by rw [coe_iInf]
    _ = M.spacelikeComplement (M.spacelikeComplement (M.spacelikeComplement (⋂ i, (B i).1))) := rfl
    _ = M.spacelikeComplement (⋂ i, (B i).1) := by
      rw [M.spacelikeComplement_spacelikeComplement_spacelikeComplement]
    _ = M.spacelikeComplement (⋂ i, M.spacelikeComplement (M.spacelikeComplement ((B i).1))) := by
      simp_rw [hclosed]
    _ = M.spacelikeComplement (M.spacelikeComplement (⋃ i, M.spacelikeComplement ((B i).1))) := by
      rw [M.spacelikeComplement_iUnion]
    _ = M.causalClosure (⋃ i, M.spacelikeComplement ((B i).1)) := rfl
    _ = M.causalClosure (⋃ i, (M.causalComplement (B i)).1) := by
      simp_rw [causalComplement_coe]
    _ = (⨆ i, M.causalComplement (B i)).1 := by rw [coe_iSup]

/-! ### Causally complete regions are causally convex -/

/-- **A causally complete region is causally convex.** Since `B = B^⊥⊥` is a spacelike
complement (of `B^⊥`), it inherits causal convexity from
`spacelikeComplement_isCausallyConvex`. -/
theorem isCausallyConvex_of_isCausallyComplete {B : Set M.Carrier}
    (h : M.IsCausallyComplete B) :
    Spacetime.IsCausallyConvex M.toSpacetime M.timeOrientation B :=
  h ▸ spacelikeComplement_isCausallyConvex M.toSpacetime M.timeOrientation (M.spacelikeComplement B)

/-- Every element of the causally-complete-region lattice is causally convex. -/
theorem CausallyCompleteRegion.isCausallyConvex (B : M.CausallyCompleteRegion) :
    Spacetime.IsCausallyConvex M.toSpacetime M.timeOrientation B.1 := by
  exact M.isCausallyConvex_of_isCausallyComplete (M.isCausallyComplete_iff_isClosed.mpr B.2)

end LorentzianSpacetime
end Spacetime
end Physicslib4
