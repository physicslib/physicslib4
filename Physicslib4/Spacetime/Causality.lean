/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Basic
import Physicslib4.Spacetime.CausalStructure
import Physicslib4.Spacetime.Curves
import Mathlib.Order.Defs.Unbundled

/-!
# Causality on a spacetime

This file formalises the causal-relations vocabulary of section 10.2 of the
AQFT-in-Lean blueprint: trips, causal trips, the chronological precedence
relation `≪`, the causal precedence relation `≺`, and their associated
chronological/causal future/past sets.

## Main definitions

* `Physicslib4.Spacetime.IsGeodesic` (placeholder): a `Prop` placeholder for
  "being a geodesic". Mathlib v4.31.0-rc1 does not provide a packaged
  notion of geodesic in a Lorentzian / pseudo-Riemannian manifold; we
  encode the predicate as an opaque `Prop`-valued definition (defined to
  `True` as a placeholder, see modelling notes).

* `Physicslib4.Spacetime.IsTrip` / `IsCausalTrip`: a trip / causal trip is a
  smooth curve which is piecewise a future-oriented timelike / causal
  geodesic, with designated past and future endpoints.

* `Physicslib4.Spacetime.ChronologicallyPrecedes` (`≪`),
  `Physicslib4.Spacetime.CausallyPrecedes` (`≺`): the existence of a trip /
  causal trip from `p` to `q`.

* `Physicslib4.Spacetime.chronologicalFuture` / `chronologicalPast`,
  `causalFuture` / `causalPast`: pointwise and set-valued versions.

* `Physicslib4.Spacetime.IsSpacelikeRelated`, `IsCompletelySpacelike`: the
  spacelike-relatedness vocabulary.

## Modelling notes

* Geodesics in Lorentzian manifolds are not packaged in Mathlib. We use a
  placeholder predicate `IsGeodesic` set to `True`; downstream agents
  should refine this to the genuine geodesic condition once Mathlib (or
  a sibling project) provides one. This is the *only* mathematical
  compromise in this file.

* The "piecewise" condition on trips is encoded by partitioning the
  parameter space into finitely many sub-intervals on each of which the
  smooth curve restricts to a future-oriented timelike (resp. causal)
  geodesic.
-/

namespace Physicslib4

namespace Spacetime

variable (M : Spacetime)

attribute [instance] Spacetime.topology Spacetime.hausdorff Spacetime.connected
  Spacetime.chartedSpace Spacetime.isManifold Spacetime.tangent_findim

/-! ### Geodesics (placeholder) -/

/--
A *geodesic* of a spacetime, as needed by section 10.2 of the blueprint.

Mathlib v4.31.0-rc1 does not provide a Lorentzian / pseudo-Riemannian
geodesic. We provide an opaque placeholder predicate. Downstream work
should replace this by the genuine geodesic condition (typically:
auto-parallelism of the tangent vector field along the curve with
respect to the Levi-Civita connection of `g`).
-/
@[nolint unusedArguments]
def IsGeodesic (_μ : M.SmoothPath) : Prop := True

/-! ### Trips and chronological precedence -/

/--
A *trip segment* from `p` to `q` in a spacetime `M` is a smooth curve `c`
together with a representative smooth path `μ` that

* is future-oriented and timelike;
* is a geodesic;
* has past endpoint `p` and future endpoint `q`.

This is a single geodesic piece; a full (piecewise) trip is a finite chain
of such segments (see `IsTrip`).

A `TimeOrientation` argument `t` is required to talk about
future-orientation. The endpoints `p, q : M.Carrier` are given as
parameters.
-/
def IsTripSegment (t : M.TimeOrientation) (p q : M.Carrier)
    (c : SmoothCurve M) : Prop :=
  ∃ rep : M.SmoothPath,
    c = SmoothCurve.ofPath M rep ∧
    SmoothPath.IsTimelike M rep ∧
    SmoothPath.IsFutureOriented M rep t ∧
    M.IsGeodesic rep ∧
    IsPastEndpoint M rep p ∧
    IsFutureEndpoint M rep q

/-- *Single-segment chronological precedence*: `p` and `q` are joined by one
future-oriented timelike geodesic segment. -/
def SegmentPrecedes (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  ∃ c : SmoothCurve M, IsTripSegment M t p q c

/--
A *trip* from `p` to `q`: a curve which is *piecewise* a future-oriented
timelike geodesic, i.e. a finite chain of trip segments joined at matching
endpoints. This is encoded as the transitive closure of single-segment
precedence, which is exactly "there is a finite ascending sequence
`p = x₀, x₁, …, xₙ = q` with each consecutive pair joined by a
future-oriented timelike geodesic segment". This genuinely piecewise form
is what makes chronological precedence transitive by concatenation. -/
def IsTrip (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  Relation.TransGen (SegmentPrecedes M t) p q

/-- *Chronological precedence*: `p ≪ q` iff there exists a trip from `p`
to `q`, relative to a fixed time orientation. -/
def ChronologicallyPrecedes (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  IsTrip M t p q

@[inherit_doc] scoped notation:50 p " ≪[" M ", " t "] " q =>
  ChronologicallyPrecedes M t p q

/-! ### Causal trips and causal precedence -/

/--
A *causal trip segment* from `p` to `q` in a spacetime `M` is a smooth curve
`c` together with a representative smooth path `μ` that

* is future-oriented and causal;
* is a (possibly degenerate) geodesic;
* has past endpoint `p` and future endpoint `q`.
-/
def IsCausalTripSegment (t : M.TimeOrientation) (p q : M.Carrier)
    (c : SmoothCurve M) : Prop :=
  ∃ rep : M.SmoothPath,
    c = SmoothCurve.ofPath M rep ∧
    SmoothPath.IsCausal M rep ∧
    SmoothPath.IsFutureOriented M rep t ∧
    M.IsGeodesic rep ∧
    IsPastEndpoint M rep p ∧
    IsFutureEndpoint M rep q

/-- *Single-segment causal precedence*: `p` and `q` are joined by one
future-oriented causal geodesic segment. -/
def CausalSegmentPrecedes (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  ∃ c : SmoothCurve M, IsCausalTripSegment M t p q c

/-- A *causal trip* from `p` to `q`: a curve which is piecewise a
future-oriented causal geodesic, i.e. a finite chain of causal trip
segments. Encoded as the transitive closure of single-segment causal
precedence. -/
def IsCausalTrip (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  Relation.TransGen (CausalSegmentPrecedes M t) p q

/-- *Causal precedence*: `p ≺ q` iff there exists a causal trip from `p`
to `q`, relative to a fixed time orientation. -/
def CausallyPrecedes (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  IsCausalTrip M t p q

@[inherit_doc] scoped notation:50 p " ≺[" M ", " t "] " q =>
  CausallyPrecedes M t p q

/-! ### Chronological and causal futures and pasts -/

/-- The *chronological future* `I^+(p)` of a point `p`. -/
def chronologicalFuture (t : M.TimeOrientation) (p : M.Carrier) :
    Set M.Carrier :=
  {q | ChronologicallyPrecedes M t p q}

/-- The *chronological past* `I^-(p)` of a point `p`. -/
def chronologicalPast (t : M.TimeOrientation) (p : M.Carrier) :
    Set M.Carrier :=
  {q | ChronologicallyPrecedes M t q p}

/-- The *chronological future* `I^+(S)` of a set `S`, defined as
`⋃ p ∈ S, I^+(p)`. -/
def chronologicalFutureSet (t : M.TimeOrientation) (S : Set M.Carrier) :
    Set M.Carrier :=
  ⋃ p ∈ S, chronologicalFuture M t p

/-- The *chronological past* `I^-(S)` of a set `S`, defined as
`⋃ p ∈ S, I^-(p)`. -/
def chronologicalPastSet (t : M.TimeOrientation) (S : Set M.Carrier) :
    Set M.Carrier :=
  ⋃ p ∈ S, chronologicalPast M t p

/-- The *causal future* `J^+(p)` of a point `p`. -/
def causalFuture (t : M.TimeOrientation) (p : M.Carrier) : Set M.Carrier :=
  {q | CausallyPrecedes M t p q}

/-- The *causal past* `J^-(p)` of a point `p`. -/
def causalPast (t : M.TimeOrientation) (p : M.Carrier) : Set M.Carrier :=
  {q | CausallyPrecedes M t q p}

/-- The *causal future* `J^+(S)` of a set `S`, defined as
`⋃ p ∈ S, J^+(p)`. -/
def causalFutureSet (t : M.TimeOrientation) (S : Set M.Carrier) :
    Set M.Carrier :=
  ⋃ p ∈ S, causalFuture M t p

/-- The *causal past* `J^-(S)` of a set `S`, defined as
`⋃ p ∈ S, J^-(p)`. -/
def causalPastSet (t : M.TimeOrientation) (S : Set M.Carrier) :
    Set M.Carrier :=
  ⋃ p ∈ S, causalPast M t p

/-! ### Spacelike relatedness -/

/-- Two points `p₁, p₂` of a spacetime are *spacelike related* if
`p₂ ∉ J^+(p₁) ∪ J^-(p₁)`. -/
def IsSpacelikeRelated (t : M.TimeOrientation) (p₁ p₂ : M.Carrier) : Prop :=
  p₂ ∉ causalFuture M t p₁ ∪ causalPast M t p₁

/-- Two subsets `O₁, O₂` of a spacetime are *completely spacelike* with
respect to each other if every point of `O₁` is spacelike related to every
point of `O₂`. -/
def IsCompletelySpacelike (t : M.TimeOrientation) (O₁ O₂ : Set M.Carrier) :
    Prop :=
  ∀ p₁ ∈ O₁, ∀ p₂ ∈ O₂, IsSpacelikeRelated M t p₁ p₂

/-! ### Chronological implies causal

A timelike trip is in particular a causal trip, so chronological precedence
refines causal precedence and chronological futures/pasts sit inside the
corresponding causal ones. -/

/-- A timelike path is causal. -/
theorem isCausal_of_isTimelike {μ : M.SmoothPath}
    (h : SmoothPath.IsTimelike M μ) : SmoothPath.IsCausal M μ :=
  fun s hs => Or.inl (h s hs)

/-- Every trip segment is a causal trip segment. -/
theorem isCausalTripSegment_of_isTripSegment (t : M.TimeOrientation)
    {p q : M.Carrier} {c : SmoothCurve M} (h : M.IsTripSegment t p q c) :
    M.IsCausalTripSegment t p q c := by
  obtain ⟨rep, hc, htl, hfo, hg, hpe, hfe⟩ := h
  exact ⟨rep, hc, M.isCausal_of_isTimelike htl, hfo, hg, hpe, hfe⟩

/-- Single-segment chronological precedence implies single-segment causal
precedence. -/
theorem causalSegmentPrecedes_of_segmentPrecedes (t : M.TimeOrientation)
    {p q : M.Carrier} (h : M.SegmentPrecedes t p q) :
    M.CausalSegmentPrecedes t p q := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, M.isCausalTripSegment_of_isTripSegment t hc⟩

/-- **Transitivity of chronological precedence.** Two trips joined at a common
point `q` concatenate to a single (piecewise) trip: `p ≪ q` and `q ≪ r` give
`p ≪ r`. This is exactly the transitivity of the transitive closure. -/
theorem chronologicallyPrecedes_trans (t : M.TimeOrientation)
    {p q r : M.Carrier} (h₁ : M.ChronologicallyPrecedes t p q)
    (h₂ : M.ChronologicallyPrecedes t q r) :
    M.ChronologicallyPrecedes t p r :=
  Relation.TransGen.trans h₁ h₂

/-- **Transitivity of causal precedence.** `p ≺ q` and `q ≺ r` give `p ≺ r`. -/
theorem causallyPrecedes_trans (t : M.TimeOrientation)
    {p q r : M.Carrier} (h₁ : M.CausallyPrecedes t p q)
    (h₂ : M.CausallyPrecedes t q r) :
    M.CausallyPrecedes t p r :=
  Relation.TransGen.trans h₁ h₂

/-- Chronological precedence implies causal precedence. -/
theorem causallyPrecedes_of_chronologicallyPrecedes (t : M.TimeOrientation)
    {p q : M.Carrier} (h : M.ChronologicallyPrecedes t p q) :
    M.CausallyPrecedes t p q :=
  Relation.TransGen.mono (fun _ _ => M.causalSegmentPrecedes_of_segmentPrecedes t) _ _ h

/-- The chronological future is contained in the causal future. -/
theorem chronologicalFuture_subset_causalFuture (t : M.TimeOrientation)
    (p : M.Carrier) : chronologicalFuture M t p ⊆ causalFuture M t p :=
  fun _ hq => M.causallyPrecedes_of_chronologicallyPrecedes t hq

/-- The chronological past is contained in the causal past. -/
theorem chronologicalPast_subset_causalPast (t : M.TimeOrientation)
    (p : M.Carrier) : chronologicalPast M t p ⊆ causalPast M t p :=
  fun _ hq => M.causallyPrecedes_of_chronologicallyPrecedes t hq

/-! ### Symmetry of spacelike relatedness -/

/-- Spacelike relatedness is symmetric. -/
theorem isSpacelikeRelated_comm (t : M.TimeOrientation) {p₁ p₂ : M.Carrier} :
    M.IsSpacelikeRelated t p₁ p₂ ↔ M.IsSpacelikeRelated t p₂ p₁ := by
  unfold IsSpacelikeRelated
  simp only [Set.mem_union, causalFuture, causalPast, Set.mem_setOf_eq, not_or]
  tauto

/-- Complete spacelike separation is symmetric in its two regions. -/
theorem isCompletelySpacelike_comm (t : M.TimeOrientation)
    {O₁ O₂ : Set M.Carrier} :
    M.IsCompletelySpacelike t O₁ O₂ ↔ M.IsCompletelySpacelike t O₂ O₁ := by
  constructor <;> intro h p hp q hq <;>
    exact (isSpacelikeRelated_comm M t).mp (h q hq p hp)

/-- Complete spacelike separation is monotone under shrinking either region. -/
theorem isCompletelySpacelike_mono (t : M.TimeOrientation)
    {O₁ O₁' O₂ O₂' : Set M.Carrier} (h₁ : O₁' ⊆ O₁) (h₂ : O₂' ⊆ O₂)
    (h : M.IsCompletelySpacelike t O₁ O₂) :
    M.IsCompletelySpacelike t O₁' O₂' :=
  fun p₁ hp₁ p₂ hp₂ => h p₁ (h₁ hp₁) p₂ (h₂ hp₂)

/-- The empty region is completely spacelike to anything (on the left). -/
@[simp] theorem isCompletelySpacelike_empty_left (t : M.TimeOrientation)
    (O : Set M.Carrier) : M.IsCompletelySpacelike t ∅ O :=
  fun p₁ hp₁ => absurd hp₁ (Set.notMem_empty p₁)

/-- The empty region is completely spacelike to anything (on the right). -/
@[simp] theorem isCompletelySpacelike_empty_right (t : M.TimeOrientation)
    (O : Set M.Carrier) : M.IsCompletelySpacelike t O ∅ :=
  fun _ _ p₂ hp₂ => absurd hp₂ (Set.notMem_empty p₂)

/-- A union of regions is completely spacelike to `O₂` iff each part is. -/
theorem isCompletelySpacelike_union_left (t : M.TimeOrientation)
    (O₁ O₁' O₂ : Set M.Carrier) :
    M.IsCompletelySpacelike t (O₁ ∪ O₁') O₂ ↔
      M.IsCompletelySpacelike t O₁ O₂ ∧ M.IsCompletelySpacelike t O₁' O₂ := by
  constructor
  · intro h
    exact ⟨fun p₁ hp₁ => h p₁ (Or.inl hp₁), fun p₁ hp₁ => h p₁ (Or.inr hp₁)⟩
  · rintro ⟨h, h'⟩ p₁ (hp₁ | hp₁) p₂ hp₂
    · exact h p₁ hp₁ p₂ hp₂
    · exact h' p₁ hp₁ p₂ hp₂

/-- `O₁` is completely spacelike to a union iff it is to each part. -/
theorem isCompletelySpacelike_union_right (t : M.TimeOrientation)
    (O₁ O₂ O₂' : Set M.Carrier) :
    M.IsCompletelySpacelike t O₁ (O₂ ∪ O₂') ↔
      M.IsCompletelySpacelike t O₁ O₂ ∧ M.IsCompletelySpacelike t O₁ O₂' := by
  constructor
  · intro h
    exact ⟨fun p₁ hp₁ p₂ hp₂ => h p₁ hp₁ p₂ (Or.inl hp₂),
      fun p₁ hp₁ p₂ hp₂ => h p₁ hp₁ p₂ (Or.inr hp₂)⟩
  · rintro ⟨h, h'⟩ p₁ hp₁ p₂ (hp₂ | hp₂)
    · exact h p₁ hp₁ p₂ hp₂
    · exact h' p₁ hp₁ p₂ hp₂

/-! ### Monotonicity of set-valued futures and pasts -/

/-- The set-valued chronological future is monotone. -/
theorem chronologicalFutureSet_mono (t : M.TimeOrientation)
    {S T : Set M.Carrier} (h : S ⊆ T) :
    chronologicalFutureSet M t S ⊆ chronologicalFutureSet M t T := by
  intro q hq
  simp only [chronologicalFutureSet, Set.mem_iUnion] at hq ⊢
  obtain ⟨p, hp, hpq⟩ := hq
  exact ⟨p, h hp, hpq⟩

/-- The set-valued chronological past is monotone. -/
theorem chronologicalPastSet_mono (t : M.TimeOrientation)
    {S T : Set M.Carrier} (h : S ⊆ T) :
    chronologicalPastSet M t S ⊆ chronologicalPastSet M t T := by
  intro q hq
  simp only [chronologicalPastSet, Set.mem_iUnion] at hq ⊢
  obtain ⟨p, hp, hpq⟩ := hq
  exact ⟨p, h hp, hpq⟩

/-- The set-valued causal future is monotone. -/
theorem causalFutureSet_mono (t : M.TimeOrientation)
    {S T : Set M.Carrier} (h : S ⊆ T) :
    causalFutureSet M t S ⊆ causalFutureSet M t T := by
  intro q hq
  simp only [causalFutureSet, Set.mem_iUnion] at hq ⊢
  obtain ⟨p, hp, hpq⟩ := hq
  exact ⟨p, h hp, hpq⟩

/-- The set-valued causal past is monotone. -/
theorem causalPastSet_mono (t : M.TimeOrientation)
    {S T : Set M.Carrier} (h : S ⊆ T) :
    causalPastSet M t S ⊆ causalPastSet M t T := by
  intro q hq
  simp only [causalPastSet, Set.mem_iUnion] at hq ⊢
  obtain ⟨p, hp, hpq⟩ := hq
  exact ⟨p, h hp, hpq⟩

/-! ### Alexandrov topology -/

/-- The basis sets generating the Alexandrov topology: all sets of the
form `I^+(p) ∩ I^-(q)` for `p, q ∈ M`. -/
def alexandrovBasis (t : M.TimeOrientation) : Set (Set M.Carrier) :=
  {U | ∃ p q : M.Carrier, U = chronologicalFuture M t p ∩ chronologicalPast M t q}

/--
The *Alexandrov topology* on a spacetime `M`, with respect to a chosen
time orientation `t`: the topology generated by the basis `alexandrovBasis`
consisting of all intersections of chronological futures and pasts.
-/
@[reducible] def alexandrovTopology (t : M.TimeOrientation) :
    TopologicalSpace M.Carrier :=
  TopologicalSpace.generateFrom (alexandrovBasis M t)

/-- Every basis set is open in the Alexandrov topology. -/
theorem isOpen_alexandrov_of_mem_basis (t : M.TimeOrientation)
    {B : Set M.Carrier} (hB : B ∈ alexandrovBasis M t) :
    @IsOpen M.Carrier (alexandrovTopology M t) B :=
  TopologicalSpace.GenerateOpen.basic B hB

end Spacetime

end Physicslib4
