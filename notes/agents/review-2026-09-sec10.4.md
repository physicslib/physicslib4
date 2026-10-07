# Audit: blueprint §10.4 "Spacetime"

Date: 2026-09-25
Scope: `blueprint/src/sections/sec10/spacetime.tex` (all ~90 numbered nodes,
from `def:spacetime` through `def:cross-metric-isometry`), and the Lean files
its `\lean{}` tags cite, principally `Physicslib4/Spacetime/{Basic, CausalStructure,
Curves, Causality, CausalComplement, LorentzianSpacetime, Minkowski,
MinkowskiDirected, MinkowskiDilation, LorentzCauchySchwarz, LorentzCone,
LorentzOrthogonal, Diffeo, DiffeoPath, Isometry, IsometryCausality,
IsometryTopology, Pullback, CrossMetricIsometry}.lean`.

## Method (tool-verified vs. judged by reading)

Tool-verified:
- All 294 distinct `\lean{...}` names in `spacetime.tex` resolve against
  `blueprint/lean_decls` (0 missing) and every short name has at least one
  occurrence somewhere under `Physicslib4/` (0 missing).
- `grep` for `sorry`, `admit`, `native_decide`, `implemented_by`,
  `skipKernelTC`, `nolint`, `axiom`, `maxHeartbeats`, `Restriction:`,
  `: Prop := True` across `Physicslib4/Spacetime/`.
- `lake env lean` + `#print axioms` on six sampled theorems spanning the
  causal-order core, the causally-complete-region lattice, curve
  well-definedness, and the Minkowski/dilation/cross-isometry results — all
  six report exactly `[propext, Classical.choice, Quot.sound]`.
- `.git/lean-kit/verify-receipt.json` (last `lake build` + `lake lint`,
  2026-09-18) and `git log` since that timestamp restricted to
  `Physicslib4/Spacetime/` and the blueprint file (no hits): the receipt is
  stale for the repository as a whole (many unrelated spectral-theory commits
  since), but nothing in §10.4's scope changed after it, so its content is not
  invalidated for this section.
- No `.git/lean-kit/approvals.json` file exists — no approvals in effect to
  review.

Judged by reading (no tool support): the statement audit table below, all
"match" classifications, and the two non-match findings (Critical-1,
Minor-1/2) were established by reading blueprint prose against the Lean
declarations side by side, tracing `\uses{}`/dependency chains by hand, and
tracing which downstream Lean declarations actually consume `IsGeodesic`.

## Classification counts

Of the ~90 blueprint nodes with `\lean{}` in scope:
- **match**: all of them at the *individual declaration* level (Lean signature
  vs. blueprint prose line up exactly, including quantifier order, the
  existential vs. universal reading of "smooth", edge cases such as the empty
  region, the zero vector, and singleton parameter spaces).
- **different objects** (one, but with wide blast radius): `def:trip` /
  `def:causal-trip`, and by inheritance every theorem downstream of `≪`/`≺`.
  See Critical-1.
- **can't determine**: none.
- No case of "Lean assumes more" or "Lean concludes less" was found at the
  level of an individual `\lean{}`-tagged statement — the mismatches found are
  structural (one vacuous side-condition polluting a large dependency
  subgraph) rather than per-statement hypothesis/conclusion drift.

## Critical

**C-1. `IsGeodesic := True` is not a per-node restriction; it is the defining
condition of `≪`/`≺`, and essentially the whole back half of the chapter is a
theorem about the resulting non-geodesic relation.**

- `Physicslib4/Spacetime/Causality.lean:76`:
  ```
  @[nolint unusedArguments]
  def IsGeodesic (_μ : M.SmoothPath) : Prop := True
  ```
  This is already known (flagged in `notes/agents/review-2026-09-sec10.1-10.7.md`
  for the `general-covariance-in-curved-spacetime` dependency chain) and the
  blueprint has an honest remark at `spacetime.tex:327-328` ("Remark (geodesic
  placeholder in the formalization)") next to `def:trip`/`def:causal-trip`.
  I re-verified the definition and traced its consumers directly rather than
  taking the remark's scope at face value.
- Consumers, confirmed by reading `Causality.lean:95-165`: `IsTripSegment`,
  `IsCausalTripSegment` both include an `M.IsGeodesic rep` conjunct that is
  vacuously true, so both segment predicates reduce to "future-oriented
  timelike (resp. causal) `C^∞` curve with the prescribed past/future
  endpoints" — no geodesic (auto-parallel-tangent) condition at all. `IsTrip`,
  `IsCausalTrip` are the transitive closures of these segment relations, and
  `ChronologicallyPrecedes` (`≪`)/`CausallyPrecedes` (`≺`) are literally these.
- The blast radius is not confined to `def:trip`/`def:causal-trip`. Every one
  of the following blueprint nodes states a theorem about `≪`/`≺` as defined,
  hence about the non-geodesic relation, even though nothing in their own
  statement or proof mentions geodesics: `thrm:precedence-transitive`,
  `def:no-closed-causal-curve`, `thrm:causal-order-refinements`,
  `def:chronological-future-and-chronological-past`,
  `def:causal-future-and-causal-past`, `lmm:chronological-implies-causal`,
  `lmm:future-past-monotone`, the entire "Causal diamonds" subsection
  (`def:causal-diamond` through `thrm:causal-complement-de-morgan`), the
  entire "Causal convexity" subsection, `def:alexandrov-topology` and its
  subsection, `lmm:minkowski-*` directedness lemmas,
  `thrm:minkowski-dilation-causal-automorphism`, the "Isometries and basis-set
  preservation" subsection, and the "Pullback metrics and cross-metric
  isometries" subsection — i.e. everything from `spacetime.tex:309` to the end
  of the file bottoms out on `≪`/`≺`.
- This does not make any Lean theorem *false*: `IsGeodesic := True` only
  widens the trip/causal-trip relations (drops a conjunct), so every proved
  inclusion/closure/lattice/topology fact still holds for the wider relation.
  But the blueprint's English prose for these ~40 downstream nodes reads as
  "the trip-based order relation of §10.4" without repeating that the trips in
  question are not (yet) geodesics; a reader who only encounters, say,
  `thrm:causally-complete-lattice` or `thrm:causal-complement-de-morgan` has no
  local signal that the causal order underneath is coarser than intended.
- *Suggested fix (report only, not applied)*: either (a) add the
  `**Restriction:**` marker required by `CLAUDE.md` to `IsGeodesic`'s
  docstring (`Causality.lean:68-75`), naming Stone's-theorem-style blocker
  precisely (a Lorentzian Levi-Civita connection is unavailable in the pinned
  Mathlib), and (b) add one sentence to the blueprint at the first downstream
  node that is genuinely a "chapter-wide" consequence (e.g.
  `def:alexandrov-topology` or the "Causal diamonds" subsection header)
  pointing back to the remark at `def:trip`, so the scope of the caveat is
  visible without following the whole dependency graph by hand.

## Major

None found. (The one structural gap is C-1; no per-statement hypothesis
mismatch, no false or junk-value-dependent statement, and no
non-`\leanok`-honest node was found in this section.)

## Minor

**m-1. Two stale module/field docstrings still describe the abandoned
chart-local ("`ContDiffWithinAt`") smoothness formulation, contradicting the
correct bundle-section (`ContMDiff`) field they sit next to.**

- `Physicslib4/Spacetime/Basic.lean:48-51` (file-level docstring): "The
  'smoothness' of `g` is encoded via the standard idiom used by
  `PseudoRiemannianMetric`: smoothness of the coordinate-expression in any
  extended chart, applied to two arbitrary constant vectors in the model
  space `ℝ⁴`." The actual `contMDiff` field (`Basic.lean:169-174`, correctly
  documented at `Basic.lean:152-168`) is the bundle-section `ContMDiff`
  statement mandated by the current `def:spacetime` text, not a chart-local
  statement on constant vectors.
- `Physicslib4/Spacetime/CausalStructure.lean:145-158` (structure-level
  docstring for `TimeOrientation`): "`smooth`: smoothness of the section in
  any extended chart, expressed via the chart-local form of the field... a
  genuine `Prop` field of the structure (a `ContDiffWithinAt` condition on the
  chart-local representative)." The actual `smooth` field
  (`CausalStructure.lean:166-177`) is the bundle-section `ContMDiff` statement,
  correctly documented immediately below in the same file.
- Both are leftovers from the chart-local → bundle-section migration that the
  blueprint itself calls out as "historical" at `spacetime.tex:1299` for a
  different node (`lmm:pullback-metric-smooth-in-charts`'s label name); these
  two docstrings are the same kind of leftover but were not caught by that
  note. *Suggested fix*: reword both to describe the `ContMDiff`
  bundle-section form (or delete the stale sentence and refer to the
  field-level docstring immediately below, which is already correct).

**m-2. `Curve`/`SmoothCurve`/`OrientedSmoothCurve` are quotients by relations
that are never shown to be equivalence relations.**

- `Physicslib4/Spacetime/Curves.lean:333` (`def Curve : Type := Quot
  M.PathEquiv`) docstring: "We package this as a `Quot` over the (possibly
  non-equivalence) relation `PathEquiv`; the actual equivalence-class
  structure is left implicit." Confirmed by grep: there is no
  `PathEquiv`-is-`Equivalence` (or `.refl`/`.symm`/`.trans`) lemma anywhere in
  the file, nor for `SmoothPathEquiv` or `OrientedSmoothPathEquiv`.
- This is not a soundness gap — `Quot r` always denotes the quotient by the
  equivalence closure `Relation.EqvGen r` (used correctly throughout, e.g.
  `Quot.eqvGen_exact` in `isTimelikeSmoothCurve_ofPath_iff`,
  `Curves.lean:611-616`), so the well-definedness proofs are unaffected
  regardless of whether `PathEquiv` itself happens to already be reflexive/
  symmetric/transitive. But the blueprint's `def:curves` reads "an equivalence
  class of paths equivalent under homeomorphisms," which presupposes the
  relation is an equivalence relation; nobody has recorded that fact for
  `PathEquiv`, `SmoothPathEquiv`, or `OrientedSmoothPathEquiv` in Lean.
  *Suggested fix*: either add the three straightforward `Equivalence` lemmas
  (reflexivity via `id`; symmetry by swapping the witness pair `(φ, ψ)`;
  transitivity by composing) or drop the hedge from the docstring once they
  exist.

**m-3. `SmoothPath.nonvanishing` docstring says "at each interior point" but
the field quantifies over the whole parameter space.**

- `Physicslib4/Spacetime/Curves.lean:109-114`: docstring reads "non-zero at
  each interior point of the parameter space," but the field is
  `∀ s ∈ parameterSpace, mfderivWithin ... s (1:ℝ) ≠ 0`, i.e. quantified over
  all of `Σ` including its two boundary points, matching the blueprint's
  "smooth path" definition (`spacetime.tex:34-41`, no interior restriction).
  The code is correct and matches the blueprint; only the English comment is
  imprecise. *Suggested fix*: reword to "at every point of the parameter
  space."

## Lean quality

- No duplication beyond the deliberate, explicitly-labelled
  single-metric/cross-metric pairs (e.g. `Isometry.pushforwardPath` vs.
  `CrossIsometry.pushforwardPath_isTimelike`), which the blueprint itself
  documents as intentional copies with the target metric changed
  (`spacetime.tex:1508-1521`) rather than duplication to be golfed.
- `IsTripSegment`'s doc-comment (`Causality.lean:79-93`) lists "is a geodesic"
  as one of three bullet conditions on equal footing with "is future-oriented
  and timelike" and "has past/future endpoint `p`/`q`" — read on its own, this
  bullet reads as a live constraint. It is currently vacuous (C-1). This is a
  narrower, file-local version of the same issue as C-1; flagging separately
  because a reader of just this docstring (without cross-referencing
  `IsGeodesic`'s own docstring) would not learn that the bullet is inert.
- No oversized single-tactic-block proofs; the longest proof in scope
  (`Physicslib4/Spacetime/Minkowski.lean`'s pullback/contMDiff machinery,
  outside the file list above but adjacent) is well-commented and structured
  in `have`-steps, consistent with the blueprint's own detailed proof prose
  for the corresponding nodes (`lmm:pullback-metric-smooth-in-charts`).
- No multi-conclusion conjunctions that quietly narrow scope were found; where
  the blueprint states a conjunction (e.g. `thrm:causally-complete-lattice`'s
  "form a complete lattice... spacelike complement is causally complete...
  causal complement is an order-reversing involution"), the `\lean{}` list
  cites one declaration per conjunct plus the bundling `CausallyCompleteRegion`
  abbreviation, and the blueprint prose itself flags that the `CompleteLattice`
  instance is anonymous (`spacetime.tex:587`) — confirmed: it is indeed an
  anonymous `noncomputable instance` at `CausalComplement.lean:246`.

## Integrity checklist

- `sorry` / `admit` / `native_decide` / `implemented_by` / `skipKernelTC`:
  none in `Physicslib4/Spacetime/` (the only two grep hits for the string
  "sorry" are inside docstring prose explaining that the structures are
  sorry-free, at `Basic.lean:59` and `Curves.lean:53`).
- `nolint`: exactly one use in scope,
  `Causality.lean:75` (`@[nolint unusedArguments]` on `IsGeodesic`) — justified
  by the placeholder's nature (the argument is unused because the predicate is
  `True`), but see C-1 for the missing `**Restriction:**` marker.
- `axiom`: none declared in `Physicslib4/Spacetime/`.
- `maxHeartbeats`: one use, `Physicslib4/Spacetime/Pullback.lean:154`
  (`set_option maxHeartbeats 1000000 in`), a performance escape hatch on one
  proof, not a correctness concern.
- `#print axioms` (via `lake env lean` on a `/tmp` scratch file, oleans were
  already cached so this used the build cache, not a fresh `lake build`) on
  `chronologicallyPrecedes_trans`, `causallyPrecedes_antisymm`,
  `LorentzianSpacetime.isCausallyConvex_of_isCausallyComplete`,
  `LorentzianSpacetime.causalComplement_iSup`,
  `isTimelikeSmoothCurve_ofPath_iff`, `parameterSpace_eq_Icc_of_endpoints`,
  `isTopologicalBasis_alexandrovBasis_standardMinkowski`,
  `alexandrovBasis_image_smul`, `exists_minkowskiForm_smul_ne`, and
  `CrossIsometry.chronologicalFuture_image`: all ten report exactly
  `[propext, Classical.choice, Quot.sound]`. No hidden `sorryAx` or custom
  axiom.
- `verify-receipt.json`: `lake build` and `lake lint` both exited 0 on
  2026-09-18T14:08:28Z. No commit since then touches
  `Physicslib4/Spacetime/*` or `blueprint/src/sections/sec10/spacetime.tex`,
  so the receipt is current *for this section specifically*, even though the
  repository as a whole has since had ~15 unrelated commits (spectral-theory
  work) that would need a fresh `lake build`/`lake lint` pass to be covered by
  the same receipt.
- Approvals: `.git/lean-kit/approvals.json` does not exist — no approvals in
  effect to review for this section.
- `\leanok` honesty: every `\leanok`-marked node checked (all of them; see
  Method) corresponds to a Lean declaration with no `sorry` and standard
  axioms only, so `\leanok` is truthful throughout this section.

## Blueprint soundness

- No inaccurate `\uses{}` or dangling `\ref` was found; every `\label{}`
  referenced by a `\ref{}` or `\uses{}` in this file resolves to a `\label{}`
  defined earlier in the same file (spot-checked the longest dependency
  chains: `thrm:causal-complement-de-morgan`, `thrm:causally-complete-convex`,
  `lmm:pullback-alexandrov-homeomorphism`, `thrm:pullback-is-lorentzian-spacetime`).
- The blueprint is unusually candid about its own implementation quirks — the
  anonymous `CompleteLattice` instance (`spacetime.tex:587`), the historical
  but now-inaccurate label name `lmm:pullback-metric-smooth-in-charts`
  (`spacetime.tex:1299`), the failure of the full orthocomplement law
  (`spacetime.tex:587`, confirmed against the matching docstring caveat at
  `CausalComplement.lean:158-163`), and the geodesic placeholder itself
  (`spacetime.tex:327-328`). All of these self-reports were checked against
  the Lean source and found accurate. The one gap is that the geodesic
  caveat's *scope* (C-1) is not repeated at the many downstream nodes it
  actually affects.
- No gaps found in the informal proofs read against their Lean counterparts;
  the algebraic proof sketches (reverse Cauchy-Schwarz, the sign lemma for the
  future cone, the De Morgan laws for the causal complement) match their Lean
  proofs step for step, including the notable non-obvious point that the
  binary/infinitary De Morgan equalities for the causal complement need the
  *involution* (bijectivity), not just antitonicity — the blueprint says this
  explicitly (`spacetime.tex:650`) and the Lean proof indeed routes through
  `spacelikeComplement_spacelikeComplement_spacelikeComplement`
  (`CausalComplement.lean:377-378` etc.) rather than any one-sided inequality.

## Files referenced

- `/Users/kdavis/Code/physicslib/physicslib4/blueprint/src/sections/sec10/spacetime.tex`
- `/Users/kdavis/Code/physicslib/physicslib4/Physicslib4/Spacetime/Basic.lean`
- `/Users/kdavis/Code/physicslib/physicslib4/Physicslib4/Spacetime/CausalStructure.lean`
- `/Users/kdavis/Code/physicslib/physicslib4/Physicslib4/Spacetime/Curves.lean`
- `/Users/kdavis/Code/physicslib/physicslib4/Physicslib4/Spacetime/Causality.lean`
- `/Users/kdavis/Code/physicslib/physicslib4/Physicslib4/Spacetime/CausalComplement.lean`
- `/Users/kdavis/Code/physicslib/physicslib4/Physicslib4/Spacetime/LorentzianSpacetime.lean`
- `/Users/kdavis/Code/physicslib/physicslib4/Physicslib4/Spacetime/Minkowski.lean`
- `/Users/kdavis/Code/physicslib/physicslib4/Physicslib4/Spacetime/LorentzCauchySchwarz.lean`
- `/Users/kdavis/Code/physicslib/physicslib4/blueprint/lean_decls`
- `/Users/kdavis/Code/physicslib/physicslib4/.git/lean-kit/verify-receipt.json`
- `/Users/kdavis/Code/physicslib/physicslib4/notes/agents/review-2026-09-sec10.1-10.7.md`
  (prior partial review; this memo independently re-verifies and extends its
  `IsGeodesic` finding).
