# Plan: make causal precedence ≺ reflexive (option (a))

## Decisions recorded (2026-10-16)

- The design is approved: `CausallyPrecedes := Relation.ReflTransGen (CausalSegmentPrecedes)`, and
  `NoClosedCausalCurve := ∀ p, ¬ IsCausalTrip p p`.
- `causallyPrecedes_asymm` is restated for `IsCausalTrip` (`isCausalTrip_asymm`).
- No new notation for the strict relation.
- Guard approvals: the user runs them for `Causality.lean`, `LorentzCausality.lean` and
  `CausalComplement.lean`.

## The problem

- **The Lean.** `CausallyPrecedes M t p q` is `IsCausalTrip M t p q` (`Spacetime/Causality.lean:171`). That is
  a chain of one or more causal trip segments (`Relation.TransGen`). A segment is a curve whose smooth
  path has nowhere-vanishing velocity (`SmoothPath.nonvanishing`, `Curves.lean:122`) on a parameter space
  with at least two points (`Path.nontrivial`). So `p ≺ p` holds only if there is a closed causal
  curve. In Minkowski space it is false.
- **The blueprint.** `def:causal-trip` (`spacetime.tex:611`) says "(Note a causal geodesic is possibly
  degenerate.)". This is the Hawking–Ellis / O'Neill convention: $`p \in J^+(p)`, and ≺ is reflexive.
  Tutorial chapter 1 uses that convention as well.
- **The consequence.** `IsSpacelikeRelated t p₁ p₂ := p₂ ∉ J⁺(p₁) ∪ J⁻(p₁)` (`Causality.lean:225`). With
  ≺ irreflexive, every point of Minkowski space is spacelike-related to itself. So the spacelike
  complement $`O'` of a set can meet $`O`.

## Proposed design (protected; needs your approval)

1. **`CausallyPrecedes` becomes reflexive:**
   `CausallyPrecedes M t p q := Relation.ReflTransGen (M.CausalSegmentPrecedes t) p q`.
   - This is equivalent to `p = q ∨ IsCausalTrip M t p q` (Mathlib's
     `Relation.reflTransGen_iff_eq_or_transGen`).
   - `ReflTransGen` gives reflexivity, transitivity and induction from Mathlib.
   - `IsCausalTrip` is kept unchanged, as the non-degenerate relation: a genuine causal curve.
2. **`NoClosedCausalCurve`** is currently `∀ p, ¬ p ≺ p` (`Causality.lean:300`). With a reflexive ≺ that
   would be false in every spacetime, so it must change to `∀ p, ¬ IsCausalTrip M t p p`. This matches
   its name: no closed causal *curve*.
3. **Unchanged:** `Path`, `SmoothPath`, causal trip segments, geodesics, and chronological precedence ≪
   (`IsTrip`, strict).
4. **Effects on the derived notions.** `causalFuture` and `causalPast` contain $`p`; `IsSpacelikeRelated`
   becomes irreflexive; $`O \cap O' = \emptyset`$ holds for every set $`O`. The definitions of
   `IsSpacelikeRelated`, `IsCompletelySpacelike`, `spacelikeComplement`, `causalDiamond`,
   `IsCausallyConvex` and the rest stay as they are; only their meaning changes.

## Affected Lean declarations

A survey found 112 declarations in 14 files that mention these notions. Most only use the relation
abstractly; their statements are unchanged and their proofs either compile as they are or need small
repairs.

**Definitions whose text changes (protected):**
- `CausallyPrecedes` (`Causality.lean:171`);
- `NoClosedCausalCurve` (`:300`).

**Theorems whose statement must change:**
- `causallyPrecedes_asymm`: asymmetry fails, since `p ≺ p`. Replace it by asymmetry for distinct
  points, or move it to `IsCausalTrip`. `causallyPrecedes_antisymm` keeps its statement.
- `chronologicallyPrecedes_irrefl`: the statement stays; the proof goes through `IsCausalTrip`.

**Proofs likely to need repair** (they use `TransGen` induction or the structure of a trip, and now get a
reflexive case):
- `Spacetime/Causality.lean`:
  - `causallyPrecedes_trans`
  - `causallyPrecedes_of_chronologicallyPrecedes`
  - `chronologicalFuture_subset_causalFuture`, `chronologicalPast_subset_causalPast`
  - `causallyPrecedes_asymm`, `causallyPrecedes_antisymm`
  - `causalDiamond_subset_of`, `causalDiamond_causallyConvex`, `causallyPrecedes_of_causalDiamond_nonempty`
  - `chronologicalDiamond_subset_causalDiamond`
  - `causalFutureSet_mono`, `causalPastSet_mono`
- `Spacetime/LorentzCausality.lean`:
  - `causallyPrecedes_smul`, `causallyPrecedes_smul_iff`
  - `isSpacelikeRelated_smul_iff`, `isSpacelikeRelated_congr`
  - `isCompletelySpacelike_image`, `isCompletelySpacelike_smul_iff`, `isCompletelySpacelike_smul`
  - the reflexive case is trivial, since `g • p = g • p`
- `Spacetime/CausalComplement.lean`, 33 declarations. The statements should hold as they are; some proofs
  may simplify. Check each, in particular:
  - `isCompletelySpacelike_singleton_left_iff`
  - the `spacelikeComplement` and `causalClosure` lemmas
  - `isCausallyComplete_*`, `causalComplement_*`
- `Spacetime/LorentzianSpacetime.lean`, the `IsCompletelySpacelike` API (7 declarations): likely
  unaffected.

**Expected to compile unchanged** (they use `IsCompletelySpacelike` only abstractly). Confirm with the
build.
- `AQFT/HaagKastler/`:
  - `LocalCommutativity` and its lemmas
  - `Net.lean` (`commute_ι_of_spacelike*`)
  - `EinsteinCausality.lean`
  - `LocalVonNeumann.lean` (5)
- `AQFT/HaagKastlerCurved/`:
  - `LocalCommutativity`, `Net.lean` (`commute_of_spacelike*`; `trivialSpacetime` uses
    `IsCompletelySpacelike := True`), `EinsteinCausality.lean`, `LocalVonNeumann.lean`
  - `Spacetime.lean` (the abstract interface)
  - `Concrete.lean` (5 declarations, including `toAbstractIdentityComponent`)

**New lemmas worth adding** (they become provable):
- `causallyPrecedes_refl`;
- `isSpacelikeRelated_irrefl`;
- `disjoint_spacelikeComplement` ($`O \cap O' = \emptyset`$);
- `causallyPrecedes_iff_eq_or_isCausalTrip`.

## Affected blueprint nodes (23, all in `blueprint/src/sections/sec10/spacetime.tex`)

**Text changes needed:**
- `def:causal-trip`: "We write $`p \prec q` if $`p = q` or there is a causal trip from $`p` to
  $`q`". Remove the "possibly degenerate" parenthetical, or make it say this.
- `def:no-closed-causal-curve`: state it with causal trips, so that it excludes closed causal curves.
- `thrm:causal-order-refinements`: the asymmetry claim for ≺ changes (see `:649`); the antisymmetry
  claim stays.
- `def:causal-future-and-causal-past`: add that $`p \in J^\pm(p)`.
- `def:spacelike-related`: add that a point is not spacelike-related to itself.
- `def:causal-diamond` and `lmm:causal-diamond-structure`: $`J^+(p) \cap J^-(p) = \{p\}`.
- New nodes, or `\lean{}` entries, for the new lemmas above.

**Check that the text still holds** (statements unchanged):
- `thrm:precedence-transitive`
- `lmm:chronological-implies-causal`
- `thrm:causal-diamond-vs-chronological`
- `def:completely-spacelike`, `lmm:completely-spacelike-symm`
- `lmm:precedence-preserving-spacelike`
- `def:spacelike-complement`, `def:causal-closure`, `lmm:causal-closure-is-closure-operator`
- `def:causally-complete-region`, `thrm:causally-complete-lattice`, `def:causally-convex-region`
- `lmm:lorentzian-causal-lifts`
- `def:lorentz-path`
- `thrm:causal-precedence-lorentz-invariant`
- `crllr:spacelike-lorentz-invariant`

Also grep the blueprint, the home page and the docstrings for "irreflexive", "reflexive" and
"degenerate", and for claims that a point is or isn't spacelike to itself.

## Documentation

- **Tutorial chapter 1** is then correct as written: "or zero" and $`J^+(p) \cap J^-(p) = \{p\}`.
- **Tutorial chapter 2** (uncommitted draft): the planned sentence "the library's ≺ is not reflexive"
  becomes "≺ is reflexive", and any example that depends on it must be checked.
- **Home page:** the §10.5 page, if it describes the relation.
- **`CHANGELOG.md`:** add an entry.

## Stages

1. **Your approval** of the design above (items 1–2). Then guard approvals:
   - `python3 ~/.claude/lean-kit/lean_guard.py approve --file Physicslib4/Spacetime/Causality.lean --note causal-refl`;
   - the same for `LorentzCausality.lean` and `CausalComplement.lean`, in case a statement there needs
     a change.
2. **Lean (one prover):**
   - change the two definitions;
   - repair the proofs in dependency order: `Causality`, then `LorentzCausality`, then
     `CausalComplement`, then the AQFT files;
   - restate `causallyPrecedes_asymm`, and add the new lemmas;
   - full build, lint and axiom check, with a progress log.
3. **Blueprint (writer, then reviewer):** the text changes above, and nodes for the new lemmas.
   `blueprint_validate`, `checkdecls`, then rebuild.
4. **Documentation:** tutorial chapter 2, the home page and the changelog. Renumber the home page if
   nodes were added.
5. **Re-audit** of the changed declarations and nodes, then commit.

## Questions for you

1. `ReflTransGen` (recommended) or `p = q ∨ IsCausalTrip`? They are equivalent; `ReflTransGen` has more
   ready-made API.
2. Should `causallyPrecedes_asymm` become "for $`p \neq q`, $`p \prec q` excludes $`q \prec p`", or be
   stated for `IsCausalTrip` instead?
3. Should the strict relation `IsCausalTrip` get its own notation (for example `≺≺`), or stay a named
   predicate?

## Stage 2 progress (2026-10-16)

Done, uncommitted (details in `causal-refl-progress.md`). Only `Causality.lean`, `LorentzCausality.lean`
and `CausalComplement.lean` changed; nothing downstream needed repair. Added `causallyPrecedes_refl`,
`causallyPrecedes_iff_eq_or_isCausalTrip`, `causallyPrecedes_of_isCausalTrip`, `isCausalTrip_trans`,
`isCausalTrip_of_chronologicallyPrecedes`, `isSpacelikeRelated_irrefl`, `disjoint_spacelikeComplement`
(two versions), `spacelikeComplement_univ`, `inf_causalComplement`, `sup_causalComplement`.
`causallyPrecedes_asymm` is replaced by `isCausalTrip_asymm`, and the blueprint tag in
`thrm:causal-order-refinements` is switched so that `checkdecls` passes. Build, lint and axiom checks
pass. Next: stage 3, the blueprint text.
