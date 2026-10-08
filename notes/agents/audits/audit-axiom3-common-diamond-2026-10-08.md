# Audit: Axiom 3 restated through a common containing diamond

Branch `numina/axiom3-common-diamond` vs base `15cdea7` (tip of `numina/aqft-in-lean`).
Scope: the change described in `notes/agents/plan-axiom3-common-diamond-2026-10-08.md`
(D1-D5, approved 2026-10-08). Read-only audit; nothing in the repo was changed.

## Verdict

**Pass.** The Lean restatement of `LocalCommutativity` matches the approved plan and the
blueprint, binder-for-binder parallel to the curved axiom. The protected-definition change
(the one thing CLAUDE.md flags as sensitive) is exactly D1(a) as specified. The two theorem
signatures the task asked me to confirm are unchanged, and the new iff's right side is a
byte-for-byte match of the old definition body. No `sorry`, no non-standard axioms (checked
with the tool), no new `nolint`, no `Restriction:` markers added or needed. One real gap:
**the verification receipt is stale** — it does not cover the current tree, so "lake build"
and "lake lint" have not been confirmed to pass since Stage 3's proofs were written. That
should be closed with a fresh `lean_guard.py verify` before this merges into
`numina/aqft-in-lean`.

## 1. Changes to defs/structures/classes/instances/fields under `Physicslib4/`

`git diff 15cdea7 -- Physicslib4` touches four files, one declaration body, and otherwise only
docstrings:

- **`Physicslib4.AQFT.HaagKastler.LocalCommutativity`** (def, protected) —
  `LocalCommutativity.lean`.
  - Old: `∃ Q : QuasilocalAlgebra U i, ∀ ⦃B₁ B₂⦄ hB₁ hB₂, IsCompletelySpacelike B₁ B₂ → ∀ a b, Commute (Q.ι hB₁ a) (Q.ι hB₂ b)` — commutation in *some* quasilocal algebra.
  - New: `∀ ⦃B₁ B₂ B⦄ hB₁ hB₂ hB, IsCompletelySpacelike B₁ B₂ → (h₁ : B₁ ⊆ B) → (h₂ : B₂ ⊆ B) → ∀ a b, Commute (i.map hB₁ hB h₁ a) (i.map hB₂ hB h₂ b)` — commutation of the isotony images in every common containing basis set `B`.
  - Matches plan D1(a) exactly, and is binder-for-binder parallel to
    `Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity` (verified by reading both
    definitions side by side; only the Minkowski-specific `IsAlexandrovBasisSet` /
    `Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime …` replace the curved `M.IsBasisSet`
    / `M.IsCompletelySpacelike`). Approved.
- **`HaagKastlerNet` structure** (`Net.lean`) — the `localCommutativity` field's *type*
  (`LocalCommutativity U isotony`) is untouched; only its field docstring is reworded to describe
  the new statement. No structure-shape change.
- **`QuasilocalAlgebra` structure** (`QuasilocalAlgebra.lean`) — unchanged except for one comment
  on the `carrier` field explaining why a free universe isn't used, updated to name the new lemma
  it would otherwise have complicated. No field added, removed or retyped.
- No other def/structure/class/instance/abbrev changed under `Physicslib4/`.

Everything here is covered by the approved plan; nothing looks unapproved.

Note on the guard output: `lean_guard.py check --base 15cdea7` also lists `.claude/CLAUDE.md`
and `.claude/lean-policy.json` as "changes [to] a protected file". That is an artefact, not a
real finding: `.claude/` is untracked in this checkout (`git ls-files .claude/` is empty; it
shows only as `?? .claude/` in `git status`), so the guard is comparing "absent at base" against
"present now" for files that were never committed on this branch — nothing in the project's
actual history edited those files. Flagging for awareness, not action.

## 2. Theorems: statement changes, removals, renames

- **`LocalCommutativity.commute_ι`** (blueprint `lmm:local-commutativity-any-quasilocal`):
  signature confirmed **unchanged**:
  ```
  theorem LocalCommutativity.commute_ι {U : LocalNet} {i : Isotony U}
      (h : LocalCommutativity U i) (Q : QuasilocalAlgebra U i)
      ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
      (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
      (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation B₁ B₂)
      (a : U.algebra B₁) (b : U.algebra B₂) :
      Commute (Q.ι hB₁ a) (Q.ι hB₂ b)
  ```
  Only the proof body changed (it now goes through directedness plus one use of the bridge,
  instead of unpacking the old existential witness).
- **`HaagKastlerNet.localCommutativity` field type**: confirmed **unchanged**
  (`LocalCommutativity U isotony`), see §1.
- **New `localCommutativity_iff_exists_commute_ι`** (blueprint
  `lmm:local-commutativity-iff-quasilocal`). Its right-hand side was checked character-for-character
  against the old `LocalCommutativity` body (both quoted above in §1) and is **identical**:
  `∃ Q : QuasilocalAlgebra U i, ∀ ⦃B₁ B₂⦄ hB₁ hB₂, IsCompletelySpacelike … → ∀ a b, Commute (Q.ι hB₁ a) (Q.ι hB₂ b)`.
  So the old axiom is preserved verbatim as the right side of a new iff, exactly as the plan
  specified for D3.
- **`QuasilocalAlgebra.commute_ι_iff_commute_map`**: unchanged (plan said so; confirmed by diff —
  no lines touched).
- **`trivialLocalNet_localCommutativity`** (`Net.lean`): statement unchanged
  (`LocalCommutativity trivialLocalNet trivialLocalNetIsotony`); only the proof was rewritten
  (`mul_comm` directly instead of building `trivialQuasilocalAlgebra`), matching the plan.
- **`commute_ι_of_spacelike`** (`Net.lean`): statement and proof both unchanged; only its
  docstring was reworded (it no longer says Axiom 3 "only asserts this in *some* quasilocal
  algebra").
- No theorem was removed or renamed.

## 3. sorry / non-standard axioms / Restriction markers

- Grep for `sorry`, `admit`, `native_decide`, `debug.skipKernelTC`, `implemented_by` across
  `Physicslib4/` (excluding `scratch_*`) finds no occurrences in code; the only hits are two
  prose mentions of the word "sorry" in doc comments explaining that other structures are
  *sorry-free*.
- `#print axioms` (via `lake env lean` on a throwaway file, tool-verified) on the five relevant
  theorems — `LocalCommutativity.commute_ι`, `localCommutativity_iff_exists_commute_ι`,
  `QuasilocalAlgebra.commute_ι_iff_commute_map`, `trivialLocalNet_localCommutativity`,
  `HaagKastlerNet.einstein_causality` — and on the two lemmas they depend on,
  `exists_quasilocalAlgebra` and `Spacetime.alexandrovBasis_directed`, all report only
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no other axiom.
- No `Restriction:` marker was added by this change, and none is needed: the restated axiom is
  unconditional in Minkowski space (a containing diamond always exists, by
  `alexandrovBasis_directed`), so there is no deliberate narrowing to flag.
- `nolint`: no new uses. The only two `nolint`s in the repository
  (`Spectral/BorelClasses.lean:279`, `Analysis/CStarCompletion.lean:84`) are untouched by this
  branch (confirmed: `git diff 15cdea7` on those two files is empty) and out of scope.

## 4. Blueprint consistency

Checked `blueprint/src/sections/sec10/haag-kastler-axioms.tex` for the five named nodes:

- **`def:local-commutativity`** — `\lean{Physicslib4.AQFT.HaagKastler.LocalCommutativity}`
  exists and the Lean name resolves. Statement: "for any Alexandrov topology basis element `B`
  such that `B1, B2 ⊆ B` the algebras … commute in … `U(B)`" — matches the new Lean definition
  quantifier-for-quantifier (universal in `B`, isotony images, commute in `U(B)`). It states
  "such a `B` always exists … so the condition is never vacuous" and that the axiom "has the same
  shape as its curved counterpart", both of which I independently verified by reading the curved
  definition (§1). It also correctly points to `lmm:local-commutativity-iff-quasilocal` for the
  quasilocal form and no longer `\uses{def:quasilocal-algebra}`. Match.
- **`def:quasilocal-algebra`** — `\lean{Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra}`; now
  carries the `ι`/cocone-condition prose that used to live partly in the Axiom 3 node. Matches
  the unchanged `QuasilocalAlgebra` structure (carrier, `ι`, `ι_injective`, cocone field,
  `dense_range`). Match.
- **`lmm:local-commutativity-any-quasilocal`** — `\lean{LocalCommutativity.commute_ι,
  QuasilocalAlgebra.commute_ι_iff_commute_map}`; premised on "Suppose the net satisfies Axiom 3"
  and concludes commutation of the images in *any* quasilocal algebra `U'`. Matches
  `commute_ι`'s signature exactly (§2).
- **`lmm:local-commutativity-iff-quasilocal`** (new) — `\lean{localCommutativity_iff_exists_commute_ι}`;
  states the iff with the quasilocal-algebra form on the right, "and in that case this holds in
  every quasilocal algebra of the net." Matches the Lean iff and its proof shape (`⇒` via
  `exists_quasilocalAlgebra` + `commute_ι`; `⇐` via the bridge), confirmed by reading both proof
  and blueprint proof text side by side.
- **`thrm:einstein-causality`** — unchanged statement; the surrounding prose (line 790) now reads
  "Local commutativity … is an algebraic statement about the local algebras, which in the
  quasilocal algebra takes the form of `lmm:local-commutativity-any-quasilocal`", replacing the
  old "about the quasilocal algebra" wording — exactly the plan's Stage 1 item 5 edit, and its
  proof's `\uses` now includes `lmm:local-commutativity-any-quasilocal`. Match.

**Remaining "quasilocal algebra" prose, checked for staleness:**
- `blueprint/src/sections/sec9/axiom-3-local-commutativity.tex` (curved chapter): the diff adds
  one sentence — "This is exactly where curved spacetime parts ways with Minkowski spacetime:
  there, any two basis elements lie in a common, larger basis element …, so isotony always
  places their algebras in a common algebra, and Axiom 3 can be stated in it." This is accurate
  and matches plan item D5/Stage-1-item-6; the surrounding sentences about "no basis element `B`
  contains both" in curved spacetime are still true and were correctly left alone.
- `blueprint/src/sections/sec5/quasilocal-algebra.tex`: fully rewritten per plan D4(a), with the
  two approved refinements from the progress log ("nonempty nested regions", the common-upper-bound
  parenthetical) present. The final `\begin{quote}…\end{quote}` now reads "commute in
  `U(B)` for every basis element `B` containing both `B1` and `B2`" — the quasilocal-algebra
  reading is kept as an explicitly-flagged equivalent reading in the following remark, not as the
  primary statement. No stale "commute in the quasilocal algebra" claim remains as the main
  statement.
- `EinsteinCausality.lean` module docstring: now says Axiom 3 "asserts that the local algebras …
  commute in any local algebra containing both; by `commute_ι` they then commute inside the
  quasilocal algebra" — consistent, no stale claim.
- I did not find any remaining prose (grepped Chapter 10 and the touched Lean docstrings) that
  still asserts Axiom 3 itself lives in the quasilocal algebra, as opposed to merely having an
  equivalent form there.

The `def:local-commutativity` node still carries `\leanok` (the plan's Stage 1 item 8 called for
stripping it in the text edit and re-recording it once Lean matched; since Stage 2/3 are already
done and the Lean does match, `\leanok` being present now is the correct final state, not a
leftover).

## 5. Integrity: verify receipt

- `.git/lean-kit/verify-receipt.json` records `lake build` and `lake lint` both passing, but at
  `2026-10-07T10:32:35+00:00` — **before** the base commit `15cdea7` (dated `22:45:12` the same
  day) and well before any commit on this branch.
- I recomputed the guard's digest over the current index and worktree (read-only, via the kit's
  own `digest_of`/`index_entries`/`worktree_entries` helpers) and both differ from the receipt's
  digest. **The receipt does not cover the current tree.** Concretely: `lake build` / `lake lint`
  have not been confirmed to pass since Stage 3's proofs (`commute_ι`, the new iff,
  `trivialLocalNet_localCommutativity`) were written, as far as the recorded receipt shows. The
  plan's progress log claims "build and lint clean" for Stage 3, but no fresh receipt backs that
  claim.
- No `.git/lean-kit/approvals.json` file exists in this checkout, so there is no
  `lean_guard.py approve` record for the protected `LocalCommutativity` change; the only recorded
  approval is the user's sign-off text in the plan file itself ("approved 2026-10-08... D1-D5").
  That is consistent with how the plan describes itself, but it means the guard's own approval
  ledger has nothing to check against.
- Recommendation (not an action I can take): run `python3 ~/.claude/lean-kit/lean_guard.py verify`
  on this tree before merging, so the receipt actually covers what is being merged.

## Summary of classifications

Using the statement-audit vocabulary for the four blueprint/Lean pairs explicitly in scope:

- **Match**: `def:local-commutativity`, `def:quasilocal-algebra`,
  `lmm:local-commutativity-any-quasilocal`, `lmm:local-commutativity-iff-quasilocal`,
  `thrm:einstein-causality` — 5 of 5.
- **Notation only / Lean assumes more / Lean concludes less / different objects / edge cases
  differ**: none found.
- **Can't determine**: none.

Non-matches: none to order.

## What I verified with a tool vs. by reading

- Tool-verified: the `git diff`/`git log` content for every claim in §1-§2 and §4; the guard's
  `check` output; the stale-receipt finding (recomputed the digest with the kit's own code); the
  axiom lists for five theorems plus two dependencies via `lake env lean` + `#print axioms`; the
  `sorry`/`nolint`/`Restriction:` greps.
- Read-only judgement (no mechanical check beyond reading): the mathematical equivalence of the
  blueprint prose to the Lean statements (quantifier order, which variables are universal vs.
  existential); whether the curved and Minkowski definitions are "the same shape" (read both
  side by side); whether the Chapter 5/9 prose changes match the plan's approved wording
  (read the plan's proposed text against the actual diff).
