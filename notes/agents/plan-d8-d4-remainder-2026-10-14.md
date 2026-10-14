# Plan: D8 (curved-net universe) and the rest of D4

Follows `plan-review-1.0-fixes-2026-10-11.md`, which is complete except for these two items.

## Decision recorded (2026-10-14)

D8: option (b), `Type v`. Stages 1-3 done, uncommitted (details in `notes/agents/d8-progress.md`):
`LocalNet.{u, v}`/`HaagKastlerNet.{u, v}` with algebras in `Type v`; the 11 curved GNS results, the Axiom 4
definition `LocalAlgebra` and the net-level observable lemmas use `Type v`; the trivial net and the
satisfiability theorems fix `v := 0`. Build, lint and axiom checks pass. The blueprint and home page say
nothing about universes, so they need no change.

## Decision needed: D8 (protected)

The curved `LocalNet.algebra` is `Set M.Carrier → Type` (`HaagKastlerCurved/LocalAlgebras.lean:62`). The
Minkowski one is `Set StandardMinkowskiSpacetime.Carrier → Type*` (`HaagKastler/LocalAlgebras.lean:82`). The
module docstring of `HaagKastlerCurved/Spacetime.lean:56-61` records the curved choice as deliberate: it
fixes the universe of the GNS spaces in Axiom 4. The `Carrier` and `Isom` fields of the interface are
already universe-polymorphic.

- (a) Keep `Type`. Mention the difference from the Minkowski net in the docstring of the curved `LocalNet`
  and in a sentence of `def:local-algebras-in-curved-spacetime`. Small, docs only.
- (b) Make it `Type v`, with `LocalNet.{u, v}` and `HaagKastlerNet.{u, v}`. The GNS witnesses in the
  curved files become `Type v`, as D1 did for Minkowski. The Minkowski and curved nets are then parallel,
  as they are for Axiom 3. Mechanical, but it touches the 17 files that use `LocalNet`/`HaagKastlerNet`,
  so every one needs a guard approval.

**Recommendation: (b)**, for the parallel with Minkowski. Choose (a) if the extra universe parameter in
the curved API is unwanted.

### Stages for (b)

1. Guard approvals: `python3 ~/.claude/lean-kit/lean_guard.py approve --file <f> --note D8` for each
   file under `Physicslib4/AQFT/HaagKastlerCurved/` that changes (the subagent lists them first).
2. One prover: change the field, add universe parameters, change `∃ (H : Type)` to `Type v` in the 11
   GNS declarations listed in R13-7, then fix callers. Update the `Spacetime.lean` modelling note. Build,
   lint and axiom check.
3. Blueprint: if `def:local-algebras-in-curved-spacetime` says anything about universes, align it.
   Re-audit the changed signatures. Commit.

## The rest of D4 (no decision needed)

Two items remain: list the minor helpers in the module docstrings, and triage the declarations that
have no blueprint citation.

A fresh survey finds 65 public declarations that appear in no `\lean{}` tag and are not referred to by
name anywhere else. They are spread over about 30 files, with at most 7 per file (curved `Net.lean` 7,
`Minkowski.lean` 6, `Superselection.lean` 5, Minkowski `Net.lean` 5). The count overstates dead code:
`@[simp]` lemmas used only through `simp` have no name occurrence.

1. **Triage (one read-only agent, writes a memo).** Sort each candidate into one of four kinds:
   - (i) used through `simp` or instances: keep;
   - (ii) API or helper: list in the module docstring;
   - (iii) headline result: needs a node or a `\lean{}` entry;
   - (iv) dead and superseded: delete.

   Include `chronologicallyPrecedes_smul_iff` and `isAlexandrovBasisSet_smul`, left over from stage 5a.
2. **Your review of the memo.** Your approval is needed only for kind (iv) deletions (removing a
   declaration is a definition-level change), and for any kind (iii) that would be a new blueprint node.
3. **Apply.** Add the kind (ii) docstring lists, with one subagent per group of files. Add the kind (iii)
   nodes with the blueprint writer, then the reviewer. Make the approved kind (iv) deletions with
   guard approvals.
4. **Verify.** Build, lint, `checkdecls`, and the present-tense check. If nodes were added, renumber the
   home page as in stage 8. Commit.

## Budget

Run one subagent at a time, each with a progress log in `notes/agents/`. D8 needs about three agent
runs; D4 needs three or four, plus a home-page renumbering if nodes are added. Do them as two separate
sessions.
