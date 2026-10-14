# Audit: review-1.0 fix plan, stages 1-7 (40a55f6..working tree)

Scope: `git diff 40a55f6 -- Physicslib4 blueprint/src` plus uncommitted `home_page/`.
Commits baf635a..309b89d (stages 1-7 of `notes/agents/plan-review-1.0-fixes-2026-10-11.md`).
`scratch_*` ignored.

## 1. Protected changes

`python3 ~/.claude/lean-kit/lean_guard.py check --base 40a55f6` reports 12 protected changes:
9 blueprint-text edits (all stage-4/5/6 prose: `gns-construction-details.tex`,
`haag-kastler-axioms-in-curved-spacetime.tex`, `haag-kastler-axioms.tex`, `spacetime.tex`,
`spectral-theorems.tex`, `unbounded-spectral-theorems.tex`, `isotony.tex`,
`quasilocal-algebra.tex`) plus `.github/workflows/{blueprint,lean_action_ci}.yml`
(stage 7, R16-2/R16-3) and `.claude/{CLAUDE.md,lean-policy.json}` (new protected files on
this branch, unmodified in this diff scope). None unexpected.

No Lean declaration appears in this list because all four Lean signature changes the plan
calls out are covered by recorded approvals in `.git/lean-kit/approvals.json`:
`VacuumState.lean` (D1), `QuasilocalKMS.lean` (D1), `PureStateExists.lean` (D7),
`LorentzCauchySchwarz.lean` (D7). I read the diffs directly to confirm each matches its
decision:

- D1: `HaagKastlerNet.IsVacuumState (N : HaagKastlerNet)` -> `(N : HaagKastlerNet.{u})`,
  `∃ (K : Type) ...` -> `∃ (K : Type u) ...` (`VacuumState.lean:122-128`). Same pattern for
  `IsGroundStateForFlow` and `IsGroundStateForFlow.exists_strongContinuous_unitary`, both now
  take `N : HaagKastlerNet.{u}` explicitly and use `Type u` (`QuasilocalKMS.lean:96-131`).
  Matches "D1 universes" exactly.
- D7 (`isCompact_weakStateSet`): `[Nontrivial A]` hypothesis dropped; proof adds a
  `subsingleton_or_nontrivial A` case split, trivial subcase shown empty hence compact
  (`PureStateExists.lean:83-95`). Matches.
- D7 (`reverse_cauchy_schwarz_of_lorentzianAt`): `(_hv : B v v < 0)` hypothesis removed;
  statement now holds for arbitrary `v` given only `w` timelike (`LorentzCauchySchwarz.lean:60`).
  The blueprint-facing wrapper `Spacetime.reverse_cauchy_schwarz` keeps both hypotheses
  (`hv` renamed `_hv`, now unused) to match `lmm:reverse-cauchy-schwarz`'s symmetric
  statement, as the plan records. Matches.

No other changed Lean signature found outside these four files when diffing the full
`Physicslib4/` tree against `40a55f6`. **Pass.**

## 2. sorry / admit / native_decide / axioms / set_option maxHeartbeats

`git diff 40a55f6 -- Physicslib4` grepped (case-insensitive) for `sorry`, `admit`,
`native_decide`, `axiom `, `set_option maxHeartbeats`: no additions, no removals. Consistent
with stage 2's note that all 11 `set_option`s were kept (none removable) and stage 3's `erw`
removal being unrelated to heartbeats. **Pass.**

## 3. Changed docstrings / new comments

Spot-checked the added docstrings and notes (`Net.lean:341-342,347-348` two new one-line
theorem docstrings; `Concrete.lean:38-68` module docstring + new "Implementation note" on
`toAbstractIdentityComponent`; the stage-4/5 blueprint "Formalization note" / prose additions
in `haag-kastler-axioms-in-curved-spacetime.tex`, `haag-kastler-axioms.tex`,
`gns-construction-details.tex`, `unbounded-spectral-theorems.tex`). All present tense, no
"no longer" / "previously" / "now proved" style narration (confirmed also by the grep for
those patterns over all `+` lines in the Lean diff: no hits). Content checks:
- `Concrete.lean`'s rewritten module-docstring line still asserts `orientedIdentityComponent`
  "is the blueprint's group of 'isometries connected to the identity'" in the same breath as
  pointing to the implementation note; the note itself (and the mirrored blueprint
  Formalization note) correctly state the equality is *not* proved, only asserted by
  definition, pending a Myers-Steenrod-type rigidity theorem. Matches D3's content; the
  surrounding sentence is slightly less hedged than the note it points to, but not inaccurate
  given D3 explicitly decided the two descriptions "name the same group" and chose a note
  over a Restriction line. No independent Restriction marker was added for D2 or D3, matching
  the recorded decisions (both ended up "no Lean change / no Restriction line"). **Pass**,
  one minor wording observation above, not a finding.

## 4. Blueprint `\lean{}` tags and statement spot-checks

Collected every name inside an added `\lean{...}` tag in `git diff 40a55f6 -- blueprint/src`
(55 names, stage 4/5 additions). All 55 resolve in `blueprint/lean_decls`. The one name that
disappears from a `\lean{}` tag (`Physicslib4.AQFT.exp_generator_unique`) is on a deletion
line only (R06-2, stage 4), not a dangling reference.

Spot-checked declarations exist with matching signatures:
- `IsLorentz`, `IsProper`, `IsOrthochronous` (`Minkowski.lean:206-216`) against
  `def:lorentz-transformation` (`spacetime.tex`): exact match (Minkowski-form preservation,
  det = 1, positive time component of `L e_0`).
- `isOrthochronous_pos_time_of_timelike`, `isLorentz_refl`/`_trans`/... exist and are used
  under the matching new nodes `lmm:orthochronous-preserves-future-timelike`,
  `lmm:lorentz-closure`.
- `nonempty_haagKastlerNet_identityComponent`, `isometricCovariance_trivial_identityComponent`,
  `identityComponent_faithfulSMul` (`IdentityComponent.lean:33-55`) exist and their types
  line up with the new theorem `thrm:haag-kastler-net-in-curved-spacetime-nonempty`'s prose
  (trivial net over the concrete oriented-identity-component spacetime satisfies isometric
  covariance and is nonempty; faithfulness stated for the full identity component, with the
  blueprint text noting faithfulness passes to the Axiom-5 subgroup rather than Lean proving
  a second faithfulness instance directly for it).
- `commute_of_spacelike_mono_geometric` exists in `HaagKastlerCurved/` and backs
  `lmm:local-commutativity-mono-in-curved-spacetime`.

No mismatches found among the 13 new nodes' spot-checked statements. **Pass** (statement
match verified by reading Lean source for ~6 of 13 new nodes plus the GNS/Formalization-note
additions by inspection; the remaining new nodes were only checked for `\lean{}` name
resolution, per the task's "focus on obvious mismatches" instruction given they were already
reviewed).

## 5. Home page vs `blueprint/web`

`blueprint/web/*.html` timestamp (07:56) is after the last commit (07:49), consistent with
stage-8-in-progress regeneration (`notes/agents/stage8-progress.md`, uncommitted). Checked 5
entries from `home_page/sec10-5-spacetime.md` and `home_page/sec10-7-curved.md` against
`blueprint/web/chptr-haag-kastler-axioms-blueprint.html`:

| Entry | MD number/title | HTML `id` / label / title | Match |
|---|---|---|---|
| Definition 336 | Lorentz, Proper and Orthochronous Transformations | `def:lorentz-transformation`, 336, same title | yes |
| Lemma 337 | Orthochronous Lorentz Transformations Preserve the Future Cone | `lmm:orthochronous-preserves-future-timelike`, 337, same | yes |
| Lemma 338 | Closure of the Lorentz Conditions | `lmm:lorentz-closure`, 338, same | yes |
| Theorem 645 | The Curved Haag-Kastler Axioms are Jointly Satisfiable | `thrm:haag-kastler-net-in-curved-spacetime-nonempty`, 645, same | yes |
| Lemma 647 | Local Commutativity for Subregions (Concrete Spacetime) | `lmm:local-commutativity-mono-in-curved-spacetime`, 647, same | yes |

All 5 match (number, title, anchor). **Pass.**

## Summary

All five checks pass. No unapproved protected Lean signature changes, no sorry/admit/
native_decide/new-axiom/set_option additions, docstrings read present-tense and accurate
(one minor non-finding wording note on `Concrete.lean`'s module docstring), all 55 new
`\lean{}` names resolve and spot-checked statements match, and the 5 sampled home-page
entries agree with the freshly rebuilt `blueprint/web` HTML.

Verified by tool: `lean_guard.py check`, `grep`/`git diff` greps for sorry/admit/axioms/
set_option, `blueprint/lean_decls` membership check for all 55 added `\lean{}` names.
Judged by reading: docstring wording/accuracy, statement-vs-Lean matches for the new nodes,
home-page entry correctness.
