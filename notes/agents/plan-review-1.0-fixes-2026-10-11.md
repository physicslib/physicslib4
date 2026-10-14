# Staged plan: fixes from the 1.0 pre-release review

Source: `notes/agents/review-1.0/SUMMARY.md` and reports R01–R16. Finding IDs refer to those reports.

Execution rule for every stage: one subagent at a time, each writing progress to disk; one commit per
stage on `numina/aqft-in-lean` (or a stage branch); `lake build` + `lake lint` + `leanblueprint checkdecls`
+ `scripts/check_temporal_wording.py` before each commit.

## Decisions recorded (2026-10-11)

No stage has started; work resumes after the weekly budget reset.

- D1: approved as recommended, option (a): `Type u`.
- D2: option (c). Reword the blueprint so `def:geodesic` is stated for spacetimes only; no Lean change and
  no Restriction line.
- D3: no `**Restriction:**` line. The two descriptions name the same group, so the Lean group is not
  narrower in content. Record the implementation choice as a note instead:
  - Blueprint: a "Formalization note" under Axiom 5 (curved) saying the Lean defines the group as the
    identity component intersected with the future-orientation-preserving isometries; that this equals
    the isometries connected to the identity; and that the Lean doesn't prove the equality because it
    needs a Myers–Steenrod-type rigidity result Mathlib lacks.
  - Lean: an "Implementation note" in the docstring of `toAbstractIdentityComponent` with the same content,
    replacing the bare "matching the blueprint's ..." claim in the module docstring.
  - Plan stage 1 drops the D3 Restriction item and instead carries these two notes.
- D4: approved as recommended, option (a): new Chapter 10 nodes for headline results.
- D5: approved as recommended: `\uses{}` follows the informal proof; GNS option (a) with a
  Formalization note.
- D6: default approved.
- D7: default approved.

## Stage 1 progress (2026-10-13)

- Done, uncommitted: D2 rewording (`spacetime.tex` lead-in and `def:geodesic`, `home_page/sec10-5-spacetime.md`);
  D3 notes (Formalization note under curved Axiom 5; implementation notes in `Concrete.lean` and on
  `orientedIdentityComponent`, whose docstring wrongly said the C⁰ topology "does not give" orientation
  preservation); docstring on `isCompact_weakStateSet`.
- After the user's guard approvals: D1 applied (`IsVacuumState`, `IsGroundStateForFlow`,
  `IsGroundStateForFlow.exists_strongContinuous_unitary` now use `Type u`); D7 applied (`[Nontrivial A]`
  removed from `isCompact_weakStateSet`). Build and lint pass. Stage 1 complete, uncommitted.
- (Earlier) blocked by the lean-kit guard, waiting on user approval: D1 for `IsVacuumState`, `IsGroundStateForFlow`
  and `IsGroundStateForFlow.exists_strongContinuous_unitary` (Minkowski, `VacuumState.lean`, `QuasilocalKMS.lean`);
  D7 removal of `[Nontrivial A]` (`PureStateExists.lean`).
- D1 scope correction: the curved declarations in R13-7 need no change. The curved `LocalNet.algebra`
  lands in `Type` (`HaagKastlerCurved/LocalAlgebras.lean:62`), so `∃ (H : Type)` already matches. The
  Minkowski `LocalNet.algebra` uses `Type*` (`HaagKastler/LocalAlgebras.lean:82`). New protected question
  D8: should the curved net also be universe-polymorphic?

## Stage 2 progress (2026-10-13)

Done, uncommitted; details in `notes/agents/stage2-progress.md`. All items applied. No `set_option` could
be removed (each is needed; the guard also treats removing one as a definition change), so all 11 carry
a comment. One `erw` became `rw`; two stay with comments. Build and lint pass.

## Stage 3 progress (2026-10-13)

Details in `notes/agents/stage3-progress.md`. R15-3 done: the shared estimate is `private lemma
norm_mul_sub_mul_lt` in `OperatorIntegral.lean` (29 lines fewer). R01-3 was not a real duplicate:
`lmm2` already uses `nullSubmodule_isClosed`. R07-1 done after the user's guard approval (blueprint left as is; the blueprint-named wrapper
`Spacetime.reverse_cauchy_schwarz` keeps both hypotheses, the first unused). Before that it waited on
`LorentzCauchySchwarz.lean`; callers are `LorentzCone.lean:73` and `LorentzOrthogonal.lean:57,219-220`;
blueprint node `lmm:reverse-cauchy-schwarz` (`spacetime.tex:67-86`) assumes both vectors timelike.

## Stage 4 progress (2026-10-14)

Done, uncommitted. Formalization notes: GNS existence (Mathlib's `PositiveLinearMap.GNS`), `prpstn:hall-10.3`
(bounded resolvent), `prpstn:integral-norm-bound` (the preliminary 6-sup bound via `lmm:lemma-1`; per D5 a
note rather than a `\uses{}` edge). `\lean{}`: added `isSelfAdjoint_toOperator` and `integral_one`; removed
`exp_generator_unique` from `lmm:exp-generator-unique` (bounded special case; its docstring says so).
R14-1: blueprint statement narrowed to the derivative claim. R03-1: proof `\uses{}` of `prpstn:hall-8.4`,
`thrm:hall-8.10` and `thrm:spectral-theorem-for-bounded-operators` trimmed to the nodes each proof cites
(19→5, 47→6, 75→2). `blueprint_validate` shows only the existing `conv:` label errors.

## Decisions needed first (original options, kept for reference)

Protected (definitions, axiom-structure fields, or blueprint specification):

- **D1. Universe of GNS witnesses** (R10-1, R13-7). About 14 declarations state `∃ (H : Type) ...` although
  `gns_construction` gives `H : Type u`. Two of them are Prop-valued definitions used as hypotheses:
  `HaagKastlerNet.IsVacuumState` and the two `IsGroundStateForFlow`. For a net in `Type u` with `u > 0`,
  a `Type 0` witness need not exist, so these definitions can be unsatisfiable there.
  - (a) `Type u`, matching the net's algebra universe. **Recommended.**
  - (b) A separate universe `Type v`: more general, but the definitions get an extra universe parameter
    that callers must fix.
  - (c) Keep `Type` and add a `**Restriction:**` line.
- **D2. Scope of `IsGeodesic`** (R14-2). The blueprint states `def:geodesic` for a general
  pseudo-Riemannian manifold; Lean states it only for `M : Spacetime`, because `SmoothPath` exists only
  for `Spacetime`.
  - (a) Keep Lean and add a `**Restriction:**` line (waiting on `SmoothPath` for general manifolds),
    plus a sentence in the blueprint. **Recommended.**
  - (b) Generalise `SmoothPath` and `IsGeodesic` to `PseudoRiemannianMetric`. Larger, and touches
    every curve declaration.
  - (c) Reword the blueprint to state it for spacetimes only.
- **D3. Axiom 5 and the oriented identity component** (R11-1). `toAbstractIdentityComponent` uses
  orientation-preserving isometries connected to the identity; the blueprint says "isometries connected
  to the identity". The reason (needs a Myers–Steenrod-type result) appears only on the home page.
  - (a) Add a `**Restriction:**` line in `Concrete.lean` and a remark in the blueprint, keeping the
    blueprint definition as is. **Recommended.**
  - (b) Change the blueprint definition to the oriented component.
- **D4. Blueprint coverage of Lean without nodes** (R07-2, R07-4, R06-1, R10-2, R13-6). This covers the
  orthochronous Lorentz section of `Minkowski.lean`, most of `LorentzCausality.lean` (imported by the
  Axiom 5 and quasilocal-action files), `strongContinuous_of_weak`, the stronger `exists_gns_unitary*`
  variants, and about 10 theorems such as `exists_isLocalObservable`.
  - (a) Add Chapter 10 nodes for the headline results (new blueprint specification), and list the
    remaining helpers in the module docstrings. **Recommended.**
  - (b) Only add names to existing nodes' `\lean{}` tags, with no new nodes.
  - (c) Delete Lean that nothing uses and no node needs.
- **D5. `\uses{}` convention and the GNS proof route** (R01-1, R01-2, R04-1, R03-1).
  `thrm:gns-construction-theorem` cites `lmm1`, `lmm2` and `cauchy_schwarz_inequality`, but the Lean
  proof uses Mathlib's GNS. `prpstn:hall-10.3` cites the direct-sum lemmas, but the Lean proof uses a
  bounded resolvent.
  - Convention: `\uses{}` in a proof lists the informal proof's direct dependencies; a note records a
    different Lean route. **Recommended.** The alternative is to have the tags follow the Lean proof.
  - GNS: (a) keep the blueprint's five-part proof and its edges, and add a "Formalization note" that
    Lean uses Mathlib's GNS; `lmm1`/`lmm2`/`cauchy_schwarz_inequality` stay as stated lemmas.
    **Recommended.** (b) Rewrite the blueprint proof along the Mathlib route and drop the edges.
  - Under the convention, the broad `\uses{}` on the capstone nodes (R03-1) is checked against the
    informal proofs, not the one-line Lean proofs.

Not protected; defaults apply unless you say otherwise:

- **D6. Present-tense check** (R16-1). Add patterns for bare "no longer" and "previously", and for "now"
  only in history-telling phrases ("is now", "are now", "now proved", "now uses"), since bare "now"
  matches far too much. A per-line allow comment covers legitimate uses.
- **D7. Hypotheses to remove instead of record.** Remove `[Nontrivial A]` from `isCompact_weakStateSet`
  (R01-5): for trivial `A` the state set is empty, so it is compact. Drop the unneeded non-emptiness
  hypothesis from the blueprint's Boundedness Theorem (R15-5). Drop the unused timelike-`v` hypothesis
  (R07-1) if no caller needs it.

## Stages

1. **Restrictions and universes** (after D1–D3). Apply D1 to the 14 declarations
   (mechanical: their proofs already use `gns_construction`), with matching blueprint wording if any
   statement names the universe. Add the D2 and D3 restriction lines and blueprint remarks. Do D7's
   `[Nontrivial A]` removal. Check: the declarations that consume `IsVacuumState` and `IsGroundStateForFlow`
   still build.
2. **Small Lean fixes** (no decisions). Remove the leaked comment `OperatorIntegral.lean:963-965` (R15-2).
   Move the misplaced docstring in `Minkowski.lean:592-608` (R13-3). Add docstrings to the
   substantive undocumented theorems (R13-5). Fix the `Basic.lean` claim about `IsCyclicVector` (R01-4)
   and the KMS wording (R10-3). Explain or remove each unexplained `set_option` (R07-3, R08-1, R13-1,
   R13-2, R13-4, R03-2) and `erw` (R04-2), testing removal first.
3. **Code tidying.** Remove the duplicated ~70-line proof (R15-3) by reordering or extracting a lemma.
   Resolve `nullSubmodule_isClosed` versus `lmm2` (R01-3). Remove the unused hypothesis (R07-1).
   Run `fuse:golfer` on the touched proofs only.
4. **`\uses{}` and `\lean{}` tags** (after D5). Add the GNS and `prpstn:hall-10.3` formalization notes.
   Add the missing edge `lmm:lemma-1` (R15-1). Complete the `\lean{}` lists: `isSelfAdjoint_toOperator`
   (R02-1), `integral_one` (R15-4); reassess `exp_generator_unique` (R06-2). Add the other half of
   `mfderiv_apply_tangent_eq_zero`, or narrow the blueprint statement (R14-1). Then `blueprint_validate`.
5. **Blueprint coverage** (after D4). `fuse:blueprint` + `fuse:blueprint-reviewer` draft the new nodes
   for Lorentz/orthochronous, Lorentz covariance of causal relations, the weak-to-strong continuity
   upgrade, and the uncited theorems. Link them with `blueprint_set_declaration_status`. Update the
   affected module docstrings' "Main results" lists.
6. **Prose and home page.** Fix the lemma range in `home_page/sec10-6-haag-kastler.md:90` (R09-1, likely
   renumbered by stage 5 anyway), list `FunctionalCalculus.lean` on the §10.3 page (R05-1), fix the stray
   `*` (R12-1), use `\cref` for chapter references (R12-2), the LaTeX markup (R14-3), the contraction
   (R02-3) and the Boundedness hypothesis (R15-5).
7. **CI and infrastructure.** Apply D6 to `check_temporal_wording.py` and fix whatever it then flags.
   Drop the unused `issues`/`pull-requests` permissions (R16-2). Align checkout versions and pinning
   (R16-3).
8. **Rebuild and verify.** Full build and lint, `checkdecls`, rebuild the blueprint and `lean_decls`,
   regenerate the home-page numbers and links (node numbers shift after stage 5), refresh the verify
   receipt (R03-3), then a short re-audit of the touched nodes only.

Order: stages 2, 3, 6 and 7 need no decisions and can run while D1–D5 are open; 1, 4 and 5 wait on
their decisions; 8 is last.
