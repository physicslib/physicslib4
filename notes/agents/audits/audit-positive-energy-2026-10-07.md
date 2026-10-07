# Audit: unbounded positive-energy condition (`numina/positive-energy` vs b1cf7d9)

Date: 2026-10-07. Base: `b1cf7d9` (tip of `numina/aqft-in-lean`). Branch under audit:
`numina/positive-energy`, working tree at commit `85c1072`. Plan audited against:
`notes/agents/plan-positive-energy-2026-10-07.md` (decisions D1–D5, D2 refinement, both approved
2026-10-07).

## 1. Protected-definition changes (`git diff b1cf7d9 -- Physicslib4`)

`python3 ~/.claude/lean-kit/lean_guard.py check --base b1cf7d9` reports two `Physicslib4/`
protected changes (plus guard-context and blueprint-prose findings, below).

**1a. `Physicslib4.AQFT.IsPositiveEnergy`, `Physicslib4/AQFT/PositiveEnergy.lean`.** Changed from
a `def` to a `structure`:

- Old: `def IsPositiveEnergy (V : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop := ∃ P : H →L[ℂ] H, P.IsPositive ∧ ∀ t x, V t x = exp((t·I) • P) x` — bounded generator only.
- New: `structure IsPositiveEnergy (V : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop where isOneParameterUnitaryGroup : IsOneParameterUnitaryGroup V; isStronglyContinuous : IsStronglyContinuous V; isPositive_generator : Spectral.Unbounded.IsPositive (generator V)`.

This is **exactly D1(a)**, the recommended intrinsic shape: one-parameter unitary group ∧
strongly continuous ∧ positive generator, naming `generator V` rather than quantifying over a
bounded witness. **Matches the approved design.** The outer type `V : ℝ → (H ≃ₗᵢ[ℂ] H)` is
unchanged, so this is a strict generalization (every old instance, with `P` bounded, now gives an
instance of the new structure via `isPositiveEnergy_exp`; the converse needs Stone and does not
hold the other way, which is the intended effect of lifting the restriction).

**1b. `Physicslib4.Spectral.Unbounded.IsPositive`, `Physicslib4/Spectral/Unbounded/Basic.lean`
(new def).** `def IsPositive (A : H →ₗ.[ℂ] H) : Prop := IsSymmetric A ∧ ∀ ψ : A.domain, 0 ≤ (⟪(ψ:H), A ψ⟫_ℂ).re`.
This is **exactly D2 as refined** (quadratic-form positivity, with the symmetric conjunct
mirroring `ContinuousLinearMap.IsPositive`). The guard flags new `def`s as reserved for the user
by policy; this one is a verbatim implementation of the text the user already approved in the
plan ("D2 refinement accepted 2026-10-07: `Unbounded.IsPositive A := IsSymmetric A ∧ ∀ ψ : A.domain, 0 ≤ re ⟪ψ, A ψ⟫`"). **No deviation found**, but per the guard's own policy this still needs the
user's sign-off on the committed text, not just the plan's prose — flagging it here is that
sign-off request.

**1c. Guard also flags a `variable`/`open`-style change in the same file**: `open Spectral.Stone`
was added before the kept declarations (`exp_generator_unique`, etc.). I checked each kept
theorem's binders and statement text against `b1cf7d9`; none changed (see §2). The new `open`
does not introduce a name clash with anything the kept statements reference. Benign.

**No other `def`/`structure`/`class`/`abbrev`/`instance` or structure field changed** in
`Physicslib4/`. `Spectral/Stone/Basic.lean` and the new `Spectral/Stone/Bounded.lean` only add
`theorem`s (allowed by policy); `VacuumState.lean`, `QuasilocalKMS.lean`, `StabilizerKMS.lean`,
`CovariantState.lean` change only docstrings/module comments — the `def`s
`IsVacuumState`, `IsVacuumStateConcrete`, and both `IsGroundStateForFlow` are byte-for-byte
unchanged in body (see §2).

**Unrelated guard findings, not from this branch's work:** the guard also lists `.claude/CLAUDE.md`
and `.claude/lean-policy.json` as "changed protected files." These are artifacts of the sandbox:
`.claude/` is entirely untracked in this repository's git history (`git show b1cf7d9:.claude/CLAUDE.md`
and `git show HEAD:.claude/lean-policy.json` both fail with "exists on disk, but not in <rev>"),
so the guard's working-tree comparison treats the whole directory as new/changed relative to any
base commit. This is not an edit made on `numina/positive-energy`; it is the environment's copy of
agent configuration, which was never committed. Flagging for completeness, not as a finding against
the branch.

## 2. Statement changes, removals, renames

**Changed statements** (beyond the `IsPositiveEnergy` structure itself, §1a), all in
`PositiveEnergy.lean`:

- `isPositiveEnergy_const_refl` — same statement (`IsPositiveEnergy (fun _ => refl)`); proof
  changed to match the new structure. Unchanged `omit [CompleteSpace H]` added (generalization,
  not a restriction — `CompleteSpace H` was never needed by this particular theorem).
- `IsPositiveEnergy.conj` — same statement (`IsPositiveEnergy V → IsPositiveEnergy (conjugate by W)`); proof rewritten against the new structure fields and the new `Unbounded.IsPositive.of_conj`/`mem_generator_conj_domain_iff`/`generator_conj_apply` lemmas.
- `IsPositiveEnergy.strongContinuous` — same statement and conclusion (`Continuous (fun t => V t x)`); now a one-line projection of the `isStronglyContinuous` field rather than a computation from the bounded exponential.
- `exp_generator_unique` — **kept, statement unchanged** (two bounded `P`,`Q` with the same
  `exp(itP) = exp(itQ)` for all `t` are equal); this is still a true, self-contained statement
  about `exp`, per D3.

**New theorems** (not renames — genuinely new content, all per the plan's stage 3/4):
`generator_eq_of_eq_expUnitary` (the D4 uniqueness lemma: `V t = e^{itB}`, `B` self-adjoint ⟹
`generator V = B`), `isPositiveEnergy_exp` (bounded case, D3's promised backward-compatibility
lemma), `isPositiveEnergy_iff_exists_exp` (the existential/exponential form, proved as an
equivalence via Stone, per the D1(a)/D1(b) reconciliation in the plan). In
`Spectral/Stone/Basic.lean`: `isOneParameterUnitaryGroup_refl`, `isStronglyContinuous_refl`,
`generator_refl`, `IsOneParameterUnitaryGroup.conj`, `IsStronglyContinuous.conj`,
`mem_generator_conj_domain_iff`, `generator_conj_apply` (plus a private helper
`tendsto_generatorQuotient_conj_iff`). New file `Spectral/Stone/Bounded.lean`:
`hasDerivAt_exp_smul_I`, `exists_isOneParameterUnitaryGroup_exp`, `isStronglyContinuous_of_eq_exp`,
`generator_eq_of_eq_exp`. In `Spectral/Unbounded/Basic.lean`: `isPositive_toPMap_iff`,
`IsPositive.of_conj`.

**No theorem was removed or renamed** in `Physicslib4/` on this branch. (The blueprint label
`thrm:vacuum-no-stone` was renamed to `thrm:vacuum-invariance-consequences` in commit `79f642a`;
that is a blueprint-label rename, not a Lean rename — the underlying Lean theorems
`IsVacuumState.invariant` and `IsVacuumState.exists_gns_irreducible_covariant` are unaffected.)

**Confirmed unchanged statements**, by diffing body text against `b1cf7d9`:

- `HaagKastlerNet.IsVacuumState` (`VacuumState.lean`) — identical `def` body (invariance ∧
  ∀ future-timelike-translation subgroup, `IsPositiveEnergy (fun t => U (γ t))`). Only the
  docstring changed (dropped "scaffold"/"Stone-gated" wording and the `**Restriction:**` line).
- `HaagKastlerNet.IsVacuumStateConcrete` — identical (`IsVacuumState IsFutureTimelikeTranslation ω`); docstring-only change, `**Restriction:**` line dropped.
- `HaagKastlerNet.IsGroundStateForFlow` in `QuasilocalKMS.lean` (Minkowski/covariance-flow form)
  — identical body; docstring-only change, `**Restriction:**` line dropped.
- `HaagKastlerNet.IsGroundStateForFlow` in `StabilizerKMS.lean` (curved/Killing-flow form) —
  identical body; docstring-only change, `**Restriction:**` line dropped.

Since `IsPositiveEnergy` itself became strictly more general (not narrower), every statement that
takes it as a hypothesis or field became correspondingly more general (weaker hypothesis to
discharge, same conclusion) rather than changed in shape — consistent with the plan's stated risk
("the new definition is strictly weaker than the old bounded one... today no consumer theorem
silently assumed a bounded generator").

## 3. Axioms, `sorry`, restrictions

- `#print axioms` (via `lake env lean` on a temp file, against the current `.lake` build — the
  `.olean` for `PositiveEnergy.lean` is newer than its source, so the build is current):
  - `Physicslib4.AQFT.isPositiveEnergy_iff_exists_exp`: `[propext, Classical.choice, Quot.sound]`
  - `Physicslib4.AQFT.IsPositiveEnergy.conj`: `[propext, Classical.choice, Quot.sound]`
  - `Physicslib4.AQFT.isPositiveEnergy_exp`: `[propext, Classical.choice, Quot.sound]`
  - `Physicslib4.Spectral.Stone.stone`: `[propext, Classical.choice, Quot.sound]`

  No axiom beyond the three standard ones.
- `grep -rn "sorry\|admit\b\|native_decide\|debug.skipKernelTC\|implemented_by" Physicslib4/`:
  no hits that are actual tactics/attributes — the only matches are two prose uses of the word
  "sorry" inside comments in `Spacetime/Basic.lean` and `Spacetime/Curves.lean` (pre-existing,
  unrelated to this branch, describing that a structure is *free of* `sorry`). **No `sorry` in
  the project.**
- `**Restriction:**` lines: **none remain anywhere in `Physicslib4/`.** All four
  (`PositiveEnergy.lean`'s old `IsPositiveEnergy`, `VacuumState.lean`'s `IsVacuumState` and
  `IsVacuumStateConcrete`, `QuasilocalKMS.lean`'s and `StabilizerKMS.lean`'s
  `IsGroundStateForFlow`) were removed in stage 5 (commit `85c1072`), consistent with lifting the
  restriction. One process note, already flagged in the plan's own log: CLAUDE.md's worked
  example of the marker convention ("the positive-energy docstring in
  `Physicslib4/AQFT/HaagKastler/VacuumState.lean` (bounded generators until Stone's theorem is
  available)") no longer exists as written — CLAUDE.md itself is a protected file and wasn't
  touched, so this is a now-stale example the user may want to update, not a bug in the branch.
- No new unrecorded restriction found: D5 (scope of the vacuum spectrum condition — per-direction
  positive energy, not the joint-spectrum form) is documented in `def:vacuum-state`'s new remark
  paragraph as a textbook-equivalent simplification, not silently dropped; stage 4b (the
  spectral-support characterization of `Unbounded.IsPositive`) was deferred by the plan and is
  absent from the Lean and the blueprint alike (no dangling reference to it), so it is not an
  unrecorded gap either.
- `nolint`: two pre-existing uses, both predating this branch and untouched by it —
  `Physicslib4/Analysis/CStarCompletion.lean:84` and `Physicslib4/Spectral/BorelClasses.lean:279`,
  both `@[nolint unusedArguments]`. Out of scope for this audit (no diff touches either file).
- Verify receipt: `.git/lean-kit/verify-receipt.json` records `lake build` and `lake lint` both
  exit 0, but at `2026-09-29T11:11:06Z` — **before** this branch's commits (2026-10-07). The
  receipt does not reflect the current sources; a fresh `lake build`/`lake lint` has not been
  recorded since. (The `.lake` build artifacts on disk are newer than the sources and the
  `#print axioms` queries above resolved cleanly against them, so the tree appears to build, but
  this has not been captured in a verify receipt.)
- Approvals: `.git/lean-kit/approvals.json` does not exist (no approvals recorded through
  `lean_guard.py approve`). The user's approval for D1–D5 and the D2 refinement is recorded only
  in the plan file's prose ("Status: approved 2026-10-07 ... D2 refinement accepted 2026-10-07").
  That is a real approval from the user in conversation, but it is not in the guard's approvals
  ledger, so `lean_guard.py check` continues to flag the two `def` changes on every run. This
  report is the review the guard is asking for; it does not and cannot itself grant the approval.

## 4. Blueprint consistency (sec10 nodes changed since `b1cf7d9`)

Files changed: `haag-kastler-axioms.tex`, `stones-theorem.tex`, `unbounded-spectral-theorems.tex`,
`haag-kastler-axioms-in-curved-spacetime.tex`. Every `\lean{...}` name introduced or kept in these
diffs was checked against `blueprint/lean_decls` (a declaration-name cache dated today) and, for
the positive-energy nodes, against the Lean source directly:

- `def:positive-energy` (`Physicslib4.AQFT.IsPositiveEnergy`) — **match**. Blueprint: "a family
  $V(t)$ ... has positive energy when $V$ is a strongly continuous one-parameter unitary group
  ... whose infinitesimal generator $A$ ... is a positive operator ... By Stone's Theorem the
  generator $A$ is then ... self-adjoint, and $V(t)=e^{itA}$ ..." — this is exactly the three
  structure fields plus the Stone-theorem consequence stated as a remark (proved separately as
  `thrm:positive-energy-iff-exp` / `isPositiveEnergy_iff_exists_exp`). Title and prose no longer
  say "bounded-generator scaffold"; good.
- `def:positive-unbounded-operator` (`Physicslib4.Spectral.Unbounded.IsPositive`) — **match**.
  Blueprint: "symmetric ... and $\mathrm{Re}\langle\psi,A\psi\rangle \ge 0$ for all
  $\psi\in\mathrm{Dom}(A)$," explicitly density-free — matches the Lean `IsSymmetric A ∧ ∀ ψ : A.domain, 0 ≤ re ⟪ψ, A ψ⟫` exactly, including the density-free framing.
- `lmm:positive-conj` (`Spectral.Unbounded.IsPositive.of_conj`) — **match**. Blueprint states
  domain-and-formula form ("$WAW^{-1}$ with domain $W\,\mathrm{Dom}(A)$ is positive"); Lean states
  it via the `hdom`/`happ` characterization rather than building `WAW⁻¹` as a `LinearPMap`
  directly — a deliberate, reviewer-recommended proof-engineering choice (stage-2 log), and the
  blueprint proof text (lines 1940-1948) walks through exactly that domain/formula argument, so
  this is match, not merely notation-only.
- `thrm:positive-energy-iff-exp` (`isPositiveEnergy_iff_exists_exp`) — **match**. Blueprint: "$V$
  has positive energy iff there is a positive self-adjoint operator $A$ with $V(t)=e^{itA}$ for
  all $t$" — matches `IsPositiveEnergy V ↔ ∃ A hA, Unbounded.IsPositive A ∧ ∀ t, V t = expUnitary hA t` exactly (`expUnitary hA t` is the Lean realization of $e^{itA}$ for self-adjoint `A`).
- `lmm:generator-conj` (`Stone.mem_generator_conj_domain_iff`, `Stone.generator_conj_apply`) —
  **match**. Blueprint: "$\mathrm{Dom}(B)=W\,\mathrm{Dom}(A)$ and $B=WAW^{-1}$," stated as the
  iff-membership + pointwise-value pair — matches the two Lean lemmas' signatures exactly (same
  split, for the same domain-care reason given in the plan's risk section).
- `lmm:generator-exp-bounded` (`Stone.generator_eq_of_eq_exp`) — **match**. Blueprint: "the
  one-parameter unitary group $V(t)=\exp(itP)$ ... is strongly continuous, and its infinitesimal
  generator is $P$, with domain $\mathbf{H}$" — matches `generator V = (P : H →ₗ[ℂ] H).toPMap ⊤`
  (`⊤` domain, i.e. all of `H`) plus `isStronglyContinuous_of_eq_exp`, the companion lemma stated
  immediately above it with the same hypothesis pattern.

All `\lean{}` names cited in the diffs of these four files were verified present in
`blueprint/lean_decls` (18 names checked, all present) and, for the five spot-checked nodes above,
read directly against the Lean declarations.

**One unresolved loose end, already flagged by the plan's own stage-2 log and left for the user's
call**: `thrm:positive-energy-api` (kept, same label, rewritten body) carries
`\lean{Physicslib4.AQFT.isPositiveEnergy_const_refl, Physicslib4.AQFT.exp_generator_unique, Physicslib4.AQFT.IsPositiveEnergy.conj, Physicslib4.AQFT.IsPositiveEnergy.strongContinuous}`
and `\leanok`, but its body now states six parts (i)-(vi), and its own `\uses` line correctly
points the *proof* at the newer, finer-grained lemmas
(`lmm:positive-energy-const, lmm:exp-generator-unique, lmm:positive-conj, lmm:positive-energy-conj, lmm:positive-energy-strong-continuous, lmm:positive-energy-exp-bounded, thrm:positive-energy-iff-exp`).
Concretely:
- part (ii) ("if $B$ is self-adjoint and $V(t)=e^{itB}$ ... then $B$ is the generator") is proved
  by `generator_eq_of_eq_expUnitary`, not by the `\lean`-listed `exp_generator_unique` (which is
  the narrower bounded-$P,Q$ statement, D3's keeper);
- parts (v) (`isPositiveEnergy_exp`) and (vi) (`isPositiveEnergy_iff_exists_exp`) are not in the
  `\lean` list at all.

This does not fail `leanblueprint checkdecls` (every name in the stale list still exists as a
declaration), but the tag no longer documents what the theorem's six parts actually cite, for a
reader following the `\lean` link rather than the `\uses` graph. The plan's own stage-2 log already
recorded this as deferred ("its `\lean` line still names the old declarations ... reviewer notes
for stage 3: `exp_generator_unique` must be restated (or a new name used) for the D4 form"),
and it does not appear to have been revisited in stages 3-5. Worth a decision: either update the
`\lean` line to the six underlying declarations, or drop it from the summary theorem now that each
part has its own fully-tagged lemma node.

- `def:ground-state-for-flow-in-curved-spacetime` and the Minkowski `def:vacuum-state`/
  `thrm:vacuum-invariance-consequences` — prose-only changes (dropped "Stone-free"/"Stone-gated"
  wording, added `lmm:positive-energy-strong-continuous` to the curved node's `\uses`, removed a
  stale `\leanfile{}` tag from the curved node); `\lean{}` targets unchanged and still correct,
  since the underlying `def`s/`theorem`s did not change (§2).

## Verdict

No unapproved *definition* changes: the one changed `def` (`IsPositiveEnergy`, now a `structure`)
and the one new `def` (`Spectral.Unbounded.IsPositive`) both implement, verbatim, the forms the
user approved in the plan (D1(a) and D2-refined respectively). The guard's flags on these two are
the expected "this touches a protected surface, get it reviewed" signal, not evidence of scope
creep — I checked both against the plan text word-for-word and found no deviation.

No statement regressions: `IsVacuumState`, `IsVacuumStateConcrete`, and both
`IsGroundStateForFlow` definitions are byte-identical to `b1cf7d9`; no theorem was removed, and
the only theorem whose *statement* changed is the `IsPositiveEnergy` structure itself, which is a
strict generalization, not a narrowing. Axioms are clean (only `propext`/`Classical.choice`/
`Quot.sound`), there is no `sorry`, and all four `**Restriction:**` lines were removed with the
restriction actually lifted (not just the marker deleted) — the new structure genuinely drops the
bounded-generator requirement. All five spot-checked blueprint nodes match the Lean exactly.

Things for the user to decide, none blocking:
1. Sign off on the two protected-definition changes (§1a, §1b) — both match the approved plan; no
   change recommended, just the formal "I looked, it's as specified" this report provides.
2. `thrm:positive-energy-api`'s stale `\lean` tag (§4) — cosmetic/documentation-only, flagged by
   the plan's own authors and not yet fixed; decide whether to update it to the six underlying
   declarations or retire it now that per-part lemma nodes exist.
3. The verify receipt is stale relative to this branch (§3) — rerun `lake build && lake lint`
   (or `lean_guard.py verify`) to get a current receipt before merging, even though the build
   artifacts and `#print axioms` queries here suggest it currently builds clean.
4. CLAUDE.md's worked example of a `**Restriction:**` docstring (the old `IsPositiveEnergy` one)
   no longer exists; CLAUDE.md is protected and wasn't touched by this branch, so this is just a
   note that the example will need a replacement next time CLAUDE.md is edited.

## What was tool-verified vs. read-judged

- Tool-verified: the guard's list of protected changes (`lean_guard.py check --base b1cf7d9`);
  axiom dependencies for the four named theorems (`lake env lean` + `#print axioms`, against the
  current, source-newer-than-build-confirmed `.lake` build); presence of every cited `\lean{}`
  name in `blueprint/lean_decls`; absence of `sorry`/`admit`/`native_decide`/
  `debug.skipKernelTC`/`implemented_by` and of `**Restriction:**` lines (`grep`); `nolint` sites
  and that they predate this branch (`git diff --stat`); the verify receipt's timestamp vs. the
  branch's commit timestamps; the absence of an approvals ledger.
- Read-judged: every statement-vs-blueprint comparison in §4 (translating Lean signatures to
  prose and comparing against the `.tex`); the classification of each docstring-only change in
  §2 as not touching the `def` body; the "no name clash from the new `open`" claim in §1c (checked
  by reading the kept statements' full text, not by re-elaborating them in isolation).
