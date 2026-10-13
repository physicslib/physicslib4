# Stage 2 progress (small Lean fixes, 2026-10-13)

Working through `notes/agents/plan-review-1.0-fixes-2026-10-11.md` stage 2 items.

## 1. R15-2 — leaked process comment (OperatorIntegral.lean:963-965)
Replaced "proved by another prover in the real file" with "proved above in this file".
Comment-only change; no proof/statement touched, so no diagnostics risk. Will be covered
by the final `lake build`.

## 2. R13-3 — misplaced docstring (Minkowski.lean:592-608)
Moved the three paragraphs describing `MinkowskiSpacetime` (carrier, convention, retopologisation)
into `MinkowskiSpacetime`'s own docstring at line ~1729 (merged, no duplication). Left
`standardMinkowskiTimeOrientation`'s docstring as a short standalone description (the `∂_0`
vector field and why it's needed, pointing to `MinkowskiSpacetime` for the Alexandrov-topology
context). Verified with `lake env lean Physicslib4/Spacetime/Minkowski.lean`: no output (no
errors/warnings).

## 3. R13-5 — docstrings on substantive undocumented theorems
Added one-line docstrings to: `isCausallyComplete_iff_isClosed`, `causalComplement_antitone`
(CausalComplement.lean); `isClosed_weakStateSet` (GNS/PureStateExists.lean;
`isCompact_weakStateSet` already had one, skipped as instructed);
`extendHom_continuous`, `nonempty_trivialQuasilocalLift` (QuasilocalIntertwiner.lean);
`trivialLocalNet_localCommutativity`, `trivialLocalNet_lorentzCovariance` (HaagKastler/Net.lean).
Verified each touched file with `lake env lean <file>`: no output (no errors/warnings) for all four
files.

## 4. R01-4 — GNS/Basic.lean docstring correctness
Corrected the "Notes" paragraph: it had claimed `IsCyclicVector` keeps `A` "general enough" for a
plain algebra per `def:cyclic-vector`, but `A` is fixed to `[CStarAlgebra A]` via the file's
ambient `variable`. Reworded to say Lean requires a unital C*-algebra (matching every call site)
and that the generality is kept on the `H` side instead. Docstring-only change.
Verified with `lake env lean Physicslib4/GNS/Basic.lean`: no output.

## 5. R10-3 — KMS.lean module docstring wording
Replaced "unconditionally for `β > 0`" (ambiguous: reads as "with no hypotheses") with an explicit
statement that `IsKMSState.invariant` needs a `StripLiouville β` hypothesis and that
`invariant_of_pos` discharges it automatically whenever `β > 0`. Confirmed against the actual
signatures (`IsKMSState.invariant` takes `hSL : StripLiouville β`; `invariant_of_pos` takes
`hβ : 0 < β`). Verified with `lake env lean Physicslib4/AQFT/KMS.lean`: no output.

## 6. Unexplained `set_option` uses
All six `respectTransparency` declarations (`StandardMinkowskiSpacetime`,
`standardMinkowskiTimeOrientation`, `MinkowskiSpacetime` in Minkowski.lean; `pullbackVal` and its
six siblings in Pullback.lean; one site in CrossMetricIsometry.lean) are committed, so removing the
`set_option` line itself is a guard-protected change to the declaration (confirmed: the guard
blocked a direct test-removal on `StandardMinkowskiSpacetime`, citing "changes the definition of
the existing def"). Tested removal anyway via a throwaway `/tmp` copy with `sed` + `lake env lean`
(never touching the tracked files): with all three Minkowski.lean occurrences stripped, five
distinct elaboration failures appear across the file (`Application type mismatch` between
`TangentSpace 𝓘(ℝ, SpacetimeModel) x` and `SpacetimeModel`/`WithLp 2 (...)`, and a failed
`ContMDiffAt` rewrite) — confirmed load-bearing. Kept every occurrence (R07-3, R13-1, R13-2,
R08-1's 7 sites) and added a one-line explanatory comment above each `set_option` line (a
comment-only edit, not a guard-blocked change): the reason is that `TangentSpace I x` is only
semireducibly, not reducibly, defeq to the model space `SpacetimeModel`, which several
`val`/`symm`/`contMDiff` fields and lemmas need across the transparency boundary. The first
Pullback.lean occurrence and the CrossMetricIsometry.lean occurrence point to the existing
explanation already on `bilinearPrecomp`'s docstring; the other five in Pullback.lean just
cross-reference the first.
For R13-4 (`GNS/Amplification.lean:47`, `linter.unusedDecidableInType false` on
`not_isIrreducible_directSum`): tested removal first with `lake env lean` on the single file
(clean, no output), so removed it — but the whole-project `lake build` then reintroduced the
warning the option was suppressing (`'not_isIrreducible_directSum' does not use ... [DecidableEq
ι]`), i.e. single-file `lake env lean` does not run this linter the same way the full build does.
Restored the `set_option` with a one-line comment explaining the hypothesis is bound by the
ambient `variable` but only used irrelevantly (through `lp.single`/instance resolution).
Re-verified with `lake build Physicslib4.GNS.Amplification`: warning gone, build succeeds.
Set_options removed: 0. Set_options kept with an added comment: 9 (`respectTransparency` × 3 in
Minkowski.lean, × 6 in Pullback.lean [one site also carries `maxHeartbeats`, already commented],
× 1 in CrossMetricIsometry.lean; `linter.unusedDecidableInType false` × 1 in Amplification.lean).

## Final verification
`lake build` (whole project): succeeds, 3358 jobs. All warnings present are pre-existing and in
files/lines untouched by stage 2 (`GNS/Construction.lean`, `GNS/ExtremeState.lean`,
`GNS/NullSpace.lean`, `GNS/Superselection.lean`, `Operators/Conjugation.lean`,
`Spacetime/CrossMetricIsometry.lean:633/636/638` [pre-existing, not the line I commented],
`Spectral/Basic.lean`, `Spectral/BorelCalculus.lean`, `Spectral/ContinuousCalculus.lean`,
`Spectral/Forms.lean`, `Spectral/OperatorIntegral.lean` [pre-existing, not the lines I edited],
`Spectral/ProjectionValuedMeasure.lean`, `Spectral/Spectrum.lean`, `Analysis/CStarCompletion.lean`)
— none of the eight files edited in this stage (CausalComplement.lean, PureStateExists.lean,
QuasilocalIntertwiner.lean, Net.lean, GNS/Basic.lean, KMS.lean, BorelClasses.lean, DirectSum.lean,
Minkowski.lean, Pullback.lean, Amplification.lean, OperatorIntegral.lean) contribute a new warning.
`lake lint`: "Linting passed for Physicslib4." Stage 2 complete.

## 7. R03-2 — `@[nolint unusedArguments]` on `L0` (BorelClasses.lean:279)
Added a one-line comment above the attribute: `MeasurableSpace X` is unused in the body (only
`TopologicalSpace X` is needed via `C(X, ℝ)`), kept for parity with the file's other definitions,
and pointed back at the docstring for why the measurability conjunct is dropped. Comment-only
edit (the `def` itself untouched). Verified with
`lake env lean Physicslib4/Spectral/BorelClasses.lean`: no output.

## 8. R04-2 — unexplained `erw` in DirectSum.lean (lines 262, 294, 467 in the original; shifted by
docstring edits elsewhere in this stage)
Tested `rw` in place of each `erw`, individually, via the Edit tool (these are proof-body edits on
committed `private theorem`s, not statement changes, so not guard-protected):
- `single_mem_range_subSmul` (`apply_single_of_isDirectSumOperator hT i ξ`): `rw` fails with an
  `Application type mismatch` between `T.domain` and `(subSmul T c).domain` membership proofs
  under the subtype — a genuine semireducible-defeq gap. Kept `erw`, added a one-line comment.
- `sum_single_mem_graph` (`apply_single_of_isDirectSumOperator hT i (η i)` ... `at this`): `rw`
  **succeeds** here (no defeq obstruction in this context, unlike the `subSmul`-domain sites).
  Replaced `erw` with `rw` — a genuine simplification, no comment needed.
- `summand_mem_range_subSmul` (`apply_of_mem_summand hT m ξ`): same `subSmul`-domain mismatch as
  the first site; `rw` fails the same way. Kept `erw`, added a one-line comment.
Verified with `lake env lean Physicslib4/Spectral/Unbounded/DirectSum.lean`: no output (no new
errors/warnings) after all three changes together.
