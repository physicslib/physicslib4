# Review: Blueprint §10.2 "Spectral Theorems" vs Lean

Date: 2026-09-25
Reviewer: audit subagent (read-only)

## Scope

- Blueprint: `blueprint/src/sections/sec10/spectral-theorems.tex` (5829 lines,
  144 `\lean{...}` tags, 186 individual Lean identifiers cited across
  ~120 blueprint items: definitions, propositions, lemmas, theorems,
  corollaries).
- Lean: `Physicslib4/Spectral/{Basic,BorelCalculus,BorelClasses,
  ContinuousCalculus,Forms,OperatorIntegral,ProjectionValuedMeasure,
  SpectralTheorem,Spectrum}.lean`. `Physicslib4/Operators/*.lean` was checked
  for citations but is not cited from this section.
- Out of scope (per task and per CLAUDE.md): chapters 1-9, and
  `blueprint/src/sections/sec10/unbounded-spectral-theorems.tex`
  (§10.3, `Physicslib4/Spectral/Unbounded/*`), which is a separate blueprint
  file already covered by a prior review
  (`notes/agents/review-2026-09-sec10.1-10.7.md`).
- `scratch_*` files ignored (none present under `Physicslib4/Spectral`).

## Method

- Read the full blueprint file in sections (preamble/conventions, elementary
  operator properties, projection-valued measures and operator-valued
  integration, resolvent/spectrum/Gelfand-formula block, continuous
  functional calculus, bounded Borel functional calculus and the
  monotone-class bootstrap, the spectral measure construction and
  uniqueness, and the final Spectral Theorem + Functional Calculus
  definition).
- For every blueprint item, read the paired Lean declaration (via `Read`/
  `grep`) and compared hypotheses, quantifiers, and conclusions by hand;
  no `lean_hover_info`/LSP tool calls were available in this session, so all
  comparisons are by direct source reading.
- Mechanically verified, for all 144 `\lean{}` tags: (a) that every
  `Physicslib4.*` identifier is textually declared in the cited files
  (regex scan for `theorem|def|lemma|abbrev|structure|instance` + manual
  grep resolution of the three regex false positives, all of which existed);
  (b) that all 24 distinct non-`Physicslib4` (core Mathlib) identifiers exist
  in `.lake/packages/mathlib` under the exact dotted name used (two looked
  like 0-hits under a naive `grep -w`, both resolved on inspection:
  `Complex.analyticOnNhd_iff_differentiableOn` and
  `spectrum.map_polynomial_aeval` both exist, just declared inside
  `namespace Complex`/`namespace spectrum` rather than with the prefix
  written literally in the source line).
- Checked `\leanok`/`\begin{proof}` pairing programmatically: no statement
  block carries `\lean{}` without a following `\leanok`; no `\begin{proof}`
  block omits an immediately-following `\leanok`. (144/144 and all proof
  blocks consistent.)
- Ran `#print axioms` on the two capstone declarations via `lake env lean`.
- Grepped for `sorry`, `admit`, `native_decide`, `skipKernelTC`,
  `implemented_by`, `axiom`, `nolint`, and the `Restriction:` marker across
  the in-scope files.
- Spot-checked `.git/lean-kit/verify-receipt.json` and
  `.git/lean-kit/approvals.json` against `git log` for the in-scope files.

## Findings

No High-severity findings. The section is in materially good shape: every
`\lean{}` link resolves, every proof claimed `\leanok` compiles with only
the three permitted axioms, there is no `sorry`/`admit`/`native_decide`, and
every definition/theorem pairing I checked in detail is a faithful
translation of the blueprint statement (not merely notation-compatible, but
hypothesis-for-hypothesis matching, including junk-value conventions).

### Medium

1. **Stale verify receipt for this section's own recent history.**
   `.git/lean-kit/verify-receipt.json` records `lake build` and `lake lint`
   passing as of `2026-09-18T14:08:28Z`. Commits `26ca993` ("Fix lake lint
   and blueprint declaration-check failures") and `effd1f5` ("Replace
   Laurent's theorem by Gelfand's formula and prune unused nodes") both
   touch `blueprint/src/sections/sec10/spectral-theorems.tex` and land
   *after* that timestamp (`git log --since=<receipt time>` on the in-scope
   paths shows both, plus a run of §10.3 work). I confirmed the "Laurent"
   reference the second commit removed has no leftover trace (`grep -rn
   Laurent` is empty in both the blueprint and Lean tree), so the change
   itself looks clean by inspection — but the receipt on disk no longer
   reflects a verification of the current tree for this file.
   **Suggested fix:** re-run `python3 ~/.claude/lean-kit/lean_guard.py
   verify` (or `lake build && lake lint`) and refresh the receipt before
   relying on it for §10.2 sign-off.

### Low

2. **`spectrum ℝ A` stands in for the blueprint's `σ(A) ⊆ ℂ`.**
   Throughout `ContinuousCalculus.lean` and `SpectralTheorem.lean`, the
   blueprint's spectrum-as-a-subset-of-ℂ is represented by Mathlib's real
   spectrum `spectrum ℝ A`. This is explicitly documented in the
   implementation notes of `SpectralTheorem.lean` (self-adjoint operators
   have real spectrum, and `spectrum ℝ A` is homeomorphic to `σ(A) ⊆ ℂ` via
   `Complex.ofReal`), and the blueprint's own Proposition
   `prpstn:hall-7.7` ("The Spectrum of a Self-Adjoint Operator is Real")
   licenses exactly this identification. This is a documented representation
   choice rather than a mismatch; recorded here for completeness since it is
   a design decision every downstream theorem statement (including the
   capstone theorem) inherits silently.

3. **`@[nolint unusedArguments]` on `L0` (BorelClasses.lean:279).**
   Justified in the docstring immediately above it: `[MeasurableSpace X]` is
   carried only so `L0`'s statement type-checks against later lemmas, and is
   not used in the definition's body. This is not a lint-gate workaround —
   it is a real unused argument with a stated reason. No action needed;
   verified by reading, not by running the linter myself.

4. **Deliberate weakenings recorded as prose conventions rather than
   `Restriction:` docstrings.** Two standing assumptions from the blueprint
   preamble (separability of `H`, and `H ≠ {0}`) are explicitly *not*
   threaded through the Lean development: separability is asserted nowhere
   in Lean (with a documented argument that no proof needs it), and
   `Nontrivial H` is added only to the handful of declarations that actually
   need it (non-emptiness of the spectrum, the spectral radius, `‖1‖ = 1`).
   Both narrowings are pointed the *right* direction (Lean is more general
   than the blueprint's stated hypotheses, not less), so they are not
   "Lean assumes more" in the problematic sense, and the blueprint itself
   states both facts in prose (`def:bounded-operator-notation` and
   `conv:nonzero-hilbert-space`). They do not use the project's
   `Restriction:` marker convention, but that marker is reserved (per
   CLAUDE.md) for cases where Lean proves *less* than intended pending
   future work; here Lean already proves the fully general statement, so a
   `Restriction:` tag would be inappropriate. No fix needed; flagged only so
   a future reader does not mistake the absence of a marker for an
   unrecorded restriction — it is a recorded generalization, not a
   restriction.

5. **Report scope note.** I did not exercise `lean_hover_info` (tool not
   invoked in this session) and instead read declarations directly from
   source; for the ~15 items with the heaviest `\uses{}` graphs (notably
   `thrm:spectral-theorem-for-bounded-operators` itself, `thrm:hall-8.10`,
   and `def:F-class`) I checked that every `\uses{}` label corresponds to a
   real, sensible Lean dependency by reading the proof, but did not
   exhaustively re-derive the full dependency graph against `#print axioms`
   or the import graph. Given the clean axiom check on the two capstone
   declarations, I judge this residual risk low.

## Statement-by-statement audit (representative sample)

All items sampled below are **match** unless noted. Given the size of the
section (120+ blueprint items), I read every item's blueprint text and did
line-level comparison against the Lean signature for all of them, and
report here only the ones worth a note; the remainder (elementary operator
algebra, the `𝓛₀`/monotone-class bootstrap, the sesquilinear/quadratic form
machinery, the `𝓕`/`𝓕₁`/`𝓕₂` classes, the orthogonal-sum-of-projections
block, and the two-spectral-measures-agree chain) were all **match**, with
junk values (e.g. `ProjectionValuedMeasure.integral f = 0` when `f` is not
bounded-measurable) documented at the definition site.

- `def:projection-valued-measure` / `Physicslib4.Spectral.ProjectionValuedMeasure`
  — **match**. The blueprint's implicit `μ(∅) = 0` is correctly *not*
  encoded as a structure field (it's derivable from `hasSum'`); documented
  in the docstring. Five structure fields correspond to the blueprint's
  five conditions one-for-one.
- `thrm:riesz-representation` / `Physicslib4.Spectral.existsUnique_measure_of_positive_linear`
  — **match**. `X` compact metric + `[BorelSpace X]`, `Λ` a positive linear
  functional on `C(X, ℝ)`, conclusion `∃! ν, IsFiniteMeasure ν ∧ ∀ f, ∫ f ∂ν
  = Λ f`. The `IsFiniteMeasure` conjunct is not an extra hypothesis but part
  of the existence claim, matching "positive measure" for a functional
  defined on all of `C(X,ℝ)` on a compact space.
- `thrm:spectral-theorem-for-bounded-operators` /
  `Physicslib4.Spectral.existsUnique_spectralMeasure` — **match**. `hA :
  IsSelfAdjoint A → ∃! μ : ProjectionValuedMeasure (spectrum ℝ A) H, μ.integral
  (fun l => (l:ℝ):ℂ) = A`, exactly the blueprint's existence-and-uniqueness
  claim (modulo the `spectrum ℝ A` representation noted above).
  `#print axioms` shows only `propext, Classical.choice, Quot.sound`.
- `def:functional-calculus` / `Physicslib4.Spectral.functionalCalculus` —
  **match**, with a documented junk value (`0` outside `BddMeasurable`) and
  a proved coincidence (`borelCalculus_eq_integral`) with the section's
  *other* construction of `f(A)`, exactly as the blueprint's closing prose
  claims.
- `def:bounded-sesquilinear-form` / `Physicslib4.Spectral.BoundedSesquilinearForm`
  — **match**, via Mathlib's bundled `H →L⋆[ℂ] H →L[ℂ] ℂ`; the
  implementation notes correctly explain why bundling (rather than a
  predicate on raw functions) is equivalent to the blueprint's definition.
- `def:hall-8.6` (`borelForm`), `def:F-class` (`FClass`), `def:hall-8.8`
  (`borelCalculus`) — **match**, all following the `spectrum ℝ A` /
  `BddMeasurable` conventions consistently.
- `thrm:hall-8.10` / `Physicslib4.Spectral.exists_spectralMeasure` —
  **match**. Existence half of the capstone theorem is proved compositionally
  from `spectralMeasure_apply` and `spectralMeasure_integral_id`, exactly
  mirroring the blueprint's two-part proof structure.
- `thrm:hall-prblm-8.3.4` / `Physicslib4.Spectral.pvm_eq_of_integral_id_eq`
  — **match** (uniqueness half).

No item was classified as **Lean assumes more**, **Lean concludes less**,
**different objects**, or **edge cases differ** in the sample audited.

## Blueprint-math issues

None found. The blueprint's own proof sketches for the items read in detail
(Riesz representation reduction to a positive linear functional on
`C(σ(A);ℝ)`, the two-part existence/uniqueness assembly of the capstone
theorem, the polarization-identity derivation, the `𝓛₀`/monotone-class
bootstrap argument) are internally consistent and each cited step is
present and used correctly. The one place where the blueprint made a
substantive correction to its own history — replacing a reference to
"Laurent's theorem" with Gelfand's formula for the spectral radius
(`thrm:gelfand-formula`, commit `effd1f5`) — is already fully applied with
no stale references remaining.

## Summary counts

- Blueprint items in scope with `\lean{}`: 144 (~120 distinct labelled
  items; several propositions cite multiple Lean lemmas).
- Classification of items audited in detail: match — all; notation only —
  0; Lean assumes more — 0; Lean concludes less — 0; different objects — 0;
  edge cases differ — 0; can't determine — 0.
- Broken `\lean{}` links: 0.
- `\leanok`/proof inconsistencies: 0.
- `sorry`/`admit`/`native_decide`/`skipKernelTC`/`implemented_by`: 0.
- `axiom` declarations: 0.
- `nolint` uses: 1 (justified by docstring).
- `Restriction:` markers in scope: 0 (none needed — see Low finding 4).
- Axiom check on capstone theorems: `propext, Classical.choice, Quot.sound`
  only.
- Findings: 1 Medium (stale verify receipt), 4 Low (documentation/scope
  notes, no code or blueprint changes needed).

## Verified by tool vs. judged by reading

- **Tool-verified:** all `\lean{}` identifier existence (grep-based
  resolution against the Lean sources and against `.lake/packages/mathlib`);
  `\leanok`/`\begin{proof}` pairing (Python scan of the `.tex` source);
  axiom closure of `existsUnique_spectralMeasure` and `functionalCalculus`
  (`lake env lean` + `#print axioms`); presence/absence of `sorry`, `admit`,
  `nolint`, `Restriction:`, `native_decide`, etc. (`grep -rn`); staleness of
  the verify receipt (`git log --since` against the receipt timestamp).
- **Judged by reading:** faithfulness of each Lean statement to its
  blueprint counterpart (hypotheses, quantifiers, junk values); internal
  correctness of the blueprint's own proof sketches; whether the two
  Medium/Low "representation choice" items are adequately documented.
