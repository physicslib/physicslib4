# Review: manual chapter Unbounded + docstring passes (2026-10-23)

Scope: commits 3309c86, 9ff9402 (docstrings, Physicslib4/Spectral/Unbounded/), 7663dbe (web/Manual/Unbounded.lean).

## A. Docstring passes

Checks run. Comments-only: all eight files of `Physicslib4/Spectral/Unbounded/` are identical
between `3309c86^` and `9ff9402` with `--` and `/- -/` comments stripped and whitespace
normalised (own stripper, string-literal aware). Nothing in `Physicslib4/` changed after
`9ff9402`. Format: no added line over 100 characters, no unescaped asterisk outside code spans,
no keyword-initial line; every "Blueprint:" line is plain text. Accuracy: each cited lemma was
looked up and its hypotheses compared with the prose. Mathlib's adjoint
(`toFun := if hT : Dense .. then adjointAux hT else 0`, domain `adjointDomain` always); the
guard in `integralApply` (`if h : Measurable f ∧ ∃! χ, .. then h.2.choose else 0`) and the
linearity argument by `by_cases hf`; `pushforwardPVM` / `cayleyPVM` definitions;
`existsUnique_spectralMeasure_normal` (no `Nontrivial H`); `existsUnique_spectralMeasure_unbounded`
(`subsingleton_or_nontrivial`); `IsPositiveEnergy.isPositive_generator` (uses `IsPositive`). The
two corrected names and the "nonzero Hilbert space" fix are right.

A1. *should fix.* `AbstractCalculus.lean`, module docstring l. 14–17, and the
`IsAbstractCalculus` docstring (new in `9ff9402`, l. 72–74 of the docstring body).
- **Problem.** The module docstring says the bounded self-adjoint case of
  `Physicslib4/Spectral/SpectralTheorem.lean` and the bounded normal case "are then two instances
  of the one statement". The `IsAbstractCalculus` docstring repeats it: "the passage ... is
  carried out once, for the self-adjoint and the normal case together". Neither holds in Lean.
  `abstractPVM`/`IsAbstractCalculus` occur only in `AbstractCalculus.lean` and `Cayley.lean`, and
  `SpectralTheorem.lean` imports only `BorelCalculus` and `OperatorIntegral`, so it cannot use
  them. The blueprint itself says only that the *normal* case is an instance, and that §10.2's
  stage 2 is "the same argument specialized to X = σ(A)", reproduced here in general.
  Writer's doubt (2) is **confirmed**, and the pass introduced the same claim a second time.
- **Fix, module docstring** (replace the sentence "The bounded self-adjoint case of ... one
  statement."):
  "The bounded normal case below is an instance of it. The bounded self-adjoint case of
  `Physicslib4/Spectral/SpectralTheorem.lean` runs the same argument directly on X = σ(A), and
  is not derived from this file."
- **Fix, `IsAbstractCalculus`** (replace "so the passage from a continuous functional calculus
  to a spectral measure is carried out once, for the self-adjoint and the normal case together."):
  "so the passage from a continuous functional calculus to a spectral measure is carried out
  once, in general; the spectral theorem for bounded normal operators
  (`existsUnique_spectralMeasure_normal`) is the case Φ = `normalCalculus`."

A2. *nit.* `Basic.lean`, `existsUnique_adjoint_apply`, implementation note: "When `T.domain` is
not dense, Mathlib's `T†` is the zero map on that domain".
- **Problem.** "that domain" reads as `T.domain`; the zero map is on `adjointDomain`.
- **Fix.** "When `T.domain` is not dense, Mathlib's `T†` keeps the domain `adjointDomain` but is
  the zero map there; this is why the density hypothesis is needed here."

A3. *nit.* `Cayley.lean`, `pushforwardPVM`: "∫ g d(T(\*)μ) = ∫ (g ∘ T) dμ".
- **Problem.** `T(\*)μ` renders as "T(\*)μ", not a standard notation (the push-forward is T₊μ
  or T_\*μ; the parenthesis convention is for multi-character subscripts).
- **Fix.** "For a bounded measurable g on Z, ∫ g dν = ∫ (g ∘ T) dμ, where ν is the pushforward
  (`integral_pushforwardPVM`)."

A4. *nit.* `FunctionalCalculus.lean`, `functionalCalculus`: "the Hamiltonian H gives the time
evolution e^(−itH)".
- **Problem.** H is the Hilbert space in the same docstring ("defined on all of H"); the chapter
  writes Ĥ for this reason (log, Step 19).
- **Fix.** "the Hamiltonian Ĥ gives the time evolution e^(−itĤ)".

A5. *Proposals.*
- **`subSmul` → def:hall-3.1: confirm, with a preference.** The A − λ𝟙 convention is the
  unlabelled paragraph right after def:hall-3.1 (l. 28 of the section), so citing it from
  def:hall-3.1's `\lean{}` is defensible. Cleaner: wrap that paragraph in a
  `\begin{convention}` node (the section already uses `conv:` nodes, e.g. `conv:section-abstract`),
  say `conv:operator-minus-scalar`, with `\lean{Physicslib4.Spectral.Unbounded.subSmul}`; the
  docstring line then becomes "Blueprint: conv:operator-minus-scalar". Either is for the
  lean-blueprint agent and the user.
- **`pushforwardPVM` → thrm:hall-10.4: correct it.** The `\lean{}` list of thrm:hall-10.4
  names the statement (`existsUnique_spectralMeasure_unbounded`, `spectralMeasure_concentrated`);
  a proof device does not belong there, and lmm:borel-bijection-transports-pvm is about
  bijections, which `pushforwardPVM` is not. Proposed instead: a formalization note after the
  proof of thrm:hall-10.4, in the style of l. 1818: "\noindent\textit{Formalization note.} In
  Step 3 the Lean proof (\texttt{eq\_cayleyPVM\_of\_pmapIntegral\_eq}) pushes $\nu$ forward
  along $C$ directly to all of $S^1$ (\texttt{pushforwardPVM}, \texttt{integral\_pushforwardPVM}),
  which needs only measurability of $C$, instead of transporting it to $S^1\setminus\{1\}$ by
  Part 2 of Lemma~\ref{lmm:borel-bijection-transports-pvm} and extending by zero." The docstring's
  descriptive Blueprint line stays until the note exists. A similar note for thrm:hall-10.30
  (`cayleyPVM` composes with D instead of restriction and transport) would back the `cayleyPVM`
  docstring's claim.

A summary: 0 errors, 1 should-fix (A1), 3 nits (A2–A4), proposals A5.

## B. Chapter

Checks run. `cd web && lake build && lake exe generate-manual --output _out/manual`: exit 0; the
only warnings naming `Unbounded` are the library's module-system import notices. Rendered page
`_out/manual/html-multi/Unbounded-operators-and-their-spectral-theorem/index.html`: no literal
`\*`, `**`, `$\``, unresolved `[..][..]`, `{docstring`, `{apiDocs` or `{ref`. All 56 blueprint
anchors exist in `blueprint/web/chptr-haag-kastler-axioms-blueprint.html`; `home_page/sec10-3-unbounded.md`
exists. Word counts (prose, code and link definitions excluded): intro 170 (incl. imports and
comments), Overview 669, Design 1,336, Main 927, Where to look 236. Every §10.3 statement and
proof has `\leanok` (only the two `conv:` nodes lack it, as conventions) and `Spectral/Unbounded/`
has no `sorry`, so "Every statement of the section is proved in Lean" holds. All 12 `#check`
outputs match their declarations. Headline coverage of §10.3 is complete: 9.17, 9.21, 9.26 (both
forms), 10.1–10.3, 10.20, 10.23, the normal calculus, 10.28, 10.30, 10.4, def:spectral-measure,
10.5 and lmm:functional-calculus-bounded each have a docstring, a `#check` or a link. Prose:
present tense, reminders where due ("As you will recall"), well pitched; no temporal wording.

B1. *error.* Main, "The abstract functional calculus", l. 502 (`{docstring IsAbstractCalculus}`),
against Design l. 200–201.
- **Problem.** The embedded docstring renders "the passage from a continuous functional calculus
  to a spectral measure is carried out once, for the self-adjoint and the normal case together"
  (confirmed in the HTML), which is false (see A1). Design l. 200–201 says, correctly, that the
  bounded self-adjoint theorem is not rederived from `abstractPVM`, so the page contradicts itself.
- **Fix.** The A1 fix to the `IsAbstractCalculus` docstring; nothing in the chapter changes.

B2. *should fix.* Design l. 102: "no declaration assumes $`H` separable".
- **Problem.** `Integral.lean` l. 399, `completeSpace_and_separableSpace_of_isClosed`, carries
  `[TopologicalSpace.SeparableSpace H]` (it is lmm:closed-subspace-is-hilbert as the blueprint
  states it). The claim is false as written. (Outside scope: `Spectral/Basic.lean` l. 91 says
  the same of "the `Spectral` directory"; it needs the same qualification.)
- **Fix.** "bounded operators are `H →L[ℂ] H`, no result on the way to the spectral theorem
  assumes $`H` separable (only
  {apiDocs Physicslib4.Spectral.Unbounded.completeSpace_and_separableSpace_of_isClosed}[`completeSpace_and_separableSpace_of_isClosed`],
  the blueprint's lemma on closed subspaces, does), and bounded operators are obtained from
  bounded quadratic forms."

B3. *should fix.* Design l. 184: "The Cayley transform of a self-adjoint operator is unitary,
normal but not self-adjoint".
- **Problem.** Not true in general: for A = 0, U = (i)(−i)⁻¹ = −𝟙, which is self-adjoint.
- **Fix.** "The Cayley transform of a self-adjoint operator is unitary, hence normal, but in
  general not self-adjoint, so the route ..."

B4. *should fix.* Design l. 100 and l. 214 (writer's doubt 4); also l. 115.
- **Problem.** l. 100 promises that each departure "links the blueprint's formalization note".
  The three Cayley bullets have no note to link (the blueprint has none for thrm:hall-10.30 or
  thrm:hall-10.4), and def:product-hilbert-space has no paragraph labelled "Formalization note"
  (it has "A word on the Lean formalization", inside the definition). The bullets themselves are
  accurate: blueprint Step 3 uses Part 2 of lmm:borel-bijection-transports-pvm onto S¹ \ {1} and
  extends by zero; the Lean proof pushes ν to S¹ with `pushforwardPVM`. "Differ from the
  blueprint's text" is the right wording; it is only the promise of a note that is unbacked.
- **Fix.** l. 100: "Where the library departs from the blueprint's route, this section says so,
  and links the blueprint's formalization note where it has one." l. 214: "Three choices differ
  from the blueprint's text; the blueprint does not record them:". l. 115: "(the remark on the
  Lean formalization in def:product-hilbert-space)". If the A5 notes are added, revert l. 214 to
  link them.

B5. *should fix.* Blueprint lines of "Domains, adjoints and self-adjointness" (l. 248–251) and
"Bounded normal operators" (l. 453–456).
- **Problem.** l. 238 says "Each subsection opens with the blueprint entries it covers", but
  entries the subsection does discuss are missing: def:hall-9.3 (extension, `T ≤ B`),
  def:closed-linear-map-on-a-subspace (`isClosed_iff_forall_tendsto`), prpstn:hall-9.8
  (`isClosable_of_isSymmetric`), prpstn:hall-9.10 (`adjoint_closure_eq_adjoint`),
  def:kernel-of-an-unbounded-operator, def:range-of-an-unbounded-operator (`ker`, `range`),
  prpstn:hall-9.13 (`isSelfAdjoint_add_of_isSelfAdjoint`); and def:hall-7.14 (`spectralSubspace`).
- **Fix.** Add these labels, with link definitions in the same `[ub-..]` style, to the two lines.

B6. *nit.* Design length (writer's doubt 1): 1,336 words. Cut about 45:
- delete l. 227–229 "Functions of $`A` are functions `f : ℝ → ℂ`, and the identity function is
  `fun x : ℝ => (x : ℂ)`, which Lean prints as `fun x => ↑x`." (Main intro l. 241 says it);
- replace item 2 (l. 160–162) by "2. On $`W_f`, $`Q_f(\psi) = \int f \, d\mu_\psi` is a quadratic
  form on a subspace (`integralForm`, `IsQuadraticFormOn`)."
  Result about 1,290.

B7. *nit.* Design l. 145: `IsResolvent T λ B`; l. 149 says `λ` is a Lean keyword. Write
`IsResolvent T lam B`.

B8. *nit.* Where to look l. 659: "one stage per file". Eight files, five stages. Write "in eight
files, by topic."

B9. *nit.* Overview l. 41: "any observable with unbounded spectrum, such as a Hamiltonian".
Write "such as most Hamiltonians" (the `HasDenseDomain` docstring's wording).

B10. *nit.* Plain code where `{apiDocs}` is used elsewhere (spectral review B5 pattern): Design
l. 179 `isEssentiallySelfAdjoint_of_isDirectSumOperator`, l. 207 `exists_isCayleyTransform`,
l. 216–222 `cayleyPVM`, `restrictPVM`, `mapPVM`, `eq_of_integral_id_eq_ambient`, `pushforwardPVM`;
Main l. 630 `isSelfAdjoint_pmapIntegral_of_real`. Wrap each in
`{apiDocs Physicslib4.Spectral.Unbounded.<name>}[...]`.

## Writer's doubts B(1)–(5)

1. **Design length:** the cut in B6 (about 45 words, to about 1,290).
2. **Unbounded normal spectral theorem: confirmed.** The blueprint has none (its unbounded
   theorem is thrm:hall-10.4, self-adjoint only; normal operators appear only bounded, from
   l. 1822), and no declaration in `Spectral/Unbounded/` combines `IsStarNormal` with
   `H →ₗ.[ℂ] H`. Overview l. 90–92 is accurate.
3. **AbstractCalculus overstatement: confirmed** (A1). The chapter's own Design text
   (l. 194–201) is right; the embedded `IsAbstractCalculus` docstring is not (B1). Fix both
   docstrings as in A1.
4. **`pushforwardPVM` "departure":** the content is right and "differ from the blueprint's
   text" is the correct wording; what is wrong is l. 100's promise of a formalization note (B4).
   Better still, add the note (A5).
5. **Hellinger–Toeplitz: reads as background.** It sits in the "As you will recall" paragraph,
   is attributed by name, and no library name is attached; nothing in the library proves or
   uses it (no match for "Hellinger" in `Physicslib4/` or the blueprint). No change needed.
   The Sobolev example likewise reads as a reminder.

## web/ temporal-wording check

`scripts/check_temporal_wording.py` scans `blueprint/src/sections`, `Physicslib4`, `home_page`,
`README.md`, not `web/`. A `/tmp` copy with `ROOTS = ["web/Tutorial", "web/Manual",
"web/Tutorial.lean", "web/Manual.lean"]` flags three lines, all in
`web/Tutorial/DoingItYourself.lean`, all false positives:
- l. 120 "Change an example so that it no longer checks" (about the build, not history);
- l. 205 'no "previously" or "now"' (states the rule);
- l. 876 'a docstring ... that reads "The state is now proved unique."' (the exercise's bad example).
`web/Manual/` (including this chapter) and the rest of `web/` (`README.md`, `Site`, `Book`):
nothing, and no version strings. Adding `web/` to `ROOTS` (excluding `_out/` and `.lake/`) would
therefore need `temporal-ok` on those three lines.

## Verdict and top 5

Verdict: **accept with fixes.** Part A is comments-only, accurate apart from one overstatement
it repeats, and in the agreed format. Part B is accurate, complete on §10.3's headline results,
well pitched, and renders cleanly; one rendered contradiction (from the docstring) and three
unbacked or false claims need fixing.

Counts. A: 0 errors, 1 should-fix, 3 nits (plus the A5 proposals). B: 1 error, 4 should-fix,
5 nits.

Top 5:
1. A1/B1: fix the `IsAbstractCalculus` docstring and the `AbstractCalculus.lean` module
   docstring; the bounded self-adjoint theorem is not derived from `abstractPVM`.
2. B2: "no declaration assumes H separable" is false (`completeSpace_and_separableSpace_of_isClosed`).
3. B3: the Cayley transform is not "not self-adjoint" in general (A = 0 gives U = −𝟙).
4. B4: qualify l. 100's promise of formalization notes; optionally add the notes (A5).
5. B5: complete the Blueprint lines (def:hall-9.3, 9.8, 9.10, 9.13, closedness, kernel, range,
   def:hall-7.14).
