# Review: manual chapter on spectral theory (2026-10-22)

Scope: A. docstring pass `25c01d5` (`Physicslib4/Spectral/`, 9 files, and
`Operators/LpDiagonal.lean`); B. `web/Manual/Spectral.lean` (uncommitted) and its rendered HTML
(`web/_out/manual/html-multi/Bounded-spectral-theory/index.html`, rebuilt: `lake build` and
`generate-manual` succeed).

Read: `.claude/CLAUDE.md`, the plan (chapter pattern, l. 69–91), the four earlier review memos, the
writer's log.

## A. Docstring pass (25c01d5)

### Checks that pass

- **Comments only.** All 10 files, with `--` and nested `/- -/` comments stripped (string literals
  kept) and whitespace normalised, are identical to `25c01d5^`. Nothing in these files changed
  after the commit.
- **Labels.** Every blueprint label cited in an added line exists in `blueprint/src`.
- **Format.** Summary line first; "Implementation note:" before a plain-text "Blueprint:" line;
  descriptive Blueprint lines for uncited declarations; `C\*-algebra` and `\*-algebra` escaped.
  No added docstring line is over 100 characters (by character count). No added line starts with
  a Lean keyword. No `**Restriction:**` lines are needed: none of these declarations is a
  deliberate restriction.
- **Accuracy, spot-checked against code and blueprint:**
  - `isCompact_spectrum`: prpstn:hall-7.5 part (1) is "closed, bounded, and non-empty", part (2)
    the |λ| > ‖A‖ bound. The corrected "the first two claims of part (1)" is right. The parts
    (3)–(4) remark matches lmm:spectrum-is-compact-metric-measurable.
  - `spectrum_nonempty` is part (1) of the same lemma, which lists it in `\lean{}`. Correct.
  - `realCalculus`: `realCalculus_properties` has the five conjuncts listed (mul, self-adjoint,
    positive, `‖f(A)‖ = ‖f‖`, `σ = range f`). `existsUnique_realCalculus` is uniqueness among
    `C(σ(A), ℝ) →L[ℝ] (H →L[ℂ] H)`. Mathlib's `Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`
    exists.
  - Associated measures: `existsUnique_assocMeasure` is fully proved (no `sorry` or `axiom` in
    `Spectral/*.lean`). The corrected claims are right.
  - Forms:
    - `toSesq` is `mkContinuous₂` of the two `choose`s; the "no real choice" note is accurate.
    - `isSelfAdjoint_toOperator` exists.
  - Borel classes:
    - `IsBumpFunction` fields: `[0,1]`, `= 1` on E, support ⊆ U.
    - `L0` is a bounded pointwise limit with no measurability conjunct.
    - `isClosed_mem_L0` omits `CompactSpace` and `BorelSpace`.
    - `IsBorelGenerating` fields: `bddMeasurable`, `smul_add_mem`, `continuous_mem`, `tendsto_mem`.
  - PVM:
    - Six fields as described.
    - μ(∅) = 0 follows from `HasSum` of the constant family. `existsUnique_assoc` derives it this
      way (l. 145).
    - `existsUnique_assoc` includes `IsFiniteMeasure`.
  - `integral`, `borelForm`, `FClass` (`smul_add_mem_FClass`, `continuous_mem_FClass`,
    `mem_FClass_of_tendsto` exist), `borelCalculus` (`borelCalculus_of_notMem`), `F1Class`,
    `F2Class`: accurate.
  - `spectralMeasure`: the four prpstn:mua-* labels exist.
  - `existsUnique_spectralMeasure`: the integrand is `fun l => ((l : ℝ) : ℂ)`, as stated.
  - `lpDiag`: def:finite-amplification names `Physicslib4.lpDiag` in its text, but its `\lean{}`
    is `diagAmplification, ampDiag, toLp2`. `lpDiag` is used in `GNS/DirectSum.lean` and
    `GNS/Amplification.lean`, as the docstring says.

### Findings

A1. *should fix.* `Spectral/ContinuousCalculus.lean`, `realCalculus` docstring, implementation note.
- **Problem.** The span `` `cfcHom hA` `` fails to elaborate in the manual because `hA` is
  unbound, so even `cfcHom` renders as an unlinked token. Writer's doubt B(1).
- **Fix.** Write: "the definition is Mathlib's continuous functional calculus `cfcHom` at the
  hypothesis `hA`, available because ...". Bare constants with implicit arguments do link in this
  chapter (for example `RealRMK.rieszMeasure` in the `assocMeasure` box), so `` `cfcHom` `` alone
  will link. `` `hA` `` renders as harmless plain code.
- **Also.** The module path `` `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap` `` renders as
  plain unlinked code. Optional: replace it with "because Mathlib makes `H →L[ℂ] H` a
  C\*-algebra".

A2. *nit.* `realCalculus` docstring writes "C⋆-algebra". The other docstrings in the pass (`lpDiag`)
and the chapter write "C\*-algebra". Fix: `C\*-algebra`.

A3. *nit.* `ProjectionValuedMeasure.assoc` docstring.
- **Problem.** `` `IsFiniteMeasure` `` renders unlinked: the manual does not open `MeasureTheory`.
- **Fix.** `` `MeasureTheory.IsFiniteMeasure` ``.
- **Also.** In the `ProjectionValuedMeasure` docstring, `` `MeasureTheory.VectorMeasure` ``
  renders unlinked, presumably because the module is not imported. Leave it as plain code, or
  drop the backticks.

A4. *nit.* `mul_resolvent_of_mem_resolventSet`: "The library states only this right-inverse equation."
- **Problem.** "The library" can be read as Mathlib.
- **Fix.** "This project states only the right-inverse equation." The project has no
  `resolvent_mul` lemma, so the claim is true.

A5. *nit.* `functionalCalculus`: "the properties proved for `borelCalculus` (...) hold for it".
- **Problem.** No lemma states these properties for `functionalCalculus`; they follow by
  rewriting.
- **Fix.** "... transfer to it through that equation."

A6. *nit.* The commit message says "19 uncited declarations". The log's proposals list 18, and a
grep of every `\lean{}` in `blueprint/src` confirms 18: the 17 `Spectral` declarations below plus
`lpDiag`. Fix the count in the log; the commit message stays as it is.

A7. *should fix, outside the pass; the log already flags it.* Two theorem and module docstrings are
wrong:
- `BorelClasses.lean` module docstring, l. 44 and 402: "the compact metric Borel context is
  needed". Both theorems `omit [CompactSpace X]`. Fix: "the metric Borel context (no compactness)".
- `ContinuousCalculus.lean` l. 345: "The four properties". The conjunction has five parts
  (l. 348 says "five"). Fix: "The five properties".

### Blueprint proposals for the 18 uncited declarations

I agree with the log's list, with these refinements. Each `\lean{}` addition is for the
lean-blueprint agent.

| # | Declaration | Proposed `\lean{}` node | Note |
|---|---|---|---|
| 1 | `polyOn`, `realCalculus` | prpstn:hall-8.3 | |
| 2 | `assocFunctional`, `assocMeasure` | prpstn:associated-measures-self-adjoint | Only this node, not def:hall-8.6: one home per declaration. |
| 3 | `ProjectionValuedMeasure.assoc` | thrm:projection-valued-measures-associated-measure | |
| 4 | `ProjectionValuedMeasure.integral` | thrm:operator-valued-integration | |
| 5 | `spectralMeasure` | thrm:hall-8.10 | The node that constructs μ^A. |
| 6 | `SesquilinearForm` | def:bounded-sesquilinear-form | |
| 6 | `IsQuadraticForm`, `polarization` | def:bounded-quadratic-form | |
| 7 | `IsBoundedQuadraticForm.toSesq` | prpstn:hall-a.61 | |
| 7 | `IsBoundedQuadraticForm.toOperator` | prpstn:hall-a.63 | |
| 8 | `IsMonotoneClass` | thrm:monotone-class-theorem | |
| 8 | `IsBorelGenerating` | lmm:hall-prblm-8.3.3b | |
| 9 | `BddMeasurable` | thrm:operator-valued-integration | Its first use in the blueprint's order; better still, a new definition node "Bounded measurable functions" next to def:indicator-function. Not def:hall-8.8, which comes later. |
| 9 | `BoundedPointwiseLimit` | thrm:bounded-convergence-theorem | |
| 10 | `mul_resolvent_of_mem_resolventSet` | def:bounded-operator-resolvent-and-spectrum | |
| 11 | `Physicslib4.lpDiag` | def:finite-amplification (`haag-kastler-axioms.tex`) | Its prose already names it. |

## B. Chapter `web/Manual/Spectral.lean`

### Checks that pass

- **Pattern.** Overview, Design, Main definitions and theorems, Where to look. About 2,800 words
  of prose, inside the plan's 2,500–4,000.
- **Section numbers.** These match `blueprint/src/content.tex` (GNS 10.1, spectral 10.2,
  unbounded 10.3, Stone 10.4, spacetime 10.5, HK 10.6).
- **Claims checked:**
  - Every statement is proved: no `sorry` or `axiom`.
  - `isOpen_resolventSet`, `exists_hasSum_resolvent`,
    `isBoundedQuadraticForm_integral_bddMeasurable`, `existsUnique_measure_of_positive_linear`
    and `pvm_integral_bddMeasurable_eq` exist.
  - The `sq_norm_sub_smul_apply_le` estimate is as stated.
  - "6 sup|f|" matches the formalization note of prpstn:integral-norm-bound (l. 1306).
  - "Separable and nonzero only for convenience" matches the blueprint (l. 45, 67).
  - `#check` outputs agree with the declarations.
  - The printed `fun l => ↑↑l` matches the prose.
- **Rendering.**
  - No literal `\*`, `$``, `**`, `{docstring` or `{apiDocs` leaks into the text.
  - The 23 "Blueprint:" lines are plain text.
  - All reference-style `[..][bp-*]` links resolve.
  - The only unlinked docstring spans are `cfcHom hA`, the module path, `Measurable f`,
    `IsFiniteMeasure`, `MeasureTheory.VectorMeasure` and two file paths. See A1 and A3.
- **Links.** All blueprint anchors exist (the writer checked them; I spot-checked
  prpstn:mua-integrates-to-A, lmm:lemma-3 and sctn:spectral-theorems). The page
  `sec10-2-spectral.html` exists. The chapter has no cross-chapter links, so the manual-root rule
  does not arise.
- **Style.** Present tense, no history narration, reminders for familiar material (Hermitian
  matrices, Born rule, multiplication operator). Pitched right for the reader.

### Findings

B1. *should fix.* Overview, Borel-calculus bullet (l. 62–65): "Both facts are extended from
continuous to Borel functions by a monotone-class argument."
- **Problem.** The bullet lists four facts: Q_f bounded, linearity, multiplicativity, and
  self-adjointness for real f. Only boundedness of Q_f and multiplicativity use the bootstrap.
  Linearity comes from linearity of f ↦ Q_f, and self-adjointness from Q_f being real.
- **Fix.** "The boundedness of Q_f and the multiplicativity are extended from continuous to Borel
  functions by a monotone-class argument."

B2. *should fix.* Headline coverage: the spectral radius and Gelfand's formula are not mentioned.
- **Problem.** §10.2 states def:spectral-radius (`\lean{spectralRadius}`) and
  thrm:gelfand-formula (`\lean{spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius}`);
  both are Mathlib's.
- **Fix.** After the compactness and nonemptiness sentence in "Spectrum and resolvent" (l. 246–251),
  add: "The spectral radius and Gelfand's formula are Mathlib's `spectralRadius` and
  `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`." Add [def:spectral-radius] and
  [thrm:gelfand-formula] to that subsection's Blueprint line.

B3. *should fix.* `web/README.md` (writer's doubt 2). The Layout list names only
`Manual/HaagKastler.lean`, marked "(in preparation)", although GNS, Spacetime and Curved are
published too. The plan (l. 91) requires the README to be updated.
- **Exact line,** inserted after l. 48 (`Manual.lean`), in include order:
  `` - `Manual/Spectral.lean`: "Bounded spectral theory" (blueprint Section 10.2). ``
- **For consistency,** also add:
  - `` - `Manual/GNS.lean`: "The GNS construction" (blueprint Section 10.1). ``
  - `` - `Manual/Spacetime.lean`: "Spacetime and geometry" (blueprint Section 10.5). ``
  - `` - `Manual/Curved.lean`: "The axioms in curved spacetime and general covariance" (blueprint Sections 10.7–10.8). ``
- **And change** the HaagKastler line to
  `` - `Manual/HaagKastler.lean`: "The Haag–Kastler axioms in Minkowski spacetime" (blueprint Section 10.6). ``

B4. *nit.* Design, l. 162: "Both are total functions on `X → ℂ`".
- **Problem.** `borelCalculus` is on `spectrum ℝ A → ℂ`.
- **Fix.** "Both are defined on all functions, with the value 0 on functions that are not bounded
  and measurable, so every statement takes the hypothesis `f ∈ BddMeasurable _` explicitly."

B5. *nit.* Some names in Main and Design are plain code where neighbours use `{apiDocs}`.
- **Names:** `isOpen_resolventSet`, `exists_hasSum_resolvent` (l. 250), `realCalculus_polyOn`
  (l. 295), `isSetAlgebra_L0`, `IsBorelGenerating.indicator_mem` (l. 413–415),
  `IsBoundedQuadraticForm.isSelfAdjoint_toOperator` (l. 373).
- **Fix.** Wrap each in `{apiDocs Physicslib4.Spectral.<name>}[...]`.

B6. *nit.* l. 35 is about 120 characters (the formula line). Reflow.

B7. *nit, optional.* Main intro (l. 218–225): one sentence would orient readers who come from the
blueprint. Proposed: "The subsections follow the order of the proof; the blueprint introduces
projection-valued measures before the continuous calculus."

## Writer's doubts B(1)–(4)

1. **`cfcHom hA`: fixable.** Write `` `cfcHom` `` alone and mention `hA` separately; see A1.
   Bare constants link here (for example `RealRMK.rieszMeasure`), and full qualification is not
   needed because `cfcHom` is root-namespace and imported. An import cannot bind `hA`.
2. **README: give the line.** See B3:
   `` - `Manual/Spectral.lean`: "Bounded spectral theory" (blueprint Section 10.2). ``, after
   l. 48. The other three published chapters are also missing.
3. **Dependency order: acceptable.** The plan's chapter pattern groups by topic and does not
   prescribe the blueprint's order. Dependency order reads better, since PVMs are only used after
   the Borel calculus exists, and every subsection's Blueprint line maps back to the nodes.
   Optionally state it (B7).
4. **`lpDiag` omitted: right.** It is §10.6 material (def:finite-amplification) used by
   `GNS/DirectSum.lean` and `GNS/Amplification.lean`; nothing in §10.2 uses it. Its natural home
   is the GNS chapter's "Direct sums and amplification" (`web/Manual/GNS.lean` l. 198). That
   chapter does not mention it either, so a `{docstring Physicslib4.lpDiag}` or an `apiDocs` link
   there is a follow-up.

## Verdict and top 5

Verdict: **accept with minor fixes.**
- Part A is comment-only and accurate. Its corrections (prpstn:hall-7.5 parts; the
  associated-measure theorem is proved) are right.
- Part B is accurate, well pitched and renders cleanly.
- No errors found. A: 2 should-fix, 5 nits. B: 3 should-fix, 4 nits.

Top 5:
1. B1: the Overview credits linearity and self-adjointness to the monotone-class argument.
2. B2: add the spectral radius and Gelfand's formula (Mathlib's) to "Spectrum and resolvent".
3. A1: `cfcHom hA` becomes `cfcHom` (links), with `hA` mentioned separately.
4. B3: list `Manual/Spectral.lean`, and the other published chapters, in `web/README.md`.
5. A7: fix the module and theorem docstrings the log flagged (no compactness needed; "five
   properties").
