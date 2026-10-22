# Reference manual, chapter "Bounded spectral theory": progress log

Plan: `plan-verso-reference-manual-2026-10-17.md` (chapter 2). Part A is a docstring pass over the
headline declarations of `Physicslib4/Spectral/` (top level only, not `Unbounded/` or `Stone/`)
and `Physicslib4/Operators/LpDiagonal.lean`; part B (the chapter text) is a later step. Appended
after each file.

## Step 0: reconnaissance (2026-10-22)

- Read `.claude/CLAUDE.md`, the plan (chapter 2), the review memos (format: one-sentence first
  line; mathematics for a first-year theoretical-physics PhD student; "Implementation note:" as
  the last paragraph before "Blueprint: <label>" in plain text, descriptive form for uncited
  declarations; multi-character subscripts in parentheses; literal asterisks escaped as `\*`
  where Markdown would pair them; no docstring line starting with a Lean keyword; present tense).
- Blueprint: `blueprint/src/sections/sec10/spectral-theorems.tex` (labels and `\lean{}` lists
  collected with grep).
- Headline definitions found: `BddMeasurable`, `BoundedPointwiseLimit` (Basic); none in
  Spectrum (spectrum and resolvent set are Mathlib's); `polyOn`, `realCalculus`,
  `assocFunctional`, `assocMeasure` (ContinuousCalculus); `SesquilinearForm`,
  `BoundedSesquilinearForm`, `polarization`, `IsQuadraticForm`, `IsBoundedQuadraticForm`,
  `toSesq`, `toOperator` (Forms); `IsBumpFunction`, `IsMonotoneClass`, `L0`,
  `IsBorelGenerating` (BorelClasses); `ProjectionValuedMeasure`, `assoc` (PVM); `integral`
  (OperatorIntegral); `borelForm`, `FClass`, `borelCalculus`, `F1Class`, `F2Class`
  (BorelCalculus); `spectralMeasure`, `functionalCalculus` (SpectralTheorem); `lpDiag`
  (LpDiagonal).

## Step A1: `Spectral/Basic.lean` (2026-10-22)

- `BddMeasurable`, `mem_resolventSet_iff_isUnit_sub_smul`, `spectrum_eq_compl_resolventSet`,
  `mul_resolvent_of_mem_resolventSet`, `BoundedPointwiseLimit` (5 docstrings; the field
  docstrings of `BoundedPointwiseLimit` are accurate and kept). The resolvent theorems stand in
  for the resolvent/spectrum definitions, which are Mathlib's.
- Checked: Mathlib's resolvent set uses λ𝟙 − A (`spectrum.mem_resolventSet_iff`); `spectrum` is
  `rfl` the complement; Mathlib's `resolvent A λ` = Ring.inverse (λ𝟙 − A), the negative of the
  blueprint's (A − λ𝟙)⁻¹ (stated in the docstring); the quadratic bound `C * ‖φ‖ ^ 2` is used with
  `BoundedPointwiseLimit` in Forms.lean (l. 557, 606).
- Uncited (descriptive Blueprint lines): `BddMeasurable`, `mul_resolvent_of_mem_resolventSet`,
  `BoundedPointwiseLimit`.
- Built; 15 warnings, same as HEAD (pre-existing long line 662, flexible-simp notices).

## Step A2: `Spectral/Spectrum.lean` (2026-10-22)

- No definitions (spectrum and resolvent set are Mathlib's; their identification with the
  blueprint is in Basic.lean). Rewrote the three headline theorems the chapter will cite:
  `isCompact_spectrum`, `spectrum_nonempty`, `spectrum_subset_real` (3 docstrings). Other
  theorems left alone.
- Corrected: `isCompact_spectrum` said closedness and boundedness are "parts (1) and (2)" of
  prpstn:hall-7.5; both are in part (1) (part (2) is the bound |λ| > ‖A‖ ⇒ λ ∈ ρ(A)).
- Checked: `spectrum.isCompact`, `spectrum.nonempty` (Liouville), `IsSelfAdjoint.spectrumRestricts`
  (`SpectrumRestricts A Complex.re`: each z in the complex spectrum equals its real part).
- Built; only the pre-existing `simp` and module-system notices.

## Step A3: `Spectral/ContinuousCalculus.lean` (2026-10-22)

- `polyOn`, `realCalculus`, `assocFunctional`, `assocMeasure` (4 docstrings), plus one sentence
  of `existsUnique_assocMeasure` (error, below). Kept the formalization route: `realCalculus` is
  Mathlib's `cfcHom hA`, a `StarAlgHom` over ℝ (part of prpstn:hall-8.4); `assocMeasure` is
  `RealRMK.rieszMeasure (assocFunctional hA ψ)`.
- Corrected: `realCalculus` said the definition avoids "any unproved statement", `assocMeasure`
  called `existsUnique_assocMeasure` "unproved", and `existsUnique_assocMeasure` said uniqueness
  "is left open". The theorem is fully proved (uniqueness by
  `Measure.ext_of_integral_eq_on_compactlySupported`); all three texts are fixed.
- Checked: `realCalculus_properties` (multiplicative, self-adjoint, positive, isometric,
  σ(f(A)) = range f); `assocMeasure_univ` (mass ‖ψ‖²); `borelForm` integrates against
  `assocMeasure`.
- Uncited (descriptive Blueprint lines): `polyOn`, `realCalculus`, `assocFunctional`,
  `assocMeasure`.
- Built; only the pre-existing `Try this` notices.

## Step A4: `Spectral/Forms.lean` (2026-10-22)

- `SesquilinearForm`, `BoundedSesquilinearForm`, `polarization`, `IsQuadraticForm`,
  `IsBoundedQuadraticForm`, `IsBoundedQuadraticForm.toSesq`, `IsBoundedQuadraticForm.toOperator`
  (7 docstrings). The four field docstrings of the two structures are accurate and kept.
- Checked against def:bounded-sesquilinear-form and def:bounded-quadratic-form: bundled
  `H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ` / `H →L⋆[ℂ] H →L[ℂ] ℂ`; homogeneity Q(λψ) = |λ|² Q(ψ); polarization formula;
  `polarization_inner`, `polarization_diag`, `exists_bound_polarization`; `toOperator` is the
  adjoint of `continuousLinearMapOfBilin toSesq`; `integral` and `borelCalculus` are built from
  bounded quadratic forms (via `existsUnique_integral` / `existsUnique_borelCalculus`, whose
  proofs use `toOperator`/`eq_toOperator`). Dropped a draft claim ⟨φ, Aψ⟩ = L(φ, ψ) for
  `toOperator`, which has no library lemma.
- Uncited (descriptive Blueprint lines): `SesquilinearForm`, `polarization`, `IsQuadraticForm`,
  `toSesq`, `toOperator`.
- Built; no new warnings (the long lines 305–357 are pre-existing, in proofs).

## Step A5: `Spectral/BorelClasses.lean` (2026-10-22)

- `IsBumpFunction`, `IsMonotoneClass`, `L0`, `IsBorelGenerating` (4 docstrings; the field
  docstrings of the three structures are accurate and kept).
- Checked: `isClosed_mem_L0` (thickenings, bump functions; metric only), `isSetAlgebra_L0`
  (algebra of sets and contains the open sets), `measurableSet_of_mem_L0` (`BorelSpace`),
  `IsBorelGenerating.indicator_mem` and `.eq_bddMeasurable` both `omit [CompactSpace X]`, so they
  need a metric space with its Borel σ-algebra but not compactness; the docstring says so. The
  measurability conjunct of def:L0-class is omitted by design (kept as implementation note).
- Follow-up (module docstring, outside this pass): it says `indicator_mem` and
  `eq_bddMeasurable` need "the compact metric Borel context"; neither needs compactness.
- Uncited (descriptive Blueprint line): `IsMonotoneClass`; `IsBorelGenerating` (hypotheses of
  lmm:hall-prblm-8.3.3b, whose `\lean{}` lists only `IsBorelGenerating.indicator_mem`).
- Built; no new warnings.

## Step A6: `Spectral/ProjectionValuedMeasure.lean` (2026-10-22)

- `ProjectionValuedMeasure` and its 6 fields, `ProjectionValuedMeasure.assoc` (8 docstrings).
  Kept the implementation notes (total function vanishing off measurable sets, as
  `VectorMeasure`; μ(∅) = 0 derived, not a field; `HasSum`; equivalence = equality via `ext`).
- Checked against def:projection-valued-measure (items 1–4 and the equivalence clause);
  `assoc` is `(existsUnique_assoc μ ψ).choose`; `inner_integral` gives ⟨ψ, (∫ f dμ)ψ⟩ = ∫ f dμ_ψ.
  There is no named lemma for μ(∅) = 0 or for the total mass of μ_ψ; the docstrings say how each
  follows (constant family; `assoc_apply` with E = X) and claim no lemma.
- Uncited (descriptive Blueprint line): `ProjectionValuedMeasure.assoc`.
- Built; no new warnings.

## Step A7: `Spectral/OperatorIntegral.lean` (2026-10-22)

- `ProjectionValuedMeasure.integral` (1 docstring; the only definition). Checked:
  `(existsUnique_integral μ).choose ⟨f, h⟩`, 0 off `BddMeasurable X`; `inner_integral`;
  `integral_indicator`, `integral_add`/`integral_smul` (linearity not definitional),
  `integral_mul`, `norm_integral_le` (‖∫ f dμ‖ ≤ ⨆ x, ‖f x‖), `integral_conj`;
  `existsUnique_integral` builds the map from `toOperator` of Q_f.
- Uncited (descriptive Blueprint line): `ProjectionValuedMeasure.integral`.
- Built; no new warnings (long lines 691–750 are pre-existing, in proofs).

## Step A8: `Spectral/BorelCalculus.lean` (2026-10-22)

- `borelForm`, `FClass`, `borelCalculus`, `F1Class`, `F2Class` (5 docstrings).
- Checked: `borelForm` integrates against `assocMeasure`; `FClass` is shown to be all bounded
  Borel functions only inside the proof of `isBoundedQuadraticForm_borelForm` (no public
  equality lemma; the docstring says so); `borelCalculus` is the choice from
  `existsUnique_borelCalculus` (built from `toOperator`), 0 off `BddMeasurable`
  (`borelCalculus_of_notMem`); linearity, `borelCalculus_mul`, `isSelfAdjoint_borelCalculus`
  (real f), `borelCalculus_eq_integral` (SpectralTheorem.lean); agreement with `realCalculus`
  is the private `borelCalculus_eq_realCalculus` (SpectralTheorem.lean) and an inline bridge in
  `isBorelGenerating_F1Class`, whose continuous case uses `realCalculus_mul`;
  `F1Class_eq_bddMeasurable`, `F2Class_eq_bddMeasurable`.
- Blueprint: all five are in `\lean{}` (def:hall-8.6, def:F-class, def:hall-8.8,
  def:F1-F2-classes).
- Built; no new warnings (long line 723 and the keyword-led line 821 are pre-existing, outside
  the headline docstrings).

## Step A9: `Spectral/SpectralTheorem.lean` (2026-10-22)

- `spectralMeasure`, `functionalCalculus` (definitions) and the headline theorem
  `existsUnique_spectralMeasure` (3 docstrings).
- Checked: `spectralMeasure` is `if MeasurableSet E then borelCalculus hA (E.indicator 1) else 0`
  with fields from `isStarProjection_borelCalculus_indicator`, `borelCalculus_indicator_univ`,
  `hasSum_borelCalculus_indicator`, `borelCalculus_indicator_mul` (the prpstn:mua-* nodes);
  `spectralMeasure_integral_id`, `pvm_eq_of_integral_id_eq`, `borelCalculus_eq_integral`;
  `functionalCalculus` is `(spectralMeasure hA).integral f`. The physics examples (finite-
  dimensional eigenprojections, e^(itA)) are illustrations; the docstrings claim no lemma for
  them (e.g. no unitarity claim for e^(itA) in this file).
- Uncited (descriptive Blueprint line): `spectralMeasure` (thrm:hall-8.10 lists only
  `exists_spectralMeasure`).
- Built; no new warnings.

## Step A10: `Operators/LpDiagonal.lean` (2026-10-22)

- `lpDiag` (1 docstring; the only definition; the lemmas keep their short docstrings).
  Checked: built by `LinearMap.mkContinuous` with bound K (‖lpDiag T‖ ≤ K); `lpDiag_congr`
  (independent of K); the five algebra laws; used for direct sums (`GNS/DirectSum.lean`, family
  πᵢ(a)) and amplifications (`GNS/Amplification.lean`, constant family). Escaped `C\*-algebra`.
- Uncited: `lpDiag` is named in the text of def:finite-amplification
  (`haag-kastler-axioms.tex`) but in no `\lean{}`; descriptive Blueprint line.
- Built; no warnings.

## Step A11: final checks (2026-10-22)

- Full `lake build`: succeeds. Warnings in the 10 edited files are all pre-existing (`Try this`,
  `simp` notices, long lines in proofs); the long lines of each file are identical to HEAD.
- `lake lint`: passed. `python3 scripts/check_temporal_wording.py`: OK.
- Comments only: all 10 changed files, with `--` and nested `/- -/` comments removed (the
  guard's `strip_comments`) and whitespace normalised, are identical to HEAD.
- No added docstring line starts with a Lean keyword or exceeds 100 characters; no unescaped
  literal asterisk outside code spans (`\*-algebra`, `C\*-algebra` escaped). No `**Restriction:**`
  lines exist in these files.
- Guard: no edits blocked. `lean_guard.py check --base HEAD` reports only `.claude/CLAUDE.md`
  and `.claude/lean-policy.json`, which are untracked files present before this pass (not
  touched here).

## Totals

41 docstrings in 10 files: Basic 5, Spectrum 3, ContinuousCalculus 4 (+1 corrected sentence in
`existsUnique_assocMeasure`), Forms 7, BorelClasses 4, ProjectionValuedMeasure 8 (structure + 6
fields + `assoc`), OperatorIntegral 1, BorelCalculus 5, SpectralTheorem 3, LpDiagonal 1.

Errors corrected: `isCompact_spectrum` (closed and bounded are part (1) of prpstn:hall-7.5, not
parts (1) and (2)); `realCalculus`, `assocMeasure`, `existsUnique_assocMeasure` (called a proved
theorem "unproved" / uniqueness "left open").

## Blueprint proposals (for the lean-blueprint agent; the blueprint is not edited here)

Uncited declarations whose docstrings carry a descriptive Blueprint line:

1. `Physicslib4.Spectral.realCalculus`, `Physicslib4.Spectral.polyOn`: add to `\lean{}` of
   prpstn:hall-8.3 (the map and its polynomial inputs).
2. `Physicslib4.Spectral.assocFunctional`, `Physicslib4.Spectral.assocMeasure`: add to
   prpstn:associated-measures-self-adjoint (Λ_ψ and μ_ψ); `assocMeasure` could also go to
   def:hall-8.6, whose statement uses μ_ψ.
3. `Physicslib4.Spectral.ProjectionValuedMeasure.assoc`: add to
   thrm:projection-valued-measures-associated-measure.
4. `Physicslib4.Spectral.ProjectionValuedMeasure.integral`: add to
   thrm:operator-valued-integration.
5. `Physicslib4.Spectral.spectralMeasure`: add to thrm:hall-8.10 (and possibly
   thrm:spectral-theorem-for-bounded-operators).
6. `Physicslib4.Spectral.SesquilinearForm`: add to def:bounded-sesquilinear-form;
   `Physicslib4.Spectral.IsQuadraticForm`, `Physicslib4.Spectral.polarization`: add to
   def:bounded-quadratic-form.
7. `Physicslib4.Spectral.IsBoundedQuadraticForm.toSesq`: add to prpstn:hall-a.61;
   `Physicslib4.Spectral.IsBoundedQuadraticForm.toOperator`: add to prpstn:hall-a.63.
8. `Physicslib4.Spectral.IsMonotoneClass`: add to thrm:monotone-class-theorem;
   `Physicslib4.Spectral.IsBorelGenerating`: add to lmm:hall-prblm-8.3.3b.
9. `Physicslib4.Spectral.BddMeasurable`: add to def:hall-8.8 or thrm:operator-valued-integration
   (or a small definition node "bounded Borel functions");
   `Physicslib4.Spectral.BoundedPointwiseLimit`: add to thrm:bounded-convergence-theorem.
10. `Physicslib4.Spectral.mul_resolvent_of_mem_resolventSet`: add to
    def:bounded-operator-resolvent-and-spectrum (records the sign of Mathlib's `resolvent`).
11. `Physicslib4.lpDiag`: add to `\lean{}` of def:finite-amplification
    (`haag-kastler-axioms.tex`), which names it in its text.

Follow-ups outside this pass:
- `BorelClasses.lean` module docstring: says `IsBorelGenerating.indicator_mem` and
  `eq_bddMeasurable` need the compact metric Borel context; both `omit [CompactSpace X]`.
- `ContinuousCalculus.lean`, `realCalculus_properties` (theorem, not rewritten): "The four
  properties ... the five statements above"; the conjunction has five parts.

## Part B: the chapter `web/Manual/Spectral.lean` (2026-10-22)

### B1: header and Overview

- New chapter `web/Manual/Spectral.lean` (tag `spectral`, file `Bounded-spectral-theory`),
  included in `web/Manual.lean` right after the GNS chapter (the include order follows the
  section numbers of Chapter 10: 10.1, 10.2, 10.5, 10.6, 10.7–8).
- Imports `Physicslib4.Spectral.SpectralTheorem` (all of §10.2 transitively); opens
  `Physicslib4.Spectral` and the namespaces `ProjectionValuedMeasure`, `IsBoundedQuadraticForm`,
  `IsBorelGenerating` so that docstring code spans resolve.
- Overview: Hermitian-matrix reminder, the theorem as an integral, the seven stages, "every
  statement proved". Checked: no `sorry` or `axiom` in `Physicslib4/Spectral/*.lean`; all 144
  blueprint nodes of the section carry `\lean{}` and `\leanok` (the only exception is the
  convention conv:nonzero-hilbert-space, which has no Lean content). Example of continuous
  spectrum taken from the `spectrum_eq_compl_resolventSet` docstring (multiplication operator on
  L²([0, 1])), not the position operator (unbounded).
- Built: `lake build` and `generate-manual` succeed.

### B2: Design (about 1,130 words)

- Subsections: operators and the Hilbert space (Mathlib's `H →L[ℂ] H`, physics inner-product
  convention, no separability, `Nontrivial H` only where used); spectrum and resolvent (sign of
  Mathlib's resolvent set and `resolvent`; the real spectrum `spectrum ℝ A` from then on; λ as
  `fun l => ((l : ℝ) : ℂ)`); the continuous calculus is `cfcHom`; measures from RMK; operators
  from quadratic forms (one route for `borelCalculus` and `integral`; choices with value 0 off
  `BddMeasurable`, linearity a theorem); the monotone-class bootstrap (three uses: `FClass`,
  `F1Class`/`F2Class`, spectral-measure uniqueness in `pvm_integral_bddMeasurable_eq`); PVMs as a
  structure; two routes to f(A) and uniqueness.
- Links: blueprint def:inner-product, conv:nonzero-hilbert-space, prpstn:hall-8.3 (formalization
  note), prpstn:hall-a.63, def:projection-valued-measure. No internal memos.
- Checked: `tendsto_integral_of_boundedPointwiseLimit` is used in BorelCalculus (l. 318, 524,
  763) and SpectralTheorem (l. 838); OperatorIntegral uses Mathlib's dominated convergence
  directly; `generateFrom_subset_of_isMonotoneClass` is proved in the library;
  `IsBorelGenerating.eq_bddMeasurable` needs `MetricSpace`, `BorelSpace`, no `CompactSpace`;
  `pvm_integral_continuous_eq` uses `dense_polynomial_spectrum` (complex Stone–Weierstrass).
- Built.

### B3: Main definitions and theorems, first half

- Spectrum and resolvent: `#check mem_resolventSet_iff_isUnit_sub_smul`, `spectrum_subset_real`;
  links to `isCompact_spectrum`, `spectrum_nonempty`. Corrected own draft: the resolvent near z₀
  is a power series in z − z₀ (`exists_hasSum_resolvent`), not "a Neumann series".
- Continuous calculus: `{docstring realCalculus}`; `#check existsUnique_realCalculus`,
  `norm_realCalculus`; `realCalculus_properties` linked, not printed (five nested conjuncts).
- Associated measures: `{docstring assocMeasure}`; `#check existsUnique_assocMeasure`; RMK
  theorem linked.
- Forms: `{docstring}` for `BoundedSesquilinearForm`, `IsQuadraticForm`,
  `IsBoundedQuadraticForm`; `#check existsUnique_operator_of_isBoundedQuadraticForm`.
- #check outputs taken from `lake env lean` with `format.width 120` in a /tmp file; Verso
  accepts them. Built.

### B4: Main definitions and theorems, second half

- Bootstrap: `{docstring}` for `BddMeasurable`, `BoundedPointwiseLimit`, `IsBorelGenerating`;
  `#check IsBorelGenerating.eq_bddMeasurable`; `L0`, monotone class theorem linked.
- PVMs: `{docstring}` for `ProjectionValuedMeasure`, `.assoc`, `.integral`;
  `#check existsUnique_integral`, `integral_mul`; `norm_integral_le`, `integral_conj`,
  `existsUnique_assoc` linked.
- Borel calculus: `{docstring}` for `borelForm`, `borelCalculus`;
  `#check isBoundedQuadraticForm_borelForm`, `borelCalculus_mul`; `FClass`, `F1Class`, `F2Class`
  linked.
- Spectral theorem: `{docstring}` for `spectralMeasure`, `functionalCalculus`;
  `#check existsUnique_spectralMeasure`, `borelCalculus_eq_integral`.
- Built.

### B5: Where to look

- The nine top-level files with a representative `apiDocs` link each; `Unbounded/` and
  `Stone/` pointed to Sections 10.3 and 10.4; blueprint section and `sec10-2-spectral.html`.
  Checked: `home_page/sec10-2-spectral.md` exists; Basic.lean's module doc has the
  "Blueprint conventions that are literally Mathlib declarations" list.
- Built.

### B6: Main section expanded (prose was about 580 words)

- Added: the reality proof is Mathlib's `IsSelfAdjoint.spectrumRestricts`, with the blueprint's
  estimate `sq_norm_sub_smul_apply_le` linked; reading of `existsUnique_assocMeasure` and
  `assocMeasure_univ` (ENNReal); what must be proved of Q_f (prpstn:F-homogeneous to
  prpstn:F-bounded); reading of `existsUnique_integral` and the three-stage boundedness of Q_f;
  the preliminary 6 sup|f| bound (formalization note of prpstn:integral-norm-bound); the two
  bootstrap steps for multiplicativity (F1: all continuous real g; F2: all bounded Borel f);
  `exists_spectralMeasure` as the blueprint's form of existence.
- Built.

### B7: final checks and reread

- `lake build` and `generate-manual` succeed; `python3 scripts/check_temporal_wording.py`: OK.
- Links in `_out/manual/html-multi/Bounded-spectral-theory/index.html`: all 40-odd blueprint
  anchors exist in `blueprint/web/chptr-haag-kastler-axioms-blueprint.html`; every Physicslib4
  API-docs link points at an existing source file containing the name; `sec10-2-spectral` exists.
  The chapter has no cross-chapter `{ref}` links; the title page lists it second, after GNS.
- Reread fixes: Design intro no longer says every departure has a blueprint note; "in the order
  of the blueprint" removed from Where to look (the blueprint treats PVMs before Stage 1);
  long lines reflowed.
- Totals: prose about 2,810 words (Overview 517, Design 1,148, Main 841, Where to look 238,
  intro 67); 15 `{docstring}` boxes, 13 `#check` blocks.
- Doubts for the reviewer: (1) `cfcHom hA` in the `realCalculus` docstring renders unlinked (hA
  unbound in the chapter scope); (2) `web/README.md` Layout does not list `Manual/Spectral.lean`
  (outside this task's files); (3) Main follows the dependency order (spectrum, CFC, measures,
  forms, bootstrap, PVMs, Borel calculus, theorem), not the blueprint's (PVMs first);
  (4) `lpDiag` (docstring in A10) is §10.6 material and is not shown here.

## Part C: review fixes (`review-manual-ch-spectral-2026-10-22.md`)

### C1: group A (docstrings; comments only)

- A1/A2: `realCalculus` implementation note writes "Mathlib's continuous functional calculus
  `cfcHom` at the hypothesis `hA`, available because Mathlib makes `H →L[ℂ] H` a C\*-algebra"
  (module path dropped, C⋆ → C\*). A3: `assoc` writes `MeasureTheory.IsFiniteMeasure`;
  `MeasureTheory.VectorMeasure` left as plain code (memo allows). A4: "This project states only
  the right-inverse equation." A5: `functionalCalculus` "... transfer to it through that
  equation". A7: BorelClasses module docstring (two places) "the metric Borel context (no
  compactness)"; `realCalculus_properties` "The five properties".
- A6: count correction: the uncited declarations of the pass are 18 (the 17 `Spectral`
  declarations of the proposals list plus `lpDiag`), not 19 as in the commit message.
- Comments only: the 5 changed files, comments stripped, are identical to HEAD. No new line over
  100 characters, none starting with a Lean keyword; no guard blocks.
- `lake build`: succeeds, warning count of `Physicslib4.Spectral.SpectralTheorem` unchanged
  (56 before and after). `lake lint`: passed.
- Blueprint proposals of the memo: not applied (out of scope).

### C2: group B (chapter and README)

- B1: Overview bullet: only the boundedness of Q_f and the multiplicativity go through the
  monotone-class argument. B2: "Spectrum and resolvent" names Mathlib's `spectralRadius` and
  `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` (apiDocs links), with
  def:spectral-radius and thrm:gelfand-formula added to its Blueprint line (anchors exist).
- B3: `web/README.md` Layout lists the five published chapters in include order (GNS 10.1,
  Spectral 10.2, Spacetime 10.5, HaagKastler 10.6 without "(in preparation)", Curved
  10.7–10.8), checked against `web/Manual.lean` and the `#doc` titles.
- B4: "defined on all functions ... `f ∈ BddMeasurable _`". B5: apiDocs links for
  `isOpen_resolventSet`, `exists_hasSum_resolvent`, `realCalculus_polyOn`, `isSetAlgebra_L0`,
  `IsBorelGenerating.indicator_mem`, `IsBoundedQuadraticForm.isSelfAdjoint_toOperator`.
  B6: display formula split over two lines. B7: Main intro states that the subsections follow
  the order of the proof.
- Rendered page: `cfcHom` in the `realCalculus` box now links (`const-cfcHom`).
- `lake build`, `generate-manual`: succeed. `check_temporal_wording.py`: OK.
