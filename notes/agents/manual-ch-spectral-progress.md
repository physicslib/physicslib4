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
