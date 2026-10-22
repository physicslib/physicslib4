# Reference manual, chapter "Unbounded spectral theory": progress log

Part 1 of the docstring pass: headline definitions and structures (and their fields) of
`Physicslib4/Spectral/Unbounded/Basic.lean`, `Spectrum.lean` and `Integral.lean`. The remaining
files of `Spectral/Unbounded/` are for a later session. Appended after each file.

## Step 0: reconnaissance (2026-10-22)

- Read `.claude/CLAUDE.md`, `review-manual-ch-spectral-2026-10-22.md` and
  `manual-ch-spectral-progress.md` (format: one-sentence summary; mathematics for a first-year
  theoretical-physics PhD student; "Implementation note:" last before a plain-text
  "Blueprint: <label>", descriptive for uncited declarations; multi-character subscripts in
  parentheses; literal asterisks escaped as `\*`; no docstring line starting with a Lean
  keyword; present tense).
- Blueprint: `blueprint/src/sections/sec10/unbounded-spectral-theorems.tex` (labels and
  `\lean{}` lists by grep).
- Checks per file: added lines ≤ 100 characters, no keyword-initial lines, no unescaped
  asterisks outside code spans (script `/tmp/dscheck/check.py`); comments-only, by comparing the
  file with `--` and `/- -/` comments stripped and whitespace normalised against `HEAD`
  (`/tmp/dscheck/strip.py`).

## Step 1: `Spectral/Unbounded/Basic.lean` (2026-10-22)

- Rewritten (8 docstrings, plus the 3 field docstrings of `IsEssentiallySelfAdjoint`):
  `HasDenseDomain`, `existsUnique_adjoint_apply` (stands in for Mathlib's `LinearPMap.adjoint`),
  `IsSymmetric` (also explains self-adjointness, which is Mathlib's `IsSelfAdjoint`, `T† = T`),
  `IsPositive`, `isClosed_iff_forall_tendsto` (stands in for Mathlib's `IsClosed`, `IsClosable`,
  `closure`), `IsEssentiallySelfAdjoint`, `ker`, `range`, `subSmul`. Other theorems left alone.
- Checked: Mathlib's `adjoint` has domain `adjointDomain` (continuity of ψ ↦ ⟨φ, Tψ⟩) and
  `toFun := if dense then adjointAux else 0`; `IsSelfAdjoint.dense_domain` is a root-namespace
  Mathlib lemma; `isSelfAdjoint_def : IsSelfAdjoint A ↔ A† = A`; `IsPositive` is used by
  `Physicslib4.AQFT.IsPositiveEnergy.isPositive_generator`; `isEssentiallySelfAdjoint_iff_dense_range`
  needs `HasDenseDomain` (stated "densely defined"); T + i𝟙 is `subSmul T (-Complex.I)`.
- No errors in the old headline docstrings. Found outside scope (helper theorem, left for the
  later session): `adjoint_le_adjoint_of_le` says "Mathlib's `LinearPMap.adjoint` is `0` on all
  of `H` when the domain is not dense". The domain of `T†` is `T.adjointDomain` in every case;
  only the action is 0. Suggested: "is the zero map on its domain when the domain of the
  operator is not dense".
- Uncited (descriptive Blueprint line): `subSmul` ("the convention for A − λ𝟙 stated after
  def:hall-3.1").
- Built: no new warnings (only the pre-existing module-system notices for this file); checks
  clean; comments-only confirmed.

## Step 2: `Spectral/Unbounded/Spectrum.lean` (2026-10-22)

- Rewritten (5 docstrings, plus the 3 field docstrings of `IsResolvent`): `IsResolvent`,
  `pmapResolventSet`, `pmapSpectrum`, and the two main statements `pmapSpectrum_subset_real`,
  `isEssentiallySelfAdjoint_iff_dense_range`. Helper theorems left alone.
- Checked: Mathlib's `LinearPMap` has no `Mul`/ring instance (so "no ring structure" holds);
  `pmapResolventSet_toPMap_top` uses −B (sign convention of Mathlib's resolvent λ𝟙 − A);
  `mem_pmapResolventSet_of_im_ne_zero` states only membership, so the 1/|Im λ| bound is credited
  to its proof, not its statement; `orthogonal_range_subSmul` gives
  Range(T − λ𝟙)ᗮ = Ker(T\* − λ̄𝟙), so the ±i pairing in the essential self-adjointness criterion is
  Range(T ∓ i𝟙)ᗮ = Ker(T\* ± i𝟙).
- Corrected: `pmapSpectrum_subset_real` cited `LinearPMap.IsSelfAdjoint.dense_domain`; the
  Mathlib lemma is `_root_.IsSelfAdjoint.dense_domain` (written `IsSelfAdjoint.dense_domain`).
- Uncited: none (all three definitions are in def:hall-9.16).
- Built: no warnings for this file; checks clean; comments-only confirmed.

## Step 3: `Spectral/Unbounded/Integral.lean` (2026-10-22)

- Rewritten (9 docstrings, plus the 4 field docstrings of `IsQuadraticFormOn` and
  `IsBoundedQuadraticFormOn`): `SesquilinearFormOn`, `polarizationOn`, `IsQuadraticFormOn`,
  `IsBoundedQuadraticFormOn`, `integralDomain`, `integralForm`, `integralApply` (keeps the
  measurability guard and the junk value 0, now with a Blueprint line), `pmapIntegral`, and the
  main statement `isSelfAdjoint_pmapIntegral_of_real`. Helper lemmas left alone.
- Corrected: the module docstring listed `IsSesquilinearFormOn`; the declaration is
  `SesquilinearFormOn` (a type abbreviation, not a predicate). `integralApply` had no Blueprint
  line; it is cited by prpstn:hall-10.1.
- Checked: `integralDomain` is `MemLp f 2 (μ.assoc ψ)`, which includes a.e. strong
  measurability (stated); `assoc_add_le` (μ_(φ+ψ) ≤ 2(μ_φ + μ_ψ)) and `assoc_smul` give the
  submodule structure; `IsBoundedQuadraticForm.toOperator` exists in `Spectral/Forms.lean`;
  `existsUnique_spectralMeasure_unbounded` (Cayley.lean) is `pmapIntegral μ (fun x => x) = A`
  and `functionalCalculus` is `pmapIntegral (spectralMeasure hA) f`; no `sorry` in
  `Spectral/Unbounded/`; `pmapIntegral_sub_smul_integral_inv` uses ∫ (f − c)⁻¹ dμ as a right
  inverse. Every theorem about the values of `pmapIntegral` assumes `Measurable f` or
  `BddMeasurable` (`pmapIntegral_domain` is about the domain only).
- Did not claim Q_f is unbounded for unbounded f (false when f is unbounded only on a null set):
  "in general not bounded".
- Uncited: none (all nine are in `\lean{}` lists: def:hall-sesquilinear-form-on-a-subspace,
  def:hall-quadratic-form-on-a-subspace, prpstn:hall-10.2, prpstn:hall-10.1, prpstn:hall-10.3).
- Built: no warnings for this file beyond the pre-existing module-system notice; checks clean
  (the one asterisk hit is a module-docstring bullet); comments-only confirmed.

## Step 4: final checks (2026-10-22)

- `lake build`: succeeds, 0 errors; the only warnings in the three files are the module-system
  import notices, which `HEAD` also has (imports unchanged). `lake lint`: passed.
  `python3 scripts/check_temporal_wording.py`: OK.
- Comments-only: all three files identical to `HEAD` with comments stripped and whitespace
  normalised. No declaration was blocked by the lean-kit guard. No `**Restriction:**` lines
  were present or needed.
- Totals: Basic 8 + 3 fields, Spectrum 5 + 3 fields, Integral 9 + 4 fields (and one module-doc
  name fix).

## Blueprint proposals (for the lean-blueprint agent)

| Declaration | Proposed `\lean{}` node | Note |
|---|---|---|
| `Physicslib4.Spectral.Unbounded.subSmul` | def:hall-3.1 | The A − λ𝟙 convention is the paragraph right after def:hall-3.1; alternatively a new definition node for it. |

All other declarations whose docstrings were rewritten are already cited.

## For the later session

- `adjoint_le_adjoint_of_le` (Basic.lean): fix the claim that Mathlib's adjoint "is `0` on all
  of `H`" for non-dense domains (see Step 1).
