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

# Part 2

Headline definitions and structures (and their fields), plus the main statements, of
`Normal.lean`, `DirectSum.lean`, `AbstractCalculus.lean`, `Cayley.lean` and
`FunctionalCalculus.lean` (the directory has no other file outside part 1). Same format and
checks as part 1 (`/tmp/dscheck/check.py`, `/tmp/dscheck/strip.py`).

## Step 5: `adjoint_le_adjoint_of_le` (Basic.lean) (2026-10-22)

- Corrected the flagged claim: Mathlib's `LinearPMap.adjoint` "is the zero map on its domain
  when the domain of the operator is not dense" (its domain is `adjointDomain` in every case),
  and the conclusion would say that `C₁†` is the zero map on its domain. Comments-only confirmed.

## Step 6: `Spectral/Unbounded/Normal.lean` (2026-10-22)

- Rewritten (9 docstrings, plus the 2 field docstrings of `IsAlmostEigenvector`): `mvApply`,
  `mvEvalConj`, `spectralSubspace`, `pvmOperator`, `IsAlmostEigenvector`, `spectrum_mvApply`,
  `mvPolyOn`, `normalCalculus`, `existsUnique_normalCalculus`. Helper lemmas left alone.
- Checked: `isStarNormal_mvApply`, `commute_mvApply` (four commutations) exist and assume
  `IsStarNormal`; no lemma states multiplicativity of `mvApply` itself, so none is claimed;
  `spectrum_mvApply` and `existsUnique_normalCalculus` have no `Nontrivial H` (blueprint has
  H ≠ {0}; stated "not needed"); `ContinuousMap.elemental_id_eq_top` is in Mathlib's
  `StoneWeierstrass`; `IsAlmostEigenvector` has no ε > 0 condition (stated).
- Corrected: `normalCalculus` wrote "C⋆-algebra" and cited a module path; now "C\*-algebra" and
  "Mathlib makes `H →L[ℂ] H` a C\*-algebra" (review A1/A2 pattern). `mvEvalConj` and
  `mvPolyOn` had no Blueprint line.
- Uncited: none (`mvEvalConj` is in lmm:polynomials-in-normal-are-normal, `mvPolyOn` in
  thrm:continuous-functional-calculus-normal).
- Built: no warnings for this file beyond the module-system notices; checks clean;
  comments-only confirmed.

## Step 7: `Spectral/Unbounded/DirectSum.lean` (2026-10-22)

- Rewritten (8 docstrings, plus the 9 field docstrings of `IsInternalOrthogonalDecomposition`,
  `IsDirectSumOperator` and `IsInternalDirectSumOperator`): those three structures,
  `directSumDomain`, `internalDomain`, and the main statements
  `isHilbertSum_of_isInternalOrthogonalDecomposition`,
  `isEssentiallySelfAdjoint_of_isDirectSumOperator`,
  `isEssentiallySelfAdjoint_of_isInternalDirectSumOperator` (its `CompleteSpace (K n)` remark
  kept, as the implementation note). Other theorems left alone, including the four with the same
  remark.
- Checked: the external index type is arbitrary (blueprint: sequences), stated; the internal
  one is ℕ; `internalDomain` asks for some convergent decomposition (unique by
  `hasSum_injective_of_isInternalOrthogonalDecomposition`); the surjectivity of Aᵢ − c𝟙 for
  non-real c comes from `IsSelfAdjoint.mem_spectrum_eq_re` (real spectrum), as stated. No Lean
  declaration outside this file uses `IsDirectSumOperator` or `IsInternalDirectSumOperator`
  (the blueprint's proofs of prpstn:hall-10.3 and thrm:hall-10.30 do; the Lean proofs take
  other routes), so the docstring says "the form in which the blueprint applies it".
- Corrected: none of substance; the old docstrings had no errors.
- Uncited: none.
- Built: no warnings for this file beyond the module-system notices; checks clean;
  comments-only confirmed.

## Step 8: `Spectral/Unbounded/AbstractCalculus.lean` (2026-10-22)

- Rewritten (8 docstrings, plus the 5 field docstrings of `IsAbstractCalculus`): `ofRealCM`,
  `IsAbstractCalculus`, `existsUnique_abstractMeasure`, `abstractMeasure`, `abstractForm`,
  `extendedCalculus` (keeps the junk value 0 off `BddMeasurable`), `abstractPVM`, and the main
  statement `existsUnique_spectralMeasure_normal`. Helper lemmas left alone.
- Checked: Riesz–Markov is `RealRMK.rieszMeasure`, uniqueness
  `Measure.ext_of_integral_eq_on_compactlySupported`; projections via
  `extendedCalculus_indicator_inter` (idempotent) and `isSelfAdjoint_extendedCalculus_of_real`;
  countable additivity through the convergence principle (`tendsto_inner_extendedCalculus`),
  not monotone convergence (a first draft said the latter; corrected before the build);
  `abstractPVM` is 0 on non-measurable sets because `extendedCalculus` is 0 off
  `BddMeasurable`; `extendedCalculus_smul_add`, `_mul`, `_conj`, `_continuous`,
  `abstractForm_continuous`, `abstractPVM_assoc`, `abstractMeasure_univ` exist.
- Corrected: `existsUnique_spectralMeasure_normal` said "on a nonzero Hilbert space"; the
  statement has no `Nontrivial H` (now stated: the blueprint's H ≠ {0} is not needed).
  `ofRealCM` had no Blueprint line (it is cited by lmm:abstract-calculus-non-negative).
- Uncited: none.
- Built: no warnings for this file beyond the module-system notices; checks clean;
  comments-only confirmed.

## Step 9: `Spectral/Unbounded/Cayley.lean` (2026-10-22)

- Rewritten (11 docstrings, plus the 2 field docstrings of `IsCayleyTransform`):
  `unitCircleMinusOne`, `cayleyMap`, `cayleyInv`, `IsCayleyTransform`,
  `exists_isCayleyTransform`, `mem_spectrum_iff_cayleyMap_mem_spectrum`, `restrictPVM`,
  `mapPVM`, `cayleyPVM`, `pushforwardPVM`, and the main statement
  `existsUnique_spectralMeasure_unbounded`. Helper lemmas left alone.
- Checked: `cayleyInv` is the real part of i(u + 1)/(u − 1) (0 at u = 1 by division by zero);
  `IsCayleyTransform.unitary_eq` gives U determined by A alone (B, B' arbitrary); `restrictPVM`
  and `mapPVM` are used by no Lean proof (stated: `cayleyPVM` composes with D directly);
  `mapPVM`'s inverse-measurability hypothesis is used only for the non-measurable-set field
  (stated); `pushforwardPVM` is used in `eq_cayleyPVM_of_pmapIntegral_eq`, pushing a second
  spectral measure of A to the unit circle for `eq_of_integral_id_eq_ambient`;
  `existsUnique_spectralMeasure_unbounded` treats H = {0} by `subsingleton_or_nontrivial`;
  the domain statement follows from equality of `LinearPMap`s and `integralDomain` being
  `MemLp f 2`.
- Corrected: none of substance. `unitCircleMinusOne` had no Blueprint line (it is cited by
  lmm:cayley-map).
- Uncited: `pushforwardPVM` (descriptive line "the change of variables in the uniqueness proof
  of thrm:hall-10.4 (Step 3)").
- Built: no warnings for this file beyond the module-system notices (one long line caught by
  the build and fixed); checks clean; comments-only confirmed.

## Step 10: `Spectral/Unbounded/FunctionalCalculus.lean` (2026-10-22)

- Rewritten (3 docstrings): `spectralMeasure`, `functionalCalculus`, and the main statement
  `functionalCalculus_of_bddMeasurable`. The other four theorems left alone.
- Checked: `Stone.expUnitary` is built from `(Unbounded.spectralMeasure hA).integral (expFun t)`
  (so "the unitary group of Stone's theorem is of this kind" holds); the bounded-integral
  lemmas cited (`ProjectionValuedMeasure.integral_mul`, `integral_conj`, `norm_integral_le`)
  exist in `Spectral/OperatorIntegral.lean`; the blueprint's third remark (f(A) depends only on
  f on σ(A)) has no Lean statement, so it is not claimed. Review A5's wording ("transfer to it
  through this definition") used for `functionalCalculus`.
- Corrected: none.
- Uncited: none.
- Built: no warnings for this file beyond the module-system notices; checks clean;
  comments-only confirmed.

## Step 11: final checks, part 2 (2026-10-22)

- `lake build`: succeeds, 0 errors; the non-module-system warnings are the same 54 as part 1's
  baseline (none in `Spectral/Unbounded/`). `lake lint`: passed.
  `python3 scripts/check_temporal_wording.py`: OK.
- Comments-only: all eight files of `Spectral/Unbounded/` identical to `HEAD` with comments
  stripped and whitespace normalised. No declaration was blocked by the lean-kit guard. No
  `**Restriction:**` lines were present or needed.
- Totals (part 2): Normal 9 + 2 fields, DirectSum 8 + 9 fields, AbstractCalculus 8 + 5 fields,
  Cayley 11 + 2 fields, FunctionalCalculus 3; Basic: one claim corrected in
  `adjoint_le_adjoint_of_le`.

## Blueprint proposals, part 2 (for the lean-blueprint agent)

| Declaration | Proposed `\lean{}` node | Note |
|---|---|---|
| `Physicslib4.Spectral.Unbounded.pushforwardPVM` | thrm:hall-10.4 | Used in Step 3 of the uniqueness proof (`eq_cayleyPVM_of_pmapIntegral_eq`); alternatively next to `mapPVM` in lmm:borel-bijection-transports-pvm as a non-bijective variant. |

The part 1 proposal (`subSmul`) stands. Every other declaration whose docstring was rewritten
in part 2 is already cited.
