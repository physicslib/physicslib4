# Reference manual, chapter "Stone's theorem": progress log

Part 1 of the docstring pass: headline definitions and structures (and their fields), plus the
headline statements, of `Physicslib4/Spectral/Stone/` (Basic, Bounded, Exponential, Density,
Theorem). Files outside the directory (`AQFT/PositiveEnergy.lean`, `Operators/Conjugation.lean`,
`Analysis/StrongContinuity.lean`) are for a later session. Appended after each file.

## Step 0: reconnaissance (2026-10-23)

- Read `.claude/CLAUDE.md`, `review-manual-ch-unbounded-2026-10-23.md` and
  `manual-ch-unbounded-progress.md` (format: one-sentence summary; mathematics for a first-year
  theoretical-physics PhD student; "Implementation note:" paragraph last before a plain-text
  "Blueprint: <label>", descriptive for uncited declarations; multi-character sub- and
  superscripts in parentheses, e.g. A^(cl); literal asterisks escaped as `\*`; no docstring line
  starting with a Lean keyword; present tense).
- Blueprint: `blueprint/src/sections/sec10/stones-theorem.tex`.
- Checks per file: `/tmp/dscheck/check.py` (added lines ≤ 100 characters, no keyword-initial
  lines, no unescaped asterisks outside code spans) and `/tmp/dscheck/strip.py` (comments-only
  against `HEAD`, comments stripped and whitespace normalised).
- Baseline: `lake build` at `HEAD` gives 210 warnings; the only ones in `Spectral/Stone/` are
  module-system import notices.

## Step 1: `Spectral/Stone/Basic.lean` (2026-10-23)

- Rewritten (5 docstrings, plus the 2 field docstrings of `IsOneParameterUnitaryGroup`):
  `IsOneParameterUnitaryGroup`, `IsStronglyContinuous`, `generatorQuotient`, `generatorDomain`,
  `generator`. Helper lemmas (including the symmetry, orbit and conjugation lemmas) left alone.
- Checked: unitaries are `H ≃ₗᵢ[ℂ] H`; the two fields are stated vector by vector;
  `IsStronglyContinuous` is defined for any family; `adjoint_eq` gives U(t)\* = U(−t);
  `isStronglyContinuous_iff_tendsto_zero` assumes the group law; `generatorQuotient` is
  `(I * t)⁻¹ • (U t ψ - ψ)` (0 at t = 0 by 0⁻¹ = 0); `generator` uses `limUnder (𝓝[≠] 0)` and
  assumes nothing about U; `generator_expUnitary` gives e^(itA) generator A (so the sign
  convention, and e^(−itĤ) has generator −Ĥ). The translation/momentum example (domain H¹,
  strong but not norm continuity) is background, attached to no library name.
- Corrected: none of substance (old docstrings accurate; they cited a blueprint label for
  density, now the Lean name `hasDenseDomain_generator`).
- Uncited: none (all in def:hall-10.11, def:hall-10.13).
- Built: no warnings for this file beyond the module-system notices; checks clean (after
  reflowing three keyword-initial lines: "by", "for", "in"); comments-only confirmed.

## Step 2: `Spectral/Stone/Bounded.lean` (2026-10-23)

- Rewritten (2 docstrings): the file's headline results `exists_isOneParameterUnitaryGroup_exp`
  and `generator_eq_of_eq_exp` (the bounded case of the correspondence). The file has no
  definitions; `hasDerivAt_exp_smul_I` and `isStronglyContinuous_of_eq_exp` left alone.
- Checked: the exponential is `NormedSpace.exp (((t : ℂ) * I) • P)`; unitarity via
  `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint` and `Unitary.linearIsometryEquiv`; group law
  via `exp_add_of_commute`; `generator_eq_of_eq_exp` has no hypothesis on P and concludes
  `generator V = (P : H →ₗ[ℂ] H).toPMap ⊤` (existing remark kept as the implementation note).
- Corrected: none.
- Uncited: none (lmm:exp-bounded-unitary-group, lmm:generator-exp-bounded).
- Built: no warnings for this file; checks clean (one "theorem"-initial line reflowed);
  comments-only confirmed.

## Step 3: `Spectral/Stone/Exponential.lean` (2026-10-23)

- Rewritten (4 docstrings): `expFun`, `expUnitary`, `functionalCalculus_expFun` (the third
  name in def:exp-unitary-group's `\lean{}` list) and the headline statement
  `generator_expUnitary`. Lemmas on the group law, strong continuity, the norm identity and the
  derivative at 0 left alone.
- Checked: `expUnitary` is `Unitary.linearIsometryEquiv` of
  `(Unbounded.spectralMeasure hA).integral (expFun t)` and takes the proof `hA` (hence the
  existential in `stone`); notation μ(A) follows `Unbounded.spectralMeasure`'s docstring;
  `functionalCalculus_expFun` is `(functionalCalculus_of_bddMeasurable ..).2`, an equality of
  `LinearPMap`s with domain ⊤; `generator_expUnitary` is proved by
  `eq_of_isSelfAdjoint_of_isSymmetric_of_le` with `isSymmetric_generator`; strong continuity and
  `tendsto_generatorQuotient_expUnitary` go through the private `tendsto_integral_norm_sub_sq`,
  which is `tendsto_integral_filter_of_dominated_convergence` (filter DCT note added to the
  implementation note). e^(−itĤ) is `expUnitary` at −t by the definition of `expFun`.
- Corrected: none.
- Uncited: none (def:exp-unitary-group, prpstn:hall-10.14).
- Built: no warnings for this file beyond the module-system notice; checks clean (one
  "theorem"-initial line reflowed); comments-only confirmed.

## Step 4: `Spectral/Stone/Density.lean` (2026-10-23)

- Rewritten (2 docstrings): the definition `average` and the headline statement
  `hasDenseDomain_generator`. `average_eq_convolution`, `average_mem_generator_domain`,
  `tendsto_average_bump` left alone.
- Checked: Mathlib's `integral` is `if CompleteSpace G then (if Integrable .. else 0) else 0`
  (stated); `average_eq_convolution` assumes only the group law (stated "holds for every f");
  `average_mem_generator_domain` assumes strong continuity, `ContDiff ℝ 1 f` and compact support;
  `tendsto_average_bump` and `hasDenseDomain_generator` assume `CompleteSpace H`; the bumps are
  `⟨1 / (2 * (n + 1)), 1 / (n + 1), ..⟩` (the blueprint's f_n reindexed from 0);
  `ker_adjoint_generator_subSmul_eq_bot` and `isEssentiallySelfAdjoint_generator` use the
  density. Convolution route kept in the implementation notes. The Gårding remark is
  background, attached to no library name.
- Corrected: none (the old `hasDenseDomain_generator` docstring cited `def:hall-3.1` in
  backticks; now the Lean name `Unbounded.HasDenseDomain`).
- Uncited: none (lmm:averaging-translate, lmm:hall-10.18).
- Built: no warnings for this file; checks clean; comments-only confirmed.

## Step 5: `Spectral/Stone/Theorem.lean` (2026-10-23)

- Rewritten (1 docstring): `stone`. The lemmas of the proof (ODE along orbits, deficiency
  subspaces, essential self-adjointness, orbit difference, agreement on a dense subspace) left
  alone.
- Checked: the statement is `∃ hA : IsSelfAdjoint (generator U), HasDenseDomain (generator U) ∧
  (∀ t, U t = expUnitary hA t) ∧ ∀ B hB, (∀ t, U t = expUnitary hB t) → B = generator U`, with
  only `CompleteSpace H` (no separability, no nontriviality); the proof route (essential
  self-adjointness via `ker_adjoint_generator_subSmul_eq_bot`, `orbit_eq_expUnitary_closure`
  via `eq_zero_of_hasDerivAt_of_isSymmetric`, `eq_of_eqOn_dense`, then
  `generator_expUnitary` for the closure) matches the module docstring and the code. The
  physics paragraph (Hamiltonian, momentum, angular momentum) is background, attached to no
  library name.
- Corrected: none.
- Uncited: none (thrm:hall-10.15).
- Built: no warnings for this file; checks clean (one "with"-initial line reflowed);
  comments-only confirmed.

## Step 6: final checks (2026-10-23)

- `lake build`: succeeds; 210 warnings, identical (modulo line numbers) to the `HEAD` baseline,
  so no new warnings. `lake lint`: passed. `python3 scripts/check_temporal_wording.py`: OK.
- Comments-only: all five files identical to `HEAD` with comments stripped and whitespace
  normalised. No edit was blocked by the lean-kit guard. No `**Restriction:**` lines were
  present or needed.
- Totals: Basic 5 + 2 fields, Bounded 2, Exponential 4, Density 2, Theorem 1.

## Blueprint proposals (for the lean-blueprint agent)

None: every declaration whose docstring was rewritten is already in a `\lean{}` list
(def:hall-10.11, def:hall-10.13, lmm:exp-bounded-unitary-group, lmm:generator-exp-bounded,
def:exp-unitary-group, prpstn:hall-10.14, lmm:averaging-translate, lmm:hall-10.18,
thrm:hall-10.15).

## For the later session

- `AQFT/PositiveEnergy.lean`, `Operators/Conjugation.lean`, `Analysis/StrongContinuity.lean`.
- Helper docstrings in `Spectral/Stone/` still use the older "Blueprint reference: `label`."
  form with backticks; the module docstrings cite labels in backticks too (left alone, as
  outside the headline scope).
