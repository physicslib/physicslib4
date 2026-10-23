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

# Part 2: files outside `Spectral/Stone/`

## Step 7: `AQFT/PositiveEnergy.lean` (2026-10-23)

- Rewritten (7 docstrings): `IsPositiveEnergy`, `isPositiveEnergy_const_refl`,
  `generator_eq_of_eq_expUnitary`, `IsPositiveEnergy.conj`, `IsPositiveEnergy.strongContinuous`,
  `isPositiveEnergy_exp`, `isPositiveEnergy_iff_exists_exp`. The three field docstrings of
  `IsPositiveEnergy` already met the format and are unchanged; `exp_generator_unique` (supporting
  lemma) and the module docstring left alone.
- Checked: the generator is unbounded (`generator V : H →ₗ.[ℂ] H`), no bounded-generator
  restriction anywhere, no `**Restriction:**` line needed; `IsPositive` is symmetry plus
  0 ≤ Re⟨ψ, Aψ⟩; `generator_refl` gives generator 0 on ⊤; `IsPositiveEnergy.conj` states only
  the positive-energy conclusion (the form W A W⁻¹ on W Dom(A) is `mem_generator_conj_domain_iff`
  and `generator_conj_apply`, used in the proof), so the docstring now says so;
  `isPositiveEnergy_exp` takes Mathlib's `ContinuousLinearMap.IsPositive` and a pointwise
  hypothesis, proof via `exists_isOneParameterUnitaryGroup_exp`, `isStronglyContinuous_of_eq_exp`,
  `generator_eq_of_eq_exp`, `isPositive_toPMap_iff`; the iff goes through `stone` and
  `generator_expUnitary`. `omit [CompleteSpace H]` on const, conj and strongContinuous (stated).
  Vacuum/generator links: `HaagKastlerNet.IsVacuumState` (t ↦ U(γ(t)) for every
  future-timelike translation γ) and `HaagKastlerNet.IsGroundStateForFlow` (Minkowski
  `QuasilocalKMS.lean`, curved `StabilizerKMS.lean`) both use `IsPositiveEnergy`; the latter's
  `exists_strongContinuous_unitary` uses `IsPositiveEnergy.strongContinuous`.
- Corrected: `IsPositiveEnergy.conj` claimed "with generator W A W⁻¹ on W · Dom(A)" as if part
  of the statement (now attributed to the two Stone lemmas). TeX-style e^{itA} replaced by
  e^(itA). No mathematical errors otherwise.
- Uncited: none (def:positive-energy, lmm:positive-energy-const, lmm:exp-generator-unique,
  lmm:positive-energy-conj, lmm:positive-energy-strong-continuous,
  lmm:positive-energy-exp-bounded, thrm:positive-energy-iff-exp).
- Built: only the module-system import notices; checks clean (one "for"-initial line and one
  long line reflowed); comments-only confirmed.

## Step 8: `Operators/Conjugation.lean` (2026-10-23)

- Rewritten (11 docstrings): `Units.conjMulEquiv`, `MulEquiv.image_centralizer`,
  `MulEquiv.image_centralizer_centralizer`, `lieConj`, `exp_lieConj`, `scalarOperators`,
  `IsFactor`, `IsFactor.conj`, `lieConj_apply_eq_conjStarAlgEquiv`, `norm_lieConj`,
  `restrictStarAlgEquiv`. Helpers left alone: `conjMulEquiv_apply`, `lieConj_apply`,
  `lieConj_smul`, `lieConj_one`, `lieConj_add`, `lieConj_star`, `lieConj_image_scalarOperators`;
  module docstring left alone.
- Checked: `lieConj` is `Units.conjMulEquiv` of `Uop.toContinuousLinearEquiv.toUnit` (only a
  `MulEquiv`); `exp_lieConj` is `NormedSpace.exp_units_conj` and needs `CompleteSpace H`;
  `IsFactor R` is `R ∩ Set.centralizer R = scalarOperators H` for any set R (so a factor contains
  1); `IsFactor.conj` is used by both `localVonNeumann_isFactor_smul`;
  `image_centralizer_centralizer` and `lieConj_apply_eq_conjStarAlgEquiv` by both
  `GeometricCovariance.lean` files; `restrictStarAlgEquiv` by both `localVonNeumannEquiv`
  (R(B) ≃⋆ₐ R(L·B)); `isFactor_of_isIrreducibleInclusion` exists. `omit [CompleteSpace H]` on
  `IsFactor.conj` and `norm_lieConj` (stated). Schur's lemma and the central-projection
  characterisation of factors are background, attached to no library name.
- Corrected: `IsFactor` and `IsFactor.conj` called R "a von Neumann algebra"; the definition
  takes any set of operators (now said). `restrictStarAlgEquiv` said e "carries S onto T"; the
  hypotheses are the two inclusions e(S) ⊆ T and e⁻¹(T) ⊆ S (now stated). "Our bare-monoid
  conjugation" (first person) removed.
- Uncited (all 11): see the blueprint proposals at the end of this log.
- Built: only the module-system notices and the pre-existing `Try this` at `exp_lieConj`'s
  `simp only` (in the `HEAD` baseline); checks clean (three keyword-initial lines reflowed);
  comments-only confirmed.

## Step 9: `Analysis/StrongContinuity.lean` (2026-10-23)

- Rewritten (1 docstring): `strongContinuous_of_weak`, the file's only declaration. The module
  docstring and the step comments in the proof left alone.
- Checked: X is any topological space, U any family `X → (H ≃ₗᵢ[ℂ] H)` (no group law), H not
  assumed complete; the hypothesis is continuity of `⟪ξ, U x η⟫` for ξ, η ∈ D with D dense; the
  three proof steps and the polarization identity match the code and the blueprint proof; the
  user is `GNS.exists_gns_unitary_of_invariant_strongContinuous` (dense set π(a)Ω, matrix
  coefficients ω(a\* γ_g(b))).
- Corrected: none (old docstring accurate, but not in the format and without a Blueprint line).
- Uncited: none (lmm:weak-continuity-implies-strong).
- Built: only the module-system notices; checks clean (two keyword-initial lines reflowed);
  comments-only confirmed.

## Step 10: final checks, part 2 (2026-10-23)

- `lake build`: succeeds; 210 warnings, identical (modulo line numbers) to the part-1 result, so
  no new warnings. `lake lint`: passed. `python3 scripts/check_temporal_wording.py`: OK.
- Comments-only: the three files identical to `HEAD` with comments stripped and whitespace
  normalised. No edit was blocked by the lean-kit guard. No `**Restriction:**` lines were present
  or needed (positive energy uses the unbounded generator throughout).
- Totals: PositiveEnergy 7, Conjugation 11, StrongContinuity 1.

## Blueprint proposals, part 2 (for the lean-blueprint agent)

None of `Operators/Conjugation.lean` is in a `\lean{}` list. Proposed homes (all in
`haag-kastler-axioms.tex`, near thrm:von-neumann-geometric-covariance; the curved chapter could
reference them):
- `Units.conjMulEquiv`, `Physicslib4.lieConj`, `Physicslib4.lieConj_apply_eq_conjStarAlgEquiv`,
  `Physicslib4.norm_lieConj`, `Physicslib4.exp_lieConj`: a definition node
  "Conjugation by a unitary" (T ↦ U T U⁻¹ as an automorphism of B(H), a `*`-automorphism,
  isometric, commuting with exp).
- `MulEquiv.image_centralizer`, `MulEquiv.image_centralizer_centralizer`: a lemma node
  "Automorphisms preserve commutants and bicommutants", the "reusable core" already described in
  prose in the proof of thrm:von-neumann-geometric-covariance; add it to that proof's `\uses{}`.
- `Physicslib4.scalarOperators`, `Physicslib4.IsFactor`: a definition node "Factor" (center
  R ∩ R' = ℂ𝟙), currently defined only inline in the statement of thrm:von-neumann-factor-orbit
  and used by thrm:irreducible-inclusion-factor and thrm:self-inclusion-factor.
- `Physicslib4.IsFactor.conj`: a lemma node "Unitary conjugation preserves factors", used by the
  proof of thrm:von-neumann-factor-orbit.
- `Physicslib4.restrictStarAlgEquiv`: a lemma node "Restriction of a `*`-automorphism", used
  for the bundled equivalence R(B) ≃ R(L·B) (`localVonNeumannEquiv`).
Each docstring carries a descriptive "Blueprint: uncited (...)" line until then.

# Part 3: the chapter `web/Manual/Stone.lean`, part 1 (header, intro, Overview, Design)

## Step 11: reconnaissance (2026-10-23)

- Read `.claude/CLAUDE.md`, the plan (chapter 4, per-chapter pattern), `web/README.md`,
  `Manual/Unbounded.lean` and `Manual/Spectral.lean` (header, tags, link style),
  `review-manual-ch-unbounded-2026-10-23.md` (no unbacked claims; do not promise formalization
  notes that do not exist), this log, `stones-theorem.tex`, and the positive-energy and
  weak-continuity entries of `haag-kastler-axioms.tex` (§10.6, l. 1898 and l. 1979–2100).
- Facts for the chapter: `stones-theorem.tex` has no "Formalization note" paragraph; its Lean
  remarks are inside entries (def:hall-10.13, lmm:generator-symmetry-identity, proof of
  prpstn:hall-10.14), so Design links entries and says so. 79 `\leanok` for 79 environments in
  §10.4; no `sorry` in `Spectral/Stone/`, `AQFT/PositiveEnergy.lean`,
  `Analysis/StrongContinuity.lean`; no `SeparableSpace` or `Nontrivial` there. Filter DCT
  (`tendsto_integral_filter_of_dominated_convergence`) is used in `Exponential.lean` only (bounds
  2 and 2|λ|, squared 4 and 4λ²), not in the density proof, which uses
  `HasCompactSupport.hasDerivAt_convolution_left` and
  `ContDiffBump.convolution_tendsto_right_of_continuous`. No theorem identifies `expUnitary` with
  `NormedSpace.exp` for bounded P; the chapter does not claim one. `strongContinuous_of_weak` is
  used by `GNS/UnitaryRepresentation.lean` (and through it by the Minkowski and curved stabiliser
  files).

## Step 12: chapter header, intro and Overview (2026-10-23)

- Created `web/Manual/Stone.lean` (tag `stone`, file `Stones-theorem`); import and `{include}`
  after `Manual.Unbounded` in `web/Manual.lean` (blueprint order); line added to the manual list
  in `web/README.md`. Imports `AQFT.PositiveEnergy`, `Analysis.StrongContinuity`,
  `GNS.UnitaryRepresentation`, `AQFT.HaagKastler.VacuumState` (for the `apiDocs` links).
- Intro 107 words; Overview 616: reminder on e^(−itĤ) and the Schrödinger equation (derivative
  at 0 is −iĤ), definitions, sign convention (e^(−itĤ) has generator −Ĥ), the bijection, eight
  parts (groups, generator, bounded case, e^(itA), density, Stone, positive energy, weak
  continuity), status (no `sorry`; Mathlib for the four imported results; only completeness of
  H), namespaces.
- Placeholders under "Main definitions and theorems" and "Where to look": "This section is in
  preparation."
- Built: `lake build` and `generate-manual` succeed; page `Stones-theorem/index.html` renders
  with no literal `\*`, `**`, `` $` ``, `{apiDocs` or `{ref`.

## Step 13: Design (2026-10-23)

- Design 1,148 words, seven subsections: unitarity / group law / continuity separate; the
  generator (`LinearPMap`, `generatorDomain` where the punctured limit exists, `limUnder`,
  `exists_generator_eq_iff`, 0⁻¹ = 0, density-free symmetry with the remark of
  lmm:generator-symmetry-identity); the exponential through the functional calculus (links the
  unbounded chapter; `functionalCalculus_expFun`; the `∃ hA` in `stone`; filter DCT for strong
  continuity and the derivative at 0; maximality of self-adjoint operators); density by
  convolution (Gårding as background); proof route and uniqueness (`generator_eq_of_eq_expUnitary`,
  `exp_generator_unique`); positive energy as a property of the generator (three fields,
  `isPositiveEnergy_iff_exists_exp`, vacuum and ground states); weak continuity
  (`isStronglyContinuous_iff_tendsto_zero`, `strongContinuous_of_weak`, the GNS theorems).
- Links: blueprint entries only (def:hall-10.13, lmm:generator-symmetry-identity,
  prpstn:hall-10.14, lmm:hall-10.18, thrm:hall-10.15, thrm:positive-energy-iff-exp,
  thrm:invariant-state-gns-unitary-general); chapters by `{ref}` (unbounded, unbounded-design,
  haag-kastler, curved, gns-design). No internal memos linked.
- Built: `lake build` and `generate-manual` succeed. `python3 scripts/check_temporal_wording.py`:
  OK; a grep of the chapter for temporal words and version strings finds nothing.

## For part 2

- Main definitions and theorems (docstrings of `IsOneParameterUnitaryGroup`,
  `IsStronglyContinuous`, `generator`, `expUnitary`, `average`, `IsPositiveEnergy`; `#check` of
  `generator_expUnitary`, `hasDenseDomain_generator`, `stone`, `isPositiveEnergy_iff_exists_exp`,
  `strongContinuous_of_weak`), with Blueprint lines; Where to look. Add the `open` lines for
  docstring code spans (`Physicslib4.Spectral.Stone`, `Physicslib4.AQFT`, and
  `Physicslib4.Spectral.Unbounded` hiding the bounded/unbounded name clashes as in
  `Unbounded.lean`).
