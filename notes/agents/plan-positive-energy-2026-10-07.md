# Plan: lift the bounded-generator restriction on IsPositiveEnergy

Date: 2026-10-07. Toolchain: Lean / Mathlib v4.34.1. Proposed branch: `numina/positive-energy`
off `numina/aqft-in-lean`. Status: approved 2026-10-07 (D1–D5 as recommended; stage 4b, the spectral-support
equivalence, deferred). D2 refinement accepted 2026-10-07: `Unbounded.IsPositive A :=
IsSymmetric A ∧ ∀ ψ : A.domain, 0 ≤ re ⟪ψ, A ψ⟫`.

Stage 9 of `plan-stones-theorem-2026-10-04.md`. It changes definitions, so per CLAUDE.md
nothing is changed until the user approves.

## Current state

- `Physicslib4/AQFT/PositiveEnergy.lean:54`:
  `IsPositiveEnergy V := ∃ P : H →L[ℂ] H, P.IsPositive ∧ ∀ t x, V t x = exp((t I) • P) x`.
  - It has a `**Restriction:**` docstring line saying it is waiting on Stone's theorem.
  - API, all in the same file:
    - `isPositiveEnergy_const_refl`;
    - `exp_generator_unique`, uniqueness of a bounded generator;
    - `IsPositiveEnergy.conj`;
    - `IsPositiveEnergy.strongContinuous`.
- Consumers. Each one uses `IsPositiveEnergy` as a hypothesis or a field. The only API they
  use is `strongContinuous`.
  - `HaagKastler/VacuumState.lean`: `IsVacuumState` (Restriction line 137) and
    `IsVacuumStateConcrete` (Restriction line 198).
  - `HaagKastler/QuasilocalKMS.lean`: `IsGroundStateForFlow` (Restriction line 97), and
    `exists_strongContinuous_unitary`.
  - `HaagKastlerCurved/StabilizerKMS.lean`: `IsGroundStateForFlow` (Restriction line 147), and
    `exists_strongContinuous_unitary`.
- Blueprint (`haag-kastler-axioms.tex` and `haag-kastler-axioms-in-curved-spacetime.tex`). These
  nodes describe the bounded scaffold or call it "Stone-gated":
  - `def:positive-energy` and `thrm:positive-energy-api` (around line 1900);
  - `def:vacuum-state`, `def:vacuum-state-concrete`, and the two ground-state nodes.
  - Some carry a stale `\leanfile{}` tag.
- Now available, from §10.3 and §10.4:
  - `IsOneParameterUnitaryGroup`, `IsStronglyContinuous`, `generator`;
  - `expUnitary hA`, `generator_expUnitary`, and `stone`, which gives uniqueness;
  - `Unbounded.IsSelfAdjoint` and `spectralMeasure`.
- There is no positivity notion for unbounded operators, in Mathlib (no `LinearPMap.IsPositive`)
  or in the project.

## Decisions needed

**D1. Shape of the new definition.**
- (a) **Intrinsic (recommended).** The definition is
  `IsOneParameterUnitaryGroup V ∧ IsStronglyContinuous V ∧ Unbounded.IsPositive (generator V)`.
  - It names the generator instead of quantifying over one.
  - Stone's theorem then gives `V t = e^{itA}` with `A = generator V` self-adjoint, as a
    theorem.
  - The API is easy:
    - strong continuity is a field;
    - the conjugate group's generator is the conjugated generator, straight from the limit
      definition;
    - the constant group's generator is `0` on all of `H`.
- (b) **Existential, mirroring today's form.** The definition is
  `∃ A (hA : IsSelfAdjoint A), Unbounded.IsPositive A ∧ ∀ t, V t = expUnitary hA t`.
  - It reads closest to the current definition and to "V = e^{itP}, P ≥ 0".
  - But `conj` and `const_refl` then need the functional calculus to commute with unitary
    conjugation and to send `0` to `1`. That needs new spectral-measure lemmas.
- Either way, the other form becomes a proved equivalence (`isPositiveEnergy_iff_exists_exp`),
  via `stone` and `generator_expUnitary`.

**D2. Positivity of an unbounded operator** (a new definition, `Unbounded.IsPositive`, in §10.3).
- (a) **Quadratic form (recommended).** `∀ ψ : A.domain, 0 ≤ re ⟪ψ, A ψ⟫`.
  - It is elementary.
  - For a symmetric `A` the inner product is real, so this is the textbook `⟪ψ, Aψ⟫ ≥ 0`.
  - For a bounded `P` it agrees with Mathlib's `ContinuousLinearMap.IsPositive`, which is a short
    lemma.
- (b) **Spectral.** The spectral measure is concentrated on `[0, ∞)`.
  - This is the form physicists quote as the spectrum condition, but it needs self-adjointness
    just to be stated.
- Recommendation: define (a), and add (b) as an optional proved equivalence for self-adjoint `A`
  (stage 4b). The equivalence is not needed by any consumer.

**D3. The bounded case.**
- Drop the bounded predicate.
- Keep backward compatibility with one lemma, `isPositiveEnergy_exp`: for a positive bounded `P`,
  `t ↦ exp(itP)` has positive energy.
  - Its proof computes the generator directly as `P` on all of `H`, from the derivative of
    `NormedSpace.exp`.
  - No spectral theory is needed.
- `exp_generator_unique` (bounded uniqueness) can stay as is; it is a true lemma about `exp`.

**D4. Uniqueness, part (ii) of `thrm:positive-energy-api`.**
- Under D1(a) the generator is unique by definition.
- Replace (ii) by the meaningful statement: if `V t = e^{itB}` with `B` self-adjoint, then
  `B = generator V`. This is the uniqueness half of `stone`.

**D5. Scope of the vacuum spectrum condition.**
- Keep it as it is: positive energy for every future-timelike translation subgroup.
- That is equivalent to the joint energy-momentum spectrum lying in the closed forward cone.
- Formalising the joint-spectrum form needs a joint spectral measure for commuting unbounded
  operators. That is out of scope; the docstring will note it as the textbook form, not as a
  Restriction.

## Stages

1. **Scout (read-only).**
   - Confirm that no other file unfolds `IsPositiveEnergy` (the grep above found none).
   - Find Mathlib's derivative of `t ↦ exp(t • X)` at `0` (used in `exp_generator_unique`).
   - Find `ContinuousLinearMap.IsPositive`'s API, for the bounded-agreement lemma.
2. **Blueprint** (writer, then reviewer; targeted edits to the user's chapters).
   - §10.3, new nodes:
     - `def:positive-unbounded-operator`;
     - `lmm:positive-bounded-agrees`;
     - optionally `lmm:positive-iff-spectral-support`.
   - `haag-kastler-axioms.tex`:
     - rewrite `def:positive-energy` in the D1 form, with no "scaffold" or "Stone-gated" wording;
     - restate `thrm:positive-energy-api`: (i) trivial group, (ii) uniqueness per D4, (iii)
       unitary invariance, (iv) strong continuity, plus (v) the bounded special case and (vi) the
       exponential form via Stone;
     - decompose any part with a nontrivial proof into its own lemma, per the small-proof
       convention.
   - Vacuum and ground-state nodes: change prose only. Their statements are unchanged, because
     they reference `def:positive-energy`.
   - Remove the stale `\leanfile{}` tags from these nodes. The convention forbids them.
3. **Lean definitions** (orchestrator; these are protected definitions).
   - `Unbounded.IsPositive`, in `Spectral/Unbounded/Basic.lean`.
   - The new `IsPositiveEnergy`. `PositiveEnergy.lean` then imports `Spectral/Stone/Theorem`.
   - Update the module docstring, and delete the `**Restriction:**` line.
   - State the API lemmas with `sorry`, then run formalizer-reviewer.
4. **Proofs** (provers, in parallel).
   - Generator lemmas in `Stone/Basic.lean`:
     - `generator_const_refl`: the generator of `t ↦ id` is `0` on `⊤`;
     - `generator_conj`: the generator of `W V W⁻¹` is `W A W⁻¹`, with domain `W(Dom A)`;
     - `generator_exp_bounded`: the generator of `exp(itP)` is `P.toPMap ⊤`.
   - Then, in `PositiveEnergy.lean`:
     - `isPositiveEnergy_const_refl`;
     - `IsPositiveEnergy.conj`, where positivity transports under `W`;
     - `IsPositiveEnergy.strongContinuous`, which is a projection;
     - `isPositiveEnergy_exp`;
     - `isPositiveEnergy_iff_exists_exp`, via `stone` and `generator_expUnitary`;
     - the D4 uniqueness lemma.
   - Optional 4b: `isPositive_iff_spectralMeasure_Iio_eq_zero`. This needs the spectral measure
     to be supported on the spectrum, plus the norm identity. It is the hardest item and can be
     deferred.
5. **Consumers.**
   - Delete the `**Restriction:**` lines and the "Stone-gated" wording in `VacuumState.lean`,
     `QuasilocalKMS.lean` and `StabilizerKMS.lean`.
   - Their proofs use only `strongContinuous`, so they should compile unchanged; fix them if not.
   - Grep the repo for remaining "Stone" and "scaffold" wording and fix it.
6. **Verify.**
   - Build, lint, `leanblueprint checkdecls`, and `#print axioms` on the key results.
   - Have the lean-auditor list the protected-definition changes since the branch point, for
     the user to review.
7. **Publish locally.**
   - Rebuild the PDF and web blueprint.
   - Refresh the home page: the axioms page (spectrum condition), the §10.6 and §10.7 pages, the
     index counts, and the Formalisation status (remove any mention of the restriction).
   - Commit, then merge into `numina/aqft-in-lean`. Don't push unless asked.

## Risks

- **Universe and instance mismatch.** `IsPositiveEnergy` lives in `Physicslib4.AQFT`, and the
  Stone API is in `Physicslib4.Spectral.Stone`, which needs `[CompleteSpace H]`. That is already
  required here.
- **Conjugation lemma.** `generator_conj` changes the domain (`W(Dom A)`). Stating it as an
  equation of `LinearPMap`s needs care with domains; an `∃ h, … = …` characterisation, as in
  `exists_generator_eq_iff`, avoids casts.
- **Weaker definition.** The new definition is strictly weaker than the old bounded one. That is
  the point, but any future theorem that silently assumed a bounded generator will no longer go
  through. Today none does: the only consumer API is `strongContinuous`.

## Estimate

- About 3 new definitions and 8–10 lemmas.
- Most lemmas are short, because Stone's theorem carries the analysis.
- Stage 4b is the only substantial piece, and it is optional.

## Progress log

- 2026-10-07, Stage 1 (scout) done, on branch `numina/positive-energy`.
  - Code consumers: only three statements mention `IsPositiveEnergy` (VacuumState:153,
    QuasilocalKMS:109, StabilizerKMS:160). None unfolds it; the only API they use is
    `hpe.strongContinuous ψ` (QuasilocalKMS:135, StabilizerKMS:186). Keeping that name and
    signature means no consumer proof changes.
  - Imports: no `Spectral/` or `Operators/` file imports `AQFT/`, so `AQFT/PositiveEnergy.lean`
    can import `Spectral/Stone/Theorem` without a cycle. The existing `Operators.Conjugation`
    import (`lieConj`, `exp_lieConj`) is still needed by `isPositiveEnergy_exp`/`conj` if kept.
  - Exponential derivative: `hasDerivAt_exp_smul_const (𝕂 := ℝ) X t` (as already used in
    `exp_generator_unique`) gives `generator_exp_bounded` directly.
  - Mathlib positivity: `ContinuousLinearMap.IsPositive T := T.IsSymmetric ∧ ∀ x,
    0 ≤ re ⟪T x, x⟫` (Positive.lean:273); `isPositive_iff_complex` (line 457) shows that over ℂ
    the symmetric conjunct is not implied by `re ≥ 0` alone (e.g. `T = i·1`).
    **Refinement of D2 (needed for D2's stated property):** define
    `Unbounded.IsPositive A := IsSymmetric A ∧ ∀ ψ : A.domain, 0 ≤ re ⟪(ψ : H), A ψ⟫`, mirroring
    Mathlib, so that `Unbounded.IsPositive (P.toPMap ⊤) ↔ P.IsPositive` holds. For generators the
    symmetric conjunct is free (`isSymmetric_generator`).
  - Blueprint nodes to touch: `def:positive-energy` (haag-kastler-axioms.tex:1899, title
    "bounded-generator scaffold"), `thrm:positive-energy-api` (1907, "all Stone-free"),
    `def:vacuum-state` (1921, title "generator-parameterized scaffold"), `thrm:vacuum-no-stone`
    (1930, title "No-Stone Consequences"; label kept, title/prose only), the Minkowski ground-state
    node (2187) and the curved one (curved.tex:694). Stale `\leanfile{}` tags on 1902, 1910, 1924,
    1933.
  - Home page: §10.6 page entries 587–590 carry the old titles; the axioms page does not mention
    positive energy.
- 2026-10-07, Stage 2 done (writer + reviewer; REVISE then PASS). New nodes:
  §10.3 `def:positive-unbounded-operator` (symmetric, density-free, and Re⟨ψ,Aψ⟩ ≥ 0),
  `lmm:positive-bounded-agrees`; §10.4.1 `lmm:generator-const`, `lmm:conj-unitary-group`,
  `lmm:generator-conj`, `lmm:exp-bounded-unitary-group`, `lmm:exp-bounded-hasDerivAt`,
  `lmm:generator-exp-bounded`; haag-kastler-axioms.tex `lmm:positive-energy-const`,
  `lmm:exp-generator-unique` (D4 form), `lmm:positive-conj`, `lmm:positive-energy-conj`,
  `lmm:positive-energy-strong-continuous`, `lmm:positive-energy-exp-bounded`,
  `thrm:positive-energy-iff-exp`. `thrm:positive-energy-api` kept as a summary (label is the
  user's); its \lean line still names the old declarations and its \leanok was removed, as was
  def:positive-energy's. Retitled def:positive-energy, def:vacuum-state, thrm:vacuum-no-stone (label
  kept); "Stone-gated"/"scaffold" prose gone; stale \leanfile removed from the touched nodes;
  line ≈1883 now points forward to def:vacuum-state.
  Reviewer notes for stage 3: put each Lean name on its split lemma; state lmm:positive-conj as
  "Dom(B) = W·Dom(A) and B = WAW⁻¹ there ⇒ B positive" to avoid building WAW⁻¹ as a LinearPMap;
  `exp_generator_unique` must be restated (or a new name used) for the D4 form. Optional: the
  label `thrm:vacuum-no-stone` is now a misnomer (user's call).
- 2026-10-07, Rename: `thrm:vacuum-no-stone` → `thrm:vacuum-invariance-consequences` (79f642a).
- 2026-10-07, Stage 3 done (statements; 20 `sorry`s on this branch until stage 4):
  - Defs (orchestrator): `Spectral.Unbounded.IsPositive` (Basic.lean); `AQFT.IsPositiveEnergy`
    rewritten as a structure (`isOneParameterUnitaryGroup`, `isStronglyContinuous`,
    `isPositive_generator`); PositiveEnergy.lean now imports Stone.Theorem and Stone.Bounded.
  - Statements: Unbounded/Basic `isPositive_toPMap_iff`, `IsPositive.of_conj`; Stone/Basic
    `isOneParameterUnitaryGroup_refl`, `isStronglyContinuous_refl`, `generator_refl` (= 0),
    `IsOneParameterUnitaryGroup.conj`, `IsStronglyContinuous.conj`,
    `mem_generator_conj_domain_iff`, `generator_conj_apply`; new Stone/Bounded
    `hasDerivAt_exp_smul_I`, `exists_isOneParameterUnitaryGroup_exp`,
    `isStronglyContinuous_of_eq_exp`, `generator_eq_of_eq_exp`; PositiveEnergy
    `isPositiveEnergy_const_refl`, `generator_eq_of_eq_expUnitary`, `IsPositiveEnergy.conj`,
    `IsPositiveEnergy.strongContinuous` (same signature), `isPositiveEnergy_exp`,
    `isPositiveEnergy_iff_exists_exp`. Bounded `exp_generator_unique` kept (proved).
  - Consumers compile unchanged. Formalizer review FAIL → fixed the two bundled statements
    (split) and the canonical `0 : H →ₗ.[ℂ] H`; its remaining finding (stale consumer docstrings
    and Restriction lines) is stage 5 work.
- 2026-10-07, Stage 4 done: all 20 statements proved by 8 parallel provers (one private helper,
  `tendsto_generatorQuotient_conj_iff`, in Stone/Basic). `omit [CompleteSpace H]` added to
  `isPositiveEnergy_const_refl`, `IsPositiveEnergy.conj`, `IsPositiveEnergy.strongContinuous`
  (unused); `Operators.Conjugation` import dropped from PositiveEnergy.lean (no longer used).
  No sorry in the project; build, lint, checkdecls clean; key results depend only on propext,
  Classical.choice, Quot.sound. Next: stage 5 (consumer docstrings and Restriction lines).
- 2026-10-07, Stage 5 done: docstrings rewritten in VacuumState.lean (module doc, IsVacuumState,
  invariant, exists_gns_irreducible_covariant, IsVacuumStateConcrete), QuasilocalKMS.lean and
  StabilizerKMS.lean (IsGroundStateForFlow, invariant, exists_strongContinuous_unitary), and the
  CovariantState.lean module note. All four `**Restriction:**` lines removed; the project now has
  none. No statement or proof changed. Build, lint clean. Note: CLAUDE.md cites the
  positive-energy docstring as its example of a Restriction line; that example no longer exists.
- 2026-10-07, Stage 6 done: build, lint, checkdecls clean; key results on standard axioms only.
  lean-auditor (`notes/agents/audits/audit-positive-energy-2026-10-07.md`): exactly two
  protected changes (IsPositiveEnergy def→structure; new Unbounded.IsPositive), both as approved;
  no unapproved changes, no statement regressions, no removed/renamed theorems, consumers'
  statements unchanged, no sorry, no unrecorded restrictions. Fixed its one mismatch: the \lean
  tag of thrm:positive-energy-api now lists the six current declarations (statement \uses
  restored by hand after the status tool's strip/rewrite dropped it). lean-kit verify receipt
  refreshed (164 files). CLAUDE.md Restriction example replaced (file is untracked).
- 2026-10-07, Stage 7: PDF and web blueprint rebuilt (341 pp.). Home page: entries renumbered
  from the new aux (664 entries incl. conventions), 15 new entries, 4 retitled, subsection item
  counts recomputed; counts now 661 declarations (150/156/252/99/4), 660 formalised, 511 results,
  471 written proofs, 510 formalised proofs, 1,143 distinct Lean names; §10.3/§10.4/§10.6
  overviews and the index status paragraph describe the unbounded positive-energy condition;
  page refs checked against node pages. Jekyll builds, 11 pages, no broken links. Merged into
  numina/aqft-in-lean (fast-forward, not pushed).
