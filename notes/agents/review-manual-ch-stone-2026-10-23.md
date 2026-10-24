# Review: Stone's theorem docstrings and manual chapter (2026-10-23)

Scope: commits `0b4f8d1`, `2661aa4` (docstrings); `web/Manual/Stone.lean` (part 1 in `1ca022b`, part 2
uncommitted). Read-only review; nothing else edited.

Severity: error / should fix / nit.

## A. Docstring passes

Checks run.
- Comments-only: for each of the 8 `.lean` files, the parent and the commit agree once block and
  line comments are stripped and whitespace normalised (`/tmp/stonerev/strip.py`, nested `/- -/`
  aware): all 8 SAME.
- Format: no added line over 100 characters (counted in characters, not bytes); no added line
  starts with a Lean keyword; no unescaped asterisk outside code spans; all 33 added "Blueprint:"
  lines are plain text (8 cited labels in part 2, 14 in part 1, 11 "uncited (...)").
- Accuracy: each docstring checked against its code and against `stones-theorem.tex` and
  `haag-kastler-axioms.tex` (def:positive-energy, thrm:positive-energy-api, lmm:positive-conj,
  lmm:weak-continuity-implies-strong). Cited names all exist (`isFactor_of_isIrreducibleInclusion`,
  `localVonNeumann_isFactor_smul`, `IsGroundStateForFlow.exists_strongContinuous_unitary`,
  `exists_gns_unitary_of_invariant_strongContinuous`, the users of `image_centralizer_centralizer`,
  `lieConj_apply_eq_conjStarAlgEquiv` and `restrictStarAlgEquiv` in both `GeometricCovariance.lean`).
  `exp_lieConj`'s "converges because H is complete" is right: Mathlib's `exp_units_conj` sits in the
  `[CompleteSpace 𝔸]` section. The DCT bounds (`b := fun _ => 2`, squared 4) match the code.

The three corrections in `2661aa4`:
- `IsPositiveEnergy.conj`: confirmed. The statement gives only positive energy; the generator form
  is `mem_generator_conj_domain_iff`/`generator_conj_apply`, now cited as such. (The blueprint's
  thrm:positive-energy-api (iii) still says "with generator WAW⁻¹"; that is covered by
  lmm:generator-conj, so no blueprint change is needed.)
- `IsFactor` takes any set: confirmed (`R : Set (H →L[ℂ] H)`), and "a factor contains 𝟙" follows.
- `restrictStarAlgEquiv` two inclusions: the new text is accurate, but the old "carries S onto T"
  was not wrong, since e(S) ⊆ T and e⁻¹(T) ⊆ S together say e(S) = T. It is a clarification, not a
  correction (see A3).

A1. *should fix.* `AQFT/PositiveEnergy.lean`, `IsPositiveEnergy` docstring, "For time translations
A is the Hamiltonian, and the condition says that the energy is bounded below by 0."
- **Problem.** The docstring is embedded in the chapter (Main, Positive energy), whose Overview
  l. 58–59 and the `generator` docstring say that the time evolution e^(−itĤ) has generator −Ĥ.
  Read together, the page seems to say that positive energy for time evolution means −Ĥ ≥ 0. The
  sentence is right only for the representation of time *translations*, U(t·e₀) = e^(itĤ) in the
  convention U(a) = e^(iP·a), which is the inverse of the Schrödinger evolution. Neither the
  docstring nor the blueprint states this convention.
- **Fix.** Replace the sentence with: "For the unitaries of time translations, U(t) = e^(itĤ) in
  the convention U(a) = e^(iP·a) (the inverse of the Schrödinger evolution e^(−itĤ)), A is the
  Hamiltonian Ĥ, and the condition says that the energy is bounded below by 0."

A2. *nit.* `Analysis/StrongContinuity.lean`, `strongContinuous_of_weak`: "This lemma upgrades their
continuity to the strong continuity that the hypotheses of Stone's theorem require
(`GNS.exists_gns_unitary_of_invariant_strongContinuous`)."
- **Problem.** The parenthesis follows "Stone's theorem", so it reads as if it named Stone's
  theorem. It names the user of the lemma.
- **Fix.** "... to the strong continuity that Stone's theorem requires; this is how
  `GNS.exists_gns_unitary_of_invariant_strongContinuous` uses it."

A3. *nit.* `Operators/Conjugation.lean`, `lieConj_apply_eq_conjStarAlgEquiv`: "the equation
transfers linearity and preservation of adjoints to `lieConj U`".
- **Problem.** Only `lieConj_star` goes through this lemma. `lieConj_add` and `lieConj_smul` are
  proved directly with `simp`.
- **Fix.** "so the equation transfers preservation of adjoints to `lieConj U` (`lieConj_star`)".
  Also, for the record: `restrictStarAlgEquiv`'s old text was correct (see above), so the log's
  "Corrected" entry for it should read "clarified".

A4. *nit.* `restrictStarAlgEquiv`, Blueprint line "restriction of a `*`-automorphism to
subalgebras it maps onto each other": "onto each other" is loose, since e maps S onto T and e⁻¹
maps T onto S. Write "(restriction of a `*`-automorphism that maps one star-subalgebra onto
another)".

A5. *proposals.* Placement of the 11 uncited `Conjugation.lean` declarations. I agree with the
writer's grouping. One change: put the commutant lemmas in the existing proof's `\uses{}` rather
than in a node of their own, and use one short new subsection in `haag-kastler-axioms.tex` just
before thrm:von-neumann-geometric-covariance (l. 927), "Conjugation by a unitary":
- `def:unitary-conjugation`:
  `\lean{Units.conjMulEquiv, Physicslib4.lieConj, Physicslib4.lieConj_apply_eq_conjStarAlgEquiv, Physicslib4.norm_lieConj, Physicslib4.exp_lieConj}`.
  The map T ↦ UTU⁻¹ on B(H); a `*`-automorphism, isometric, and exp(UAU⁻¹) = U exp(A) U⁻¹.
- `lmm:automorphism-commutant`: `\lean{MulEquiv.image_centralizer, MulEquiv.image_centralizer_centralizer}`
  (φ(S') = φ(S)', φ(S'') = φ(S)''). Add it to the `\uses{}` of the proofs of
  thrm:von-neumann-geometric-covariance and of its curved-spacetime counterpart, which already
  describe it in prose.
- `def:factor`: `\lean{Physicslib4.scalarOperators, Physicslib4.IsFactor}` (R ∩ R' = ℂ𝟙, for any
  set R). It replaces the inline definition in thrm:von-neumann-factor-orbit and goes in the
  `\uses{}` of thrm:irreducible-inclusion-factor and thrm:self-inclusion-factor (l. 1041, 1054).
- `lmm:factor-conj`: `\lean{Physicslib4.IsFactor.conj}`, in the `\uses{}` of the proof of
  thrm:von-neumann-factor-orbit.
- `lmm:restrict-star-alg-equiv`: `\lean{Physicslib4.restrictStarAlgEquiv}`, used where R(B) ≃⋆ₐ
  R(L·B) is stated (`localVonNeumannEquiv`, under thrm:von-neumann-geometric-covariance).
  `GNS/Superselection.lean`'s `restrictStarAlgEquiv'` (two ambient algebras) could share this node.

This is for the lean-blueprint agent. Until it is done, the "uncited (...)" lines stay. These
nodes are not definitional design changes, since they name existing declarations.

A summary: 0 errors, 1 should fix (A1), 3 nits (A2–A4), proposals A5.

## B. Chapter `web/Manual/Stone.lean`

Checks run.
- Build: `cd web && lake build && lake exe generate-manual --output _out/manual` exits 0. The only
  warnings that name Stone files are the module-system import notices.
- Rendered page `_out/manual/html-multi/Stones-theorem/index.html`: no literal `\*`, `**`, `` $` ``,
  `{apiDocs`, `{ref`, `{docstring`, unresolved `][st-` or KaTeX errors. The 6 docstring boxes
  render.
- Links: all 53 blueprint anchors exist in `blueprint/web/chptr-haag-kastler-axioms-blueprint.html`,
  and every label of `stones-theorem.tex` is linked. All 39 API-doc links point to existing modules
  and declarations. Internal links resolve, apart from the shared header's `../tutorial/` and
  `../site/`, which lie outside `_out/manual` (not a chapter issue). `home_page/sec10-4-stone.md`
  exists.
- Claims: 79 `\leanok` for 79 environments in §10.4. No `sorry`, `SeparableSpace` or `Nontrivial`
  in `Spectral/Stone/`, `AQFT/PositiveEnergy.lean` or `Analysis/StrongContinuity.lean`. All 6
  `#check` outputs match the declarations. The deficiency-subspace sketch matches
  `hasDerivAt_inner_orbit` and `eq_zero_of_hasDerivAt_of_bounded`. Uniqueness, the DCT bounds 4
  and 4λ², the hypotheses of `average_mem_generator_domain` and `tendsto_average_bump` (group law
  and strong continuity), the GNS users of `strongContinuous_of_weak` (the bundled form goes
  through the unbundled one) and the `IsVacuumState` description (∀ γ one-parameter subgroup,
  future-timelike) are all correct.
- Headline coverage of §10.4 is complete: 10.11, 10.13, the bounded case, def:exp-unitary-group,
  10.14, 10.17, 10.18 and 10.15 each have a docstring, a `#check` or a link, as do positive energy
  (all of thrm:positive-energy-api) and weak continuity.
- Word counts (prose only): intro 107, Overview 616, Design 1,148, Main 569, Where to look 175.
- Prose: present tense, a reminder at the start of the Overview ("As you will recall"), well
  pitched. No temporal wording and no version strings.

B1. *should fix.* Design l. 104–105, writer's doubt 3: "where one of its entries remarks on the Lean
formalization, this section links that entry."
- **Problem.** The first clause is accurate: `stones-theorem.tex` has no "Formalization note". The
  second overclaims. The entries that do remark on Lean or Mathlib are lmm:generator-symmetry-identity
  (l. 107), lmm:exp-bounded-unitary-group (l. 183, 195), lmm:exp-bounded-hasDerivAt (l. 208), the
  proof of lmm:generator-exp-bounded, the four imported results (l. 239, 252, 269, 294, 306), and
  the proofs of lmm:exp-strongly-continuous (l. 371, filter DCT) and lmm:exp-derivative-at-zero
  (l. 446). Design links only the first of these. Of the entries it does link, def:hall-10.13 has
  no Lean remark at all, and the filter-DCT paragraph (l. 158–167) cites prpstn:hall-10.14 rather
  than the two lemmas whose proofs name the Mathlib theorem.
- **Fix.** l. 104–105: "Section 10.4 of the blueprint has no paragraph labelled "Formalization
  note"; its remarks on the Lean formalization sit inside entries, mostly naming the Mathlib
  results a proof uses, and this section links the entries it draws on." At l. 163, after
  `tendsto_integral_filter_of_dominated_convergence`, add "(the proofs of
  [lmm:exp-strongly-continuous](…#lmm:exp-strongly-continuous) and
  [lmm:exp-derivative-at-zero](…#lmm:exp-derivative-at-zero))".

B2. *should fix.* The sign of time translations (Overview l. 58–59 against the embedded
`IsPositiveEnergy` docstring and Overview l. 83–86).
- **Problem.** As in A1: the page says that e^(−itĤ) has generator −Ĥ and then that positive energy
  of time translations means Ĥ ≥ 0, without saying that the translation unitaries are e^(+itĤ).
- **Fix.** The A1 docstring fix. Also, in Design "Positive energy is a property of the generator",
  after l. 213, add: "For time translations the unitaries are $`U(t) = e^{it\hat H}`, in the
  convention $`U(a) = e^{iP\cdot a}`, the inverse of the Schrödinger evolution, so their generator
  is $`\hat H` and positive energy says $`\hat H \ge 0`."

B3. *nit.* Main, Positive energy, l. 497–498: "The blueprint collects these six results in
thrm:positive-energy-api." The label is plain text, although `[st-pea]` is defined. Write
"[thrm:positive-energy-api][st-pea]".

B4. *nit.* Where to look l. 541–543, writer's doubt 4: `Basic.lean`'s bullet does not mention the
scalar ODE lemma that lives there. Add "the equation y' = cy (`eq_mul_exp_of_hasDerivAt`)" to the
bullet; keep lmm:linear-ode-scalar under "Stone's theorem" (see doubt 4 below).

B5. *nit.* Design l. 112: "linear isometric equivalence"; the docstrings and Mathlib say "linear
isometry equivalence". Use the latter.

B6. *nit.* Main intro l. 247–249, writer's doubt 2: add one sentence after the coercion sentence:
"Names in the printed statements are relative to the opened namespaces: `HasDenseDomain` and
`IsPositive` are `Spectral.Unbounded.HasDenseDomain` and `Spectral.Unbounded.IsPositive`, and
`generator` and `expUnitary` are in `Spectral.Stone`." The printed declaration names stay fully
qualified.

### Writer's doubts

1. **Main + Where to look at 744 words: nothing important is missing.** The 6 embedded docstrings
   (about 150–250 words each) are not in the count, so the rendered sections are well over the
   ~1,100 target. Every §10.4 label and every positive-energy result is linked. Add B3, B4 and B6;
   do not add more prose, which would repeat Design.
2. **`open` lines: not harmful; keep them.** They are the settled convention of `Unbounded.lean`.
   The declaration being checked still prints its full name, there is only one `IsPositive` for
   partial maps (Mathlib's bounded one prints as `P.IsPositive` on `H →L[ℂ] H`), and each short
   name is apiDocs-linked in the surrounding prose. The one risk is `IsPositive` sitting next to
   Design's `Spectral.Unbounded.IsPositive`; B6 removes it.
3. **"No Formalization note" wording:** the first half is accurate and well put; the second half
   overclaims (B1).
4. **lmm:linear-ode-scalar: keep it under "Stone's theorem".** The subsections are organised by
   role, and its only use is lmm:bounded-exp-solution-zero in `Theorem.lean`, in the
   deficiency-subspace step. The file location belongs in Where to look (B4).

B summary: 0 errors, 2 should fix (B1, B2), 4 nits (B3–B6).

## Verdict and top 5

Verdict: **accept with fixes.** Part A changes only comments, is accurate, and keeps to the agreed
format. Its one substantive problem is the unstated sign convention for time translations, which
shows up on the chapter page. Part B is accurate, covers every §10.4 label, renders cleanly, and
reads well. The fixes are small.

Counts. A: 0 errors, 1 should fix, 3 nits (plus the A5 proposals). B: 0 errors, 2 should fix,
4 nits.

Top 5:
1. A1/B2: state that time-translation unitaries are e^(+itĤ) (U(a) = e^(iP·a)), so that "A is the
   Hamiltonian" does not clash with "e^(−itĤ) has generator −Ĥ".
2. B1: reword Design l. 104–105, and link lmm:exp-strongly-continuous and
   lmm:exp-derivative-at-zero for the filter DCT.
3. A5: add the Conjugation nodes (def:unitary-conjugation, lmm:automorphism-commutant, def:factor,
   lmm:factor-conj, lmm:restrict-star-alg-equiv) through the lean-blueprint agent.
4. B6: one sentence on the namespaces of the printed short names.
5. B3/B4: link thrm:positive-energy-api; mention `eq_mul_exp_of_hasDerivAt` in `Basic.lean`'s
   bullet.
