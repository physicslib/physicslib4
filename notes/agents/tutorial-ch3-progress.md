# Tutorial chapter 3 ("Worked examples"): progress log

Plan: `notes/agents/plan-verso-stage3-tutorial-ch3-2026-10-16.md`. Chapter file:
`web/Tutorial/WorkedExamples.lean`, included after chapter 2 in `web/Tutorial.lean`.

Words are counted as in the chapter 2 log: prose only, code blocks excluded, each inline code span
and each maths span counted as one word.

## Sections

| Section | Words | Build |
|---|---|---|
| Introduction | 181 | OK |
| 1. The trivial net (with the curved aside, 2 exercises) | 1148 | OK (`#check` outputs print full names; one 61-column line wrapped; `mul_comm` needs `(G := ℂ)`) |
| 2. A state and its GNS representation (2 exercises) | 1195 | OK (`identityState`, GNS run, `trivialQuasilocalAlgebra` state, `IsVacuumState` signature; vector-state solution with `positivity` under `ComplexOrder`) |
| 3. Local commutativity in a diamond (2 exercises) | 779 | OK (`ι_inclusion` `#check` output; worked proof `have`/`rw ←`/`Commute.map`; Einstein causality restated as an `example`) |
| 4. Lorentz invariance of causal precedence (2 exercises) | 943 | OK (one 63-column line wrapped; `InhomogeneousLorentzGroup` excerpt pinned by a hidden constructor check) |
| 5. What the examples show | 333 | OK |

## Final state (2026-10-16), after one full reread

- Words (same counting): intro 181, 1: 1224, 2: 1204, 3: 769, 4: 946, 5: 331; total 4655.
- Reread fixes: vacuous-consistency sentence made precise; "stages" of the trivial net (not "three
  pieces"); `noncomputable` reason; type class search and `trivialLocalNet`; blueprint status of the
  trivial net stated; curved Axiom 4 is `HaagKastlerCurved.localAlgebra_of`, not "the proofs above";
  a hidden-statement paragraph in section 3 replaced by a forward reference to the worked proof;
  the overlap remark corrected; `𝔘` in code spans replaced by maths; `chronologicallyPrecedes_smul_iff`
  named; closing section says the library constructs no vacuum state and that the chapter's states
  are on single algebras.
- States constructed in the chapter (tutorial code, not library code): `identityState : GNS.State ℂ`
  (worked, with `goals`), reused as a state on `trivialQuasilocalAlgebra.carrier`; `vectorState Ω hΩ`
  on `EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)` (exercise solution, via `vectorFun`,
  `vectorFun_nonneg`, `norm_vectorFun`).
- Worked proofs in `goals` blocks: `trivialLocalNet_localCommutativity` (`intro`, `exact mul_comm
  (G := ℂ) a b`); the `identityState` construction; running `gns_construction` (`obtain`, `exact`);
  commutation in `𝔘` from the common diamond (`have`, `rw [← ι_inclusion …]`, `Commute.map`); forward
  direction of Lorentz invariance of `≺` by cases (`rfl` / `Relation.TransGen.lift` of
  `causalSegmentPrecedes_smul`); the converse by `g⁻¹` and `inv_smul_smul` (the library's proof).
- Exercises: 8 (two per example), all in Lean with `sorry` statements and checked solutions.
- `lake build` and `lake exe generate-tutorial --output _out/tutorial` succeed, with no warnings from
  the chapter's Lean blocks. Headless-Chrome screenshot of section 1 checked (`goals` states open).

## For the reviewer

- The plan's "state on the trivial net's quasilocal algebra" is shown on `trivialQuasilocalAlgebra`
  (carrier `ℂ`), not on `trivialHaagKastlerNet.quasilocal`, which is chosen by `Classical.choice` and
  is not definitionally `ℂ`. The link to `HaagKastlerNet.IsVacuumState` is a `#check` plus prose; the
  chapter proves no vacuum property.
- `mul_comm a b` fails on `trivialLocalNet.algebra B` (no `CommMagma` instance found); the chapter
  uses `mul_comm (G := ℂ) a b` and explains it as type class search not unfolding `trivialLocalNet`.
- `import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap` (for the C\*-algebra of operators in
  the vector-state exercise) produces Lake's "designed for use with the module system" warning, as
  the library's own Mathlib imports do.
- `#check`/`leanOutput` lines exceed 60 columns (Lean's own output; wrapped by the existing CSS).
- Section 1 is the longest (1224 words, with the curved aside); it can be trimmed if needed.
- The closing section describes chapter 4 in the present tense, as chapter 2 does, before chapter 4
  exists.

## Revision after review (`notes/agents/review-tutorial-ch3-2026-10-16.md`), 2026-10-16

- Group 1 (section 1), build OK: A5 ("up to isomorphism"), A7 (universe display), A8
  (`noncomputable`), A9 (abstract group; "repeat those above"), 2b (reducible-instance wording for
  `mul_comm (G := ℂ)`), cuts 1–7 (the `trivialQuasilocalAlgebra` sentence moves to section 2 in
  group 2), plus small extra trims (the `algebra` bullet, the `rfl` lead-in, the lesson opening,
  the exercise 1 remark). Section 1: 1011 words (from 1224); the 2b wording adds about 45 words
  back against the ~950 target.
- Group 2 (section 2, import), build OK, no warnings from the chapter: 2c (Mathlib import deleted;
  the vector-state code elaborates with the three library imports), A1 (positivity and
  normalisation give ω(1) = 1), A6 (`Nontrivial (Cn n)` hint), A10 (Mathlib's GNS space as the
  completion with null vectors identified), A11 ("some representation reproducing ω"), 2a
  (`trivialQuasilocalAlgebra` is not the chosen `trivialHaagKastlerNet.quasilocal`; `Classical.choice`;
  the `GNS.State.comp` route as a chapter 4 project), cut 4 (the quasilocal-algebra sentence moved
  here), P5 ("up to unitary equivalence, since every vector is aΩ"). Section 2: 1353 words.
- Group 3 (sections 3–5), build OK: A2 (det Λ = 1), A3 (covariance paragraph and second §4
  exercise reworded: the hypothesis of Axiom 3 is Lorentz invariant, the proof uses only the type of
  `covEquiv`; `commute_covEquiv_iff` remark added), A4 (`ReflTransGen` as Mathlib's, "this is why ≺
  is reflexive"), A12 (overlap via isotony), A13 (membership proofs), A14 (the two `_`), P1 (§4
  opening varied), P2 ("As in chapter 2"), P3 (`exists_gns_einstein_causality`), P4 ("reviewed
  against it"), P6 ("The law reads:").
- Not applied: the two rendering nits (chapter-level `#…` fragments are shared infrastructure of
  chapters 1–2; unhighlighted source excerpts are the chapter 2 convention, which the reviewer
  accepts).
- Final: 4669 words (intro 181, 1: 1011, 2: 1353, 3: 784, 4: 1009, 5: 331). `lake build` and
  `lake exe generate-tutorial --output _out/tutorial` succeed with no warnings from the chapter.
  The earlier note on the Mathlib import warning no longer applies.
