# Reference manual, chapter "The GNS construction": progress log

Plan: `plan-verso-reference-manual-2026-10-17.md` (chapter 1). Part A is a docstring pass over the
headline declarations the chapter shows with `{docstring}`, in `Physicslib4/GNS/`; part B (the
chapter text) is a later step. Appended after each file.

## Step 0: reconnaissance (2026-10-21)

- Read `.claude/CLAUDE.md`, the plan (chapter 1), the two manual reviews (format: one-sentence
  first line; mathematics for a first-year theoretical-physics PhD student; "Implementation note:"
  last before "Blueprint: <label>" in plain text; multi-character subscripts in parentheses).
- Blueprint nodes: `gns-construction-details.tex` (def:state, def:cyclic-vector,
  thrm:gns-construction-theorem, lmm:lmm1, lmm:lmm2) and `haag-kastler-axioms.tex` (the
  representation-theory nodes, l. 1067–1763, and thrm:separating-faithful at l. 2148).
- `gns_construction` uses Mathlib's `PositiveLinearMap.GNS` (completion of the type synonym
  `PreGNS` of A), not `nullSet`/`nullSubmodule`; the quotient by the null space is implicit in the
  completion of a pseudometric space. Recorded in the `nullSet` docstring.

## Step A1: `GNS/Basic.lean` (2026-10-21)

- `State` and its 2 fields, `State.IsFaithful`, `IsCyclicVector` (5 docstrings). Checked:
  ‖φ‖ = Re φ(1) for positive φ needs `[Nontrivial A]` (`norm_eq_re_apply_one_of_positive`), so the
  text says "on a nonzero algebra"; representations are unital (`StarAlgHom`); the blueprint's
  def:cyclic-vector allows any algebra, the Lean A is a unital C*-algebra (implementation note).
  Built (only the pre-existing module-system notices).

## Step A2: `GNS/NullSpace.lean` (2026-10-21)

- `nullSet`, `orthSet`, `nullSubmodule` (3 docstrings). None of the three is in a `\lean{}` list,
  so the last line names the blueprint set ("Blueprint: the set 𝒩 of lmm:lmm1 and lmm:lmm2").
  Proposal for the lean-blueprint agent: add `nullSet`, `orthSet` to `\lean{}` of lmm:lmm1 and
  `nullSubmodule` to lmm:lmm2.
- Checked: N(ω) is not used by `gns_construction` (Mathlib's GNS space); the left-ideal property
  the blueprint uses for π(a)[b] = [ab] is not stated in the library (said so). Built (the
  `haveILetI` linter notice in `lmm1`'s proof is pre-existing).

## Step A3: `GNS/CauchySchwarz.lean` (2026-10-21)

- `omega_star_swap_conj`, `cauchy_schwarz_inequality` (2 docstrings; theorems, but the chapter
  shows the inequality). Checked: hypotheses are linearity and positivity only, on a complex
  *-ring; the symmetry proof uses positivity at a + b and i·a + b; real parts and
  `Complex.normSq` as stated. Built.

## Step A4: `GNS/Construction.lean` (2026-10-21)

- `gns_construction`, `gns_unique` (2 docstrings; the headline theorems of the chapter).
  Checked: H is `f.GNS`, π is `f.gnsStarAlgHom`, Ω is the class of 1 (`f.toPreGNS 1`); H in the
  universe of A; faithfulness gives injectivity; `gns_unique` gives `H₁ ≃ₗᵢ[ℂ] H₂` with UΩ₁ = Ω₂
  and intertwining, built by `LinearEquiv.extendOfIsometry` from the dense orbits. Built.

## Step A5: `GNS/Separating.lean` (2026-10-21)

- `separating_of_faithful`, `exists_gns_separating` (2 docstrings; the library has no separate
  `IsSeparating` definition, so these carry "separating"). Checked: separating is stated on A
  (π(a)Ω = 0 → a = 0), not on π(A)''; this is said in an implementation note. Holds in any
  reproducing representation. Built.

## Step A6: `GNS/Irreducibility.lean` (2026-10-21)

- `IsIrreducible`, `IsPure`, `gnsVonNeumann`, `vonNeumannOfSelfAdjoint`, `gnsVonNeumannAlgebra`,
  `vonNeumannCenter` (6 docstrings). Theorems (Schur lemma, `isIrreducible_of_isPure`) left as
  they are.
- Added a fact the old text did not state: on H = 0 every representation satisfies
  `IsIrreducible` (every operator is 0·1); recorded as an implementation note.
- `IsPure`: dominated ψ are continuous (`A →L[ℂ] ℂ`), harmless since positive functionals on a
  C*-algebra are continuous; equivalences cited (`isPure_iff_isExtremePoint`,
  `isPure_iff_isIrreducible`, in later files).
- `gnsVonNeumann`: density cited as `exists_forall_norm_sub_lt_of_mem_bicommutant`
  (`Operators/DensityTheorem.lean`, root namespace `Physicslib4`; not imported by this file, so
  Verso may not link it). `gnsVonNeumann` and `gnsVonNeumannAlgebra` have no `\lean{}` node; no
  Blueprint line (proposal: add them to def:local-von-neumann or a new node).
- Built (the `haveILetI` notice is pre-existing).

## Step A7: `GNS/UnitaryEquiv.lean` (2026-10-21)

- `UnitaryEquiv` (1 docstring). Checked: U : H₁ ≃ₗᵢ[ℂ] H₂ with U(π₁ a x) = π₂ a (U x); refl,
  symm, trans, `isIrreducible_iff`, `isFactor_iff` (on `gnsVonNeumann`) exist. Helpers
  (`conjCLM`, `conjMulEquiv`) left alone. Built.

## Step A8: `GNS/Superselection.lean` (2026-10-21)

- `Intertwines`, `AreDisjoint`, `commutantVonNeumann`, `QuasiEquiv` (4 docstrings). Checked:
  intertwining stated pointwise; `AreDisjoint.symm`, `UnitaryEquiv.not_areDisjoint` (needs
  `[Nontrivial H₁]`), `areDisjoint_or_unitaryEquiv_of_isIrreducible`,
  `mem_commutantVonNeumann_iff_intertwines`, `isIrreducible_iff_commutantVonNeumann_eq_scalars`,
  `commutant_gnsVonNeumannAlgebra`, `commutant_commutantVonNeumann`, `QuasiEquiv.refl/symm/trans`,
  `UnitaryEquiv.quasiEquiv` exist. `QuasiEquiv` uses a `StarAlgEquiv` of the underlying
  *-subalgebras with no normality condition (automatic for *-isomorphisms of von Neumann
  algebras; said so). `Intertwines` is not in a `\lean{}` list (proposal: add it to
  def:disjoint-representations). Built.

## Step A9: `GNS/DirectSum.lean` and `GNS/Amplification.lean` (2026-10-21)

- `directSum` (DirectSum) and `amplification` (Amplification) (2 docstrings). Checked: ℓ² space
  `lp H 2`, diagonal `lpDiag` bounded by ‖a‖ via contractivity; `intertwines_single`,
  `summandProj_mem_commutant`, `not_isIrreducible_directSum` (two distinct indices with nonzero
  vectors), `amplification_intertwines_single`. The quasi-equivalence π ~ ι·π is not proved (the
  module note says so); the `amplification` and `QuasiEquiv` docstrings now say so too. Helpers
  (`lpEvalCLM`, `directSumFun`, `summandProj`) left alone. Both built.

## Step A10: `GNS/ExtremeState.lean` (2026-10-21)

- `State.IsExtremePoint`, `State.precomp`, `State.convexCombo`, `stateSpace`, `State.comp`
  (5 docstrings). Checked: extremality is pointwise with real t and concludes ω₁ = ω₂;
  normalisation of pullbacks and mixtures via `norm_eq_re_apply_one_of_positive`; functoriality
  `State.comp_id`/`comp_comp`; `isPure_comp_iff`, `isPure_precomp_iff`,
  `unitaryEquiv_comp_of_gns` (Covariance.lean) exist.
- Avoided a wrong suggestion: `stateSpace` carries the norm topology, so Krein–Milman is applied
  to `weakStateSet`, not to it (said so).
- `State.precomp`, `State.convexCombo` and `stateSpace` are not in a `\lean{}` list; their last
  lines name the node that describes them (proposal: add them to thrm:purity-covariance-invariant
  and thrm:state-space-convex-bridge). Helpers `starAlgEquivCLM`, `starAlgHomCLM` left alone.
  Built.

## Step A11: `GNS/PureStateExists.lean` (2026-10-21)

- `weakStateSet` (1 docstring). Checked: defined by positivity and φ(1) = 1 in `WeakDual ℂ A`;
  `isCompact_weakStateSet` proved; existence of a pure state by Krein–Milman is not proved (the
  module note says why), and the docstring says so. Built.

## Step A12: `GNS/Covariance.lean` and `GNS/UnitaryRepresentation.lean` (2026-10-21)

- Covariance: `exists_unitary_of_gns_comp`, `unitaryEquiv_comp_of_gns` (2 docstrings; the file
  has no definitions). Checked: proof is `gns_unique` applied to π₁ and π₂ ∘ Φ with
  `isCyclicVector_comp_of_surjective`; transport lemmas `isIrreducible_iff_of_gns_comp`,
  `isFactor_iff_of_gns_comp` exist.
- UnitaryRepresentation: `exists_gns_unitary_of_invariant`, `exists_gns_unitaryRep_of_invariant`,
  `exists_gns_unitary_of_invariant_strongContinuous`,
  `exists_gns_unitaryRep_of_invariant_strongContinuous` (4 docstrings; no definitions in the
  file). Checked: G is a monoid; clauses listed match each statement (the strongly continuous
  forms have no cyclicity clause, the others do); composition convention `g.trans f`. None of the
  four is in a `\lean{}` list; the last line names the Minkowski node they generalise
  ("the general form of thrm:invariant-state-gns-unitary"). Proposal: a blueprint node for the
  algebra-agnostic form, or add them to those nodes.
- `gns_operator_covariance` (helper) left alone. Both built.

## Step A13: `GNS/RadonNikodym.lean` (2026-10-21)

- `rnOp`, `isPure_iff_isIrreducible` (2 docstrings). Checked: `rnOp_inner`, `rnOp_commute`,
  `rnOp_reproducing`, `isPure_of_isIrreducible`, `isIrreducible_of_isPure`; T is built from the
  Riesz vectors `rnVec` and `extendOfNorm` over `cycLM`, with ‖rnVec b‖ ≤ ‖π(b)Ω‖. Helpers
  (`cycLM`, `rnFun`, `rnVec`, `rnLM`) left alone. Built.

## Step A14: final checks (2026-10-21)

- 41 docstrings in 15 files. No `**Restriction:**` lines existed in `Physicslib4/GNS/` at HEAD;
  none added. No guard blocks. One docstring line starting with "with" reworded; no line starts
  with a Lean keyword.
- Full `lake build` passes; the GNS warnings (`Try this`, `simp` suggestions in proofs, the empty
  line in the proof of `exists_smul_adjoint_comp_of_isIrreducible`) are all in proof bodies and
  pre-existing. `lake lint` passes. `scripts/check_temporal_wording.py`: OK.
- Comments-only: all 15 files are identical to HEAD with `--` and nested `/- -/` comments removed
  and whitespace normalised. All backticked names in the new text resolve (library or Mathlib).
- Blueprint `\lean{}` proposals collected above: `nullSet`, `orthSet`, `nullSubmodule`,
  `Intertwines`, `gnsVonNeumann`, `gnsVonNeumannAlgebra`, `State.precomp`, `State.convexCombo`,
  `stateSpace`, and the four `exists_gns_unitary*_of_invariant*` theorems have no node of their
  own.

## Part B: the chapter `web/Manual/GNS.lean`

### Step B0: reconnaissance (2026-10-21)

- Read the plan (chapter 1, per-chapter pattern), `web/README.md`, the two existing chapters and
  their reviews, and this log. Blueprint anchors checked in
  `blueprint/web/chptr-haag-kastler-axioms-blueprint.html`: `sctn:gns-construction-details` and all
  28 node labels the chapter cites exist. The representation theory lives in Section 10.6
  (`haag-kastler-axioms.tex` l. 1067–1762, 2143), so the chapter cites both sections.
- The blueprint has a formalization note in the proof of thrm:gns-construction-theorem
  (`gns-construction-details.tex` l. 325): Mathlib's GNS space, lemmas not used. Linked from Design.
- `#check` outputs taken with `lake env lean` at width 120. `gns_construction` prints the anonymous
  instance binders as `x`, `x_1`, `x_2`; `IsIrreducible` prints as `GNS.IsIrreducible` (a root
  `IsIrreducible` exists).

### Step B1: header, include, Overview (2026-10-21)

- `web/Manual/GNS.lean` created (imports the GNS modules, plus `Operators.DensityTheorem` so that
  `exists_forall_norm_sub_lt_of_mem_bicommutant` in the `gnsVonNeumann` docstring links);
  `{include 1 Manual.GNS}` placed first in `web/Manual.lean` (blueprint order: 10.1 before 10.5,
  10.6), with its import. Overview: 423 words. Web build and generate-manual pass; the page is
  `_out/manual/html-multi/The-GNS-construction/`.

### Step B2: Design (2026-10-21)

- Seven subsections: states as a structure; the construction via Mathlib's GNS space (with the
  blueprint formalization note linked) and the universe of H; cyclic and separating vectors (no
  separate definition of "separating"; stated on A here, the operator form in the Haag–Kastler
  chapter); irreducibility, purity and the commutant (the zero-space fact stated once, neutrally;
  the two topologies on the state space; pure-state existence not proved, with the reason from the
  `PureStateExists.lean` module note); disjointness, quasi-equivalence and superselection
  (amplification quasi-equivalence not proved); direct sums and amplification; covariance and
  unitary implementation. About 1,150 words. Links go to blueprint nodes, not internal memos.
- Checked: "Stone's theorem needs strong continuity" phrased as in the docstring, without claiming
  what the library derives. Web build and generate-manual pass.

### Step B3a: Main, first three subsections (2026-10-21)

- States (2 boxes, 1 `#check`: `cauchy_schwarz_inequality`); the GNS construction (1 box,
  3 `#check`: `gns_construction`, `gns_unique`, `separating_of_faithful`); irreducibility and purity
  (4 boxes: `IsIrreducible`, `gnsVonNeumann`, `IsPure`, `State.IsExtremePoint`, `weakStateSet`;
  5 `#check`). `gns_construction` printed, with a sentence decoding `x`, `x_1`, `x_2` and a link to
  tutorial chapter 3, which reads it line by line. All `leanOutput` blocks match. Build passes.
  (Correction: five boxes in "Irreducibility and purity", not four.)

### Step B3b: Main, last three subsections (2026-10-21)

- Equivalence and disjointness (5 boxes: `UnitaryEquiv`, `Intertwines`, `AreDisjoint`,
  `QuasiEquiv`, `commutantVonNeumann`; 2 `#check`: the irreducible dichotomy,
  `UnitaryEquiv.quasiEquiv`); direct sums and amplification (2 boxes, 1 `#check`:
  `not_isIrreducible_directSum`); covariance (1 box `State.comp`; 2 `#check`: `isPure_comp_iff`,
  `exists_unitary_of_gns_comp`). The four `exists_gns_unitary*_of_invariant*` theorems are linked,
  not printed (anonymous nested existentials), with their clauses stated in prose. Blueprint: the
  invariant-state nodes are cited as the Minkowski form these theorems generalise.
- Main: about 900 words of prose; 16 docstring boxes and 14 `#check` blocks in the chapter.
  All 37 blueprint anchors exist. Build passes.

### Step B4: Where to look, final checks (2026-10-21)

- All 15 files of `Physicslib4/GNS/` listed with an `{apiDocs}` link each; the section pages are
  `home_page/sec10-1-gns.md` and `sec10-6-haag-kastler.md` (the Spacetime chapter's naming pattern
  does not apply). About 300 words.
- Reread: "commutant form" equivalence now gives both directions; superselection sectors
  "labelled by" classes of irreducibles; the Overview no longer says "one algebra" (covariance uses
  two). The Schur-lemma sentence states the hypothesis as in the code (proportional to
  ⟨Ω, π(a)Ω⟩, no state assumed).
- Rendering: 76 highlighted inline spans in the docstring boxes, 6 unresolved (expressions with free
  variables such as `ω a`, `H₁ ≃ₗᵢ[ℂ] H₂`, and Mathlib-relative `extremePoints`, `ComplexOrder`);
  accepted, as in the Spacetime chapter.
- Word counts (prose, without code and boxes): Overview 423, Design 1,170, Main 908, Where to
  look 295, intro 112; total about 2,900. `scripts/check_temporal_wording.py`: OK. Web build and
  generate-manual pass. Nothing committed.
- Doubts for the reviewer: (1) `gns_construction` is printed although its `#check` shows the
  instance binders as `x`, `x_1`, `x_2`; the prose decodes them and links the tutorial's reading.
  (2) Design states "A GNS space is never zero, since ‖Ω‖² = ω(1) = 1" as mathematics; the library
  has no lemma `Nontrivial` for the GNS space. (3) The Krein–Milman reason is paraphrased from the
  `PureStateExists.lean` module note (missing `LocallyConvexSpace ℝ (WeakDual ℂ A)` instance); the
  note also cites missing `WeakDual` evaluation lemmas, not mentioned. (4) The chapter cites
  Section 10.6 subsections for the representation theory; the blueprint's own §10.1 covers only
  states and the construction.

## Part C: applying the review `review-manual-ch-gns-2026-10-21.md`

### Step C1: B1, cross-chapter links (2026-10-21)

- Chapter pages carry `<base href="./../">` (the manual root), so `../Haag-…` left the manual.
  Fixed in `web/Manual/GNS.lean` (3 links) and `web/Manual/Spacetime.lean` (2 links, l. 187, 654):
  the chapter link is `{ref "haag-kastler"}[…]`, as the tutorial writes in-book links; subsection
  links are base-relative, `Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--…`
  (the form Verso's own cross-chapter links use; the target subsections have no tags to `ref`).
- Check: rebuilt, regenerated `_out/manual` from clean, served `/tmp/srv/physicslib4/{manual,tutorial}`
  with `http.server`, and resolved every in-book and tutorial href of both pages against the page
  URL and its base: 53 (GNS) and 85 (Spacetime) links, all pages load and all section anchors
  exist. The only anchors without an `id` are the chapter tags (`#haag-kastler`, `#spacetime`,
  `#gns`), which Verso emits itself for its table of contents; they load the page top. Build and
  generate-manual pass.

### Step C2: docstrings, findings A1–A7 (2026-10-21)

- A1 `weakStateSet`: "mathematically these are exactly the states; the library proves that every
  state lies in the set …, not the converse". A2 `QuasiEquiv`: paragraph reflowed to 100 columns;
  the normal-states, folium and multiplicity statements marked as mathematics the library does not
  prove. A3 `omega_star_swap_conj`: "Blueprint: the Hermitian symmetry used in
  lmm:cauchy-schwarz-inequality". A4/A5 `stateSpace`: "Blueprint: the state space of
  thrm:state-space-convex-bridge"; Krein–Milman marked as mathematics, compactness only proved.
  A6 `UnitaryEquiv`: "superselection sectors are classes of irreducible representations of the
  algebra of observables". A7 is a blueprint proposal (formalization note: `PreGNS` is not a
  quotient), not applied; blueprint not edited.
- Blueprint proposals (not applied): the review's A(13) list plus `omega_star_swap_conj` →
  lmm:cauchy-schwarz-inequality (14 uncited); `gnsVonNeumann`/`gnsVonNeumannAlgebra` → a new
  def node in §10.6, not def:local-von-neumann; the four `exists_gns_unitary*` → a new
  algebra-agnostic node.
- Checks: the 5 files are identical to HEAD with comments removed; no new docstring line starts
  with a Lean keyword; no line over 100 columns. `lake build` passes with the same 38 warnings in
  the 5 modules as at HEAD (all pre-existing, in proofs); `lake lint` passes.

### Step C3: chapter, findings B2–B14 (2026-10-21)

- B2: "never zero" marked as immediate from the reproducing condition at a = 1, no separate
  library lemma; zero case does not arise in `isPure_iff_isIrreducible`. B3: Mathlib's
  `IsIrreducible` is about subsets of a topological space. B4: "among the missing pieces …
  `LocallyConvexSpace ℝ (WeakDual ℂ A)`". B5: both summands nonzero. B6: centre lemma plus
  `isFactor_gnsVonNeumann_of_isIrreducible` (checked: `AQFT/HaagKastler/GeometricCovariance.lean`,
  namespace `Physicslib4.GNS`); "Where to look" notes `IsFactor` is in `Operators/Conjugation.lean`.
  B7: "mostly for an arbitrary C\*-algebra". B8: (π(A) ⊗ 1)' = π(A)' ⊗̄ B(ℓ²(ι)). B9: "any unital
  C\*-algebra". B10: "The chapter has five parts". B11: GNS representations of two pure states.
  B12: "as `Nontrivial H` or as a nonzero vector". B13: types of `x`, `x_1`, `x_2` named
  (`gns_construction` kept printed). B14: the ComplexOrder and `FunLike` sentences cut from
  Design (both are in the `State` box).
- Word counts: Overview 424, Design 1,194, Main 936, Where to look 299. Web build and
  generate-manual pass; `check_temporal_wording.py` OK. Nothing committed.
