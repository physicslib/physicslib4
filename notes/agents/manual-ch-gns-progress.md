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
