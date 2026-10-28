# Reference manual, chapter "The Haag–Kastler axioms in Minkowski spacetime": progress log

Plan: `plan-verso-reference-manual-2026-10-17.md` (chapter 6, written first). Part A is a docstring
pass over the declarations the chapter shows with `{docstring}`; part B is the chapter,
`web/Manual/HaagKastler.lean`. Appended after each step.

## Step 0: reconnaissance (2026-10-17)

- Read the plan, `web/README.md`, the stage-0 log, the prose-style section of the Verso scout memo,
  tutorial chapters 1 and 2, the Lean files of `Physicslib4/AQFT/HaagKastler/` and the blueprint
  section `haag-kastler-axioms.tex`.
- Docstring conventions for the pass: first line a one-sentence summary; then the mathematics; an
  "Implementation note:" paragraph last when needed; blueprint labels as plain text after
  "Blueprint:"; code spans only for Lean names (code spans are highlighted as Lean in Verso), with
  mathematics in plain Unicode (𝔘(B), ι_B, α_L).
- Blueprint nodes are at
  `https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#<label>`;
  the tutorial's chapter 1 sections at `../tutorial/AQFT-in-brief/#physicslib4-tutorial--AQFT-in-brief--...`.
- No `**Restriction:**` lines in the files of this pass.

## Step A1: docstrings, axiom files (2026-10-17)

Docstrings and comments only; each module built with `lake build <module>` (only the pre-existing
"consider adding `module`" warning).

- `LocalAlgebras.lean`: `IsAlexandrovBasisSet`; `LocalNet` and its 3 fields.
- `Isotony.lean`: `Isotony` and its 4 fields.
- `QuasilocalAlgebra.lean`: `QuasilocalAlgebra` and its 6 fields (the universe and indexing
  rationales kept as short "Implementation note:" paragraphs).
- `LocalCommutativity.lean`: `LocalCommutativity`.
- `LorentzCovariance.lean`: `InhomogeneousLorentzGroup` and its 5 fields (orthochronous checked
  against `IsOrthochronous`: (Λe₀)⁰ > 0).
- `LorentzCovarianceAxiom.lean`: `LorentzCovariance`.
- `Net.lean`: `HaagKastlerNet` and its 4 fields, `HaagKastlerNet.quasilocal`,
  `HaagKastlerNet.covEquiv`.

## Step A2: docstrings, representation and state files (2026-10-17)

- `LocalVonNeumann.lean`: `localOperators`, `localVonNeumann`, `localVonNeumannAlgebra`,
  `vonNeumannNet`. One line over 100 characters caught by the linter and rewrapped.
- `QuasilocalIntertwiner.lean`: `HaagKastlerNet.action`, `HaagKastlerNet.IsInvariantState`
  (checked: β_L is defined on the union of local images, a dense *-subalgebra, `localStarSubalgebra`).
- `VacuumState.lean`: `IsFutureTimelikeTranslation` (open forward cone, checked against
  `minkowskiForwardCone`), `HaagKastlerNet.IsVacuumState`, `HaagKastlerNet.IsVacuumStateConcrete`.
- `QuasilocalKMS.lean`: `flowAut`, `IsKMSStateForFlow`, `IsGroundStateForFlow` (KMS condition
  checked against `AQFT.IsKMSState`: bounded, continuous on the closed strip, holomorphic inside).
- `ObservableBridge.lean`: `ObservableCorrespondence` and its 3 fields.
- `QuasilocalObservable.lean`: `IsQuasilocalObservable`.
- Each module built; the only warnings are pre-existing ones in untouched files (Spectral long
  lines, `haveI`/`letI` style, the module-system notice).

## Step A3: checks after the docstring pass (2026-10-17)

- Full `lake build`: passes (3403 jobs). The only warnings in `Physicslib4/AQFT/HaagKastler/` are
  the pre-existing module-system notices; no new warnings.
- `lake lint`: "Linting passed for Physicslib4."
- `python3 scripts/check_temporal_wording.py`: OK.
- `lean_guard.py check --base HEAD`: only the untracked `.claude/` files (present before this
  session); no signature, field, type, proof or attribute changes. No edit was blocked.
- Count: 24 declaration docstrings (`IsAlexandrovBasisSet`, `LocalNet`, `Isotony`,
  `QuasilocalAlgebra`, `LocalCommutativity`, `InhomogeneousLorentzGroup`, `LorentzCovariance`,
  `HaagKastlerNet`, `HaagKastlerNet.quasilocal`, `HaagKastlerNet.covEquiv`, `localOperators`,
  `localVonNeumann`, `localVonNeumannAlgebra`, `vonNeumannNet`, `HaagKastlerNet.action`,
  `IsInvariantState`, `IsFutureTimelikeTranslation`, `IsVacuumState`, `IsVacuumStateConcrete`,
  `flowAut`, `IsKMSStateForFlow`, `IsGroundStateForFlow`, `ObservableCorrespondence`,
  `IsQuasilocalObservable`) and 25 field docstrings, in 13 files.

## Step B1: chapter, introduction and Overview (2026-10-17)

- `web/Manual/HaagKastler.lean`: imports the HaagKastler modules the chapter elaborates; short
  introduction (links to the blueprint section and tutorial chapters 1 and 2) and "Overview" (the
  five declarations of the axioms, what is constructed rather than assumed, the headline results).
- `cd web && lake build && lake exe generate-manual --output _out/manual`: both pass. Links to
  `../tutorial/AQFT-in-brief/` and `../tutorial/Lean-in-brief/` render as relative hrefs.

## Step B2: Design (2026-10-17)

- Subsections: regions are causal diamonds (and `LocalNet.algebra` total, junk values never
  constrained); isotony is data; local commutativity in a common diamond (why: curved spacetime);
  covariance under the identity component (own isotony family, `Eq.mp` transport, β_L);
  the quasilocal algebra is constructed (no ambient algebra, `QuasilocalAlgebra` as interface, no
  uniqueness claim, Axiom 4 kept apart); universes.
- Decisions linked to their blueprint entries (def:isotony, def:local-commutativity,
  def:quasilocal-completeness, thrm:quasilocal-algebra-exists design notes) and to tutorial sections.
  The decision memos under `notes/agents/` are not linked: they are not published on the site.
- Build and generate pass. About 1,200 words.

## Step B3: Main definitions and theorems, parts 1 and 2 (2026-10-17)

- "The axioms": `{docstring}` for `IsAlexandrovBasisSet`, `LocalNet`, `Isotony`,
  `LocalCommutativity`, `InhomogeneousLorentzGroup` (+hideStructureConstructor), `LorentzCovariance`,
  `HaagKastlerNet`; `#check nonempty_haagKastlerNet`.
- "The quasilocal algebra and Axiom 4": `{docstring}` for `QuasilocalAlgebra`,
  `HaagKastlerNet.quasilocal`, `IsQuasilocalObservable`, `ObservableCorrespondence`; `#check` of
  `exists_quasilocalAlgebra`, `LocalCommutativity.commute_ι`,
  `localCommutativity_iff_exists_commute_ι`, `isQuasilocalObservable_measure`.
- `leanOutput` texts taken from `lake env lean` on a scratch file in `/tmp` (same 120-column
  format as Verso); all match. Blueprint links use Markdown reference definitions
  (`[def:isotony][bp-isotony]` with `[bp-isotony]: url`), which Verso resolves.
- Build and generate pass after each part.

## Step B4: Main definitions and theorems, parts 3 and 4 (2026-10-17)

- "Representations and local von Neumann algebras": `#check` of `einstein_causality`,
  `localVonNeumannAlgebra_mono`, `localVonNeumannAlgebra_le_commutant`,
  `localVonNeumannAlgebra_separating`, `dense_range_in_bicommutant`; `{docstring}` for
  `localVonNeumann`, `localVonNeumannAlgebra`. Geometric covariance stated with its actual
  hypothesis (a unitary implementing β_L), checked against `lieConj_image_localVonNeumann`.
- "Symmetry and states": `{docstring}` for `HaagKastlerNet.action`, `IsInvariantState`,
  `IsVacuumState`, `IsFutureTimelikeTranslation`, `IsVacuumStateConcrete`, `flowAut`,
  `IsKMSStateForFlow`, `IsGroundStateForFlow`; `#check` of `action_ι`, `QuasilocalLift.unique`,
  `isOneParameterAut_flowAut`, `IsKMSStateForFlow.convexCombo`. The GNS unitary theorems
  (`exists_gns_unitaryRep`, `..._strongContinuous`, `exists_gns_irreducible_covariant`) are linked
  with `apiDocs` rather than printed: their `#check` output is an unreadable nest of anonymous
  existentials (`∃ H x x_1, ...`).
- State definition checked against `GNS.State` (positive, norm 1).
- Build and generate pass.

## Step B5: Where to look (2026-10-17)

- Files of `Physicslib4/AQFT/HaagKastler/` grouped (axioms, quasilocal algebra, representations,
  states), each with an `apiDocs` link to a representative declaration; the spacetime facts the
  axioms use (`alexandrovBasis_directed`, `isAlexandrovBasisSet_smul`); links to the blueprint
  section and the home page's section page.
- First build failed: `apiDocs` resolves names at build time, and `GeometricCovariance`,
  `CovariantState` and `Purity` were not imported. Imports added; build and generate pass.

## Step B6: review pass and final checks (2026-10-17)

- Rendered page checked in headless Chrome. Fixes: braced subscripts (i_{B₁B₂}, β_{L_t}) render
  literally in docstring boxes (plain text, no KaTeX), so the rewritten docstrings use i(B₁, B₂),
  ι_B₂, α_(L'L), β_(L_t); long `apiDocs` names overflowed the column and now have short link text.
- The lean-kit guard read a prose line of the chapter beginning "instance, ..." as a new
  `instance` declaration; reworded (guard: no findings other than the pre-existing `.claude/` files).
- Final: `lake build` passes (no warnings in HaagKastler files beyond the module-system notices),
  `lake lint` passes, `check_temporal_wording.py` OK; `cd web && lake build && lake exe
  generate-manual --output _out/manual` passes.
- Word counts (prose, excluding Lean blocks and rendered docstrings): introduction 52, Overview 379,
  Design 1,192, Main definitions and theorems about 1,230 (1,298 including link definitions),
  Where to look 317; about 3,170 in all, plus roughly 1,700 words of rendered docstrings.

## Step R: review findings applied (2026-10-17)

Memo: `review-manual-ch-haag-kastler-2026-10-17.md`. All 21 findings applied.

- Docstrings (A1–A11): `InhomogeneousLorentzGroup` no longer claims reflections are not
  symmetries of nature, and gains "Blueprint: def:inhomogeneous-lorentz-group"; `flowAut` says
  "Poincaré transformations"; `IsKMSStateForFlow` writes the dynamics τ_t (distinct from α_L and
  from the inverse temperature β); `localOperators` notes the short form π(𝔘(B)); `Isotony`
  credits the colimit (`exists_quasilocalAlgebra`); `QuasilocalAlgebra` names
  `QuasilocalExistence.lean` and completes the ι indexing argument; `LorentzCovariance` names
  `Set.smul_set_mono`; `IsGroundStateForFlow` summary reworded; the `LocalCommutativity` equation
  is a paragraph of its own. Multi-character subscripts in parentheses throughout.
- Chapter (B1–B9): identity-component wording; `commute_ι` sketch credits the homomorphism, the
  converse the injectivity; Schlieder property with "completely spacelike" and the blueprint's name;
  "to any given accuracy" (twice); strong operator topology wording; 1964 Axiom 4 wording;
  uniqueness of 𝔘 remark; common unit wording; KMS "at positive inverse temperature"; a paragraph
  pointing to the blueprint's representation-theory subsections and `Physicslib4/GNS/`.
- B10: Verso elaborates docstring code spans in the chapter's scope (`getCurrNamespace`,
  `getOpenDecls` in `VersoManual/Docstring.lean`). The chapter now opens `Physicslib4`,
  `Physicslib4.AQFT`, `Physicslib4.AQFT.HaagKastler` and `...HaagKastlerNet` before `#doc`:
  unresolved docstring spans drop from 55 of 72 to 2 of 74 (a field name and a file name); every
  `leanOutput` is unchanged. Recorded in `web/README.md` ("Writing the reference manual").
- Checks: `lake build` (no new warnings), `lake lint` pass; `cd web && lake build && lake exe
  generate-manual --output _out/manual` pass; `check_temporal_wording.py` OK; guard: no findings
  beyond the pre-existing `.claude/` files.
