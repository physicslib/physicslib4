# Reference manual, chapters "The axioms in curved spacetime" and "General covariance": progress log

Plan: `plan-verso-reference-manual-2026-10-17.md` (chapters 7 and 8). Part A is a docstring pass
over the headline declarations of `Physicslib4/AQFT/HaagKastlerCurved/`; part B (the chapter text)
is a later step. Appended after each file.

## Step 0: reconnaissance (2026-10-21)

- Read `.claude/CLAUDE.md`, the plan (chapters 7, 8) and the three manual reviews (format:
  one-sentence first line; mathematics for a first-year theoretical-physics PhD student;
  "Implementation note:" last before "Blueprint: <label>" in plain text; multi-character
  subscripts in parentheses; present tense).
- Blueprint nodes: `haag-kastler-axioms-in-curved-spacetime.tex` (Axioms 1–5, the net, the
  satisfiability theorem, Einstein causality, local von Neumann algebras, relative commutants,
  covariant states, stabilizer action, KMS/ground states) and
  `general-covariance-in-curved-spacetime.tex` (def:net-equivalence-in-curved-spacetime,
  def:general-covariance-in-curved-spacetime).
- Facts checked in code: concrete complete spacelike separation is pointwise
  (`Spacetime.IsCompletelySpacelike`: every point of O₁ spacelike to every point of O₂); spacelike
  vectors have g(v, v) > 0; the bridge's `Isom` is `orientedIdentityComponent` =
  `identityComponent ⊓ futureOrientationPreserving`.

## Step A1: `HaagKastlerCurved/Spacetime.lean` (2026-10-21)

- `LorentzianSpacetime` and its 7 fields (8 docstrings). Checked: `Carrier` and `Isom` both in
  `Type u`; the only axiom of the interface is `isBasisSet_smul`; the concrete instance is
  `toAbstractIdentityComponent`. The old text said the interface "corresponds to"
  def:lorentzian-spacetime; that node's `\lean{}` lists only the geometric
  `Physicslib4.Spacetime.LorentzianSpacetime`, so the Blueprint line names the interface
  descriptively. Uncited: `HaagKastlerCurved.LorentzianSpacetime` (proposal below).
- Built (only the pre-existing module-system notices).

## Step A2: `HaagKastlerCurved/LocalAlgebras.lean` (2026-10-21)

- `LocalNet` and its 3 fields (4 docstrings), parallel to the Minkowski `LocalNet`. Checked:
  `algebra : Set M.Carrier → Type v` with `M : LorentzianSpacetime.{u}` (D8: algebras in `Type v`,
  v independent of u); unital because `CStarAlgebra` is; 𝔘(∅) ≅ ℂ via `emptyEquivComplex`.
  Helper lemmas (`mul_comm_algebra_empty`, `finrank_algebra_empty`) left alone. Built.

## Step A3: `HaagKastlerCurved/Isotony.lean` (2026-10-21)

- `Isotony` and its 4 fields (5 docstrings), parallel to the Minkowski `Isotony`. Checked against
  def:isotony-in-curved-spacetime: non-strict inclusion, data not existence, laws (a)–(c), the
  design note (no quasilocal algebra; containing algebra; Axiom 3 uses this family). Theorems
  `exists_injective_self`, `Isotony.trans` left alone. Built.

## Step A4: `HaagKastlerCurved/LocalCommutativity.lean` (2026-10-21)

- `LocalCommutativity` (1 docstring). Checked: quantifies over a common containing basis set B,
  as the Minkowski Axiom 3 does; the isotony family is a parameter (no family of its own); vacuous
  when no B exists. The module docstring's "the curved axioms genuinely diverge" (common
  containing set vs quasilocal algebra) predates the Minkowski Axiom 3 in a common diamond and is
  now misleading; module docstrings are outside this pass (follow-up). Built.

## Step A5: `HaagKastlerCurved/LocalAlgebra.lean` (2026-10-21)

- `IsLocalObservable`, `LocalAlgebra` (Axiom 4), `localObservables` (3 docstrings). Corrected:
  the old texts said "every GNS representation"; π is any unital *-homomorphism 𝔘(B) → B(H)
  (H : Type v in `LocalAlgebra`, `Type*` in `IsLocalObservable`). Stated that the axiom holds for
  every net (`localAlgebra_of`, self-adjoint part (b + b*)/2). Uncited: `localObservables`
  (descriptive Blueprint line). Theorems left alone. Built.

## Step A6: `HaagKastlerCurved/IsometricCovariance.lean` (2026-10-21)

- `IsometricCovariance` (Axiom 5; 1 docstring), parallel to the Minkowski `LorentzCovariance`.
  Checked: α is a family of `StarAlgEquiv`s on every subset B; laws 1, 2 by `Eq.mp` along
  `one_smul`/`mul_smul`; law 3 for the Axiom 2 family, with `isBasisSet_smul` and
  `Set.smul_set_mono` discharging the side conditions; `covEquiv` (Net.lean) chooses α and
  `stabAut` restricts it to a fixed region. Added: a generic spacetime has trivial isometry group,
  so the axiom is then weak. Built.

## Step A7: `HaagKastlerCurved/Net.lean` (2026-10-21)

- `HaagKastlerNet` and its 5 fields, `covEquiv`, `commIsotony`, `trivialSpacetime`,
  `trivialLocalNet`, `trivialLocalNetIsotony`, `trivialHaagKastlerNet`, `nonempty_haagKastlerNet`
  (13 docstrings), parallel to the Minkowski `Net.lean`. Checked: the curved net has Axiom 4 as a
  field (the Minkowski one does not); `trivialSpacetime` has `IsCompletelySpacelike := True`, so
  every set is spacelike to itself there; said that the abstract interface does not impose the
  geometric fact that no point is spacelike to itself (`Spacetime.IsCompletelySpacelike`
  docstring: completely spacelike regions are disjoint). Trivial net in universe 0.
- `nonempty_haagKastlerNet` is named in the text of thrm:haag-kastler-net-in-curved-spacetime-
  nonempty but not in its `\lean{}`; `trivialLocalNet`, `trivialLocalNetIsotony`,
  `trivialHaagKastlerNet`, `covEquiv`, `commIsotony`, `trivialSpacetime` are uncited (proposals).
- Module docstring (not in this pass) says the witness gives `Nonempty (Σ M, HaagKastlerNet M)`;
  no such declaration exists (follow-up).
- Helper lemmas left alone. Built (the GNS `Try this`/`simp` notices are pre-existing).

## Step A8: `HaagKastlerCurved/Concrete.lean` (2026-10-21)

- `toAbstractIdentityComponent`, `instTopologicalSpaceToAbstractIdentityComponentIsom`
  (2 docstrings). Kept the D3 implementation note (oriented identity component = isometries
  connected to the identity; equality needs a Myers–Steenrod-type theorem; no Restriction line).
  Checked: `IsCompletelySpacelike` pointwise; `Isom` = `orientedIdentityComponent`
  (`identityComponent ⊓ futureOrientationPreserving`); the isometry-group topology is induced by
  φ ↦ (φ, φ⁻¹) into C(M, M) × C(M, M) (`IsometryTopology.lean`). `toAbstractIdentityComponent`
  itself is in no `\lean{}` (proposal). simp lemmas and the two geometric theorems left alone.
  Built.

## Step A9: `HaagKastlerCurved/IdentityComponent.lean` (2026-10-21)

- `nonempty_haagKastlerNet_identityComponent` (1 docstring; the headline consistency theorem).
  `identityComponent_faithfulSMul` and `isometricCovariance_trivial_identityComponent` keep their
  docstrings (theorems, accurate). Built.

## Step A10: `HaagKastlerCurved/EinsteinCausality.lean` (2026-10-21)

- No definitions (two theorems). Docstrings checked and left: `exists_gns_einstein_causality`
  has its GNS witness in `Type v`, `einstein_causality` is for any representation. 0 changes.

## Step A11: `HaagKastlerCurved/LocalVonNeumann.lean` (2026-10-21)

- `localOperators`, `localVonNeumann`, `localVonNeumannAlgebra`, `vonNeumannNet`,
  `relativeCommutant`, `IsIrreducibleInclusion` (6 docstrings), parallel to the Minkowski file.
  Corrected: `relativeCommutant` and `IsIrreducibleInclusion` were described as for a "nested
  pair"; the definitions take any B₁, B₂ ⊆ B (as the blueprint node says), the nesting is a
  hypothesis of the theorems. Checked the closure argument (commutant of R(B₁) ∪ π(𝔘(B₂))'),
  `scalarOperators H`, `isIrreducibleInclusion_self_iff_isFactor`. Theorems left alone. Built.

## Step A12: `HaagKastlerCurved/GeometricCovariance.lean` (2026-10-21)

- `localVonNeumannEquiv` (1 docstring; the only definition). Made explicit that U is any unitary
  with U π(a) U⁻¹ = π(α̂_g a) (hypothesis `hcov`), of which the stabilizer GNS unitaries are an
  instance, and that the isomorphism is between the underlying *-subalgebras. Theorems left
  alone. Built.

## Step A13: `HaagKastlerCurved/CovariantState.lean` (2026-10-21)

- `IsCovariantFamily` (1 docstring). Checked: indexed by all subsets; condition uses `covEquiv`.
  Added the stabilizer-invariance consequence, marked as mathematics with no library lemma
  (`IsCovariantFamily` has no uses outside this file). `.one`, `.comp` left alone. Built.

## Step A14: `HaagKastlerCurved/StabilizerAction.lean` (2026-10-21)

- `stabAut`, `stabAutHom`, `stabAutMonoidHom` (3 docstrings). Checked: `stabAut` takes any φ with
  a proof h : φ • B = B and any region B; it is `covEquiv φ B` then `algCongr h`; `stabAutHom`
  indexes by `MulAction.stabilizer`; `stabAutMonoidHom` is a `MonoidHom` into
  `StarAlgEquiv.aut`; the Minkowski `actionHom` exists (`QuasilocalIntertwiner.lean`). Helper
  `algCongr` and all theorems left alone. `stabAutHom`, `stabAutMonoidHom` uncited (descriptive
  Blueprint lines; proposals). Also changed the `nonempty_haagKastlerNet` Blueprint line in
  `Net.lean` to the descriptive form, since it is not in `\lean{}`. Built.

## Step A15: `HaagKastlerCurved/Purity.lean` (2026-10-21)

- No definitions (eight theorems). Left alone; 0 changes.

## Step A16: `HaagKastlerCurved/StabilizerKMS.lean` (2026-10-21)

- `flowAut`, `IsKMSStateForFlow`, `IsGroundStateForFlow` (3 docstrings), parallel to the
  Minkowski `QuasilocalKMS.lean` (dynamics written τ_t, as there). Checked: `flow` is any
  ℝ → Stab(B) (group laws are hypotheses of `isOneParameterAut_flowAut` and the GNS theorem);
  the strongly continuous GNS unitary needs one-parameter subgroup, β > 0 and continuity of
  t ↦ ω(a* τ_t b) (`hwc`); ground-state space K : Type v; strong continuity is a field of
  `IsPositiveEnergy`. Theorems left alone. Built.

## Step A17: `HaagKastlerCurved/GeneralCovariance.lean` (2026-10-21)

- `pullbackCarrierEquiv`, `NetEquivalence` and its 2 fields, `NetTheory`, `IsGenerallyCovariant`
  (6 docstrings). Checked against general-covariance-in-curved-spacetime.tex: e : M₁ ≃ M₂ as
  data, only the basis-set hypothesis `he`; Θ data; square on one inclusion; ψ (not ψ⁻¹) carries
  ψ*L-diamonds to L-diamonds; `Diffeo` is C^∞ (`Diffeomorph … ∞`); `NetTheory.{u}` ranges over
  geometric spacetimes with carriers in `Type` (`pullback` uses `Diffeo.{0, 0}`) and nets
  `HaagKastlerNet.{0, u}`. `toAbstractIdentityComponent_pullback_isBasisSet` (theorem) left
  alone. Built.

## Step A18: format pass and final checks (2026-10-21)

- Reflowed 20 docstring lines that began with a Lean keyword (`for`, `where`, `in`, `let`,
  `local`, `theorem`, `instance`, `structure`, `def`, `axiom`) and one line over 100 characters.
  Corrected along the way: the `IsKMSStateForFlow` text first tied flow-invariance to the
  continuity hypothesis; invariance needs only a one-parameter subgroup and β > 0, continuity is
  for the strongly continuous unitary group.
- Full `lake build`: succeeds; no warnings in `HaagKastlerCurved/` (the 54 build warnings are the
  pre-existing ones elsewhere and the module-system notices). `lake lint`: passed.
  `python3 scripts/check_temporal_wording.py`: OK.
- Comments only: all 15 changed files, with `--` and nested `/- -/` comments removed and whitespace
  normalised, are identical to HEAD. No `**Restriction:**` lines existed in these files.
- No edits were blocked by the guard; nothing skipped. `EinsteinCausality.lean` and `Purity.lean`
  contain only theorems and are unchanged.

## Totals

58 docstrings in 15 files: Spacetime 8, LocalAlgebras 4, Isotony 5, LocalCommutativity 1,
LocalAlgebra 3, IsometricCovariance 1, Net 13, Concrete 2, IdentityComponent 1,
LocalVonNeumann 6, GeometricCovariance 1, CovariantState 1, StabilizerAction 3,
StabilizerKMS 3, GeneralCovariance 6 (including the 2 fields of `NetEquivalence`).

## Blueprint proposals (for the lean-blueprint agent; the blueprint is not edited here)

Uncited declarations whose docstrings carry a descriptive Blueprint line:

1. `Physicslib4.AQFT.HaagKastlerCurved.LorentzianSpacetime`: add to `\lean{}` of
   def:local-algebras-in-curved-spacetime (it is the M of Axiom 1), or a new node "abstract
   Lorentzian spacetime interface" in `haag-kastler-axioms-in-curved-spacetime.tex`.
2. `Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent`: add to `\lean{}` of
   def:isometric-covariance-in-curved-spacetime (its formalization note describes exactly this
   group), or to the new node of item 1.
3. `HaagKastlerCurved.nonempty_haagKastlerNet`, `trivialHaagKastlerNet`, `trivialLocalNet`,
   `trivialLocalNetIsotony`: add to `\lean{}` of thrm:haag-kastler-net-in-curved-spacetime-nonempty
   (the first is already named in its text). `trivialSpacetime` stays uncited (a test instance).
4. `HaagKastlerNet.covEquiv`: add to def:isometric-covariance-in-curved-spacetime;
   `HaagKastlerNet.commIsotony`: add to def:isotony-in-curved-spacetime (general-covariance text
   already names `commIsotony`).
5. `HaagKastlerCurved.localObservables`: add to def:local-observable.
6. `HaagKastlerNet.stabAutHom`: add to def:stabilizer-action-in-curved-spacetime;
   `HaagKastlerNet.stabAutMonoidHom`: add to lmm:stabilizer-action-laws-in-curved-spacetime.

## Follow-ups outside this pass (module docstrings)

- `LocalCommutativity.lean` module docstring: "the curved axioms genuinely diverge" by
  quantifying over a common containing basis set; the Minkowski Axiom 3 does the same, so the
  divergence is only the possible absence of such a set and of a quasilocal algebra.
- `Net.lean` module docstring: claims `Nonempty (Σ M, HaagKastlerNet M)`; no such declaration.

## Part B: the chapter `web/Manual/Curved.lean`

Structure: one chapter, "The axioms in curved spacetime and general covariance" (plan chapters 7
and 8 combined; the general-covariance material is three definitions and a relabelling map, so it
is a subsection of Design and of Main, not a part of its own). Tag `curved`, file
`The-axioms-in-curved-spacetime-and-general-covariance`; included in `web/Manual.lean` after
`Manual.HaagKastler`, before `FeatureTests`.

### Step B1: skeleton, introduction and Overview (2026-10-21)

- Imports the 12 `HaagKastlerCurved` modules used. Opens `Physicslib4`, `Physicslib4.AQFT`,
  `…HaagKastlerCurved`, `…HaagKastlerCurved.HaagKastlerNet`, `Physicslib4.Spacetime.LorentzianSpacetime`;
  not `Physicslib4.Spacetime` (its `LorentzianSpacetime` would clash with the interface's).
- Overview (~520 words): what changes in curved spacetime; the six axiom declarations; general
  covariance as a property of a `NetTheory`; the list of proved results. Cross-chapter links via
  `{ref "haag-kastler"}` and `{ref "haag-kastler-design"}` (tags, so base-relative).
- Facts checked: no declaration uses `IsGenerallyCovariant`/`NetEquivalence` outside
  `GeneralCovariance.lean`, so no theory is proved generally covariant (to be said in Main).
- Built (`lake build`, `generate-manual`): OK, only pre-existing notices.

### Step B2: Design (2026-10-21)

- Six subsections: the interface (fields, the one law, no further conditions, `trivialSpacetime`,
  `commute_of_spacelike_mono` takes monotonicity as a hypothesis); the bridge (pieces read off L;
  D3 as an implementation choice, no Restriction marker; links the Spacetime chapter's Symmetries
  subsection base-relatively); local algebras and universes (D8, `Type v`, trivial net v = 0);
  Axiom 3 in a common containing basis set (Schwarzschild example from the tutorial and blueprint
  ch. 9 Axiom 3; vacuous case; composition law; Axiom 4 read locally, a field, `localAlgebra_of`);
  Axiom 5 and stabilisers; general covariance (bijection as data, `NetTheory` over all spacetimes,
  dilations, postulate, not identity-component restricted, not BFV).
- ~1,250 words of prose (1,309 tokens with markup). Moved the `Isom` topology instance to Main.
- Checked: `orientedIdentityComponent` carrier is {g | g and g⁻¹ preserve the future orientation}
  ∩ identity component; blueprint ch. 9 anchor `sctn:axiom-3-(local-commutativity)` (written with
  %28/%29).
- Built: OK.

### Step B3: Main definitions and theorems (2026-10-21)

- Five subsections: interface and bridge; the axioms; Einstein causality and local von Neumann
  algebras; stabilisers, covariant states and KMS states; general covariance.
- 20 `{docstring}` boxes (`LorentzianSpacetime`, `toAbstractIdentityComponent`, `LocalNet`,
  `Isotony`, `LocalCommutativity`, `IsLocalObservable`, `LocalAlgebra`, `IsometricCovariance`,
  `HaagKastlerNet`, `localVonNeumannAlgebra`, `stabAut`, `stabAutMonoidHom`, `localVonNeumannEquiv`,
  `IsCovariantFamily`, `IsKMSStateForFlow`, `IsGroundStateForFlow`, `NetEquivalence`, `NetTheory`,
  `pullbackCarrierEquiv`, `IsGenerallyCovariant`) and 6 `#check`s (`nonempty_haagKastlerNet`,
  `nonempty_haagKastlerNet_identityComponent`, `einstein_causality`,
  `localVonNeumannAlgebra_le_commutant`, `localVonNeumannAlgebra_mono`, `isOneParameterAut_flowAut`).
  The stabiliser GNS unitary theorems, `lieConj_image_localVonNeumann` (prints `⋯` in its
  conclusion), the Schlieder property and the purity results are linked with `apiDocs`, not printed.
- "Not proved" statements: no Reeh–Schlieder theorem (grep: none in `Physicslib4/`); no concrete
  Schwarzschild/de Sitter net, so Hartle–Hawking/Bunch–Davies are not proved KMS; no net theory
  proved generally covariant (the trivial theory is, mathematically).
- `nonempty_haagKastlerNet` prints without the algebra universe (0); said so in the prose.
- ~1,100 words of prose. Built: OK.

### Step B4: Where to look (2026-10-21)

- Files grouped as axioms (7), consequences (7), general covariance (1, plus the Spacetime
  pullback files); KMS and positive-energy files; links to the GNS chapter (`{ref "gns"}`), the
  blueprint sections 10.7/10.8 and the home-page section pages `sec10-7-curved`,
  `sec10-8-general-covariance` (both exist in `home_page/`). Built: OK.

### Step B5: final checks and reread (2026-10-21)

- Reread: reworded "every theorem is proved over the interface" (a few geometric forms are over
  the bridge); the Schwarzschild argument now says the blueprint argues it informally and the
  library does not formalise it; reflowed one long line.
- `python3 scripts/check_temporal_wording.py`: OK (it does not scan `web/`; a manual grep of the
  chapter for the same patterns finds nothing).
- Links in the generated page: 116 checked, all resolve (blueprint anchors in
  `blueprint/web/`, including the ch. 9 `sctn:axiom-3-(local-commutativity)`; API-doc paths are
  the declaring files; tutorial anchors; base-relative manual links to the Spacetime Symmetries
  subsection and the `spacetime-design`, `spacetime-main`, `gns-design`, `haag-kastler-design`
  tags; home-page section pages). Chapter-level `{ref}` links point to existing pages.
- Word counts (prose, maths and code excluded): introduction 92, Overview 401, Design 1,280,
  Main 967, Where to look 278; total about 3,000. 20 docstring boxes, 6 `#check`s.
- Final build: `lake build` and `generate-manual` succeed.

## Part C: review fixes (`review-manual-ch-curved-2026-10-21.md`, 2026-10-22)

### Group A: docstrings

- A1: escaped the 13 `ψ*` in `pullbackCarrierEquiv` and `IsGenerallyCovariant` as `ψ\*`
  (reflowed the second paragraph).
- A2 (user's decision): `stabAut`, `flowAut`, `IsKMSStateForFlow` now say that the black-hole
  exterior and de Sitter static patch are not diamonds (basis sets), that no such flow fixes a
  nonempty diamond, so the axioms as stated place no constraint on their algebras, and that the
  examples motivate the definitions but are not instances; `IsKMSStateForFlow` adds "the library
  constructs neither state". The same correction in the module docstrings of
  `StabilizerAction.lean` and `StabilizerKMS.lean` and in the docstring of
  `IsKMSStateForFlow.exists_gns_unitary_strongContinuous`, which made the same claim.
- A3: `IsometricCovariance` implementation note uses `1 • B`, `(φ'φ) • B`, `φ' • (φ • B)`.
- A4: "a witness ... would come from a `ULift`" replaced by "the library gives no witness in other
  universes", in both `HaagKastlerCurved.nonempty_haagKastlerNet` and the Minkowski
  `HaagKastler.nonempty_haagKastlerNet` (consistency).
- A5: follow-ups added below (not edited in this round).
- Comments only: all 6 changed files identical to HEAD with comments stripped. No docstring line
  over 100 characters or starting with a guarded keyword. `lake build`: OK, no new warnings;
  `lake lint`: passed. No guard blocks.

Follow-ups outside the passes (module docstrings), in addition to the two above:
- `Isotony.lean`: calls `Isotony` "a `Prop`-valued predicate"; it is a structure carrying data.
- `LocalAlgebra.lean`: says Axiom 4 holds "in **every** GNS representation"; π is any
  representation.

### Blueprint sentences (user's decision on A2; targeted edit)

- `haag-kastler-axioms-in-curved-spacetime.tex`, four sentences: the "Physically Stab(B) is the
  stand-in ..." sentence before def:stabilizer-action-in-curved-spacetime; the opening sentence and
  the "precise sense in which ... thermal" sentence of the KMS subsection intro; and the last
  sentence of thrm:kms-thermal-representation-in-curved-spacetime ("realized for the
  Hartle-Hawking and Gibbons-Hawking states"). Each now says that those regions are not diamonds
  (basis sets), no such flow fixes a nonempty diamond, so the axioms as stated place no constraint
  on their algebras; the examples motivate the definitions but are not instances. (The FLRW
  rotation example is kept as a separate sentence.)
- `mcp__fuse__blueprint_refresh`: 677 entries, no errors. No `\lean{}` or node proposals applied.
- Follow-up to the above: the FLRW rotation example is kept, as its own sentence, in the
  blueprint and in the `StabilizerAction.lean` module docstring. Refreshed again: no errors.

### Group B: chapter

- B1: fixed by A1; the rendered page has no stray `<em>` (only the two intended `_net theory_`,
  `_generally covariant_`), and ψ\*L renders as ψ*L.
- B2: Design "Isometric covariance and stabilisers" uses the user's wording (not diamonds; no such
  flow fixes a nonempty diamond; the axioms place no constraint on their algebras; motivation, not
  instances), plus the memo's rotations remark and "definitions accept any B, axioms constrain
  𝔘(B) only on basis sets". The Hartle–Hawking/Bunch–Davies "not proved" sentence adds the same
  point and links the Design section (item 3).
- B3: added after the microcausality `#check`, with the memo's term "additive-free locality" and
  wording, linking `localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric`.
- B4: one sentence with 6 `apiDocs` links (centre, factor, dichotomy, `unitaryEquiv_gns_covEquiv`,
  `unitaryEquiv_gns_stabAut`, `isPure_precomp_stabAut_iff`).
- B5: link to the GNS Design subsection "Covariance and unitary implementation".
- B6: Minkowski link `localCommutativity_iff_exists_commute_ι` (needed the import
  `Physicslib4.AQFT.HaagKastler.LocalCommutativity`).
- B7: "preserved by the stabiliser". B8: Overview uses R(gB₁), g ∈ Stab(B).
- B9: BFV cited with the DOI link (Commun. Math. Phys. 237 (2003) 31–68) and the tutorial link.
- Built: `lake build`, `generate-manual` OK; 47 internal anchors resolve;
  `check_temporal_wording.py` OK. Library `lake build` OK.
