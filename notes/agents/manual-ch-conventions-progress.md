# Progress log: reference manual, conventions chapter

Plan: `plan-manual-conventions-chapter-2026-10-24.md`. File: `web/Manual/Conventions.lean`,
included last in `web/Manual.lean` (after `Manual.Curved`, before the draft-only
`Manual.FeatureTests`). First half (sections 1–4), 2026-10-24.

## Section 1: How the blueprint and the Lean fit together (2026-10-24)

- Written, ~440 words (raw, URLs included). Placeholders ("This section is in preparation.") for
  sections 5 (Universes) and 6 (Implementation choices). Include line added to `web/Manual.lean`.
- Verified: no `**Restriction:**` line in `Physicslib4/` (grep empty); "Blueprint: <label>" lines in
  82 files (285 lines); "Implementation note:" paragraphs exist (207); "Formalization note"
  paragraphs in 9 sec10 entries, examples used: thrm:gns-construction-theorem (Mathlib GNS space),
  prpstn:hall-8.3 (`cfcHom`); `CHANGELOG.md` exists; `home_page/guide.md` is the guide page.
- `lake build` and `generate-manual` pass.

## Section 2: Sign and notational conventions (2026-10-24)

- Written, ~400 words raw. Verified: signature and "zero vector is null" (def:spacetime,
  lmm:causal-classification); generator with factor 1/i (def:hall-10.13); time-translation
  unitaries e^{itĤ}, inverse of the Schrödinger evolution (`IsPositiveEnergy` docstring, Stone
  chapter Design); Mathlib inner product conjugate-linear in the first argument; notation `≪[M, t]`,
  `≺[M, t]` scoped in `Physicslib4.Spacetime` (Causality.lean l. 150, 214); `U.algebra`,
  `N.algebra`, `Q.ι hB`, `i.map hB₁ hB₂ h`, `covEquiv` as printed in the HK and curved chapters.
- Doubt: the `IsPositiveEnergy` docstring writes the convention as U(a) = e^(iP·a). With signature
  (−,+,+,+) and the η-pairing, P·a at a = (t, 0) is −Ĥt, which gives e^(−itĤ), the opposite sign.
  The chapter therefore states only U(t) = e^{itĤ} and omits the P·a form; the docstring may need
  a word on which pairing is meant.
- `lake build` and `generate-manual` pass.

## Section 3: Causal structure (2026-10-24)

- Written, ~510 words raw (URLs and one `#check` with its output included; prose about 420).
  Shortened from the material moved out of the spacetime chapter (`manual-ch-spacetime-progress.md`,
  "Material moved out of the chapter Design section"). One `#check`:
  `causallyPrecedes_iff_eq_or_isCausalTrip`.
- Verified: `TransGen`/`ReflTransGen` (Causality.lean l. 137, 195, 212); Hawking–Ellis wording in
  def:causal-trip; `isSpacelikeRelated_irrefl`, `NoClosedCausalCurve`, partial order under it
  (`causallyPrecedes_antisymm`); nowhere-vanishing velocity (def:paths, Curves.lean `nonvanishing`);
  `hdir` hypothesis and "not proved in the library" (spacetime chapter, thrm:alexandrov-topological-basis);
  `IsManifold model ∞ Carrier` (Basic.lean) and the index remark in def:spacetime.
- `lake build` and `generate-manual` pass.

## Section 4: The axiom structures (2026-10-24)

- Written, ~550 words raw (prose about 450). Verified against the HK and curved chapters' Design
  sections and the blueprint: diamonds incl. the empty one, `algebra` on all subsets (HK Design);
  `Isotony` as data with identity/composition laws (def:isotony); Axiom 3 in a common diamond and
  `localCommutativity_iff_exists_commute_ι`; `exists_quasilocalAlgebra`, interface
  `QuasilocalAlgebra`; curved non-existence argued informally in the blueprint, not formalised
  (curved Design); `InhomogeneousLorentzGroup` proper orthochronous (LorentzCovariance.lean
  l. 83–108); Minkowski KMS on `N.quasilocal.carrier`; curved flow a curve into the stabiliser
  (`flowAut`), Killing-flow examples not instances (def:kms-state-for-flow-in-curved-spacetime,
  thrm:kms-thermal-representation-in-curved-spacetime).
- "Kept deliberately" for the Killing-flow point follows the plan; the curved chapter does not use
  the word, so the reason given ("the definitions stay with the regions the axioms govern") is the
  chapter's own phrasing.
- `lake build` and `generate-manual` pass.

## Checks after sections 1–4 (2026-10-24)

- `python3 scripts/check_temporal_wording.py`: OK.
- Link check of `web/_out/manual/html-multi/Conventions-and-design-decisions/index.html`: every
  blueprint anchor exists in `blueprint/web/chptr-haag-kastler-axioms-blueprint.html`, the guide and
  section pages exist in `home_page/`, and every relative chapter link and anchor exists in the
  generated manual. Only Verso's own navigation (`find/…`, chapter-title anchors) is not checked.
- The changelog link to GitHub `main` would 404 (`CHANGELOG.md` is not on `main` yet), so the
  chapter names `CHANGELOG.md` as plain code, as the tutorial does.
- Not yet done (process step 2 of the plan): `web/README.md` entry, title-page link, pointers from
  each chapter's Design section; sections 5–6 and the "not proved" appendix.

## Second half (2026-10-24)

- Section 2 updated: the translation convention U(a) = e^{−iP·a}, P·a = −P⁰a⁰ + P⃗·a⃗, P⁰ = Ĥ, so
  U(t) = e^{itĤ} for a = (t, 0⃗); matches the `IsPositiveEnergy` docstring and the Stone chapter.
  Build passes.

## Section 5: Universes (2026-10-27)

- Written, ~540 words raw. Verified: `gns_construction.{u}` with H in `Type u` (GNS chapter
  output); `QuasilocalIntertwiner.lean` existentials `∃ H : Type u`; Minkowski `LocalNet.{u}`,
  quasilocal carrier in `Type u` (QuasilocalAlgebra.lean l. 103); curved interface `Carrier`,
  `Isom : Type u` (Spacetime.lean l. 98, 107); `LocalNet.{u, v}`, `algebra : … → Type v`;
  `LocalAlgebra` quantifies `H : Type v`; checked with `lake env lean` (pp.universes):
  `toAbstractIdentityComponent : Spacetime.LorentzianSpacetime → LorentzianSpacetime.{0}`,
  `NetTheory.{u_1}`; trivial-net consistency at universe 0 (Net.lean l. 383, curved Net.lean
  l. 426–431).
- `lake build` and `generate-manual` pass.

## Section 6: Implementation choices (2026-10-27)

- Written, ~650 words raw, two subsections (the group of the curved Axiom 5; conventions inherited
  from Mathlib). Verified against the blueprint formalization note of
  def:isometric-covariance-in-curved-spacetime and the Design sections of the spacetime, curved,
  unbounded, GNS and bounded chapters (`LinearPMap`, `LinearPMap.adjoint` zero on its domain when
  not dense, `integralApply` guard, `IsIrreducible` and the zero space (Irreducibility.lean
  l. 53–55), `realCalculus = cfcHom`, `PositiveLinearMap.GNS`). No internal labels.
- "Kept deliberately" for `IsIrreducible` follows the coordinator's brief; the docstring states the
  behaviour and the `Nontrivial H` hypotheses but not the word "deliberately".
- `lake build` and `generate-manual` pass.

## Appendix: what the library does not prove (2026-10-27)

- `web/Manual/NotProved.lean` (tag `not-proved`, file `What-the-library-does-not-prove`), included
  in `web/Manual.lean` right after the conventions chapter. ~640 words raw, 13 items in four groups,
  gathered by grepping `web/Manual/` for "not proved", "does not prove", "not formalise", "no lemma",
  "Mathlib does not": pure states; quasi-equivalence with amplifications; unbounded normal spectral
  theorem; Kaplansky density; intersection property (general spacetime); geodesic equation at
  endpoints; oriented identity component = identity component (Myers–Steenrod); uniqueness of the
  quasilocal algebra; Reeh–Schlieder; vacuum states of nontrivial nets; non-existence of a curved
  quasilocal algebra (informal in the blueprint); Hartle–Hawking/Bunch–Davies as KMS; general
  covariance of the trivial theory.
- The intro's claim that a theorem depending on one of them takes it as a hypothesis: checked that
  `Physicslib4/` has no `sorry` and no `axiom` declarations.
- Conventions section 1 links the appendix ("Where the library stops"). `web/README.md` lists both
  files.
- `check_temporal_wording.py` OK. Link check of both generated pages: all blueprint anchors, section
  pages, tutorial anchors and chapter-section anchors resolve. The three chapter-level `{ref}` links
  (`#not-proved`, `#conventions`, `#curved`) reach the right page, but Verso emits no element with
  the chapter tag as id, so the fragment lands at the top of the page; the existing chapters'
  `{ref "haag-kastler"}` links behave the same.
- `lake build` and `generate-manual` pass.

## Links into the conventions chapter (2026-10-27)

- Title page (`web/Manual.lean`): one sentence linking the conventions chapter and the appendix.
- One sentence at the start of each Design section, linking the relevant conventions section: GNS
  (Universes, Implementation choices), Spectral and Unbounded (Implementation choices), Stone
  (Sign and notational conventions), Spacetime (Causal structure), Haag–Kastler (The axiom
  structures, Universes), Curved (The axiom structures, Universes, Implementation choices).
- Spacetime: the three plain-text "conventions chapter" pointers are now links (index → Causal
  structure, reflexive ≺ → Causal structure, oriented identity component → Implementation choices).
- `lake build`, `generate-manual` and `check_temporal_wording.py` pass. All 21 links to the two
  new pages resolve (section anchors exist; the two chapter-level links open the page at the top).

## Review fixes (`review-manual-ch-conventions-2026-10-27.md`), 2026-10-28

- Chapter (C1–C8) applied with the memo's text: KMS heading "In curved spacetime, …" (C1); "a
  quasilocal algebra need not exist, and the library constructs none" (C2); "settles them in
  parallel … where the two differ, the paragraph says so" (C3); spectrum condition as positive
  energy along every future-timelike translation t ↦ U(tn), generator P⁰n⁰ − P⃗·n⃗, Ĥ ≥ 0 for time
  translations (C4; sign checked against U(a) = e^{−iP·a}); `M.IsCausalTrip t p q` (C5); "the sets
  that generate the Alexandrov topology" (C6); "One such convention is Lean's 0⁻¹ = 0" (C7);
  140-character prose line rewrapped (C8). Build passes.
- Appendix (A1–A6): "every nonempty diamond" for Reeh–Schlieder (A1); new item "The spectrum
  condition in its joint-spectrum form", linked to the Haag–Kastler chapter, Symmetry and states
  (A2, from the `VacuumState.lean` docstring); A3: added "The isometries of Minkowski space connected
  to the identity are the proper orthochronous Poincaré transformations" (IsometryTopology.lean
  l. 142–144) under Spacetime; consciously omitted the Hausdorff/strong-causality equivalence
  (blueprint chapter 9 context, not formalised by design) and "causal closure of a ball is its
  double cone" (a docstring remark, not used anywhere); intro: "or, for the group of the
  curved-spacetime Axiom 5, part of a definition" (A4) and "takes as hypotheses, mentions in prose
  without proof, or leaves out" (A5); Spacetime "Symmetries" link added to the orientation item (A6).
  L1 needs no action. Appendix now has 15 items.
- `lake build`, `generate-manual`, `check_temporal_wording.py` pass; all links in both pages resolve
  (chapter-level refs land at page top, as before).
