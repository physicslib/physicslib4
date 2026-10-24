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
