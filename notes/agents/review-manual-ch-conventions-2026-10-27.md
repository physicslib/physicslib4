# Review: reference manual, Conventions chapter and "Not proved" appendix (2026-10-27)

Scope: `web/Manual/Conventions.lean` (sections 1–6), `web/Manual/NotProved.lean`, the title-page
sentence in `web/Manual.lean`, the pointers in the seven Design sections, rendered HTML
(`lake build` and `generate-manual` pass; `check_temporal_wording.py` OK).

Severity: error / should fix / nit.

## 1. Accuracy of stated conventions

Verified correct (no action):
- Blueprint/Lean mapping (`\lean`, `\leanok`, `\uses`, "Blueprint:" lines, formalization notes);
  no `**Restriction:**` line anywhere in `Physicslib4/` or the blueprint (grep empty).
- Signature (−,+,+,+), null includes zero (def:timelike-spacelike-null-vectors uses "zero").
- U(a) = e^(−iP·a), P·a = −P⁰a⁰ + P⃗·a⃗, P⁰ = Ĥ, U(t) = e^(itĤ): matches the `IsPositiveEnergy`
  docstring (PositiveEnergy.lean l. 55–59) and Stone.lean l. 221. Generator with factor 1/i and
  V(t) = e^(itA): matches `generatorQuotient` (Stone/Basic.lean l. 85–96) and def:hall-10.13.
  Sign check: a = (t, 0⃗) gives P·a = −Ĥt, so e^(−iP·a) = e^(itĤ). Correct.
- `ChronologicallyPrecedes`/`IsCausalTrip` = `TransGen`, `CausallyPrecedes` = `ReflTransGen`;
  `causallyPrecedes_iff_eq_or_isCausalTrip`, `isSpacelikeRelated_irrefl`, `NoClosedCausalCurve`,
  `causallyPrecedes_antisymm`, orthocomplement (CausalComplement.lean) exist.
- `hdir` in `isTopologicalBasis_alexandrovBasis` (LorentzianSpacetime.lean l. 200);
  `isTopologicalBasis_alexandrovBasis_standardMinkowski` proves the Minkowski case. The claim
  "holds in every spacetime" is mathematically right (pick p ∈ I⁻(x) ∩ I⁺(p₁) ∩ I⁺(p₂), etc.).
- Isotony as data; Axiom 3 in a common diamond; `exists_quasilocalAlgebra (U) (i : Isotony U)`.
- Universes: `gns_construction.{u}` with `∃ H : Type u`; `gns_unique` with `Type*` for H₁, H₂;
  curved `nonempty_haagKastlerNet (M : LorentzianSpacetime.{u}) : Nonempty (HaagKastlerNet.{u, 0} M)`.
- `orientedIdentityComponent` = identity component ∩ future-orientation-preserving (with inverse);
  Myers–Steenrod remark matches the docstring (IsometryCausality.lean l. 209–223).
- `IsIrreducible` commutant form (Irreducibility.lean l. 59) so zero rep counts; `realCalculus` is
  `cfcHom hA` (ContinuousCalculus.lean l. 253, 274); `LinearPMap.adjoint` zero on its domain when
  not dense; `IsSelfAdjoint` implies dense domain (Mathlib `LinearPMap.IsSelfAdjoint.dense_domain`).

Findings:

C1. **should fix** — Conventions.lean l. 240, heading "_KMS states and flows act on diamonds._"
  contradicts the next sentence (in Minkowski spacetime they act on the quasilocal algebra,
  QuasilocalKMS.lean `flowAut`, `IsKMSStateForFlow` on `N.quasilocal`). Fix: rename to
  "_In curved spacetime, KMS states and flows act on diamonds._"

C2. **should fix** — l. 242 "In curved spacetime there is no such algebra" overstates what
  l. 227–230 say (a quasilocal algebra *need not* exist; the argument is informal and not
  formalised). Fix: "In curved spacetime a quasilocal algebra need not exist, and the library
  constructs none, so a flow is …".

C3. **should fix** — l. 194–197 "The library settles each the same way in Minkowski and in curved
  spacetime" contradicts the quasilocal paragraph (constructed in Minkowski only) and the KMS
  paragraph. Fix: "The library settles them in parallel in Minkowski and in curved spacetime, so
  that the Minkowski axioms read as a special case; where the two differ, the paragraph says so."

C4. **should fix** — l. 103–104 "the spectrum condition, stated as positive energy, says Ĥ ≥ 0"
  under-states the library's form, which is positive energy along *every* future-timelike
  translation (HaagKastler.lean l. 592–595, VacuumState.lean l. 14–20), equivalent to P in the
  closed forward cone. Fix: "…and the spectrum condition is stated as positive energy along every
  future-timelike translation t ↦ U(tn), whose generator is P⁰n⁰ − P⃗·n⃗; for time translations
  it says Ĥ ≥ 0."

C5. **nit** — l. 132 `IsCausalTrip t p q` drops the spacetime argument, while l. 117 writes
  `ChronologicallyPrecedes M t p q`. Fix: `M.IsCausalTrip t p q`.

C6. **nit** — l. 200 "the basic open sets of the Alexandrov topology": l. 168–175 explain that the
  diamonds are only a subbasis in general. Fix: "the sets that generate the Alexandrov topology".

C7. **nit** — l. 343–344 "You know one such convention already: 0⁻¹ = 0" presumes Lean
  knowledge the stated audience may lack. Fix: "One such convention is Lean's 0⁻¹ = 0." 

C8. **nit** — l. 300 is a 140-character prose line (not a URL); rewrap to ≤ 100.

## 2. Appendix items

Absence check (grep `Physicslib4/`, excluding `scratch_*`; no `sorry`/`axiom` declarations):
all 13 items confirmed not proved.
- Pure states: `PureStateExists.lean` proves only weak-* compactness (and `convex_stateSpace` in
  ExtremeState.lean); its note confirms the missing `LocallyConvexSpace` instance. OK.
- Amplification quasi-equivalence: Amplification.lean l. 102 "is not proved". OK.
- Unbounded normal spectral theorem: Normal.lean is the bounded normal case only. OK.
- Kaplansky: StrongDensity.lean l. 82–83 "deliberately not claimed". OK.
- `hdir`, geodesic endpoints (Causality.lean l. 83), oriented identity component: OK.
- Quasilocal uniqueness: only `QuasilocalLift.unique` (uniqueness of lifts), not of the algebra. OK.
- Reeh–Schlieder, vacuum states of nontrivial nets, curved non-existence, Hartle–Hawking/
  Bunch–Davies, general covariance of the trivial theory: OK, each matches its chapter.
All links resolve to the subsection where the chapter discusses the item.

A1. **should fix** — NotProved.lean l. 74–75 "the vacuum is cyclic for the algebra of every
  region": the library counts ∅ as a diamond with 𝔘(∅) = ℂ𝟏, for which Ω is not cyclic (unless
  H is one-dimensional). Fix: "for the algebra of every nonempty diamond".

A2. **should fix** — missing item, marked "not formalised" in a docstring (VacuumState.lean
  l. 14–20) but in no chapter: the equivalence of positive energy along every future-timelike
  translation with the textbook spectrum condition (joint spectrum of P^μ in the closed forward
  cone), which needs a joint spectral measure for commuting unbounded operators. Proposed item
  under "The axioms in Minkowski spacetime": "_The spectrum condition in its joint-spectrum form._
  The library states the spectrum condition as positive energy along every future-timelike
  translation. Its equivalence with the textbook form, that the joint spectrum of the
  energy-momentum operators lies in the closed forward cone, needs a joint spectral measure for
  commuting unbounded operators and is not formalised ([Haag–Kastler chapter], Symmetry and
  states)."

A3. **nit** — further docstring-only "not formalised" facts, absent from every chapter; add or
  consciously omit: Minkowski's identity component is the proper orthochronous Poincaré group
  (IsometryTopology.lean l. 142–144); Hausdorff Alexandrov topology ⇔ strong causality ⇔ agreement
  with the manifold topology (LorentzianSpacetime.lean l. 64–70, chapter 9 context); causal
  closure of a ball is its double cone (CausalComplement.lean l. 211–213). The first is the most
  relevant to the appendix's Spacetime group.

A4. **nit** — intro l. 17–18 "where a theorem depends on one, it is a hypothesis of that theorem"
  is not true of the Myers–Steenrod item, which is built into a definition. Fix: append "or, for
  the group of the curved-spacetime Axiom 5, part of a definition".

A5. **nit** — intro l. 14 "states without proof in prose" reads awkwardly. Fix: "the standard
  facts that the library takes as hypotheses, mentions in prose without proof, or leaves out".

A6. **nit** — l. 59–63 (orientation item) links only the conventions chapter; the other items link
  where the fact matters. Add the Spacetime chapter's Design "Symmetries" link alongside.

Intro tense: present tense, no narration ("it changes as results are formalised" is a present
statement of policy, acceptable).

## 3. Labels, narration, tense, audience, consistency

- No D1/D3/D8, no memo paths, no "now/no longer/previously/new" (grep and
  `check_temporal_wording.py` clean). Present tense throughout.
- "As you will recall" appears three times (l. 88, 194, 258), as settled in earlier memos. OK.
- Consistency with other chapters: no contradictions found beyond C1–C4 (internal to the chapter).
  Curved chapter l. 174 and 553 agree with C2's proposed wording.

## 4. Links and rendering

- Title page: one sentence linking `#conventions` and `#not-proved`; renders.
- Seven Design pointers (GNS, Spectral, Unbounded, Stone, Spacetime, Haag–Kastler, Curved) and the
  three Spacetime in-text links: all `{ref "conventions-*"}` section anchors exist in the output.
- All blueprint anchors in both pages exist in `blueprint/web/chptr-haag-kastler-axioms-blueprint.html`;
  tutorial anchor exists; `sec10-5-spacetime.html` and guide exist.
- L1. **nit** (known, Verso behaviour) — chapter-level refs (`#conventions`, `#not-proved`,
  `#curved`, …) have no element with that id, so they land at the page top. Same as the existing
  chapters; no action needed.

## Verdict and top 5

Accurate and well pitched; ready to commit after the four should-fix edits in the chapter and two
in the appendix. Counts: 0 errors, 6 should fix (C1–C4, A1–A2), 9 nits (C5–C8, A3–A6, L1).

Top 5:
1. C1 — KMS heading says "diamonds" but Minkowski KMS acts on the quasilocal algebra.
2. A1 — Reeh–Schlieder "every region" is false for the library's empty diamond; say "nonempty".
3. C4 — spectrum condition is positive energy along every future-timelike translation, not just Ĥ ≥ 0.
4. A2 — add the joint-spectrum form of the spectrum condition to the appendix.
5. C2/C3 — "there is no such algebra" and "settles each the same way" overstate; soften.
