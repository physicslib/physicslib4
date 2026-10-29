# Audit: Jekyll home-page content and its destinations (2026-10-29)

Read-only audit for stage 2 of `notes/agents/plan-site-consolidation-2026-10-29.md`. Each unit of
the Jekyll pages is mapped to a destination and checked against the text actually there (grep plus
targeted reads of `web/Site/`, `web/Tutorial/`, `web/Manual/`, `README.md`, `blueprint/src/`).

Status legend: **ALREADY** (destination covers it), **PARTLY**, **NOT**.
Destinations: Landing (`web/Site/`), Tutorial (`web/Tutorial/`), Manual (`web/Manual/`), Blueprint,
README, Dropped.

Facts checked against the current build: 683 Chapter 10 declarations (environment counts per
`blueprint/src/sections/sec10/*.tex`: 6/144/123/41/146/169/52/2), 1,268 distinct names in
`blueprint/lean_decls`, 348 PDF pages, numbering Definition 13 / Definition 517 / Definition 698
(local `blueprint/web`), Lean v4.35.0, no `sorry` in `Physicslib4/`. All current today; all are
counts that go stale and are to be generated at build time.

## home_page/index.md

| ID | Unit (first words) | Destination | Status | Notes |
|---|---|---|---|---|
| I1 | Title "AQFT in Lean", "by Kelly J Davis" | Landing | PARTLY | Landing has wordmark and tagline; no author line anywhere on the Verso site. |
| I2 | Link row "Blueprint (web) … GitHub" | Landing | ALREADY | Header nav (Tutorial, Manual, Blueprint, API docs) and footer (GitHub, Blueprint PDF) in `Site/Links.lean`, `Site/Theme.lean`. |
| I3 | Intro "In 1964, Rudolf Haag and Daniel Kastler…" | Landing | PARTLY | Hero line + "About" (`Site/FrontPage.lean`) cover sharpening and blueprint-as-spec; no named 1964 paper / DOI link, no "curved spacetime + general covariance" sentence (only in the cards). README §"AQFT in Minkowski and Lorentzian Spacetime" covers it. |
| I4 | Overview "The blueprint is 348 pages long…" | Dropped | n/a | Superseded count. |
| I5 | Overview "Chapters 1–9 are mathematical background… twelve supporting results" | Manual, Conventions › "How the blueprint and the Lean fit together" | PARTLY | Manual says chs 1–9 are context, not formalised; it does not say items 1–12 are background results with no Lean declaration. |
| I6 | Overview "Chapter 10 collects… 683 declarations… 1,268 Lean declarations… Conventions 22, 213, 260" | Landing (status, generated) | NOT | Counts to be generated (stage 3). The "three conventions share the numbering but are not counted" remark should go with the generated table as a footnote. |
| I7 | Overview "All 683 are formalised… no `sorry`… 486 carry a written proof… 40 quoted" | Landing (status, generated) | PARTLY | Landing "About" says "the Lean contains no `sorry`". The quoted-results point (stated in full, not proved in prose, linked to Mathlib) is only implicit in Manual Conventions ("Mathlib's own where Mathlib already has the result"). |
| I8 | Overview table per section (pages, kinds, total, formalised) | Landing (status, generated) | NOT | Page ranges: Dropped. Section links: to manual chapters. |
| I9 | Explore list (guide, axioms, eight section pages) | Landing | ALREADY | Six feature cards link to manual chapters (`Site/Components.lean`); guide/axioms entries go with their pages. |
| I10 | Highlight "The Haag–Kastler axioms in Minkowski spacetime…" | Landing | PARTLY | Card one-liner only. Full content ALREADY in Manual HaagKastler › Overview. Stale wording, see S-1. |
| I11 | Highlight "The Haag–Kastler axioms in Lorentzian spacetime…" | Landing | PARTLY | Card one-liner; Manual Curved › Overview ALREADY. |
| I12 | Highlight "The spectral theorem for bounded self-adjoint operators…" | Landing | PARTLY | Card one-liner; Manual Spectral ALREADY. |
| I13 | Highlight "The spectral theorem for unbounded self-adjoint operators…" | Landing | PARTLY | Card one-liner; Manual Unbounded ALREADY. |
| I14 | Status "The blueprint annotates every node… one place… no `sorry`" | Landing (status) | NOT | Manual Conventions › "Restrictions" says the library has no `**Restriction:**` line (related, not the same claim). |
| I15 | Status item "Axiom 5 in curved spacetime (Definition 651)… Myers–Steenrod" | Manual, Conventions › Implementation choices › "The group of the curved-spacetime Axiom 5" | ALREADY | Also in blueprint ch. 9 and §10.7 formalization notes. Landing status section should link there. |
| I16 | Useful links (blueprint web/pdf, dep graph, docs, original paper) | Landing | PARTLY | Blueprint, PDF, API docs present. Dependency graph and the 1964 paper (DOI) are not on the landing page (both in README; paper in `Tutorial/Papers.lean`). |
| I17 | Contributing "Contributions are welcome… Doing it yourself" | Tutorial ("Doing it yourself") | ALREADY | Also README §Contributing. |
| I18 | Contributing "The project targets Lean and Mathlib v4.35.0" | README | ALREADY | README §Getting Started. Per decision, nowhere else. |
| I19 | Acknowledgements "We are grateful to Rudolf Haag…" | Landing | NOT | README §Acknowledgements ALREADY, and more complete (adds Project Numina). |
| I20 | "physicslib4 is maintained by Kelly J Davis" | Landing | NOT | README footer ALREADY. |

## home_page/guide.md

| ID | Unit | Destination | Status | Notes |
|---|---|---|---|---|
| G1 | Top nav bar | Dropped | n/a | Jekyll navigation. |
| G2 | "How the blueprint is organised" (3 ¶, "348 pages…", "Chapters 1–9…", "Chapter 10…") | Dropped | n/a | Verbatim duplicate of I4–I6. |
| G3 | "Chapters 1–9: unpacking the original axioms" lead + 9-item chapter list | Manual, Conventions › "How the blueprint and the Lean fit together" | PARTLY | Substance is ALREADY in Tutorial "AQFT in brief" (The axioms; aside on primitivity; "What this project sharpens", incl. Schwarzschild) and Manual HaagKastler › Design (diamonds vs causal cones, constructed quasilocal algebra, density theorem). Not covered anywhere on the Verso site: the chapter-to-axiom map (which blueprint chapter discusses which axiom), the comparison of four topologies (ch. 2), the BLT extension of the action (ch. 7). The Manual links to `guide.html` for exactly this map. |
| G4 | "The lower numbers, 1 through 12, label supporting theorems…" | Manual, Conventions | NOT | See gap 5. |
| G5 | "The section pages" ¶ ("Each section page below summarises… derived mechanically") | Dropped | n/a | Pages retired; item lists replaced by manual + blueprint index. |
| G6 | Section-pages link list | Dropped | n/a | Replaced by feature cards / manual TOC. |
| G7 | "Where the Lean lives" ¶ + module table | Manual, "Where to look" section of each chapter | ALREADY | Each chapter lists its files with API-docs links. Stale row, see S-4. |
| G8 | Bottom nav bar | Dropped | n/a | |

## home_page/axioms.md

| ID | Unit | Destination | Status | Notes |
|---|---|---|---|---|
| A1 | Nav bar | Dropped | n/a | |
| A2 | "Axiom 6 (Primitivity)… is not carried… The five sharpened axioms… bundled together as a `HaagKastlerNet`" | Manual HaagKastler › Overview; Tutorial "An aside: primitivity" | ALREADY | Stale for Minkowski, see S-1. |
| A3 | Minkowski table (Axiom, Node, Lean) | Manual HaagKastler › Overview + "Main definitions and theorems › The axioms" | ALREADY | Lean names ALREADY; node numbers belong to the blueprint. |
| A4 | Curved table | Manual Curved › Overview + "The axioms" | ALREADY | |
| A5 | "General Covariance… is deliberately *not* a sixth axiom" | Manual Curved › Overview and Design › "General covariance relates nets…" | ALREADY | |
| A6 | Design note "Isotony supplies its embeddings as data" (incl. Lemma 603) | Manual Conventions › The axiom structures; HaagKastler › Design ("proved, not assumed") | ALREADY | |
| A7 | Design note "Local commutativity is stated in a common containing diamond" | Manual Conventions › The axiom structures | ALREADY | Names `localCommutativity_iff_exists_commute_ι`. |
| A8 | Design note "Axiom 4 is a bridge principle; the quasilocal algebra is a theorem" | Manual HaagKastler › Design › "The quasilocal algebra is constructed" | ALREADY | |

## home_page/sec10-*.md

Per page: the opening summary, each layer bullet, "Where the Lean lives", and the Items block
(item lists + nav bars, Dropped: replaced by the manual and the blueprint's own index, `\lean`
annotations and dependency graph).

### §10.1 GNS (`sec10-1-gns.md`)
| ID | Unit | Destination | Status |
|---|---|---|---|
| 1a | "States and proves the GNS Construction Theorem (Theorem 15)…" | Manual GNS › Overview | ALREADY (faithfulness, uniqueness up to unitary equivalence, Cauchy–Schwarz, null space) |
| 1b | Where the Lean lives | Manual GNS › Where to look | ALREADY |
| 1c | Items + nav | Dropped | n/a |

### §10.2 Spectral (`sec10-2-spectral.md`)
| ID | Unit | Destination | Status |
|---|---|---|---|
| 2a | "The largest section by proposition count… Hall… Standard results… stated in full but not proved" | Manual Spectral › Overview | PARTLY: Hall and the route are covered; the "quoted, not proved in prose, formalised via Mathlib" remark is not stated as such (see gap 1). Count: Dropped. |
| 2b–2g | Six layers: elementary properties; PVMs; Stage 1 CFC; Stage 2 Riesz; Borel calculus and spectral measure; uniqueness and the theorem | Manual Spectral › Design + Main definitions (Spectrum and resolvent, CFC, associated measures, forms, Borel bootstrap, PVM, Borel calculus, spectral theorem) | ALREADY (item numbers: Blueprint) |
| 2h | Where the Lean lives | Manual Spectral › Where to look | ALREADY |
| 2i | Items + nav | Dropped | n/a |

### §10.3 Unbounded (`sec10-3-unbounded.md`)
| ID | Unit | Destination | Status |
|---|---|---|---|
| 3a | "123 declarations… momentum operator… six stages" | Manual Unbounded › Overview | ALREADY (count Dropped) |
| 3b–3g | Six layers, incl. the Lemma 253 / `cfc_map_spectrum` note and Lemma 189 (maximal symmetry) | Manual Unbounded › Design ("Normal operators and the abstract calculus" states the two-variable mapping is proved via Mathlib's CFC), Main definitions; Stone chapter for maximal symmetry | ALREADY |
| 3h | Where the Lean lives | Manual Unbounded › Where to look | ALREADY |
| 3i | Items + nav | Dropped | n/a |

### §10.4 Stone (`sec10-4-stone.md`)
| ID | Unit | Destination | Status |
|---|---|---|---|
| 4a | "41 declarations… Stone's Theorem… one-to-one correspondence… energy–momentum… positive energy" | Manual Stone › Overview | ALREADY |
| 4b–4f | Five layers (unitary groups; imported results; exp(itA); intermediate results; the theorem) | Manual Stone › Design + Main definitions | ALREADY (Bochner, dominated convergence, density by smoothing all present) |
| 4g | "The closing Summary… recorded in prose and is not a separate declaration" | Blueprint | ALREADY |
| 4h | Where the Lean lives | Manual Stone › Where to look | ALREADY |
| 4i | Items + nav | Dropped | n/a |

### §10.5 Spacetime (`sec10-5-spacetime.md`)
| ID | Unit | Destination | Status |
|---|---|---|---|
| 5a | "146 items… trips… genuine geodesics of the Levi-Civita connection… nine layers" | Manual Spacetime › Overview | ALREADY |
| 5b–5j | Nine layers (tangent causality and curves; Levi-Civita/Koszul/geodesics; trips; diamonds, complements, lattice/De Morgan; causal convexity; closure system and Alexandrov basis; dilations; isometries; pullback metrics, Theorem 475) | Manual Spacetime › Design + Main definitions; dilations and pullbacks also in Manual Curved › General covariance | ALREADY |
| 5k | Where the Lean lives | Manual Spacetime › Where to look | ALREADY |
| 5l | Items + nav | Dropped | n/a |

### §10.6 Minkowski (`sec10-6-haag-kastler.md`)
| ID | Unit | Destination | Status |
|---|---|---|---|
| 6a | "The largest section by definition and theorem count… Each axiom is stated as a definition so that it appears as a node" | Blueprint | ALREADY (count Dropped) |
| 6b | Axioms and quasilocal colimit (476–504): isotony as data, colimit+completion, ambient-algebra shortcut rejected, Axiom 4 bridge, junk fibres | Manual HaagKastler › Design (all four subsections) + Conventions › The axiom structures | ALREADY |
| 6c | §10.6.2 von Neumann density theorem (Murphy 4.1.4 route, Kaplansky out of scope) | Manual HaagKastler (density theorem), NotProved (Kaplansky); Murphy route in Blueprint | ALREADY |
| 6d–6o | §10.6.3–10.6.14 and §10.6.16 (Axiom 5 and the net; Einstein causality; local vN algebras/Schlieder; unitary conjugation; relative commutants; irreducibility/Schur/purity; superselection; GNS covariance; disjointness/quasi-equivalence/centre; direct sums; covariant states/vacuum/positive energy; separating vector; KMS for the covariance flow) | Manual HaagKastler (Representations and local von Neumann algebras; Symmetry and states) and Manual GNS (Irreducibility, Equivalence and disjointness, Direct sums, Covariance) | ALREADY (pure-state existence: see S-2) |
| 6p | §10.6.15 KMS condition (no unbounded theory needed; Strip–Liouville route; automatic invariance) | Manual HaagKastler › Symmetry and states | PARTLY: one sentence says the invariance of a KMS state is in `AQFT/KMS.lean`; the Strip–Liouville route is in the Blueprint only. Acceptable as is. |
| 6q | Where the Lean lives | Manual HaagKastler and GNS › Where to look | ALREADY |
| 6r | Items + nav | Dropped | n/a |

(6d–6o count as 13 units, one per subsection bullet.)

### §10.7 Curved (`sec10-7-curved.md`)
| ID | Unit | Destination | Status |
|---|---|---|---|
| 7a | "52 items… abstract Lorentzian spacetime interface… no coherence hypothesis is needed… explicit hypothesis remains only… Theorem 665" | Manual Curved › Overview + Design | PARTLY: interface, bridge, and "no result assumes the factorisation separately" ALREADY; the single remaining explicit hypothesis (basis-set preservation in Geometric Covariance, Theorem 665) is not named; Design names `commute_of_spacelike_mono` as its example of a hypothesis. Minor. |
| 7b–7h | §10.7.1–10.7.7 | Manual Curved › Main definitions (Einstein causality and local vN algebras; Stabilisers, covariant states and KMS states) | ALREADY (10.7.7: stale claim, see S-3) |
| 7i | Where the Lean lives | Manual Curved › Where to look | ALREADY |
| 7j | Items + nav | Dropped | n/a |

### §10.8 General covariance (`sec10-8-general-covariance.md`)
| ID | Unit | Destination | Status |
|---|---|---|---|
| 8a | "Two definitions. The gauge group… hole argument… Leibniz equivalence… carriers related by data… postulate… geometric not causal (dilations)… ψ not the identity… not a sixth field" | Manual Curved › Design › "General covariance relates nets over different spacetimes" | ALREADY (hole argument and Leibniz equivalence are in Blueprint §10.8 only; the manual says "describe the same physics", which suffices) |
| 8b | Where the Lean lives | Manual Curved › Where to look | ALREADY |
| 8c | Items + nav | Dropped | n/a |

## Gaps

Content not covered at its destination that should be kept:

1. **Landing: status section, generated** (I6, I7, I8, I14). One table per Chapter 10 section,
   showing declarations by kind and the number formalised, with the totals and the number of
   distinct Lean declarations. Below it, a sentence: every entry is formalised, statements and
   proofs, with no `sorry`; the standard results the blueprint quotes without proof are linked to
   the Mathlib declarations that supply them; Conventions 22/213/260 are numbered but are not
   declarations. Then one line linking the single implementation choice (the curved Axiom 5 group)
   to Manual Conventions › Implementation choices. Section rows link to the manual chapters.
2. **Landing: Highlights** (I10–I13). Four short entries: each names the headline theorem or
   structure, gives its Lean name, and links to the manual chapter and the API docs.
   Minkowski net (`HaagKastlerNet`, four fields; Axiom 4 is `ObservableCorrespondence`;
   `exists_quasilocalAlgebra`), curved net (`HaagKastlerCurved.HaagKastlerNet`,
   `IsGenerallyCovariant`), the bounded spectral theorem (`existsUnique_spectralMeasure`), and the
   unbounded spectral theorem (`existsUnique_spectralMeasure_unbounded`). Fix the wording in S-1.
3. **Landing: acknowledgements and maintainer** (I19, I20, I1). Copy the README text, which
   includes Project Numina, plus "Maintained by Kelly J Davis".
4. **Landing: links and attribution of the 1964 paper** (I3, I16). Add a sentence to "About" that
   names Haag and Kastler (1964) and links the DOI. Add the dependency graph to the footer's
   "Project" column, or to a links list.
5. **Manual Conventions › "How the blueprint and the Lean fit together": a blueprint chapter map**
   (G3, G4, I5). Add a list with one line per blueprint chapter 1–9, giving the axiom it discusses
   and the point it settles (topology; diamonds; the unit; where commutation happens; the
   quasilocal algebra and density; the extension of the action by BLT; primitivity dropped;
   curved spacetime and Schwarzschild). Add one sentence: items 1–12 are background results quoted
   in chapters 4–9 and have no Lean declaration. This replaces the link to `guide.html`.
6. **Manual Conventions: replace the "section pages" sentence** (G5). Say instead that the
   blueprint's `\lean` annotations, its index and the dependency graph list every entry with its
   declarations. Each manual chapter opens its subsections with the entries they cover.
7. Optional, low priority: name the basis-set-preservation hypothesis of the curved Geometric
   Covariance theorem in Manual Curved › Design (7a).

Links that must change when the pages go, besides the redirects. These are not content gaps.
- `web/Manual/Conventions.lean:31` (`guide.html`), `:46` (`sec10-5-spacetime.html`, "section pages" sentence)
- "Where to look" footers linking section pages: `Manual/GNS.lean:677-678`, `Spectral.lean:640`,
  `Unbounded.lean:705`, `Stone.lean:577`, `Spacetime.lean:885`, `HaagKastler.lean:729`,
  `Curved.lean:655-656`. They can be removed, since the blueprint section links beside them remain.
- `web/Site/FrontPage.lean:54,67`: the gallery tabs link to `sec10-5-spacetime.html` and
  `sec10-6-haag-kastler.html`. Repoint them to the Spacetime and Haag–Kastler manual chapters, via
  `manualChapterUrl`.
- `web/Tutorial/DoingItYourself.lean:185-186`: the `home_page/` bullet in "Where things are".
- `guide.md` links `./#formalisation-status`. That anchor should exist on the new landing status
  section.

## Possibly stale or wrong facts

- **S-1 (wrong for Minkowski).** `axioms.md` ("The five sharpened axioms in each setting, bundled
  together as a `HaagKastlerNet`") and Highlight I10 ("Five axioms… They are bundled as a
  Haag–Kastler net") are wrong for Minkowski. `Physicslib4/AQFT/HaagKastler/Net.lean`
  `HaagKastlerNet` has four fields (U, isotony, localCommutativity, lorentzCovariance), and Axiom 4
  is the separate `ObservableCorrespondence`, as Manual HaagKastler states ("bundles the four").
  The curved net does bundle five (`localAlgebra` field).
- **S-2 (overclaim).** `sec10-6` §10.6.8 says weak-* compactness of the state space (Theorem 566)
  "supplies the existence of pure states via Krein–Milman". The existence of pure states is not
  proved: Manual NotProved names it first, and `GNS/PureStateExists.lean` proves only the
  compactness. The blueprint's wording is "the analytic input for".
- **S-3 (wrong).** `sec10-7` §10.7.7 says KMS states for a Killing flow "are the precise algebraic
  sense in which the Hartle–Hawking and Gibbons–Hawking states are thermal". The blueprint
  (§10.7.7 motivation) and Manual Curved / Conventions say those examples are *not* instances: the
  regions are not diamonds, and no such flow fixes a nonempty diamond.
- **S-4 (minor).** The `guide.md` "Where the Lean lives" row for §10.3 omits `FunctionalCalculus`.
  The sec10-3 page and the manual include it.
- **S-5 (divergence).** The `index.md` Acknowledgements omit Project Numina, which README includes.
- Counts, page numbers, item numbers and the version (v4.35.0) are all correct as of today. They
  are dropped or generated, so they cannot go stale after the switch.

## Redirects

Slugs taken from `web/_out/manual/html-multi/`. Paths are relative to the Pages root
`/physicslib4/`, after stage 4.

| Old URL | Target | Note |
|---|---|---|
| `index.html` / `/` | `/` (Verso landing) | Same path. `#formalisation-status` should resolve on the new status section. |
| `site/` | `/` | Per plan. |
| `guide.html` | `manual/Conventions-and-design-decisions/#conventions-blueprint` | The plan says tutorial. Recommend the manual section, which receives the guide's content (gap 5). Fallback: `tutorial/`. |
| `axioms.html` | `manual/Haag-Kastler-axioms-in-Minkowski-spacetime/` | Per plan. Alternatively `manual/Conventions-and-design-decisions/#conventions-axioms`, which covers both settings and the design notes. |
| `sec10-1-gns.html` | `manual/The-GNS-construction/` | |
| `sec10-2-spectral.html` | `manual/Bounded-spectral-theory/` | |
| `sec10-3-unbounded.html` | `manual/Unbounded-operators-and-their-spectral-theorem/` | |
| `sec10-4-stone.html` | `manual/Stones-theorem/` | |
| `sec10-5-spacetime.html` | `manual/Spacetime-and-geometry/` | |
| `sec10-6-haag-kastler.html` | `manual/Haag-Kastler-axioms-in-Minkowski-spacetime/` | |
| `sec10-7-curved.html` | `manual/The-axioms-in-curved-spacetime-and-general-covariance/` | |
| `sec10-8-general-covariance.html` | `manual/The-axioms-in-curved-spacetime-and-general-covariance/#physicslib4-reference-manual--The-axioms-in-curved-spacetime-and-general-covariance--Design--General-covariance-relates-nets-over-different-spacetimes` | The manual has no §10.8 chapter. |

Total: 12 redirect pages (11 old Jekyll pages plus `site/`). `index.html` stays at the root as the
new page and needs no redirect. `404.html` is replaced, not redirected.

## Summary

Units audited: 110 (index 20, guide 8, axioms 8, section pages 74).

| Destination | Units | ALREADY | PARTLY | NOT |
|---|---|---|---|---|
| Landing | 15 | 2 | 8 | 5 |
| Tutorial | 1 | 1 | 0 | 0 |
| Manual | 76 | 70 | 5 | 1 |
| Blueprint | 2 | 2 | 0 | 0 |
| README | 1 | 1 | 0 | 0 |
| Dropped | 15 | n/a | n/a | n/a |

Reasons for the 15 Dropped units: a superseded page count (I4); a duplicate of the Overview (G2);
Jekyll navigation (G1, G8, A1); retired section-page index (G5, G6); and the item lists of the
eight section pages, which the manual and the blueprint's own index and `\lean` annotations
replace.

Gaps, by priority:
1. Landing: generated status section.
2. Landing: Highlights.
3. Landing: acknowledgements and maintainer, from README.
4. Landing: the 1964 paper link and the dependency graph.
5. Manual Conventions: the blueprint chapter 1–9 map, and the note that items 1–12 have no Lean.
6. Manual Conventions: replace the "section pages" sentence.
7. Optional: Manual Curved, the Theorem 665 hypothesis.

Plus 13 in-site links to Jekyll pages, and one tutorial bullet, to update.

Stale or wrong facts:
- S-1: the Minkowski `HaagKastlerNet` is described as bundling five axioms; it bundles four.
- S-2: pure-state existence via Krein–Milman is claimed; it is not proved.
- S-3: the Hartle–Hawking and Gibbons–Hawking states are claimed as instances of the Killing-flow
  KMS definition; they are not.
- S-4: the guide's module table omits `FunctionalCalculus`.
- S-5: the home page's acknowledgements omit Project Numina.

Redirect table: 12 entries, above. The recommended `guide.html` target differs from the plan.
