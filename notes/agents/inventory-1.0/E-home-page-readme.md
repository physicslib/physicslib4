# Inventory E: home page and README (read-only, 2026-10-08)

Scope: `home_page/**/*.md`, `home_page/**/*.html`, `home_page/_config.yml`, `README.md`. Section pages: front matter and overview prose above "## Items", plus grep of the item lists.

| file:line | exact quoted phrase | category | action | replacement |
|---|---|---|---|---|
| home_page/index.md:68 | "**Recently completed: Stone's Theorem.** The new [§10.4](sec10-4-stone.html) (Definition 289 through Theorem 329, pp. 236–249) proves Stone's Theorem" | change-notice | replace | replace by Highlights (D8) |
| home_page/index.md:68 | "and four new §10.3 nodes supply what it needs" | change-notice | replace | replace by Highlights (D8) |
| home_page/index.md:68 | "positive energy (the spectrum condition behind vacuum and ground states) is now stated with a genuine unbounded generator" | change-notice | replace | replace by Highlights (D8) |
| home_page/index.md:68 | "The former bounded-generator restriction is gone, and the project records no remaining restrictions." | history | replace | replace by Highlights (D8); if a status sentence is wanted elsewhere: "The project records no `**Restriction:**` lines." |
| home_page/index.md:70 | "**Recently completed: smoothness of the inverse musical isomorphism.** Lemma 358 (§10.5, p. 255), the last unformalised node, states" | change-notice | replace | replace by Highlights (D8) (not one of the four D8 highlights; drop) |
| home_page/index.md:72 | "**Recently completed: the von Neumann density theorem.** Theorem 506 ... is now proved." | change-notice | replace | replace by Highlights (D8) (not one of the four D8 highlights; drop) |
| home_page/index.md:72 | "following Murphy, Lemma 4.1.4, in the new §10.6.2 (Lemmas 496–505, Definition 499)" | change-notice | replace | replace by Highlights (D8) |
| home_page/index.md:72 | "Mathlib has the strong operator topology (`PointwiseConvergenceCLM`) and the double commutant property ... but not the density theorem itself" | version-dated | replace | replace by Highlights (D8); undated Mathlib-content claim, goes with the block |
| home_page/index.md:76 | "rests on a Myers–Steenrod-type rigidity result not yet in Mathlib" | version-dated | rewrite | "rests on a Myers–Steenrod-type rigidity result that the project does not formalise." |
| home_page/index.md:66 | "There is one place where the Lean is deliberately shaped differently from the prose; it is flagged in the blueprint text itself and collected here so that it is not discovered by surprise." | rationale | keep | present tense already; keep |
| home_page/index.md:86-93 | "## Contributing" (no version line present) | version-dated | add | D6 web line: "This project targets Lean and Mathlib v4.34.1, as pinned by `lean-toolchain` and `lakefile.toml`." (only version string on the web pages) |
| home_page/axioms.md:35 | "Three changes to the axioms are worth calling out for readers coming from an earlier version of this blueprint:" | change-notice | rewrite | → Design notes (D8). Heading "## Design notes" and lead: "Three design choices in the axioms are worth noting:" |
| home_page/axioms.md:37 | "**Isotony now supplies its embeddings as data.**" | change-notice | rewrite | → Design notes (D8). "**Isotony supplies its embeddings as data.**" |
| home_page/axioms.md:37 | "and Axiom 5 (Definitions 507 and 632) now states its coherence condition for the same family" | change-notice | rewrite | → Design notes (D8). "and Axiom 5 (Definitions 507 and 632) states its coherence condition for the same family" |
| home_page/axioms.md:37 | "and it removes the coherence side-hypotheses that curved-spacetime statements about nested regions previously had to carry." | history | rewrite | → Design notes (D8). "and it means that curved-spacetime statements about nested regions carry no coherence side-hypotheses." |
| home_page/axioms.md:38 | "Definition 485 now requires completely spacelike local algebras to commute in every local algebra" | change-notice | rewrite | → Design notes (D8). "Definition 485 requires completely spacelike local algebras to commute in every local algebra" |
| home_page/axioms.md:38 | "The former statement, commutation in the quasilocal algebra, is now Lemma 487 (`...localCommutativity_iff_exists_commute_ι`), proved equivalent." | history | rewrite | → Design notes (D8). "Commutation in the quasilocal algebra is an equivalent form, Lemma 487 (`Physicslib4.AQFT.HaagKastler.localCommutativity_iff_exists_commute_ι`)." |
| home_page/axioms.md:39 | "**Axiom 4 has been split.** The mathematical claim that a quasilocal algebra exists is now Theorem 490" | change-notice | rewrite | → Design notes (D8). "**Axiom 4 is a bridge principle; the quasilocal algebra is a theorem.** That a quasilocal algebra exists is Theorem 490" |
| home_page/axioms.md:39 | "what remains as Axiom 4 (Definition 489) is the bridge principle relating physical observables to quasilocal ones" | history | rewrite | → Design notes (D8). "Axiom 4 (Definition 489) is the bridge principle relating physical observables to quasilocal ones" |
| home_page/axioms.md:11 | "Axiom 6 (Primitivity) from the original 1964 Haag–Kastler paper is not carried into the sharpened axiom set" | rationale | keep | refers to the 1964 paper, not a project version; keep |
| home_page/axioms.md:33 | "**General Covariance ...** is deliberately *not* a sixth axiom." | rationale | keep | present-tense design rationale; keep (could move under Design notes) |
| home_page/guide.md:29 | "this axiom is ultimately abandoned in the sharpened formulation, following later presentations by Haag himself" | rationale | keep | literature history, not project history; optional: "this axiom is not part of the sharpened formulation, following later presentations by Haag himself" |
| home_page/guide.md:32-34 | "The lower numbers, 1 through 12, appear in these chapters:" followed by "The lower numbers, 1 through 12, label supporting theorems" | process | delete | — (delete) line 32 (duplicated lead-in, editing leftover; not temporal) |
| home_page/guide.md:38 | "running from Definition 13 through Definition 678" | process | rewrite | "from Definition 13 through Definition 677" (index.md:32 and guide.md:16 say 677; consistency fix, not temporal) |
| home_page/sec10-3-unbounded.md:19 | "Added for §10.4. The spectral measure of a self-adjoint operator is named (Definition 286)" | change-notice | rewrite | "These items supply what §10.4 needs. The spectral measure of a self-adjoint operator is named (Definition 286)" |
| home_page/sec10-3-unbounded.md:19 | "Earlier in the section, a self-adjoint operator is shown to have no proper symmetric extension (Lemma 189)" | positional-keep | keep | — |
| home_page/sec10-3-unbounded.md:17 | "Combined with the previous stage, this gives the Spectral Theorem for Bounded Normal Operators" | positional-keep | keep | — |
| home_page/sec10-5-spacetime.md:12 | "(Mathlib itself has only a Riemannian Levi-Civita connection and no geodesics)" | version-dated | rewrite | "(the pseudo-Riemannian Levi-Civita connection and geodesics are constructed in this project)" — or delete the parenthesis |
| home_page/sec10-5-spacetime.md:15 | "A new layer. Pseudo-Riemannian metrics (Definition 354) are smooth" | change-notice | delete | — (delete) "A new layer." |
| home_page/sec10-5-spacetime.md:19 | "Upward-directedness is what the quasilocal colimit of §10.6.1 later consumes." | positional-keep | keep | — |
| home_page/sec10-5-spacetime.md:22 | "with the two round-trip cancellation identities that Mathlib does not supply for a global `Diffeomorph` proved by hand (Lemmas 437–439)" | version-dated | rewrite | "with the two round-trip cancellation identities for a global `Diffeomorph` proved directly (Lemmas 437–439)" |
| home_page/sec10-6-haag-kastler.md:14 | "Axiom 2 (Isotony, Definition 468) now supplies the family of unital \*-monomorphisms" | change-notice | rewrite | "Axiom 2 (Isotony, Definition 468) supplies the family of unital \*-monomorphisms" |
| home_page/sec10-6-haag-kastler.md:14 | "equivalent to commutation in some quasilocal algebra, the form used by earlier versions of this blueprint (Lemma 487)" | history | rewrite | "equivalent to commutation in some quasilocal algebra (Lemma 487)" |
| home_page/sec10-6-haag-kastler.md:14 | "**Axiom 4 is now split in two.**" | change-notice | delete | — (delete); following sentence already states the bridge principle in present tense |
| home_page/sec10-6-haag-kastler.md:14 | "The mathematical content previously conflated with it is separated out as a theorem: every local net satisfying Axiom 2 admits a quasilocal algebra" | history | rewrite | "The mathematical content is a theorem: every local net satisfying Axiom 2 admits a quasilocal algebra" |
| home_page/sec10-6-haag-kastler.md:14 | "the blueprint records why the shortcut of realising $$\mathfrak{U}$$ as a closed \*-subalgebra of an ambient C\*-algebra is rejected" | rationale | keep | present tense already; keep |
| home_page/sec10-6-haag-kastler.md:15 | "A new subsection of general operator theory for a unital \*-homomorphism" | change-notice | rewrite | "A subsection of general operator theory for a unital \*-homomorphism" |
| home_page/sec10-6-haag-kastler.md:15 | "Mathlib lacks the density theorem, so it is proved here following Murphy, Lemma 4.1.4." | version-dated | rewrite | "The density theorem is proved here following Murphy, Lemma 4.1.4." |
| home_page/sec10-6-haag-kastler.md:15 | "turns this into the density theorem (Theorem 506), now fully proved." | change-notice | rewrite | "turns this into the density theorem (Theorem 506)." |
| home_page/sec10-6-haag-kastler.md:15 | "$$\pi_\omega(\mathfrak{U})$$ is strongly dense in $$\pi_\omega(\mathfrak{U})$$" | process | rewrite | "... strongly dense in $$\pi_\omega(\mathfrak{U})''$$" (typo: bicommutant primes missing; not temporal) |
| home_page/sec10-6-haag-kastler.md:16 | "whose coherence condition is now stated for the Axiom 2 isotony family itself" | change-notice | rewrite | "whose coherence condition is stated for the Axiom 2 isotony family itself" |
| home_page/sec10-6-haag-kastler.md:19 | "A new block organising the theory of inclusions" | change-notice | rewrite | "Organises the theory of inclusions" |
| home_page/sec10-6-haag-kastler.md:22 | "A new block. Cyclicity pulls back along a surjective \*-homomorphism (Lemma 556)" | change-notice | delete | — (delete) "A new block." |
| home_page/sec10-6-haag-kastler.md:25 | "is automatically covariance-compatible (Lemma 588, new)" | change-notice | rewrite | "is automatically covariance-compatible (Lemma 588)" |
| home_page/sec10-7-curved.md:12 | "Local Commutativity (Definition 629, which now **consumes** the Axiom 2 family rather than choosing its own witnesses)" | change-notice | rewrite | "Local Commutativity (Definition 629, which **consumes** the Axiom 2 family rather than choosing its own witnesses)" |
| home_page/sec10-7-curved.md:12 | "The change to Axioms 2 and 3 has a visible consequence downstream:" | change-notice | rewrite | "This form of Axioms 2 and 3 has a visible consequence downstream:" |
| home_page/sec10-7-curved.md:12 | "and that factorisation is now the composition law of Axiom 2, so **the coherence hypotheses that earlier versions carried at each such site are gone**—curved isotony" | history | rewrite | "and that factorisation is the composition law of Axiom 2, so **no coherence hypothesis is needed at any such site**—curved isotony" |
| home_page/sec10-7-curved.md:12 | "the coherence of the stabiliser action with the isotony embeddings is no longer a hypothesis there, being condition (3) of Axiom 5" | change-notice | rewrite | "the coherence of the stabiliser action with the isotony embeddings is not a hypothesis there: it is condition (3) of Axiom 5" |
| home_page/sec10-8-general-covariance.md:12 | "Two definitions, and the newest structural addition to the blueprint." | change-notice | rewrite | "Two definitions." |
| home_page/_config.yml:3 | "This config file is meant for settings that affect your whole blog" | blog | rewrite | "This config file holds settings that affect the whole site" (Jekyll boilerplate comment; not rendered, but D5 forbids "blog" wording) |
| home_page/_config.yml:24 | "baseurl: \"\" # the subpath of your site, e.g. /blog" | blog | rewrite | "baseurl: \"\" # the subpath of the site, e.g. /docs" (comment only) |
| home_page/_config.yml:31 | "remote_theme: pages-themes/cayman@v0.2.0" | version-dated | keep | configuration, not documentation (D6 exempts configuration); keep |
| home_page/_config.yml:23 | "description: by KellyJDavis" | process | keep | rendered tagline; not temporal. Optional consistency with index.md front matter: "by Kelly J Davis" |
| home_page/_includes/mathjax.html:14 | "MathJax 3 from the jsDelivr CDN (the old cdn.mathjax.org has been retired)." | history | rewrite | "MathJax 3 from the jsDelivr CDN." (HTML comment; not rendered) |
| home_page/404.html | (no hits) | — | none | — |
| home_page/_layouts/default.html | (no hits) | — | none | — |
| README.md:48-50 | "Requires [Lean 4](...) and [Mathlib4](...)." (no version stated) | version-dated | add | D6 code line: "Requires Lean 4 and Mathlib, both at v4.34.1, as pinned by `lean-toolchain` and `lakefile.toml`." (only version string in README) |
| README.md:13 | "## Current Focus: AQFT in Minkowski and Lorentzian Spacetime" | process | keep | present tense; optional: "## AQFT in Minkowski and Lorentzian Spacetime" |
| README.md:15 | "The current work formalises **Algebraic Quantum Field Theory (AQFT)**" | process | rewrite | "physicslib4 formalises **Algebraic Quantum Field Theory (AQFT)**" |
| README.md:61 | "The blueprint is the canonical guide to what has been stated, what has been proved, and what remains open." | process | rewrite | "The blueprint is the canonical guide to what is stated and what is proved." (every Chapter 10 node is formalised; nothing remains open) |
| README.md:63 | "to find items not yet linked to Lean proofs." | process | rewrite | "to see how each item is linked to its Lean declarations." |
| README.md:73 | "Maintained by [Kelly J Davis](https://github.com/kellyjdavis). Started June 2026." | history | rewrite | "Maintained by [Kelly J Davis](https://github.com/kellyjdavis)." (start date to CHANGELOG) |
| README.md:29 | "The repository is therefore designed to grow. Future work may include, for example:" | rationale | keep | forward-looking scope, not backward-looking; keep |

Notes:
- Section-page item lists (below "## Items") have no hits for "(new)", "new", "previously", "now", "formerly", "no longer", "earlier", "version", "not yet" or version strings. All hits are in the overview prose.
- §10.1, §10.2 and §10.4 overview prose: no temporal wording.
- No version string (Lean, Mathlib, `v4.`) appears anywhere in `home_page/*.md` or `README.md` today. D6 therefore needs two additions (index.md "Contributing", README "Getting Started"), not removals. The only version strings in scope are `cayman@v0.2.0` (config, keep) and `mathjax@3` (CDN URL, keep).
- Rows tagged `process` with "not temporal" are editorial defects found along the way (a duplicated line in guide.md, Definition 678 vs 677, missing `''` in sec10-6), not backward-looking wording.

## To CHANGELOG

- Stone's Theorem (§10.4, Definition 289 to Theorem 329) and the four §10.3 nodes it uses (Lemma 189, Definitions 286–287, Lemma 288) are added. Positive energy (Theorem 603) moves from a bounded generator to an unbounded self-adjoint generator, and the bounded-generator `**Restriction:**` is removed, leaving none (index.md:68).
- Lemma 358 (smoothness of the inverse musical isomorphism), the last unformalised node, is formalised (index.md:70).
- The von Neumann density theorem (Theorem 506) is proved, with §10.6.2 (Lemmas 496–505, Definition 499) added. Mathlib did not have it at the time (index.md:72; sec10-6:15).
- The Levi-Civita connection and geodesics layer (§10.5, items 354–369) is added (sec10-5:15).
- Isotony (Axiom 2) supplies its embeddings as data. Axiom 3 consumes that family, and Axiom 5's coherence condition is restated for it. The curved-spacetime coherence side-hypotheses are removed (axioms.md:37; sec10-6:14,16; sec10-7:12).
- Minkowski Axiom 3 is restated in a common containing diamond. The earlier quasilocal-algebra form becomes Lemma 487 (axioms.md:38; sec10-6:14).
- Axiom 4 is split: quasilocal existence becomes Theorem 490, and Axiom 4 (Definition 489) stays as the bridge principle (axioms.md:39; sec10-6:14).
- New blocks: §10.6.6 relative commutants, §10.6.9 GNS covariance, Lemma 588. §10.8 general covariance is the latest structural addition (sec10-6:19,22,25; sec10-8:12).
- The MathJax CDN moves from cdn.mathjax.org to jsDelivr (mathjax.html:14).
- The project started in June 2026 (README.md:73).

## Totals

- Rows: 63 (index.md 11, axioms.md 10, guide.md 3, sec10-3 3, sec10-5 4, sec10-6 13, sec10-7 4, sec10-8 1, _config.yml 4, mathjax.html 1, 404/default.html 2 no-hit, README.md 7).
- By category: change-notice 25, history 9, process 8, version-dated 8, rationale 6, blog 2, positional-keep 3, no-hit 2.
- By action: rewrite 35, replace 8 (all "replace by Highlights (D8)", index.md:68–72), delete 4, add 2 (D6 version lines), keep 12, none 2.
- "→ Design notes (D8)": 8 rows (axioms.md:35–39).
- Retractions: 0. Blog references in rendered text: 0 (2 in `_config.yml` comments).
