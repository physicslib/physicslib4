# Plan: the reference manual (the second Verso book)

Follows the tutorial (chapters 1–4, ending at `df94e92`) and the decisions in
`scout-verso-site-2026-10-14.md`: two books, the Lean FRO theme, served at `/manual/`.

## Decisions recorded (2026-10-17)

1. Declarations are shown with option (c): `{docstring}` for definitions and structures, whose
   docstrings are made reader-facing chapter by chapter, and `#check` with the manual's own prose for
   theorems.
2. Scope: headline definitions and theorems, with links to the API docs for everything else.
3. Chapter order as proposed: 6, 5, 1, 7–8, 2–4, then 9.
4. The conventions chapter comes last.
5. When Jekyll is retired, the manual replaces the home page's section pages.

## Purpose and difference from the tutorial

The tutorial teaches. The manual is consulted. A reader who knows the material comes to the manual
to find out how the library encodes a piece of mathematics: which definitions exist, why they take
the form they do, which theorems are proved, where they live, and how they map to the blueprint.

- **Organised by topic,** one chapter per Chapter 10 section, not by learning order.
- **No exercises.** Short examples only where they show how to use an API.
- **The same prose rules as the tutorial:**
  - written for a first-year theoretical-physics PhD student;
  - crisp and straightforward;
  - present tense;
  - familiar material opens with a reminder ("As you will recall, ...").

  It is denser than the tutorial, since the reader is assumed to have read the tutorial or to know
  the field.
- **Kept current by the build.** Every declaration named is elaborated by Verso, so renames and
  changes in the library break the manual's build rather than going stale.

## Chapters (one per Chapter 10 section)

1. **The GNS construction:** states, null spaces, the construction and its uniqueness, cyclic and
   separating vectors, purity and irreducibility, direct sums.
2. **Bounded spectral theory:** the continuous and Borel functional calculi, projection-valued
   measures, and the spectral theorem.
3. **Unbounded operators and their spectral theorem:**
   - domains, adjoints and self-adjointness;
   - integration against a projection-valued measure;
   - normal operators and the Cayley transform.
4. **Stone's theorem:** one-parameter unitary groups, generators, exponentials, and the theorem.
   Positive energy.
5. **Spacetime and geometry:**
   - spacetimes and Minkowski space;
   - causal structure, with ≺ reflexive and `IsCausalTrip` strict;
   - diamonds and the Alexandrov topology, causal complements;
   - the Lorentz group;
   - the pseudo-Riemannian layer, the Levi-Civita connection and geodesics.
6. **The Haag–Kastler axioms in Minkowski spacetime:**
   - `LocalNet`, `Isotony`, `LocalCommutativity`, `LorentzCovariance` and `HaagKastlerNet`;
   - the quasilocal algebra, local von Neumann algebras and the density theorem;
   - vacuum states and KMS states.
7. **The axioms in curved spacetime:** the abstract `LorentzianSpacetime` interface, the concrete
   bridge (`toAbstractIdentityComponent`), and the stabilizer actions.
8. **General covariance.**
9. **Conventions and design decisions,** collected in one place:
   - the universe choices (D1, D8);
   - reflexive causal precedence;
   - isotony as data;
   - Axiom 3 in a common diamond;
   - the oriented identity component (the D3 note);
   - `**Restriction:**` lines;
   - how blueprint labels map to Lean names.

Each chapter follows the same pattern:

1. **Overview:** what the section formalises and its main results.
2. **Design:** why the definitions take their form, with links to the decisions recorded in the
   repository.
3. **Main definitions and theorems:** grouped, each named and elaborated, with a one- or two-line
   explanation and a link to its blueprint node.
4. **Where to look:** the files and modules.

Target: about 2,500–4,000 words per chapter, or about 25,000–30,000 words for the whole book. That
is several writer sessions.

## Infrastructure (stage 0, one agent)

- **The book:**
  - a `VersoManual` book with its own executable (`generate-manual`), sharing the tutorial's theme,
    header and navigation;
  - served at `/physicslib4/manual/`;
  - the website's "Reference manual" link and its placeholder page are replaced.
- **CI and docs:**
  - both workflows build the manual, filtered by changed paths;
  - `home_page/manual/` is added to `.gitignore`;
  - `web/README.md` is updated.
- **Declaration listings.** The tutorial replaced docstring boxes with checked structure excerpts
  because many docstrings are written for developers. The manual needs a choice; see question 1.
- **Build time.** The manual imports the whole library, so expect several seconds of elaboration per
  chapter. Check the CI time after stage 0.

## Process

- Stage 0: the infrastructure, with a placeholder chapter. One commit.
- Then one chapter per round: a writer drafts section by section with a progress log; a reviewer
  checks it against the Lean and the blueprint; you read it; then commit.
- Suggested order:
  1. 6, the Minkowski axioms, the project's core;
  2. 5, spacetime;
  3. 1, GNS;
  4. 7–8, curved spacetime and general covariance;
  5. 2–4, the spectral theory and Stone's theorem;
  6. 9, conventions, last, collecting what the others refer to.

## Relation to the Jekyll section pages

- The home page's section pages (`home_page/sec10-*.md`) list every blueprint item with its number and
  Lean names.
- The manual's chapters cover the same ground, with explanation added.
- When the Verso site replaces Jekyll, the section pages can be dropped in favour of the manual plus
  the blueprint's own index. The generated item lists would then not need porting.

## Questions for you

1. **Declaration listings.** Options:
   - (a) the library's docstrings embedded with `{docstring}`, which first need a pass to make them
     reader-facing;
   - (b) checked excerpts and `#check`, as in tutorial chapter 2;
   - (c) a mix: docstrings for definitions, `#check` for theorems.

   (a) improves the library's docstrings as a side benefit, but means a docstring pass across the
   library first.
2. **Scope per chapter:** only the headline definitions and theorems, plus pointers to the API docs;
   or every public declaration grouped by topic? The second is closer to a full reference, but much
   longer and partly duplicates doc-gen4.
3. **Chapter order:** is the suggested order right?
4. **The conventions chapter:** last, as proposed, or first, so readers meet the design decisions
   before the details?
5. **The section pages:** should the manual replace them when Jekyll is retired, as proposed?
