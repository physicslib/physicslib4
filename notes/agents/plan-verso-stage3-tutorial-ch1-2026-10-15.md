# Plan: Verso stage 3, tutorial chapter 1 "AQFT in brief"

Follows `scout-verso-site-2026-10-14.md` (decisions and prose style at the end) and stages 1–2
(`verso-stage1-progress.md`, `verso-stage2-progress.md`).

## Decisions recorded (2026-10-15)

1. GNS: sketched with its proof idea (quotient by the null space, completion, cyclic vector).
2. Axiom 6 (primitivity): an aside, not one of the listed axioms.
3. Exercises: one or two per section, with solutions in collapsible blocks.
4. Further reading as proposed, plus arXiv:2410.16599.

Infrastructure started: see `verso-stage3-progress.md`.

## Goal

The first chapter of the tutorial. A reader who knows quantum mechanics and special relativity, but
not algebraic QFT, finishes it knowing:

- what a net of local algebras is;
- what each Haag–Kastler axiom says and why it is there;
- what states and the GNS construction are for;
- what this project sharpens relative to the 1964 axioms.

Lean does not appear yet; it starts in chapter 2. At most, the chapter ends with a short "In the
library" pointer per section, naming the Lean declaration that encodes the idea.

## Audience and style (recorded decisions)

- **Audience:** a first-year PhD student in theoretical physics. Crisp and straightforward, present
  tense. The model is arXiv:2410.16599.
- **Familiar material** opens with a reminder ("As you will recall, ..."):
  - Hilbert spaces;
  - bounded operators and their adjoints;
  - observables as self-adjoint operators;
  - Minkowski space, light cones and causal structure;
  - the Poincaré group.
- **New material** is introduced properly, without the reminder phrase:
  - C*-algebras and *-homomorphisms;
  - states as positive normalised functionals;
  - causal diamonds and the Alexandrov topology;
  - nets, isotony, local commutativity, covariance;
  - the quasilocal algebra;
  - the GNS construction;
  - superselection sectors, in one paragraph.
- **Notation:** follows the blueprint and the Lean:
  - signature (−,+,+,+);
  - $`\mathfrak{U}(\mathbf{B})` for the algebra of a diamond $`\mathbf{B}`;
  - $`\prec` for causal precedence;
  - $`I^{\pm}` for chronological future and past.

## Proposed sections

1. **Why algebras.** In QFT, the fields are operator-valued distributions, and they are not
   observable themselves. The physically meaningful structure is which observables can be measured
   where. Haag's idea is to take that assignment as the primary object.
2. **Regions of spacetime.** A reminder of Minkowski space and causality. Causal diamonds
   $`I^+(p) \cap I^-(q)`, why diamonds rather than arbitrary open sets, and the Alexandrov topology
   that they generate. Reuses the landing page's diamond diagram.
3. **C*-algebras of observables.** A reminder of $`\mathcal{B}(\mathbf{H})`; then the C*-algebra as
   its abstract counterpart; self-adjoint elements as observables.
4. **The axioms.** One short subsection each, each ending with what the axiom rules out physically:
   - Axiom 1, local algebras;
   - Axiom 2, isotony;
   - Axiom 3, local commutativity (Einstein causality), with the diagram;
   - Axiom 4, the quasilocal algebra;
   - Axiom 5, Lorentz covariance;
   - Axiom 6, primitivity.
5. **States and the GNS construction.** States as expectation-value assignments; the GNS
   construction recovers a Hilbert space, a representation and a cyclic vector. The vacuum as an
   invariant state with positive energy. Stone's theorem is mentioned as the link between unitary
   groups and generators, with no proof.
6. **What this project sharpens.** The 1964 axioms leave details open, and the blueprint fixes them:
   - the topology and the class of regions;
   - isotony as embeddings given as data;
   - local commutativity inside a common containing diamond;
   - the curved-spacetime version, where no quasilocal algebra need exist.

   One paragraph on curved spacetime, with a forward pointer.
7. **Further reading.**
   - Haag, *Local Quantum Physics*;
   - Haag and Kastler (1964);
   - Brunetti, Fredenhagen and Verch (2003) for the locally covariant setting;
   - the blueprint chapters.

Target length: about 3,500–4,500 words. Up to two figures: the diamond diagram, and a light-cone
figure for causality.

## Sources

- Blueprint Chapters 1–9 (`blueprint/src/sections/sec1`–`sec9`, about 8,400 words). These are the
  motivation chapters: the original axioms, the topologies on Minkowski space, regions of measurement,
  isotony and GNS, local commutativity, the quasilocal algebra, Lorentz covariance, primitivity, and
  curved spacetime.
- Chapter 10 (`sec10/introduction.tex`, `haag-kastler-axioms.tex`) for the sharpened statements.
- The tutorial paraphrases. It does not copy blueprint statements and does not number items, so it
  does not drift when the blueprint changes (decision 3 in the scout memo).

## Infrastructure (part of this stage)

- The tutorial becomes its own Verso **manual-genre** book at `/tutorial/` (decision 7), replacing
  the stub page in the website. Steps:
  - a `VersoManual` book target in `web/`, alongside the site, with the shared theme;
  - CI builds it into `home_page/site/tutorial/`, or `home_page/tutorial/` per decision 7;
  - the nav link points to it.
- Mathematics renders through Verso's TeX support (KaTeX). Check that it handles
  $`\mathfrak{U}`, $`\mathbf{B}` and the display equations.

## Process

1. **Infrastructure:** one agent sets up the manual book with a placeholder chapter, built locally
   and in CI. One commit.
2. **Draft:** one writer agent drafts chapter 1 from the sources, in the style above, with a progress
   log, section by section.
3. **Review:** one reviewer agent checks the physics and mathematics against the blueprint and
   standard references, the prose against the style rules, and that the HTML renders.
4. **Your review:** you read the rendered chapter. Changes go back to the writer.
5. **Commit:** after your approval.

## Questions for you

1. **Depth of section 5.** Should the GNS construction be sketched with its proof idea (the quotient
   by the null space and completion), or only stated?
2. **Axiom 6 (primitivity).** Keep it in the list as in the blueprint's chapters, or treat it as an
   aside? It is not one of the formalised Chapter 10 axioms in the same form.
3. **Exercises.** End each section with one or two short exercises, without solutions or with
   solutions in a collapsible block, or leave exercises for the Lean chapters?
4. **Citations.** Is the further-reading list above right? Should arXiv:2410.16599 itself be cited?
