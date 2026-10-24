# Plan: the reference manual's conventions chapter

Follows `plan-verso-reference-manual-2026-10-17.md` (decision 4: the conventions chapter comes last). The
other seven chapters are committed (GNS, bounded and unbounded spectral theory, Stone's theorem,
spacetime, the Minkowski axioms, curved spacetime and general covariance).

## Decisions recorded (2026-10-24)

1. The chapter goes last in the book, linked from the title page and from each chapter's Design section.
2. The "not proved" list (section 7) becomes a short separate appendix, because it is likely to change.
   The conventions chapter links to it.
3. Plain descriptions only; no internal decision labels (D1, D3, D8).

First half (sections 1–4) started 2026-10-24; log: `manual-ch-conventions-progress.md`.

## Purpose

One place that collects the library's design decisions and conventions. The other chapters each
mention a few of them where they arise; this chapter states each one once, says why it is made, and
links to where it matters. A reader who knows AQFT but not this library reads it first or second, so
it goes **last in the book but is linked from the title page and from each chapter's Design
section**.

No new docstring pass is needed: the chapter has no definitions of its own, and shows declarations only
through `#check` or links.

## Sections

1. **How the blueprint and the Lean fit together.**
   - The blueprint is the specification, and only Chapter 10 is formalised.
   - Labels, `\lean{}`, `\leanok` and `\uses{}`, and the docstring "Blueprint:" lines.
   - Formalization notes, where a Lean proof takes a different route from the blueprint.
   - `**Restriction:**` lines: the library has none at present, and the chapter says what one would
     mean.
   - Present-tense documentation, and where history is kept (`CHANGELOG.md`).
2. **Sign and notational conventions.**
   - Metric signature (−,+,+,+).
   - Time translations as U(a) = e^(iP·a), so the time-translation unitaries are e^(itĤ).
   - The generator conventions of Stone's theorem.
   - Notation shared by the blueprint and the Lean: 𝔘(B), ≺, ≪, I±, J±.
3. **Causal structure.**
   - Causal precedence is reflexive (`ReflTransGen`, Hawking–Ellis); `IsCausalTrip` is strict.
   - What follows: p ∈ J±(p), and no point is spacelike-related to itself.
   - Paths have nowhere-vanishing velocity, with the trivial case p = q in place of degenerate curves.
   - Diamonds and the intersection-property hypothesis `hdir`: it holds in every spacetime in the
     standard theory, but is not proved in the library.
   - The ∞ versus ω smoothness note.
   - Source: the material moved out of the spacetime chapter (`manual-ch-spacetime-progress.md`, from
     l. 247), shortened.
4. **The axiom structures.**
   - Regions are Alexandrov diamonds.
   - Isotony is data (embeddings), not a property.
   - Axiom 3 is stated inside a common containing diamond, in Minkowski and curved spacetime alike.
   - The quasilocal algebra is a completion. It exists in Minkowski spacetime but need not exist in
     curved spacetime.
   - Covariance under the identity component.
   - KMS states and flows act on diamonds only. The Killing-flow examples (black-hole exterior, de
     Sitter static patch) motivate the definitions but are not instances of them, and this is kept
     deliberately.
5. **Universes.**
   - GNS Hilbert spaces live in the universe of the algebra, `Type u` (D1).
   - The curved net's algebras live in their own universe, `Type v` (D8).
   - The trivial nets sit in universe 0.
   - What this means for a reader writing their own net.
6. **Implementation choices.**
   - The oriented identity component in curved Axiom 5 (D3): an implementation choice, not a
     restriction; the equality needs a Myers–Steenrod-type theorem.
   - Mathlib's conventions the library inherits:
     - `LinearPMap` and its adjoint, which is zero on its domain;
     - the measurability guard and junk value in `integralApply`;
     - `IsIrreducible` counting the zero representation, kept deliberately;
     - `realCalculus` as Mathlib's `cfcHom`;
     - GNS via Mathlib's construction.
7. **What is not proved in the library.** One list of the standard facts the chapters mark as not
   proved:
   - Reeh–Schlieder;
   - the existence of pure states;
   - the intersection property for general spacetimes;
   - the spectral theorem for unbounded normal operators;
   - the Hartle–Hawking and Bunch–Davies states as KMS states.

   Each item links to where it matters. The list makes clear where the library stops.

Target: about 3,000 words. Mostly prose with links; few `#check`s.

## Process (as for the other chapters)

1. One writer drafts the chapter in two halves (sections 1–4, then 5–7), with a log entry after each
   section. Budget allowing, the halves go in separate sessions.
2. Then:
   - add the chapter to `web/Manual.lean` (last, before the draft-only tests) and to `web/README.md`;
   - link it from the title page;
   - add a one-line pointer from each chapter's Design section.
3. A reviewer checks every stated convention against the code and the blueprint, and that the "not
   proved" list is complete and accurate.
4. You read it, then it is committed.

## Questions for you

1. **Placement:** last, as decided, but also linked from the title page and every Design section? Or
   move it to the front of the book now that it exists?
2. **The "not proved" list (section 7):** keep it here, or make it a separate short appendix?
3. **The decision labels (D1, D3, D8):** they are internal names. Should the chapter use plain
   descriptions only? (Proposed: plain descriptions only.)
