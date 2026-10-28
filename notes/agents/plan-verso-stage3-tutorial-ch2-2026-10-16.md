# Plan: tutorial chapter 2, "Lean in brief"

Follows `plan-verso-stage3-tutorial-ch1-2026-10-15.md`. Chapter 1 ("AQFT in brief") is committed
(`413c929`). The same audience, style rules and process apply.

## Decisions recorded (2026-10-16)

1. Section 4 has two fully worked tactic proofs: one algebraic, one about causal structure.
2. Exercises are read-only in the browser; running them locally is left to chapter 4.
3. Universe levels get a short aside.
4. The further-reading list is as proposed.

## Goal

A reader who finished chapter 1 and has never used a proof assistant ends chapter 2 able to:

- read a definition, structure or theorem from this library and say what it means mathematically;
- read a short tactic proof and follow its goals;
- write and check a small statement and proof of their own in the library's setting;
- find existing results in Mathlib and in this library.

The chapter teaches only the Lean needed to read the library. It does not teach Lean in general;
it points to *Theorem Proving in Lean 4* and *Mathematics in Lean* for that.

## Audience and style (as for chapter 1)

- **Audience:** a first-year PhD student in theoretical physics. Crisp and straightforward, present
  tense. The model is arXiv:2410.16599.
- **Familiar material** opens with a reminder ("As you will recall, ..."):
  - sets, functions and logic (quantifiers, implication);
  - proof by cases and by induction;
  - the objects of chapter 1 (nets, isotony, diamonds, states).
- **New material** is introduced properly:
  - types and terms;
  - propositions as types and proofs as terms;
  - dependent functions;
  - structures and type classes;
  - tactics;
  - namespaces;
  - Mathlib.
- **Lean code:** every example is elaborated by Verso when the site is built, with hover information.
  Examples come from the library, or are small self-contained snippets that import `Physicslib4`.

## Proposed sections

1. **What a proof assistant does.** Lean checks every step of a definition or proof against a small
   trusted kernel. What "formalised" and "sorry-free" mean for this library.
2. **Types and terms.**
   - Every object has a type: `ℝ`, `ℂ`, functions, `Set X`.
   - `#check` and `#eval` on familiar examples.
   - Dependent function types, where the type of the output depends on the input, as in "for each
     diamond, an algebra".
3. **Propositions and proofs.**
   - Statements are types, and a proof is a term of that type.
   - `∀`, `∃`, `→` and `↔`, read as in mathematics.
   - `theorem` and `example`.
   - A first proof by `exact` and by `rfl`.
4. **Tactic proofs.**
   - Goals and hypotheses.
   - `intro`, `exact`, `apply`, `constructor`, `rcases`, `simp`, `rw`, `calc`, `linarith`.
   - One worked proof from the library, shown step by step with the goal after each tactic.
     Candidate: a short lemma about causal precedence or isotony.
5. **Structures and type classes.**
   - How a mathematical structure with axioms becomes a Lean `structure` with fields.
   - The running example is the library's `LocalNet` (`AQFT/HaagKastler/LocalAlgebras.lean:79`) and
     `Isotony` (`Isotony.lean:61`): the fields are the data and the axioms of chapter 1.
   - Type classes such as `CStarAlgebra A`: how Lean finds the C*-structure on `A` by itself.
   - `HaagKastlerNet` (`Net.lean:71`) bundles the axioms.
6. **Definitions that are propositions.**
   - `LocalCommutativity` (`LocalCommutativity.lean:64`) is a `def` whose value is a `Prop`.
   - Reading it line by line against Axiom 3 of chapter 1.
   - `IsAlexandrovBasisSet` (`LocalAlgebras.lean:62`) for diamonds.
   - `Physicslib4.GNS.State` (`GNS/Basic.lean:59`), a structure that extends a continuous linear map.
7. **Mathlib and finding things.**
   - What Mathlib provides, and how this library builds on it.
   - Namespaces and `open`.
   - Search with Loogle, `exact?`, the API docs and the blueprint's links.
   - How a blueprint node links to its Lean declaration.
8. **Further reading.**
   - *Theorem Proving in Lean 4*;
   - *Mathematics in Lean*;
   - *Functional Programming in Lean*;
   - the Lean Language Reference;
   - Mathlib's documentation.

Each section ends with one or two exercises, with collapsible solutions (decision 3 of chapter 1).
Exercises in Lean give the statement, with `sorry` standing for the part to fill in, and the solution
is a full, checked proof. Target length: 4,000–5,000 words, since the code examples add space.

## Infrastructure to check first

- **Exercise statements containing `sorry`.** Verso must show them without failing the build. Verso
  has expected-warning and expected-error blocks, as in the website's `leanOutput`; check which
  one applies.
- **Proof states.** Verso must display the goal state after each tactic in the worked proof of
  section 4. The Lean reference manual shows goals this way; find the mechanism.
- **Build time.** Each chapter that imports `Physicslib4` adds elaboration time, which is CI time,
  only when `web/` or the library changes.

## Process (as for chapter 1)

1. One agent checks the two infrastructure points above with tiny tests, then a writer drafts
   section by section, building after each one and keeping a progress log.
2. A reviewer checks Lean accuracy, that every example is current, the prose style, and the
   rendering.
3. You read the rendered chapter, and changes go back to the writer.
4. Commit after your approval.

## Questions for you

1. **Depth of section 4.** Is one fully worked tactic proof enough, or do you want two (one
   algebraic, one about causal structure)?
2. **Exercises in Lean.** Should readers be told how to run the exercises locally (clone, `lake build`,
   open in VS Code)? Or keep them reading-only in the browser, and leave the setup to chapter 4,
   "Doing it yourself"?
3. **Universe levels.** The library uses `Type u` and universe parameters (D1, D8). Mention them in
   one short aside, or leave them out of chapter 2?
4. **Further reading.** Is the list above right?
