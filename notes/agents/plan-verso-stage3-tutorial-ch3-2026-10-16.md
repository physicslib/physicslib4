# Plan: tutorial chapter 3, "Worked examples"

Follows chapters 1 ("AQFT in brief", `413c929`) and 2 ("Lean in brief", `97568b2`). The audience,
style rules, exercise format and process are the same as before. See
`plan-verso-stage3-tutorial-ch1-2026-10-15.md` and `plan-verso-stage3-tutorial-ch2-2026-10-16.md`.

## Decisions recorded (2026-10-16)

1. Example 2: the identity state on ℂ is worked in full; a vector state on $`\mathcal{B}(H)`$ for a
   finite-dimensional $`H`$ is an exercise with a checked solution.
2. Curved spacetime: only the trivial curved net, as an aside.
3. The order is as proposed: net, state, locality, covariance.

## Goal

Chapter 1 gave the physics, and chapter 2 gave the Lean needed to read it. Chapter 3 puts them
together: four examples, each a piece of AQFT that the reader works through in the library.

A reader finishes able to:

- build, or inspect, a concrete Haag–Kastler net and check its axioms;
- go from a state to its GNS representation in Lean;
- use local commutativity and Lorentz covariance in proofs;
- see where each step sits in the blueprint.

Each example follows the same pattern:

1. **The physics:** a short reminder of the chapter 1 material, opened with "As you will recall, ...".
2. **The Lean statement:** elaborated by Verso, read line by line.
3. **A proof or construction:** shown with the goal after each step, using the `goals` directive.
4. **One or two exercises** with collapsible, checked solutions.

## The four examples

1. **The trivial net and its axioms.**
   - **Lean:**
     - `Physicslib4.AQFT.HaagKastler.trivialLocalNet` (`AQFT/HaagKastler/Net.lean:306`);
     - `trivialLocalNetIsotony`, `trivialLocalNet_localCommutativity`, `trivialLocalNet_lorentzCovariance`;
     - `trivialHaagKastlerNet`, and `nonempty_haagKastlerNet` (the axioms are consistent).
   - Every region gets ℂ, so every axiom holds for simple reasons: show which, axiom by axiom.
   - Lesson: the axioms can be satisfied, but satisfying them says nothing about physics; a real
     model needs non-commutative local algebras.
   - The curved counterpart, `HaagKastlerCurved.trivialHaagKastlerNet`, gets a short aside.
2. **A state and its GNS representation.**
   - **Lean:** `Physicslib4.GNS.State` (`GNS/Basic.lean:59`), `gns_construction`, `gns_unique`.
   - The library has no named concrete state. The chapter builds one, for example the identity state on
     ℂ (or a vector state $`\omega(a) = \langle \Omega, a\Omega \rangle`$ on bounded operators), and
     runs `gns_construction` on it. Then it reads off $`(H, \pi, \Omega)`$ and the reproducing formula
     $`\omega(a) = \langle \Omega, \pi(a)\Omega \rangle`$.
   - Also shows a state on the trivial net's quasilocal algebra, and connects it to
     `HaagKastlerNet.IsVacuumState`.
3. **Local commutativity in a diamond.**
   - **Lean:**
     - `IsAlexandrovBasisSet` and `LocalCommutativity`;
     - `HaagKastlerNet.commute_ι_of_spacelike` (`Net.lean:225`);
     - `localCommutativity_iff_exists_commute_ι`;
     - `HaagKastlerNet.einstein_causality`.
   - Worked proof: for diamonds $`\mathbf{B}_1, \mathbf{B}_2`$ that are spacelike-separated inside a
     common diamond, the embedded observables commute, both in the common diamond and in the
     quasilocal algebra. Uses the landing page's diamond figure.
   - Mentions that a point is not spacelike-related to itself (`isSpacelikeRelated_irrefl`), so
     overlapping regions are never completely spacelike.
4. **Lorentz invariance of causal precedence.**
   - **Lean:**
     - `Physicslib4.causallyPrecedes_smul_iff`, `isCompletelySpacelike_smul_iff`;
     - `lorentzPath`;
     - `HaagKastlerNet.covEquiv`, and how covariance moves observables between diamonds.
   - Worked proof: why $`g \cdot p \prec g \cdot q \leftrightarrow p \prec q`$. The proof transports
     causal trips along $`g`$, and the reflexive case $`p = q`$ is trivial.
   - Then the physical point: covariance maps the algebra of $`\mathbf{B}`$ to that of
     $`g \cdot \mathbf{B}`$, and preserves local commutativity.

A closing section, **What the examples show**, makes the bridge to chapter 4 ("Doing it yourself"):
where to go to state and prove a result of one's own.

Target length: 4,500–5,500 words. The code takes space.

## Infrastructure

Nothing new is expected. Chapters 1–2 already provide maths, figures, `goals`, exercises and the
library imports. Example 2 defines a state inside the tutorial (a `def` or `example` in a Verso Lean
block); that is tutorial code, not library code.

## Process (as before)

1. One writer drafts section by section, building after each section and keeping a progress log.
2. A reviewer checks the Lean, the physics, the prose and the rendering.
3. You read the rendered chapter, and changes go back to the writer.
4. Commit after your approval.

## Questions for you

1. **The concrete state in example 2:** the identity state on ℂ (trivial but transparent), or a vector
   state on $`\mathcal{B}(H)`$ for a finite-dimensional $`H`$ (closer to physics; more Lean)? Or
   both, the first worked and the second as an exercise?
2. **The curved-spacetime counterparts:** only the trivial curved net as an aside (as proposed), or one
   example in curved spacetime as well?
3. **Order:** keep this order (net, state, locality, covariance), or put locality before states, so
   the purely spacetime examples come first?
