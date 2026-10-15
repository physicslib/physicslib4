# Tutorial chapter 1 ("AQFT in brief"): writer's progress log

Plan: `plan-verso-stage3-tutorial-ch1-2026-10-15.md`. File: `web/Tutorial/AQFTInBrief.lean`. Build:
`cd web && lake build && lake exe generate-tutorial --output _out/tutorial`. Word counts exclude maths.

- Intro + section 1 "Why algebras": 85 + 627 words, 1 exercise. Build OK.
- Section 2 "Regions of spacetime": 834 words, 2 exercises, new figure `cones` (`Site.conesDiagram`, registered in `Tutorial.diagrams`). Build OK.
- Section 3 "C*-algebras of observables": 567 words, 1 exercise. `C\*` escape renders correctly. Build OK.
- Section 4 "The axioms": 1209 words, subsections for Axioms 1-5 and the primitivity aside, figure `diamond`, 2 exercises. Build OK.
- Section 5 "States and the GNS construction": 926 words (subsections GNS, vacuum, superselection), 2 exercises. Build OK. Running total 4253, over budget: trim in the final pass.
- Sections 6 "What this project sharpens" (513 words, 1 exercise) and 7 "Further reading" (104 words). Build OK.
- Final pass: reread for physics, notation and style; trimmed to about 4,500 words (counting each formula and
  Lean name as one word), dropped one section-4 exercise, fixed the domain-of-dependence and Schwarzschild
  wording, the strip-exercise solution, and cross-references. `scripts/check_temporal_wording.py` passes.
  8 exercises, 8 collapsible solutions. Build OK.
- Review fixes, group 1 (physics/maths: Borchers class, real f, ball radius, compact J-diamond, ||A*|| = ||A|| step, alpha_e, 1964 unit wording). Build OK.
- Review fixes, group 2 (prose: commutant/bicommutant and precise strong density in Axiom 4; vacuum
  paragraph restructured, spectrum condition rewritten; curved-spacetime paragraph split in three with
  the late-time Schwarzschild example and "strongly causal; topologies then agree"; intertwiner
  defined; "inductive limit" first; Axiom 2 repetition and Cambridge sentence cut; Axiom 5 name
  explained; source rewrapped to 100 columns, one long inline formula made a display). Signalling
  exercise left in place (memo: acceptable). Trimmed to 4,557 words (formulas and Lean names count as
  one word each). Build OK, temporal-wording check OK.
