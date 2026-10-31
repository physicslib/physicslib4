import VersoBlog
import Site.Components

open Verso Genre Blog
open Site

#doc (Page) "Roadmap" =>

# Two pillars

physicslib4 is built around two pillars.

*Pillar 1: Formalizing physics in Lean.* The first pillar is to solve Hilbert's sixth problem in
Lean 4, presenting physical theories axiomatically: algebraic quantum field theory, locally covariant
quantum field theory, topological quantum field theory, axiomatic quantum mechanics and others. The
goal is one library in which each theory has precise axioms and machine-checked consequences.

*Pillar 2: Using AI to discover new physics.* A cycle of proof and revision that treats an axiom system
as a physical hypothesis to be tested and changed, centered on the theories of Pillar 1, such as AQFT and
LCQFT. Because every derivation is checked by machine, a conflict with observation cannot be put down to
a slip in the proof: it points at the axioms. The cycle has four steps:

- *Derive.* AI systems prove theorems from a theory's axioms at a scale that hand derivation cannot match,
  and Lean checks every one. The PCT and spin–statistics theorems of axiomatic quantum field theory show
  the kind of consequence an axiom system can yield.

- *Compare.* Each consequence is set against experiment. Some theorems reflect observation, and some do
  not. Those that have not been tested are predictions.

- *Revise.* A theorem that does not reflect observation implies that the axioms used to derive it are in
  error. A formal proof names the hypotheses it depends on, which narrows the search for the axiom at
  fault. AI proposes a weakened, strengthened or replaced axiom, and Lean reports every proof that the
  change breaks.

- *Re-derive.* AI repairs the broken proofs and derives the consequences of the revised axioms, and the
  cycle begins again.

Each pass through the cycle yields candidates for new physical foundations, the axioms, and new
consequences, their theorems.
