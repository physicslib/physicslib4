# Review: Lean statements for borchers-wedges batch 4, part 1 (2026-11-17)

File reviewed: `Physicslib4/AQFT/HaagKastler/BisognanoWichmann.lean`.

There are 12 sorry'd statements. Fifteen nodes that need the four new definitions are deferred,
pending guard approval for this file.

**Verdict: PASS.**

The signs check out:
- **The l₊ direction:** Borchers' theorem gives e^{−2πs}.
- **The reversed form:** its hypothesis V(−t)xV(t) ∈ M gives e^{+2πs}, through the commutant.
- **The l₋ direction** follows from the reversed form, and the general-translation lemma gives
  U(Λ(−2πs)a).
- **The commutant:** Δ_{M′}^{it} = Δ^{−it} and J_{M′} = J.

Three choices were judged acceptable:
- **Standardness:** an explicit hΩ replaces weak additivity.
- **The reverse-endomorphism lemma** drops its unused von Neumann and cyclic hypotheses.
- **Some operator identities are stated applied to a vector.**

Optional cleanups:
- **`commutant_modularUnitaryGroup`:** drop the conjunct that repeats
  `isCyclicSeparatingVector_centralizer`.
- **The translation-unitaries lemma:** split its 7-way conjunction.
