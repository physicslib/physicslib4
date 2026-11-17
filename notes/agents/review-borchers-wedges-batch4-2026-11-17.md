# Review: borchers-wedges.tex, batch 4 (wedge corollary and BW-a), 2026-11-17

This was a narrow-scope review. **Verdict: PASS on the first pass.**

The sign bookkeeping checks out:
- **The l₊ direction:** Borchers' theorem gives e^{−2πs}.
- **The l₋ direction:** Borchers for M′ gives e^{+2πs}. This uses Δ_{M′}^{it} = Δ^{−it} and J_{M′} = J.
- **The reflection:** j = (−x⁰, −x¹, x², x³).

These match the form Δ^{it} = U(b(−2πt)). Other points checked:
- the properties of Z(t);
- the propagation of (MC) to every wedge;
- the internal-symmetry lemmas;
- BW-a itself.

Every statement needing weak additivity states it. The closing remark and the Restriction line are
accurate.

All optional cleanups are applied:
- **A new factorisation lemma,** `lmm:translation-light-cone-factorisation`, gives
  U(a) = U(αl₊)U(βl₋)U(a⊥).
- **Explicit hypotheses** in the statements of the commutant trio.
- **`\uses` edges added:** `lmm:poincare-maps-diamonds`, `lmm:modular-unitary-group-props` and
  `def:future-timelike-translation`.
- **Wording:** "states what can separate" replaces "states exactly what can separate".

Open item: the wedge corollary is attributed to Borchers 1992 without a theorem number.
