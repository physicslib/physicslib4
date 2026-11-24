# Review: Lean statements for borchers-wedges batch 4, part 1 (2026-11-17)

File reviewed: `Hilbert6/AQFT/HaagKastler/BisognanoWichmann.lean`.

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

## Part 2: four definitions and 15 nodes — PASS

The definitions are faithful:
- **`wedgeModularDefect`:** Z(t) = Δ^{it}∘U(b(2πt)). Remember that `trans` applies its first argument first.
- **`wedgeReflection`:** j, as a linear map.
- **`IsWedgeModularCovariant`:** conj[Δ^{it}] R(B) = R(b(−2πt)·B). It does not involve U.
- **`IsInternalSymmetry`:** a structure with two fields, XΩ = Ω and invariance of every R(B). A structure is preferred over a conjunction.

The signs check out:
- Δ^{it} = Z(t)U(b(−2πt)) and JU(a)J = U(ja).
- The b_g conventions in the general-wedge statements are right.
- The group law Z(s+t) = Z(t).trans Z(s), that is Z(s)∘Z(t), is right.

Two generalisations are sound:
- **Regions with standardness.** The internal-symmetry commutation is stated for any region with standardness, not only wedges.
- **One reference conjugation C** is shared between the two wedges.

The BW-a docstring has the **Restriction:** line word for word.

Non-blocking points:
- `hΩ` in the general-wedge corollary is derivable from the other hypotheses.
- Two corollaries restate earlier lemmas, as the blueprint does.
