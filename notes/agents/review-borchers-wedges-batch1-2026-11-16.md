# Review: borchers-wedges.tex, batch 1 (2026-11-16)

Scope: the intro of `sctn:borchers-wedges`, `sbsctn:causal-precedence-minkowski` and
`sbsctn:unitary-intertwining-modular`.

## Pass 1 — REVISE

All statements are true and the sign conventions match the library. The cited labels state what
the proofs use.

Required fixes:
1. Split `lmm:closed-forward-cone-convex` into:
   - `lmm:closed-forward-cone-iff-norm`, with the component bound |vⁱ| ≤ v⁰;
   - `lmm:closed-forward-cone-closed-convex`.
2. Add `lmm:unitary-commutes-of-conj-eq` and rebuild `crllr:unitary-commutes-modular-objects` on
   it.
3. Add `def:causal-future-and-causal-past` to the proof `\uses` of
   `lmm:spacelike-of-coordinate-separation`.

Non-blocking points:
- Trim `lmm:unitary-conjugate-graph`.
- State the core of `lmm:unitary-intertwines-modular-operator` as a pointwise iff.
- Complete the citations. BGL Theorem 2.3 is confirmed from the paper.

## Pass 2 — PASS

- All required fixes and non-blocking points are applied correctly.
- Every proof is at most about 10 Lean lines, and the `\uses` lists are complete.
- `blueprint_validate` finds nothing in this file; the 14 errors it reports are older ones in the
  spectral chapters.

Notes for the formalizer:
1. **The S-part of the corollary.** `UnitaryCommutes` takes `LinearPMap`s, but `tomitaOperator` is
   a function on a subtype. Take the S-part of the corollary directly from
   `lmm:unitary-intertwines-tomita-operator`, applied at ψ and at V⁻¹ψ.
2. **Proof terms.** Rewriting f(VΔ₁V⁻¹) to f(Δ₂) changes the self-adjointness proof term inside
   `functionalCalculus`. Use `subst` or a congruence lemma, not `rw`.
3. **An alternative route.** `lmm:unitary-transport-bounded-fc` could instead apply
   `integral_antiunitaryConj` twice. The real/imaginary route as written is fine.

Suggested Lean locations:
- the causal-cone lemmas in `Spacetime/Minkowski.lean` (the spatial projection `spatialProj` is
  private there);
- the unitary-conjugation lemmas in `Spectral/Unbounded/Commuting.lean`;
- the standard-pair lemmas in a new `Operators/Modular/` file.
