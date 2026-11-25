# Review: Lean statements for borchers-wedges batch 1 (2026-11-17)

Files reviewed:
- `Hilbert6/Spacetime/MinkowskiCausalCone.lean`
- `Hilbert6/Spectral/Unbounded/UnitaryConjugation.lean`
- `Hilbert6/Operators/Modular/Intertwining.lean`

There are 22 labels, all sorry'd. **Verdict: PASS.**

**Checks that hold:**
- The Minkowski signs and the closed cone {η(v,v) ≤ 0 ∧ v⁰ ≥ 0}.
- The coordinate-separation lemma, which cannot be falsified by the reflexive case.
- The graph identity `B.graph = A.graph.map Φ[V]` means B = VAV⁻¹.
- `conj[V]` is V ∘ a ∘ V⁻¹, and every conclusion matches it: S₀, S, Δ, f(Δ), Δ^{it} and J.
- The double-antiunitary form is right.
- The hypotheses of each statement can hold together.
- The roughly 12-binder signatures are accepted. A bundling structure would be a new definition,
  so it can only be proposed.

**Non-blocking points:**
1. **`tomitaPre_graph_unitary_intertwine`:** hM₁ and hM₂ are not needed. Keep them only if the
   proof uses `tomitaPre_apply`.
2. **`functionalCalculus_unitaryConj_of_bounded`:** hB follows from the other hypotheses.
   Consider `∀ hB, …` in the conclusion, as the unbounded lemma has.
3. **lmm:unitary-commutes-of-conj-eq:** the Lean form covers partial linear operators and total
   maps, but not partial antilinear ones. The S-part of the corollary has to be proved directly.
4. **`mem_closedForwardCone_iff_sqrt_le`** combines an iff with a corollary, so it cannot be used
   with `rw`. Consider splitting it.
5. **The displacement lemma** mixes `μ.tangent s` with the raw `mfderivWithin` (definitionally
   equal). A comment would help.
6. **`Φ[V]`** is a local notation duplicated in two files.
