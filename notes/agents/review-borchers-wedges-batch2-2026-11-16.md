# Review: borchers-wedges.tex, batch 2 (2026-11-16)

Scope: wedges, region algebras and covariant vacuum representations (lines 285–667).

## Pass 1 — REVISE

Every statement is true, and the definitions are faithful to the library. All `\uses` targets exist.
Points verified:
- the boost sign convention: BGL's Λ_{W₁}(t) is Λ(−2πt) here;
- R = diag(1,−1,−1,1) lies in SO(1,3)↑;
- the explicit diamonds B± lie in W_R and W_L respectively;
- the Reeh–Schlieder route (`reeh_schlieder_cyclic_of_vonNeumann`) with the bridge data;
- separation via the opposite wedge.

The required fixes concern granularity, grounding and `\uses`:
1. **lmm:poincare-maps-diamonds.** Cite `chronologicallyPrecedes_smul_iff`, and split into:
   - (a) the explicit image identity of a diamond;
   - (b) the inclusion iff, via `Set.smul_set_subset_smul_set_iff`.
2. **lmm:wedges-contain-diamonds.** Add a strict open-cone bound |vⁱ| < v⁰, prove only B₊, then
   take B₋ = (R,0)B₊. Move lmm:left-wedge-is-wedge before it.
3. **lmm:left-wedge-is-wedge.** Split off "R ∈ SO(1,3)↑", grounding the determinant via
   `LinearMap.det_toMatrix` and `Matrix.det_diagonal`.
4. **lmm:boost-matrix-lorentz.** Split into:
   - η-preservation, by direct expansion;
   - det = 1, via `det_toMatrix`, `Matrix.det_succ_row_zero` and `Real.cosh_sq_sub_sinh_sq`;
   - orthochronous.

   Also build Λ(s) as a `≃ₗ[ℝ]` with inverse Λ(−s).
5. **lmm:boost-continuous-subgroup.** Split into:
   - the group law;
   - continuity, via `continuous_induced_rng`;
   - a generic lemma that conjugates of continuous one-parameter subgroups are again ones;
   - continuity of `translationFlow`.
6. **lmm:boost-preserves-wedge.** Split into:
   - b(s)W_{R,L} = W_{R,L};
   - the generic statement that b(s)W = W implies b_g(s)(gW) = gW.
7. **lmm:region-generating-set-covariance.** Split off the reindexing of S(gO).
8. **lmm:wedge-translations.** Split parts (1) and (2).
9. **`\uses` fixes:**
   - crllr:wedge-contains-diamond;
   - thrm:wedge-cyclic-separating: add def:left-wedge and the modular definitions;
   - crllr:wedge-modular-covariance: add def:tomita-operator;
   - lmm:covariant-vacuum-bridge: cite the label that defines V̄₊.

Non-blocking points:
1. **The type of U.** Use `U : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H)`, with the group law in
   the library's form `U (L' * L) = (U L).trans (U L')`.
2. **Continuity.** Add a definition "continuous one-parameter subgroup": Lean's
   `IsOneParameterSubgroup` has no continuity.
3. **A generic helper.** If N ⊆ M′ and Ω is cyclic for both M and N, then Ω is cyclic and
   separating for M.
4. **Notation.** Write U(b(−2πt)).
5. **File length.** Consider moving this batch into its own file.

## Pass 2 — PASS

All required fixes and non-blocking points 1–4 are applied, and every proof is now at most about 10 Lean lines.

Non-blocking:
- `lmm:conjugate-continuous-subgroup` should list `def:wedge-boost` in its statement `\uses`. Applied.
- The proof `\uses` of `lmm:poincare-maps-diamonds` could be trimmed.
