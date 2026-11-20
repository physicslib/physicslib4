# Review: borchers-wedges.tex, batch 3 (Borchers' theorem), 2026-11-17

This was a narrow-scope review: soundness, gaps, oversized proofs, and any missing `\uses` noticed.

## Pass 1 — REVISE

**Soundness.** The proof route is sound. It follows Florig's argument (Lett. Math. Phys. 46 (1998)),
as written in Longo's *Lectures on Conformal Nets*, Part I, Theorem 2.2.1. Points checked:
- the function F(z) = ⟨k_{z♭}(Δ)ψ♯, Ṽ(τe^{2πz}) k_z(Δ)φ♯⟩ on the strip 0 ≤ Im z ≤ 1/2;
- its boundary values and their reality;
- the chain "real on both edges, hence constant": reflection, periodic extension, strip Liouville
  and strip uniqueness, whose hypotheses match;
- reading off Δ^{is}V(t)Δ^{−is} = V(e^{−2πs}t) and JV(t)J = V(−t);
- the extension to all t;
- determination of an operator by matrix coefficients, using cyclicity for M and M′.

**Analytic inputs.** Positive energy gives the contraction bound. Operator-norm holomorphy comes
from a Taylor bound. Strong continuity up to the real axis comes from dominated convergence.

**Required fixes.**
- Split five oversized proofs:
  - `lmm:borchers-function-constant`
  - `lmm:strip-real-boundary-periodic`
  - `lmm:strip-power-functions-bounded`
  - `lmm:reflected-group-unitary`
  - `thrm:borchers`
- Two `\uses` fixes.
- Drop one unused reference.

**Non-blocking points.**
- State (B1)/(B2) in each lemma that uses them.
- `StripPeriodicExtension.lean` can be reused.

## Pass 2 — PASS

All fixes are applied, and every changed proof is at most about 10 Lean lines. A remaining
inconsistency was in the definition of W(t), whose domain read t ≥ 0. It now reads t ∈ ℝ.

**Open items for formalization.**
- The theorem number "Borchers, Theorem II.9" is confirmed only through Araki–Zsidó.
- Several Mathlib names were cited from memory: `Real.continuous_sqrt`, `Complex.conj_eq_iff_real`,
  `ContinuousOn.inner` and `HasDerivAt.conj_conj`.
- The helper objects (Φ_f, Ṽ, k_ζ, F, F_n, W) are notation in the blueprint. In Lean they will
  probably need small definitions, which need lean-kit guard approval.
- Suggested Lean modules:
  - `Analysis/StripRealBoundary.lean`
  - `AQFT/PositiveEnergyHalfPlane.lean`
  - `AQFT/Borchers.lean`
