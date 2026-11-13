# Review: van Daele batch 5a (complex powers of Δ), 2026-11-13

## Pass 1: REVISE

Mathematics sound throughout; no false statement or gap; Mathlib names checked. Granularity only.

Blocking:
1. `lmm:modular-power-function-identities` (~15–25 lines): split into (a) multiplicativity with p_{0,n} = 1_{K_n}; (b) conjugation; (c) the e_t shift; (d) restriction to K_n.
2. `lmm:modular-inverse-scalar-identities` (~15–20 lines): split into three lemmas, one per identity; identity 2 uses identity 1 off K_n.
3. `lmm:antiunitary-conjugate-bounded-fc` (~15 lines): split out a lemma f(A) = (Re f)(A) + i(Im f)(A), f̄(A) = (Re f)(A) − i(Im f)(A) (from `lmm:functional-calculus-bounded`, linearity in `thrm:operator-valued-integration`), then the conjugation step via `crllr:antiunitary-conjugate-functional-calculus`.

Recommended: split `lmm:log-power-on-interval` (log bound / cpow bound) and `crllr:modular-power-matrix-coefficients` (vector-valued claim and ⟨η, p_z ξ⟩ / the sandwich p_z a p_{−z}).

Minor: in `lmm:modular-power-half` add `max_eq_left` for s and drop `Real.rpow_neg` (r is λ^{−1/2} directly).

Note for 5c: this project's inner product is linear in the second slot, so write f(z) = λ^{2z}⟨p_{z̄}η, a p_{−z}ξ⟩ = λ^{2z}⟨η, p_z a p_{−z}ξ⟩ (the form `crllr:modular-power-matrix-coefficients` provides), not Jones's ⟨a p_{−z}ξ, p_{z̄}η⟩.

## Pass 2: PASS

All findings resolved; new nodes correct (cpow_conj/inv_cpow side conditions hold since λ > 0 on K_n); `\uses` updated with no stale references; new Mathlib names exist (`Complex.abs_re_le_norm`, `Complex.abs_im_le_norm`, `RCLike.conj_eq_re_sub_im`); every proof ≤ ~10 Lean lines. Optional: `lmm:modular-inverse-scalar-identities` and `lmm:modular-power-function-identities` now hold only one identity each; renaming is left to the user.
