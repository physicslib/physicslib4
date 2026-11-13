# Review: van Daele batch 5b (Jones Lemmas 13.1.5–13.1.7), 2026-11-13

VERDICT: PASS. All 23 nodes correct in this project's convention (inner product linear in the second slot); every conjugation and slot checked; cited nodes and Mathlib names exist; validate clean for this batch.

Non-blocking (to apply before formalization):
- `lmm:van-daele-functions-identities`: state v_λ·r = g_λ for all t (both sides 0 for t ≤ 0); then drop the `lmm:modular-fc-congr-positive` step from `lmm:van-daele-fc-products` (~8 lines).
- Extract a shared node "cΩ ∈ Dom S and S(cΩ) = c*Ω for c ∈ M" (e.g. `lmm:tomita-operator-on-algebra`) and cite it from `lmm:van-daele-first-term` and `lmm:van-daele-second-term`.
- Make the hypotheses of `lmm:van-daele-identity-algebra` explicit (as in `lmm:van-daele-sesquilinear-identity`).
- Add `lmm:modular-spectral-projections-nested` to the `\uses` of `crllr:van-daele-rearranged-identity-H0`.
- Optional: split off the J(M′Ω) density step from `crllr:van-daele-approximation`; drop the unused "J maps Dom S ∩ Dom S* onto itself" clause of `lmm:tomita-operators-after-conjugation`.
- Design decisions for the user: a definition node for g_λ, v_λ, k_λ (used in ~10 statements); splitting the van Daele material into its own chapter file (tomita-takesaki.tex is ~3260 lines).
