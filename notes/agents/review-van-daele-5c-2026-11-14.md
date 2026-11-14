# Review: van Daele batch 5c (Tomita's theorem), 2026-11-14

## Pass 1: REVISE (granularity only)

Mathematics correct throughout (every sign, conjugation, λ^{2it} factor, cosh factor, both inclusions checked); Mathlib names spot-checked. Route notes: commutation with all b′ ∈ M′ and (M′)′ = M is used directly (no unitaries needed); Δ_{M′}^{it} = Δ^{−it} is not needed (only the t = 0 case for (M′, Ω), with J_{M′} = J) — requires all 5a–5c lemmas to be stated for an arbitrary pair (M, Ω).

Blocking splits:
1. `lmm:modular-conjugation-bounded-conjugate`: separate the construction of JTJ (bounded linear, (JTJ)ψ = J(T(Jψ))) from the bound and the identities J(JTJ)J = T, (JTJ)(JT′J) = J(TT′)J.
2. `prpstn:van-daele-integral-formula`: split out `lmm:modular-spectral-approximants` (ψ_m = E_{m+1}ψ: E_{m+1}ψ_m = ψ_m, ‖ψ_m‖ ≤ ‖ψ‖, ψ_m → ψ).
3. `lmm:van-daele-commutator-fourier`: add `lmm:van-daele-commutator-integral-zero` (∫ λ^{2it}h(t) dt = 0 via the F₁ − F₂ split, `integral_sub`, the integral formula twice, ab′ = b′a).
4. `lmm:tomita-modular-automorphism`: split out `lmm:tomita-modular-automorphism-subset` (Δ^{is}xΔ^{−is} ∈ M for all s, x ∈ M).

Recommended: split the pointwise limit out of `lmm:van-daele-integral-continuity`; split the real inequality λ^s ≤ max(λ, λ⁻¹) out of `lmm:van-daele-phase-strip`.

Proposals needing the user's decision (not applied): `def:modular-conjugation-conjugate` (JTJ as a definition), `def:van-daele-triple` (the van Daele equation as a Prop, used in ≥ 5 statements); moving `sbsctn:van-daele` to its own file (the user has declined this).
