# Review: sorry'd statements for `sbsctn:tomita-adjoint` (stage 3b), 2026-11-11

Files: `Physicslib4/Spectral/Unbounded/Commuting.lean` (15 labels),
`Physicslib4/Operators/Modular/TomitaAdjoint.lean` (23 labels). All 38 labels are recorded and
each blueprint `\lean{}` matches. Both files compile with only `declaration uses sorry` warnings.
`Commuting.lean` imports only `Polar.lean`. No `def`/`abbrev`/`instance`/`structure` is added.
Docstrings are one line plus `Blueprint: <label>`, in the present tense.

## Encodings checked

- `antiunitaryConj W A = W ∘ A ∘ W⁻¹` with domain `W(Dom A)` (Polar.lean:1317). `C.trans U = U ∘ C`,
  so the double conjugate is `U C C A C⁻¹ C⁻¹ U⁻¹ = U A U⁻¹` given `hC`. This is faithful.
- `Γ(S*)`: `S′ = linearizedTomitaPre` closure with `S′ = C S` (Tomita.lean:328). Mathlib's convention
  is `⟪T† y, x⟫ = ⟪y, T x⟫`, so `⟪η, ζ⟫ = ⟪Cξ, C Sζ⟫ = ⟪Sζ, ξ⟫`, which conjugates to
  `⟪ζ, η⟫ = ⟪ξ, Sζ⟫`. This matches `mem_tomitaAdjoint_iff`, and `_inner_algebra` (ζ = xΩ) as well.
  `F₀ ⊆ S*` holds: `⟪b′Ω, x*Ω⟫ = ⟪xΩ, b′*Ω⟫`.
- `a₀†(yΩ) = yη` holds with the first-slot conjugate-linear convention:
  `⟪yΩ, xξ⟫ = conj⟪ξ, (y*x)*Ω⟫ = conj⟪y*xΩ, η⟫ = ⟪yη, xΩ⟫`.
- The functions h_n and k_n match the blueprint. `‖c R_n ψ‖ = ‖|c|(R_n ψ)‖ = ‖K_n ψ‖ ≤ n‖ψ‖` holds,
  since k_n < n. At n = 0 every function is 0, so the convergence statements are unaffected.
- `x_n† = R_n c†` on `Dom c†` holds because `(cR_n)* ⊇ R_n c*`. `x_nΩ → ξ` follows from
  `‖c(R_nΩ − Ω)‖ = ‖K_nΩ − |c|Ω‖`, and `x_n*Ω = R_n η → η`.
- `mem_modularOperator_centralizer_iff`: with T = C J Δ^{-1/2}, the two antiunitaries cancel in
  `⟪Tψ, Tφ⟫`. This is correct.
- `mem_tomitaAdjoint_iff_mem_closure_graph` follows from these lemmas.
  - ← is `_of_mem_closure_graph`.
  - → chains `leftMap_existsUnique`, then `closure_props` (which gives hc and hcl), then
    `approximant_operator` (choose x_n for n ≥ 1), then `approximant_mem_centralizer` and
    `approximant_tendsto`. It closes with `mem_closure_of_tendsto` and `star = adjoint`.
  - `unitary.linearIsometryEquiv` bridges `closure_commute` (`≃ₗᵢ`) to
    `mem_centralizer_of_commute_unitary` (`unitary`).
- `commutant_modular_objects` follows from `isCyclicSeparatingVector_centralizer`,
  `tomitaOperator_centralizer_iff` (by set ext), `modularOperator_centralizer`, and
  `modularOperatorSqrt_modularConjugation_centralizer`.

## Deviations judged

- `tomitaAdjoint_leftMap_existsUnique` drops `hξη`. This is correct and a strict strengthening that
  still holds: well-definedness needs only that Ω is separating, and density needs only that Ω is
  cyclic. Accept.
- The "in particular" conjuncts in `tomitaAdjoint_leftMap_adjoint` and
  `mem_tomitaAdjoint_iff_modularOperatorInvSqrt` follow the blueprint wording. Accept.
- `tomitaOperator_centralizer_iff` as (A ↔ B) ∧ (B ↔ C) follows the blueprint's "iff … iff".
  Accept.
- Large signatures: `tomitaAdjoint_approximant_mem_centralizer` has 17 binder groups and
  `tomitaAdjoint_approximant_tendsto` has 16. Every group can be accounted for:
  - 6 are the fixed (M, Ω, C) context.
  - ξ, η and `hξη` are the section hypothesis.
  - `a₀, ha₀, ha₀x` stand in for the operator. No definition is allowed for it, so it cannot be
    bundled.
  - `hc, hcl` are needed to name `functionalCalculus`.
  - n, `hn`, x and `hx` define the approximant.

  Accept, with the optional trims below.

## Non-blocking suggestions

1. `approximant_operator_commute` and `tomitaAdjoint_approximant_mem_centralizer`: `hn : 1 ≤ n` is
   not needed. At n = 0, `hx` forces x = 0, and both conclusions hold. Drop it if desired; keeping
   it matches the blueprint's "n ≥ 1".
2. `tomitaAdjoint_approximant_mem_centralizer` (and `tomitaAdjoint_leftMap_closure_commute`): `hξη`
   is mathematically unused. The first has `hc`/`hcl` as binders. In the second, a unitary in M
   commutes with any such `a₀`, and therefore with `a₀.closure`, whether or not `a₀` is closable.
   Dropping it gives a stronger statement and one fewer binder. Keeping it matches the blueprint's
   section convention.
3. `approximant_operator`: the defining property quantifies over `ψ : (R_n).domain` rather than
   `ψ : H`. The two are equivalent by `approximant_bounded` (domain = ⊤). `∀ ψ : H, ∃ hR, …` would
   read closer to the blueprint, but this is optional.

VERDICT: PASS
