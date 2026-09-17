# Plan: prove a theorem from blueprint §10.3 (Unbounded Spectral Theorems)

## Section identification

`blueprint/print/print.toc` confirms the numbering inside chapter 10:

- 10.1 GNS Construction Details
- 10.2 Spectral Theorems
- **10.3 Unbounded Spectral Theorems** -> `blueprint/src/sections/sec10/unbounded-spectral-theorems.tex`
- 10.4 Spacetime, 10.5 Haag Kastler Axioms, ...

So §10.3 is `unbounded-spectral-theorems.tex`, formalized under
`Physicslib4/Spectral/Unbounded/`.

## Objective

Land complete proofs (no `sorry`, build passing) for:

1. **Primary** `Physicslib4.Spectral.Unbounded.sq_norm_le_of_isSymmetric`
   (`Physicslib4/Spectral/Unbounded/Spectrum.lean:105`), blueprint
   `lmm:b-squared-inequality-symmetric` — "The `b²` Inequality for Symmetric Operators".

   ```
   theorem sq_norm_le_of_isSymmetric {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T) (a b : ℝ)
       (ψ : T.domain) :
       b ^ 2 * ‖(ψ : H)‖ ^ 2 ≤ ‖T ψ - ((a : ℂ) + (b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2
   ```

2. **Stretch** `Physicslib4.Spectral.Unbounded.isClosed_range_subSmul`
   (`Physicslib4/Spectral/Unbounded/Basic.lean:470`), blueprint `prpstn:hall-9.14` —
   "Closedness of the Range from a Lower Bound".

Both are load-bearing: `thrm:hall-9.17` (spectrum of a self-adjoint operator is real) and
`thrm:hall-9.21` both cite them.

## Approach

The blueprint proof of the `b²` lemma is the same computation as the already-proved bounded
case `Physicslib4.Spectral.sq_norm_sub_smul_apply_le`
(`Physicslib4/Spectral/Spectrum.lean:298`): set `B ψ = T ψ - a ψ`, note `⟪B ψ, ψ⟫` is real by
symmetry, expand `‖B ψ - i b ψ‖²` with `norm_sub_sq`, and drop the nonnegative `‖B ψ‖²`.
The only change is that `T` is a `LinearPMap`, so `B` is not an operator — the symmetric
inner-product identity is used pointwise at `ψ` instead.

For `prpstn:hall-9.14`: given `φ n = (T - λ) ψ n -> φ`, the lower bound makes `ψ n` Cauchy,
completeness gives `ψ n -> ψ`, then `T ψ n = λ ψ n + φ n -> λ ψ + φ`, and closedness of the
graph gives `ψ ∈ Dom T` with `T ψ = λ ψ + φ`.

## Verifiable stopping condition

- `lake build` succeeds with no `sorry` warning at the target declarations.
- `lean_verify` reports only the standard axioms for each target.
- `\lean{}` / `\leanok` added to the corresponding blueprint entries and
  `leanblueprint checkdecls` passes.

## Delegations

1. `lean-search` — scout memo: Mathlib API for `LinearPMap` graph closedness / sequential
   characterization of `IsClosed`, and the inner-product lemmas needed for the `b²`
   expansion. Memo at `notes/agents/memos/sec10-3-b-squared.md`.
2. `lean-prover` — prove target 1 (then target 2) in place, no statement changes.
3. `lean-auditor` — check statements against the blueprint, axioms, restrictions.
4. `lean-blueprint` — add `\lean{}` / `\leanok` to the two blueprint entries.

## Constraints

- No statement, definition or structure-field changes (policy blocks new `def`/`structure`).
- New helper `theorem`/`lemma` declarations are allowed.
- Any narrowing relative to the blueprint must be recorded with a `**Restriction:**` line.
