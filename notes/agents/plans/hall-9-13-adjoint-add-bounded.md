# Plan: prove `prpstn:hall-9.13` (adjoint of a sum with a bounded operator)

## Objective

Close the two `sorry`s in `Physicslib4/Spectral/Unbounded/Basic.lean` that together formalize
blueprint Proposition `prpstn:hall-9.13` (§10.3, `blueprint/src/sections/sec10/unbounded-spectral-theorems.tex`,
line 502):

- `adjoint_add_toPMap` (Basic.lean:430) — `(T + B.toPMap ⊤)† = T† + (B*).toPMap ⊤`.
- `isSelfAdjoint_add_of_isSelfAdjoint` (Basic.lean:441) — corollary, the last paragraph of the
  blueprint proof.

Chosen because the prior session's report flags `prpstn:hall-9.13` as the most-cited remaining
sorry in this part of the dependency graph: `thrm:hall-9.17` (spectrum of a self-adjoint operator
is real), `thrm:hall-9.21`, `prpstn:hall-9.14`'s domain convention, and several chapter-10 normal
operator results all `\uses` it.

## Statements (verbatim, must not change)

```lean
theorem adjoint_add_toPMap {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (B : H →L[ℂ] H) :
    (T + (B : H →ₗ[ℂ] H).toPMap ⊤)† =
      T† + ((ContinuousLinearMap.adjoint B : H →ₗ[ℂ] H).toPMap ⊤)

theorem isSelfAdjoint_add_of_isSelfAdjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hTsa : IsSelfAdjoint T) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (T + (B : H →ₗ[ℂ] H).toPMap ⊤)
```

## Intended route

The blueprint's boundedness bookkeeping (Parts 1 and 2) is not needed in Lean, because the project
already has an *exact-representation* characterization of adjoint-domain membership:

- `mem_adjoint_domain_iff_exists` (Basic.lean:130): `ψ ∈ (T†).domain ↔ ∃ φ, ∀ χ : T.domain, ⟪ψ, T χ⟫ = ⟪φ, χ⟫`
- `adjoint_apply_eq_of_forall_inner` (Basic.lean:145): identifies the representing vector as `T† ψ`.

So both containments follow by adding/subtracting `B* ψ`, with `⟪ψ, B χ⟫ = ⟪B* ψ, χ⟫` from
`ContinuousLinearMap.adjoint_inner_left/right`. Structure:

1. Note `(T + Bᵖ).domain = T.domain ⊓ ⊤ = T.domain` and so `HasDenseDomain (T + Bᵖ)` from `hT`.
2. Domain equality both ways via `mem_adjoint_domain_iff_exists`.
3. Values via `adjoint_apply_eq_of_forall_inner`.
4. Conclude with `LinearPMap.ext` (domain equality + pointwise agreement).
5. Corollary: rewrite with step 4, `hTsa : T† = T`, and `hB : B* = B`.

## Stopping condition

`lake build` passes; `lean_diagnostic_messages` on `Basic.lean` and `Spectrum.lean` is empty; no new
`sorry` anywhere; `lean_verify` shows no extra axioms; `lean_guard.py check` reports no protected
change; blueprint `prpstn:hall-9.13` carries `\lean{}`/`\leanok` matching the code.

## Delegations

1. lean-search → scout memo on the Mathlib `LinearPMap.adjoint` / `LinearPMap.add` / `toPMap` API.
2. lean-prover → close the two sorries, memo path supplied.
3. lean-auditor → review.
4. lean-blueprint → `\lean`/`\leanok` sync.

## Non-goals

Do not touch the other sorries in Basic.lean or Spectrum.lean. Do not change any statement,
definition, or structure field.
