# Review: Takesaki's lemma statements (stage 3a), 2026-11-11

Scope: `Physicslib4/Operators/Modular/Takesaki.lean` against `sbsctn:takesaki-lemma` (32 labels).
All 32 labels have a `leanDeclaration`. The file compiles with only `sorry` warnings. Nothing
was added except theorems and one `local notation`: no `def`, `abbrev`, `instance` or
`structure`.

## Blocking

None.

## Correctness checks

- Conjugations: `takesaki_transfer` gives `⟪φ, aΩ⟫ = z⟪χ, aΩ⟫ - ⟪a⋆Ω, Sχ⟫` from
  `φ = z̄χ - Δχ`. That is correct for an inner product that is conjugate-linear in its first
  argument. It also agrees with `Δ = S′†S′` and `S = C ∘ S′`, since
  `⟪Sη, Sχ⟫ = conj⟪S′η, S′χ⟫ = ⟪Δχ, η⟫`. `takesaki_test_inner_products` is correct, using
  `(s u)⋆ = s̄ u⋆`. In `takesaki_transfer_resolvent`, the adjoint identity
  `⟪φ, r_z(Δ)x⟫ = ⟪r_{z̄}(Δ)φ, x⟫` is the right direction.
- Encodings: `r_z`, `d(z)`, `r_z(Δ)`, `M′` and `P[h, ε, s]` all match the blueprint. In the
  local notation, `cfc` with a real function on `star h * h` is well posed because the operator
  is self-adjoint and `f_s` is continuous for `ε > 0`.
- `modularResolvent_isResolvent`: the sign `B = -r_z(Δ)` agrees with `IsResolvent`, which
  inverts `T - λ𝟙`.
- Vacuity and edge cases:
  - `takesaki_test_element` and `takesaki_key_estimate` are false without `hz`: at
    `z ∈ [0, ∞)`, `c` collapses to `0`. Both keep `hz`.
  - With an arbitrary `c`, `takesakiBall_closure_bound` and `takesakiG_uniform_approximation`
    are vacuous for `c < 0` and true for `c ≥ 0`.
  - `commutantExtension_mem` does not need the norm bound. `T` is continuous, `Td′` and `d′T`
    agree on `M′Ω`, and `M′Ω` is dense by the second conjunct of `IsCyclicSeparatingVector`.
    So departure (5) is valid.
- Chaining: the lemmas fit together as written.
  - `exists_re_inner_add_le_of_not_mem_convex` applies with `K = 𝒦_c`; nonemptiness comes from
    `takesakiBall_closure_isClosed_convex` with `c ≥ 0`.
  - `takesaki_transfer` produces `hS`, and `⟨χ, hS⟩` feeds `takesakiG_uniform_approximation`.
    The `G` expressions match term for term, because `↑⟨χ, hS⟩ = χ` holds by `rfl`.
  - `takesakiG_uniform_approximation` and `takesaki_key_estimate` share the same `G(hΩ, h⋆Ω; a)`
    expression and the same `c`, which gives the contradiction.
  - `takesaki_lemma` follows from `takesaki_resolvent_mem_ball_closure`,
    `takesakiBall_closure_bound` and `commutantExtension`, with `0 ≤ ‖a′‖/√…`.
  - `takesaki_transfer_resolvent` follows from `modularResolvent_rightInverse` at `conj z`
    (`(conj z - t)⁻¹` matches) and the adjoint conjunct of `modularResolvent_bounded`.
- Departures:
  - (1) Generalizing `c`: fine.
  - (3) Uniqueness among all `ã ∈ M` with `ãΩ = ψ`: this is stronger than the blueprint and
    still provable, since `Ω` is separating. Fine.
  - (5) Fine.
  - (2) and (4) are inconsistent with each other; see below.

## Non-blocking (recommended)

1. `takesakiG_lipschitz` (departure 4): `ha : a ∈ M` is unused, and it is the only mention of
   `M`. Drop `{M}` and `ha`. This matches the rule applied to `h ∈ M` in the pure `cfc` lemmas.
2. `takesakiShiftedPow_isSelfAdjoint`, `_zero` and `_commute`: `hε` is unused. `cfc` of a real
   function is always self-adjoint, `x ^ (0:ℝ) = 1`, and `cfc` always commutes with its
   argument. Drop `hε` there, or keep it consistently and say why. Only `_mul`, `_norm_le` and
   `_mem` need it.
3. `cfc_mem_of_isVonNeumannSet`: `hsa` is redundant, because `cfc f x = 0 ∈ M` when `x` is not
   self-adjoint. Keeping it to match the blueprint text is acceptable.
4. `commutantExtension_linearMap`: `hM` and `hΩ` are unused. `Set.centralizer M` is always a
   submodule, and the proof needs no cyclicity. Optional.
5. `lmm:takesaki-shifted-powers`: the blueprint `\lean{}` and `leanDeclaration` list only
   `takesakiShiftedPow_mem`. Add `_isSelfAdjoint`, `_mul`, `_zero`, `_commute` and `_norm_le`,
   so that the split declarations are linked.
6. Rename `exists_re_inner_add_le_of_not_mem_convex` to `..._of_notMem_convex`. Current Mathlib
   uses `notMem`, for example `IsClosed.notMem_iff_infDist_pos`.
7. `commutantExtension`: the uniqueness binder is named `a'`, which clashes visually with the
   commutant element `a′` used everywhere else. Rename it to `ã`, as in `takesaki_lemma`.
8. Some conclusions bundle several results: `modularResolvent_isResolvent` repeats the norm and
   adjoint conjuncts of `modularResolvent_bounded`, and `takesaki_approximate_polar` has six
   conjuncts. Both mirror the blueprint, so this is acceptable. Splitting the `∈ M` conjuncts
   of `takesaki_approximate_polar` (the only ones needing `hM`, `hh`) from the algebraic
   identities would match the `takesakiShiftedPow_*` split.

## Readability and docstrings

Binder counts are at most 11: `takesaki_transfer` and `takesaki_transfer_resolvent` have 11,
and `takesaki_lemma` has 10. Every group is accounted for: `M`, `Ω`, `hM`, `hΩ`, `C`, `hC` form
the fixed modular context the definitions require, followed by `z`, `hz`, `a′` (with `ha′`
where used), then `φ`, `χ`, `hχ`. Docstrings are in the present tense and each carries a
`Blueprint:` line. None states a deliberate restriction, so no `**Restriction:**` line is
needed.

VERDICT: PASS
