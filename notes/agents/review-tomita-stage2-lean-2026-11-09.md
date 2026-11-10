# Review: Tomita–Takesaki stage 2, Lean statements (batches A–D)

Files: `Physicslib4/Spectral/Unbounded/Polar.lean` (A–C), `Physicslib4/Operators/Modular/Modular.lean` (D).
Blueprint: `blueprint/src/sections/sec10/tomita-takesaki.tex` (§ modular operator / modular conjugation).

**VERDICT: REVISE.** There is 1 blocking item, a documentation-accuracy fix only. Every statement checked is true, and the batch-D statements follow from A–C plus stage 1.

## Diagnostics

`lean_diagnostic_messages` on both files shows only `declaration uses sorry` warnings: 44 in Polar.lean and 10 in Modular.lean. No errors.

## Definitions (none contain `sorry`)

- `pmapMul B A`: this is `B.comp (A.domRestrict ((Dom B).comap A).map ι)`. Its domain is `{x ∈ Dom A | Ax ∈ Dom B}` and its values are `B(Ax)`. Correct.
- `adjointMulSelf T := pmapMul T† T`. This is T†T with the intended domain. Correct.
- `absoluteValue T hT hcl := functionalCalculus (isSelfAdjoint_adjointMulSelf hT hcl).1 (√·)`. The hypotheses are arguments, so there is no junk branch. `Real.sqrt` is 0 on negatives, which is harmless because T†T ≥ 0. Correct.
- `antiunitaryConj W A := W ∘ (A.comp ⟨(Dom A).comap W⁻¹, W⁻¹ ∘ ι⟩)`. Its domain is `{x | W⁻¹x ∈ Dom A}` and its value is `W(A(W⁻¹x))`. The ring homs compose as conj∘id∘conj = id. Correct.
- `modularOperator := adjointMulSelf S′`, `modularOperatorSqrt := absoluteValue S′ …` (= s(Δ) = |S′|), and `modularOperatorInvSqrt := functionalCalculus (Δ s.a.) (√x)⁻¹`. Correct. The junk `(√0)⁻¹ = 0` is harmless because Δ is injective (μ({0}) = 0) and positive.
- `modularConjugation := (Classical.choose (polar_decomposition …)).trans C`. `LinearIsometryEquiv.trans e₁ e₂` applies e₁ first, so J x = C (V x), which is J = CV as in def:modular-conjugation. The type `H ≃ₗᵢ⋆[ℂ] H` comes from `RingHomCompTriple id conj conj`. Correct.

## Classical.choose and independence of C

The `polar_decomposition` spec fixes V on `Range |S′|`, because `V(|S′|ψ) = S′ψ` there. That range is dense (`absoluteValue_injective_denseRange`), and V is continuous, so every witness V is the same map. J therefore does not depend on which V was chosen.

`modular_objects_independent_of_conjugation` holds:
- **Δ:** S′_C = C S, so S′_C† S′_C = S† S as a partial map, domains included.
- **Δ^{1/2}:** this follows from the Δ equality by `subst`, since the functional calculus is proof-irrelevant in `hA`.
- **J:** C_i V_i |S|ψ = Sψ, so both J's equal the continuous extension of S∘|S|⁻¹ on a dense set. This is exactly `eq_modularConjugation_of_continuous`.

## Truth of key statements (all checked TRUE)

polar_decomposition, polar_decomposition_unique, absoluteValue_domain, isSelfAdjoint_adjointMulSelf, inverse_eq_functionalCalculus_inv (with `0⁻¹=0` harmless given `hinj`), exists_antiunitaryConj_pvm (ν_ψ = μ_{W⁻¹ψ}, since the value is real), pmapIntegral_/functionalCalculus_antiunitaryConj, modularOperator_properties, mem_modularOperator_iff, tomitaOperator_eq_modularConjugation_sqrt, modular_objects_independent_of_conjugation, modularConjugation_involution, modularConjugation_conj_modularOperator.

Notes on individual statements:
- `exists_antiunitaryConj_pvm` and `functionalCalculus_antiunitaryConj` take **real** f only. This is right: for complex f the conjugate is f̄.
- In `mem_modularOperator_iff`, the inner-product order was checked: ⟪Sφ,Sψ⟫ = conj⟪S′φ,S′ψ⟫ = ⟪S′ψ,S′φ⟫ = ⟪χ,φ⟫. Correct.
- `spectralMeasure_antiunitaryConj` quantifies over all `E`. This is fine because `ProjectionValuedMeasure.notMeasurable'` sends non-measurable sets to 0 on both sides.
- `tomitaOperator := C ∘ S′` (Tomita.lean:328), so S ψ = C V |S′| ψ = J Δ^{1/2} ψ.

## Composability (D from A–C)

- **`modularConjugation_involution`:** polar_decomposition_unique applies to S′ = (C J⁻¹) P (from `linearizedTomita_closure_eq_unitary_conj_invSqrt`). It gives P = |S′| and U|S′|ψ = S′ψ. Then U = chosen V on a dense range, so CJ⁻¹ = CJ. This composes.
- **`modularConjugation_conj_modularOperator`:** sq_sqrt_functionalCalculus (Δ = q(Δ^{1/2})), functionalCalculus_antiunitaryConj with f = x², the involution, and sq_inv_sqrt_functionalCalculus. This composes. It needs a small `functionalCalculus_congr` (A = B → fc hA f = fc hB f) and the cast `((x^2:ℝ):ℂ) = (x:ℂ)^2`.
- **`tomitaOperator_eq_symm_conj_invSqrt`:** see finding 2.

## Findings

### Blocking

1. **pmapMul `**Restriction:**` is inaccurate.** It says the general form waits on "a semilinear version of this product (the semilinear `LinearPMap.comp` …)". Mathlib's `LinearPMap.comp` (LinearPMap.lean:745, `E →ₛₗ.[σ] F`, `RingHomCompTriple`) and `domRestrict` (l.766) are already semilinear, and `antiunitaryConj` in the same file uses semilinear `comp`. The general form waits on nothing.
   - **Fix (preferred):** generalize `pmapMul` to `(B : H →ₛₗ.[τ] H) (A : H →ₛₗ.[σ] H) [RingHomCompTriple σ τ ρ] : H →ₛₗ.[ρ] H` and drop the line.
   - **Fix (alternative):** reword it as a deliberate restriction, "the general form is expressible with Mathlib's semilinear `LinearPMap.comp`, and is not generalized because no downstream node uses an antilinear factor". CLAUDE.md requires the line to name what the general form is waiting on, so the preferred fix is cleaner.

### Optional

2. **`inverse_unitary_compPMap` does not cover the case its consumer uses.** Its Restriction is accurate (Mathlib `LinearPMap.inverse` is `E →ₗ.[R] F` only). However, the blueprint proof of lmm:tomita-inverse-as-product cites lmm:inverse-of-product-with-bijection with W = J **antiunitary**, and the Lean lemma covers only unitary U. So the unitary version currently has no consumer. The Lean statement of `tomitaOperator_eq_symm_conj_invSqrt` is still provable pointwise:
   - ψ = S(Sψ) = J Δ^{1/2}(Sψ), so J⁻¹ψ ∈ Range Δ^{1/2} = Dom Δ^{-1/2} with Δ^{-1/2}J⁻¹ψ = Sψ (`inverse_sqrt_functionalCalculus`, `tomitaOperator_inverse_eq_self`). The converse is similar.

   Fix: add to the Restriction line that the antiunitary case (used by lmm:tomita-inverse-as-product) is argued pointwise in that proof. Alternatively, BLUEPRINT: adjust that proof's `\uses`.
3. **Some polar-decomposition lemmas take hypotheses they do not use.**
   - `hran` is unnecessary in `absoluteValue_injective_denseRange`, `exists_polarIsometry_on_range` and `existsUnique_polarIsometry`. Range |T| is dense from self-adjointness plus injectivity. Only `polar_decomposition`, for surjectivity of V, needs `hran`.
   - `hinj` and `hran` are unnecessary in `polar_decomposition_unique`: T = UP gives T†T = PP, so P = |T|.

   `polar_decomposition_unique` has about 10 binder groups. Dropping these two brings it to 8 and makes the lemmas easier to apply. The blueprint states them under standing hypotheses, so this is cosmetic.
4. **The polar hypotheses repeat.** `(hT, hcl, hinj, hran)` recurs about 6 times. They could be bundled as a named `Prop` structure (for example `IsPolarizable T`), but structures are design decisions, so this is only a proposal.
5. **`antiunitaryConj` reuses a label.** The def cites `lmm:antiunitary-conjugate-spectral-measure`, the same label as `spectralMeasure_antiunitaryConj`. The definition itself has no blueprint node of its own (the product def covers WAW⁻¹). Consider pointing the docstring at def:product-of-unbounded-operators.
6. **Several conclusions are long conjunctions** (`modularOperator_properties` has 6 conjuncts, `absoluteValue_closed` has 4). They mirror the blueprint nodes, so this is acceptable. Splitting them would ease rewriting downstream.
