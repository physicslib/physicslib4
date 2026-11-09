# Review: `blueprint/src/sections/sec10/tomita-takesaki.tex` (stages 1–2)

Reviewer pass on 2026-11-09, covering 67 nodes, none formalized yet.

## Verdict

**REVISE.** I found no false statement: every statement I checked is true as written. Before formalization the file needs four kinds of fix:
- two grounding gaps: there is no inverse-operator node, and `lmm:fc-core` applies "core" to an operator not known to be closed;
- an unjustified separability assumption;
- one wrong citation target;
- about ten proofs that are too large for one node, judged against the spike sizes in `tomita-stage2-trial.md`.

`mcp__fuse__blueprint_validate` reports only the 14 known `conv:*` errors, all in the spectral chapters. Nothing comes from this file and there are no cycles. All 49 cited external labels exist (each one checked by grep). `check_temporal_wording.py` passes.

## Blocking findings

1. **The preamble (line 7) assumes separability without justification.** The Lean `Spectral` directory deliberately carries no `SeparableSpace H` (see the module docstring of `Physicslib4/Spectral/Basic.lean`, around line 85: separability "is *never* needed in this directory"). The only exception is `completeSpace_and_separableSpace_of_isClosed` (`Integral.lean:399`), which is the Lean name of `lmm:closed-subspace-is-hilbert`. The file also contradicts itself: `def:reference-conjugation` says "no separability is needed". Fix:
   - Replace "a separable complex Hilbert space" with "a complex Hilbert space", and add a sentence saying that the results of Section `sctn:unbounded-spectral-theorems` that are used here hold without separability, as their Lean forms do.
   - In `lmm:core-of-adjoint-product`, replace the citation of `lmm:closed-subspace-is-hilbert` with completeness of a closed subspace (Mathlib `IsClosed.completeSpace_coe`). Otherwise the Lean proof inherits `[SeparableSpace H]`.

2. **The blueprint has no unbounded inverse, but `lmm:inverse-functional-calculus`, `crllr:inverse-square-root`, `lmm:tomita-inverse-polar` and `crllr:modular-conjugation-inverts` all use one.** They use "A⁻¹ with domain Range(A)", S⁻¹ for the antilinear S, and the identity (JΔ^{1/2})⁻¹ = (Δ^{1/2})⁻¹J⁻¹. The only inverse node is `def:bounded-inverse` in `spectral-theorems.tex`, which is bounded. Add:
   - `def:inverse-of-operator`: for injective A, Γ(A⁻¹) is the flip of Γ(A) and Dom(A⁻¹) = Range(A). This is Mathlib's `LinearPMap.inverse`.
   - `lmm:inverse-of-product-with-bijection`: (WA)⁻¹ = A⁻¹W⁻¹ for a (anti)unitary W.
   - `lmm:tomita-inverse-is-self`: S⁻¹ = S as operators, from `thrm:tomita-operator-involution`.

   Then cite these in `lmm:tomita-inverse-polar`, and make `lmm:inverse-functional-calculus` use `def:inverse-of-operator`.

3. **`lmm:fc-core` is ill-typed as stated.** `def:core` requires a closed operator, but closedness of f(A) for complex f is not established anywhere: `prpstn:hall-10.3` gives self-adjointness only for real f. Only f = s is used. Fix: restrict to real f and cite `prpstn:hall-10.3` and `prpstn:hall-9.8` for closedness. Alternatively, keep complex f but drop the word "core" and state only the explicit convergence.

4. **`thrm:von-neumann-adjoint-product` cites the wrong node.** It cites `thrm:hall-9.21`, whose statement is the ±i essential-self-adjointness criterion. What it actually uses is `adjoint_eq_of_range_eq_top` (`Spectrum.lean:323`): S ≤ S†, ran(S − μ) = ⊤ and ker(S† − μ) = ⊥ imply S† = S. That result has no blueprint node of its own, and the proof re-derives it inline. Fix: add `lmm:self-adjoint-of-range-eq-top` with `\lean{Physicslib4...adjoint_eq_of_range_eq_top}`, cite it, and delete the inline re-derivation. This also helps with item 5.

5. **Proofs that are too large for one node.** Size estimates use the spike line counts where available.

   | Label | Estimated Lean size | Split |
   |---|---|---|
   | `lmm:antiunitary-composition` | 5 separate claims, 30+ lines | (a) isometric and continuous; (b) W⁻¹ antiunitary; (c) WU and UW antiunitary, W₁W₂ unitary; (d) an antilinear isometric bijection is antiunitary (polarization). Better: model antiunitaries as Mathlib `H ≃ₗᵢ⋆[ℂ] H` (`LinearIsometryEquiv` over `starRingEnd ℂ`). Then (a)–(c) are `trans`/`symm` and only the inner-product identity remains. |
   | `thrm:von-neumann-adjoint-product` | spike: main part about 40 lines | (a) `lmm:von-neumann-symmetric-positive`: D ≤ D* and positivity; (b) `lmm:von-neumann-kernel`: ker(D* + 1) = 0 via `prpstn:hall-9.12` and `prpstn:hall-9.13`; (c) the theorem, applying item 4's lemma with μ = −1. |
   | `lmm:fc-dominated-convergence` | spike `fc_tendsto_bdd` about 50 lines | (a) ‖h_n(μ)ψ − t_n(μ)ψ‖ → 0 by dominated convergence; (b) combine with `lmm:truncations-converge`. |
   | `lmm:pushforward-pvm` | 3 moves | (a) φ_*μ is a PVM with (φ_*μ)_ψ = φ_*(μ_ψ); (b) W domains agree (`lintegral_map`); (c) operators agree by the uniqueness clause of `prpstn:hall-10.1`. |
   | `lmm:antiunitary-conjugate-pvm` | 3 moves | (a) ν is a PVM with ν_ψ = μ_{W⁻¹ψ}; (b) domain identity; (c) operator identity for real f by form uniqueness. |
   | `lmm:closure-transfer-common-core` | spike (v): 40–60 lines | (a) one direction: an isometry on a common core of closed A, B gives Dom A ⊂ Dom B with equal norms; (b) the symmetric statement as a two-line corollary. |
   | `lmm:absolute-value-norm-on-core` | spike (ii): 25–35 lines | (a) x ∈ Dom D implies x ∈ W_s (support plus `lmm:l2-implies-l1`); (b) the norm identity. |
   | `lmm:polar-isometry` | construction, extension, domain identity | (a) V₀ on Range(\|T\|) is well defined, linear and isometric; (b) the BLT extension, its uniqueness and T = V\|T\|. |
   | `crllr:inverse-square-root` | 3 moves | (a) A^{1/2} is injective (pushforward of the null atom); (b) (A^{1/2})⁻¹ = r(A); (c) r(A) is positive and self-adjoint. Note that ι⁻∘s = r holds everywhere, so no null-set step is needed. |
   | `lmm:tomita-inverse-polar` | 3–4 moves | Use the item 2 lemmas: (a) S = J⁻¹P as operators; (b) P is positive and self-adjoint, and CJ⁻¹ is unitary. |
   | `crllr:modular-conjugation-inverts` | 3 moves | (a) the general lemma (A^{1/2})² = A for positive self-adjoint A; (b) (A^{-1/2})² = A⁻¹; (c) assembly via `crllr:antiunitary-conjugate-functional-calculus`. Lemma (a) can be shared with `lmm:positive-square-root-unique`. |
   | `lmm:inverse-functional-calculus` | two inclusions, about 20 lines | (a) ι⁻(A) ⊇ A⁻¹; (b) Dom ι⁻(A) ⊂ Range A. |

## Optional findings

6. **Missing `\uses` edges.**
   - `lmm:fc-composition-domain` passes from the set identity of `lmm:fc-associated-measure` to ∫|f|² dμ_{gψ} = ∫|f|²|g|² dμ_ψ. That step needs measure extensionality plus `lintegral_withDensity_eq_lintegral_mul`. Better: restate `lmm:fc-associated-measure` as μ_{h(μ)ψ} = μ_ψ.withDensity(|h|²), which is the spike's recommended shape `assoc_functionalCalculus`.
   - `lmm:absolute-value-norm-on-core` and `crllr:modular-conjugation-inverts` use ι(A) = A, that is A = ∫λ dμ^A. Add `thrm:hall-10.4` to their `\uses`.
7. **`lmm:cyclic-commutant-separating`** lists `thrm:statistical-independence` in its proof `\uses`. That pulls net theory into a section that says it "involves no net", and the theorem is not actually used. Keep the remark as prose and drop the edge.
8. **`def:product-of-unbounded-operators`, "Equality of operators", and `def:hall-3.1`.** `def:hall-3.1` requires a dense domain, but products (T*T before `lmm:von-neumann-dense-domain`) and inverses need not be densely defined. Say explicitly that products and inverses are partial maps that need not be densely defined. Mathlib's `LinearPMap` has no density requirement either. Also note that the trial recommends characterising T*T by a graph hypothesis rather than a new `def`. That is a design decision for the user (CLAUDE.md), so flag it rather than encode it.
9. **File layout.** At 670 lines the file is past the ~500-line guideline, and stages 3–5 are still to come. Proposed split (this is a design decision, so flag it to the user):
   - `sec10/tomita-operator.tex`: the current subsection 1;
   - `sec10/unbounded-operator-toolkit.tex`: products, cores, von Neumann, the composition law, pushforward and antiunitary conjugation, |T|, the polar decomposition and inverses. These are general unbounded-operator results with no M or Ω, and they belong next to the unbounded spectral chapter;
   - `sec10/modular-objects.tex`: Δ and J.
10. **Notation** is consistent with sec10: `\text{Dom}`, `\left< \cdot,\cdot \right>`, `\mathbf{H}`, `W_f`, `\mu_\psi`. One clash: Ω is both the cyclic vector and the σ-algebra Ω(X) (line 310). Rename the σ-algebra locally, or add a sentence noting the clash.

## Per-declaration soundness pass (summary)

**Stage 1.** I instantiated every statement on its defining data.
- `lmm:tomita-adjoint-relation`: ⟨bΩ, a*Ω⟩ = ⟨abΩ, Ω⟩ = ⟨baΩ, Ω⟩ = ⟨aΩ, b*Ω⟩. Correct for the first-slot-antilinear convention, and both sides are antilinear in x and in y.
- `lmm:linearized-adjoint-extends`: ⟨Cy, CS₀x⟩ = conj⟨y, S₀x⟩ = ⟨F₀y, x⟩, so (S₀′)*∘C = F₀, that is (S₀′)* ⊇ F₀C (using C = C⁻¹). Correct.
- Closability, the closure of Γ(S₀) by the real homeomorphism Φ, the flip invariance (aΩ, a*Ω) ↦ (a*Ω, a**Ω), the bijectivity of S with S² = 1 on Dom S, and the injectivity and dense range of S′: all correct.

**Setting.**
- `def:von-neumann-algebra-commutant-convention` (self-adjoint and M = M″) is the right notion. It is satisfiable: take M = B(H), or M = ℂ1 on H = ℂ with Ω ≠ 0.
- `def:cyclic-separating-vector` (cyclic for M and for M′) is equivalent to cyclic and separating, by `lmm:cyclic-commutant-separating` and its converse. The converse is not needed.

**Von Neumann's theorem.** The solvability decomposition gives T*v = −u and Tx = −v, so T*Tx = u. The form identity, density, the core property and the theorem itself are all correct.

**Composition law.** f(μ)g(μ) ⊂ (fg)(μ) with Dom = W_g ∩ W_{fg} matches Schmüdgen Thm 4.16.
- The proof's two applications of the bounded-left lemma are valid: 1_{E_n}f is bounded.
- The left-hand limit uses E_n ↑ X, which holds because f is finite-valued.

**Commuting with projections, pushforward and fc-of-fc.** Correct. Note that fc-of-fc is stated only for real f, as it must be.

**|T| results.**
- Dom|T| = Dom T with ‖|T|ψ‖ = ‖Tψ‖: correct via the common core Dom(T*T).
- Square-root uniqueness: PP = q(P) because λ² ≤ 1 + λ⁴, and s∘q = |λ| = λ μ^P-a.e. Correct.

**Polar decomposition** (hypotheses: closed, densely defined, injective, dense range).
- |T| is injective with dense range.
- V is unitary because Range(T) is dense and an isometric range is closed.
- Uniqueness: (UP)*(UP) = PP. The domain bookkeeping holds because U⁻¹U = 1 everywhere.

**Inverses and conjugation.**
- `lmm:antiunitary-conjugate-pvm`: correctly restricted to real f (for complex f the conjugate function appears).
- Corollaries: correct.

**Modular objects.**
- `lmm:modular-operator-intrinsic`: checked linearity in φ on both sides. Correct.
- J = CV is antiunitary, and S = JΔ^{1/2} with equal domains.
- J is the unique continuous map with JΔ^{1/2} = S.
- Independence from C: correct.
- Second polar decomposition: CJ⁻¹ = V = CJ, so J² = 1, and JΔ^{-1/2}J = Δ^{1/2}, hence JΔ^{1/2}J = Δ^{-1/2}.
- JΔJ = Δ⁻¹: q∘s = λ and q∘r = ι⁻ off (−∞, 0], which is μ^Δ-null. Correct.

The statements to watch are the lemmas whose proofs rely on undefined objects: item 2 (inverse) and item 3 (core).

## Per-declaration granularity pass (summary)

**Small enough (≤ ~10 lines, one or two moves):**
- `lmm:reference-conjugation-properties`, `lmm:commutant-von-neumann-algebra`, `lmm:cyclic-commutant-separating`
- `lmm:tomita-pre-operators-well-defined`, `lmm:tomita-pre-operators-dense-involutive`, `lmm:tomita-adjoint-relation`
- `lmm:linearized-adjoint-extends`, `lmm:closable-of-dense-adjoint`, `crllr:linearized-tomita-closable`
- `lmm:tomita-operator-independent-of-c`, `lmm:tomita-graph-flip`, `thrm:tomita-operator-involution`, `crllr:linearized-tomita-properties`
- `lmm:von-neumann-form`, `lmm:von-neumann-dense-domain`
- `lmm:fc-bounded-left-composition`, `lmm:fc-associated-measure`, `lmm:fc-composition-domain`, `thrm:fc-composition` (spike: 15 lines), `lmm:fc-commutes-with-projections`, `lmm:fc-core`, `crllr:fc-of-fc`
- `lmm:absolute-value-closed`, `thrm:absolute-value-domain`, `lmm:positive-square-root-unique` (borderline)
- `lmm:absolute-value-injective-dense-range`, `thrm:polar-decomposition`, `lmm:adjoint-unitary-product`, `thrm:polar-decomposition-unique`
- `lmm:injective-no-atom-at-zero`, `crllr:antiunitary-conjugate-functional-calculus`
- `thrm:modular-operator-properties`, `lmm:modular-operator-intrinsic`, `thrm:modular-conjugation-polar`, `lmm:modular-conjugation-intrinsic`
- `thrm:modular-objects-independent-of-c`, `thrm:modular-conjugation-involution`

**Borderline but acceptable:**
- `lmm:von-neumann-solvability` (about 25–30 lines with the WithLp graph pullback). Consider splitting off "Γ(T) is a closed subspace of WithLp 2 (H × H)".
- `lmm:core-of-adjoint-product` (spike: 30 lines). Consider splitting off "(y, Ty) ⊥ Γ(T|_{Dom T*T}) implies y ⊥ ran(1 + T*T)".

**Too large:** the 12 labels in item 5.

---

## Pass 2 (re-review of the revised file: 897 lines, 87 nodes)

### Verdict

**PASS.** All five blocking findings are resolved. The 20 new nodes are sound, small and grounded. What remains is optional.

Checks run:
- `blueprint_refresh`: 811 declarations.
- `blueprint_validate`: only the 14 known `conv:*` errors in the spectral chapters. None come from this file, and there are no cycles.
- The two newly cited external labels exist: `def:hall-9.2` (`unbounded-spectral-theorems.tex:170`) and `thrm:operator-valued-integration` (`spectral-theorems.tex:515`).
- `check_temporal_wording.py`: OK.

### Blocking findings from pass 1

1. **Separability: resolved.**
   - The preamble now says only "complex Hilbert space" and explains why the separable spectral chapter still applies.
   - `lmm:core-of-adjoint-product` cites `IsClosed.completeSpace_coe` and no longer cites `lmm:closed-subspace-is-hilbert`.
2. **Inverse: resolved.**
   - `def:inverse-of-operator` defines the inverse by the flipped graph, with Dom = Range. This matches `LinearPMap.inverse`.
   - `lmm:inverse-of-product-with-bijection` is correct: both sides have domain W(Range A) = {φ : W⁻¹φ ∈ Range A}.
   - `lmm:tomita-inverse-is-self` is correct.
   - `lmm:tomita-inverse-as-product` uses all three. The hypothesis of the product lemma (injectivity of Δ^{1/2}) comes through `crllr:inverse-square-root` → `lmm:square-root-injective`.
3. **`lmm:fc-core`: resolved.** It is now stated for real f, with closedness from `prpstn:hall-10.3` and `prpstn:hall-9.8`.
4. **Range criterion: resolved.** `lmm:self-adjoint-of-range-eq-top` has the same hypotheses as `adjoint_eq_of_range_eq_top` (S ≤ S†, Range(S − μ) = ⊤, Ker(S† − μ) = ⊥), and the von Neumann theorem is now a pure assembly of its parts.
5. **Splits: resolved.** All 12 splits are made as specified, and each resulting node is at most about 10 Lean lines with one or two moves.

### Soundness of the 20 new nodes

- `lmm:antiunitary-isometric`, `lmm:antiunitary-composition` (narrowed), `lmm:antilinear-isometry-antiunitary`: correct.
- `lmm:von-neumann-symmetric-positive`: ⟨x′, Dx⟩ = ⟨Tx′, Tx⟩ = conj⟨x, Dx′⟩ = ⟨Dx′, x⟩. Correct.
- `lmm:von-neumann-kernel`: Ker(D* + 1) = Range(D + 1)^⊥, by 9.12 and 9.13 with D densely defined. Correct.
- `lmm:fc-difference-to-truncation`: the dominating function 4|h|² is integrable. Correct.
- `lmm:pushforward-pvm-is-pvm`, `lmm:pushforward-pvm-domain`, `lmm:pushforward-pvm`: correct. For ψ ∈ W_g, the function g is in L¹ because μ_ψ is finite.
- `lmm:adjoint-product-domain-in-sqrt-domain`, `lmm:absolute-value-norm-on-core`: correct.
- `lmm:closure-transfer-one-direction`: correct. D is a subspace, so the Cauchy estimate is valid.
- `lmm:polar-isometry-on-range`: correct.
- `lmm:inverse-fc-extends`, `lmm:inverse-fc-domain`: correct. ι⁻ι and ιι⁻ are bounded and equal 1 off {0}, which is null.
- `lmm:square-root-injective`, `lmm:inverse-square-root-positive`: correct.
- `lmm:square-of-square-root`: q∘s = λ off (−∞, 0). Correct.
- `lmm:square-of-inverse-square-root`: q∘r = ι⁻ off (−∞, 0), and both vanish at 0. Correct.
- `lmm:antiunitary-conjugate-pvm-is-pvm`, `lmm:antiunitary-conjugate-pvm-domain`: correct.
- `lmm:tomita-inverse-as-product`: correct. The bookkeeping Δ^{-1/2}J⁻¹ = J⁻¹(JΔ^{-1/2}J⁻¹) holds with equal domains because JJ⁻¹ = 1 everywhere.

### Optional findings

- **O1. `lmm:square-root-injective`: wrong lemma cited for the kernel step.** The proof cites `lmm:range-membership-concentrates-measure`, which goes the other way (range membership implies concentration). The step actually needed is: ‖A^{1/2}ψ‖² = ∫ s² dμ^A_ψ = ∫ λ⁺ dμ^A_ψ = 0 gives μ^A_ψ((0, ∞)) = 0 (Mathlib `lintegral_eq_zero_iff`). Together with μ^A((−∞, 0]) = 0 this gives ‖ψ‖² = μ^A_ψ(ℝ) = 0. Rewrite the proof along these lines and drop the wrong citation. The step is small, but a node should not rest on a citation that does not support it.
- **O2. Three nodes still carry two or three claims.** `lmm:square-root-injective` (self-adjoint, positive, injective), `crllr:antiunitary-conjugate-functional-calculus` (spectral measure, identity, positivity and injectivity) and `lmm:fc-core` (closedness plus core). Each is still roughly 10–15 Lean lines, so splitting is optional.
- **O3. `lmm:pushforward-pvm-domain`** cites `lintegral_map`. For the complex (Bochner) integral, `MeasureTheory.integral_map` is the direct lemma.
- **O4. Redundant statement.** `thrm:tomita-operator-involution` already states S⁻¹ = S, which duplicates `lmm:tomita-inverse-is-self`. Drop the "thus S⁻¹ = S" clause from the theorem, or move the new lemma next to it.
- **O5. File length.** The file is now 897 lines, well past the guideline, with stages 3–5 still to come. The three-file split from pass-1 item 9 is still recommended. It is the user's decision.
