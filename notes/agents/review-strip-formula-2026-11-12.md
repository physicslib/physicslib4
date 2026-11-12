# Review: `sbsctn:strip-formula` (tomita-takesaki.tex, lines 2262-2466)

The mathematics is correct throughout, and both statements fit their stage 5 uses. What needs revising is one citation that does not apply, one real-to-complex step left implicit, three proofs that are too large, and where the file lives. Validation reports no issues in this subsection; its 14 errors are all in the spectral-theorem files.

## Soundness, checked line by line

- **The dslope construction (`lmm:strip-quotient-regular`).** `continuousOn_dslope (h : s ∈ 𝓝 a) : ContinuousOn (dslope f a) s ↔ ContinuousOn f s ∧ DifferentiableAt 𝕜 f a` (Mathlib/Analysis/Calculus/DSlope.lean:108). It applies with s = S, which is a neighbourhood of 0 because S° ⊆ S is open and contains 0. DifferentiableAt f 0 follows from DifferentiableOn on the open set S°. At boundary points, continuity is part of this lemma, so no separate argument is needed. `Complex.differentiableOn_dslope (hc : s ∈ 𝓝 c)` (RemovableSingularity.lean:60) applies with s = S°. It needs S° ∈ 𝓝 0, not differentiability on a neighbourhood of every point. Correct.
- **The denominator.** dslope s 0 (0) = deriv s 0 = π (`dslope_same`). Off 0 it is sin(πz)/z, and the only zero of sin(πz) in S is z = 0 (`Complex.sin_eq_zero_iff` gives z = k with |k| ≤ 1/2). Correct.
- **Rectangle signs.** Mathlib's statement (CauchyIntegral.lean:279) is ∫_{z.re}^{w.re} f(x+z.im I) − ∫ f(x+w.im I) + I•∫_{z.im}^{w.im} f(w.re+yI) − I•∫ f(z.re+yI) = 0. With z = −1/2 − iT and w = 1/2 + iT this gives −H + iV₊ − i(−V₋) = 0, so i(V₊+V₋) = H. That matches the blueprint. The closed rectangle `[[z.re,w.re]] ×ℂ [[z.im,w.im]]` lies in S and the open one in S°.
- **Horizontal bound.** |sin(πx ± iπT)| ≥ πT, and |f(z) − f(0)| ≤ 2M uses z, 0 ∈ S. This gives 2M/(πT). Then `intervalIntegral.norm_integral_le_of_norm_le_const` gives C·|b−a| with |b−a| = 1, so ‖H‖ ≤ 4M/(πT) → 0. Correct.
- **Vertical limit.** `MeasureTheory.intervalIntegral_tendsto_integral (hfi) (ha : Tendsto a l atBot) (hb : Tendsto b l atTop)` matches the use.
- **The cosh integrals.** cosh x = 1 + 2 sinh²(x/2) ≥ 1 + x²/2 ≥ (1+x²)/2. F(t) = 2 arctan(eᵗ) has F′(t) = 2eᵗ/(1+e²ᵗ) = sech t, with limits 0 and π. `integral_of_hasDerivAt_of_tendsto` (IntegralEqImproper.lean:1054) gives n − m. `Measure.integral_comp_mul_left : ∫ g(a x) = |a⁻¹| • ∫ g` gives ∫ dt/cosh(πt) = 1. Correct. One detail: `Real.tendsto_arctan_atTop` lands in 𝓝[<](π/2), so it needs `.mono_right nhdsWithin_le_nhds`.
- **Final algebra.** Each ∫(f(±½+it) − f(0))/cosh = ∫ f(±½+it)/cosh − f(0). Summing gives 2f(0). Then ∫(a+b)/(2c) = ½∫(a+b)/c by `MeasureTheory.integral_div`. Correct.
- **Fourier.** `Real.fourier_real_eq_integral_exp_smul : 𝓕 f w = ∫ v, exp(↑(−2π v w) I) • f v` (FourierTransform.lean:488), so θ = −2πw. `Continuous.fourierInv_fourier_eq (h : Continuous f) (hf : Integrable f) (h'f : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) = f` (Inversion.lean:175) is used correctly, with 𝓕h = 0 integrable.
- **Edge cases and hypotheses.** M ≥ 0 is forced because S is nonempty. In `lmm:cosh-dominated-integrable` the hypothesis K ≥ 0 is implied by the norm bound, so it can be dropped. In `lmm:strip-quotient-formula` and `lmm:strip-denominator-ne-zero`, the hypotheses on f (and on f at all, for the denominator) are unused, because these are pure algebra. Drop them so the Lean statements are minimal.
- **Fit for stage 5.**
  - `thrm:strip-formula`: f : ℂ → ℂ with hypotheses only on S suits f(z) = λ^{2z}⟨aΔ^{−z}ξ, Δ^{z̄}η⟩, because junk values off S are harmless. "Bounded on S" should read ∃ M, ∀ z ∈ S, ‖f z‖ ≤ M.
  - `thrm:fourier-uniqueness`: the hypotheses (continuous, integrable, ∫ e^{iθt}h = 0 for all θ) fit g(t). Integrability comes from `lmm:cosh-dominated-integrable`, and all θ are reached via λ = e^θ.

## Blocking issues

1. **`thrm:fourier-uniqueness`: the cited lemma does not apply.** `FourierTransform.fourierInv_zero` (Notation.lean:132) needs a `FourierInvAdd E F` instance. Mathlib has such instances only for Lp, 𝓢 and 𝓢′, not for plain functions `V → E`, because Fourier additivity fails off integrable functions. Fix: get 𝓕⁻ 0 = 0 pointwise from `Real.fourierInv_eq` (FourierTransform.lean:450) together with `smul_zero` and `MeasureTheory.integral_zero`.
2. **`thrm:strip-formula`: the real-to-complex step is implicit.** Lemmas `lmm:inv-cosh-pi-integrable` and `lmm:integral-inv-cosh-pi` are real-valued, but the proof integrates the complex-valued f(0)/cosh(πt). Fix: name `MeasureTheory.Integrable.ofReal` and `integral_ofReal`. Also split the final proof (about 15 Lean lines): add a lemma `lmm:strip-boundary-split` stating ∫ (f(±½+it) − f(0))/cosh(πt) dt = ∫ f(±½+it)/cosh(πt) dt − f(0). It uses `integral_sub`, `integral_const_mul`, `integral_ofReal` and Lemmas `lmm:integral-inv-cosh-pi` and `lmm:strip-boundary-integrable`. The theorem then only adds the two instances and halves the result.
3. **`lmm:strip-rectangle-identity` is about 15–20 lines with three moves.** The moves are: the rectangle inclusions after min/max simplification, the Mathlib call, and rewriting both vertical integrals by `intervalIntegral.integral_congr` before the `linear_combination`. Split out:
   - (a) `lmm:strip-rectangle-subset`: [[−½,½]] ×ℂ [[−T,T]] ⊆ S and Ioo(−½,½) ×ℂ Ioo(−T,T) ⊆ S°;
   - (b) `lmm:strip-vertical-sides`: ∫_{−T}^{T} g(½+it) dt = V₊(T) and ∫_{−T}^{T} g(−½+it) dt = −V₋(T).
4. **`lmm:integral-inv-cosh` is about 15 lines with three moves** (a derivative calculation, two limits, then the improper FTC). Split out `lmm:hasDerivAt-two-arctan-exp`: HasDerivAt (fun t ↦ 2 arctan(eᵗ)) (1/cosh t) t. Mention the `nhdsWithin_le_nhds` coercion for the arctan limit.

## Non-blocking issues

- **File layout.** tomita-takesaki.tex is 2466 lines, far past the roughly 500-line guideline. This subsection is self-contained scalar complex analysis with no Tomita dependency. Move it to its own chapter file, `blueprint/src/sections/sec10/strip-formula.tex`, which is `\input` before tomita-takesaki. This changes the layout, so flag it for the user.
- **Missing definitions.** g, V±, H are defined only in prose. Add `definition` blocks (for example `def:strip-quotient`) so the Lean definitions get a label and `\lean{}` tracking, and the lemma statements refer to them.
- **Hypotheses to drop:** K ≥ 0 in `lmm:cosh-dominated-integrable`, and the f-hypotheses in `lmm:strip-quotient-formula` and `lmm:strip-denominator-ne-zero`.
- **Proofs that are fine as written** (small or borderline, no split needed): `lmm:inv-cosh-le` (about 7 lines), `lmm:sin-norm-lower-bound` (about 10, borderline), and the rest at 3–8 lines each.
- **Citations.** The other names were spot-checked and exist with the claimed statements. Prose is in the present tense. The Jones citation is present.

VERDICT: REVISE

## Pass 2 (2026-11-12)

VERDICT: PASS. All four blocking findings are resolved (pointwise 𝓕⁻0 = 0 via `Real.fourierInv_eq`; explicit `Integrable.ofReal`/`integral_ofReal` in `lmm:strip-boundary-split`; splits `lmm:strip-rectangle-subset`, `lmm:strip-vertical-sides`, `lmm:hasDerivAt-two-arctan-exp`). New nodes re-derived: signs give i(V₊+V₋) = H; ∫(a−c)/k = ∫a/k − c. Minor, for the formalizer/prover: T > 0 unused in `lmm:strip-vertical-sides`; the cast in `lmm:strip-boundary-split` also needs `Complex.ofReal_div`, `Complex.ofReal_one`; `div_div` gives c·2 (needs `mul_comm`) in `thrm:strip-formula`. Deferred by the orchestrator: definition blocks for g, V±, H; moving the subsection to its own file.
