# Review: blueprint subsection "Takesaki's KMS Theorem" (`sbsctn:takesaki-kms`), 2026-11-15

Scope: the 26 new nodes at the end of `blueprint/src/sections/sec10/tomita-takesaki.tex`
(lines 3917-4215) and the roadmap sentence at line 5. The design decisions in
`notes/agents/design-takesaki-kms-2026-11-15.md` (reversed flow at beta = 1, the norm-one hypothesis,
the `modularAlgebra` / `modularAutomorphism` / `vectorState` defs) are taken as given.

## Overall assessment

The mathematics is correct throughout. I re-derived every sign and boundary computation with the
inner product conjugate-linear in the first slot, and they all check out. The theorem matches
`Hilbert6.AQFT.IsKMSState` exactly. Every cited existing label states what the new proofs use it
for, every `\uses` target exists (`blueprint_validate` reports no issue in this subsection), and the
Mathlib names cited are real with matching statements. The prose is in the present tense and has no
historical narration.

What blocks a PASS is granularity: four proofs are clearly over the 5-10 Lean-line target. There are
also two small `\uses` omissions.

## Soundness, per declaration

- **def:modular-algebra / lmm:modular-algebra-closed.** `StarSubalgebra.coe_centralizer` gives the
  carrier `(s ∪ star s).centralizer` (Mathlib/Algebra/Star/Subalgebra.lean:317). M' is
  self-adjoint and (M')' = M (lmm:commutant-von-neumann-algebra), so the carrier is M.
  `Set.isClosed_centralizer` (Mathlib/Topology/Algebra/Group/Basic.lean:34) and
  `StarSubalgebra.cstarAlgebra` (needs `[IsClosed]`, Mathlib/Analysis/CStarAlgebra/Classes.lean:50)
  both match. Sound.
- **lmm:vector-functional-state / def:vector-state.** Positivity is <Ω, x*xΩ> = ‖xΩ‖². The bound
  ‖ω‖ ≤ ‖Ω‖² = 1 holds, with equality at 1, and the proof handles H ≠ 0 (needed for ‖1‖ = 1). Matches
  `State` (`isPositive`, `isNormalized`). Sound.
- **lmm:modular-automorphism-well-defined / def:modular-automorphism /
  lmm:modular-automorphism-one-parameter.** Membership comes from
  lmm:tomita-modular-automorphism-subset. Unitarity and the group law come from
  lmm:modular-unitary-group-props, and (Δ^{it}xΔ^{-it})* = Δ^{it}x*Δ^{-it} holds. Sound.
  IsKMSState does not require `IsOneParameterAut`, so the one-parameter lemma is not needed for the
  theorem (it is harmless and useful for `invariant_of_pos`).
- **lmm:spectral-eigenvector-variance.** The identity ∫(λ-c)² dμ_ψ = ‖Aψ‖² - 2c Re<ψ,Aψ> + c²‖ψ‖²
  = ‖Aψ - cψ‖² is correct for ψ ∈ Dom(A) = W_ι. prpstn:hall-10.1 does give ∫ι dμ_ψ = <ψ,Aψ> and
  ∫ι² dμ_ψ = ‖Aψ‖². Sound.
- **lmm:spectral-eigenvector-projection, lmm:spectral-eigenvector-bounded-fc.** Correct.
  f·1_{c} = f(c)·1_{c} pointwise, so multiplicativity applies.
- **lmm:modular-operator-fixes-omega.** I checked the chain. With ξ = η = Ω,
  lmm:tomita-adjoint-intrinsic gives <Ω, Sζ> = <ζ, Ω>. Conjugating gives <Sζ, SΩ> = <Ω, ζ>, which is
  exactly the hypothesis of lmm:modular-operator-intrinsic with ψ = χ = Ω. The input
  (S')*CΩ = Ω is the first conjunct of lmm:tomita-adjoint-on-commutant at b' = 1 (Lean
  `tomitaAdjoint_apply_of_mem_centralizer`). Sound.
- **lmm:modular-unitary-group-fixes-omega.** e_1 = e^{it log 1} = 1 (lmm:modular-unitary-group-fc).
  Sound.
- **lmm:modular-conjugation-commutes-unitary-group.** lmm:modular-conjugation-powers does state
  JΔ^{it}J = Δ^{it}, and so does its Lean form (second conjunct of
  `modularConjugation_indicatorCpow_modularConjugation`, VanDaele.lean:840). The design memo's worry
  that only the cut-off form exists is unfounded. The Lean lemma carries a dummy `1 ≤ n` hypothesis,
  hence "with any n ≥ 1". Sound.
- **lmm:modular-sqrt-on-algebra.** thrm:modular-conjugation-polar includes Dom S = Dom Δ^{1/2}.
  Sound.
- **lmm:takesaki-functions-bounded.** Re(-iz) = Im z. On (0,1), λ^{Im z} ≤ 1 for Im z ≥ 0. On
  [1,∞), λ^{Im z - 1} ≤ 1 for Im z ≤ 1. `Complex.norm_cpow_eq_rpow_re_of_pos`, `Real.rpow_le_one`
  and `Real.rpow_le_one_of_one_le_of_nonpos` all exist with these signatures. Sound.
- **lmm:takesaki-functions-identities.** I checked all four parts case by case:
  - (i) holds because p_{w,n} = 1_{K_n}λ^w and K_n ⊂ (0,∞).
  - (ii) 1_{(0,1)}λ^{-it} + 1_{[1,∞)}λ·λ^{-it-1} = 1_{(0,∞)}λ^{-it}.
  - (iii) -i(t+i) = 1 - it, so u_{t+i} = 1_{(0,1)}λ^{1-it} = s²g_t and v_{t+i} = 1_{[1,∞)}λ^{-it}.
  - (iv) |sv_t| = λ^{-1/2}, |s²v_t| = 1, |sg_t| = λ^{1/2}, |s²g_t| = λ.

  Sound.
- **lmm:modular-sqrt-transfer.** Pair (f,s) at η ∈ W_s ∩ W_{fs} = Dom Δ^{1/2}, then pair (s, fs) on
  W_{fs} ∩ W_{s²f} = H, then self-adjointness of s(Δ) (lmm:fc-real-closed, s real). Sound.
- **lmm:takesaki-approximants-entire / -strip / -uniform / lmm:takesaki-function-analytic.** The
  difference G - G^n = <ξ, u_z(η - E_nη)> + <Δ^{1/2}ξ, v_z(Δ^{1/2}η - E_nΔ^{1/2}η)> holds. The bound
  is uniform in z, and E_n → 1 strongly (lmm:modular-spectral-projections-converge states exactly
  this for every ψ). crllr:modular-power-vector-entire states that w ↦ <η, p_{w,n}(Δ)ξ> is entire.
  `TendstoUniformlyOn.continuousOn`, `TendstoUniformlyOn.tendstoLocallyUniformlyOn` and
  `TendstoLocallyUniformlyOn.differentiableOn` (Mathlib/Analysis/Complex/LocallyUniformLimit.lean:136,
  needs an eventual DifferentiableOn, IsOpen U and NeBot) all match. Sound.
- **lmm:takesaki-function-lower-boundary / -upper-boundary.** G(t) = <ξ, (1_{(0,∞)}e_{-t})(Δ)η>
  = <ξ, Δ^{-it}η>, using lmm:modular-indicator-positive-one. G(t+i) = <Δ^{1/2}ξ, Δ^{-it}Δ^{1/2}η>,
  which is the formal Δ^{-i(t+i)} = Δ^{1/2}Δ^{-it}Δ^{1/2}. Sound.
- **lmm:takesaki-lower-boundary-state.** <a*Ω, Δ^{-it}bΩ> = <Ω, aΔ^{-it}bΔ^{it}Ω>. Sound.
- **lmm:takesaki-upper-boundary-state.** The steps are:
  1. <JaΩ, Δ^{-it}Jb*Ω> = <JaΩ, JΔ^{-it}b*Ω>, by commutation at -t.
  2. This equals <Δ^{-it}b*Ω, aΩ>, by antiunitarity <Jφ,Jψ> = <ψ,φ>.
  3. This equals <Δ^{-it}b*Δ^{it}Ω, aΩ>.
  4. This equals <Ω, Δ^{-it}bΔ^{it}aΩ>, since (Δ^{-it}b*Δ^{it})* = Δ^{-it}bΔ^{it}.

  Sound.
- **thrm:takesaki-kms.** Matches `IsKMSState (fun t => σ_{-t}) 1 ω_Ω` field for field:
  - ContinuousOn on `kmsStrip 1`;
  - DifferentiableOn on `kmsStripInterior 1`;
  - ∃ C bound on the strip;
  - F t = ω(a * α t b);
  - F(t + 1·I) = ω(α t b * a).

  The remark's translation to the B-R (σ,-1) convention is correct: F(-z) at t - i gives ω(σ_t(b)a).
  The hypotheses are satisfiable (for example M = B(H) for H = ℂⁿ ⊗ ℂⁿ with a faithful-state vector),
  and each one is needed.

## Gaps and `\uses`

No mathematical gaps. Small omissions:

1. **lmm:takesaki-function-upper-boundary.** The proof uses boundedness and measurability of
   v_{t+i} (to add g_t + v_{t+i} under the bounded integral) but does not list
   lmm:takesaki-functions-bounded. The lower-boundary proof does list it.
2. **def:modular-automorphism.** Cites Theorem~\ref{thrm:tomita} without `\uses{thrm:tomita}` (or
   lmm:tomita-modular-automorphism). Either add the use or drop the sentence; the def does not need it.

## Granularity, per written proof (estimated Lean lines)

- lmm:modular-algebra-closed: about 8. OK.
- **lmm:vector-functional-state: about 20-25, too big.** It builds the linear map, then
  `mkContinuous`, positivity, ‖ω‖ ≤ 1, and ‖ω‖ ≥ 1 with the H ≠ 0 argument. Split into:
  - (a) `vector functional bound`: ω_Ω is linear with |ω_Ω(x)| ≤ ‖Ω‖²‖x‖, hence a continuous linear
    functional with ‖ω_Ω‖ ≤ 1;
  - (b) `vector functional norm one`: ‖ω_Ω‖ = 1 when ‖Ω‖ = 1;
  - (c) positivity, either in (a) or as its own one-liner.

  def:vector-state then assembles them.
- lmm:modular-automorphism-well-defined: about 12-15 in total, but six independent one- to three-line
  facts that the def's fields discharge separately. Borderline acceptable.
- lmm:modular-automorphism-one-parameter: about 6. OK.
- **lmm:spectral-eigenvector-variance: about 20-25, too big.** It shows integrability of 1, λ and λ²
  (mass ‖ψ‖², the bound |λ| ≤ 1 + λ²), passes between the real and complex integrals of ι, expands
  three integrals and applies `norm_sub_sq`. Split into:
  - (a) `spectral moments integrable`: for ψ ∈ Dom(A), 1, λ and λ² are μ_ψ-integrable, with
    ∫λ dμ_ψ = Re<ψ,Aψ> and ∫λ² dμ_ψ = ‖Aψ‖²;
  - (b) the variance identity, given (a), by algebra alone.
- **lmm:spectral-eigenvector-projection: about 12-15, two distinct moves.** One move is measure
  theory (∫ = 0 with a nonnegative integrand gives μ_ψ(ℝ∖{c}) = 0). The other is projection algebra
  (μ_ψ(E) = 0 gives μ(E)ψ = 0, then μ({c}) + μ({c}ᶜ) = 1). Split out a general PVM lemma: for
  E ∈ Σ, μ_ψ(E) = ‖μ(E)ψ‖², so μ_ψ(E) = 0 implies μ(E)ψ = 0 and μ(Eᶜ)ψ = ψ.
- lmm:spectral-eigenvector-bounded-fc: about 8. OK.
- lmm:modular-operator-fixes-omega: about 8-10. OK.
- lmm:modular-unitary-group-fixes-omega: about 5. OK.
- lmm:modular-conjugation-commutes-unitary-group: about 3. OK.
- lmm:modular-sqrt-on-algebra: about 5. OK.
- lmm:takesaki-functions-bounded: about 10 (measurability plus two-case bound). OK.
- **lmm:takesaki-functions-identities: about 40+, too big.** Four claims, each a three-way case split
  with cpow algebra (`cpow_add` needs λ ≠ 0 side goals). Split into four lemmas:
  - (i) `takesaki_u_v_cutoff`, used by lmm:takesaki-approximants-strip;
  - (ii) `takesaki_lower_sum`, used by the lower boundary;
  - (iii) `takesaki_upper_identities`, used by the upper boundary;
  - (iv) `takesaki_aux_bounds`, the bounds and measurability of g_t and s^k v_t, s^k g_t.

  A shared helper "for λ > 0, s(λ)² = λ and λ·λ^w = λ^{w+1}" removes repetition. Each user then
  `\uses` only the part it needs.
- lmm:modular-sqrt-transfer: about 12-15, including the W-membership side goals. Borderline. Using
  lmm:fc-bounded-left-composition for the first step (f bounded: f(Δ)s(Δ)η = (fs)(Δ)η) shortens it.
  Recommended, not blocking.
- lmm:takesaki-approximants-entire: about 6. OK.
- lmm:takesaki-approximants-strip: about 10. OK.
- lmm:takesaki-approximants-uniform: about 10. OK.
- lmm:takesaki-function-analytic: about 10-12, three independent claims. Acceptable. Splitting off the
  bound is optional.
- lmm:takesaki-function-lower-boundary: about 8. lmm:takesaki-function-upper-boundary: about 8. OK.
- lmm:takesaki-lower-boundary-state: about 4. lmm:takesaki-upper-boundary-state: about 10. OK.
- thrm:takesaki-kms: about 10. OK.

## Structure and non-blocking points

- The order is good: packaging, then invariance of Ω, then the analytic continuation, then assembly.
  The split of the two boundary computations into a spectral part and an algebraic part is clean.
- G_{ξ,η} is defined only for z ∈ 𝒯, but the Lean F is total `ℂ → ℂ`. u_z(Δ) as a bounded
  integral needs a boundedness witness, which fails off 𝒯. Say how G is extended off 𝒯 (for example
  `if z ∈ kmsStrip 1 then … else 0`, harmless because every claim is `…On 𝒯`), so the formalizer does
  not have to invent it.
- The proof of lmm:takesaki-functions-identities cites lmm:log-power-on-interval; it is needed only
  for part (i) (K_n ⊂ (0,∞)). Keep it on that part after the split.
- The closing paragraph after thrm:takesaki-kms repeats the B-R remark of the subsection
  introduction (line 3921). Keep one of them.
- tomita-takesaki.tex is about 4200 lines. That is the existing chapter's layout and not something
  this change introduced, but this subsection is self-contained and could live in its own
  `sec10/takesaki-kms.tex` included after the chapter.
- Present tense: no violations found.

## VERDICT: REVISE

Required fixes:
1. Split lmm:takesaki-functions-identities into four lemmas, parts (i)-(iv), optionally with a
   shared "λ > 0" helper, and point each user's `\uses` at the part it needs.
2. Split lmm:spectral-eigenvector-variance into a moments/integrability lemma and the variance
   identity.
3. Split lmm:spectral-eigenvector-projection: extract the general PVM fact
   μ_ψ(E) = 0 ⇒ μ(E)ψ = 0, μ(Eᶜ)ψ = ψ.
4. Split lmm:vector-functional-state into (a) a bounded positive linear functional with ‖ω‖ ≤ 1 and
   (b) ‖ω‖ = 1.
5. Add lmm:takesaki-functions-bounded to the proof `\uses` of lmm:takesaki-function-upper-boundary.
6. def:modular-automorphism: add `\uses{thrm:tomita}` or drop the sentence citing it.

Non-blocking:
- State how G_{ξ,η} is extended off the strip.
- Shorten lmm:modular-sqrt-transfer via lmm:fc-bounded-left-composition.
- Remove the duplicated B-R remark.
- Consider moving the subsection to its own file.

---

# Re-review after revision (33 nodes), 2026-11-15

All six required fixes are in place. The non-blocking points are applied, except moving the
subsection to its own file, which the user declined. `blueprint_validate` reports no issue in the
subsection; the 14 errors it lists are older ones in other chapters.

## Required fixes: status

1. **lmm:takesaki-functions-identities.** Now split into five lemmas:
   - lmm:takesaki-positive-scalar-identities, the shared λ > 0 helper:
     s² = λ, λ·λ^w = λ^{w+1}, |λ^w| = λ^{Re w}, e_{-t}(λ) = λ^{-it};
   - lmm:takesaki-functions-identities, narrowed to the K_n cut-off, which is a pure indicator
     rearrangement;
   - lmm:takesaki-functions-lower-sum;
   - lmm:takesaki-functions-upper-identities;
   - lmm:takesaki-functions-aux-bounds.

   I re-checked each one case by case on λ ≤ 0, 0 < λ < 1 and λ ≥ 1:
   - lower sum: λ·λ^{-it-1} = λ^{-it};
   - upper: -i(t+i) = 1 - it, s²g_t = 1_{(0,1)}λ^{1-it} = u_{t+i}, g_t + v_{t+i} = 1_{(0,∞)}e_{-t};
   - bounds: |sv_t| = λ^{-1/2}, |s²v_t| = 1, |sg_t| = λ^{1/2}, |s²g_t| = λ.

   All correct. Each user now `\uses` only the part it needs.
2. **lmm:spectral-eigenvector-variance.** Split into lmm:spectral-moments and an algebra-only variance
   identity. In spectral-moments, ∫λ dμ_ψ = Re<ψ,Aψ> follows from `integral_ofReal`, and integrability
   of 1 and λ follows from |λ| ≤ 1 + λ² and finite mass. Correct.
3. **lmm:pvm-null-set-vector.** Extracted. The steps are μ_ψ(E) = <ψ, μ(E)ψ> = ‖μ(E)ψ‖², then
   μ(E) + μ(X∖E) = 1. Correct. lmm:spectral-eigenvector-projection applies it with E = ℝ∖{c}
   (`compl_compl`).
4. **lmm:vector-functional-state.** Narrowed to "positive, continuous, ‖ω‖ ≤ 1". The new
   lmm:vector-functional-norm-one gives ‖ω‖ = 1 via ω(1) = 1 and ‖1‖ = 1 (H ≠ 0). def:vector-state
   uses both.
5. **lmm:takesaki-function-upper-boundary.** Now `\uses` lmm:takesaki-functions-bounded, and the text
   says why it is needed (v_{t+i} bounded and measurable).
6. **def:modular-automorphism.** The thrm:tomita sentence is gone.

Non-blocking points, all resolved:
- G_{ξ,η} is set to 0 off 𝒯, with a note that the choice is immaterial.
- lmm:modular-sqrt-transfer now uses lmm:fc-bounded-left-composition for its first step, with u = f
  and h = s at η ∈ W_s.
- The duplicated Bratteli–Robinson remark is gone.

## Soundness

No changes to the statements of the theorem or of the analytic and boundary lemmas, so the soundness
pass of the first review stands. All new statements are true as stated. The Mathlib names cited for
the first time exist: `integral_ofReal` and `Real.sqrt_le_one`.

## Granularity (estimated Lean lines, new or changed proofs)

| Proof | Lines | Verdict |
|---|---|---|
| lmm:vector-functional-state | about 10 | OK |
| lmm:vector-functional-norm-one | about 6 | OK |
| lmm:spectral-moments | about 12-15 | borderline; acceptable as a list of independent two-line facts |
| lmm:spectral-eigenvector-variance | about 8 | OK |
| lmm:pvm-null-set-vector | about 8 | OK |
| lmm:spectral-eigenvector-projection | about 6 | OK |
| lmm:takesaki-positive-scalar-identities | about 6 | OK |
| lmm:takesaki-functions-identities | about 3 | OK |
| lmm:takesaki-functions-lower-sum | about 8 | OK |
| lmm:takesaki-functions-upper-identities | about 8 | OK |
| lmm:takesaki-functions-aux-bounds | about 10-12 | OK, five bounds with one shared case split |
| lmm:modular-sqrt-transfer | about 10 | OK |

The unchanged proofs are as estimated in the first review.

## Remaining non-blocking point

- The label lmm:vector-functional-state no longer asserts a state (its title is "Vector Functionals
  are Positive and Bounded"). Renaming it, for example to lmm:vector-functional-positive-bounded,
  would match its content. That is a rename, so it is left to the user; it is not required.

## VERDICT: PASS
