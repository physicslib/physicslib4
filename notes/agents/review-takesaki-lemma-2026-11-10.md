# Review: Takesaki's Lemma subsection (`sbsctn:takesaki-lemma`), 2026-11-10

Scope: the 21 nodes from `lmm:commutant-extension-well-defined` to `thrm:takesaki-lemma` in
`blueprint/src/sections/sec10/tomita-takesaki.tex` (lines 1238-1498).

## Overall

The mathematics is correct. I checked the argument line by line and found no false statement, sign
error, conjugation error or broken limit. The constant is right and sharp: for M = C on C, Ω = 1,
Δ = 1, z = -1, the bound ‖a'‖/2 is attained. The contradiction closes, and `lmm:tomita-core`
follows correctly from `lmm:tomita-operator-independent-of-c` and `lmm:tomita-pre-operators-apply`.
None of the `blueprint_validate` errors are in this subsection. Every referenced earlier label exists
and means what the new nodes assume.

The subsection still needs revising. Five proofs are too large or carry a small hidden step, and two
resolvent proofs credit a step to the wrong lemma.

## Line-by-line mathematics (soundness)

- **commutant-extension-well-defined / -bounded / -in-algebra / commutant-extension.** These are
  correct. If b'Ω = d'Ω, the hypothesis applied to b' - d' gives b'ψ = d'ψ. `ContinuousLinearMap.extend`
  and `opNorm_extend_le (h_dense) (h_e : ∀ x, ‖x‖ ≤ N * ‖e x‖)` exist and fit (e is the subtype
  inclusion of M'Ω, N = 1). Td' and d'T agree on the dense set M'Ω. Uniqueness uses that Ω is
  separating for M (`lmm:cyclic-commutant-separating`). The hypotheses are satisfiable (ψ = aΩ,
  c = ‖a‖).
- **modular-resolvent-bounded.** This is correct. `IsClosed.notMem_iff_infDist_pos` exists (it needs
  the set nonempty, and [0,∞) is). The conjugate of r_z is r_{z̄}, which gives the adjoint.
- **modular-resolvent-right/left-inverse, crllr:modular-resolvent.** The mathematics is correct:
  g·r_z = 1_{[0,∞)}, and μ^Δ((-∞,0)) = 0. The sign convention also checks out: (Δ - z)(-r_z ξ) =
  z r_z ξ - Δ r_z ξ = ξ. However, the facts W_ι = Dom(Δ) and ι(Δ) = Δ come from the spectral theorem
  (`thrm:hall-10.4`, see the remark in `def:hall-10.5`), not from `lmm:functional-calculus-sub-bounded`.
  The step (const z)(Δ) = z·1 is also used without citation. **Gap in `\uses`, blocking (B2).**
- **takesaki-elementary-inequality.** This is correct. `Complex.re_le_norm` exists, and
  `Complex.re_eq_norm : z.re = ‖z‖ ↔ 0 ≤ z` (in `Analysis/Complex/Order`) is the right form. For real
  p, q: |zp - q|² = |z|²p² - 2Re z·pq + q² ≥ 2(|z| - Re z)pq.
- **takesaki-ball-closure-bound.** This is correct (‖b'aΩ‖ = ‖ab'Ω‖ ≤ c‖b'Ω‖, then pass to limits).
  `Convex.closure` exists.
- **takesaki-separation.** This is correct. Re⟨ξ - v, k - v⟩ ≤ 0 gives Re⟨φ,k⟩ ≤ Re⟨φ,ξ⟩ - ‖φ‖².
  `InnerProductSpace.rclikeToReal` (an abbrev, to be used with `letI`), `real_inner_eq_re_inner`,
  `exists_norm_eq_iInf_of_complete_convex` and `norm_eq_iInf_iff_real_inner_le_zero` all exist.
  Completeness comes from `IsClosed.isComplete`.
- **takesaki-transfer.** This is correct, including the conjugations. From φ = z̄χ - Δχ we get
  ⟨φ, aΩ⟩ = z⟨χ,aΩ⟩ - ⟨Δχ,aΩ⟩, because the inner product is conjugate-linear in the first slot.
  `lmm:modular-operator-intrinsic` (with ψ := χ, its χ := Δχ, φ := aΩ) gives
  ⟨S aΩ, Sχ⟩ = ⟨Δχ, aΩ⟩, that is ⟨a*Ω, Sχ⟩ = ⟨Δχ, aΩ⟩. Also
  ⟨φ, r_z a'Ω⟩ = ⟨r_{z̄}φ, a'Ω⟩. In the proof the bound name φ clashes with the lemma's φ; rename it
  (O7).
- **tomita-core.** This is correct.
- **takesaki-uniform-approximation.** The Lipschitz bound is correct:
  ΔG = Re⟨u-u₁,a'Ω⟩ - Re(z⟨u-u₁,aΩ⟩) + Re⟨a*Ω, v-v₁⟩. It is uniform in a ∈ B_c because
  ‖a*‖ = ‖a‖ ≤ c.
- **cfc-mem-von-neumann.** This is correct for every f : ℝ → ℝ: a non-continuous f gives the junk value
  0 ∈ M. `Commute.cfc_real` exists.
- **takesaki-approximate-polar.** The identities are correct on σ(P) ⊂ [0, ‖h‖²]. The bounds
  ‖u‖² = ‖(t/(ε+t))(P)‖ ≤ 1 and ‖x‖² = ‖x x*‖ = ‖(t/√(ε+t))(P)‖ ≤ √‖P‖ = ‖h‖ hold, and so does
  ε‖P_ε^{-1/2}‖ ≤ √ε. Two steps are used but not stated:
  1. ‖P_ε^{1/4}Ω‖² = ⟨Ω, P_ε^{1/2}Ω⟩ needs f_{1/4}² = f_{1/2}, which is not in the listed identities.
  2. `lmm:takesaki-numerator-bound` needs P_ε^{1/4} self-adjoint, and that is not in the statement.

  `norm_cfc_le` and `CStarRing.norm_star_mul_self` exist. **Blocking (B1).**
- **takesaki-numerator-bound.** This is correct:
  ⟨hΩ,a'Ω⟩ = ⟨Ω, P_ε^{1/4}x a'Ω⟩ = ⟨P_ε^{1/4}Ω, a'xΩ⟩, and √(p² + √ε‖Ω‖²) ≤ p + ε^{1/4}‖Ω‖.
- **takesaki-test-element.** This is correct, with a = s u_ε:
  - ⟨hΩ, aΩ⟩ = s⟨Ω, h*u Ω⟩ = s p², and ⟨(su)*Ω, h*Ω⟩ = s⟨Ω, u h*Ω⟩ = s q² (conjugate-linear slot).
  - Re(s w) = c|w| when s = c w̄/|w|.
  - The elementary inequality, applied with (p², q²), gives c|w| ≥ ‖a'‖ p q.
- **takesaki-key-estimate.** This is correct: G ≤ ε^{1/4}‖a'‖‖h‖^{1/2}‖Ω‖². ε is chosen before a,
  so the dependence of a on ε is harmless.
- **takesaki-resolvent-in-ball-closure.** This is correct. K_c ∋ 0 (c ≥ 0). Separation gives
  G(χ,Sχ;a) ≥ γ on B_c, and the approximation gives G(hΩ,h*Ω;a) > γ/2 on B_c. This contradicts the
  key estimate at δ = γ/2.
- **thrm:takesaki-lemma.** This is correct. The degenerate case a' = 0 (c = 0, a = 0) is fine.

## Granularity

| Label | Estimate | Verdict |
|---|---|---|
| commutant-extension-well-defined | 10-12 (quotient-style construction on M'Ω) | borderline, OK |
| commutant-extension-bounded | 5 | OK |
| commutant-extension-in-algebra | 8 | OK |
| commutant-extension | 6 | OK |
| modular-resolvent-bounded | about 15 (5 claims) | **split (B4)** |
| modular-resolvent-right-inverse | about 15 | **split (B2)** |
| modular-resolvent-left-inverse | about 8 once the shared lemmas exist | OK after B2 |
| crllr:modular-resolvent | 6 | OK |
| takesaki-elementary-inequality | 8 (nlinarith plus sqrt) | OK |
| takesaki-ball-closure-bound | about 12 (convexity, then closure limit) | optional split (O1) |
| takesaki-separation | 8-10 | OK |
| takesaki-transfer | about 12 (three claims) | borderline (O2) |
| tomita-core | 5 | OK |
| takesaki-uniform-approximation | about 18 | **split (B3)** |
| cfc-mem-von-neumann | 4 | OK |
| takesaki-approximate-polar | 40+ (eight conclusions) | **split (B1)** |
| takesaki-numerator-bound | 8-10 | OK |
| takesaki-test-element | about 15 | **split (B5)** |
| takesaki-key-estimate | 8 | OK |
| takesaki-resolvent-in-ball-closure | 10 | OK |
| thrm:takesaki-lemma | 5 | OK |

## Blocking findings

**B1. `lmm:takesaki-approximate-polar` is oversized and has unstated steps.** Split it as follows,
and simplify p_ε at the same time.

- (a) `lmm:takesaki-shifted-powers`: P_ε^s ∈ M, P_ε^s is self-adjoint, P_ε^s P_ε^t = P_ε^{s+t},
  P_ε^0 = 1, ‖P_ε^s‖ ≤ ε^s for s ≤ 0, and P_ε^s commutes with P. The tools are `cfc_mul`,
  `Real.rpow_add` (the base ε + max(t,0) is positive) and `norm_cfc_le`. This single power rule
  covers 1/4·(-1/4), 1/4·1/4 and (-1/4)·(-1/4).
- (b) `lmm:takesaki-approx-polar-factorizations`: h* = P_ε^{1/4}x_ε, h*u_ε = x_ε x_ε*, and
  u_ε h* = x_ε* x_ε. Both products follow from P_ε^{-1/2} = P_ε^{-1/4}P_ε^{-1/4} and from P commuting
  with P_ε^{-1/4}.
- (c) `lmm:takesaki-approx-polar-norms`: ‖u_ε‖ ≤ 1 and ‖x_ε‖² ≤ ‖h‖, by the C*-identity and
  `norm_cfc_le` on σ(P) ⊂ [0, ‖h‖²].
- (d) `lmm:takesaki-shifted-root-bound`: ‖P_ε^{1/4}Ω‖² ≤ p_ε² + √ε‖Ω‖². The proof uses
  P_ε^{1/2} = P P_ε^{-1/2} + εP_ε^{-1/2} together with f_{1/4}² = f_{1/2}.

Redefine p_ε := ‖x_ε*Ω‖, so that ⟨Ω, h*u_εΩ⟩ = p_ε² follows directly from (b). This removes P^{1/2},
f and the identity t·f_{-1/2} = t·f_{-1/4}² entirely, and makes p_ε and q_ε symmetric. Update
`lmm:takesaki-numerator-bound`, `lmm:takesaki-test-element` and `lmm:takesaki-key-estimate` to cite
the pieces they use. The numerator bound cites (a) for self-adjointness and (d).

**B2. The resolvent inverses credit the spectral theorem to the wrong lemma.** In
`lmm:modular-resolvent-right-inverse` and `-left-inverse`, the facts W_ι = Dom(Δ) and ι(Δ) = Δ come
from `thrm:hall-10.4`, not `lmm:functional-calculus-sub-bounded`. The step (const z)(Δ) = z·1 also
needs a citation (`prpstn:integral-of-indicator` plus linearity). Extract two lemmas shared by both
proofs:

- `lmm:modular-z-minus-fc`: W_{z-ι} = Dom(Δ) and (z-ι)(Δ)ψ = zψ - Δψ. It uses `thrm:hall-10.4`,
  `lmm:functional-calculus-sub-bounded` and the constant-function integral.
- `lmm:modular-indicator-nonneg-one`: 1_{[0,∞)}(Δ) = 1. It uses `lmm:positive-spectral-support`,
  `lmm:integral-ignores-null-sets` and `prpstn:integral-of-indicator`.

**B3. `lmm:takesaki-uniform-approximation` is oversized.** Split out
`lmm:takesaki-G-lipschitz`, which is the displayed inequality, for all u, v, u₁, v₁ and a ∈ B_c. The
remaining proof picks n from `lmm:tomita-core` using `Metric.tendsto_atTop`.

**B4. `lmm:modular-resolvent-bounded` is oversized (five claims).** Split out a scalar lemma
`lmm:resolvent-function-props`: d(z) > 0, r_z is measurable, |r_z| ≤ 1/d(z), and the conjugate of r_z
is r_{z̄}. The operator lemma is then about 5 lines.

**B5. `lmm:takesaki-test-element` is oversized.** Split out
`lmm:complex-rotation-choice`: for w ∈ ℂ and c ≥ 0 there is s with |s| ≤ c and Re(s w) = c|w|. Also
split out `lmm:takesaki-test-inner-products`: for s ∈ ℂ, ⟨hΩ, s u_εΩ⟩ = s p_ε² and
⟨(s u_ε)*Ω, h*Ω⟩ = s q_ε².

## Optional findings

- **O1.** In `lmm:takesaki-ball-closure-bound`, split "K_c is closed and convex" from the commutant
  bound. Add `def:von-neumann-algebra-commutant-convention` to the proof's `\uses`.
- **O2.** `lmm:takesaki-transfer` could split the resolvent part (χ ∈ Dom S and
  ⟨φ,ψ⟩ = ⟨χ,a'Ω⟩) from the identity in a.
- **O3.** Add `lmm:commutant-von-neumann-algebra` to the `\uses` of `lmm:takesaki-numerator-bound`
  (a' commutes with x_ε ∈ M) and of `lmm:takesaki-test-element` (s u_ε ∈ M).
- **O4.** Add `lmm:takesaki-ball-closure-bound` (the definition of K_c and the fact 0 ∈ K_c) to the
  statement-level `\uses` of `lmm:takesaki-resolvent-in-ball-closure`.
- **O5.** In the intro, "Lemma 2.6 of Sorce's paper" is ambiguous, because the next clause cites a
  different Sorce paper (JHEP 2023). Write "Lemma 2.6 of Sorce's proof of Tomita's theorem
  (J. Funct. Anal., 2024)". Also check the Rieffel–van Daele lemma number (4.3) against the PDF.
- **O6.** The prose is in the present tense throughout. No history narration was found.
- **O7.** In the proof of `lmm:takesaki-transfer`, rename the instantiated variable "with φ = aΩ" to
  avoid clashing with the lemma's φ.

## Pass 2 (2026-11-11)

VERDICT: PASS. All blocking findings B1–B5 and optional items O1–O7 are resolved; the new nodes were re-derived and are correct; granularity is acceptable (formalize `lmm:takesaki-shifted-powers` as one Lean lemma per conjunct). Non-blocking items N1–N3 (cite `Complex.conj_mul'`; add (z − λ)r_z(λ) = 1_{[0,∞)}(λ) to `lmm:resolvent-function-props`; cite `Real.rpow_one` and spectrum non-negativity in `lmm:takesaki-shifted-root-bound`) are applied by the orchestrator. N4 (extra convexity citations) is left for the formalizer.
