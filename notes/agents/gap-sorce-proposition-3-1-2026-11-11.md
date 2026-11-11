# Gap in Sorce's §3: the sigmoid is not entire (2026-11-11)

Found while preparing stage 3b (the scalar replacement for Sorce's Lemma 2.8). Source read:
arXiv:2309.16762v3 (23 Oct 2024, the version with Prop. 3.12). The companion paper
arXiv:2309.16766 (Thm 4.4, eqs. 4.49–4.53) uses the same argument.

## The claim

Sorce, §3: "Since f_k(z) is analytic in the complex plane, the operator f_k(∆) ... can be studied
using a contour integral", with f_k(z) = 1/(1 + e^{k(z−λ)}). Prop. 3.1 then states, for the contour γ
(half-lines t ± 2πi, t ≥ 0, joined by the half-circle of radius 2π through the left half-plane):

  ∆^n f_k(∆)ψ = (1/2πi) ∫_γ z^n f_k(z) (z − ∆)^{-1} ψ dz.

## Why it fails

f_k is meromorphic, not entire: 1 + e^{k(z−λ)} = 0 at z_m = λ + iπ(2m+1)/k, m ∈ ℤ. For k ≥ 1 the
poles with |π(2m+1)/k| < 2π, about 2k of them, lie inside γ. Each has residue −1/k, so the contour
integral equals ∆^n f_k(∆)ψ plus −(1/k) Σ_m z_m^n (z_m − ∆)^{-1}ψ.

Numerical check, scalar case (∆ = t = 0.5, λ = 1, k = 1, n = 0, contour truncated at Re z = 60):
- the contour integral is 0.523641;
- f_k(t) is 0.622459;
- f_k(t) plus the two residue terms is 0.523641.

So Prop. 3.1 is false for k ≥ 1/2, and Theorem 3.3's proof, eqs. (26)–(38), rests on it.

## Why a local repair of the norm bound is unlikely

The proof bounds ‖a_{λ,n}‖ by limsup_k ∫_γ |z|^n |h_k(z)| ‖a_z‖ ds, with ‖a_z‖ from Takesaki's lemma.
This needs h_k holomorphic inside γ with ∫_γ |h_k| w ds bounded uniformly in k, where w > 0 is
bounded below on γ. By Cauchy's formula, h_k is then locally uniformly bounded inside γ. Montel
gives a subsequence converging to a holomorphic function, which would equal the step Θ(λ − t) on
(0, ∞), and that is impossible. So no family of mollifiers approximating the sharp cut-off Θ can
satisfy the needed bound on a fixed contour. Including the residues does not help: the residue
sum is bounded by about (1/π) Σ_{m<k} 1/(2m+1) ~ log k / (2π), which diverges.

## Is Theorem 3.3 itself true?

Unclear. A heuristic suggests it can fail. In M = B(K) ⊗ 1 with Ω = Σ √p_i e_i ⊗ e_i, the statement
"there is a bounded a ∈ M with aΩ = Θ(λ − ∆)a′Ω" becomes the boundedness of the Schur multiplier
Θ(λ − p_i/p_j)(p_i/p_j)^{1/2}. If the ratios p_i/p_j are dense (e.g. p ∝ e^{−i−√2j}), this is a
sharp cut-off on log-ratios. Such cut-offs behave like triangular truncation, which is unbounded.
This is not proved here. Smooth cut-offs, whose log-scale Fourier transform is integrable, give
bounded multipliers.

## Consequences

- **Stage 3a** (commutant extension lemma, Takesaki's lemma) is unaffected. These are standard,
  true results, and the blueprint proof does not use Prop. 3.1.
- **Stage 3b as planned** (a scalar replacement for L2.8, serving Prop. 3.1) is not worth drafting
  until the route for stage 5 is settled.
- **L2.4** (strip analyticity) is correct but its shape depends on the route.

## Options

- **A. Repair Sorce.** Replace Θ by smooth cut-offs analytic inside γ, define tidy operators by
  aΩ = g(∆)bΩ with g smooth, and redo Thm 3.3, Remark 3.4, Prop. 3.9 and Prop. 3.10.
  Research-level, unrefereed, risky.
- **B. Switch stage 5 to van Daele's proof** as presented in Bratteli–Robinson vol. 1, §2.5.2
  (the source already chosen for JMJ = M′, D5). It uses Takesaki's lemma for z = −λ, λ > 0, and a
  resolvent integral formula for ∆^{it}. Batch 3a is reused as is, and one source then covers both
  halves of Tomita's theorem. Recommended, after confirming the exact statements in BR.
- **C. Rieffel–van Daele** (Pacific J. Math. 69, 1977): a complete bounded-operator route. It
  overlaps less with stages 1–2.
