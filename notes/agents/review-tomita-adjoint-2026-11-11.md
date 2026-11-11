# Review: `sbsctn:tomita-adjoint` (stage 3b, S* = closure of F0)

Scope: the 34 nodes of `\subsection{The Adjoint of the Tomita Operator}` in
`blueprint/src/sections/sec10/tomita-takesaki.tex` (lines 1600-1990). Earlier labels were checked only
for existence and meaning. `blueprint_validate` reports no issues inside this subsection; its 14
unknown-label errors (`conv:*`) are in the spectral-theorem chapters.

## Overall

The mathematics is correct throughout, and the bounded-approximant route is sound and fits the
existing machinery well. I checked every inner-product manipulation using the convention that the
inner product is conjugate-linear in the first slot. The Option-K formulation `(S')^*C` matches
`def:tomita-operator` (S = C S'), `def:modular-operator` (Delta = (S')^*S') and
`def:modular-conjugation` (J = CV). Three things need revising before formalization: one hidden
construction step (the unitary conjugation lemma), and two oversized proofs. The rest are small fixes.

## Blocking

1. **`lmm:unitary-conjugate-functional-calculus`: hidden step, and an operator Lean does not define.**
   The project defines only `antiunitaryConj` (Polar.lean:1317). There is no conjugation of an
   operator by a unitary. The proof also silently uses
   `W2 (W1 A W1^{-1}) W2^{-1} = (W2 W1) A (W2 W1)^{-1}`, including domains, and the same identity for
   f(A). This is an associativity-of-conjugation lemma that the blueprint never states. The only use
   of this lemma is `lmm:commuting-unitary-bounded-function`, where U A U^{-1} = A. Fix: drop the
   general U A U^{-1} and restate in terms of `antiunitaryConj`:
   - new `lmm:commuting-unitary-double-conjugate`: if the unitary U commutes with an operator A (in
     the sense of the subsection's definition), then `antiunitaryConj (UC) (antiunitaryConj C A) = A`.
     Prove it by graph extensionality, using C(Cφ) = φ and the commutation for U and U^{-1}. This is
     about 6 lines.
   - restate this label as: U unitary and A self-adjoint with U commuting with A imply
     `antiunitaryConj (UC) (antiunitaryConj C f(A)) = f(A)` for real measurable f. The proof applies
     `crllr:antiunitary-conjugate-functional-calculus` twice and rewrites with the new lemma.
   - in `lmm:commuting-unitary-bounded-function`, read off U f(D) ψ = f(D) U ψ from that equality,
     evaluated at Uψ.
   Also: `lmm:commuting-unitary-adjoint-product` then only needs "U commutes with c^*c". Drop its
   clause "U(c^*c)U^{-1} = c^*c".

2. **`lmm:inverse-square-root-product`: oversized, about 15 Lean lines and three moves.** The moves are
   the composition-law domain, the integrability inclusion W_{r^2} ⊂ W_r, and the null-set swap to
   ι^-. Split as follows:
   - new `lmm:fc-domain-square`: for measurable f, W_{f^2} ⊂ W_f, because |f|^2 ≤ 1 + |f|^4 and
     μ_ψ is finite. Then f(A)f(A) = (f^2)(A) including domains, by `thrm:fc-composition`.
   - the remaining step (r^2)(A) = A^{-1} is exactly the computation already proved in
     `lmm:square-of-inverse-square-root`. Either cite that lemma (via `crllr:fc-of-fc`,
     q(r(A)) = (q∘r)(A) = (r^2)(A)), or keep the null-set argument as its own 3-line step. Do not
     redo it inline.

3. **`lmm:von-neumann-span-unitaries`: oversized, about 15 lines.** It handles the x = 0 case, unfolds
   the `let`s of `CStarAlgebra.norm_smul_two_inv_smul_add_four_unitary`, shows that ℜ and ℑ of x/‖x‖
   lie in M, and shows that u_i and u_i^* lie in M. Split off
   `lmm:von-neumann-real-imaginary-part`: for y ∈ M, ℜ y = (1/2)(y + y^*) ∈ M and
   ℑ y = (-i/2)(y - y^*) ∈ M (Mathlib `realPart_apply_coe`, `imaginaryPart_apply_coe`;
   `lmm:commutant-von-neumann-algebra`). Then `lmm:commutant-of-unitaries` can work directly from the
   explicit formula; the `Fin 4` sum is not needed. I confirmed the cited Mathlib statements in
   `Mathlib/Analysis/CStarAlgebra/Unitary/Span.lean` (`self_add_I_smul_cfcSqrt_sub_sq_mem_unitary`,
   `selfAdjoint.unitarySelfAddISMul`, `norm_smul_two_inv_smul_add_four_unitary`, which requires
   `[PartialOrder A] [StarOrderedRing A]`), `ContinuousLinearMap.instStarOrderedRing`
   (InnerProductSpace/StarOrder.lean) and `CFC.sqrt_eq_real_sqrt`.

## Non-blocking (fix in the same pass)

- `lmm:commuting-unitary-adjoint`: about 12 lines, because "the same computation with U and U^{-1}
  exchanged" doubles the proof. State a one-sided helper: if U^{-1} maps Dom c into Dom c with
  c U^{-1} = U^{-1} c, then U maps Dom c^* into Dom c^* with c^* U = U c^*. Apply it to U and to
  U^{-1}.
- `lmm:tomita-adjoint-closure-props`: three moves (closability, extension, c^*Ω = η by a limit). The
  repository has an adjoint-of-closure lemma (`adjoint_closure_eq_adjoint` in
  `Physicslib4/Spectral/Unbounded/Basic.lean`). With it, c^* = a_0^*, so c^*Ω = a_0^*Ω = η in one
  line. Cite it instead of the sequence argument.
- `lmm:tomita-adjoint-sqrt-conjugation`: about 12 lines, borderline. It is acceptable as is.
  Optionally split off the inner-product identity <ξ, J v> = conj<Jξ, v>.
- `lmm:tomita-adjoint-closure-commutes`: the name x_n clashes with the approximants x_n. Rename it to
  y_n.
- `lmm:sqrt-of-inverse`: (√λ)^{-1} = λ^{-1/2} also needs `Real.rpow_neg`. Note that ι^- is Lean's
  `Inv.inv` on ℝ (0^{-1} = 0), which is what makes `measurable_inv` applicable.
- `\uses` gaps:
  - `lmm:tomita-adjoint-intrinsic` needs Dom(S') dense to use the "φ = A^*ψ" uniqueness of
    `lmm:characterizing-adjoint-domain-membership`. Add `crllr:linearized-tomita-properties`.
  - `lmm:approximant-range` uses that D is self-adjoint. Add `thrm:von-neumann-adjoint-product`.
- Intro prose: "replaces the polar decomposition, which for this c need not be injective" is
  confusing. Say instead that the partial isometry of the polar decomposition need not be unitary,
  or drop the remark.
- `lmm:approximant-functions`: `continuous_max` is unnecessary, because `Real.sqrt` already clamps.
  This is harmless.

## Soundness pass (per declaration)

- intrinsic / intrinsic-core / graph-closed / extends-closure: the condition says
  conj<ξ,Sζ> = <η,ζ>, which is equivalent to <ξ,Sζ> = <ζ,η>. This is the correct antilinear adjoint,
  and S^* = (CS')^* = (S')^*C. The core direction uses `lmm:tomita-core`. The relation
  <b'Ω, x^*Ω> = <xΩ, b'^*Ω> holds. True.
- commuting-unitary-*: the four-step inner-product chain is correct. True, given c densely defined
  and closed where the functional calculus is used.
- h_n, k_n: k_n = ns/(n+s), so 0 ≤ k_n ≤ min(n, s), k_n → s and h_n → 1. K_n = s(D)h_n(D) = |c|R_n:
  `thrm:fc-composition` gives a domain of W_{h_n} ∩ W_{k_n} = H. So k_n is the right function.
  ‖cR_nψ‖ = ‖K_nψ‖ ≤ n‖ψ‖ (`thrm:absolute-value-domain`). Dominated convergence applies because
  |k_n| ≤ |s| and ψ ∈ W_s = Dom c. ‖x_nΩ − ξ‖ = ‖K_nΩ − |c|Ω‖ → 0. True.
- x_n^* ⊇ R_n c^*: <φ, cR_nψ> = <c^*φ, R_nψ> = <R_n c^*φ, ψ>. True.
- left-map / adjoint / closure: a_0 is well defined because Ω is separating. The computation
  <xξ, yΩ> = <ξ, x^*yΩ> = <y^*xΩ, η> = <xΩ, yη> is correct. c^*Ω = η is correct (take y = 1).
  True.
- closure-commutes / approximants-commutant / converge / `thrm:tomita-adjoint-eq-closure`: correct.
  This is van Daele's argument as Jones presents it.
- S^* = Δ^{1/2}J and S^* = JΔ^{-1/2}: <ξ, JΔ^{1/2}ζ> = conj<Jξ, Δ^{1/2}ζ>. The second form follows
  from `thrm:modular-conjugation-involution`. True.
- commutant-cyclic-separating: holds by M'' = M. True.
- commutant-tomita: S_0 of M' has graph Γ(F_0), and `lmm:tomita-operator-independent-of-c` applies.
  True.
- commutant-modular-operator-intrinsic: <JPφ, JPψ> = <Pψ, Pφ>, which matches the form of
  `lmm:modular-operator-intrinsic`. True.
- inverse-square-root-product, commutant-modular-operator, sqrt-of-inverse: s∘ι^- = r at λ > 0,
  λ < 0 and λ = 0. True.
- commutant-modular-conjugation and the main theorem: J is unique by
  `lmm:modular-conjugation-intrinsic`. True.

## Granularity pass

5-10 lines, fine: tomita-adjoint-intrinsic, intrinsic-core (about 10), graph-closed,
extends-closure, commuting-unitary-adjoint-product, commuting-unitary-bounded-function,
approximant-functions (about 10), approximant-bounded, approximant-range, approximant-convergence,
approximant-operator, approximant-operator-commutes, unitary-of-contraction, commutant-of-unitaries,
left-map, left-map-adjoint, closure-commutes (about 10), approximants-commutant,
approximants-converge, eq-closure, tomita-adjoint-polar, commutant-cyclic-separating,
commutant-tomita-operator, commutant-modular-operator-intrinsic, commutant-modular-operator,
sqrt-of-inverse, commutant-modular-conjugation, commutant-modular-objects.

Split (see above): unitary-conjugate-functional-calculus, inverse-square-root-product,
von-neumann-span-unitaries (blocking); commuting-unitary-adjoint, tomita-adjoint-closure-props
(advisory); tomita-adjoint-sqrt-conjugation (optional).

## Pass 2 (2026-11-11)

VERDICT: PASS. B1–B3 and all non-blocking items are resolved. The double-conjugate form was checked against `antiunitaryConj` (Polar.lean): its domain is {φ | U⁻¹φ ∈ Dom A} and its value is UAU⁻¹φ. `prpstn:hall-9.10` is `adjoint_closure_eq_adjoint`. All 38 statements are true; every new or changed proof is about 10 Lean lines or fewer. Advisory: "U commutes with A" is used by six nodes but defined only in prose. A labelled `def:` node would give the formalizer one predicate; this is a design decision for the user.
