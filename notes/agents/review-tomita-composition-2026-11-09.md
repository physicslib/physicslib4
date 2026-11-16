# Review: Physicslib4/Spectral/Unbounded/Composition.lean (2026-11-09)

Scope: lmm:fc-difference-to-truncation, lmm:fc-dominated-convergence, lmm:fc-bounded-left-composition,
lmm:fc-associated-measure, lmm:fc-composition-domain, thrm:fc-composition,
lmm:fc-commutes-with-projections, lmm:fc-real-closed, lmm:fc-core.

VERDICT: PASS (no blocking findings).

Diagnostics: only the 9 `declaration uses sorry` warnings.

## Checks

- All 9 labels recorded (`\lean{}` present, Lean names match).
- Signatures match the verified Trial 2 spike (`fc_tendsto_bdd`, `fc_integral_pmapIntegral`,
  `fc_assoc_pmapIntegral_eq`, `fc_mem_comp_iff`, `fc_comp`, `fc_commute_proj`, `fc_core`), so the
  spike proofs transfer almost verbatim.
- Junk values: every `μ.integral u` has `u ∈ BddMeasurable X` (hypothesis, or the truncation
  `{|h|<n}.indicator h`, bounded via `hh` and `indicator_lt_mem_bddMeasurable`). Every
  `pmapIntegral μ h` is evaluated on a subtype of `integralDomain μ h`, so W_h membership is
  enforced by the types (this includes `assoc_pmapIntegral`, where ψ ∈ W_h is needed and present).
- Measurability: `hh`/`hf`/`hg` present wherever needed (W_h is `MemLp h 2`, which carries no
  measurability in this Mathlib).
- `pmapIntegral_comp` domain identity {ψ ∈ W_g | g(μ)ψ ∈ W_f} = W_g ∩ W_{fg} is true (from
  lmm:fc-composition-domain); the extension conjunct is the spike's `fc_comp`. No Lean product
  operator exists in the project, so the unbundled form is appropriate.
- `hasCore_functionalCalculus`: Mathlib `LinearPMap.HasCore f S` = `S ≤ f.domain` ∧
  `(f.domRestrict S).closure = f`. For closed f(A) this is equivalent to def:core. Correct use.
- `isSelfAdjoint_functionalCalculus_of_real`: true (prpstn:hall-10.3 via
  `isSelfAdjoint_pmapIntegral_of_real`).

## Optional findings

1. lmm:fc-real-closed: the `.IsClosed` conjunct is redundant; Mathlib's `IsSelfAdjoint.isClosed`
   (Analysis/InnerProductSpace/LinearPMap.lean:340) derives it. State only `IsSelfAdjoint (...)`;
   the proof is `isSelfAdjoint_pmapIntegral_of_real _ (Complex.measurable_ofReal.comp hf) (fun _ => Complex.ofReal_im _)`.
2. thrm:fc-composition: the first conjunct restates lmm:fc-composition-domain in set form. Fine as
   the blueprint states both; for downstream use consider exposing the second conjunct as its own
   lemma (the spike's `fc_comp` shape) so callers need not write `.2`.
3. Downstream fit (stage 2): the composition lemmas are on `pmapIntegral μ`, while stage 2
   (inverses via 1/λ, |T| = √(T*T)) works with `functionalCalculus hA`. Defeq by `rfl`, but the
   subtype-rewrite friction noted in the trial (`erw`, `fc_pmap_congr_pt`) will recur; consider
   `functionalCalculus_comp` / `mem_domain_functionalCalculus_comp_iff` wrappers as in the trial's
   "Recommended statement shapes", plus the congruence lemmas `pmapIntegral_congr(_pt)`.
4. lmm:fc-bounded-left-composition: the `∃ hψ` hides the W_h ⊆ W_{uh} fact; a separate
   `mem_integralDomain_mul_of_bddMeasurable` (spike `fc_mem_mul_bdd`) would be reused by
   fc-associated-measure and fc-commutes-with-projections.
