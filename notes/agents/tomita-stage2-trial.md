# Tomita stage 2 spike: von Neumann's theorem (T†T self-adjoint)

Date: 2026-11-08. Status: COMPLETE. Verdict: **FEASIBLE** (fully proved in the spike, 0 sorry).

## Existing API (findings)

- `Physicslib4/Spectral/Unbounded/Basic.lean`
  - `existsUnique_add_mem_orthogonal` (l.574): orthogonal decomposition for a closed
    `V : Submodule ℂ H` in any complete inner-product space. Works on
    `WithLp 2 (H × H)` (Mathlib's L² product); no H × H version in the project.
  - `orthogonal_range_eq_ker_adjoint`, `adjoint_subSmul`, `orthogonal_range_subSmul`
    (`(ran (S - λ))ᗮ = ker (S† - λ̄)`), `isSymmetric_iff_le_adjoint`, `mem_ker`, `mem_range`.
  - private `adjoint_eq_of_forall_inner_iff`, `forall_inner_iff_adjoint` (not usable outside).
- `Physicslib4/Spectral/Unbounded/Spectrum.lean`
  - **`adjoint_eq_of_range_eq_top`** (l.~323): `S ≤ S†`, `range (subSmul S μ) = ⊤`,
    `ker (subSmul S† μ) = ⊥` ⇒ `S† = S`. With μ = −1 this is the criterion
    "ran(1 + A) = H ⇒ self-adjoint" for symmetric densely-defined A. No bounded inverse needed.
  - `IsResolvent T λ B` (bounded two-sided inverse of T − λ) exists, but no lemma
    "bounded self-adjoint inverse ⇒ self-adjoint"; not needed.
- `Cayley.lean`: self-adjointness is consumed (`IsCayleyTransform`), not characterised by a
  range criterion there; the criterion lives in Spectrum.lean.
- Mathlib: `LinearPMap.comp g f H` needs `∀ x : f.domain, f x ∈ g.domain`; so T†T is
  `T†.comp (T.domRestrict D) h` with `D = (T†.domain.comap T.toFun).map T.domain.subtype`.
  No `Mul`/ring structure on `H →ₗ.[ℂ] H`. `LinearPMap.adjoint_graph_eq_graph_adjoint`,
  `Submodule.mem_adjoint_iff` give the graph description of T†.

## Plan

1. key lemma: ∀ y, ∃ x w z, (x,w) ∈ Γ(T), (w,z) ∈ Γ(T†), x + z = y.
2. S symmetric, positive; Dom S dense (z ⊥ Dom S, z = (1+S)x ⇒ ‖x‖²+‖Tx‖² = 0).
3. ker(S† + 1) = ran(S+1)ᗮ = ⊥; apply `adjoint_eq_of_range_eq_top` with μ = −1.

## Results

All four declarations compiled with `lean_diagnostic_messages` showing no errors and no
`sorry` (only the module-docstring lint warning). The file imported only
`Physicslib4.Spectral.Unbounded.Spectrum`. About 18 tool calls were used.

| Step | Lean name | Lines | API used |
|---|---|---|---|
| Key lemma: ∀ y ∃ x ∈ Dom T, Tx ∈ Dom T†, x + T†Tx = y | `vN_key` | 28 | `existsUnique_add_mem_orthogonal` on `WithLp 2 (H × H)`, `WithLp.prod_continuous_ofLp`, `WithLp.prod_inner_apply`, `adjoint_graph_eq_graph_adjoint`, `Submodule.mem_adjoint_iff` |
| ⟪u, T†w⟫ = ⟪Tu, w⟫ in graph form | `vN_inner` | 4 | `mem_adjoint_iff` |
| symmetric, positive, Dom dense, self-adjoint | `vN_main` | 60 | `adjoint_eq_of_range_eq_top` (μ = −1), `orthogonal_range_subSmul`, `isSymmetric_iff_le_adjoint`, `dense_iff_orthogonal_eq_bot`, `mem_graph_snd_inj`, `graph_fst_eq_zero_snd` |
| explicit term `T†.comp (T.domRestrict D) _` has the graph `Γ(T†)∘Γ(T)` | `vN_comp_graph` | 30 | `LinearPMap.comp`, `domRestrict_apply` |

Total: about 125 lines of proof.

### What is missing

Nothing essential is missing. The classical route through the bounded inverse B = (1 + T†T)⁻¹ is
**not needed**: `adjoint_eq_of_range_eq_top` (Spectrum.lean) already is the criterion "S ≤ S†,
ran(S + 1) = H, ker(S† + 1) = {0} ⇒ S self-adjoint", and ker(S† + 1) = ran(S + 1)ᗮ = {0} comes
from `orthogonal_range_subSmul`. The project has no lemma "bounded self-adjoint inverse ⇒
self-adjoint". `IsResolvent` exists, but no such converse. If stage 3 needs B (for
example the resolvent bound ‖B‖ ≤ 1 or `IsResolvent S (-1) B`), it is extra work of about 40 to 60
lines. Not done here.

Minor gaps:
- No H × H graph decomposition in the project. The spike pulls Γ(T) back to
  `WithLp 2 (H × H)` with `Submodule.comap (WithLp.linearEquiv 2 ℂ (H × H))`, which takes about 5 lines.
- No `Mul` on `H →ₗ.[ℂ] H`, so T†T is either the explicit `comp`/`domRestrict` term or a
  hypothesis characterising its graph.

### Recommended statement shape

Characterise S by its graph, with no new `def`:

```lean
theorem isSelfAdjoint_of_graph_eq_adjoint_comp {T S : H →ₗ.[ℂ] H}
    (hT : HasDenseDomain T) (hcl : T.IsClosed)
    (hS : ∀ x z : H, (x, z) ∈ S.graph ↔ ∃ w, (x, w) ∈ T.graph ∧ (w, z) ∈ T†.graph) :
    IsSelfAdjoint S ∧ HasDenseDomain S ∧ IsPositive S
```

Add the companion `vN_comp_graph`, which shows that the explicit term
`T†.comp (T.domRestrict D) _` with `D = (T†.domain.comap T.toFun).map T.domain.subtype`
satisfies `hS`, so that the hypothesis is never vacuous. If the guard allowed a `def`
(`adjointComp T`), the term above would be its body. That is a design decision for the user.

### Estimate for stage 2 (von Neumann part)

- Blueprint nodes: 3 or 4. (i) lemma: solvability of x + T†Tx = y through the graph decomposition;
  (ii) lemma: T†T is symmetric and positive; (iii) lemma: Dom(T†T) is dense; (iv) theorem: von Neumann
  (self-adjointness through the range criterion `thrm:hall-9.21`'s `adjoint_eq_of_range_eq_top`).
- Lean: about 130 lines as spiked, or 150 to 180 with docstrings and cleanup. The private
  `adjoint_eq_of_forall_inner_iff` is not needed.

## Verified code (the deleted scratch file)

```lean
import Physicslib4.Spectral.Unbounded.Spectrum

namespace Physicslib4.Spectral.Unbounded

open scoped InnerProductSpace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Key existence lemma: `1 + T†T` maps onto `H`. -/
theorem vN_key {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (hcl : T.IsClosed) (y : H) :
    ∃ x w z : H, (x, w) ∈ T.graph ∧ (w, z) ∈ T†.graph ∧ x + z = y := by
  let e : WithLp 2 (H × H) →ₗ[ℂ] H × H := (WithLp.linearEquiv 2 ℂ (H × H)).toLinearMap
  let G : Submodule ℂ (WithLp 2 (H × H)) := T.graph.comap e
  have hG : IsClosed (G : Set (WithLp 2 (H × H))) :=
    hcl.preimage (WithLp.prod_continuous_ofLp 2 H H)
  obtain ⟨⟨g, k⟩, ⟨hg, hk, hsum⟩, -⟩ := existsUnique_add_mem_orthogonal hG (WithLp.toLp 2 (y, 0))
  have hg' : ((WithLp.ofLp g).1, (WithLp.ofLp g).2) ∈ T.graph := hg
  have hk' : ∀ u v, (u, v) ∈ T.graph →
      ⟪u, (WithLp.ofLp k).1⟫_ℂ + ⟪v, (WithLp.ofLp k).2⟫_ℂ = 0 := by
    intro u v huv
    have := (Submodule.mem_orthogonal G k).mp hk (WithLp.toLp 2 (u, v)) huv
    simpa [WithLp.prod_inner_apply] using this
  have hadj : ((WithLp.ofLp k).2, -(WithLp.ofLp k).1) ∈ T†.graph := by
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint hT, Submodule.mem_adjoint_iff]
    intro a b hab
    have := hk' a b hab
    simp only [inner_neg_right, sub_neg_eq_add]
    rw [add_comm]; exact this
  have h1 : y = (WithLp.ofLp g).1 + (WithLp.ofLp k).1 := by
    have := congrArg (fun p => (WithLp.ofLp p).1) hsum; simpa using this
  have h2 : (0 : H) = (WithLp.ofLp g).2 + (WithLp.ofLp k).2 := by
    have := congrArg (fun p => (WithLp.ofLp p).2) hsum; simpa using this
  refine ⟨(WithLp.ofLp g).1, (WithLp.ofLp g).2, (WithLp.ofLp k).1, hg', ?_, h1.symm⟩
  have hc : (WithLp.ofLp g).2 = -(WithLp.ofLp k).2 := eq_neg_of_add_eq_zero_left h2.symm
  rw [hc]
  convert T†.graph.neg_mem hadj using 1
  simp

/-- `⟪u, T†w⟫ = ⟪Tu, w⟫` in graph form. -/
theorem vN_inner {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) {w z u v : H}
    (hwz : (w, z) ∈ T†.graph) (huv : (u, v) ∈ T.graph) : ⟪u, z⟫_ℂ = ⟪v, w⟫_ℂ := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hT, Submodule.mem_adjoint_iff] at hwz
  exact (sub_eq_zero.mp (hwz u v huv)).symm

/-- von Neumann: for closed densely defined `T`, the operator `S = T†T` (characterised by its
graph) is self-adjoint, positive, and densely defined. -/
theorem vN_main {T S : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (hcl : T.IsClosed)
    (hS : ∀ x z : H, (x, z) ∈ S.graph ↔ ∃ w, (x, w) ∈ T.graph ∧ (w, z) ∈ T†.graph) :
    IsSelfAdjoint S ∧ HasDenseDomain S ∧ IsPositive S := by
  -- for `x ∈ Dom S` and `(u, v) ∈ Γ(T)`: `⟪u, S x⟫ = ⟪v, T x⟫`
  have hinner : ∀ (x : S.domain) u v, (u, v) ∈ T.graph →
      ∃ w, (x.1, w) ∈ T.graph ∧ ⟪u, S x⟫_ℂ = ⟪v, w⟫_ℂ := by
    intro x u v huv
    obtain ⟨w, hxw, hwz⟩ := (hS _ _).mp (S.mem_graph x)
    exact ⟨w, hxw, vN_inner hT hwz huv⟩
  have hsym : IsSymmetric S := by
    intro x x'
    obtain ⟨w, hxw, -⟩ := (hS _ _).mp (S.mem_graph x)
    obtain ⟨w', hxw', e1⟩ := hinner x' x w hxw
    obtain ⟨w'', hxw'', e2⟩ := hinner x x' w' hxw'
    have : w'' = w := T.mem_graph_snd_inj hxw'' hxw rfl
    subst this
    rw [e1, ← inner_conj_symm (S x) (x' : H), e2, inner_conj_symm]
  have hpos : ∀ x : S.domain, ∃ w, (x.1, w) ∈ T.graph ∧ ⟪x.1, S x⟫_ℂ = ⟪w, w⟫_ℂ := by
    intro x
    obtain ⟨w, hxw, -⟩ := (hS _ _).mp (S.mem_graph x)
    obtain ⟨w', hxw', e⟩ := hinner x x w hxw
    exact ⟨w, hxw, (T.mem_graph_snd_inj hxw' hxw rfl) ▸ e⟩
  have hdense : HasDenseDomain S := by
    refine dense_iff_orthogonal_eq_bot.mpr (Submodule.eq_bot_iff _ |>.mpr fun y hy => ?_)
    obtain ⟨x, w, z, hxw, hwz, rfl⟩ := vN_key hT hcl y
    have hxS : (x, z) ∈ S.graph := (hS _ _).mpr ⟨w, hxw, hwz⟩
    obtain ⟨xs, hxs1, hxs2⟩ := S.mem_graph_iff.mp hxS
    simp only at hxs1 hxs2
    obtain ⟨w', hxw', e⟩ := hpos xs
    have hw : w' = w := T.mem_graph_snd_inj hxw' hxw hxs1
    rw [hxs1, hxs2, hw] at e
    have h0 : ⟪x, x + z⟫_ℂ = 0 :=
      inner_eq_zero_symm.mp ((Submodule.mem_orthogonal' _ _).mp hy x (hxs1 ▸ xs.2))
    rw [inner_add_right, e] at h0
    have hre := congrArg Complex.re h0
    simp only [← RCLike.re_to_complex, map_add, map_zero, inner_self_eq_norm_sq] at hre
    have hx : x = 0 := by
      have := sq_nonneg ‖w‖; have := sq_nonneg ‖x‖
      exact norm_eq_zero.mp (by nlinarith)
    subst hx
    have hw0 : w = 0 := T.graph_fst_eq_zero_snd hxw rfl
    subst hw0
    simpa using T†.graph_fst_eq_zero_snd hwz rfl
  have hr : range (subSmul S (-1)) = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun y => ?_
    obtain ⟨x, w, z, hxw, hwz, rfl⟩ := vN_key hT hcl y
    obtain ⟨xs, hxs1, hxs2⟩ := S.mem_graph_iff.mp ((hS _ _).mpr ⟨w, hxw, hwz⟩)
    refine mem_range.mpr ⟨⟨xs, xs.2⟩, ?_⟩
    change S xs - (-1 : ℂ) • (xs : H) = _
    simp only at hxs1 hxs2
    rw [hxs1, hxs2]; simp [add_comm]
  have hk : ker (subSmul (S†) (-1)) = ⊥ := by
    have := orthogonal_range_subSmul hdense (-1)
    rw [hr, Submodule.top_orthogonal_eq_bot] at this
    simpa using this.symm
  have hle : S ≤ S† := (isSymmetric_iff_le_adjoint hdense).mp hsym
  refine ⟨adjoint_eq_of_range_eq_top hle hr hk, hdense, hsym, fun x => ?_⟩
  obtain ⟨w, -, e⟩ := hpos x
  rw [e]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- The explicit `LinearPMap` term `T†T` satisfies the graph characterisation. -/
theorem vN_comp_graph (T : H →ₗ.[ℂ] H) (x z : H) :
    let D : Submodule ℂ H := (T†.domain.comap T.toFun).map T.domain.subtype
    (x, z) ∈ (T†.comp (T.domRestrict D) (fun p => by
        obtain ⟨q, hq, hpq⟩ := p.2.1
        rw [T.domRestrict_apply (y := q) hpq.symm]
        exact hq)).graph ↔
      ∃ w, (x, w) ∈ T.graph ∧ (w, z) ∈ T†.graph := by
  intro D
  constructor
  · intro h
    obtain ⟨y, hy1, hy2⟩ := LinearPMap.mem_graph_iff _ |>.mp h
    obtain ⟨q, hq, hyq⟩ := y.2.1
    refine ⟨T q, ?_, ?_⟩
    · exact (LinearPMap.mem_graph_iff _).mpr ⟨q, hyq.trans hy1, rfl⟩
    · refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨T q, hq⟩, rfl, ?_⟩
      rw [← hy2]
      change _ = T† ⟨T.domRestrict D y, _⟩
      congr 2
      exact (T.domRestrict_apply (y := q) hyq.symm).symm
  · rintro ⟨w, hxw, hwz⟩
    obtain ⟨q, hq1, hq2⟩ := (LinearPMap.mem_graph_iff _).mp hxw
    obtain ⟨r, hr1, hr2⟩ := (LinearPMap.mem_graph_iff _).mp hwz
    simp only at hq1 hq2 hr1 hr2
    have hqD : (q : H) ∈ D := ⟨q, show T q ∈ T†.domain from hq2 ▸ hr1 ▸ r.2, rfl⟩
    have hd : (q : H) ∈ (T.domRestrict D).domain := ⟨hqD, q.2⟩
    refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨q, hd⟩, hq1, ?_⟩
    rw [← hr2]
    change T† ⟨T.domRestrict D ⟨q, hd⟩, _⟩ = _
    congr 2
    exact (T.domRestrict_apply (x := ⟨q, hd⟩) (y := q) rfl).trans (hq2.trans hr1.symm)

end Physicslib4.Spectral.Unbounded
```

# Trial 2: functional-calculus composition and |T|

Date: 2026-11-08. Status: COMPLETE (about 40 tool calls). Scratch (deleted): `Physicslib4/Spectral/Unbounded/scratch_fc_trial.lean`
(imports `Physicslib4.Spectral.Unbounded.FunctionalCalculus`; context as in `Integral.lean`, general
`μ : ProjectionValuedMeasure X H`).

## Existing API found

- `Integral.lean`: `mem_integralDomain` (Dom f(A) = `MemLp f 2 (μ.assoc ψ)`), `norm_sq_pmapIntegral`
  (‖f(A)ψ‖² = ∫|f|² dμ_ψ), `inner_self_pmapIntegral` (⟪ψ, f(A)ψ⟫ = ∫ f dμ_ψ),
  `tendsto_integral_truncation` (f·1_{|f|<n}(A)ψ → f(A)ψ), `norm_sq_integral_apply` (bounded),
  `assoc_apply_eq_norm_sq` (μ_ψ(E) = ‖μ(E)ψ‖²), `pmapIntegral_of_bddMeasurable`,
  `eq_pmapIntegral_of_inner_self`, `isSelfAdjoint_pmapIntegral_of_real`.
- **μ_{h(A)ψ} = |h|² μ_ψ exists for BOUNDED h only**: `assoc_integral_apply`,
  `lintegral_assoc_integral_apply` (Integral.lean l.1013-1065). No unbounded version.
- `OperatorIntegral.lean`: `integral_mul`, `integral_add`, `integral_conj`, `integral_indicator`,
  `integral_one`, `inner_integral`, `norm_integral_le` (bounded Borel calculus is multiplicative).
- No `pmapIntegral_add`/`pmapIntegral_mul`, no core lemma, no composition lemma for unbounded f.
- Private helpers in Integral.lean (`mul_mem_bddMeasurable`, `indicator_one_mem_bddMeasurable`)
  must be re-proved (3-5 lines each) outside.

## Verified so far

- `fc_tendsto_bdd` (≈50 lines, 0 sorry): dominated convergence. Bounded hₙ → h pointwise,
  |hₙ| ≤ |h|, ψ ∈ W_h ⇒ hₙ(A)ψ → h(A)ψ. This is the workhorse.
- `fc_mem_mul_bdd`, `fc_integral_pmapIntegral` (≈30 lines): bounded-left composition
  u(A)(h(A)ψ) = (uh)(A)ψ for bounded u, ψ ∈ W_h (and W_h ⊆ W_{uh}).
- **`fc_assoc_pmapIntegral` / `fc_assoc_pmapIntegral_eq` (≈20 lines): μ_{h(A)ψ} = |h|² μ_ψ for
  UNBOUNDED measurable h, ψ ∈ W_h**, per set and as `withDensity`. Short once the bounded-left
  composition exists: μ_{h(A)ψ}(E) = ‖μ(E)h(A)ψ‖² = ‖(1_E h)(A)ψ‖² = ∫_E |h|² dμ_ψ.
- `fc_mem_comp_iff` (≈15 lines): for ψ ∈ W_g, g(A)ψ ∈ W_f ↔ ψ ∈ W_{fg}.
- `fc_tendsto_indicator`, `fc_pmap_one`, `fc_pmap_congr` (≈30 lines): μ({|f|<n})w → w.
- **`fc_comp` (≈15 lines): the composition law f(A)g(A) ⊆ (fg)(A), with 0 sorry.**
  Together with `fc_mem_comp_iff` this gives Dom(f(A)g(A)) = Dom g(A) ∩ Dom (fg)(A).
Q1 total: about 200 lines, all compiled (0 errors, 0 sorry) after about 30 tool calls.
- `fc_pmap_bdd`, `fc_pmap_congr_pt`, `fc_commute_proj` (≈30 lines): μ(E) preserves W_h and
  h(A)μ(E)ψ = μ(E)h(A)ψ.
- **`fc_core` (≈15 lines): functional-calculus core fact.** For ψ ∈ W_h and Eₙ = {|k| < n},
  μ(Eₙ)ψ ∈ W_k, μ(Eₙ)ψ → ψ, and h(A)μ(Eₙ)ψ = μ(Eₙ)h(A)ψ → h(A)ψ. With k = id this says that
  Dom A is a core for every h(A), in particular Dom D is a core for √D.

Whole file: 259 lines, 0 errors, 0 sorry (only lint warnings).

## Q2: Dom |T| = Dom T, ‖|T|x‖ = ‖Tx‖ (not fully proved; analysis)

| Piece | Status | Size |
|---|---|---|
| (i) D ≥ 0 self-adjoint ⇒ μ^D((−∞,0)) = 0 | MISSING, no project lemma | 40-60 lines. ψₙ = μ((−n,−1/m))φ ∈ Dom D, ⟨ψₙ,Dψₙ⟩ = ∫_{(−n,−1/m)} λ dμ_φ ≤ −μ_φ(·)/m, positivity forces 0. Uses `fc_assoc_pmapIntegral_eq` with h = 1_E and `inner_self_pmapIntegral` |
| (ii) x ∈ Dom D ⇒ x ∈ Dom √D and ‖√D x‖² = ∫ λ⁺ dμ_x = ∫ λ dμ_x = ⟨x,Dx⟩ = ‖Tx‖² | needs (i). `norm_sq_pmapIntegral`, `inner_self_pmapIntegral`, `functionalCalculus_id`, `hpos` of `vN_main` (⟨x,Dx⟩ = ⟨Tx,Tx⟩) | 25-35 lines (subtype glue between `D.domain` and `integralDomain`) |
| (iii) Dom D is a core for T: (y,Ty) ⊥_Γ Γ(T|Dom D) ⇒ ⟨y, x + T†Tx⟩ = 0 ∀x ⇒ y = 0 by `vN_key` | MISSING, straightforward | 30 lines |
| (iv) Dom D is a core for √D | **DONE**: `fc_core` (k = id, h = √) | 10 lines of glue |
| (v) closure step, both directions: √D closed (self-adjoint by `isSelfAdjoint_pmapIntegral_of_real`; closedness of an adjoint from Mathlib's `LinearPMap` adjoint API, to be checked) and T closed; the isometry on cores passes to the closure | MISSING | 40-60 lines |

Q2 total: about 150 to 200 lines, 5 blueprint nodes.

## Verdicts

- Q1 composition law: **FEASIBLE, fully proved in the spike** (≈200 lines, 0 sorry). 4 nodes: (a) dominated convergence
  for the spectral integral, (b) bounded-left composition u(A)h(A) = (uh)(A), (c) μ_{h(A)ψ} = |h|²μ_ψ,
  (d) composition law plus domain iff. About 250 lines with docstrings.
- Q2 |T|: **FEASIBLE WITH GAPS**. The functional-calculus core fact is done. Missing: the spectral support of a positive
  operator, the core property of Dom T†T for T, and the closure argument. 5 nodes, 150 to 200 lines.

## Recommended statement shapes (no new defs)

```lean
-- Q1 (state for functionalCalculus hA; the spike proves it for pmapIntegral μ, which is the same by rfl)
theorem assoc_functionalCalculus (hA) {h} (hh : Measurable h) (ψ : (functionalCalculus hA h).domain) :
    (spectralMeasure hA).assoc (functionalCalculus hA h ψ) =
      ((spectralMeasure hA).assoc ψ).withDensity fun x => (‖h x‖₊ : ℝ≥0∞) ^ 2
theorem mem_domain_functionalCalculus_comp_iff (hA) (hf) (hg) (ψ : (functionalCalculus hA g).domain) :
    functionalCalculus hA g ψ ∈ (functionalCalculus hA f).domain ↔ (ψ : H) ∈ (functionalCalculus hA (f * g)).domain
theorem functionalCalculus_comp (hA) (hf) (hg) (ψ : (functionalCalculus hA g).domain)
    (hy : functionalCalculus hA g ψ ∈ (functionalCalculus hA f).domain) :
    ∃ h : (ψ : H) ∈ (functionalCalculus hA (f * g)).domain,
      functionalCalculus hA (f * g) ⟨ψ, h⟩ = functionalCalculus hA f ⟨_, hy⟩
-- Q2 (D characterised by its graph, as in Trial 1; self-adjointness from vN_main)
theorem domain_sqrt_adjoint_comp {T D : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (hcl : T.IsClosed)
    (hD : ∀ x z, (x, z) ∈ D.graph ↔ ∃ w, (x, w) ∈ T.graph ∧ (w, z) ∈ T†.graph) :
    let S := functionalCalculus (vN_main hT hcl hD).1 (fun x => ((Real.sqrt x : ℝ) : ℂ))
    S.domain = T.domain ∧ ∀ (x : S.domain) (y : T.domain), (x : H) = y → ‖S x‖ = ‖T y‖
```

Gotchas: `(pmapIntegral μ f).domain` and `integralDomain μ f` are defeq but not syntactically
equal, so `rw` fails on subtype arguments. Use `erw`, or the point/function congruence lemmas
`fc_pmap_congr_pt` / `fc_pmap_congr` (proved by `subst; rfl`), and `calc` instead of `rw` under
dependent subtypes. In this Mathlib, `MemLp f p μ` is just `eLpNorm f p μ < ∞`, so it has no
`AEStronglyMeasurable` component. `LinearPMap.ext_iff` gives `domain = domain ∧ ∀ ⦃x⦄ ⦃hf⦄ ⦃hg⦄, …`.

## Verified code (Trial 2, the deleted scratch file)

```lean
import Physicslib4.Spectral.Unbounded.FunctionalCalculus

namespace Physicslib4.Spectral.Unbounded

open scoped InnerProductSpace LinearPMap ENNReal NNReal
open Filter Topology ContinuousLinearMap MeasureTheory

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : ProjectionValuedMeasure X H)

theorem fc_mul_bdd {u v : X → ℂ} (hu : u ∈ BddMeasurable X) (hv : v ∈ BddMeasurable X) :
    u * v ∈ BddMeasurable X :=
  let ⟨hu, Cu, hCu⟩ := hu
  let ⟨hv, Cv, hCv⟩ := hv
  ⟨hu.mul hv, Cu * Cv, fun x => by
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hCu x) (hCv x) (norm_nonneg _) ((norm_nonneg _).trans (hCu x))⟩

/-- `(∫ u) ψ - (∫ v) ψ = (∫ (u - v)) ψ` for bounded `u, v`. -/
theorem fc_integral_sub_apply {u v : X → ℂ} (hu : u ∈ BddMeasurable X)
    (hv : v ∈ BddMeasurable X) (ψ : H) :
    μ.integral u ψ - μ.integral v ψ = μ.integral (u - v) ψ := by
  rw [← sub_add_cancel u v, μ.integral_add ((BddMeasurable X).sub_mem hu hv) hv, sub_add_cancel,
    add_apply, add_sub_cancel_right]

/-- Dominated convergence for the spectral integral: bounded `hₙ → h` pointwise with
`|hₙ| ≤ |h|` gives `hₙ(A)ψ → h(A)ψ` for `ψ ∈ W_h`. -/
theorem fc_tendsto_bdd {h : X → ℂ} (hh : Measurable h) (ψ : integralDomain μ h)
    {hn : ℕ → X → ℂ} (hbdd : ∀ n, hn n ∈ BddMeasurable X)
    (hlim : ∀ x, Tendsto (fun n => hn n x) atTop (𝓝 (h x))) (hle : ∀ n x, ‖hn n x‖ ≤ ‖h x‖) :
    Tendsto (fun n => μ.integral (hn n) (ψ : H)) atTop (𝓝 (pmapIntegral μ h ψ)) := by
  set t : ℕ → X → ℂ := fun n => {x | ‖h x‖ < n}.indicator h
  have ht := indicator_lt_mem_bddMeasurable hh
  have htlim : ∀ x, Tendsto (fun n => t n x) atTop (𝓝 (h x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ⌈‖h x‖⌉₊] with n hn
    have : ‖h x‖ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    simp [t, Set.indicator_of_mem (show x ∈ {x | ‖h x‖ < (n : ℝ)} from this)]
  have htle : ∀ n x, ‖t n x‖ ≤ ‖h x‖ := fun n x => by
    by_cases hx : x ∈ {x | ‖h x‖ < (n : ℝ)} <;> simp [t, hx]
  have hint : Integrable (fun x => ‖h x‖ ^ 2) (μ.assoc (ψ : H)) :=
    ψ.2.integrable_norm_pow two_ne_zero
  have hsq : Tendsto (fun n => ‖μ.integral (hn n) (ψ : H) - μ.integral (t n) ψ‖ ^ 2) atTop
      (𝓝 0) := by
    have heq : ∀ n, ‖μ.integral (hn n) (ψ : H) - μ.integral (t n) ψ‖ ^ 2 =
        ∫ x, ‖(hn n - t n) x‖ ^ 2 ∂(μ.assoc (ψ : H)) := fun n => by
      rw [fc_integral_sub_apply μ (hbdd n) (ht n),
        norm_sq_integral_apply μ ((BddMeasurable X).sub_mem (hbdd n) (ht n))]
    simp_rw [heq]
    have := tendsto_integral_of_dominated_convergence (μ := μ.assoc (ψ : H))
      (F := fun n x => ‖(hn n - t n) x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => 4 * ‖h x‖ ^ 2)
      (fun n => (((hbdd n).1.sub (ht n).1).norm.pow_const 2).aestronglyMeasurable)
      (hint.const_mul 4)
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : ‖(hn n - t n) x‖ ≤ 2 * ‖h x‖ := by
          rw [Pi.sub_apply]
          exact (norm_sub_le _ _).trans (by linarith [hle n x, htle n x])
        nlinarith [norm_nonneg ((hn n - t n) x), norm_nonneg (h x)])
      (ae_of_all _ fun x => by
        have := ((hlim x).sub (htlim x)).norm.pow 2
        simpa using this)
    simpa using this
  have hnorm : Tendsto (fun n => ‖μ.integral (hn n) (ψ : H) - μ.integral (t n) ψ‖) atTop
      (𝓝 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have := (tendsto_integral_truncation μ hh ψ).add (tendsto_iff_norm_sub_tendsto_zero.mpr
    (by simpa using hnorm) : Tendsto (fun n => μ.integral (hn n) (ψ : H) - μ.integral (t n) ψ)
      atTop (𝓝 0))
  rw [add_zero] at this
  exact this.congr fun n => add_sub_cancel _ _

/-- `W_h ⊆ W_{uh}` for bounded `u`. -/
theorem fc_mem_mul_bdd {u h : X → ℂ} (hu : u ∈ BddMeasurable X) (hh : Measurable h) {ψ : H}
    (hψ : ψ ∈ integralDomain μ h) : ψ ∈ integralDomain μ (u * h) := by
  obtain ⟨hum, C, hC⟩ := hu
  refine MemLp.of_le (hψ.const_mul (C : ℂ)) (hum.mul hh).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Pi.mul_apply, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C)) (norm_nonneg _)

/-- Bounded-left composition: `u(A) (h(A) ψ) = (u h)(A) ψ` for bounded `u`, `ψ ∈ W_h`. -/
theorem fc_integral_pmapIntegral {u h : X → ℂ} (hu : u ∈ BddMeasurable X) (hh : Measurable h)
    (ψ : integralDomain μ h) :
    μ.integral u (pmapIntegral μ h ψ) =
      pmapIntegral μ (u * h) ⟨ψ, fc_mem_mul_bdd μ hu hh ψ.2⟩ := by
  set t : ℕ → X → ℂ := fun n => {x | ‖h x‖ < n}.indicator h
  have ht := indicator_lt_mem_bddMeasurable hh
  have h1 : Tendsto (fun n => μ.integral u (μ.integral (t n) (ψ : H))) atTop
      (𝓝 (μ.integral u (pmapIntegral μ h ψ))) :=
    ((μ.integral u).continuous.tendsto _).comp (tendsto_integral_truncation μ hh ψ)
  refine tendsto_nhds_unique h1 ?_
  have h2 := fc_tendsto_bdd μ (hu.1.mul hh) ⟨ψ, fc_mem_mul_bdd μ hu hh ψ.2⟩
    (hn := fun n => u * t n) (fun n => fc_mul_bdd hu (ht n))
    (fun x => by
      refine (tendsto_const_nhds (x := u x)).mul (tendsto_const_nhds.congr' ?_)
      filter_upwards [eventually_gt_atTop ⌈‖h x‖⌉₊] with n hn
      have : ‖h x‖ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
      simp [t, Set.indicator_of_mem (show x ∈ {x | ‖h x‖ < (n : ℝ)} from this)])
    (fun n x => by
      rw [Pi.mul_apply, Pi.mul_apply, norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      by_cases hx : x ∈ {x | ‖h x‖ < (n : ℝ)} <;> simp [t, hx])
  refine h2.congr fun n => ?_
  rw [μ.integral_mul hu (ht n)]
  rfl

theorem fc_indicator_bdd {E : Set X} (hE : MeasurableSet E) :
    E.indicator (1 : X → ℂ) ∈ BddMeasurable X :=
  ⟨measurable_const.indicator hE, 1, fun x => by by_cases hx : x ∈ E <;> simp [hx]⟩

/-- **Key fact.** For `ψ ∈ W_h`, `μ_{h(A)ψ}(E) = ∫_E |h|² dμ_ψ`. -/
theorem fc_assoc_pmapIntegral {h : X → ℂ} (hh : Measurable h) (ψ : integralDomain μ h)
    {E : Set X} (hE : MeasurableSet E) :
    (μ.assoc (pmapIntegral μ h ψ)) E = ∫⁻ x in E, (‖h x‖₊ : ℝ≥0∞) ^ 2 ∂(μ.assoc (ψ : H)) := by
  have hind := fc_indicator_bdd hE
  have hn := norm_sq_pmapIntegral μ ((hind.1).mul hh) ⟨ψ, fc_mem_mul_bdd μ hind hh ψ.2⟩
  rw [assoc_apply_eq_norm_sq, ← μ.integral_indicator hE, fc_integral_pmapIntegral μ hind hh]
  erw [hn]
  rw [ofReal_integral_eq_lintegral_ofReal
      ((fc_mem_mul_bdd μ hind hh ψ.2).integrable_norm_pow two_ne_zero)
      (ae_of_all _ fun x => by positivity), ← lintegral_indicator hE]
  congr 1
  funext x
  by_cases hx : x ∈ E <;> simp [hx, enorm_eq_nnnorm]
  exact hE

/-- As measures: `μ_{h(A)ψ} = |h|² μ_ψ`. -/
theorem fc_assoc_pmapIntegral_eq {h : X → ℂ} (hh : Measurable h) (ψ : integralDomain μ h) :
    μ.assoc (pmapIntegral μ h ψ) =
      (μ.assoc (ψ : H)).withDensity fun x => (‖h x‖₊ : ℝ≥0∞) ^ 2 :=
  Measure.ext fun E hE => by rw [withDensity_apply _ hE, fc_assoc_pmapIntegral μ hh ψ hE]

theorem fc_memLp_two_iff {F : X → ℂ} (hF : Measurable F) (ν : Measure X) :
    MemLp F 2 ν ↔ ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂ν < ∞ :=
  ⟨fun h => lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top h,
    fun h => (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        hF.aestronglyMeasurable).2 h⟩

/-- Domain part of the composition law: for `ψ ∈ W_g`, `g(A)ψ ∈ W_f ↔ ψ ∈ W_{fg}`. -/
theorem fc_mem_comp_iff {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (ψ : integralDomain μ g) :
    pmapIntegral μ g ψ ∈ integralDomain μ f ↔ (ψ : H) ∈ integralDomain μ (f * g) := by
  rw [mem_integralDomain, mem_integralDomain, fc_assoc_pmapIntegral_eq μ hg ψ,
    fc_memLp_two_iff hf, fc_memLp_two_iff (hf.mul hg),
    lintegral_withDensity_eq_lintegral_mul _
      (hg.nnnorm.coe_nnreal_ennreal.pow_const 2) (hf.enorm.pow_const _)]
  refine Iff.of_eq (congrArg (· < ∞) (lintegral_congr fun x => ?_))
  simp only [Pi.mul_apply, ENNReal.rpow_two, enorm_eq_nnnorm]
  rw [nnnorm_mul, ENNReal.coe_mul]
  ring

theorem fc_pmap_congr {f f' : X → ℂ} (e : f = f') {x : H} (hx : x ∈ integralDomain μ f)
    (hx' : x ∈ integralDomain μ f') :
    pmapIntegral μ f ⟨x, hx⟩ = pmapIntegral μ f' ⟨x, hx'⟩ := by
  subst e; rfl

theorem fc_pmap_one (w : H) (hw : w ∈ integralDomain μ (1 : X → ℂ)) :
    pmapIntegral μ 1 ⟨w, hw⟩ = w := by
  have h1 : (1 : X → ℂ) ∈ BddMeasurable X := ⟨measurable_const, 1, fun x => by simp⟩
  obtain ⟨-, hext⟩ := LinearPMap.ext_iff.mp (pmapIntegral_of_bddMeasurable μ h1)
  have := @hext w hw Submodule.mem_top
  rw [this]
  change μ.integral 1 w = w
  rw [μ.integral_one]
  rfl

/-- `μ({|f| < n}) w → w`. -/
theorem fc_tendsto_indicator {f : X → ℂ} (hf : Measurable f) (w : H) :
    Tendsto (fun n : ℕ => μ.integral ({x | ‖f x‖ < n}.indicator 1) w) atTop (𝓝 w) := by
  have h1 : (1 : X → ℂ) ∈ BddMeasurable X := ⟨measurable_const, 1, fun x => by simp⟩
  have hw : w ∈ integralDomain μ (1 : X → ℂ) := by
    rw [integralDomain_eq_top_of_bddMeasurable μ h1]
    trivial
  have := fc_tendsto_bdd μ (h := (1 : X → ℂ)) h1.1 ⟨w, hw⟩
    (hn := fun n : ℕ => {x | ‖f x‖ < n}.indicator 1)
    (fun n => fc_indicator_bdd (measurableSet_lt hf.norm measurable_const))
    (fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop ⌈‖f x‖⌉₊] with n hn
      have : ‖f x‖ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
      simp [Set.indicator_of_mem (show x ∈ {x | ‖f x‖ < (n : ℝ)} from this)])
    (fun n x => by
      by_cases hx : x ∈ {x | ‖f x‖ < (n : ℝ)} <;> simp [Set.indicator, hx])
  convert this using 2
  exact (fc_pmap_one μ w hw).symm

/-- **Composition law** `f(A) g(A) ⊆ (fg)(A)`: for `ψ ∈ W_g` with `g(A)ψ ∈ W_f`,
`ψ ∈ W_{fg}` and `(fg)(A)ψ = f(A)(g(A)ψ)`. -/
theorem fc_comp {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (ψ : integralDomain μ g) (hy : pmapIntegral μ g ψ ∈ integralDomain μ f) :
    ∃ hfg : (ψ : H) ∈ integralDomain μ (f * g),
      pmapIntegral μ (f * g) ⟨ψ, hfg⟩ = pmapIntegral μ f ⟨_, hy⟩ := by
  have hfg := (fc_mem_comp_iff μ hf hg ψ).1 hy
  refine ⟨hfg, tendsto_nhds_unique ?_ (tendsto_integral_truncation μ hf ⟨_, hy⟩)⟩
  set E : ℕ → Set X := fun n => {x | ‖f x‖ < n}
  have hE : ∀ n, MeasurableSet (E n) := fun n => measurableSet_lt hf.norm measurable_const
  refine (fc_tendsto_indicator μ hf (pmapIntegral μ (f * g) ⟨ψ, hfg⟩)).congr fun n => ?_
  have h1 := fc_integral_pmapIntegral μ (fc_indicator_bdd (hE n)) (hf.mul hg) ⟨ψ, hfg⟩
  have h2 := fc_integral_pmapIntegral μ (indicator_lt_mem_bddMeasurable hf n) hg ψ
  refine h1.trans ((fc_pmap_congr μ ?_ _ _).trans h2.symm)
  funext x
  by_cases hx : x ∈ E n <;> simp [E, Set.indicator, hx] at *

theorem fc_pmap_bdd {u : X → ℂ} (hu : u ∈ BddMeasurable X) (w : H)
    (hw : w ∈ integralDomain μ u) : pmapIntegral μ u ⟨w, hw⟩ = μ.integral u w := by
  obtain ⟨-, hext⟩ := LinearPMap.ext_iff.mp (pmapIntegral_of_bddMeasurable μ hu)
  rw [@hext w hw Submodule.mem_top]
  rfl

theorem fc_pmap_congr_pt {f : X → ℂ} {x x' : H} (e : x = x') (hx : x ∈ integralDomain μ f)
    (hx' : x' ∈ integralDomain μ f) :
    pmapIntegral μ f ⟨x, hx⟩ = pmapIntegral μ f ⟨x', hx'⟩ := by
  subst e; rfl

/-- Spectral projections preserve `W_h` and commute with `h(A)`. -/
theorem fc_commute_proj {h : X → ℂ} (hh : Measurable h) (ψ : integralDomain μ h) {E : Set X}
    (hE : MeasurableSet E) :
    ∃ hn : μ E ψ ∈ integralDomain μ h, pmapIntegral μ h ⟨_, hn⟩ = μ E (pmapIntegral μ h ψ) := by
  have hind := fc_indicator_bdd hE
  have htop : (ψ : H) ∈ integralDomain μ (E.indicator (1 : X → ℂ)) := by
    rw [integralDomain_eq_top_of_bddMeasurable μ hind]; trivial
  set ψ' : integralDomain μ (E.indicator (1 : X → ℂ)) := ⟨ψ, htop⟩
  have hval : pmapIntegral μ (E.indicator 1) ψ' = μ E ψ :=
    (fc_pmap_bdd μ hind ψ htop).trans (by rw [μ.integral_indicator hE])
  have hmem : (ψ : H) ∈ integralDomain μ (h * E.indicator 1) :=
    mul_comm h (E.indicator (1 : X → ℂ)) ▸ fc_mem_mul_bdd μ hind hh ψ.2
  have hy := (fc_mem_comp_iff μ hh hind.1 ψ').2 hmem
  obtain ⟨hfg, hcomp⟩ := fc_comp μ hh hind.1 ψ' hy
  have hn : μ E ψ ∈ integralDomain μ h := by rw [← hval]; exact hy
  refine ⟨hn, ?_⟩
  calc pmapIntegral μ h ⟨_, hn⟩ = pmapIntegral μ h ⟨_, hy⟩ := fc_pmap_congr_pt μ hval.symm _ _
    _ = pmapIntegral μ (h * E.indicator 1) ⟨ψ, hfg⟩ := hcomp.symm
    _ = pmapIntegral μ (E.indicator 1 * h) ⟨ψ, fc_mem_mul_bdd μ hind hh ψ.2⟩ :=
        fc_pmap_congr μ (mul_comm _ _) _ _
    _ = μ.integral (E.indicator 1) (pmapIntegral μ h ψ) :=
        (fc_integral_pmapIntegral μ hind hh ψ).symm
    _ = μ E (pmapIntegral μ h ψ) := by rw [μ.integral_indicator hE]

/-- **Core fact for the functional calculus.** For `ψ ∈ W_h` and `Eₙ = {|k| < n}`:
`μ(Eₙ)ψ ∈ W_k ∩ W_h`, `μ(Eₙ)ψ → ψ` and `h(A)(μ(Eₙ)ψ) = μ(Eₙ)h(A)ψ → h(A)ψ`. In particular,
for self-adjoint `A = k(A)`, `Dom A` is a core for every `h(A)`. -/
theorem fc_core {h k : X → ℂ} (_hh : Measurable h) (hk : Measurable k)
    (ψ : integralDomain μ h) :
    (∀ n : ℕ, μ {x | ‖k x‖ < n} ψ ∈ integralDomain μ k) ∧
    Tendsto (fun n : ℕ => μ {x | ‖k x‖ < n} (ψ : H)) atTop (𝓝 ψ) ∧
    Tendsto (fun n : ℕ => μ {x | ‖k x‖ < n} (pmapIntegral μ h ψ)) atTop
      (𝓝 (pmapIntegral μ h ψ)) := by
  have hE : ∀ n : ℕ, MeasurableSet {x | ‖k x‖ < (n : ℝ)} := fun n =>
    measurableSet_lt hk.norm measurable_const
  refine ⟨fun n => range_subset_integralDomain μ hk (hE n) (c := n) (fun x hx => le_of_lt hx)
    ⟨ψ, rfl⟩, ?_, ?_⟩
  · simpa only [μ.integral_indicator (hE _)] using fc_tendsto_indicator μ hk (ψ : H)
  · simpa only [μ.integral_indicator (hE _)] using fc_tendsto_indicator μ hk (pmapIntegral μ h ψ)

end Physicslib4.Spectral.Unbounded
```

Note (orchestrator, 2026-11-08): the gap "a positive self-adjoint D has μ^D((−∞,0)) = 0" is already
proved in the library as `Physicslib4.AQFT.spectralMeasure_Iio_zero_eq_zero`
(`Physicslib4/AQFT/PositiveEnergyHolomorphic.lean`); reuse it (or move it to a spectral file).
