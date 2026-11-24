# Review: sorry'd statements for `sbsctn:takesaki-kms`

Files: `Hilbert6/Operators/Modular/TakesakiKMS.lean` (26 theorems),
`Hilbert6/GNS/VectorState.lean` (2 theorems). Blueprint: end of
`blueprint/src/sections/sec10/tomita-takesaki.tex`.

Scope: all 28 labels are recorded with `leanDeclaration`/`leanFile`, and none has a terminal
assessment. The three definitions, `thrm:takesaki-kms` and `lmm:modular-automorphism-one-parameter`
are deferred on purpose and are not reviewed here. Both files compile with only `sorry` warnings,
and both are imported from `Hilbert6.lean`.

## Required fix

1. **lmm:vector-functional-state, lmm:vector-functional-norm-one** (`VectorState.lean`): the
   instance binder `[IsClosed (𝔄 : Set (H →L[ℂ] H))]` is not used by either statement or proof.
   Continuity, `‖ω‖ ≤ 1`, positivity and `‖ω‖ = 1` hold for every unital `*`-subalgebra, and the
   norm on `𝔄` is the subtype norm whether or not `𝔄` is closed. Closedness matters only for
   `def:vector-state`, which needs `CStarAlgebra 𝔄` to form `State 𝔄`, and that definition can
   supply it. Drop the binder from both lemmas, and say in the docstrings that the lemmas hold for
   any unital `*`-subalgebra. Also add `omit [CompleteSpace H] in`: completeness of `H` is not used.

## Checked and correct (no change needed)

- **Signs and strip.** `u_z = 1_{(0,1)} λ^{-iz}` and `v_z = 1_{[1,∞)} λ^{-iz-1}`. On `kmsStrip 1` we
  have `|λ^{-iz}| = λ^{Im z}`, so both functions are bounded by 1. At `z = t`,
  `u_t + s² v_t = 1_{(0,∞)} λ^{-it} = e_{-t}`, which gives `Δ^{-it}` = `modularUnitaryGroup (-t)`
  because `Δ^{it} = e_t(Δ)` (VanDaele `modularUnitaryGroup_eq_functionalCalculus`). At `z = t + i`,
  `-i(t+i) = 1 - it`, which matches `s² g_t = u_{t+i}` and `g_t + v_{t+i} = 1_{(0,∞)} e_{-t}`. I
  checked each scalar identity on λ ≤ 0, on 0 < λ < 1 and on λ ≥ 1.
- **Inner product.** `⟪·,·⟫` is conjugate-linear in the first slot, and `z` enters only through the
  second slot, so `G` and `G^n` are holomorphic in `z`. The upper-boundary correlation uses
  `⟪Jx, Jy⟫ = ⟪y, x⟫` and gives `⟪Ω, Δ^{-it} b Δ^{it} a Ω⟫`. The lower one gives
  `⟪Ω, a Δ^{-it} b Δ^{it} Ω⟫`. Both agree with `IsKMSState` at `α t = σ_{-t}`, `β = 1`.
- **Cut-offs.** `K[n]`, `p[z, n]` and `e[t]` are copied verbatim from `VanDaele.lean`, and the
  spectral measure is `spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)` as there.
  `1 ≤ n` is present wherever it matters (approximants entire, approximants on the strip, the
  uniform bound).
- **`PVM.integral`** returns `0` off `BddMeasurable`. `G` uses `u[z]` and `v[z]` only under the
  indicator of `kmsStrip 1`, where they are bounded, so no statement depends on the junk value. The
  eigenvector lemma keeps `hf : f ∈ BddMeasurable ℝ`. It is needed: without it the left side is `0`.
- **Not vacuous.** The hypotheses in each statement can hold together. The sets are right:
  `Ioo 0 1` and `Ici 1` partition `(0,∞)`, and `Ioi 0` is the support of `e_{-t}` that is used.

## Judgement on the listed deviations

- **Membership hypotheses dropped** (lmm:takesaki-lower-boundary-state, and the algebraic parts of
  lmm:modular-automorphism-well-defined): acceptable. These identities hold for every bounded
  operator, and generalising them strengthens the lemmas without changing what they say. In
  lmm:takesaki-upper-boundary-state, `ha`/`hb` are correctly kept, because the identity needs
  `Δ^{1/2}a*Ω = JaΩ`, which uses `a ∈ M`.
- **Explicit domain hypotheses `ha' hb'`** in lmm:takesaki-upper-boundary-state: acceptable. They are
  needed to form `Δs ⟨star a Ω, ha'⟩`. They follow from `ha`, `hb` by
  `modularOperatorSqrt_apply_of_mem` (with `hM.1` for `star a`), and proof irrelevance makes the
  statement independent of which proof is passed. The docstring already says this.
- **`n ≥ 1` dropped** in lmm:takesaki-functions-identities: acceptable. The identity is a
  rearrangement of indicators and holds for any `n`. At `n = 0`, `K[0] = {0}` and both sides vanish.
- **lmm:modular-algebra-closed on `StarSubalgebra.centralizer ℂ (Set.centralizer M)`**: acceptable.
  This is literally the term `def:modular-algebra` specifies. Non-blocking: the first conjunct
  repeats the internal `hB` in `isVonNeumannSet_centralizer`. When this is proved, consider exposing
  it there instead of proving it twice.
- **lmm:vector-functional-state as `∃ ω : 𝔄 →L[ℂ] ℂ, (∀ x, ω x = ⟪Ω, xΩ⟫) ∧ …`**: acceptable and
  faithful. `norm_vectorFunctional` takes `ω` and `hω`, so the pair is usable. Non-blocking
  alternative that needs no `def`: state the bound and positivity directly about the explicit term
  `innerSL ℂ Ω ∘L ContinuousLinearMap.apply ℂ H Ω ∘L 𝔄.toSubalgebra.toSubmodule.subtypeL` (or an
  equivalent CLM composite). `def:vector-state` could then reuse that term as its
  `toContinuousLinearMap`.

## Hygiene-free local notations (`μΔ`, `Δs`, `U[t]`, `G[…]`, `Gn[…]`)

Verdict: acceptable, keep them. Mathlib uses the same device
(`AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`: `set_option hygiene false` plus
`local notation3 "Proj" => Proj.toLocallyRingedSpace 𝒜`). The notations are file-local. If a
declaration lacks the binders `hM hΩ C hC`, it fails to elaborate rather than silently capturing
something else, and the module docstring documents the convention. Writing `G`/`Gn` out in full
would put 8–12 lines of expanded inner products into six signatures, which is much harder to check
than the notation. VanDaele writes things out because its closed notations never needed binders.

Alternatives considered and rejected:

- Moving `{M Ω} hM hΩ C hC` into a section `variable` block (the Proj precedent) silently drops
  `hM hΩ hC` from statements that do not mention them. `modularOperator_apply_self` mentions only
  `M Ω C`, and `coe_starSubalgebra_centralizer_centralizer` mentions only `hM`. Each would need
  `include`, which is an easy trap. It also departs from VanDaele's style.
- Passing the four binders explicitly to each notation (`G[hM, hΩ, C, hC; ξ, η, hξ, hη]`) is
  hygienic but noisy. It is a fine fallback if a later pass wants hygiene back.

Two side effects to be aware of (non-blocking):

- `fun z : ℂ => …` inside `G[…]`/`Gn[…]` is unhygienic. A `ξ`/`η` argument term containing a free
  `z` would be captured. No current use does this, and `thrm:takesaki-kms` will pass
  `star a Ω`, `b Ω`. Renaming the bound variable to something unlikely, such as `w`, removes the
  hazard.
- The generated unexpanders print `Δs` in goals in this file (hover shows `Δs.domain`). This happens
  only when the arguments are literally named `hM hΩ C hC`, so it is harmless but can hide which
  data is meant.

## Readability (binder groups)

- lmm:modular-sqrt-transfer has 13 groups and lmm:takesaki-upper-boundary-state has 12. Account:
  - Six groups (`{M} {Ω} hM hΩ C hC`) are the project's standard Tomita data, shared by every
    declaration in `Modular/*.lean`. They cannot be bundled without a new `structure`, which the
    guard blocks.
  - The rest are the blueprint's hypotheses (`f`, `hf`, `hsf`, `hs2f`, `ξ η`, `hξ hη`), or are
    needed to type a subterm (`ha' hb'`).

  Every binder is accounted for, so neither label fails on size.

## Non-blocking points

- **BLUEPRINT (lmm:modular-sqrt-transfer):** `hsf` is implied by `hf` and `hs2f`, because
  `s|f| ≤ max(|f|, s²|f|)` and `s·f` is measurable when `f` is. Dropping it from the blueprint and
  the Lean would also let lmm:takesaki-functions-aux-bounds lose its `|s v_t|` and `|s g_t|`
  conjuncts. The Lean is faithful as it stands.
- lmm:spectral-moments (7 conjuncts) and lmm:modular-automorphism-well-defined (6 conjuncts, the
  last nested) pack many conclusions, but they mirror the blueprint lemmas one-to-one. If the
  blueprint is revisited, split off the membership `σ_t(M) ⊆ M`: it carries all the Tomita content,
  and the rest is algebra of composition.
- `takesakiFunction_upper_boundary` evaluates at `(t : ℂ) + Complex.I`, while `IsKMSState` uses
  `(t : ℂ) + ((1 : ℝ) : ℂ) * Complex.I`. `thrm:takesaki-kms` will need a `simp`/`one_mul` bridge.
  This is fine to leave.

VERDICT: REVISE
1. lmm:vector-functional-state, lmm:vector-functional-norm-one: drop the unused
   `[IsClosed (𝔄 : Set (H →L[ℂ] H))]` binder (and `omit [CompleteSpace H] in`).

---

# Pass 2: the deferred nodes

Status of pass 1: the required fix is applied. The `omit [CompleteSpace H]` suggestion is
withdrawn, because `StarRing (H →L[ℂ] H)` needs completeness.

New declarations reviewed:

- `TakesakiKMS.lean`: `modularAlgebra`, `coe_modularAlgebra`, `isClosed_modularAlgebra`,
  `modularAutomorphism`, `coe_modularAutomorphism_apply`, `isOneParameterAut_modularAutomorphism`,
  `isKMSState_modularAutomorphism`.
- `GNS/VectorState.lean`: `vectorState`, `vectorState_apply`.

Both files compile with only `sorry` warnings. Those warnings fall on theorems only: the five
earlier lemmas plus `isOneParameterAut_…` and `isKMSState_…`. None of the definitions or the
instance contains a raw `sorry`.

## Required fix

1. **def:modular-algebra: drop `_hM`.** The only reason `_hM` exists is so that
   `isClosed_modularAlgebra` can be an instance, and the instance does not need it.
   - For any `s`, the carrier of `StarSubalgebra.centralizer ℂ s` is `Set.centralizer (s ∪ star s)`
     (`StarSubalgebra.coe_centralizer`).
   - That set is closed by `Set.isClosed_centralizer`, since `B(H)` is T2 with continuous
     multiplication. Mathlib itself uses this in
     `Topology/Algebra/StarSubalgebra.lean:120`.
   - So define `modularAlgebra (M : Set (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H)` and prove
     `instance : IsClosed (modularAlgebra M : Set _)` without `hM`.
   - Keep `hM` where it is used: `coe_modularAlgebra hM : (modularAlgebra M : Set _) = M`,
     `modularAutomorphism`, and the theorems.
   - The closedness half of `coe_starSubalgebra_centralizer_centralizer` then also needs no `hM`.
     Either state it separately or keep the conjunction; this is not blocking.

   This is the type every later statement is written over (`State (modularAlgebra …)`, `≃⋆ₐ`), so
   fix it now. A phantom proof argument on a def is what Mathlib's `unusedArguments` linter flags.
   This changes a definition, so it goes through the same guard approval.

## Checked and correct

- **thrm:takesaki-kms.** `IsKMSState (fun t => modularAutomorphism … (-t)) 1 (vectorState
  (modularAlgebra hM) Ω hΩ1)` unfolds to the following, for all `a b`:
  - a continuous `F` on `kmsStrip 1`, holomorphic on the interior and bounded;
  - `F t = ω(a σ_{-t}(b))`;
  - `F(t + 1·i) = ω(σ_{-t}(b) a)`.

  This is exactly the blueprint statement, with the reversed flow at `β = 1`. With
  `σ_{-t}(b) = Δ^{-it} b Δ^{it}` (`coe_modularAutomorphism_apply` at `-t`, `neg_neg`) and
  `ω x = ⟪Ω, xΩ⟫` (`vectorState_apply`, `rfl`), the boundary values are the right-hand sides of
  `inner_modularUnitaryGroup_lower/upper_boundary`. `F := G[star a Ω, b Ω, …]` fits. The upper
  boundary point is written `(t:ℂ) + ((1:ℝ):ℂ) * I`, which the proof bridges with `one_mul`.
- **lmm:modular-automorphism-one-parameter.** `IsOneParameterAut (modularAutomorphism …)` says
  `σ_0 a = a` and `σ_{s+t} a = σ_s (σ_t a)`. This is faithful. `IsKMSState` does not require the
  family to be a one-parameter group, so the theorem does not depend on this lemma. If wanted, the
  reversed flow's group property is a two-line corollary (non-blocking).
- **`modularAutomorphism`.**
  - `toFun` is `U[t] ∘L x ∘L U[-t]` and `invFun` is `U[-t] ∘L x ∘L U[t]`. Membership comes from
    the proved VanDaele lemma `modularUnitaryGroup_conj_mem_of_mem` (at `-t` plus `neg_neg` for the
    inverse).
  - The algebraic fields come from `modularAutomorphism_wellDefined`, and the add/smul fields from
    `simp`.
  - The data is concrete. Non-blocking: the first conjunct of `modularAutomorphism_wellDefined`
    (membership) duplicates `modularUnitaryGroup_conj_mem_of_mem`, which is already proved, so
    that conjunct can be closed by citing it.
- **Instances: no diamond.** `StarSubalgebra.cstarAlgebra` (`Analysis/CStarAlgebra/Classes.lean:50`)
  sets only `toCompleteSpace` and `norm_mul_self_le`. All other fields (norm, ring, star, algebra)
  are the existing subtype instances. This is confirmed in the code:
  - `vectorState`'s `isNormalized := norm_vectorFunctional 𝔄 hΩ _ fun _ => rfl` typechecks. The
    `‖·‖` on `𝔄 →L[ℂ] ℂ` built from the `CStarAlgebra` path is therefore defeq to the subtype-path
    norm used in the lemma.
  - `vectorState_apply` is `rfl`.
- **`vectorState`.** `innerSL ℂ Ω ∘L apply Ω ∘L (subtype as a CLM)` is the explicit term, so it is
  the right definition of `ω_Ω`. Positivity comes from `exists_vectorFunctional` through `hω`. The
  `[IsClosed]` binder is needed here (for `State 𝔄`) and is correctly kept on the def only.

VERDICT (pass 2): REVISE
1. def:modular-algebra: remove the unused `_hM` argument from `modularAlgebra`, and prove the
   instance `IsClosed (modularAlgebra M : Set _)` from `StarSubalgebra.coe_centralizer` and
   `Set.isClosed_centralizer` with no von Neumann hypothesis.
