# Plan: a local proof of the von Neumann density theorem

Date: 2026-09-30. Toolchain: Lean / Mathlib v4.34.1. Branch to use: a new branch off
`numina/aqft-in-lean` (e.g. `numina/von-neumann-density`).
Status: plan only. Nothing below is implemented.
Research: `notes/agents/scout/von-neumann-density-2026-09-30.md` (API inventory, estimates).

## Goal

Prove `Physicslib4.AQFT.HaagKastler.dense_range_in_bicommutant`
(`Physicslib4/AQFT/HaagKastler/StrongDensity.lean`, blueprint `thrm:quasilocal-strongly-dense`,
`blueprint/src/sections/sec10/haag-kastler-axioms.tex` ~line 569), the project's only remaining
`sorry`, **without changing its statement**: for a unital `*`-algebra hom
`π : 𝔄 →⋆ₐ[ℂ] (H →L[ℂ] H)`, the bicommutant `π(𝔄)''` lies in the strong-operator closure of
`π(𝔄)` (strong topology = Mathlib's `PointwiseConvergenceCLM`, via `UniformConvergenceCLM.ofFun`
on finite sets). Then remove its `**Restriction:**` line and mark the blueprint node proved.

Nothing else in the project depends on the theorem, so every stage keeps the build green.

## Mathematical route (Murphy, Lemma 4.1.4)

1. **One vector.** For `ξ ∈ H` let `K = closure (π(𝔄) ξ)`. `K` is invariant under every `π a`
   and every `π a* = π (star a)`, so its orthogonal projection `P` commutes with `π(𝔄)`, i.e.
   `P ∈ π(𝔄)'`. For `T ∈ π(𝔄)''`, `T P = P T`; `ξ = π 1 ξ ∈ K` (unitality), so `T ξ ∈ K`:
   `T ξ` is a limit of vectors `π a ξ`.
2. **Finitely many vectors.** Amplify: `πⁿ(a) = diag(π a, …, π a)` on `ℓ²(Fin n; H)`. If
   `T ∈ π(𝔄)''` then `diag(T) ∈ (πⁿ(𝔄))''` (every `S ∈ (πⁿ(𝔄))'` is an `n × n` block matrix with
   entries in `π(𝔄)'`, and `T` commutes with each entry). Apply step 1 to `πⁿ` and the tuple
   `(ξ₁, …, ξₙ)`: one `a` approximates `T ξᵢ` by `π a ξᵢ` for all `i` simultaneously.
3. **Strong topology.** Basic neighbourhoods of `T` are given by finitely many vectors and an
   `ε`, so step 2 puts an element of `π(𝔄)` in every neighbourhood of `T`.

## Design decisions for the user (settle before Stage 2)

1. **Finite amplification.** DECIDED (2026-10-01): option (a). `GNS/Amplification.lean` and `GNS/DirectSum.lean` require
   `[CStarAlgebra A]`, but the target has a bare `*`-algebra `𝔄`. Options:
   - (a) a new `Fin n`-indexed amplification for a single `π`, built directly on the fully
     general `lpDiag` (`Physicslib4/Operators/LpDiagonal.lean`) with the bound `‖π a‖` itself
     (recommended: additive, touches nothing existing);
   - (b) generalise `DirectSum.directSumFun`/`directSum` from `[CStarAlgebra A]` to an explicit
     uniform bound hypothesis (more general, but changes existing signatures).
2. **Where the new lemmas live.** DECIDED (2026-10-01): the recommendation. Recommendation: the general operator-theory lemma (reducing
   subspace) in `Physicslib4/Operators/ReducingSubspace.lean`; the amplification and density
   lemmas in a new `Physicslib4/Operators/DensityTheorem.lean` (or in `GNS/Amplification.lean`
   if option (b) is chosen); `StrongDensity.lean` keeps only the final assembly.
3. **Kaplansky density** (self-adjoint approximants) stays out of scope, as the blueprint says.
   DECIDED (2026-10-01): out of scope.
4. **Blueprint placement.** DECIDED (2026-10-01): a new subsection "The von Neumann density
   theorem" in `haag-kastler-axioms.tex`, just before `thrm:quasilocal-strongly-dense`.

## Stages

Each stage ends with `lake build`, `lake lint`, `leanblueprint checkdecls`, a commit, and a
progress entry in this file. New `def`s are blocked for agents by `.claude/lean-policy.json`, so
the orchestrator writes every `def`; provers write theorems.

### Stage 1: blueprint decomposition (fuse:blueprint + fuse:blueprint-reviewer)

The node `thrm:quasilocal-strongly-dense` currently says it is "deliberately not decomposed
further and not formalized". Replace its proof by a decomposition with `\uses{}` edges, adding
lemma nodes (in `haag-kastler-axioms.tex`, just before the theorem, or in a chapter-10 operator
section if one fits better):
- `lmm:reducing-subspace-projection-commutes`: a closed subspace invariant under `T` and `T*`
  has orthogonal projection commuting with `T`.
- `lmm:cyclic-subspace-reduces`: `closure(π(𝔄)ξ)` is invariant under `π(𝔄)` (and hence under
  adjoints, since `π` is a `*`-homomorphism).
- `lmm:bicommutant-single-vector`: for `T ∈ π(𝔄)''`, `Tξ ∈ closure(π(𝔄)ξ)`.
- `def:finite-amplification`: `πⁿ(a) = diag(π a, …)` on `ℓ²(Fin n; H)`.
- `lmm:commutant-of-amplification-entries`: every `S ∈ (πⁿ(𝔄))'` has block entries in `π(𝔄)'`.
- `lmm:diagonal-in-amplified-bicommutant`: `T ∈ π(𝔄)'' ⇒ diag(T) ∈ (πⁿ(𝔄))''`.
- `lmm:bicommutant-finite-vectors`: for `T ∈ π(𝔄)''`, finitely many `ξᵢ` and `ε > 0`, some
  `a` has `‖Tξᵢ − π a ξᵢ‖ < ε` for all `i`.
Deliverable: reviewed blueprint (validate clean apart from the known `conv:` errors).

### Stage 2: the one-vector case (Lean; can run before any `def` exists)

- `reducing_subspace_commutes_projection` (general, `Physicslib4/Operators/`): for `K` closed,
  `MapsTo T K K` and `MapsTo (adjoint T) K K`, `Commute T K.starProjection` (or the
  `orthogonalProjection` form). First search Mathlib live (`lean_loogle`, leansearch) for an
  existing statement phrased via `IsIdempotentElem`, `IsStarProjection`, `ker`/`range` — the
  scout's grep found none. Proof: `x = y + z`, `y ∈ K`, `z ∈ Kᗮ`; `T y ∈ K`; `T z ∈ Kᗮ` because
  `⟪T z, k⟫ = ⟪z, T* k⟫ = 0`. About 10–15 lines, possibly split in two.
- `cyclic_subspace_reduces`: invariance of `closure (range (fun a ↦ π a ξ))` (as a closed
  submodule: `(Submodule.span …).topologicalClosure` or the range of `π · ξ` as a submodule,
  since `π` is linear) under `π a` and `adjoint (π a) = π (star a)` (`map_star`, continuity,
  `closure_mono`/`Submodule.topologicalClosure_mono`). About 5–10 lines.
- `mem_closure_of_mem_bicommutant` (single vector): from the two lemmas and `map_one`. About
  10 lines.
Parallelism: the first two lemmas are independent (two provers); the third follows.
Deliverable: the one-vector case proved, target still `sorry`.

### Stage 3: the finite amplification (orchestrator defs + provers)

- Orchestrator writes (decision 1a) `finiteAmplification π n : 𝔄 →⋆ₐ[ℂ] (lp (fun _ : Fin n ↦ H) 2
  →L[ℂ] lp (fun _ : Fin n ↦ H) 2)` from `lpDiag (fun _ ↦ π a) (norm_nonneg _) (fun _ ↦ le_rfl)`,
  with the `*`-algebra-hom fields as sorry'd theorems (`map_one`, `map_mul`, `map_add`,
  `map_smul`/`commutes`, `map_star`) delegated to a prover (they follow `lpDiag_one/_mul/_add/
  _smul/_star`, exactly as `GNS/DirectSum.lean` does for `directSum`).
- Also a `def` for the diagonal operator `diag T := lpDiag (fun _ ↦ T) …` if convenient, and a
  way to build the tuple `(ξ₀, …, ξₙ₋₁)` as an element of `lp _ 2` over `Fin n` (every function
  on a finite type is in `lp`: `memℓp_gen`/`Memℓp.of_finite`-type lemma; confirm the name).
- Prove `finiteAmplification_apply` and the reusable commutant facts; `intertwines_single` and
  `summandProj_mem_commutant` from `GNS/DirectSum.lean` transfer verbatim (they use no
  C*-structure).
Deliverable: amplification with its API, no sorry.

### Stage 4: the diagonal lemma (hardest step; provers)

- Block entries: `S_{jk} := lpEvalCLM j ∘L S ∘L lp.singleContinuousLinearMap ℂ _ 2 k`; show
  `S ∈ (πⁿ(𝔄))' ⇒ S_{jk} ∈ π(𝔄)'` (unfold with `lpDiag_apply_coe`, `lp.single_apply`).
- Finite decomposition `x = ∑ k, lp.single 2 k (x k)` for `Fin n`: from `lp.hasSum_single`
  (`Mathlib/Analysis/InnerProductSpace/l2Space.lean`) and `hasSum_fintype` / `HasSum.unique`.
- `(S x) j = ∑ k, S_{jk} (x k)`, then `diag(T) S = S diag(T)` by commuting `T` past each
  `S_{jk}`; conclude `diag(T) ∈ (πⁿ(𝔄))''`.
Split into at least three lemmas (entries, decomposition, commutation); estimate 40–80 lines.
Deliverable: `lmm:diagonal-in-amplified-bicommutant` proved.

### Stage 5: assembly

- `bicommutant_finite_vectors`: apply the one-vector case to `πⁿ`, `diag(T)` and the tuple;
  read off the coordinates (`lpEvalCLM`), and use `‖(v)ᵢ‖ ≤ ‖v‖` in `lp` to get the uniform
  approximation. About 15–20 lines.
- `dense_range_in_bicommutant`: unfold `UniformConvergenceCLM.ofFun` (a type-level identity);
  use `mem_closure_iff_nhds_basis'` with the pointwise-convergence neighbourhood basis
  (`PointwiseConvergenceCLM.hasBasis_nhds_zero` is centred at `0`: translate by `T`, or find an
  at-a-point version / use `UniformConvergenceCLM` uniformity); pick the finite set and `ε` from
  the basic neighbourhood and apply the previous lemma. About 10–15 lines.
- Remove the `**Restriction:**` line and the "left unproved" sentences from the
  `StrongDensity.lean` docstrings; mark `thrm:quasilocal-strongly-dense` and the Stage 1 lemmas
  proved; `#print axioms dense_range_in_bicommutant` must show only the standard three.
Deliverable: no `sorry` in the project.

### Stage 6: clean-up

- Blueprint: update the theorem's text (it is now formalized), rebuild PDF/web, refresh
  `home_page/index.md` (counts, the "not formalised" list, renumbering), `checkdecls`.
- Optional: derive `GNS/Amplification.lean` / `DirectSum.lean` facts from the new general
  amplification if it removes duplication; run the golfer on the new files.
- Merge the branch into `numina/aqft-in-lean`.

## Risks and mitigations

- **Reducing-subspace lemma may exist in Mathlib under another phrasing**: search first
  (Stage 2); if found, Stage 2 shrinks to glue.
- **`lp` bookkeeping over `Fin n`** (coercions, `Memℓp` for finite types, `lp.single`): budget
  extra time in Stage 4; an alternative carrier is `PiLp 2 (fun _ : Fin n ↦ H)` (Mathlib's
  finite ℓ² product, an inner-product space with `EuclideanSpace`-style API), which may make
  block entries (`ContinuousLinearMap.proj`/`single`) simpler — but then `lpDiag` would not be
  reused. Decide at the start of Stage 3.
- **Neighbourhood basis centred at 0**: the translation step in Stage 5 may need a small lemma.
- **Guard hook**: every new `def` is written by the orchestrator (or approved by the user).
- **Statement must not change**: if a stage suggests the statement is inconvenient, prove a
  convenient restatement as a separate lemma instead.

## Suggested session breakdown

1. Stage 1 (blueprint) and the design decisions.
2. Stage 2 (one-vector case), plus Stage 3 defs.
3. Stage 3 proofs and Stage 4 (diagonal lemma), possibly two sessions.
4. Stage 5 (assembly) and Stage 6 (clean-up, merge).

Total estimate: about 130–200 Lean lines in about 7–10 lemmas plus 1–2 definitions.

## Progress log

- 2026-10-01, Stage 1 (branch `numina/von-neumann-density`, not committed): new subsection
  "The von Neumann Density Theorem" in `haag-kastler-axioms.tex` (lines ~568–683) with
  lmm:reducing-subspace-projection-commutes, lmm:cyclic-subspace-reduces,
  lmm:bicommutant-single-vector, def:finite-amplification, lmm:finite-amplification-star-hom,
  lmm:commutant-of-amplification-entries, lmm:amplification-block-expansion,
  lmm:diagonal-in-amplified-bicommutant, lmm:bicommutant-finite-vectors,
  lmm:strong-neighbourhood-basis; thrm:quasilocal-strongly-dense's proof rewritten (statement
  unchanged); new heading "Lorentz Covariance and the Haag--Kastler Net" after it (user choice).
  Reviewer: REVISE then PASS. Changes from the plan: the amplification is indexed by a finite
  type ι (ι = the finite set s from the neighbourhood basis), not `Fin n`; the one-vector lemmas
  are stated for an arbitrary complex Hilbert space; the strong neighbourhood basis at T is its
  own lemma. Optional reviewer notes: `norm_sub_rev` orientation in the finite-vectors lemma;
  cite `Submodule.topologicalClosure_coe`; phrase the basis lemma on the `ofFun` image.
- 2026-10-01, Stage 1 committed as `76fc546`. Stage 2 done (not committed): new
  `Physicslib4/Operators/ReducingSubspace.lean` (`commute_starProjection_of_invariant`, by hand —
  no Mathlib lemma found) and `Physicslib4/Operators/DensityTheorem.lean`
  (`starProjection_cyclic_mem_centralizer`, `apply_mem_closure_of_mem_bicommutant`), all proved,
  standard axioms. The cyclic subspace is phrased as
  `(Submodule.span ℂ (Set.range fun a ↦ ρ a ξ)).topologicalClosure`; the conclusion uses
  `closure (Set.range fun a ↦ ρ a ξ)`. `[StarModule ℂ 𝔄]` dropped from these lemmas (unused).
  Next: Stage 3 (finite amplification defs by the orchestrator).
- 2026-10-01, Stage 2 committed as `730a5d7`. Stage 3 done (not committed): in
  `DensityTheorem.lean`, `ampDiag ι T` (diag(T) on ℓ²(ι; E) via `lpDiag`), `diagAmplification ι ρ`
  (a `StarAlgHom`, all fields proved directly, following `GNS.directSum`), `toLp2` (finite family
  as an element of ℓ², via `Memℓp.all`), with simp lemmas. Indexed by any type ι (finiteness only
  for `toLp2`). def:finite-amplification and lmm:finite-amplification-star-hom marked proved.
  Next: Stage 4 (block entries, block expansion, diagonal-in-bicommutant).
- 2026-10-01, Stage 3 committed as `198c621`. Stage 4 done (not committed): `blockEntry` def
  (orchestrator), `blockEntry_apply`, `blockEntry_mem_centralizer`, `apply_eq_sum_blockEntry`
  (via `lp.hasSum_single` + `hasSum_fintype`), `ampDiag_mem_bicommutant` (statement generalised
  to `[Finite ι]` without `DecidableEq`; `classical` + `Fintype.ofFinite` inside). All proved.
  Next: Stage 5 (finite-vectors lemma, strong neighbourhood basis, assembly of the target).
- 2026-10-01, Stage 4 committed as `b3f5cdf`. Stage 5 done (not committed):
  `exists_forall_norm_sub_lt_of_mem_bicommutant` (DensityTheorem.lean), `hasBasis_nhds_ofFun` and
  `dense_range_in_bicommutant` (StrongDensity.lean) proved; the Restriction paragraph and
  "left unproved" sentences removed. `[StarModule ℂ 𝔄]` dropped from StrongDensity's variables
  (unused; the target is now slightly more general — the only change to its statement) and
  `[CompleteSpace H]` omitted from `hasBasis_nhds_ofFun`, as required by `lake lint`.
  No `sorry` remains in the project; `#print axioms dense_range_in_bicommutant` = standard three.
  Remaining: Stage 6 (blueprint text/PDF/web, home page, golf optional, merge).
- 2026-10-01, Stage 5 committed as `0642785`. Stage 6: blueprint PDF/web rebuilt, checkdecls
  green, home page refreshed (`1a073c1`: 607 declarations, 606 formalised, no sorry), and
  `numina/aqft-in-lean` fast-forwarded to `numina/von-neumann-density`. Plan complete; optional
  golf of the new files not done.
