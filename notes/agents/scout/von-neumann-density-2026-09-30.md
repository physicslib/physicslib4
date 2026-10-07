# Scout memo: von Neumann bicommutant density theorem

## Target

`Physicslib4.AQFT.HaagKastler.dense_range_in_bicommutant`
(`Physicslib4/AQFT/HaagKastler/StrongDensity.lean:68`), blueprint
`thrm:quasilocal-strongly-dense`
(`blueprint/src/sections/sec10/haag-kastler-axioms.tex` ~line 569):

```
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {𝔄 : Type*} [Ring 𝔄] [StarRing 𝔄] [Algebra ℂ 𝔄] [StarModule ℂ 𝔄]

theorem dense_range_in_bicommutant (π : 𝔄 →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ⇑(UniformConvergenceCLM.ofFun (σ := RingHom.id ℂ) (E := H) (F := H)
        {s : Set H | s.Finite}) '' Set.centralizer (Set.centralizer (Set.range π)) ⊆
    closure (⇑(UniformConvergenceCLM.ofFun (σ := RingHom.id ℂ) (E := H) (F := H)
        {s : Set H | s.Finite}) '' Set.range π) := by sorry
```

Murphy Lemma 4.1.4 / Kadison–Ringrose 5.3.1: for a **unital** `*`-hom `π`
(unitality carried by `StarAlgHom.map_one`), `π(𝔄)` is dense in `π(𝔄)''` in the
strong operator topology `H →Lₚₜ[ℂ] H` (`PointwiseConvergenceCLM`, `𝔖 =
{finite sets}`). `𝔄` is *only* a unital `*`-algebra over `ℂ`, not normed — only
the already-bounded operators `π a : H →L[ℂ] H` carry norms. `ofFun` is a
bijection (`⟨id, id, _, _⟩`), so the goal reduces to the unadorned
operator-topology statement. No route below weakens the target.

## 1. Standard proof route

`M = π(𝔄)`, unital `*`-subalgebra of `𝓑(H)`.

- **(a) One vector.** `K := closure (M · ξ) ⊆ H`. `K` is `M`-invariant
  (`π(a)` continuous) and `M`-coinvariant (`π(a)* = π(a*) ∈ M`), so `K`
  *reduces* every `π(a)` ⇒ the orthogonal projection `P` onto `K` commutes
  with every `π(a)`, i.e. `P ∈ π(𝔄)'`. Unitality gives `ξ = π(1)ξ ∈ K`. For
  `T ∈ π(𝔄)'' = centralizer(centralizer(range π))`, `T` commutes with `P`, so
  `Tξ = TPξ = PTξ ∈ K = closure(Mξ)`: `Tξ` is a norm limit of `π(a)ξ`.
- **(b) Finitely many vectors `ξ₁,…,ξₙ`.** Amplify to `Hⁿ`,
  `πⁿ(a) = diag(π(a),…,π(a))`. Key fact: `T ∈ π(𝔄)'' ⇒ diag(T,…,T) ∈
  (πⁿ(𝔄))''`. Apply (a) to `(ξ₁,…,ξₙ) ∈ Hⁿ` and `πⁿ`: `π(a)` simultaneously
  approximates `Tξ₁,…,Tξₙ`.
- **(c) Conclude.** Strong topology's `0`-nbhd basis is indexed by (finite
  `S ⊆ H`, nbhd `V` of `0` in `H`): `{f | ∀x∈S, f x∈V}`
  (`PointwiseConvergenceCLM.hasBasis_nhds_zero`). Given `T ∈ π(𝔄)''` and a
  basic neighbourhood determined by finite `S`, (b) produces `a` with `π(a)`
  in it. So `T ∈ closure(range π)`.

## 2. What the repo already has

- `Physicslib4/Operators/LpDiagonal.lean` — **fully general**, no C*-algebra
  hypothesis: `lpDiag (T : ∀ i, E i →L[𝕜] E i) (hK : 0≤K) (hTK : ∀i,‖T i‖≤K) :
  lp E 2 →L[𝕜] lp E 2`, plus `lpDiag_apply_coe/_congr/_ext/_one/_mul/_add/
  _smul/_star`. Exactly the amplification machinery for step (b), and it
  needs no norm on the source algebra — `hTK` is discharged from the already
  existing CLM norms.
- `Physicslib4/GNS/DirectSum.lean` — wraps `lpDiag` into a `StarAlgHom`
  `directSum π : A →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2)` for a *family*
  `π i : A →⋆ₐ[ℂ] (H i →L[ℂ] H i)`, requiring `[CStarAlgebra A]` only to get
  `‖π i a‖ ≤ ‖a‖` across *different* `π i` (`NonUnitalStarAlgHom.norm_apply_le`).
  Also has `intertwines_single` and `summandProj_mem_commutant` (projection
  onto summand `j` lies in the commutant) — reusable verbatim.
- `Physicslib4/GNS/Amplification.lean` — `ι`-fold amplification of a single
  `π`, still under `[CStarAlgebra A]`; docstring flags that the full
  amplification commutant theorem `(π⊗1)'' = π''⊗ℂ1` is **not proved** and is
  "a genuine von Neumann algebra result Mathlib does not currently provide."

### The key adaptation

The target's `𝔄` has no norm, so `Amplification.amplification` can't be
instantiated. But a *finite* amplification of a single already-bounded `π`
needs no norm on `𝔄` at all: `lpDiag (fun _:Fin n => π a) (norm_nonneg (π a))
(fun _ => le_refl _)` — the bound is `‖π a‖` itself, uniform "for free" across
the `n` identical copies. So a `Fin n`-indexed sibling of
`DirectSum.directSumFun/directSum` can be built for the bare
`[Ring 𝔄] [StarRing 𝔄] [Algebra ℂ 𝔄] [StarModule ℂ 𝔄]` hypotheses already in
`StrongDensity.lean`, reusing `lpDiag`'s laws exactly as `directSum` does.
`intertwines_single`/`summandProj_mem_commutant` transfer verbatim (they use
no C*-structure of `A`). Whether to generalize the existing `def` or add a
sibling is for the orchestrator/prover (defs blocked for this agent).

**Still missing, the hard part of (b):** `T ∈ π(𝔄)'' ⇒ diag(T,…,T) ∈
(πⁿ(𝔄))''`. Strictly weaker than the full amplification-commutant theorem
flagged missing in `Amplification.lean`; only one containment, one direction,
for the diagonal element. Route, using `lp.hasSum_single` + linearity, no
matrix-isomorphism needed:

1. `S ∈ (πⁿ(𝔄))'`. Define `S_{jk} := lpEvalCLM j ∘L S ∘L
   (lp.singleContinuousLinearMap ℂ _ 2 k) : H →L[ℂ] H`. Commutation of `S`
   with `πⁿ(a)` gives `S_{jk} ∈ Set.centralizer (Set.range π)` for every
   `j,k` (unfold + `lpDiag_apply_coe`/`lp.single_apply`, as in
   `summandProj_mem_commutant`'s proof).
2. `x = ∑ k, lp.single 2 k (x k)` as a genuine `Fin n`-indexed finite sum —
   from `lp.hasSum_single : HasSum (fun i => lp.single 2 i (f i)) f`
   (`Mathlib/Analysis/InnerProductSpace/l2Space.lean:435`) bridged to
   `Finset.sum` via `hasSum_fintype`/`HasSum.unique` (confirm exact lemma
   when implementing).
3. `(diag(T) S x) j = T((Sx) j) = T(∑ₖ S_{jk}(x k)) = ∑ₖ T(S_{jk}(x k)) =
   ∑ₖ S_{jk}(T(x k))` (since `S_{jk} ∈ π(𝔄)'`, `T ∈ π(𝔄)''` commute)
   `= (S(diag(T) x)) j`. So `diag(T) S = S diag(T)` for arbitrary `S`, hence
   `diag(T) ∈ (πⁿ(𝔄))''`. Elementary (no spectral theory, no C*-norm
   estimates) but index-heavy: ~40–80 Lean lines across several small lemmas.

## 3. Mathlib API inventory

| Need | Status | Name / path |
|---|---|---|
| Strong operator topology | have | `PointwiseConvergenceCLM`, `Mathlib/Topology/Algebra/Module/Spaces/PointwiseConvergenceCLM.lean` |
| Nbhd basis at 0 | have | `PointwiseConvergenceCLM.hasBasis_nhds_zero`; general `UniformConvergenceCLM.hasBasis_nhds_zero(_of_basis)`, `.../UniformConvergenceCLM.lean:275-291` |
| Closure via nbhd basis | have | `mem_closure_iff_nhds_basis'`, `mem_closure_iff_nhds`, `Mathlib/Topology/ClusterPt.lean:298,309` |
| `Set.centralizer` basics | have | `Set.centralizer`, `Set.mem_centralizer_iff`, `Mathlib/Algebra/Group/Center.lean:125,159` (root-level, distinct from `Subsemigroup.centralizer`) |
| Diagonal operator on finite ℓ² sum | have, general | `Physicslib4.lpDiag` + laws, `Physicslib4/Operators/LpDiagonal.lean` |
| Finite ℓ² decomposition `x=∑single k (x k)` | have, as `HasSum` | `lp.hasSum_single`, `.../l2Space.lean:435`; needs bridge to `Finset.sum` for `Fintype` |
| Coordinate projection/inclusion on `lp` | have | `lpEvalCLM`, `lp.singleContinuousLinearMap`, `Physicslib4/GNS/DirectSum.lean` |
| **Reducing subspace ⇒ projection commutes with operator** | **MISSING** | grepped `Mathlib/Analysis/InnerProductSpace/{Projection/*,Adjoint,Spectrum,Symmetric,Positive,Reproducing}.lean`; only `IsSymmetric.restrict_invariant` found (gives a restriction *given* invariance, symmetric operators only) — nothing of the needed shape. |
| Full amplification commutant theorem | MISSING (already flagged in-repo) | `Physicslib4/GNS/Amplification.lean` docstring; not needed here, only the weaker diagonal fact above is |
| `VonNeumannAlgebra.commutant_commutant` | have, wrong shape | double-commutant *property* of an already-bundled vN algebra, not density; matches blueprint's own assessment |

## 4. Proof decomposition

New `def`s (item 4) must be added by the orchestrator/prover, not this agent.

1. **`reducing_subspace_commutes_projection`** (new, general, e.g.
   `Physicslib4/Operators/`): `K : Submodule ℂ H` closed, `T : H →L[ℂ] H`,
   `MapsTo T K K`, `MapsTo (adjoint T) K K` ⇒ `Commute T (K.starProjection :
   H →L[ℂ] H)`. ~10–15 lines (orthogonal decomposition `x=y+z`, `y∈K,z∈Kᗮ`,
   show `Tz∈Kᗮ` via `hK'` and inner-product characterization of `Kᗮ`). **The
   one truly novel operator-theory fact**; double-check with `lean_loogle`/
   `lean_leansearch` before writing from scratch (this pass was grep-only).
2. **`cyclic_subspace_reduces`**: `K := closure(range(π · ξ))` is invariant
   under every `π a` and `π a⋆`. ~5–10 lines (`map_star`, continuity,
   `closure_mono`).
3. **`mem_bicommutant_single_vector`** (step a): `T∈π(𝔄)'', ξ` ⇒
   `Tξ ∈ closure(range(π · ξ))`. Combine 1, 2, `π 1 = 1`. ~10 lines.
4. **Finite amplification** (`def`, orchestrator): `Fin n`-specialized
   sibling of `DirectSum.directSumFun/directSum` for bare `𝔄` (§2), bound via
   `norm_nonneg (π a)`/`le_refl _`.
5. **`diag_mem_bicommutant_amp`** (hard core of step b, §2 route): `T∈π(𝔄)''
   → lpDiag (fun _:Fin n => T) … ∈ centralizer(centralizer(range(finiteAmp π
   n)))`. ~30–50 lines: `S_{jk}` extraction, `lp.hasSum_single`→`Finset.sum`
   bridge, commuting-sum computation.
6. **`mem_bicommutant_finite_vectors`** (step b conclusion): apply 3 to
   `finiteAmp π n` and the tuple `(ξ 0,…,ξ(n-1)) : lp(Fin n→H) 2` (check the
   cleanest tuple-construction API for `lp` over `Fin n`). ~15–20 lines.
7. **`dense_range_in_bicommutant`** (target, step c): unfold `ofFun` (identity
   up to coercion), `mem_closure_iff_nhds_basis' PointwiseConvergenceCLM.hasBasis_nhds_zero`
   — note that basis is centred at `0`, not at `T`; a translation argument or
   a nbhd-at-a-point version may be needed, recheck when implementing — then
   apply 6 with the finite set from the neighbourhood. ~10–15 lines.

**Total estimate:** ~130–200 lines across ~7 lemmas; lemma 1 and lemma 5
carry the real mathematical content; 4 is a new `def`; the rest is glue.

## 5. Recommendation and risks

Proceed via §4's order: 1–2 are independent, generally useful
operator-theory lemmas, attempt first; request the `def` (item 4) from the
orchestrator early since 5–7 depend on it. If time runs out, land 1–3 (single
vector case) as reusable building blocks with the target left `sorry` —
**do not narrow the target statement** to the single-vector case.

Risks:
- Lemma 1 not found in Mathlib under any name this grep pass tried, though
  `CompleteSpace H` (already in context) makes `adjoint`/`starProjection`
  available; a differently-phrased version (via `IsIdempotentElem`/
  `IsSelfAdjoint`/`ker`/`range`) might exist — worth a live `lean_loogle`/
  `leansearch` check before implementing from scratch (not run this pass).
- The `Fin n`/`lp` route needs a new `def` (blocked for this agent); an
  alternative is generalizing `DirectSum.directSumFun`'s hypothesis from
  `[CStarAlgebra A]` to an explicit bound `(hb : ∀ i, ‖π i a‖ ≤ K a)` — a
  strictly more general replacement, not a narrowing, but it touches an
  existing declaration's signature, so it's the orchestrator's call.
- Confirm the exact `lp.hasSum_single` → `Finset.sum` bridging lemma name for
  `Fin n` when implementing (only located `lp.hasSum_single` itself here).
- No evidence the target is mis-specified: it matches Murphy 4.1.4 exactly,
  and the blueprint's own proof sketch confirms this is the intended route.
