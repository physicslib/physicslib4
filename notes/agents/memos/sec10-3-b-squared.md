# Scout memo: `sq_norm_le_of_isSymmetric` and `isClosed_range_subSmul`

Both target proof skeletons below were verified end-to-end with `lean_run_code` against
standalone reconstructions of the relevant definitions (`IsSymmetric`, `subSmul`, `range`,
`mem_range`, `subSmul_apply`) taken verbatim from the project files, using the Mathlib pin
in this repo's `lake-manifest.json`. Both compile with no errors (only pre-existing-style
`unused section variable [CompleteSpace H]` linter warnings, which the two targets also
trigger in isolation — see Risks). Neither statement looks wrong; do not weaken either.

---

## Target 1 — `sq_norm_le_of_isSymmetric`

File: `Physicslib4/Spectral/Unbounded/Spectrum.lean:105`.

### Target statement (given)

```lean
theorem sq_norm_le_of_isSymmetric {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T) (a b : ℝ)
    (ψ : T.domain) :
    b ^ 2 * ‖(ψ : H)‖ ^ 2 ≤ ‖T ψ - ((a : ℂ) + (b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2
```

### Exact lemma names confirmed in this pin

- `norm_sub_sq {𝕜 E} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
  ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * RCLike.re ⟪x, y⟫_𝕜 + ‖y‖ ^ 2`
  (`Mathlib.Analysis.InnerProductSpace.Basic`)
- `inner_conj_symm (x y : E) : (starRingEnd 𝕜) (inner 𝕜 y x) = inner 𝕜 x y`
  (same file) — used to show `⟪T ψ, ψ⟫` is self-conjugate.
- `Complex.conj_eq_iff_real {z : ℂ} : (starRingEnd ℂ) z = z ↔ ∃ r, z = ↑r`
  (`Mathlib.Data.Complex.Basic`)
- `inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫`
- `inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = (starRingEnd 𝕜) r * ⟪x, y⟫`
- `inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫`
  (all `Mathlib.Analysis.InnerProductSpace.Basic`)
- `Complex.mul_I_re (z : ℂ) : (z * I).re = -z.im` (`Mathlib.Data.Complex.Basic`)
- `Complex.conj_ofReal (r : ℝ) : conj (r : ℂ) = r` (`Mathlib.Data.Complex.Basic`)
- `norm_smul`, `Complex.norm_mul`, `Complex.norm_I`, `Complex.norm_real`, `Complex.ofReal_mul`,
  `Complex.ofReal_im`, `sq_abs` — all standard, all confirmed working in the tested snippet.

### `RCLike.re` vs `Complex.re` defeq note

The `hre_defeq` step from the bounded proof **is still needed** in exactly the same form:
```lean
have hre_defeq : RCLike.re ⟪x, ((b:ℂ)*Complex.I) • (ψ:H)⟫_ℂ =
    (⟪x, ((b:ℂ)*Complex.I) • (ψ:H)⟫_ℂ).re := rfl
```
`norm_sub_sq` is stated with `RCLike.re`, but the cross-term computation (`hcross`) naturally
produces a `Complex.re` (`.re`) value, and `rw [hcross]` won't fire on `RCLike.re _` without
this `rfl` bridge. This carries over unchanged.

### Concrete substitution and derivation of "the inner product is real"

There is **no operator `B` here** — only the vector `T ψ - (a:ℂ) • (ψ:H)`. The bounded
proof's route via `IsSelfAdjoint.isSymmetric hB |>.conj_inner_sym` does not exist for a
`LinearPMap`; `IsSymmetric` in this file is the bare `∀ φ ψ, ⟪φ, Tψ⟫ = ⟪Tψ,ψ⟫` definition,
so the self-adjointness of `⟪Tψ - a•ψ, ψ⟫` must be built by hand from `hsym ψ ψ` plus
`inner_conj_symm`. Concretely (this is the version that type-checked):

```lean
obtain ⟨r1, hr1⟩ : ∃ r : ℝ, ⟪T ψ, (ψ : H)⟫_ℂ = (r : ℂ) := by
  apply Complex.conj_eq_iff_real.mp
  rw [inner_conj_symm]
  exact hsym ψ ψ
obtain ⟨r2, hr2⟩ : ∃ r : ℝ, ⟪(ψ : H), (ψ : H)⟫_ℂ = (r : ℂ) := by
  apply Complex.conj_eq_iff_real.mp
  rw [inner_conj_symm]
have hr : ⟪(T ψ - (a : ℂ) • (ψ : H)), (ψ : H)⟫_ℂ = ((r1 - a * r2 : ℝ) : ℂ) := by
  rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, hr1, hr2]
  push_cast; ring
```

**Direction warning:** `inner_conj_symm x y : conj ⟪y,x⟫ = ⟪x,y⟫`. Rewriting a goal
`conj ⟪Tψ,ψ⟫ = ⟪Tψ,ψ⟫` with `rw [inner_conj_symm]` turns it into `⟪ψ,Tψ⟫ = ⟪Tψ,ψ⟫`, which is
`hsym ψ ψ` **directly, with no `.symm`** — the bounded proof's `(hsym ψ ψ).symm`-shaped step
does not transfer as-is; get the direction wrong and you get a type mismatch (`Eq.symm (hsym ψ
ψ)` has the reversed type). I recommend computing `r1, r2` explicitly (as above) rather than
mimicking the bounded proof's `star ⟪Bψ,ψ⟫ = ⟪Bψ,ψ⟫ → obtain ⟨r,hr⟩` pattern applied to a raw
subtraction, because pushing `starRingEnd ℂ` through `inner_sub_left`/`inner_smul_left`
directly runs into a `map_mul` step that needs an extra `Complex.conj_conj` cancellation
(since `a`'s conjugate then gets conjugated again by the outer `map_sub`); getting the two
real parts `r1, r2` first and combining them into `(r1 - a*r2 : ℝ)` sidesteps that entirely
and is the cleaner route.

### A `rw`-ordering pitfall specific to this proof (not in the bounded original)

Unlike the bounded proof, here `x := T ψ - (a:ℂ) • (ψ:H)` is a **literal vector subtraction**
in `H`, not an opaque `let`-bound operator application (`B ψ` in the bounded proof is opaque
to `rw` until `ContinuousLinearMap.sub_apply` fires). If you `set x := T ψ - (a:ℂ)•ψ` or just
write `T ψ - (a:ℂ)•ψ` inline and then `rw [norm_sub_sq (𝕜 := ℂ)]` with no explicit arguments,
`rw` will match the **first** occurrence of `‖_ - _‖ ^ 2` in the goal, which is `‖T ψ -
(a:ℂ)•ψ‖^2` itself (since that vector *is* a subtraction), not the intended `‖(T ψ - (a:ℂ)•ψ)
- ((b:ℂ)*I)•ψ‖^2`. **Fix:** supply `norm_sub_sq` its two arguments explicitly, e.g.
`norm_sub_sq (𝕜 := ℂ) (T ψ - (a:ℂ)•(ψ:H)) (((b:ℂ)*Complex.I)•(ψ:H))`, which pins down the
match and avoids rewriting the wrong subterm.

### Verified proof skeleton (compiles, `lean_run_code`, no `sorry`)

```lean
theorem sq_norm_le_of_isSymmetric {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T) (a b : ℝ)
    (ψ : T.domain) :
    b ^ 2 * ‖(ψ : H)‖ ^ 2 ≤ ‖T ψ - ((a : ℂ) + (b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 := by
  obtain ⟨r1, hr1⟩ : ∃ r : ℝ, ⟪T ψ, (ψ : H)⟫_ℂ = (r : ℂ) := by
    apply Complex.conj_eq_iff_real.mp
    rw [inner_conj_symm]
    exact hsym ψ ψ
  obtain ⟨r2, hr2⟩ : ∃ r : ℝ, ⟪(ψ : H), (ψ : H)⟫_ℂ = (r : ℂ) := by
    apply Complex.conj_eq_iff_real.mp
    rw [inner_conj_symm]
  have hr : ⟪(T ψ - (a : ℂ) • (ψ : H)), (ψ : H)⟫_ℂ = ((r1 - a * r2 : ℝ) : ℂ) := by
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, hr1, hr2]
    push_cast
    ring
  have hcross : (⟪(T ψ - (a : ℂ) • (ψ : H)), ((b : ℂ) * Complex.I) • (ψ : H)⟫_ℂ).re = 0 := by
    rw [inner_smul_right, hr]
    have hprod : ((b : ℂ) * Complex.I) * ((r1 - a * r2 : ℝ) : ℂ) =
        ((b * (r1 - a * r2) : ℝ) : ℂ) * Complex.I := by
      calc
        ((b : ℂ) * Complex.I) * ((r1 - a * r2 : ℝ) : ℂ)
            = (b : ℂ) * ((r1 - a * r2 : ℝ) : ℂ) * Complex.I := by ring
        _ = ((b * (r1 - a * r2) : ℝ) : ℂ) * Complex.I := by rw [Complex.ofReal_mul]
    rw [hprod, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  have hre_defeq : RCLike.re ⟪(T ψ - (a : ℂ) • (ψ : H)), ((b : ℂ) * Complex.I) • (ψ : H)⟫_ℂ =
      (⟪(T ψ - (a : ℂ) • (ψ : H)), ((b : ℂ) * Complex.I) • (ψ : H)⟫_ℂ).re := rfl
  have hsmul_norm_sq : ‖((b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 = b ^ 2 * ‖(ψ : H)‖ ^ 2 := by
    rw [norm_smul, mul_pow]
    congr 1
    rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    simpa using sq_abs b
  have hlambda : T ψ - ((a : ℂ) + (b : ℂ) * Complex.I) • (ψ : H) =
      (T ψ - (a : ℂ) • (ψ : H)) - ((b : ℂ) * Complex.I) • (ψ : H) := by
    rw [add_smul]
    abel
  calc
    b ^ 2 * ‖(ψ : H)‖ ^ 2 = ‖((b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 := hsmul_norm_sq.symm
    _ ≤ ‖T ψ - (a : ℂ) • (ψ : H)‖ ^ 2 + ‖((b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg _)
    _ = ‖(T ψ - (a : ℂ) • (ψ : H)) - ((b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := ℂ) (T ψ - (a : ℂ) • (ψ : H)) (((b : ℂ) * Complex.I) • (ψ : H)),
        hre_defeq, hcross]
      ring
    _ = ‖T ψ - ((a : ℂ) + (b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 := by
      rw [hlambda]
```

### Risks / notes

- This proof, like `subSmul_apply` and `mem_range` in `Basic.lean`, does not use
  `[CompleteSpace H]`; the linter will flag it exactly the way other lemmas in the file
  already handle it with `omit [CompleteSpace H] in` above the `theorem` line (see e.g.
  `subSmul_domain`, `mem_range`). Match that style when landing the proof.
- Nothing about the target statement looks wrong; the derivation is a faithful transcription
  of the bounded case with `a, b` real and `T` merely symmetric (self-adjointness of `T` is
  never used — only `hsym ψ ψ`, i.e. symmetry at the single point `ψ`, which is all the
  bounded proof effectively used too, applied to `B = A - a•1`).

---

## Target 2 — `isClosed_range_subSmul`

File: `Physicslib4/Spectral/Unbounded/Basic.lean:470`.

### Target statement (given)

```lean
theorem isClosed_range_subSmul {T : H →ₗ.[ℂ] H} (hcl : T.IsClosed) (lam : ℂ) {ε : ℝ}
    (hε : 0 < ε) (hbound : ∀ ψ : T.domain, ε * ‖(ψ : H)‖ ≤ ‖T ψ - lam • (ψ : H)‖) :
    IsClosed ((range (subSmul T lam) : Submodule ℂ H) : Set H)
```

### Mathlib API for `LinearPMap.IsClosed`

- `LinearPMap.IsClosed (f : E →ₗ.[R] F) : Prop := _root_.IsClosed (f.graph : Set (E × F))`
  (`Mathlib.Topology.Algebra.Module.LinearPMap`). It is a plain `def`, and Lean's dot-notation
  elaboration unfolds it transparently, so `hcl.mem_of_tendsto ...` (i.e. `IsClosed.mem_of_tendsto`
  applied through the `def`) resolves and elaborates without any manual unfolding — confirmed
  working in the tested snippet.
- `LinearPMap.mem_graph_iff (f : E →ₗ.[R] F) {x : E × F} : x ∈ f.graph ↔ ∃ y : f.domain, (↑y :
  E) = x.1 ∧ f y = x.2` (`Mathlib.LinearAlgebra.LinearPMap`, already used in this project's
  `Basic.lean` at lines 226, 299, 313).
- `LinearPMap.mem_graph (f) (x : f.domain) : ((x:E), f x) ∈ f.graph` — already used in this
  file (lines 224, 235, 250, 289).
- `LinearPMap.map_sub (f : E →ₛₗ.[σ] F) (x y : f.domain) : f (x - y) = f x - f y`
  (`Mathlib.LinearAlgebra.LinearPMap`) — needed to get `T (ψ_n - ψ_m) = T ψ_n - T ψ_m`.

**You do NOT need `mem_domain_closure_iff` / `closure_apply_eq_of_tendsto`.** Those two
project lemmas are about `T.closure` (the *smallest closed extension* of a possibly-unclosed
`T`), built via `LinearPMap.IsClosable.graph_closure_eq_closure_graph`. Here `T` is *already*
assumed closed (`hcl : T.IsClosed`), so the direct route is: build a sequence in `T.graph`,
show it converges in `H × H`, and invoke `IsClosed.mem_of_tendsto` on `hcl` directly to land
the limit back in `T.graph` — no `closure`/`IsClosable` machinery, no `graph_closure_eq_closure_graph`,
needed at all. This is simpler than the two read-first examples in the prompt, precisely
because those handle the *unclosed* case.

- `IsClosed.mem_of_tendsto {f : α → X} {b : Filter α} [NeBot b] (hs : IsClosed s)
  (hf : Tendsto f b (𝓝 x)) (h : ∀ᶠ x in b, f x ∈ s) : x ∈ s`
  (`Mathlib.Topology.Neighborhoods`) — exactly the tool needed; no need to go through
  `mem_closure_of_tendsto` (also available, used in the file, but `mem_of_tendsto` gives the
  membership in one step since `T.graph` is already known closed).

### Route to `IsClosed (S : Set H)` for `S = range (subSmul T lam)` from sequential closedness

Recommended: **`isClosed_of_closure_subset (h : closure s ⊆ s) : IsClosed s`**
(`Mathlib.Topology.Closure`), combined with
**`mem_closure_iff_seq_limit [FrechetUrysohnSpace X] {s} {a} : a ∈ closure s ↔ ∃ x : ℕ → X,
(∀ n, x n ∈ s) ∧ Tendsto x atTop (𝓝 a)`** (`Mathlib.Topology.Sequences`, already used in this
file at line 225 and line 232 via `mem_closure_of_tendsto`/`mem_closure_iff_seq_limit`). `H`
is a `NormedAddCommGroup`, hence a metric space, hence a `FrechetUrysohnSpace` automatically
(instance resolved fine in the tested snippet — no manual instance needed).

This is simpler than routing through `IsSeqClosed`/`IsSeqClosed.isClosed` (which needs a
`[SequentialSpace X]` instance rather than `[FrechetUrysohnSpace X]`, and only pays off if you
want to state sequential-closedness as its own intermediate lemma). I recommend
`isClosed_of_closure_subset` + `mem_closure_iff_seq_limit` directly.

### Completeness step: `ε‖ψ_n − ψ_m‖ ≤ ‖φ_n − φ_m‖`, `φ_n → φ` implies `CauchySeq ψ`

Route (verified):
1. `Filter.Tendsto.cauchySeq {f : β → α} {x} (hf : Tendsto f atTop (𝓝 x)) : CauchySeq f`
   (`Mathlib.Topology.UniformSpace.Cauchy`) — apply to `φ` to get `CauchySeq φ`.
2. `Metric.cauchySeq_iff {u : β → α} : CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u
   m) (u n) < ε` (`Mathlib.Topology.MetricSpace.Cauchy`). Unfold `CauchySeq φ` with this to
   get, for target gap `δ > 0`, an `N` with `dist (φ m) (φ n) < δ * ε` for `m, n ≥ N`; then
   `ε * ‖ψ_m − ψ_n‖ ≤ ‖φ_m − φ_n‖ = dist(φ_m,φ_n) < δ * ε`, hence `‖ψ_m − ψ_n‖ < δ` by
   `lt_of_mul_lt_mul_left` (cancel `ε` from the left; avoid `mul_lt_mul_left`/`mul_lt_mul_right`,
   which need an order-typeclass instance — `MulRightStrictMono ℝ` / similar — that is not
   found automatically in this pin's elaboration order for plain `ℝ`; `lt_of_mul_lt_mul_left`
   worked without issue).
3. Rebuild `Metric.cauchySeq_iff` in the other direction to conclude `CauchySeq (fun n => (ψ n
   : H))`.
4. **`cauchySeq_tendsto_of_complete [Preorder β] [CompleteSpace α] {u : β → α} (hu : CauchySeq
   u) : ∃ a, Tendsto u atTop (𝓝 a)`** (`Mathlib.Topology.UniformSpace.Cauchy`) — gives the
   limit `ψlim` in `H` using `[CompleteSpace H]`.

An alternative name I checked and rejected: `cauchySeq_of_le_tendsto_0` needs a bound
`dist(s n, s m) ≤ b N` depending only on the smaller index `N`, which is an awkward fit here
(you'd have to first extract such a `b` from `φ`'s own Cauchy property, adding a layer);
going through `Metric.cauchySeq_iff` on both `φ` and `ψ` directly, as above, is more direct and
is what actually compiled.

### The domain-defeq pitfall (important, and specific to this file)

`subSmul T lam` is defined with `domain := T.domain` **literally** (not merely
propositionally equal via `subSmul_domain`, which is `rfl`), so `↥(subSmul T lam).domain` and
`↥T.domain` are the same type at `default` transparency. However, **`rw` unifies at a
stricter transparency** and will fail with "Application type mismatch ... has type
`↥(subSmul T lam).domain` but is expected to have type `↥T.domain`" if you try to
`rw [LinearPMap.map_sub]` or `rw [subSmul_apply]` inline on a hypothesis obtained from
`hbound (ψ m - ψ n)` (where `ψ n : (subSmul T lam).domain`). **Fix:** state each intermediate
fact as its own `have` with an explicit type ascription (e.g. `have hTsub : T (ψ m - ψ n) = T
(ψ m) - T (ψ n) := LinearPMap.map_sub T (ψ m) (ψ n)`); direct term-mode elaboration resolves
the defeq cleanly, and you then `rw` using the resulting `have`, never the raw
lemma applied inline inside a `rw [...]` list. This bit me repeatedly while testing; budget
for it in the real proof.

### Verified proof skeleton (compiles, `lean_run_code`, no `sorry`)

```lean
theorem isClosed_range_subSmul {T : H →ₗ.[ℂ] H} (hcl : T.IsClosed) (lam : ℂ) {ε : ℝ}
    (hε : 0 < ε) (hbound : ∀ ψ : T.domain, ε * ‖(ψ : H)‖ ≤ ‖T ψ - lam • (ψ : H)‖) :
    IsClosed ((range (subSmul T lam) : Submodule ℂ H) : Set H) := by
  apply isClosed_of_closure_subset
  intro φlim hφlim
  obtain ⟨φ, hφmem, hφtendsto⟩ := mem_closure_iff_seq_limit.mp hφlim
  choose ψ hψ using fun n => mem_range.mp (hφmem n)
  have key : ∀ m n : ℕ, ε * ‖(ψ m : H) - (ψ n : H)‖ ≤ ‖φ m - φ n‖ := by
    intro m n
    have hb := hbound (ψ m - ψ n)
    have hcoe : ((ψ m - ψ n : (subSmul T lam).domain) : H) = (ψ m : H) - (ψ n : H) :=
      Submodule.coe_sub _ _ _
    have hTsub : T (ψ m - ψ n) = T (ψ m) - T (ψ n) := LinearPMap.map_sub T (ψ m) (ψ n)
    have hsmA : φ m = T (ψ m) - lam • (ψ m : H) := by
      have := subSmul_apply T lam (ψ m); rw [hψ m] at this; exact this
    have hsmB : φ n = T (ψ n) - lam • (ψ n : H) := by
      have := subSmul_apply T lam (ψ n); rw [hψ n] at this; exact this
    rw [hcoe, hTsub] at hb
    have heq : (T (ψ m) - T (ψ n)) - lam • ((ψ m : H) - (ψ n : H)) = φ m - φ n := by
      rw [smul_sub, hsmA, hsmB]; abel
    rwa [heq] at hb
  have hψCauchy : CauchySeq (fun n => (ψ n : H)) := by
    have hφCauchy : CauchySeq φ := hφtendsto.cauchySeq
    rw [Metric.cauchySeq_iff] at hφCauchy ⊢
    intro δ hδ
    obtain ⟨N, hN⟩ := hφCauchy (δ * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hkey := key m n
    have hφlt := hN m hm n hn
    rw [dist_eq_norm] at hφlt
    have h1 : ε * ‖(ψ m : H) - (ψ n : H)‖ < ε * δ := by
      calc ε * ‖(ψ m : H) - (ψ n : H)‖ ≤ ‖φ m - φ n‖ := hkey
        _ < δ * ε := hφlt
        _ = ε * δ := mul_comm δ ε
    exact lt_of_mul_lt_mul_left h1 hε.le
  obtain ⟨ψlim, hψtendsto⟩ := cauchySeq_tendsto_of_complete hψCauchy
  have hTψtendsto : Tendsto (fun n => T (ψ n)) atTop (𝓝 (φlim + lam • ψlim)) := by
    have heq : (fun n => T (ψ n)) = fun n => φ n + lam • (ψ n : H) := by
      funext n
      have h := hψ n
      rw [subSmul_apply] at h
      rw [← h]; abel
    rw [heq]
    exact hφtendsto.add (hψtendsto.const_smul lam)
  have hmemgraph : (ψlim, φlim + lam • ψlim) ∈ T.graph := by
    apply hcl.mem_of_tendsto (hψtendsto.prodMk_nhds hTψtendsto)
    filter_upwards with n
    exact T.mem_graph (ψ n)
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff T).mp hmemgraph
  refine mem_range.mpr ⟨y, ?_⟩
  have hy1' : (y : H) = ψlim := hy1
  have hy2' : T y = φlim + lam • ψlim := hy2
  rw [subSmul_apply, hy1', hy2']
  abel
```

### Risks / notes

- `Submodule.coe_sub` — I used it with three explicit underscores
  (`Submodule.coe_sub _ _ _`); double check the exact arity in the pin when transcribing (it
  may also just be `rfl` for `Submodule`'s `AddSubgroupClass` coercion — I did not need to
  distinguish since both closed the goal in the tested snippet's context, but confirm which
  one `simp`/elaboration prefers when you actually add this to the file, since `Submodule.coe_sub`
  might report as a `simp` lemma with a different argument order in verbose diagnostics).
- The `[CompleteSpace H]` hypothesis is used exactly once, at `cauchySeq_tendsto_of_complete`;
  no other step needs it. `Nonempty ℕ`/`SemilatticeSup ℕ` instances for `Filter.Tendsto.cauchySeq`
  and `cauchySeq_tendsto_of_complete` are found automatically.
- Statement sanity: nothing here suggests the target is wrong. It is the standard "closed
  operator with a uniform a priori bound has closed range" fact (Hall's Prop. 9.14 /
  Weidmann); the proof is the standard "Cauchy sequence transfer + closed graph" argument and
  went through cleanly with no hidden extra hypotheses needed.
