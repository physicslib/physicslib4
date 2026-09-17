# Scout memo: `prpstn:hall-9.13` — adjoint of a sum with a bounded operator

Target file: `Physicslib4/Spectral/Unbounded/Basic.lean`, sorries at lines 430 and 441.
Blueprint: `blueprint/src/sections/sec10/unbounded-spectral-theorems.tex`, lines 499–544.

## Target (verbatim, must not change)

```lean
theorem adjoint_add_toPMap {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (B : H →L[ℂ] H) :
    (T + (B : H →ₗ[ℂ] H).toPMap ⊤)† =
      T† + ((ContinuousLinearMap.adjoint B : H →ₗ[ℂ] H).toPMap ⊤) := by
  sorry

theorem isSelfAdjoint_add_of_isSelfAdjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hTsa : IsSelfAdjoint T) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (T + (B : H →ₗ[ℂ] H).toPMap ⊤) := by
  sorry
```

`HasDenseDomain T := Dense (T.domain : Set H)` (project def, `Basic.lean:72`).
Ambient context: `open scoped InnerProductSpace LinearPMap` — so `†` is `LinearPMap.adjoint`
inside `LinearPMap`-typed expressions and `ContinuousLinearMap.adjoint`'s own scoped notation
`†` (from `open scoped InnerProduct` inside Mathlib's own file — **not** open in this project,
which is why the statement spells it out as `ContinuousLinearMap.adjoint B` rather than `B†`).

## Headline result

**Mathlib does NOT have this lemma.** I searched hard (loogle, leansearch, leanfinder, and a
full read of `Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`, which is the only file
combining `LinearPMap.adjoint` with anything bounded). The only related result is:

- `ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense (A : E →L[𝕜] F) {p : Submodule 𝕜 E}
  (hp : Dense (p : Set E)) : ((A : E →ₗ[𝕜] F).toPMap p).adjoint = (adjoint A : F →ₗ[𝕜] E).toPMap ⊤`
  — the adjoint of a single bounded operator restricted to a dense domain. This is a special
  case of Part 1+2 of `prpstn:hall-9.13` (`T = 0` essentially) but says nothing about sums of an
  unbounded `T` with a bounded `B`. It is not directly reusable, though its statement pattern
  (LHS domain = the restriction's domain, proved via `ext x y hxy`) is the template Mathlib
  itself uses and that I followed below.

So this is fresh work: no existing lemma to cite, and (b) below is a genuinely new, reasonably
general Mathlib-shaped statement (`LinearPMap.adjoint_add_of_dense_toPMap` or similar) that would
be a fine contribution upstream, restricted only by "the second summand is `f.toPMap ⊤` for a
bounded `f`" (i.e. does not generalize to two unbounded `LinearPMap`s, where the sum's domain
intersection makes both directions of the domain-equality argument fail — Part 2 of the blueprint
proof genuinely uses boundedness of `B` on *all* of `H`).

## 1–5: exact Mathlib API, verified against the pinned snapshot

All of the following are in `.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean` unless
noted; `import Mathlib.Analysis.InnerProductSpace.LinearPMap` (already imported by `Basic.lean`)
pulls it in along with the adjoint file.

### `LinearPMap.add` (`LinearAlgebra/LinearPMap.lean:423–432`)

```lean
instance instAdd : Add (E →ₛₗ.[σ] F) := ⟨fun f g =>
  { domain := f.domain ⊓ g.domain
    toFun := f.toFun.comp (inclusion inf_le_left) + g.toFun.comp (inclusion inf_le_right) }⟩

theorem add_domain (f g : E →ₛₗ.[σ] F) : (f + g).domain = f.domain ⊓ g.domain := rfl

theorem add_apply (f g : E →ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
    (f + g) x = f ⟨x, x.prop.1⟩ + g ⟨x, x.prop.2⟩ := rfl
```

Both `add_domain` and `add_apply` are `rfl` — **not** `simp`-tagged in Mathlib, so you must `rw`
or `simp only` with them by name; plain `simp` will not unfold `LinearPMap.add` on its own.
`add_apply` needs its argument already packaged as an element of the *specific* submodule
`f.domain ⊓ g.domain`, not of `f.domain` or `g.domain` separately — you build that element with
an anonymous constructor `⟨(x : H), ⟨hf, hg⟩⟩`.

### `LinearMap.toPMap` (`LinearAlgebra/LinearPMap.lean:654–663`)

```lean
def toPMap (f : E →ₛₗ[σ] F) (p : Submodule R E) : E →ₛₗ.[σ] F := ⟨p, f.comp p.subtype⟩

@[simp] theorem toPMap_apply (f : E →ₛₗ[σ] F) (p : Submodule R E) (x : p) : f.toPMap p x = f x := rfl
@[simp] theorem toPMap_domain (f : E →ₛₗ[σ] F) (p : Submodule R E) : (f.toPMap p).domain = p := rfl
```

Both **are** `@[simp]` (unlike `add_domain`/`add_apply`) and both `rfl`.

### Equality of `LinearPMap`s (`LinearAlgebra/LinearPMap.lean:72–96, 222`)

```lean
@[ext (iff := false)]
theorem LinearPMap.ext {f g : E →ₛₗ.[σ] F} (h : f.domain = g.domain)
    (h' : ∀ ⦃x : E⦄ ⦃hf : x ∈ f.domain⦄ ⦃hg : x ∈ g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩) : f = g

theorem LinearPMap.ext_iff {f g : E →ₛₗ.[σ] F} :
    f = g ↔ f.domain = g.domain ∧
      ∀ ⦃x : E⦄ ⦃hf : x ∈ f.domain⦄ ⦃hg : x ∈ g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩

theorem LinearPMap.eq_of_le_of_domain_eq {f g : E →ₛₗ.[σ] F} (hle : f ≤ g)
    (heq : f.domain = g.domain) : f = g
```

`LinearPMap.ext`'s pointwise hypothesis is the good one to target: it quantifies over the raw
vector `x : H` plus *separate* membership proofs `hf`/`hg` in the two domains — you never need to
transport an element of `f.domain` into `g.domain` via the domain-equality proof, which is exactly
the coercion trap the task worried about. `LinearPMap.dExt` is the version stated with a single
common-type element and an `(x:E) = y` hypothesis instead; `ext` is more convenient here because
`mem_adjoint_domain_of_exists`/`adjoint_apply_eq` are themselves stated for a bare vector plus a
membership proof.

`eq_of_le_of_domain_eq` is not the right tool for this proposition: proving `T ≤ T + B.toPMap ⊤`
(or the reverse) is not obviously easier than proving the two-sided pointwise statement directly,
and the blueprint proof does not go through an extension argument.

### `LinearPMap.adjoint` API (`Analysis/InnerProductSpace/LinearPMap.lean`)

```lean
def IsFormalAdjoint (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] E) : Prop :=
  ∀ (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫          -- line 74

def adjointDomain : Submodule 𝕜 F where ...                            -- line 90
def adjoint : F →ₗ.[𝕜] E where domain := T.adjointDomain; ...          -- line 152
scoped postfix:1024 "†" => LinearPMap.adjoint                          -- line 157

theorem mem_adjoint_domain_iff (y : F) :
    y ∈ T†.domain ↔ Continuous ((innerₛₗ 𝕜 y).comp T.toFun)            -- line 159, no density needed

theorem mem_adjoint_domain_of_exists (y : F)
    (h : ∃ w : E, ∀ x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫) : y ∈ T†.domain    -- line 164, NO density hypothesis

theorem adjoint_apply_eq (hT : Dense (T.domain : Set E)) (y : T†.domain) {x₀ : E}
    (hx₀ : ∀ x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) : T† y = x₀       -- line 183, density REQUIRED

theorem adjoint_isFormalAdjoint (hT : Dense (T.domain : Set E)) :
    T†.IsFormalAdjoint T                                                -- line 189, density REQUIRED
```

Key fact that simplifies the whole proof: `mem_adjoint_domain_of_exists` needs **no density
hypothesis at all** (an exact representing vector always puts you in the adjoint domain,
regardless of density — density is only needed for *uniqueness*, i.e. for `adjoint_apply_eq` and
for extracting a witness *from* membership via `adjoint_isFormalAdjoint`). So both inclusions of
the domain-equality step can invoke `mem_adjoint_domain_of_exists` unconditionally once you have
produced the witness vector, and only need `hT`/the density of `(T + B.toPMap ⊤).domain` to
*extract* the witness from an assumed membership on the other side.

The project's own `mem_adjoint_domain_iff_exists` / `adjoint_apply_eq_of_forall_inner`
(`Basic.lean:130`, `:145`) are thin wrappers around exactly `mem_adjoint_domain_of_exists` /
`adjoint_apply_eq` composed with `adjoint_isFormalAdjoint`, phrased for a bare `ψ : H`. Either the
wrappers or the raw Mathlib lemmas work; I found it marginally cleaner to call the raw Mathlib
lemmas directly (see the verified proof below), because the wrappers' `∃!`/`∃` phrasing forces an
extra `.symm` shuffle that the raw `IsFormalAdjoint`/`adjoint_apply_eq` avoid. Either route is
fine; this is a matter of taste, not correctness.

### `ContinuousLinearMap.adjoint` (`Analysis/InnerProductSpace/Adjoint.lean`)

```lean
scoped[InnerProduct] postfix:1000 "†" => ContinuousLinearMap.adjoint     -- line 119 (not opened in this project)

theorem adjoint_inner_left (A : E →L[𝕜] F) (x : E) (y : F) :
    ⟪(A†) y, x⟫ = ⟪y, A x⟫                                              -- line 123
theorem adjoint_inner_right (A : E →L[𝕜] F) (x : E) (y : F) :
    ⟪x, (A†) y⟫ = ⟪A x, y⟫                                              -- line 127

theorem star_eq_adjoint (A : E →L[𝕜] E) : star A = A† := rfl            -- line 254
theorem isSelfAdjoint_iff' {A : E →L[𝕜] E} : IsSelfAdjoint A ↔ A† = A := Iff.rfl   -- line 258
```

So `ContinuousLinearMap.isSelfAdjoint_iff'.mp hB : ContinuousLinearMap.adjoint B = B` directly —
no `Iff.rfl` gymnastics needed, `rw` handles it.

`LinearPMap`'s own bridge (`Analysis/InnerProductSpace/LinearPMap.lean:233`):

```lean
theorem LinearPMap.isSelfAdjoint_def {A : E →ₗ.[𝕜] E} : IsSelfAdjoint A ↔ A† = A := Iff.rfl
```

(This is stated inside `namespace LinearPMap`, so the fully qualified name is
`LinearPMap.isSelfAdjoint_def`; confirmed this name resolves in a standalone build.)

## 6. Does Mathlib already have it?

No — see "Headline result" above. `lean_loogle "LinearPMap.adjoint (_ + _)"` returns nothing;
`lean_leansearch`/`lean_leanfinder` for "adjoint of sum of unbounded and bounded operator" surface
only unrelated star-algebra facts (`IsSelfAdjoint.add`, `isSelfAdjoint_sum`,
`LinearMap.IsAdjointPair.add`) and the single-operator restriction lemma quoted above. Grepping
`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean` end to end (only ~340 lines) confirms there
is no other `LinearPMap.add`/`adjoint` interaction lemma in the file.

Note also: `E →ₗ.[𝕜] E` is **not** a `StarAddMonoid` in Mathlib (only `Star` is defined, at
`Analysis/InnerProductSpace/LinearPMap.lean:228`, no `Add`+`Star` compatibility instance) — so the
generic `IsSelfAdjoint.add : IsSelfAdjoint x → IsSelfAdjoint y → IsSelfAdjoint (x + y)` does not
even typecheck for two `LinearPMap`s, and would be mathematically false in general anyway (domain
mismatch for two unbounded self-adjoint extensions). This confirms the corollary genuinely needs
the bounded-toPMap-⊤ structure and can't be gotten from a generic star-algebra lemma.

## 7. Coercion friction points — verified by compiling

I verified every claim below by compiling a **standalone** file (same imports, same `open scoped
InnerProductSpace LinearPMap`, same `variable`s, same `HasDenseDomain` def as `Basic.lean`) via
`lean_run_code`. All snippets below compiled with zero errors/warnings on the pinned Mathlib.

**(a) `(T + B.toPMap ⊤).domain = T.domain` is a two-step `rw`, not `rfl` on the nose (needs
`inf_top_eq`):**

```lean
have hUdom : (T + (B : H →ₗ[ℂ] H).toPMap ⊤).domain = T.domain := by
  rw [LinearPMap.add_domain, LinearMap.toPMap_domain, inf_top_eq]
```
Compiles. (`(f + g).domain` is `rfl`-equal to `f.domain ⊓ g.domain ⊓ ... ` only up to unfolding
`add_domain`; the actual `f.domain ⊓ ⊤ = f.domain` step needs `inf_top_eq`, it is not `rfl`
because `⊓` unfolds to `Submodule.inf` whose carrier is a set-intersection, and Lean does not
reduce `s ∩ Set.univ = s` definitionally for `Submodule`'s `SetLike` carrier.)

**(b) `Dense ((T + B.toPMap ⊤).domain : Set H)` from `hT` is then a plain rewrite, no
`Submodule.ext` needed:**

```lean
have hU : Dense ((T + (B : H →ₗ[ℂ] H).toPMap ⊤).domain : Set H) := by
  rw [hUdom]; exact hT
```
Compiles (using `hUdom` from (a); `HasDenseDomain T` unfolds to exactly this shape by
`whnf`/definitional unfolding at `exact`, no explicit `unfold HasDenseDomain` was even needed once
`hUdom` has rewritten the goal into `Dense (T.domain : Set H)` — but I include an `unfold
HasDenseDomain` in the version below for robustness/readability since the statement's `hT` has
type `HasDenseDomain T` and Lean's `exact hT` needs to see through the `def`; this worked directly
in testing without any extra tactic).

**(c) The one genuinely pleasant surprise: `LinearPMap.add_apply` composed with
`LinearMap.toPMap_apply` computes by outright `rfl`, no `simp` needed, once you hand it an element
of the right submodule:**

```lean
example {T : H →ₗ.[ℂ] H} (B : H →L[ℂ] H) (y : T.domain) :
    (T + (B : H →ₗ[ℂ] H).toPMap ⊤) ⟨(y : H), ⟨y.2, trivial⟩⟩
      = T y + (B : H →ₗ[ℂ] H) y := rfl
```
Compiles by `rfl`. This is because `T ⟨(y:H), _⟩` and `T y` are definitionally equal by
`Subtype`/`Prop` proof irrelevance (any two proofs of `(y:H) ∈ T.domain` give defeq subtype
terms), and structure eta makes `⟨(y:H), y.2⟩` defeq to `y` itself. **This is the load-bearing
simplification**: it means none of the domain-membership bookkeeping in the pointwise part of the
proof needs explicit `Subtype.ext`/`congrArg` massaging — `rfl`/`simp only [LinearPMap.add_apply,
LinearMap.toPMap_apply]` is always enough.

**(d) Full domain-equality direction, verified end to end** (this is genuinely the hardest single
step — see "Risks" below):

```lean
have hdom : ((T + (B : H →ₗ[ℂ] H).toPMap ⊤)†).domain
    = (T† + ((ContinuousLinearMap.adjoint B : H →ₗ[ℂ] H).toPMap ⊤)).domain := by
  have hRHSdom :
      (T† + ((ContinuousLinearMap.adjoint B : H →ₗ[ℂ] H).toPMap ⊤)).domain = T†.domain := by
    rw [LinearPMap.add_domain, LinearMap.toPMap_domain, inf_top_eq]
  rw [hRHSdom]
  ext φ
  constructor
  · intro hφ
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨(T + (B : H →ₗ[ℂ] H).toPMap ⊤)† ⟨φ, hφ⟩ - ContinuousLinearMap.adjoint B φ, ?_⟩
    intro y
    have key := LinearPMap.adjoint_isFormalAdjoint hU ⟨φ, hφ⟩
      (⟨(y : H), ⟨y.2, trivial⟩⟩ : (T + (B : H →ₗ[ℂ] H).toPMap ⊤).domain)
    simp only [LinearPMap.add_apply, LinearMap.toPMap_apply, inner_add_right] at key
    rw [inner_sub_left]
    have hB := ContinuousLinearMap.adjoint_inner_left B (y : H) φ
    linear_combination key - hB
  · intro hφ
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨T† ⟨φ, hφ⟩ + ContinuousLinearMap.adjoint B φ, ?_⟩
    intro y
    have key := LinearPMap.adjoint_isFormalAdjoint hT ⟨φ, hφ⟩
      (⟨(y : H), y.prop.1⟩ : T.domain)
    rw [LinearPMap.add_apply, inner_add_left, inner_add_right]
    simp only [LinearMap.toPMap_apply]
    have hB := ContinuousLinearMap.adjoint_inner_left B (y : H) φ
    linear_combination key + hB
```
(`hU : Dense ((T + (B : H →ₗ[ℂ] H).toPMap ⊤).domain : Set H)` from (b) is in scope.)
This compiled with **zero** errors/warnings against the pinned Mathlib. `linear_combination` is
doing real work here: it is closing an equation between complex inner products where the atoms on
each side are defeq-but-not-syntactically-identical (`T ⟨(y:H), y.prop.1⟩` vs `T y`, etc.) — it
succeeds because `linear_combination`'s closing `ring1` call resolves atoms up to the ambient
defeq/unification, so you do **not** need explicit `Subtype.ext`/`congrArg` steps first, *provided
you first `simp only [LinearPMap.add_apply, LinearMap.toPMap_apply, ...]` to peel off the
`LinearPMap.add`/`toPMap` layer*. Skipping that `simp only` and going straight to
`linear_combination` fails with "ring failed, ring expressions not equal" (I hit this on the first
attempt) because the un-simplified `⟪φ, ((B:LinearMap).toPMap ⊤) ⟨↑y, ⋯⟩⟫` is not automatically
recognized as the same atom as `⟪φ, B ↑y⟫` even though they are `rfl`-equal — `ring`/
`linear_combination`'s atom-matching is syntactic up to some limited reducibility, not full defeq,
so `toPMap_apply` (already a `@[simp]` lemma) must be applied explicitly first.

**(e) Pointwise equality (the `h'` argument of `LinearPMap.ext`), verified end to end:**

```lean
apply LinearPMap.ext hdom
intro x hf hg
have hxT : x ∈ T†.domain := hg.1
rw [LinearPMap.add_apply]
simp only [LinearMap.toPMap_apply]
apply LinearPMap.adjoint_apply_eq hU ⟨x, hf⟩
intro y
have key := LinearPMap.adjoint_isFormalAdjoint hT ⟨x, hxT⟩
  (⟨(y : H), y.prop.1⟩ : T.domain)
rw [LinearPMap.add_apply, inner_add_left, inner_add_right]
simp only [LinearMap.toPMap_apply]
have hB := ContinuousLinearMap.adjoint_inner_left B (y : H) x
linear_combination key + hB
```
Note `hg.1 : x ∈ T†.domain` works directly because `hg : x ∈ (T† + (adjoint B).toPMap ⊤).domain`
unfolds (via `add_domain`, `rfl`) to `x ∈ T†.domain ∧ x ∈ (adjoint B).toPMap ⊤ .domain`, and `.1`
projects through that defeq without any rewrite — another instance of point (c)'s
proof-irrelevance/defeq generosity.

**(f) The full first theorem, assembled from (a)–(e), compiles standalone against the pinned
Mathlib** (verified via `lean_run_code` with the project's exact `HasDenseDomain` def, opens, and
`variable`s reproduced) — see the Route section below for the complete text to paste in.

**(g) The corollary, verified standalone:**

```lean
theorem isSelfAdjoint_add_of_isSelfAdjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hTsa : IsSelfAdjoint T) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (T + (B : H →ₗ[ℂ] H).toPMap ⊤) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_add_toPMap hT B,
    LinearPMap.isSelfAdjoint_def.mp hTsa, ContinuousLinearMap.isSelfAdjoint_iff'.mp hB]
```
Compiled with zero errors, treating `adjoint_add_toPMap` as an `axiom` in the standalone test (so
this is a pure unit test of the corollary's own three-line proof, independent of the first
theorem's internals). A first attempt using `rw [hTsa]` directly (rather than
`LinearPMap.isSelfAdjoint_def.mp hTsa`) failed with "did not find pattern `star T`" — `hTsa :
IsSelfAdjoint T` is *definitionally* `star T = T`, not syntactically `T† = T`, even though the two
are `Iff.rfl`-equal at the `Prop` level; you need `LinearPMap.isSelfAdjoint_def.mp hTsa` (or
`show T† = T from hTsa`) to get a term of the right syntactic shape for `rw`. Likewise for
`hB : IsSelfAdjoint B`, use `ContinuousLinearMap.isSelfAdjoint_iff'.mp hB : ContinuousLinearMap.adjoint B = B`.

## Route (recommended, in order)

1. `hUdom`, `hU` as in 7(a)/(b).
2. `hdom` (domain equality of the two `LinearPMap`s) exactly as in 7(d) — this is the only
   nontrivial part.
3. `LinearPMap.ext hdom` then the pointwise argument exactly as in 7(e).
4. For the corollary: `LinearPMap.isSelfAdjoint_def`, the just-proved `adjoint_add_toPMap`,
   `LinearPMap.isSelfAdjoint_def.mp hTsa`, `ContinuousLinearMap.isSelfAdjoint_iff'.mp hB`, as in
   7(g).

Full verified text for `adjoint_add_toPMap` (drop-in, only the leading `theorem ... := by` line
needs to match `Basic.lean`'s exact signature, which it already does verbatim in this file):

```lean
theorem adjoint_add_toPMap {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (B : H →L[ℂ] H) :
    (T + (B : H →ₗ[ℂ] H).toPMap ⊤)† =
      T† + ((ContinuousLinearMap.adjoint B : H →ₗ[ℂ] H).toPMap ⊤) := by
  have hUdom : (T + (B : H →ₗ[ℂ] H).toPMap ⊤).domain = T.domain := by
    rw [LinearPMap.add_domain, LinearMap.toPMap_domain, inf_top_eq]
  have hU : Dense ((T + (B : H →ₗ[ℂ] H).toPMap ⊤).domain : Set H) := by
    rw [hUdom]; exact hT
  have hdom : ((T + (B : H →ₗ[ℂ] H).toPMap ⊤)†).domain
      = (T† + ((ContinuousLinearMap.adjoint B : H →ₗ[ℂ] H).toPMap ⊤)).domain := by
    have hRHSdom :
        (T† + ((ContinuousLinearMap.adjoint B : H →ₗ[ℂ] H).toPMap ⊤)).domain = T†.domain := by
      rw [LinearPMap.add_domain, LinearMap.toPMap_domain, inf_top_eq]
    rw [hRHSdom]
    ext φ
    constructor
    · intro hφ
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨(T + (B : H →ₗ[ℂ] H).toPMap ⊤)† ⟨φ, hφ⟩ - ContinuousLinearMap.adjoint B φ, ?_⟩
      intro y
      have key := LinearPMap.adjoint_isFormalAdjoint hU ⟨φ, hφ⟩
        (⟨(y : H), ⟨y.2, trivial⟩⟩ : (T + (B : H →ₗ[ℂ] H).toPMap ⊤).domain)
      simp only [LinearPMap.add_apply, LinearMap.toPMap_apply, inner_add_right] at key
      rw [inner_sub_left]
      have hB := ContinuousLinearMap.adjoint_inner_left B (y : H) φ
      linear_combination key - hB
    · intro hφ
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨T† ⟨φ, hφ⟩ + ContinuousLinearMap.adjoint B φ, ?_⟩
      intro y
      have key := LinearPMap.adjoint_isFormalAdjoint hT ⟨φ, hφ⟩
        (⟨(y : H), y.prop.1⟩ : T.domain)
      rw [LinearPMap.add_apply, inner_add_left, inner_add_right]
      simp only [LinearMap.toPMap_apply]
      have hB := ContinuousLinearMap.adjoint_inner_left B (y : H) φ
      linear_combination key + hB
  apply LinearPMap.ext hdom
  intro x hf hg
  have hxT : x ∈ T†.domain := hg.1
  rw [LinearPMap.add_apply]
  simp only [LinearMap.toPMap_apply]
  apply LinearPMap.adjoint_apply_eq hU ⟨x, hf⟩
  intro y
  have key := LinearPMap.adjoint_isFormalAdjoint hT ⟨x, hxT⟩
    (⟨(y : H), y.prop.1⟩ : T.domain)
  rw [LinearPMap.add_apply, inner_add_left, inner_add_right]
  simp only [LinearMap.toPMap_apply]
  have hB := ContinuousLinearMap.adjoint_inner_left B (y : H) x
  linear_combination key + hB
```

and for `isSelfAdjoint_add_of_isSelfAdjoint`:

```lean
theorem isSelfAdjoint_add_of_isSelfAdjoint {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hTsa : IsSelfAdjoint T) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (T + (B : H →ₗ[ℂ] H).toPMap ⊤) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_add_toPMap hT B,
    LinearPMap.isSelfAdjoint_def.mp hTsa, ContinuousLinearMap.isSelfAdjoint_iff'.mp hB]
```

I verified this **entire** `adjoint_add_toPMap` proof compiles standalone (identical imports,
opens, `variable`s, and `HasDenseDomain` def to `Basic.lean`) with zero errors or warnings, and
separately verified the corollary's three-line proof (with `adjoint_add_toPMap` stubbed as an
`axiom`) compiles with zero errors. I did not have write access to `Basic.lean` itself (policy: no
Lean-source edits from a scout agent), so the final step — pasting this into the file in place of
the two `sorry`s and running `lake build`/`lean_diagnostic_messages` on the real file — is for the
prover to do, but I expect it to be routine given the identical ambient context.

## Risks

- **The domain-equality step (7d) is the one place a name-level breakage would show up.** It uses
  `LinearPMap.adjoint_isFormalAdjoint`, `LinearPMap.mem_adjoint_domain_of_exists`,
  `ContinuousLinearMap.adjoint_inner_left`, and the `simp only [LinearPMap.add_apply,
  LinearMap.toPMap_apply, inner_add_right/left]` normalization before `linear_combination`. If a
  future Mathlib bump renames any of these (all are old, stable names from the original 2022 PR
  and the adjoint file), the fix is mechanical.
- **Do not drop the `simp only [LinearMap.toPMap_apply]` calls before `linear_combination`** —
  without it `linear_combination`/`ring1` fails on "ring expressions not equal" even though the
  two sides are `rfl`-equal, because atom-matching does not see through the un-simplified
  `toPMap`/`add_apply` application. This is the one genuine "fight" I found; it is a one-line fix
  once you know to add the `simp only`, but it is easy to miss since the error message ("ring
  expressions not equal") does not suggest "add a simp lemma" as the fix.
- **`hg.1`/`y.prop.1` rely on `Submodule.inf`'s membership being defeq to `And`.** This worked in
  every test here (it is exactly how Mathlib's own `add_apply` is stated and proved by `rfl`), but
  if you ever see "invalid projection" or a type mismatch mentioning `Submodule.mem_inf` while
  editing around this proof, replace `.1`/`.2` with `(Submodule.mem_inf.mp _).1` /
  `(Submodule.mem_inf.mp _).2` as a fallback — I hit exactly this failure once during scouting when
  I mis-threaded a `y : (T + S).domain` where a `y : T.domain` was expected (a bug in my own draft,
  not a Mathlib issue); once the types line up, plain `.1`/`.2` works.
- **No blueprint mismatch found.** The blueprint's three-part proof (Parts 1–2: domain equality by
  a two-sided $C$/$C'$ bounding argument; Part 3: the formula by density) matches the Lean route
  above exactly, except that the exact-representation lemmas (`mem_adjoint_domain_of_exists`,
  `adjoint_isFormalAdjoint`) let Lean skip the explicit boundedness/norm bookkeeping of Parts 1–2
  entirely, going straight to an exact witness. This is a legitimate simplification, not a
  weakening: the target statements are proved exactly as given, unchanged.
- **The corollary's `\uses` list in the blueprint** (`def:hall-9.1, lmm:hall-dense-testing,
  def:bounded-operator-notation, prpstn:hall-a.43, def:hall-3.1`) does not itself need touching;
  none of chapters 1–9's material needs to be formalized per project policy, and this proof uses
  only the Mathlib primitives above plus the project's existing `HasDenseDomain`.
