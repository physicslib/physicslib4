/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Unbounded.Basic
import Physicslib4.Spectral.Unbounded.Spectrum
import Physicslib4.Spectral.Unbounded.Composition

/-!
# Products of unbounded operators and von Neumann's theorem

This file defines the product `B ∘ A` of two partial linear maps on a Hilbert space, with domain
`{x ∈ Dom A | Ax ∈ Dom B}`, and the operator `T†T` as the product of `T†` with `T`. For a
closed, densely defined `T` it states von Neumann's theorem: `T†T` is positive, self-adjoint and
densely defined, and `Dom(T†T)` is a core for `T`. It then states the transfer of the functional
calculus along the pushforward of a projection-valued measure, defines the absolute value
`|T| = (T†T)^{1/2}`, and states `Dom |T| = Dom T` with `‖|T|ψ‖ = ‖Tψ‖`, through the transfer of a
norm identity from a core to the closure.

Mathlib's `LinearPMap.comp g f` requires the range of `f` to lie in the domain of `g`, so the
product is built by first restricting `A` to `{x ∈ Dom A | Ax ∈ Dom B}` with
`LinearPMap.domRestrict`. The core property is Mathlib's `LinearPMap.HasCore`.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
The product `B A` of two partial linear maps: its domain is
`{x ∈ Dom A | Ax ∈ Dom B}` and `(B A) x = B (A x)`. It is `B.comp` applied to the restriction of
`A` to the subspace `(Dom B).comap A`, pushed into `H`. The product need not be densely defined.

Implementation note: `pmapMul` takes complex-linear factors because every product the section
needs is linear. The antilinear Tomita operator is handled through the linear `S₀′ = C ∘ S₀`, and
composites with an antiunitary operator through `antiunitaryConj`, built from Mathlib's
semilinear `LinearPMap.comp` and `LinearMap.compPMap`.

Blueprint: def:product-of-unbounded-operators
-/
def pmapMul (B A : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H :=
  B.comp (A.domRestrict ((B.domain.comap A.toFun).map A.domain.subtype)) (fun p => by
    obtain ⟨q, hq, hpq⟩ := p.2.1
    rw [A.domRestrict_apply (y := q) hpq.symm]
    exact hq)

omit [CompleteSpace H] in
/--
The domain of the product `B A` is contained in the domain of `A`.

Blueprint: def:product-of-unbounded-operators
-/
theorem pmapMul_domain_le (B A : H →ₗ.[ℂ] H) : (pmapMul B A).domain ≤ A.domain :=
  fun _ hx => hx.2

omit [CompleteSpace H] in
/--
The domain of the product `B A` is `{x ∈ Dom A | Ax ∈ Dom B}`, and on it `(B A) x = B (A x)`.

Blueprint: def:product-of-unbounded-operators
-/
theorem mem_domain_pmapMul_iff (B A : H →ₗ.[ℂ] H) (x : H) :
    x ∈ (pmapMul B A).domain ↔ ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ ∈ B.domain :=
  ⟨fun ⟨⟨q, hq, hqx⟩, hx⟩ => ⟨hx, by subst hqx; exact hq⟩,
    fun ⟨hx, h⟩ => ⟨⟨⟨x, hx⟩, h, rfl⟩, hx⟩⟩

omit [CompleteSpace H] in
/--
The value of the product: for `x ∈ Dom(B A)`, `(B A) x = B (A x)`.

Blueprint: def:product-of-unbounded-operators
-/
theorem pmapMul_apply (B A : H →ₗ.[ℂ] H) (x : (pmapMul B A).domain)
    (hx : A ⟨x, pmapMul_domain_le B A x.2⟩ ∈ B.domain) :
    pmapMul B A x = B ⟨A ⟨x, pmapMul_domain_le B A x.2⟩, hx⟩ := by
  change B ⟨A.domRestrict _ x, _⟩ = _
  congr 2

omit [CompleteSpace H] in
/--
The graph of the product `B A` is the composite of the graphs: `(x, z) ∈ Γ(B A)` if and only if
there is `w` with `(x, w) ∈ Γ(A)` and `(w, z) ∈ Γ(B)`.

Blueprint: def:product-of-unbounded-operators
-/
theorem mem_graph_pmapMul_iff (B A : H →ₗ.[ℂ] H) (x z : H) :
    (x, z) ∈ (pmapMul B A).graph ↔ ∃ w, (x, w) ∈ A.graph ∧ (w, z) ∈ B.graph := by
  constructor
  · intro h
    obtain ⟨y, hy1, hy2⟩ := LinearPMap.mem_graph_iff _ |>.mp h
    obtain ⟨q, hq, hyq⟩ := y.2.1
    refine ⟨A q, ?_, ?_⟩
    · exact (LinearPMap.mem_graph_iff _).mpr ⟨q, hyq.trans hy1, rfl⟩
    · refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨A q, hq⟩, rfl, ?_⟩
      rw [← hy2]
      change _ = B ⟨A.domRestrict _ y, _⟩
      congr 2
      exact (A.domRestrict_apply (y := q) hyq.symm).symm
  · rintro ⟨w, hxw, hwz⟩
    obtain ⟨q, hq1, hq2⟩ := (LinearPMap.mem_graph_iff _).mp hxw
    obtain ⟨r, hr1, hr2⟩ := (LinearPMap.mem_graph_iff _).mp hwz
    simp only at hq1 hq2 hr1 hr2
    have hd : (q : H) ∈ (pmapMul B A).domain :=
      ⟨⟨q, show A q ∈ B.domain from hq2 ▸ hr1 ▸ r.2, rfl⟩, q.2⟩
    refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨q, hd⟩, hq1, ?_⟩
    rw [← hr2]
    change B ⟨A.domRestrict _ ⟨q, hd⟩, _⟩ = _
    congr 2
    exact (A.domRestrict_apply (x := ⟨q, hd⟩) (y := q) rfl).trans (hq2.trans hr1.symm)

/--
The operator `T†T`: the product of `T†` with `T`, with domain `{x ∈ Dom T | Tx ∈ Dom T†}` and
`(T†T) x = T† (T x)`.

Blueprint: def:adjoint-product-operator
-/
noncomputable def adjointMulSelf (T : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H :=
  pmapMul (T†) T

/-- Key existence lemma: `1 + T†T` maps onto `H`. -/
private theorem vN_key {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (hcl : T.IsClosed) (y : H) :
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
private theorem vN_inner {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) {w z u v : H}
    (hwz : (w, z) ∈ T†.graph) (huv : (u, v) ∈ T.graph) : ⟪u, z⟫_ℂ = ⟪v, w⟫_ℂ := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hT, Submodule.mem_adjoint_iff] at hwz
  exact (sub_eq_zero.mp (hwz u v huv)).symm

/-- von Neumann: for closed densely defined `T`, the operator `S = T†T` (characterised by its
graph) is self-adjoint, positive, and densely defined. -/
private theorem vN_main {T S : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (hcl : T.IsClosed)
    (hS : ∀ x z : H, (x, z) ∈ S.graph ↔ ∃ w, (x, w) ∈ T.graph ∧ (w, z) ∈ T†.graph) :
    IsSelfAdjoint S ∧ HasDenseDomain S ∧ IsPositive S ∧ ker (subSmul (S†) (-1)) = ⊥ := by
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
  refine ⟨adjoint_eq_of_range_eq_top hle hr hk, hdense, ⟨hsym, fun x => ?_⟩, hk⟩
  obtain ⟨w, -, e⟩ := hpos x
  rw [e]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- The graph characterisation of `T†T`. -/
private theorem vN_graph (T : H →ₗ.[ℂ] H) (x z : H) :
    (x, z) ∈ (adjointMulSelf T).graph ↔ ∃ w, (x, w) ∈ T.graph ∧ (w, z) ∈ T†.graph :=
  mem_graph_pmapMul_iff (T†) T x z

/--
For a closed, densely defined `T` and every `y ∈ H` there is `x ∈ Dom(T†T)` with
`x + T†T x = y`.

Blueprint: lmm:von-neumann-solvability
-/
theorem exists_add_adjointMulSelf_eq {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) (y : H) :
    ∃ x : (adjointMulSelf T).domain, (x : H) + adjointMulSelf T x = y := by
  obtain ⟨x, w, z, hxw, hwz, rfl⟩ := vN_key hT hcl y
  obtain ⟨xs, hxs1, hxs2⟩ :=
    (adjointMulSelf T).mem_graph_iff.mp ((vN_graph T _ _).mpr ⟨w, hxw, hwz⟩)
  exact ⟨xs, by simp only at hxs1 hxs2; rw [hxs1, hxs2]⟩

/--
For a densely defined `T`, `x ∈ Dom(T†T)` and `x' ∈ Dom T`, `⟪x', T†T x⟫ = ⟪T x', T x⟫`; in
particular `⟪x, T†T x⟫ = ‖T x‖²`.

Blueprint: lmm:von-neumann-form
-/
theorem inner_adjointMulSelf {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (x : (adjointMulSelf T).domain) :
    (∀ x' : T.domain, ⟪(x' : H), adjointMulSelf T x⟫_ℂ =
        ⟪T x', T ⟨x, pmapMul_domain_le _ _ x.2⟩⟫_ℂ) ∧
      ⟪(x : H), adjointMulSelf T x⟫_ℂ = (‖T ⟨x, pmapMul_domain_le _ _ x.2⟩‖ ^ 2 : ℂ) := by
  obtain ⟨w, hxw, hwz⟩ := (vN_graph T _ _).mp ((adjointMulSelf T).mem_graph x)
  have hw : w = T ⟨x, pmapMul_domain_le _ _ x.2⟩ :=
    T.mem_graph_snd_inj hxw (T.mem_graph ⟨x, pmapMul_domain_le _ _ x.2⟩) rfl
  subst hw
  have h1 : ∀ x' : T.domain, ⟪(x' : H), adjointMulSelf T x⟫_ℂ =
      ⟪T x', T ⟨x, pmapMul_domain_le _ _ x.2⟩⟫_ℂ := fun x' => vN_inner hT hwz (T.mem_graph x')
  refine ⟨h1, ?_⟩
  exact (h1 ⟨x, pmapMul_domain_le _ _ x.2⟩).trans (inner_self_eq_norm_sq_to_K _)

/--
For a closed, densely defined `T`, the domain of `T†T` is dense.

Blueprint: lmm:von-neumann-dense-domain
-/
theorem hasDenseDomain_adjointMulSelf {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) : HasDenseDomain (adjointMulSelf T) :=
  (vN_main hT hcl (vN_graph T)).2.1

/--
For a closed, densely defined `T`, the operator `D = T†T` is symmetric, `D†` extends `D`, and
`D` is positive.

Blueprint: lmm:von-neumann-symmetric-positive
-/
theorem adjointMulSelf_symmetric_positive {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) :
    IsSymmetric (adjointMulSelf T) ∧ adjointMulSelf T ≤ (adjointMulSelf T)† ∧
      IsPositive (adjointMulSelf T) := by
  obtain ⟨-, hd, hp, -⟩ := vN_main hT hcl (vN_graph T)
  exact ⟨hp.1, (isSymmetric_iff_le_adjoint hd).mp hp.1, hp⟩

/--
For a closed, densely defined `T` and `D = T†T`, the operator `D† + 1` is injective:
`Ker(D† - (-1)) = {0}`.

Blueprint: lmm:von-neumann-kernel
-/
theorem ker_subSmul_adjoint_adjointMulSelf {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) : ker (subSmul ((adjointMulSelf T)†) (-1)) = ⊥ :=
  (vN_main hT hcl (vN_graph T)).2.2.2

/--
**von Neumann's theorem.** For a closed, densely defined `T`, the operator `T†T` is
self-adjoint, densely defined and positive.

Blueprint: thrm:von-neumann-adjoint-product
-/
theorem isSelfAdjoint_adjointMulSelf {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) :
    IsSelfAdjoint (adjointMulSelf T) ∧ HasDenseDomain (adjointMulSelf T) ∧
      IsPositive (adjointMulSelf T) := by
  obtain ⟨h1, h2, h3, -⟩ := vN_main hT hcl (vN_graph T)
  exact ⟨h1, h2, h3⟩

/--
For a closed, densely defined `T`, the domain of `T†T` is a core for `T`: the closure of the
restriction of `T` to `Dom(T†T)` is `T` (Mathlib's `LinearPMap.HasCore`).

Blueprint: lmm:core-of-adjoint-product
-/
theorem hasCore_domain_adjointMulSelf {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) : T.HasCore (adjointMulSelf T).domain := by
  have hle : ∀ R : H →ₗ.[ℂ] H, R ≤ T → R.graph.topologicalClosure ≤ T.graph := fun R h =>
    Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le h) hcl
  refine ⟨pmapMul_domain_le _ _, ?_⟩
  set R := T.domRestrict (adjointMulSelf T).domain
  have hR : R.IsClosable := hcl.isClosable.leIsClosable LinearPMap.domRestrict_le
  refine LinearPMap.eq_of_eq_graph ?_
  rw [← hR.graph_closure_eq_closure_graph]
  refine le_antisymm (hle R LinearPMap.domRestrict_le) fun p hp => ?_
  let e : WithLp 2 (H × H) →ₗ[ℂ] H × H := (WithLp.linearEquiv 2 ℂ (H × H)).toLinearMap
  let G : Submodule ℂ (WithLp 2 (H × H)) := R.graph.topologicalClosure.comap e
  have hG : IsClosed (G : Set (WithLp 2 (H × H))) :=
    R.graph.isClosed_topologicalClosure.preimage (WithLp.prod_continuous_ofLp 2 H H)
  obtain ⟨⟨g, k⟩, ⟨hg, hk, hsum⟩, -⟩ := existsUnique_add_mem_orthogonal hG (WithLp.toLp 2 p)
  have hg' : WithLp.ofLp g ∈ R.graph.topologicalClosure := hg
  have hkp : WithLp.ofLp k = p - WithLp.ofLp g := by
    have hk2 : k = WithLp.toLp 2 p - g := by rw [hsum]; simp
    rw [hk2]; rfl
  have hkT : ((WithLp.ofLp k).1, (WithLp.ofLp k).2) ∈ T.graph := by
    rw [Prod.mk.eta, hkp]
    exact T.graph.sub_mem hp (hle R LinearPMap.domRestrict_le hg')
  have hk' : ∀ u v, (u, v) ∈ R.graph →
      ⟪u, (WithLp.ofLp k).1⟫_ℂ + ⟪v, (WithLp.ofLp k).2⟫_ℂ = 0 := by
    intro u v huv
    have := (Submodule.mem_orthogonal G k).mp hk (WithLp.toLp 2 (u, v))
      (R.graph.le_topologicalClosure huv)
    simpa [WithLp.prod_inner_apply] using this
  obtain ⟨ka, hka1, hka2⟩ := T.mem_graph_iff.mp hkT
  simp only at hka1 hka2
  obtain ⟨x, hx⟩ := exists_add_adjointMulSelf_eq hT hcl (ka : H)
  have hxR : ((x : H), T ⟨x, pmapMul_domain_le _ _ x.2⟩) ∈ R.graph :=
    R.mem_graph_iff.mpr ⟨⟨x, x.2, pmapMul_domain_le _ _ x.2⟩, rfl, T.domRestrict_apply rfl⟩
  have e1 := hk' _ _ hxR
  rw [← hka1, ← hka2] at e1
  have e2 := (inner_adjointMulSelf hT x).1 ka
  have h0 : ⟪(ka : H), (ka : H)⟫_ℂ = 0 := by
    calc ⟪(ka : H), (ka : H)⟫_ℂ = ⟪(ka : H), (x : H) + adjointMulSelf T x⟫_ℂ := by rw [hx]
      _ = (starRingEnd ℂ) (⟪(x : H), (ka : H)⟫_ℂ + ⟪T ⟨x, pmapMul_domain_le _ _ x.2⟩, T ka⟫_ℂ) := by
        rw [inner_add_right, e2, map_add, inner_conj_symm, inner_conj_symm]
      _ = 0 := by rw [e1, map_zero]
  have hka0 : ka = 0 := Subtype.ext (inner_self_eq_zero.mp h0)
  have ha : (WithLp.ofLp k).1 = 0 := by rw [← hka1, hka0]; rfl
  have hb : (WithLp.ofLp k).2 = 0 := by rw [← hka2, hka0]; simp
  have hpg : p = WithLp.ofLp g := by
    rw [← sub_eq_zero, ← hkp]; exact Prod.ext ha hb
  exact hpg ▸ hg'

/-!
### Pushforward of a projection-valued measure
-/

section Pushforward

open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/--
The pushforward `φ_*μ(F) = μ(φ⁻¹(F))` is a projection-valued measure, and its associated measures
are the pushforwards: `(φ_*μ)_ψ = φ_*(μ_ψ)` for every `ψ ∈ H`.

Implementation note: the pushforward is the existing `pushforwardPVM` (`Cayley.lean`), which
already is a `ProjectionValuedMeasure`; its values on measurable sets are
`pushforwardPVM_apply`. This theorem states the remaining claim, about associated measures.

Blueprint: lmm:pushforward-pvm-is-pvm
-/
theorem assoc_pushforwardPVM (μ : ProjectionValuedMeasure X H) {φ : X → Y}
    (hφ : Measurable φ) (ψ : H) :
    (pushforwardPVM μ φ hφ).assoc ψ = (μ.assoc ψ).map φ := by
  sorry

/--
For measurable `g : Y → ℂ`, the domains agree, `W^{φ_*μ}_g = W^μ_{g ∘ φ}`, and
`∫ g d(φ_*μ)_ψ = ∫ (g ∘ φ) dμ_ψ` for `ψ` in this domain.

Blueprint: lmm:pushforward-pvm-domain
-/
theorem integralDomain_pushforwardPVM (μ : ProjectionValuedMeasure X H) {φ : X → Y}
    (hφ : Measurable φ) {g : Y → ℂ} (hg : Measurable g) :
    integralDomain (pushforwardPVM μ φ hφ) g = integralDomain μ (g ∘ φ) ∧
      ∀ ψ ∈ integralDomain (pushforwardPVM μ φ hφ) g,
        ∫ y, g y ∂((pushforwardPVM μ φ hφ).assoc ψ) = ∫ x, g (φ x) ∂(μ.assoc ψ) := by
  sorry

/--
For measurable `g : Y → ℂ`, `∫ g d(φ_*μ) = ∫ (g ∘ φ) dμ` as partial maps, including equality of
domains.

Blueprint: lmm:pushforward-pvm
-/
theorem pmapIntegral_pushforwardPVM (μ : ProjectionValuedMeasure X H) {φ : X → Y}
    (hφ : Measurable φ) {g : Y → ℂ} (hg : Measurable g) :
    pmapIntegral (pushforwardPVM μ φ hφ) g = pmapIntegral μ (g ∘ φ) := by
  sorry

end Pushforward

/--
For a self-adjoint `A` and a measurable `f : ℝ → ℝ`, `f(A)` is self-adjoint, its spectral
measure is the pushforward `f_*μ^A`, and `g(f(A)) = (g ∘ f)(A)` for every measurable
`g : ℝ → ℂ`.

Blueprint: crllr:fc-of-fc
-/
theorem functionalCalculus_functionalCalculus {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ∃ hfA : IsSelfAdjoint (functionalCalculus hA fun x => (f x : ℂ)),
      spectralMeasure hfA = pushforwardPVM (spectralMeasure hA) f hf ∧
        ∀ g : ℝ → ℂ, Measurable g →
          functionalCalculus hfA g = functionalCalculus hA (g ∘ f) := by
  sorry

/-!
### The absolute value of a closed operator
-/

/--
The absolute value `|T| = (T†T)^{1/2}` of a closed, densely defined `T`: the functional calculus
of the self-adjoint operator `T†T` (von Neumann's theorem) applied to the square root.

Implementation note: the closedness and density hypotheses are arguments, since the functional
calculus needs the self-adjointness proof of `T†T`.

Blueprint: def:absolute-value
-/
noncomputable def absoluteValue (T : H →ₗ.[ℂ] H) (hT : HasDenseDomain T) (hcl : T.IsClosed) :
    H →ₗ.[ℂ] H :=
  functionalCalculus (isSelfAdjoint_adjointMulSelf hT hcl).1 fun x => ((Real.sqrt x : ℝ) : ℂ)

/--
For a closed, densely defined `T`, every `x ∈ Dom(T†T)` lies in `Dom |T|`.

Blueprint: lmm:adjoint-product-domain-in-sqrt-domain
-/
theorem adjointMulSelf_domain_le_absoluteValue {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) : (adjointMulSelf T).domain ≤ (absoluteValue T hT hcl).domain := by
  sorry

/--
For a closed, densely defined `T` and `x ∈ Dom(T†T)`, `‖|T| x‖ = ‖T x‖`.

Blueprint: lmm:absolute-value-norm-on-core
-/
theorem norm_absoluteValue_of_mem_adjointMulSelf {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) (x : (adjointMulSelf T).domain) :
    ‖absoluteValue T hT hcl ⟨x, adjointMulSelf_domain_le_absoluteValue hT hcl x.2⟩‖ =
      ‖T ⟨x, pmapMul_domain_le _ _ x.2⟩‖ := by
  sorry

/--
For a closed, densely defined `T`, `|T|` is positive and self-adjoint, hence closed, and
`Dom(T†T)` is a core for `|T|`.

Blueprint: lmm:absolute-value-closed
-/
theorem absoluteValue_closed {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (hcl : T.IsClosed) :
    IsPositive (absoluteValue T hT hcl) ∧ IsSelfAdjoint (absoluteValue T hT hcl) ∧
      (absoluteValue T hT hcl).IsClosed ∧
      (absoluteValue T hT hcl).HasCore (adjointMulSelf T).domain := by
  sorry

omit [CompleteSpace H] in
/--
Let `A` and `B` be closed and `D` a core for `A` with `D ⊆ Dom B` and `‖Aψ‖ = ‖Bψ‖` for
`ψ ∈ D`. Then `Dom A ⊆ Dom B` and `‖Aψ‖ = ‖Bψ‖` for every `ψ ∈ Dom A`.

Blueprint: lmm:closure-transfer-one-direction
-/
theorem domain_le_of_hasCore_norm_eq {A B : H →ₗ.[ℂ] H} (hA : A.IsClosed) (hB : B.IsClosed)
    {D : Submodule ℂ H} (hD : A.HasCore D) (hDB : D ≤ B.domain)
    (hnorm : ∀ (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain), ψ ∈ D →
      ‖A ⟨ψ, hψA⟩‖ = ‖B ⟨ψ, hψB⟩‖) :
    A.domain ≤ B.domain ∧ ∀ (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain),
      ‖A ⟨ψ, hψA⟩‖ = ‖B ⟨ψ, hψB⟩‖ := by
  sorry

omit [CompleteSpace H] in
/--
Let `A` and `B` be closed and `D` a common core with `‖Aψ‖ = ‖Bψ‖` for `ψ ∈ D`. Then
`Dom A = Dom B` and `‖Aψ‖ = ‖Bψ‖` for every `ψ` in it.

Blueprint: lmm:closure-transfer-common-core
-/
theorem domain_eq_of_hasCore_norm_eq {A B : H →ₗ.[ℂ] H} (hA : A.IsClosed) (hB : B.IsClosed)
    {D : Submodule ℂ H} (hDA : A.HasCore D) (hDB : B.HasCore D)
    (hnorm : ∀ (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain), ψ ∈ D →
      ‖A ⟨ψ, hψA⟩‖ = ‖B ⟨ψ, hψB⟩‖) :
    A.domain = B.domain ∧ ∀ (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain),
      ‖A ⟨ψ, hψA⟩‖ = ‖B ⟨ψ, hψB⟩‖ := by
  sorry

/--
For a closed, densely defined `T`, `|T|` is positive and self-adjoint, `Dom |T| = Dom T`, and
`‖|T| ψ‖ = ‖T ψ‖` for every `ψ ∈ Dom T`.

Blueprint: thrm:absolute-value-domain
-/
theorem absoluteValue_domain {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (hcl : T.IsClosed) :
    IsPositive (absoluteValue T hT hcl) ∧ IsSelfAdjoint (absoluteValue T hT hcl) ∧
      (absoluteValue T hT hcl).domain = T.domain ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (absoluteValue T hT hcl).domain) (h₂ : ψ ∈ T.domain),
        ‖absoluteValue T hT hcl ⟨ψ, h₁⟩‖ = ‖T ⟨ψ, h₂⟩‖ := by
  sorry

/--
For a positive self-adjoint `P`, the product `P P` is self-adjoint and `(P P)^{1/2} = P`.

Blueprint: lmm:positive-square-root-unique
-/
theorem sqrt_pmapMul_self {P : H →ₗ.[ℂ] H} (hP : IsSelfAdjoint P) (hpos : IsPositive P) :
    ∃ hPP : IsSelfAdjoint (pmapMul P P),
      functionalCalculus hPP (fun x => ((Real.sqrt x : ℝ) : ℂ)) = P := by
  sorry

/-!
### Polar decomposition

For the next results, `T` is closed, densely defined and injective with dense range. Injectivity
is `ker T = ⊥` and dense range is `Dense (range T)`, with the project's `ker` and `range`. Each
statement carries only the hypotheses its proof uses.
-/

/--
For a closed, densely defined, injective `T`, `|T|` is injective and its range
is dense.

Blueprint: lmm:absolute-value-injective-dense-range
-/
theorem absoluteValue_injective_denseRange {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) (hinj : ker T = ⊥) :
    ker (absoluteValue T hT hcl) = ⊥ ∧ Dense (range (absoluteValue T hT hcl) : Set H) := by
  sorry

/--
For a closed, densely defined, injective `T`, the assignment
`V₀(|T|ψ) = Tψ` (`ψ ∈ Dom T`) is a well-defined linear isometry from `Range |T|` to `H`.

Blueprint: lmm:polar-isometry-on-range
-/
theorem exists_polarIsometry_on_range {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) (hinj : ker T = ⊥) :
    ∃ V₀ : range (absoluteValue T hT hcl) →ₗᵢ[ℂ] H,
      ∀ (ψ : H) (h₁ : ψ ∈ T.domain) (h₂ : ψ ∈ (absoluteValue T hT hcl).domain),
        V₀ ⟨absoluteValue T hT hcl ⟨ψ, h₂⟩,
          LinearMap.mem_range_self (absoluteValue T hT hcl).toFun ⟨ψ, h₂⟩⟩ = T ⟨ψ, h₁⟩ := by
  sorry

/--
For a closed, densely defined, injective `T`, there is a unique bounded `V`
with `V |T| ψ = T ψ` for all `ψ ∈ Dom T`, and it is isometric. Together with
`Dom |T| = Dom T` (`absoluteValue_domain`) this says `T = V|T|`.

Blueprint: lmm:polar-isometry
-/
theorem existsUnique_polarIsometry {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) (hinj : ker T = ⊥) :
    (∃! V : H →L[ℂ] H,
      ∀ (ψ : H) (h₁ : ψ ∈ T.domain) (h₂ : ψ ∈ (absoluteValue T hT hcl).domain),
        V (absoluteValue T hT hcl ⟨ψ, h₂⟩) = T ⟨ψ, h₁⟩) ∧
    ∀ V : H →L[ℂ] H,
      (∀ (ψ : H) (h₁ : ψ ∈ T.domain) (h₂ : ψ ∈ (absoluteValue T hT hcl).domain),
        V (absoluteValue T hT hcl ⟨ψ, h₂⟩) = T ⟨ψ, h₁⟩) → ∀ x, ‖V x‖ = ‖x‖ := by
  sorry

/--
**Polar decomposition.** For a closed, densely defined, injective `T` with dense range, there is
a unitary `V` with `T = V|T|`: `Dom |T| = Dom T` and `V |T| ψ = T ψ` for `ψ ∈ Dom T`, where
`|T|` is positive, self-adjoint and injective. By `existsUnique_polarIsometry`, `V` is the
isometry of `lmm:polar-isometry`.

Blueprint: thrm:polar-decomposition
-/
theorem polar_decomposition {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (hcl : T.IsClosed)
    (hinj : ker T = ⊥) (hran : Dense (range T : Set H)) :
    ∃ V : H ≃ₗᵢ[ℂ] H,
      (absoluteValue T hT hcl).domain = T.domain ∧
      (∀ (ψ : H) (h₁ : ψ ∈ T.domain) (h₂ : ψ ∈ (absoluteValue T hT hcl).domain),
        V (absoluteValue T hT hcl ⟨ψ, h₂⟩) = T ⟨ψ, h₁⟩) ∧
      IsPositive (absoluteValue T hT hcl) ∧ IsSelfAdjoint (absoluteValue T hT hcl) ∧
      ker (absoluteValue T hT hcl) = ⊥ := by
  sorry

/--
For a unitary `U` and a densely defined `P`, `(U P)† = P† U⁻¹`. Here `U P` is
`U.compPMap P` (domain `Dom P`) and `P† U⁻¹` is the product `pmapMul` of `P†` with `U⁻¹`,
regarded as an operator with domain `H`.

Blueprint: lmm:adjoint-unitary-product
-/
theorem adjoint_unitary_compPMap (U : H ≃ₗᵢ[ℂ] H) {P : H →ₗ.[ℂ] H} (hP : HasDenseDomain P) :
    (U.toLinearEquiv.toLinearMap.compPMap P)† =
      pmapMul (P†) (U.symm.toLinearEquiv.toLinearMap.toPMap ⊤) := by
  sorry

/--
**Uniqueness of the polar decomposition.** Let `T` be closed and densely defined, and
`T = U P` with `U` unitary and `P` positive and self-adjoint. Then `P = |T|`, and `U |T| ψ = T ψ`
for `ψ ∈ Dom T`, so `U` is the isometry `V` of `lmm:polar-isometry`.
The blueprint also assumes `T` injective with dense range; the proof does not use it.

Blueprint: thrm:polar-decomposition-unique
-/
theorem polar_decomposition_unique {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed)
    (U : H ≃ₗᵢ[ℂ] H) {P : H →ₗ.[ℂ] H} (hP : IsSelfAdjoint P) (hpos : IsPositive P)
    (hTUP : T = U.toLinearEquiv.toLinearMap.compPMap P) :
    P = absoluteValue T hT hcl ∧
      ∀ (ψ : H) (h₁ : ψ ∈ T.domain) (h₂ : ψ ∈ (absoluteValue T hT hcl).domain),
        U (absoluteValue T hT hcl ⟨ψ, h₂⟩) = T ⟨ψ, h₁⟩ := by
  sorry

/-!
### Inverses

The inverse of an injective operator is Mathlib's `LinearPMap.inverse`, with graph the flip of
`Γ(A)` and domain `Range A`.
-/

/--
For an injective `A` and a unitary `U`, `U A` is injective and `(U A)⁻¹ = A⁻¹ U⁻¹`, where `U⁻¹`
is regarded as an operator with domain `H`.

Implementation note: `U` is unitary by design. For an antiunitary `W` the composite `W A` is
antilinear and Mathlib's `LinearPMap.inverse` is for linear maps; the one consumer of the
antiunitary case, `lmm:tomita-inverse-as-product`, states and proves it pointwise.

Blueprint: lmm:inverse-of-product-with-bijection
-/
theorem inverse_unitary_compPMap (U : H ≃ₗᵢ[ℂ] H) {A : H →ₗ.[ℂ] H} (hA : ker A = ⊥) :
    ker (U.toLinearEquiv.toLinearMap.compPMap A) = ⊥ ∧
      (U.toLinearEquiv.toLinearMap.compPMap A).inverse =
        pmapMul A.inverse (U.symm.toLinearEquiv.toLinearMap.toPMap ⊤) := by
  sorry

/--
For a self-adjoint injective `A`, the spectral measure has no atom at `0`: `μ^A({0}) = 0`.

Blueprint: lmm:injective-no-atom-at-zero
-/
theorem spectralMeasure_singleton_zero {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hinj : ker A = ⊥) : spectralMeasure hA {0} = 0 := by
  sorry

/--
For a self-adjoint injective `A` and `ι⁻(λ) = λ⁻¹` (with `ι⁻(0) = 0`, Lean's `0⁻¹ = 0`): for
`ψ ∈ Dom A`, `Aψ ∈ Dom ι⁻(A)` and `ι⁻(A) A ψ = ψ`.

Blueprint: lmm:inverse-fc-extends
-/
theorem functionalCalculus_inv_apply_self {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hinj : ker A = ⊥) (ψ : A.domain) :
    ∃ h : A ψ ∈ (functionalCalculus hA fun x => ((x⁻¹ : ℝ) : ℂ)).domain,
      functionalCalculus hA (fun x => ((x⁻¹ : ℝ) : ℂ)) ⟨A ψ, h⟩ = ψ := by
  sorry

/--
For a self-adjoint injective `A` and `ι⁻(λ) = λ⁻¹`: every `φ ∈ Dom ι⁻(A)` has
`ι⁻(A) φ ∈ Dom A` and `A ι⁻(A) φ = φ`; in particular `Dom ι⁻(A) ⊆ Range A`.

Blueprint: lmm:inverse-fc-domain
-/
theorem self_apply_functionalCalculus_inv {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hinj : ker A = ⊥) :
    (∀ φ : (functionalCalculus hA fun x => ((x⁻¹ : ℝ) : ℂ)).domain,
      ∃ h : functionalCalculus hA (fun x => ((x⁻¹ : ℝ) : ℂ)) φ ∈ A.domain,
        A ⟨_, h⟩ = φ) ∧
    (functionalCalculus hA fun x => ((x⁻¹ : ℝ) : ℂ)).domain ≤ range A := by
  sorry

/--
For a self-adjoint injective `A`, `A⁻¹ = ι⁻(A)` with `ι⁻(λ) = λ⁻¹`.

Blueprint: lmm:inverse-functional-calculus
-/
theorem inverse_eq_functionalCalculus_inv {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hinj : ker A = ⊥) :
    A.inverse = functionalCalculus hA fun x => ((x⁻¹ : ℝ) : ℂ) := by
  sorry

/--
For a self-adjoint `A`, `A^{1/2} = s(A)` (with `s = Real.sqrt`, which is `0` on `(-∞, 0]`) is
positive and self-adjoint.

Blueprint: lmm:square-root-positive
-/
theorem sqrt_functionalCalculus_positive {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    IsPositive (functionalCalculus hA fun x => ((Real.sqrt x : ℝ) : ℂ)) ∧
      IsSelfAdjoint (functionalCalculus hA fun x => ((Real.sqrt x : ℝ) : ℂ)) := by
  sorry

/--
For a positive, self-adjoint, injective `A`, `A^{1/2}` is injective.

Blueprint: lmm:square-root-injective
-/
theorem ker_sqrt_functionalCalculus {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) (hinj : ker A = ⊥) :
    ker (functionalCalculus hA fun x => ((Real.sqrt x : ℝ) : ℂ)) = ⊥ := by
  sorry

/--
For a self-adjoint `A` and `r(λ) = λ^{-1/2}` for `λ > 0`, `r(λ) = 0` otherwise (written
`(√λ)⁻¹`, which vanishes for `λ ≤ 0`), `A^{-1/2} = r(A)` is positive and self-adjoint.

Blueprint: lmm:inverse-square-root-positive
-/
theorem inv_sqrt_functionalCalculus_positive {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    IsPositive (functionalCalculus hA fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ)) ∧
      IsSelfAdjoint (functionalCalculus hA fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ)) := by
  sorry

/--
For a positive, self-adjoint, injective `A`, `(A^{1/2})⁻¹ = A^{-1/2}`.

Blueprint: crllr:inverse-square-root
-/
theorem inverse_sqrt_functionalCalculus {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) (hinj : ker A = ⊥) :
    (functionalCalculus hA fun x => ((Real.sqrt x : ℝ) : ℂ)).inverse =
      functionalCalculus hA fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ) := by
  sorry

/--
For a positive, self-adjoint `A` and `q(λ) = λ²`, `q(A^{1/2}) = A`.

Blueprint: lmm:square-of-square-root
-/
theorem sq_sqrt_functionalCalculus {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) :
    functionalCalculus (sqrt_functionalCalculus_positive hA).2 (fun x => (x : ℂ) ^ 2) = A := by
  sorry

/--
For a positive, self-adjoint, injective `A` and `q(λ) = λ²`, `q(A^{-1/2}) = A⁻¹`.

Blueprint: lmm:square-of-inverse-square-root
-/
theorem sq_inv_sqrt_functionalCalculus {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) (hinj : ker A = ⊥) :
    functionalCalculus (inv_sqrt_functionalCalculus_positive hA).2 (fun x => (x : ℂ) ^ 2) =
      A.inverse := by
  sorry

/-!
### Antiunitary conjugation
-/

/--
The conjugate `W A W⁻¹` of a linear partial map `A` by an antiunitary `W`: the linear partial map
with domain `W(Dom A) = {x | W⁻¹x ∈ Dom A}` and `(W A W⁻¹) x = W (A (W⁻¹ x))`. It is the
semilinear composite `W ∘ A ∘ W⁻¹` (`LinearPMap.comp`, `LinearMap.compPMap`), whose ring
homomorphism `conj ∘ id ∘ conj` is the identity.

Blueprint: def:product-of-unbounded-operators
-/
noncomputable def antiunitaryConj (W : H ≃ₗᵢ⋆[ℂ] H) (A : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H :=
  W.toLinearEquiv.toLinearMap.compPMap
    (A.comp
      (⟨A.domain.comap W.symm.toLinearEquiv.toLinearMap,
        W.symm.toLinearEquiv.toLinearMap.comp (Submodule.subtype _)⟩ :
        H →ₛₗ.[starRingEnd ℂ] H)
      (fun x => x.2))

section AntiunitaryPVM

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/--
For an antiunitary `W` and a projection-valued measure `μ`, `ν(E) = W μ(E) W⁻¹` is a
projection-valued measure, with associated measures `ν_ψ = μ_{W⁻¹ψ}`.

Implementation note: this is an existence statement, not a definition, so that the proof fields
of `ProjectionValuedMeasure` (self-adjointness of the conjugated projections in particular) stay
out of a `def`. The results below take a `ν` with `ν(E)x = W(μ(E)(W⁻¹x))`.

Blueprint: lmm:antiunitary-conjugate-pvm-is-pvm
-/
theorem exists_antiunitaryConj_pvm (W : H ≃ₗᵢ⋆[ℂ] H) (μ : ProjectionValuedMeasure X H) :
    ∃ ν : ProjectionValuedMeasure X H, (∀ E x, ν E x = W (μ E (W.symm x))) ∧
      ∀ ψ, ν.assoc ψ = μ.assoc (W.symm ψ) := by
  sorry

/--
With `ν(E) = W μ(E) W⁻¹`, the domains satisfy `W^ν_f = W(W^μ_f)` for measurable `f`:
`x ∈ W^ν_f ↔ W⁻¹x ∈ W^μ_f`.

Blueprint: lmm:antiunitary-conjugate-pvm-domain
-/
theorem mem_integralDomain_antiunitaryConj (W : H ≃ₗᵢ⋆[ℂ] H) {μ ν : ProjectionValuedMeasure X H}
    (hν : ∀ E x, ν E x = W (μ E (W.symm x))) {f : X → ℂ} (hf : Measurable f) (x : H) :
    x ∈ integralDomain ν f ↔ W.symm x ∈ integralDomain μ f := by
  sorry

/--
With `ν(E) = W μ(E) W⁻¹` and `f` real and measurable, `∫ f dν = W (∫ f dμ) W⁻¹`.

Blueprint: lmm:antiunitary-conjugate-pvm
-/
theorem pmapIntegral_antiunitaryConj (W : H ≃ₗᵢ⋆[ℂ] H) {μ ν : ProjectionValuedMeasure X H}
    (hν : ∀ E x, ν E x = W (μ E (W.symm x))) {f : X → ℝ} (hf : Measurable f) :
    pmapIntegral ν (fun x => (f x : ℂ)) =
      antiunitaryConj W (pmapIntegral μ fun x => (f x : ℂ)) := by
  sorry

end AntiunitaryPVM

/--
For an antiunitary `W` and a self-adjoint `A`, `W A W⁻¹` is self-adjoint, with spectral measure
`W μ^A(·) W⁻¹`.

Blueprint: lmm:antiunitary-conjugate-spectral-measure
-/
theorem spectralMeasure_antiunitaryConj (W : H ≃ₗᵢ⋆[ℂ] H) {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) :
    ∃ h : IsSelfAdjoint (antiunitaryConj W A),
      ∀ E x, spectralMeasure h E x = W (spectralMeasure hA E (W.symm x)) := by
  sorry

/--
For an antiunitary `W` and a self-adjoint `A`, `W f(A) W⁻¹ = f(W A W⁻¹)` for every real
measurable `f`.

Blueprint: crllr:antiunitary-conjugate-functional-calculus
-/
theorem functionalCalculus_antiunitaryConj (W : H ≃ₗᵢ⋆[ℂ] H) {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) :
    ∃ h : IsSelfAdjoint (antiunitaryConj W A), ∀ f : ℝ → ℝ, Measurable f →
      antiunitaryConj W (functionalCalculus hA fun x => (f x : ℂ)) =
        functionalCalculus h fun x => (f x : ℂ) := by
  sorry

omit [CompleteSpace H] in
/--
For an antiunitary `W`: if `A` is positive, so is `W A W⁻¹`; if `A` is injective, so is
`W A W⁻¹`.

Blueprint: lmm:antiunitary-conjugate-positive
-/
theorem antiunitaryConj_positive_injective (W : H ≃ₗᵢ⋆[ℂ] H) {A : H →ₗ.[ℂ] H} :
    (IsPositive A → IsPositive (antiunitaryConj W A)) ∧
      (ker A = ⊥ → ker (antiunitaryConj W A) = ⊥) := by
  sorry

end Unbounded
end Spectral
end Physicslib4
