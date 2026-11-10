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
  ext F hF
  rw [Measure.map_apply hφ hF, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (measure_ne_top _ _), ProjectionValuedMeasure.assoc_apply _ _ hF,
    ProjectionValuedMeasure.assoc_apply _ _ (hφ hF), pushforwardPVM_apply μ hφ hF]

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
  refine ⟨Submodule.ext fun ψ => ?_, fun ψ _ => ?_⟩
  · rw [mem_integralDomain, mem_integralDomain, assoc_pushforwardPVM μ hφ ψ]
    exact memLp_map_measure_iff hg.aestronglyMeasurable hφ.aemeasurable
  · rw [assoc_pushforwardPVM μ hφ ψ]
    exact integral_map hφ.aemeasurable hg.aestronglyMeasurable

/--
For measurable `g : Y → ℂ`, `∫ g d(φ_*μ) = ∫ (g ∘ φ) dμ` as partial maps, including equality of
domains.

Blueprint: lmm:pushforward-pvm
-/
theorem pmapIntegral_pushforwardPVM (μ : ProjectionValuedMeasure X H) {φ : X → Y}
    (hφ : Measurable φ) {g : Y → ℂ} (hg : Measurable g) :
    pmapIntegral (pushforwardPVM μ φ hφ) g = pmapIntegral μ (g ∘ φ) := by
  obtain ⟨hdom, hint⟩ := integralDomain_pushforwardPVM μ hφ hg
  refine eq_pmapIntegral_of_inner_self μ (hg.comp hφ) _ hdom fun ψ => ?_
  rw [inner_self_pmapIntegral _ hg ψ, hint ψ ψ.2]
  rfl

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
  have hfA := (isSelfAdjoint_functionalCalculus_of_real hA hf).1
  have hμ : pushforwardPVM (spectralMeasure hA) f hf = spectralMeasure hfA :=
    eq_spectralMeasure_of_pmapIntegral hfA
      (pmapIntegral_pushforwardPVM _ hf Complex.measurable_ofReal)
  refine ⟨hfA, hμ.symm, fun g hg => ?_⟩
  change pmapIntegral (spectralMeasure hfA) g = pmapIntegral (spectralMeasure hA) (g ∘ f)
  rw [← hμ, pmapIntegral_pushforwardPVM _ hf hg]

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

open MeasureTheory in
/-- A positive self-adjoint operator has no spectral weight on `(−n, −1/n)`. -/
private theorem abs_spectralMeasure_Ioo_neg_eq_zero {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) (n : ℕ) (hn : 1 ≤ n) :
    spectralMeasure hA (Set.Ioo (-(n : ℝ)) (-(1 / (n : ℝ)))) = 0 := by
  set μ := spectralMeasure hA
  set E := Set.Ioo (-(n : ℝ)) (-(1 / (n : ℝ)))
  have hE : MeasurableSet E := measurableSet_Ioo
  have hf : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
  have hpos' : IsPositive (pmapIntegral μ (fun x : ℝ => (x : ℂ))) :=
    (pmapIntegral_spectralMeasure hA).symm ▸ hpos
  have hn' : (0 : ℝ) < 1 / n := by positivity
  ext ψ
  set η := μ E ψ
  have hη : η ∈ Set.range (μ E) := ⟨ψ, rfl⟩
  have hdom := range_subset_integralDomain μ hf hE (c := n) (fun x hx => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨hx.1.le, hx.2.le.trans (by linarith)⟩) hη
  have h1 : 0 ≤ (∫ x, (x : ℂ) ∂(μ.assoc η)).re := (hpos'.2 ⟨η, hdom⟩).trans_eq
    (congrArg Complex.re (inner_self_pmapIntegral μ hf ⟨η, hdom⟩))
  have hae : ∀ᵐ x ∂(μ.assoc η), x ∈ E :=
    (ae_iff (p := fun x => x ∈ E)).mpr (assoc_compl_eq_zero μ hE hη)
  have hint : Integrable (fun x : ℝ => x) (μ.assoc η) := by
    simpa using (MemLp.integrable one_le_two (mem_integralDomain μ |>.mp hdom)).re
  have h2 : ∫ x, x ∂(μ.assoc η) ≤ ∫ _, -(1 / (n : ℝ)) ∂(μ.assoc η) :=
    integral_mono_ae hint (integrable_const _) (hae.mono fun x hx => hx.2.le)
  rw [integral_const, smul_eq_mul, measureReal_def, assoc_univ_eq,
    ENNReal.toReal_ofReal (by positivity)] at h2
  have h3 : (∫ x, (x : ℂ) ∂(μ.assoc η)).re = ∫ x, x ∂(μ.assoc η) := by
    rw [integral_complex_ofReal]; rfl
  simp only [h3] at h1
  have : ‖η‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖η‖]
  simpa using this

/-- For a positive self-adjoint operator, every associated measure vanishes on `(−∞, 0)`. -/
private theorem abs_assoc_Iio_zero {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) (ψ : H) : (spectralMeasure hA).assoc ψ (Set.Iio 0) = 0 := by
  have hU : Set.Iio (0 : ℝ) ⊆
      ⋃ n : ℕ, Set.Ioo (-((n + 1 : ℕ) : ℝ)) (-(1 / ((n + 1 : ℕ) : ℝ))) := by
    intro x (hx : x < 0)
    obtain ⟨n, hn⟩ := exists_nat_gt (-x + 1 / (-x))
    have hx' : 0 < 1 / (-x) := one_div_pos.2 (neg_pos.2 hx)
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    refine Set.mem_iUnion.2 ⟨n, ?_, ?_⟩ <;> push_cast at hn1 ⊢
    · linarith
    · have : 1 / (n + 1 : ℝ) < -x := (one_div_lt hn1 (by linarith)).2 (by linarith)
      linarith
  exact MeasureTheory.measure_mono_null hU (MeasureTheory.measure_iUnion_null fun n => by
    rw [assoc_apply_eq_norm_sq _ ψ measurableSet_Ioo,
      abs_spectralMeasure_Ioo_neg_eq_zero hA hpos (n + 1) (by omega)]
    simp)

/-- The spectral measure of a positive self-adjoint operator vanishes on `(−∞, 0)`. -/
private theorem abs_spectralMeasure_Iio_zero_eq_zero {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) : spectralMeasure hA (Set.Iio 0) = 0 := by
  ext ψ
  have h0 := abs_assoc_Iio_zero hA hpos ψ
  rw [assoc_apply_eq_norm_sq _ ψ measurableSet_Iio, ENNReal.ofReal_eq_zero] at h0
  have : ‖spectralMeasure hA (Set.Iio 0) ψ‖ = 0 := by
    nlinarith [norm_nonneg (spectralMeasure hA (Set.Iio 0) ψ)]
  simpa using this

/--
For a closed, densely defined `T`, every `x ∈ Dom(T†T)` lies in `Dom |T|`.

Blueprint: lmm:adjoint-product-domain-in-sqrt-domain
-/
theorem adjointMulSelf_domain_le_absoluteValue {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) : (adjointMulSelf T).domain ≤ (absoluteValue T hT hcl).domain := by
  intro x hx
  have hA := (isSelfAdjoint_adjointMulSelf hT hcl).1
  rw [domain_eq_integralDomain_spectralMeasure hA, mem_integralDomain] at hx
  change MeasureTheory.MemLp (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ)) 2 ((spectralMeasure hA).assoc x)
  refine ((MeasureTheory.memLp_const (1 : ℝ)).add hx.norm).of_le
    (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, Pi.add_apply]
  have h2 : Real.sqrt t ^ 2 ≤ |t| := by
    rcases le_total 0 t with h | h
    · rw [Real.sq_sqrt h]; exact le_abs_self t
    · rw [Real.sqrt_eq_zero'.mpr h]; simp
  rw [abs_of_nonneg (Real.sqrt_nonneg t), abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt t - 1)]

/--
For a closed, densely defined `T` and `x ∈ Dom(T†T)`, `‖|T| x‖ = ‖T x‖`.

Blueprint: lmm:absolute-value-norm-on-core
-/
theorem norm_absoluteValue_of_mem_adjointMulSelf {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hcl : T.IsClosed) (x : (adjointMulSelf T).domain) :
    ‖absoluteValue T hT hcl ⟨x, adjointMulSelf_domain_le_absoluteValue hT hcl x.2⟩‖ =
      ‖T ⟨x, pmapMul_domain_le _ _ x.2⟩‖ := by
  have hA := (isSelfAdjoint_adjointMulSelf hT hcl).1
  set μ := spectralMeasure hA
  have hsq : Measurable fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hid : Measurable fun t : ℝ => (t : ℂ) := Complex.measurable_ofReal
  have hxid : (x : H) ∈ integralDomain μ (fun t : ℝ => (t : ℂ)) :=
    domain_eq_integralDomain_spectralMeasure hA ▸ x.2
  have h1 := norm_sq_pmapIntegral μ hsq ⟨x, adjointMulSelf_domain_le_absoluteValue hT hcl x.2⟩
  have h2 := inner_self_pmapIntegral μ hid ⟨x, hxid⟩
  have key : ∀ (B : H →ₗ.[ℂ] H) (_ : pmapIntegral μ (fun t : ℝ => (t : ℂ)) = B)
      (h' : (x : H) ∈ B.domain), pmapIntegral μ _ ⟨x, hxid⟩ = B ⟨x, h'⟩ := by
    intro B hB h'; subst hB; rfl
  have h4 : ⟪(x : H), adjointMulSelf T x⟫_ℂ = ∫ t, (t : ℂ) ∂(μ.assoc x) := by
    rw [← key _ (pmapIntegral_spectralMeasure hA) x.2]; exact h2
  rw [(inner_adjointMulSelf hT x).2, integral_complex_ofReal] at h4
  have hae : ∀ᵐ t ∂(μ.assoc x), ‖((Real.sqrt t : ℝ) : ℂ)‖ ^ 2 = t := by
    refine MeasureTheory.ae_iff.2 (MeasureTheory.measure_mono_null (fun t ht => ?_)
      (abs_assoc_Iio_zero hA (isSelfAdjoint_adjointMulSelf hT hcl).2.2 x))
    by_contra h
    exact ht (by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (not_lt.mp h)])
  rw [MeasureTheory.integral_congr_ae hae] at h1
  have h3 : ‖T ⟨x, pmapMul_domain_le _ _ x.2⟩‖ ^ 2 = ∫ t, t ∂(μ.assoc x) := by exact_mod_cast h4
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  exact h1.trans h3.symm

/--
For a closed, densely defined `T`, `|T|` is positive and self-adjoint, hence closed, and
`Dom(T†T)` is a core for `|T|`.

Blueprint: lmm:absolute-value-closed
-/
theorem absoluteValue_closed {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T) (hcl : T.IsClosed) :
    IsPositive (absoluteValue T hT hcl) ∧ IsSelfAdjoint (absoluteValue T hT hcl) ∧
      (absoluteValue T hT hcl).IsClosed ∧
      (absoluteValue T hT hcl).HasCore (adjointMulSelf T).domain := by
  have hA := (isSelfAdjoint_adjointMulSelf hT hcl).1
  have hsqrt : Measurable Real.sqrt := Real.continuous_sqrt.measurable
  have hsq : Measurable fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ) := Complex.measurable_ofReal.comp hsqrt
  obtain ⟨hsa, hcl'⟩ := isSelfAdjoint_functionalCalculus_of_real hA hsqrt
  refine ⟨⟨(isSymmetric_iff_le_adjoint hsa.dense_domain).mpr
    (LinearPMap.isSelfAdjoint_def.mp hsa).ge, fun ψ => ?_⟩, hsa, hcl', ?_⟩
  · change 0 ≤ (⟪(ψ : H), pmapIntegral (spectralMeasure hA)
      (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ)) ψ⟫_ℂ).re
    rw [inner_self_pmapIntegral _ hsq ψ, integral_complex_ofReal, Complex.ofReal_re]
    exact MeasureTheory.integral_nonneg fun t => Real.sqrt_nonneg t
  · have h := (hasCore_functionalCalculus hA hsqrt).1
    have he : (adjointMulSelf T).domain ⊓
        (functionalCalculus hA fun x => ((Real.sqrt x : ℝ) : ℂ)).domain =
          (adjointMulSelf T).domain :=
      inf_eq_left.mpr (adjointMulSelf_domain_le_absoluteValue hT hcl)
    rw [he] at h
    exact h

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
  suffices key : ∀ ψ (hψ : ψ ∈ A.domain), ∃ χ, (ψ, χ) ∈ B.graph ∧ ‖A ⟨ψ, hψ⟩‖ = ‖χ‖ by
    refine ⟨fun ψ hψ => ?_, fun ψ hψA hψB => ?_⟩
    · obtain ⟨χ, hχ, -⟩ := key ψ hψ
      obtain ⟨z, hz, -⟩ := B.mem_graph_iff.1 hχ
      have hz' : (z : H) = ψ := hz
      exact hz' ▸ z.2
    · obtain ⟨χ, hχ, hn⟩ := key ψ hψA
      obtain ⟨z, hz, hzχ⟩ := B.mem_graph_iff.1 hχ
      have hzχ' : B z = χ := hzχ
      rw [hn, ← hzχ']
      exact congrArg (‖B ·‖) (Subtype.ext hz)
  intro ψ hψ
  have hmem : (ψ, A ⟨ψ, hψ⟩) ∈ (A.domRestrict D).graph.topologicalClosure := by
    rw [(hA.isClosable.leIsClosable (A.domRestrict_le)).graph_closure_eq_closure_graph,
      hD.closure_eq]
    exact A.mem_graph ⟨ψ, hψ⟩
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose y hy1 hy2 using fun n => (A.domRestrict D).mem_graph_iff.1 (hu n)
  set a : ℕ → H := fun n => A ⟨y n, (y n).2.2⟩ with ha_def
  set b : ℕ → H := fun n => B ⟨y n, hDB (y n).2.1⟩ with hb_def
  have hau : ∀ n, a n = (u n).2 := fun n => by
    rw [← hy2 n]; exact (LinearPMap.domRestrict_apply rfl).symm
  have hx : Filter.Tendsto (fun n => ((y n : H))) Filter.atTop (nhds ψ) := by
    exact ((continuous_fst.tendsto _).comp hlim).congr fun n => (hy1 n).symm
  have ha : Filter.Tendsto a Filter.atTop (nhds (A ⟨ψ, hψ⟩)) := by
    exact ((continuous_snd.tendsto _).comp hlim).congr fun n => (hau n).symm
  have hdist : ∀ m n, dist (b m) (b n) = dist (a m) (a n) := fun m n => by
    have := hnorm ((y m : H) - y n) (sub_mem (y m).2.2 (y n).2.2)
      (sub_mem (hDB (y m).2.1) (hDB (y n).2.1)) (sub_mem (y m).2.1 (y n).2.1)
    rw [dist_eq_norm, dist_eq_norm, ha_def, hb_def]
    dsimp only
    rw [← LinearPMap.map_sub, ← LinearPMap.map_sub]
    exact this.symm
  have hb : CauchySeq b := Metric.cauchySeq_iff.2 fun ε hε =>
    (Metric.cauchySeq_iff.1 ha.cauchySeq ε hε).imp fun N h m hm n hn =>
      (hdist m n) ▸ h m hm n hn
  obtain ⟨χ, hχ⟩ := cauchySeq_tendsto_of_complete hb
  refine ⟨χ, hB.mem_of_tendsto (hx.prodMk_nhds hχ)
    (Filter.Eventually.of_forall fun n => B.mem_graph ⟨y n, hDB (y n).2.1⟩), ?_⟩
  refine tendsto_nhds_unique ha.norm ?_
  have : ∀ n, ‖a n‖ = ‖b n‖ := fun n => hnorm _ _ _ (y n).2.1
  simpa only [this] using hχ.norm

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
  have h1 := domain_le_of_hasCore_norm_eq hA hB hDA hDB.le_domain hnorm
  have h2 := domain_le_of_hasCore_norm_eq hB hA hDB hDA.le_domain
    fun ψ hψB hψA hψ => (hnorm ψ hψA hψB hψ).symm
  exact ⟨le_antisymm h1.1 h2.1, h1.2⟩

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
  obtain ⟨hp, hsa, hc, hcore⟩ := absoluteValue_closed hT hcl
  obtain ⟨hd, hn⟩ := domain_eq_of_hasCore_norm_eq hc hcl hcore
    (hasCore_domain_adjointMulSelf hT hcl)
    fun ψ _ _ hψ => norm_absoluteValue_of_mem_adjointMulSelf hT hcl ⟨ψ, hψ⟩
  exact ⟨hp, hsa, hd, hn⟩

/--
For a positive self-adjoint `P`, the product `P P` is self-adjoint and `(P P)^{1/2} = P`.

Blueprint: lmm:positive-square-root-unique
-/
theorem sqrt_pmapMul_self {P : H →ₗ.[ℂ] H} (hP : IsSelfAdjoint P) (hpos : IsPositive P) :
    ∃ hPP : IsSelfAdjoint (pmapMul P P),
      functionalCalculus hPP (fun x => ((Real.sqrt x : ℝ) : ℂ)) = P := by
  set μ := spectralMeasure hP
  set i : ℝ → ℂ := fun x => (x : ℂ)
  have hi : Measurable i := Complex.measurable_ofReal
  have hid : pmapIntegral μ i = P := functionalCalculus_id hP
  -- `W_{x²} ⊆ W_x`, since `|x| ≤ 1 + |x|²` and the measures are finite
  have hdom : ∀ ψ, ψ ∈ integralDomain μ (i * i) → ψ ∈ integralDomain μ i := fun ψ h => by
    have : MeasureTheory.IsFiniteMeasure (μ.assoc ψ) :=
      ⟨by rw [assoc_univ_eq]; exact ENNReal.ofReal_lt_top⟩
    rw [mem_integralDomain] at h ⊢
    refine ((MeasureTheory.memLp_const (1 : ℂ)).add h).of_le hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    change ‖(x : ℂ)‖ ≤ ‖(1 : ℂ) + (x : ℂ) * (x : ℂ)‖
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [mul_self_nonneg x] : (0 : ℝ) ≤ 1 + x * x)]
    nlinarith [abs_nonneg x, abs_mul_abs_self x, sq_nonneg (|x| - 1)]
  have hsq : pmapMul P P = functionalCalculus hP fun x => ((x ^ 2 : ℝ) : ℂ) := by
    have hfun : (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) = i * i := by
      funext x; simp [i, sq]
    rw [functionalCalculus, hfun]
    have key : pmapMul (pmapIntegral μ i) (pmapIntegral μ i) = pmapIntegral μ (i * i) := by
      obtain ⟨-, hval⟩ := pmapIntegral_comp μ hi hi
      refine LinearPMap.ext ?_ fun x hx hx' => ?_
      · ext ψ
        rw [mem_domain_pmapMul_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact (pmapIntegral_mem_integralDomain_iff μ hi hi ⟨ψ, h1⟩).1 h2
        · intro h
          exact ⟨hdom ψ h, (pmapIntegral_mem_integralDomain_iff μ hi hi ⟨ψ, hdom ψ h⟩).2 h⟩
      · obtain ⟨h1, h2⟩ := (mem_domain_pmapMul_iff _ _ _).1 hx
        rw [pmapMul_apply _ _ ⟨x, hx⟩ h2]
        obtain ⟨hfg, he⟩ := hval ⟨x, h1⟩ h2
        exact he.symm
    rw [hid] at key
    exact key
  have hsa := (isSelfAdjoint_functionalCalculus_of_real hP (f := fun x => x ^ 2)
    (measurable_id.pow_const 2)).1
  refine ⟨hsq ▸ hsa, ?_⟩
  obtain ⟨hfA, -, hcomp⟩ := functionalCalculus_functionalCalculus hP
    (f := fun x => x ^ 2) (measurable_id.pow_const 2)
  have htr : ∀ {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B), A = B →
      functionalCalculus hA (fun x => ((Real.sqrt x : ℝ) : ℂ)) =
        functionalCalculus hB (fun x => ((Real.sqrt x : ℝ) : ℂ)) := by
    rintro _ _ _ _ rfl; rfl
  rw [htr _ hfA hsq, hcomp (fun x => ((Real.sqrt x : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)]
  conv_rhs => rw [← functionalCalculus_id hP]
  refine pmapIntegral_congr_of_null μ
    ((Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).comp
      (measurable_id.pow_const 2)) hi measurableSet_Iio
    (abs_spectralMeasure_Iio_zero_eq_zero hP hpos) fun x hx => ?_
  simp only [Set.mem_Iio, not_lt] at hx
  simp [Function.comp, Real.sqrt_sq hx]

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
  obtain ⟨-, hsa, hd, hn⟩ := absoluteValue_domain hT hcl
  have hker : ker (absoluteValue T hT hcl) = ⊥ := by
    rw [Submodule.eq_bot_iff] at hinj ⊢
    rintro ψ hψ
    obtain ⟨h₁, h0⟩ := mem_ker.1 hψ
    have h₂ : ψ ∈ T.domain := hd ▸ h₁
    refine hinj ψ (mem_ker.2 ⟨h₂, norm_eq_zero.1 ?_⟩)
    rw [← hn ψ h₁ h₂, h0, norm_zero]
  refine ⟨hker, ?_⟩
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    orthogonal_range_eq_ker_adjoint (absoluteValue_closed hT hcl).2.1.dense_domain,
    LinearPMap.isSelfAdjoint_def.mp hsa, hker]

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
  obtain ⟨-, -, hd, hn⟩ := absoluteValue_domain hT hcl
  set A := absoluteValue T hT hcl
  let B : A.domain →ₗ[ℂ] H := T.toFun.comp (Submodule.inclusion hd.le)
  have hBA : ∀ ψ : A.domain, ‖B ψ‖ = ‖A.toFun ψ‖ := fun ψ => (hn ψ ψ.2 (hd ▸ ψ.2)).symm
  have hker : LinearMap.ker A.toFun ≤ LinearMap.ker B := fun ψ h => by
    rw [LinearMap.mem_ker] at h ⊢
    rw [← norm_eq_zero, hBA, h, norm_zero]
  let L : range A →ₗ[ℂ] H := (LinearMap.ker A.toFun).liftQ B hker ∘ₗ
    (LinearMap.quotKerEquivRange A.toFun).symm.toLinearMap
  have hL : ∀ ψ : A.domain, L ⟨A.toFun ψ, LinearMap.mem_range_self _ ψ⟩ = B ψ := by
    intro ψ
    have : (LinearMap.quotKerEquivRange A.toFun).symm ⟨A.toFun ψ, LinearMap.mem_range_self _ ψ⟩
        = Submodule.Quotient.mk ψ := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    change (LinearMap.ker A.toFun).liftQ B hker
      ((LinearMap.quotKerEquivRange A.toFun).symm ⟨A.toFun ψ, LinearMap.mem_range_self _ ψ⟩) = B ψ
    rw [this]
    rfl
  refine ⟨{ L with norm_map' := ?_ }, fun ψ h₁ h₂ => hL ⟨ψ, h₂⟩⟩
  rintro ⟨_, ψ, rfl⟩
  exact (congrArg norm (hL ψ)).trans (hBA ψ)

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
  set A := absoluteValue T hT hcl
  obtain ⟨-, -, hd, -⟩ := absoluteValue_domain hT hcl
  obtain ⟨V₀, hV₀⟩ := exists_polarIsometry_on_range hT hcl hinj
  have hden := (absoluteValue_injective_denseRange hT hcl hinj).2
  have hdr : DenseRange (range A).subtypeL := hden.denseRange_val
  have hui : IsUniformInducing (range A).subtypeL :=
    isUniformEmbedding_subtype_val.isUniformInducing
  let V := V₀.toContinuousLinearMap.extend (range A).subtypeL
  have hVe : ∀ x : range A, V x = V₀ x := fun x =>
    ContinuousLinearMap.extend_eq V₀.toContinuousLinearMap hdr hui x
  have hP : ∀ V' : H →L[ℂ] H, (∀ (ψ : H) (h₁ : ψ ∈ T.domain) (h₂ : ψ ∈ A.domain),
      V' (A ⟨ψ, h₂⟩) = T ⟨ψ, h₁⟩) ↔ ∀ x : range A, V' x = V₀ x := by
    intro V'
    constructor
    · rintro h ⟨_, ψ, rfl⟩
      exact (h ψ (hd ▸ ψ.2) ψ.2).trans (hV₀ ψ _ ψ.2).symm
    · intro h ψ h₁ h₂
      exact (h _).trans (hV₀ ψ h₁ h₂)
  have huniq : ∀ V' : H →L[ℂ] H, (∀ x : range A, V' x = V₀ x) → V' = V := fun V' h =>
    ContinuousLinearMap.ext (congrFun (hdr.equalizer V'.continuous V.continuous
      (funext fun x => (h x).trans (hVe x).symm)))
  have hiso : ∀ x, ‖V x‖ = ‖x‖ := fun x =>
    hdr.induction_on x (isClosed_eq (continuous_norm.comp V.continuous) continuous_norm)
      fun a => by
        change ‖V a‖ = ‖(a : H)‖
        rw [hVe, LinearIsometry.norm_map, Submodule.norm_coe]
  exact ⟨⟨V, (hP V).2 hVe, fun V' h => huniq V' ((hP V').1 h)⟩,
    fun V' h x => huniq V' ((hP V').1 h) ▸ hiso x⟩

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
  obtain ⟨⟨V, hV, -⟩, hiso⟩ := existsUnique_polarIsometry hT hcl hinj
  obtain ⟨hp, hsa, hd, -⟩ := absoluteValue_domain hT hcl
  let L : H →ₗᵢ[ℂ] H := { V.toLinearMap with norm_map' := hiso V hV }
  have hsurj : Function.Surjective L := by
    have hsub : (range T : Set H) ⊆ Set.range L := by
      rintro _ ⟨ψ, rfl⟩
      exact ⟨_, hV ψ ψ.2 (by rw [hd]; exact ψ.2)⟩
    have hcl' : IsClosed (Set.range L) := (Isometry.isClosedEmbedding L.isometry).isClosed_range
    have := hran.closure_eq ▸ closure_minimal hsub hcl'
    exact fun y => this (Set.mem_univ y)
  exact ⟨LinearIsometryEquiv.ofSurjective L hsurj, hd, fun ψ h₁ h₂ => hV ψ h₁ h₂, hp, hsa,
    (absoluteValue_injective_denseRange hT hcl hinj).1⟩


/--
For a unitary `U` and a densely defined `P`, `(U P)† = P† U⁻¹`. Here `U P` is
`U.compPMap P` (domain `Dom P`) and `P† U⁻¹` is the product `pmapMul` of `P†` with `U⁻¹`,
regarded as an operator with domain `H`.

Blueprint: lmm:adjoint-unitary-product
-/
theorem adjoint_unitary_compPMap (U : H ≃ₗᵢ[ℂ] H) {P : H →ₗ.[ℂ] H} (hP : HasDenseDomain P) :
    (U.toLinearEquiv.toLinearMap.compPMap P)† =
      pmapMul (P†) (U.symm.toLinearEquiv.toLinearMap.toPMap ⊤) := by
  set Q := U.toLinearEquiv.toLinearMap.compPMap P
  have hQ : Dense (Q.domain : Set H) := hP
  have key : ∀ (y : H) (x : P.domain), ⟪y, Q ⟨x, x.2⟩⟫_ℂ = ⟪U.symm y, P x⟫_ℂ := fun y x => by
    rw [← U.inner_map_map (U.symm y), U.apply_symm_apply]; rfl
  have hdom : ∀ y : H, y ∈ Q†.domain ↔ U.symm y ∈ P†.domain := fun y => by
    constructor
    · intro hy
      refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨Q† ⟨y, hy⟩, fun x => ?_⟩
      rw [← key]
      exact LinearPMap.adjoint_isFormalAdjoint hQ ⟨y, hy⟩ ⟨x, x.2⟩
    · intro hy
      refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨P† ⟨U.symm y, hy⟩, fun x => ?_⟩
      rw [key y ⟨x, x.2⟩]
      exact LinearPMap.adjoint_isFormalAdjoint hP ⟨U.symm y, hy⟩ ⟨x, x.2⟩
  have hdom' : Q†.domain = (pmapMul (P†) (U.symm.toLinearEquiv.toLinearMap.toPMap ⊤)).domain := by
    ext y
    rw [hdom, mem_domain_pmapMul_iff]
    exact ⟨fun h => ⟨Submodule.mem_top, h⟩, fun ⟨_, h⟩ => h⟩
  refine LinearPMap.ext hdom' fun y hy1 hy2 => ?_
  have hy : U.symm y ∈ P†.domain := (hdom y).1 hy1
  rw [pmapMul_apply _ _ ⟨y, hy2⟩ hy]
  refine LinearPMap.adjoint_apply_eq hQ ⟨y, hy1⟩ fun z => ?_
  change _ = ⟪y, Q ⟨z, z.2⟩⟫_ℂ
  rw [key y ⟨z, z.2⟩]
  exact LinearPMap.adjoint_isFormalAdjoint hP ⟨U.symm y, hy⟩ ⟨z, z.2⟩

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
  subst hTUP
  have hPadj : P† = P := LinearPMap.isSelfAdjoint_def.mp hP
  have hdP : HasDenseDomain P := hT
  have heq : adjointMulSelf (U.toLinearEquiv.toLinearMap.compPMap P) = pmapMul P P := by
    unfold adjointMulSelf
    rw [adjoint_unitary_compPMap U hdP, hPadj]
    refine LinearPMap.ext ?_ fun x hx hx' => ?_
    · ext x
      simp only [mem_domain_pmapMul_iff]
      constructor
      · rintro ⟨h1, _, h2⟩
        refine ⟨h1, ?_⟩
        convert h2 using 1
        simp [LinearMap.compPMap_apply, LinearMap.toPMap_apply]
        rfl
      · rintro ⟨h1, h2⟩
        refine ⟨h1, Submodule.mem_top, ?_⟩
        convert h2 using 1
        simp [LinearMap.compPMap_apply, LinearMap.toPMap_apply]
        rfl
    · obtain ⟨h1, h2⟩ := (mem_domain_pmapMul_iff _ _ _).1 hx'
      rw [pmapMul_apply _ _ ⟨x, hx'⟩ h2]
      obtain ⟨h3, h4⟩ := (mem_domain_pmapMul_iff _ _ _).1 hx
      rw [pmapMul_apply _ _ ⟨x, hx⟩ h4]
      obtain ⟨_, h5⟩ := (mem_domain_pmapMul_iff _ _ _).1 h4
      rw [pmapMul_apply _ _ ⟨_, h4⟩ h5]
      congr 2
      simp [LinearMap.compPMap_apply, LinearMap.toPMap_apply]
      rfl
  obtain ⟨hPP, hsq⟩ := sqrt_pmapMul_self hP hpos
  have htr : ∀ {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B), A = B →
      functionalCalculus hA (fun x => ((Real.sqrt x : ℝ) : ℂ)) =
        functionalCalculus hB (fun x => ((Real.sqrt x : ℝ) : ℂ)) := by
    rintro _ _ _ _ rfl; rfl
  have habs : P = absoluteValue _ hT hcl :=
    (hsq.symm.trans (htr hPP _ heq.symm))
  refine ⟨habs, fun ψ h₁ h₂ => ?_⟩
  have hval : ∀ A : H →ₗ.[ℂ] H, P = A → ∀ h₂ h₁, A ⟨ψ, h₂⟩ = P ⟨ψ, h₁⟩ := by
    rintro _ rfl _ _; rfl
  rw [hval _ habs h₂ h₁, LinearMap.compPMap_apply]
  rfl

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
