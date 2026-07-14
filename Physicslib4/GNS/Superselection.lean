/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.UnitaryEquiv
import Physicslib4.GNS.RadonNikodym

/-!
# Disjointness and quasi-equivalence of representations

Building on `UnitaryEquiv`, this file introduces the two coarser comparisons of
`*`-representations from superselection theory:

* an **intertwiner** is a bounded operator `T : H₁ →L H₂` with `T π₁(a) = π₂(a) T`;
* two representations are **disjoint** (`AreDisjoint`) when the only intertwiner is
  `0` — equivalently, they share no unitarily equivalent subrepresentation;
* two representations are **quasi-equivalent** (`QuasiEquiv`) when there is a
  `*`-isomorphism of the generated von Neumann algebras `π₁(A)'' ≃⋆ₐ π₂(A)''`
  carrying `π₁(a)` to `π₂(a)`.

We prove the basic algebra of intertwiners, that disjointness is symmetric and
irreflexive (unitarily equivalent representations are never disjoint), that
quasi-equivalence is an equivalence relation, and that unitary equivalence implies
quasi-equivalence.
-/

namespace Physicslib4
namespace GNS

open scoped InnerProductSpace

variable {A : Type*} [CStarAlgebra A]
variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
variable {H₃ : Type*} [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]

/-! ### Intertwiners -/

/-- `T : H₁ →L H₂` **intertwines** `π₁` and `π₂` when `T π₁(a) = π₂(a) T`. -/
def Intertwines (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂))
    (T : H₁ →L[ℂ] H₂) : Prop :=
  ∀ (a : A) (x : H₁), T (π₁ a x) = π₂ a (T x)

variable {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)} {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)}
  {π₃ : A →⋆ₐ[ℂ] (H₃ →L[ℂ] H₃)}

theorem intertwines_zero : Intertwines π₁ π₂ (0 : H₁ →L[ℂ] H₂) := fun a x => by simp

theorem Intertwines.add {S T : H₁ →L[ℂ] H₂} (hS : Intertwines π₁ π₂ S)
    (hT : Intertwines π₁ π₂ T) : Intertwines π₁ π₂ (S + T) := fun a x => by
  simp only [ContinuousLinearMap.add_apply, hS a x, hT a x, map_add]

theorem Intertwines.smul {T : H₁ →L[ℂ] H₂} (c : ℂ) (hT : Intertwines π₁ π₂ T) :
    Intertwines π₁ π₂ (c • T) := fun a x => by
  simp only [ContinuousLinearMap.smul_apply, hT a x, map_smul]

/-- The composition of intertwiners is an intertwiner. -/
theorem Intertwines.comp {S : H₂ →L[ℂ] H₃} {T : H₁ →L[ℂ] H₂}
    (hS : Intertwines π₂ π₃ S) (hT : Intertwines π₁ π₂ T) :
    Intertwines π₁ π₃ (S.comp T) := fun a x => by
  simp only [ContinuousLinearMap.comp_apply]
  rw [hT a x, hS a (T x)]

/-- The adjoint of an intertwiner `π₁ → π₂` is an intertwiner `π₂ → π₁`. -/
theorem Intertwines.adjoint {T : H₁ →L[ℂ] H₂} (hT : Intertwines π₁ π₂ T) :
    Intertwines π₂ π₁ (ContinuousLinearMap.adjoint T) := by
  have hcomp : ∀ a : A, (ContinuousLinearMap.adjoint T).comp (π₂ a)
      = (π₁ a).comp (ContinuousLinearMap.adjoint T) := by
    intro a
    have h1 : T.comp (π₁ (star a)) = (π₂ (star a)).comp T :=
      ContinuousLinearMap.ext (fun x => hT (star a) x)
    have h2 := congrArg ContinuousLinearMap.adjoint h1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at h2
    have hp1 : ContinuousLinearMap.adjoint (π₁ (star a)) = π₁ a := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
    have hp2 : ContinuousLinearMap.adjoint (π₂ (star a)) = π₂ a := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
    rw [hp1, hp2] at h2
    exact h2.symm
  intro a x
  have hx := DFunLike.congr_fun (hcomp a) x
  simpa only [ContinuousLinearMap.comp_apply] using hx

/-! ### Disjointness -/

/-- Two representations are **disjoint** when the only operator intertwining them
is `0`. -/
def AreDisjoint (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) :
    Prop :=
  ∀ T : H₁ →L[ℂ] H₂, Intertwines π₁ π₂ T → T = 0

/-- Disjointness is symmetric (take adjoints of intertwiners). -/
theorem AreDisjoint.symm (h : AreDisjoint π₁ π₂) : AreDisjoint π₂ π₁ := by
  intro T hT
  have h0 : ContinuousLinearMap.adjoint T = 0 := h _ hT.adjoint
  rw [← ContinuousLinearMap.adjoint_adjoint T, h0, map_zero]

/-- A representation on a nonzero Hilbert space is never disjoint from itself (the
identity is a nonzero intertwiner). -/
theorem not_areDisjoint_self [Nontrivial H₁] (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    ¬ AreDisjoint π π := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : H₁)
  have h1 : (1 : H₁ →L[ℂ] H₁) = 0 := h 1 (fun a x => by simp)
  exact hv (by simpa using ContinuousLinearMap.ext_iff.mp h1 v)

/-- **Unitarily equivalent representations are not disjoint** (on nonzero spaces):
the implementing unitary is a nonzero intertwiner. -/
theorem UnitaryEquiv.not_areDisjoint [Nontrivial H₁] (h : UnitaryEquiv π₁ π₂) :
    ¬ AreDisjoint π₁ π₂ := by
  obtain ⟨U, hU⟩ := h
  intro hd
  have hint : Intertwines π₁ π₂ (↑U.toContinuousLinearEquiv : H₁ →L[ℂ] H₂) := by
    intro a x
    simp only [ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    exact hU a x
  have h0 : (↑U.toContinuousLinearEquiv : H₁ →L[ℂ] H₂) = 0 := hd _ hint
  obtain ⟨v, hv⟩ := exists_ne (0 : H₁)
  have hUv : U v = 0 := by
    have := ContinuousLinearMap.ext_iff.mp h0 v
    simpa only [ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearMap.zero_apply] using this
  exact hv (U.injective (hUv.trans (map_zero U).symm))

/-! ### Schur's lemma and the irreducible dichotomy -/

/-- **Schur's lemma.** A nonzero intertwiner between two irreducible representations
rescales to a unitary: `π₁` and `π₂` are unitarily equivalent. The operator `T⋆T`
commutes with `π₁`, hence is a positive scalar `r · 1`; the normalisation
`(√r)⁻¹ · T` is then a linear isometry, and `T T⋆` being a nonzero scalar makes it
surjective, i.e. a unitary equivalence. -/
theorem UnitaryEquiv.of_intertwines_of_isIrreducible
    (h1 : IsIrreducible π₁) (h2 : IsIrreducible π₂)
    {T : H₁ →L[ℂ] H₂} (hT : Intertwines π₁ π₂ T) (hT0 : T ≠ 0) :
    UnitaryEquiv π₁ π₂ := by
  obtain ⟨c, hc⟩ := h1 ((ContinuousLinearMap.adjoint T).comp T)
    (fun a => ContinuousLinearMap.ext fun x => ((hT.adjoint.comp hT) a x).symm)
  obtain ⟨d, hd⟩ := h2 (T.comp (ContinuousLinearMap.adjoint T))
    (fun a => ContinuousLinearMap.ext fun x => ((hT.comp hT.adjoint) a x).symm)
  -- `⟪T x, T x⟫ = c ⟪x, x⟫`.
  have hcT : ∀ x : H₁, inner ℂ (T x) (T x) = c * inner ℂ x x := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right T x (T x)]
    change inner ℂ x (((ContinuousLinearMap.adjoint T).comp T) x) = c * inner ℂ x x
    rw [hc]
    simp [inner_smul_right]
  -- a witness with `T x₀ ≠ 0`.
  obtain ⟨x₀, hx₀⟩ : ∃ x, T x ≠ 0 := by
    by_contra h; simp only [not_exists, not_not] at h
    exact hT0 (ContinuousLinearMap.ext fun x => by simp [h x])
  -- `‖T x‖² = c.re ‖x‖²`, so `c.re =: r > 0`.
  have hnorm2 : ∀ x : H₁, ‖T x‖ ^ 2 = RCLike.re c * ‖x‖ ^ 2 := by
    intro x
    have h0 := congrArg RCLike.re (hcT x)
    rwa [RCLike.mul_re, inner_self_im, mul_zero, sub_zero, inner_self_eq_norm_sq,
      inner_self_eq_norm_sq] at h0
  set r : ℝ := RCLike.re c with hr_def
  have hr_pos : 0 < r := by
    have := hnorm2 x₀
    have hx₀0 : x₀ ≠ 0 := fun h => hx₀ (by rw [h, map_zero])
    have hxpos : (0:ℝ) < ‖x₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx₀0) 2
    have hTpos : (0:ℝ) < ‖T x₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx₀) 2
    nlinarith [this, hxpos, hTpos]
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr_pos
  have hnorm : ∀ x : H₁, ‖T x‖ = Real.sqrt r * ‖x‖ := by
    intro x
    rw [← Real.sqrt_sq (norm_nonneg (T x)), hnorm2 x, Real.sqrt_mul hr_pos.le,
      Real.sqrt_sq (norm_nonneg x)]
  -- the rescaled isometry.
  have hfnorm : ∀ x : H₁, ‖((Real.sqrt r)⁻¹ : ℂ) • T x‖ = ‖x‖ := by
    intro x
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg r),
      hnorm x, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsr), one_mul]
  -- `T` is surjective (from `T T⋆ = d • 1`, `d ≠ 0`).
  have hdT : ∀ y : H₂,
      inner ℂ ((ContinuousLinearMap.adjoint T) y) ((ContinuousLinearMap.adjoint T) y)
        = d * inner ℂ y y := by
    intro y
    rw [← ContinuousLinearMap.adjoint_inner_right (ContinuousLinearMap.adjoint T) y
      ((ContinuousLinearMap.adjoint T) y), ContinuousLinearMap.adjoint_adjoint]
    change inner ℂ y ((T.comp (ContinuousLinearMap.adjoint T)) y) = d * inner ℂ y y
    rw [hd]
    simp [inner_smul_right]
  have hd0 : d ≠ 0 := by
    obtain ⟨y, hy⟩ : ∃ y, (ContinuousLinearMap.adjoint T) y ≠ 0 := by
      by_contra h; simp only [not_exists, not_not] at h
      have hadj : ContinuousLinearMap.adjoint T = 0 :=
        ContinuousLinearMap.ext fun x => by simp [h x]
      exact hx₀ (by rw [← ContinuousLinearMap.adjoint_adjoint T, hadj]; simp)
    intro hdz
    have hz := hdT y
    rw [hdz, zero_mul] at hz
    exact hy (inner_self_eq_zero.mp hz)
  have hTsurj : Function.Surjective T := by
    intro y
    refine ⟨d⁻¹ • (ContinuousLinearMap.adjoint T) y, ?_⟩
    rw [map_smul]
    have : T ((ContinuousLinearMap.adjoint T) y) = d • y := by
      have h' : T ((ContinuousLinearMap.adjoint T) y)
          = (T.comp (ContinuousLinearMap.adjoint T)) y := rfl
      rw [h', hd]; simp
    rw [this, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  -- bundle the isometry and its surjectivity.
  let fLI : H₁ →ₗᵢ[ℂ] H₂ :=
    { toLinearMap := ((Real.sqrt r)⁻¹ : ℂ) • (T : H₁ →ₗ[ℂ] H₂)
      norm_map' := hfnorm }
  have hfsurj : Function.Surjective fLI := by
    intro y
    obtain ⟨x, hx⟩ := hTsurj (((Real.sqrt r) : ℂ) • y)
    refine ⟨x, ?_⟩
    change ((Real.sqrt r)⁻¹ : ℂ) • T x = y
    rw [hx, smul_smul]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hsr),
      Complex.ofReal_one, one_smul]
  refine ⟨LinearIsometryEquiv.ofSurjective fLI hfsurj, fun a x => ?_⟩
  rw [LinearIsometryEquiv.coe_ofSurjective]
  change ((Real.sqrt r)⁻¹ : ℂ) • T (π₁ a x) = π₂ a (((Real.sqrt r)⁻¹ : ℂ) • T x)
  rw [hT a x, map_smul]

/-- **The irreducible dichotomy.** Two irreducible representations are either disjoint
or unitarily equivalent. -/
theorem areDisjoint_or_unitaryEquiv_of_isIrreducible
    (h1 : IsIrreducible π₁) (h2 : IsIrreducible π₂) :
    AreDisjoint π₁ π₂ ∨ UnitaryEquiv π₁ π₂ := by
  by_cases hd : AreDisjoint π₁ π₂
  · exact Or.inl hd
  · refine Or.inr ?_
    rw [AreDisjoint] at hd
    obtain ⟨T, hT'⟩ := not_forall.mp hd
    obtain ⟨hT, hT0⟩ := Classical.not_imp.mp hT'
    exact UnitaryEquiv.of_intertwines_of_isIrreducible h1 h2 hT hT0

/-- **Schur multiplicity.** The space of intertwiners between two irreducible
representations is at most one-dimensional: any two intertwiners with `S ≠ 0` are
proportional, `T = λ • S`. -/
theorem eq_smul_of_intertwines_of_isIrreducible
    (h1 : IsIrreducible π₁) (h2 : IsIrreducible π₂)
    {S T : H₁ →L[ℂ] H₂} (hS : Intertwines π₁ π₂ S) (hT : Intertwines π₁ π₂ T)
    (hS0 : S ≠ 0) : ∃ lam : ℂ, T = lam • S := by
  obtain ⟨a, ha⟩ := h1 ((ContinuousLinearMap.adjoint S).comp S)
    (fun x => ContinuousLinearMap.ext fun y => ((hS.adjoint.comp hS) x y).symm)
  obtain ⟨b, hb⟩ := h1 ((ContinuousLinearMap.adjoint S).comp T)
    (fun x => ContinuousLinearMap.ext fun y => ((hS.adjoint.comp hT) x y).symm)
  obtain ⟨c, hc⟩ := h2 (S.comp (ContinuousLinearMap.adjoint S))
    (fun x => ContinuousLinearMap.ext fun y => ((hS.comp hS.adjoint) x y).symm)
  obtain ⟨x₀, hx₀⟩ : ∃ x, S x ≠ 0 := by
    by_contra h; simp only [not_exists, not_not] at h
    exact hS0 (ContinuousLinearMap.ext fun x => by simp [h x])
  have ha0 : a ≠ 0 := by
    intro haz
    apply hx₀
    refine (inner_self_eq_zero (𝕜 := ℂ)).mp ?_
    rw [← ContinuousLinearMap.adjoint_inner_right S x₀ (S x₀)]
    change inner ℂ x₀ (((ContinuousLinearMap.adjoint S).comp S) x₀) = 0
    rw [ha, haz]; simp
  have hc0 : c ≠ 0 := by
    obtain ⟨y, hy⟩ : ∃ y, (ContinuousLinearMap.adjoint S) y ≠ 0 := by
      by_contra h; simp only [not_exists, not_not] at h
      have hadj : ContinuousLinearMap.adjoint S = 0 :=
        ContinuousLinearMap.ext fun x => by simp [h x]
      exact hx₀ (by rw [← ContinuousLinearMap.adjoint_adjoint S, hadj]; simp)
    intro hcz
    apply hy
    refine (inner_self_eq_zero (𝕜 := ℂ)).mp ?_
    rw [← ContinuousLinearMap.adjoint_inner_right (ContinuousLinearMap.adjoint S) y
      ((ContinuousLinearMap.adjoint S) y), ContinuousLinearMap.adjoint_adjoint]
    change inner ℂ y ((S.comp (ContinuousLinearMap.adjoint S)) y) = 0
    rw [hc, hcz]; simp
  refine ⟨b / a, ?_⟩
  -- `S⋆` is injective (from `S S⋆ = c • 1`, `c ≠ 0`).
  have hSadj_inj : Function.Injective (ContinuousLinearMap.adjoint S) := by
    intro u v huv
    have happ : (S.comp (ContinuousLinearMap.adjoint S)) u
        = (S.comp (ContinuousLinearMap.adjoint S)) v := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, huv]
    rw [hc] at happ
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at happ
    have hcuv : c • (u - v) = 0 := by rw [smul_sub, happ, sub_self]
    rcases smul_eq_zero.mp hcuv with h | h
    · exact absurd h hc0
    · exact sub_eq_zero.mp h
  -- `S⋆ ((T − (b/a) • S) x) = 0`, so by injectivity `T = (b/a) • S`.
  have hkey : ∀ x, (ContinuousLinearMap.adjoint S) ((T - (b / a) • S) x) = 0 := by
    intro x
    have hTx : (ContinuousLinearMap.adjoint S) (T x) = b • x := by
      have := DFunLike.congr_fun hb x
      simpa using this
    have hSx : (ContinuousLinearMap.adjoint S) (S x) = a • x := by
      have := DFunLike.congr_fun ha x
      simpa using this
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul,
      hTx, hSx, smul_smul, div_mul_cancel₀ b ha0, sub_self]
  have hzero : T - (b / a) • S = 0 := by
    ext x
    have hx := hkey x
    rw [← map_zero (ContinuousLinearMap.adjoint S)] at hx
    simpa using hSadj_inj hx
  exact sub_eq_zero.mp hzero

/-! ### The endomorphism algebra of an irreducible representation -/

/-- A self-intertwiner is exactly an operator in the commutant of the representation. -/
theorem intertwines_self_iff_mem_centralizer {π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {T : H₁ →L[ℂ] H₁} : Intertwines π π T ↔ T ∈ Set.centralizer (Set.range π) := by
  rw [Set.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨a, rfl⟩
    ext x
    simpa only [ContinuousLinearMap.mul_apply] using (h a x).symm
  · intro h a x
    simpa only [ContinuousLinearMap.mul_apply] using
      (DFunLike.congr_fun (h (π a) ⟨a, rfl⟩) x).symm

/-- **The endomorphism algebra of an irreducible representation is `ℂ · 1`.** Every
self-intertwiner of an irreducible representation is a scalar multiple of the
identity. -/
theorem intertwines_self_iff_isScalar {π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    (h : IsIrreducible π) {T : H₁ →L[ℂ] H₁} :
    Intertwines π π T ↔ ∃ c : ℂ, T = c • 1 := by
  rw [intertwines_self_iff_mem_centralizer, isIrreducible_iff_centralizer.mp h]
  exact Iff.rfl

/-! ### The commutant (self-intertwiner) von Neumann algebra -/

/-- **The commutant `π(A)'` as a von Neumann algebra**: the algebra of
self-intertwiners of `π` — its "gauge"/intertwiner algebra. The centralizer of
`π(A)` is self-adjoint, and a commutant is always a von Neumann algebra
(`S''' = S'`). -/
noncomputable def commutantVonNeumann (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    VonNeumannAlgebra H₁ :=
  vonNeumannOfSelfAdjoint (Set.centralizer (Set.range π))
    (fun _ hx => star_mem_setCentralizer (range_selfAdjoint π) hx)

@[simp] theorem coe_commutantVonNeumann (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    (commutantVonNeumann π : Set (H₁ →L[ℂ] H₁)) = Set.centralizer (Set.range π) := by
  unfold commutantVonNeumann
  rw [coe_vonNeumannOfSelfAdjoint, Set.centralizer_centralizer_centralizer]

/-- Membership in the commutant von Neumann algebra is exactly being a
self-intertwiner of `π`. -/
theorem mem_commutantVonNeumann_iff_intertwines
    {π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)} {T : H₁ →L[ℂ] H₁} :
    T ∈ commutantVonNeumann π ↔ Intertwines π π T := by
  rw [intertwines_self_iff_mem_centralizer, ← coe_commutantVonNeumann, SetLike.mem_coe]

/-- **A representation is irreducible iff its commutant von Neumann algebra is
trivial**, `π(A)' = ℂ · 1`. This is the von Neumann form of Schur's lemma: the
gauge/intertwiner algebra collapses to the scalars exactly for irreducibles. -/
theorem isIrreducible_iff_commutantVonNeumann_eq_scalars
    {π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)} :
    IsIrreducible π ↔
      (commutantVonNeumann π : Set (H₁ →L[ℂ] H₁)) = scalarOperators H₁ := by
  rw [coe_commutantVonNeumann]
  exact isIrreducible_iff_centralizer

/-! ### The pure-state dichotomy -/

/-- **The pure-state dichotomy.** The GNS representations of two pure states are
either disjoint or unitarily equivalent. Pure states thus fall into superselection
sectors: the sector of a pure state is the unitary-equivalence class of its
(irreducible) GNS representation. -/
theorem exists_gns_areDisjoint_or_unitaryEquiv_of_isPure.{u} {A : Type u} [CStarAlgebra A]
    {ω₁ ω₂ : State A} (h1 : IsPure ω₁) (h2 : IsPure ω₂) :
    ∃ (K₁ : Type u) (_ : NormedAddCommGroup K₁) (_ : InnerProductSpace ℂ K₁)
      (_ : CompleteSpace K₁) (π₁ : A →⋆ₐ[ℂ] (K₁ →L[ℂ] K₁)) (Ω₁ : K₁)
      (K₂ : Type u) (_ : NormedAddCommGroup K₂) (_ : InnerProductSpace ℂ K₂)
      (_ : CompleteSpace K₂) (π₂ : A →⋆ₐ[ℂ] (K₂ →L[ℂ] K₂)) (Ω₂ : K₂),
        (∀ a : A, (ω₁ a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ) ∧
        (∀ a : A, (ω₂ a : ℂ) = ⟪Ω₂, π₂ a Ω₂⟫_ℂ) ∧
        (AreDisjoint π₁ π₂ ∨ UnitaryEquiv π₁ π₂) := by
  obtain ⟨K₁, i1, i2, i3, π₁, Ω₁, hcyc₁, hrep₁, _⟩ := gns_construction ω₁
  obtain ⟨K₂, j1, j2, j3, π₂, Ω₂, hcyc₂, hrep₂, _⟩ := gns_construction ω₂
  refine ⟨K₁, i1, i2, i3, π₁, Ω₁, K₂, j1, j2, j3, π₂, Ω₂, hrep₁, hrep₂, ?_⟩
  exact areDisjoint_or_unitaryEquiv_of_isIrreducible
    ((isPure_iff_isIrreducible hcyc₁ hrep₁).mp h1)
    ((isPure_iff_isIrreducible hcyc₂ hrep₂).mp h2)

/-! ### Quasi-equivalence -/

omit [CompleteSpace H₁] [CompleteSpace H₂] in
theorem conjCLM_add (U : H₁ ≃ₗᵢ[ℂ] H₂) (S T : H₁ →L[ℂ] H₁) :
    conjCLM U (S + T) = conjCLM U S + conjCLM U T := by
  ext x; simp [map_add]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
theorem conjCLM_mul (U : H₁ ≃ₗᵢ[ℂ] H₂) (S T : H₁ →L[ℂ] H₁) :
    conjCLM U (S * T) = conjCLM U S * conjCLM U T := by
  ext x
  simp only [conjCLM_apply, ContinuousLinearMap.mul_apply,
    LinearIsometryEquiv.symm_apply_apply]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
theorem conjCLM_smul (U : H₁ ≃ₗᵢ[ℂ] H₂) (c : ℂ) (T : H₁ →L[ℂ] H₁) :
    conjCLM U (c • T) = c • conjCLM U T := by
  ext x; simp [map_smul]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
theorem conjCLM_leftInv (U : H₁ ≃ₗᵢ[ℂ] H₂) (T : H₁ →L[ℂ] H₁) :
    conjCLM U.symm (conjCLM U T) = T := by
  ext x; simp

/-- Conjugation by a unitary preserves the adjoint (star). -/
theorem conjCLM_star (U : H₁ ≃ₗᵢ[ℂ] H₂) (T : H₁ →L[ℂ] H₁) :
    conjCLM U (star T) = star (conjCLM U T) := by
  conv_rhs => rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [conjCLM_apply, conjCLM_apply, ContinuousLinearMap.star_eq_adjoint]
  calc ⟪U (ContinuousLinearMap.adjoint T (U.symm x)), y⟫_ℂ
      = ⟪U (ContinuousLinearMap.adjoint T (U.symm x)), U (U.symm y)⟫_ℂ := by
        rw [LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪ContinuousLinearMap.adjoint T (U.symm x), U.symm y⟫_ℂ :=
        LinearIsometryEquiv.inner_map_map U _ _
    _ = ⟪U.symm x, T (U.symm y)⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_left T (U.symm y) (U.symm x)
    _ = ⟪U (U.symm x), U (T (U.symm y))⟫_ℂ :=
        (LinearIsometryEquiv.inner_map_map U _ _).symm
    _ = ⟪x, U (T (U.symm y))⟫_ℂ := by rw [LinearIsometryEquiv.apply_symm_apply]

/-- Conjugation by a unitary as a `*`-algebra isomorphism of the operator
algebras. -/
noncomputable def conjStarAlgEquiv (U : H₁ ≃ₗᵢ[ℂ] H₂) :
    (H₁ →L[ℂ] H₁) ≃⋆ₐ[ℂ] (H₂ →L[ℂ] H₂) where
  toFun := conjCLM U
  invFun := conjCLM U.symm
  left_inv T := by ext x; simp
  right_inv S := by ext x; simp
  map_mul' := conjCLM_mul U
  map_add' := conjCLM_add U
  map_smul' := conjCLM_smul U
  map_star' := conjCLM_star U

@[simp] theorem conjStarAlgEquiv_apply (U : H₁ ≃ₗᵢ[ℂ] H₂) (T : H₁ →L[ℂ] H₁) :
    conjStarAlgEquiv U T = conjCLM U T := rfl

@[simp] theorem conjStarAlgEquiv_symm_apply (U : H₁ ≃ₗᵢ[ℂ] H₂) (S : H₂ →L[ℂ] H₂) :
    (conjStarAlgEquiv U).symm S = conjCLM U.symm S := rfl

/-- A `*`-isomorphism carrying the underlying set of one star-subalgebra onto that
of another restricts to a `*`-isomorphism between them (cross-space form). -/
def restrictStarAlgEquiv' {B C : Type*}
    [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    [Ring C] [StarRing C] [Algebra ℂ C] [StarModule ℂ C]
    (e : B ≃⋆ₐ[ℂ] C) {S : StarSubalgebra ℂ B} {T : StarSubalgebra ℂ C}
    (hfwd : ∀ x ∈ S, e x ∈ T) (hbwd : ∀ y ∈ T, e.symm y ∈ S) : S ≃⋆ₐ[ℂ] T where
  toFun x := ⟨e x, hfwd x x.2⟩
  invFun y := ⟨e.symm y, hbwd y y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)
  map_star' x := Subtype.ext (map_star e _)

theorem coe_gnsVonNeumann_toStarSubalgebra (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    ((gnsVonNeumannAlgebra π).toStarSubalgebra : Set (H₁ →L[ℂ] H₁)) = gnsVonNeumann π :=
  coe_gnsVonNeumannAlgebra π

/-- The generators `π(a)` lie in the generated von Neumann algebra `π(A)''`. -/
theorem pi_mem_gnsVonNeumann (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (a : A) :
    π a ∈ (gnsVonNeumannAlgebra π).toStarSubalgebra := by
  rw [← SetLike.mem_coe, coe_gnsVonNeumann_toStarSubalgebra]
  unfold gnsVonNeumann
  exact Set.mem_centralizer_iff.mpr
    (fun M hM => (Set.mem_centralizer_iff.mp hM (π a) ⟨a, rfl⟩).symm)

/-- Two representations are **quasi-equivalent** when there is a `*`-isomorphism of
their generated von Neumann algebras carrying `π₁(a)` to `π₂(a)`. -/
def QuasiEquiv (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) :
    Prop :=
  ∃ Φ : (gnsVonNeumannAlgebra π₁).toStarSubalgebra
          ≃⋆ₐ[ℂ] (gnsVonNeumannAlgebra π₂).toStarSubalgebra,
    ∀ a : A, (Φ ⟨π₁ a, pi_mem_gnsVonNeumann π₁ a⟩ : H₂ →L[ℂ] H₂) = π₂ a

/-- Quasi-equivalence is reflexive. -/
theorem QuasiEquiv.refl (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) : QuasiEquiv π π :=
  ⟨StarAlgEquiv.refl ℂ (gnsVonNeumannAlgebra π).toStarSubalgebra, fun _ => rfl⟩

/-- Quasi-equivalence is symmetric. -/
theorem QuasiEquiv.symm (h : QuasiEquiv π₁ π₂) : QuasiEquiv π₂ π₁ := by
  obtain ⟨Φ, hΦ⟩ := h
  refine ⟨Φ.symm, fun a => ?_⟩
  have hstep : Φ ⟨π₁ a, pi_mem_gnsVonNeumann π₁ a⟩
      = ⟨π₂ a, pi_mem_gnsVonNeumann π₂ a⟩ := Subtype.ext (hΦ a)
  rw [← hstep, StarAlgEquiv.symm_apply_apply]

/-- Quasi-equivalence is transitive. -/
theorem QuasiEquiv.trans (h₁₂ : QuasiEquiv π₁ π₂) (h₂₃ : QuasiEquiv π₂ π₃) :
    QuasiEquiv π₁ π₃ := by
  obtain ⟨Φ, hΦ⟩ := h₁₂
  obtain ⟨Ψ, hΨ⟩ := h₂₃
  refine ⟨Φ.trans Ψ, fun a => ?_⟩
  have hstep : Φ ⟨π₁ a, pi_mem_gnsVonNeumann π₁ a⟩
      = ⟨π₂ a, pi_mem_gnsVonNeumann π₂ a⟩ := Subtype.ext (hΦ a)
  rw [StarAlgEquiv.trans_apply, hstep]
  exact hΨ a

/-- **Unitary equivalence implies quasi-equivalence.** The conjugation
`*`-isomorphism restricts to a `*`-isomorphism of the generated von Neumann
algebras carrying `π₁(a)` to `π₂(a)`. -/
theorem UnitaryEquiv.quasiEquiv (h : UnitaryEquiv π₁ π₂) : QuasiEquiv π₁ π₂ := by
  obtain ⟨U, hU⟩ := h
  have hfwd : ∀ x ∈ (gnsVonNeumannAlgebra π₁).toStarSubalgebra,
      conjStarAlgEquiv U x ∈ (gnsVonNeumannAlgebra π₂).toStarSubalgebra := by
    intro T hT
    rw [← SetLike.mem_coe, coe_gnsVonNeumann_toStarSubalgebra] at hT ⊢
    rw [conjStarAlgEquiv_apply, conjMulEquiv_image_gnsVonNeumann hU]
    exact ⟨T, hT, (conjMulEquiv_apply U T)⟩
  have hbwd : ∀ y ∈ (gnsVonNeumannAlgebra π₂).toStarSubalgebra,
      (conjStarAlgEquiv U).symm y ∈ (gnsVonNeumannAlgebra π₁).toStarSubalgebra := by
    intro S hS
    rw [← SetLike.mem_coe, coe_gnsVonNeumann_toStarSubalgebra] at hS ⊢
    rw [conjMulEquiv_image_gnsVonNeumann hU] at hS
    obtain ⟨T, hT, rfl⟩ := hS
    rw [conjStarAlgEquiv_symm_apply, conjMulEquiv_apply, conjCLM_leftInv]
    exact hT
  refine ⟨restrictStarAlgEquiv' (conjStarAlgEquiv U) hfwd hbwd, fun a => ?_⟩
  change conjStarAlgEquiv U (π₁ a) = π₂ a
  rw [conjStarAlgEquiv_apply, ← conjMulEquiv_apply]
  exact conjMulEquiv_pi hU a

end GNS
end Physicslib4
