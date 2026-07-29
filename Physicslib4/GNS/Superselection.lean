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
  simp only [add_apply, hS a x, hT a x, map_add]

theorem Intertwines.smul {T : H₁ →L[ℂ] H₂} (c : ℂ) (hT : Intertwines π₁ π₂ T) :
    Intertwines π₁ π₂ (c • T) := fun a x => by
  simp only [smul_apply, hT a x, map_smul]

/-- The composition of intertwiners is an intertwiner. -/
theorem Intertwines.comp {S : H₂ →L[ℂ] H₃} {T : H₁ →L[ℂ] H₂}
    (hS : Intertwines π₂ π₃ S) (hT : Intertwines π₁ π₂ T) :
    Intertwines π₁ π₃ (S.comp T) := fun a x => by
  simp only [ContinuousLinearMap.comp_apply]
  rw [hT a x, hS a (T x)]

/-- The adjoint of an intertwiner `π₁ → π₂` is an intertwiner `π₂ → π₁`. -/
theorem Intertwines.adjoint {T : H₁ →L[ℂ] H₂} (hT : Intertwines π₁ π₂ T) :
    Intertwines π₂ π₁ (ContinuousLinearMap.adjoint T) := fun a x => by
  have h := congrArg ContinuousLinearMap.adjoint
    (ContinuousLinearMap.ext (hT (star a)) :
      T.comp (π₁ (star a)) = (π₂ (star a)).comp T)
  simp only [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint] at h
  exact (DFunLike.congr_fun h x).symm

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
      zero_apply] using this
  exact hv (U.injective (hUv.trans (map_zero U).symm))

/-! ### Schur's lemma and the irreducible dichotomy -/

/-- For intertwiners `S, T : π₁ → π₂` the operator `S⋆ T` is a self-intertwiner of
`π₁`, so if `π₁` is irreducible it is a scalar: `S⋆ (T x) = z • x`. -/
private lemma exists_smul_adjoint_comp_of_isIrreducible (h1 : IsIrreducible π₁)
    {S T : H₁ →L[ℂ] H₂} (hS : Intertwines π₁ π₂ S) (hT : Intertwines π₁ π₂ T) :
    ∃ z : ℂ, ∀ x : H₁, (ContinuousLinearMap.adjoint S) (T x) = z • x := by
  -- (extracted by Fuse golfer)
  obtain ⟨z, hz⟩ := h1 ((ContinuousLinearMap.adjoint S).comp T)
    (fun a => ContinuousLinearMap.ext fun x => ((hS.adjoint.comp hT) a x).symm)
  exact ⟨z, fun x => by simpa using DFunLike.congr_fun hz x⟩

/-- **Schur's lemma.** A nonzero intertwiner between two irreducible representations
rescales to a unitary: `π₁` and `π₂` are unitarily equivalent. The operator `T⋆T`
commutes with `π₁`, hence is a positive scalar `r · 1`; the normalisation
`(√r)⁻¹ · T` is then a linear isometry, and `T T⋆` being a nonzero scalar makes it
surjective, i.e. a unitary equivalence. -/
theorem UnitaryEquiv.of_intertwines_of_isIrreducible
    (h1 : IsIrreducible π₁) (h2 : IsIrreducible π₂)
    {T : H₁ →L[ℂ] H₂} (hT : Intertwines π₁ π₂ T) (hT0 : T ≠ 0) :
    UnitaryEquiv π₁ π₂ := by
  obtain ⟨c, hTx⟩ := exists_smul_adjoint_comp_of_isIrreducible h1 hT hT
  obtain ⟨d, hTT⟩ := exists_smul_adjoint_comp_of_isIrreducible h2 hT.adjoint hT.adjoint
  rw [ContinuousLinearMap.adjoint_adjoint] at hTT
  obtain ⟨x₀, hx₀⟩ : ∃ x, T x ≠ 0 := by simpa using DFunLike.ne_iff.mp hT0
  -- `‖T x‖² = c.re ‖x‖²`, so `c.re =: r > 0`.
  have hnorm2 : ∀ x : H₁, ‖T x‖ ^ 2 = RCLike.re c * ‖x‖ ^ 2 := fun x => by
    have h0 : inner ℂ (T x) (T x) = c * inner ℂ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_right T x (T x), hTx x, inner_smul_right]
    have h1 := congrArg RCLike.re h0
    rwa [RCLike.mul_re, inner_self_im, mul_zero, sub_zero, inner_self_eq_norm_sq,
      inner_self_eq_norm_sq] at h1
  set r : ℝ := RCLike.re c with hr_def
  have hr_pos : 0 < r := by
    have hx2 : (0:ℝ) < ‖x₀‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr fun h => hx₀ (by rw [h, map_zero])) 2
    rw [← mul_div_cancel_right₀ r hx2.ne', ← hnorm2 x₀]
    exact div_pos (pow_pos (norm_pos_iff.mpr hx₀) 2) hx2
  have hsr : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
  -- `T (T⋆ (T x₀)) = c • T x₀ = d • T x₀`, so `d = c ≠ 0`.
  have hd0 : d ≠ 0 := by
    have h := hTT (T x₀)
    rw [hTx x₀, map_smul] at h
    rw [← sub_eq_zero, ← sub_smul, smul_eq_zero_iff_left hx₀, sub_eq_zero] at h
    rw [← h]
    exact fun h0 => hr_pos.ne' (by rw [hr_def, h0, map_zero])
  -- the rescaled isometry.
  have hfnorm : ∀ x : H₁, ‖((Real.sqrt r)⁻¹ : ℂ) • T x‖ = ‖x‖ := fun x => by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg r),
      ← Real.sqrt_sq (norm_nonneg (T x)), hnorm2 x, Real.sqrt_mul hr_pos.le,
      Real.sqrt_sq (norm_nonneg x), ← mul_assoc, inv_mul_cancel₀ hsr, one_mul]
  let fLI : H₁ →ₗᵢ[ℂ] H₂ :=
    { toLinearMap := ((Real.sqrt r)⁻¹ : ℂ) • (T : H₁ →ₗ[ℂ] H₂)
      norm_map' := hfnorm }
  -- `T` is surjective (from `T T⋆ = d • 1`, `d ≠ 0`), hence so is `fLI`.
  have hfsurj : Function.Surjective fLI := fun y => by
    refine ⟨d⁻¹ • (ContinuousLinearMap.adjoint T) (((Real.sqrt r) : ℂ) • y), ?_⟩
    change ((Real.sqrt r)⁻¹ : ℂ) • T (d⁻¹ • _) = y
    rw [map_smul, hTT, inv_smul_smul₀ hd0,
      inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hsr)]
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
  obtain ⟨a, hSx⟩ := exists_smul_adjoint_comp_of_isIrreducible h1 hS hS
  obtain ⟨b, hTx⟩ := exists_smul_adjoint_comp_of_isIrreducible h1 hS hT
  obtain ⟨c, hSS⟩ := exists_smul_adjoint_comp_of_isIrreducible h2 hS.adjoint hS.adjoint
  rw [ContinuousLinearMap.adjoint_adjoint] at hSS
  obtain ⟨x₀, hx₀⟩ : ∃ x, S x ≠ 0 := by simpa using DFunLike.ne_iff.mp hS0
  -- `a ≠ 0`, since `⟪S x₀, S x₀⟫ = a ⟪x₀, x₀⟫` and `S x₀ ≠ 0`.
  have ha0 : a ≠ 0 := fun haz => hx₀ ((inner_self_eq_zero (𝕜 := ℂ)).mp (by
    rw [← ContinuousLinearMap.adjoint_inner_right S x₀ (S x₀), hSx x₀, haz, zero_smul,
      inner_zero_right]))
  -- `S (S⋆ (S x₀)) = a • S x₀ = c • S x₀`, so `c = a ≠ 0`.
  have hca : c = a := by
    have h := hSS (S x₀)
    rw [hSx x₀, map_smul] at h
    rw [← sub_eq_zero, ← sub_smul, smul_eq_zero_iff_left hx₀, sub_eq_zero] at h
    exact h.symm
  -- `S (S⋆ (T x)) = b • S x = c • T x = a • T x`, so `T x = (b/a) • S x`.
  refine ⟨b / a, ContinuousLinearMap.ext fun x => ?_⟩
  have h := hSS (T x)
  rw [hTx x, map_smul, hca] at h
  rw [smul_apply, div_eq_mul_inv, mul_comm, ← smul_smul, h, inv_smul_smul₀ ha0]

/-! ### The endomorphism algebra of an irreducible representation -/

/-- A self-intertwiner is exactly an operator in the commutant of the representation. -/
theorem intertwines_self_iff_mem_centralizer {π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {T : H₁ →L[ℂ] H₁} : Intertwines π π T ↔ T ∈ Set.centralizer (Set.range π) := by
  rw [Set.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨a, rfl⟩
    ext x
    simpa only [mul_apply_eq_comp] using (h a x).symm
  · intro h a x
    simpa only [mul_apply_eq_comp] using
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

/-! ### Double-commutant duality -/

/-- **Double-commutant duality (I).** The commutant of the generated von Neumann
algebra `π(A)''` is the commutant von Neumann algebra `π(A)'`. This is the
triple-commutant collapse `S''' = S'` applied to the self-adjoint image `π(A)`. -/
theorem commutant_gnsVonNeumannAlgebra (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    (gnsVonNeumannAlgebra π).commutant = commutantVonNeumann π :=
  SetLike.coe_injective (by
    simp [gnsVonNeumann])

/-- **Double-commutant duality (II).** The commutant of the commutant von Neumann
algebra `π(A)'` is the generated von Neumann algebra `π(A)''` — this is exactly the
definition of the bicommutant. So `π(A)''` and `π(A)'` are each other's commutants. -/
theorem commutant_commutantVonNeumann (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    (commutantVonNeumann π).commutant = gnsVonNeumannAlgebra π :=
  SetLike.coe_injective (by
    simp [gnsVonNeumann])

/-- **A factor and its commutant.** A von Neumann algebra and its commutant share the
same center (their intersection is symmetric), so the generated algebra `π(A)''` is a
factor if and only if its commutant `π(A)'` is a factor. -/
theorem isFactor_gnsVonNeumann_iff_isFactor_commutant (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    IsFactor (gnsVonNeumann π) ↔
      IsFactor (commutantVonNeumann π : Set (H₁ →L[ℂ] H₁)) := by
  unfold IsFactor
  simp only [coe_commutantVonNeumann]
  unfold gnsVonNeumann
  simp only [Set.centralizer_centralizer_centralizer]
  constructor <;> intro h <;> rw [Set.inter_comm] at h <;> exact h

/-- **Triviality duality.** The commutant collapses to the scalars `π(A)' = ℂ · 1` if
and only if the generated algebra is everything `π(A)'' = B(H)`. This is the commutant
form of the equivalence "irreducible ⟺ generates `B(H)`". -/
theorem commutantVonNeumann_eq_scalars_iff_gnsVonNeumann_eq_univ
    (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    (commutantVonNeumann π : Set (H₁ →L[ℂ] H₁)) = scalarOperators H₁ ↔
      gnsVonNeumann π = Set.univ := by
  rw [← isIrreducible_iff_commutantVonNeumann_eq_scalars]
  exact isIrreducible_iff_gnsVonNeumann_eq_univ

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
  simp only [conjCLM_apply, mul_apply_eq_comp,
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
