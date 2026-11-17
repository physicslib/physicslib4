/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Physicslib4.AQFT.HaagKastler.VacuumState
import Physicslib4.Spacetime.LorentzCausality
import Physicslib4.Spacetime.MinkowskiCausalCone

/-!
# Wedges and boosts in standard Minkowski spacetime

The right wedge `W_R = {x | |x⁰| < x¹}`, the left wedge `W_L = {x | x¹ < -|x⁰|}`, and the wedges
`g W_R` for `g` in the restricted Poincaré group `InhomogeneousLorentzGroup`. Wedges are not a
class of regions of the net axioms, which are indexed by diamonds (`IsAlexandrovBasisSet`) only:
a wedge is a subset of spacetime used only to index the region algebras of `RegionAlgebra.lean`.

The boost matrices `Λ(s)` act on the `(x⁰, x¹)`-plane with rapidity `s`, normalised by
`Λ(s) l₊ = eˢ l₊` and `Λ(s) l₋ = e⁻ˢ l₋` for the lightlike vectors `l₊ = (1, 1, 0, 0)` and
`l₋ = (1, -1, 0, 0)`. The boost of the right wedge is `b(s) = (Λ(s), 0)`, and the boost of the
wedge `g W_R` along `g` is `b_g(s) = g b(s) g⁻¹`; it is indexed by `g`, not by the wedge.

Conventions:
* Wedges are sets of `StandardMinkowskiSpacetime.Carrier`, on which the Poincaré group acts;
  coordinates are read on the definitionally equal `SpacetimeModel = EuclideanSpace ℝ (Fin 4)`.
* The diamond with tips `p`, `q` is `I⁺(p) ∩ I⁻(q)`, written `◇[p, q]` (local notation).
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open scoped Pointwise

/-- The diamond `I⁺(p) ∩ I⁻(q)` of standard Minkowski spacetime with its standard time
orientation. -/
local notation "◇[" p ", " q "]" =>
  Spacetime.chronologicalFuture StandardMinkowskiSpacetime standardMinkowskiTimeOrientation p ∩
    Spacetime.chronologicalPast StandardMinkowskiSpacetime standardMinkowskiTimeOrientation q

/-- The lightlike vector `l₊ = (1, 1, 0, 0)`. -/
local notation "l₊" => (!₂[1, 1, 0, 0] : SpacetimeModel)

/-- The lightlike vector `l₋ = (1, -1, 0, 0)`. -/
local notation "l₋" => (!₂[1, -1, 0, 0] : SpacetimeModel)

/-! ### The standard wedges -/

/-- The right wedge `W_R = {x ∈ ℝ⁴ | |x⁰| < x¹}`.

Blueprint: def:right-wedge -/
def rightWedge : Set StandardMinkowskiSpacetime.Carrier :=
  {x : SpacetimeModel | |x 0| < x 1}

/-- The left wedge `W_L = {x ∈ ℝ⁴ | x¹ < -|x⁰|}`, the point reflection of the right wedge.

Blueprint: def:left-wedge -/
def leftWedge : Set StandardMinkowskiSpacetime.Carrier :=
  {x : SpacetimeModel | x 1 < -|x 0|}

/-- The left wedge is the point reflection of the right wedge: `x ∈ W_L` if and only if
`-x ∈ W_R`.

Blueprint: def:left-wedge -/
theorem mem_leftWedge_iff_neg_mem_rightWedge (x : SpacetimeModel) :
    x ∈ leftWedge ↔ -x ∈ rightWedge := by
  sorry

/-- The wedges in light-cone coordinates: `x ∈ W_R` if and only if `x¹ + x⁰ > 0` and
`x¹ - x⁰ > 0`, and `x ∈ W_L` if and only if `x¹ + x⁰ < 0` and `x¹ - x⁰ < 0`.

Blueprint: lmm:wedge-light-cone-coordinates -/
theorem wedge_lightCone_coordinates (x : SpacetimeModel) :
    (x ∈ rightWedge ↔ 0 < x 1 + x 0 ∧ 0 < x 1 - x 0) ∧
      (x ∈ leftWedge ↔ x 1 + x 0 < 0 ∧ x 1 - x 0 < 0) := by
  sorry

/-- `W_R` and `W_L` are open and nonempty: `(0, 1, 0, 0) ∈ W_R` and `(0, -1, 0, 0) ∈ W_L`.

Blueprint: lmm:wedge-open-nonempty -/
theorem wedge_isOpen_nonempty :
    IsOpen rightWedge ∧ IsOpen leftWedge ∧
      (!₂[0, 1, 0, 0] : SpacetimeModel) ∈ rightWedge ∧
      (!₂[0, -1, 0, 0] : SpacetimeModel) ∈ leftWedge := by
  sorry

/-! ### Poincaré transformations of diamonds -/

/-- A Poincaré transformation maps diamonds to diamonds: `g (I⁺(p) ∩ I⁻(q)) = I⁺(gp) ∩ I⁻(gq)`,
so `g B` is a diamond for every diamond `B`, nonempty if `B` is.

Blueprint: lmm:poincare-maps-diamonds -/
theorem smul_diamond_eq (g : InhomogeneousLorentzGroup) :
    (∀ p q : StandardMinkowskiSpacetime.Carrier, g • ◇[p, q] = ◇[g • p, g • q]) ∧
      ∀ B : Set StandardMinkowskiSpacetime.Carrier, IsAlexandrovBasisSet B →
        IsAlexandrovBasisSet (g • B) ∧ (B.Nonempty → (g • B).Nonempty) := by
  sorry

/-- A Poincaré transformation preserves inclusion: `g O₁ ⊆ g O₂ ↔ O₁ ⊆ O₂`. Consequently
`B ↦ g B` is a bijection from the diamonds contained in `O` onto the diamonds contained in
`g O`, with inverse `B' ↦ g⁻¹ B'`.

Blueprint: lmm:poincare-diamond-inclusion -/
theorem smul_diamond_subset_bijOn (g : InhomogeneousLorentzGroup)
    (O₁ O₂ O : Set StandardMinkowskiSpacetime.Carrier) :
    (g • O₁ ⊆ g • O₂ ↔ O₁ ⊆ O₂) ∧
      Set.BijOn (fun B => g • B) {B | IsAlexandrovBasisSet B ∧ B ⊆ O}
        {B | IsAlexandrovBasisSet B ∧ B ⊆ g • O} ∧
      Set.InvOn (fun B => g⁻¹ • B) (fun B => g • B) {B | IsAlexandrovBasisSet B ∧ B ⊆ O}
        {B | IsAlexandrovBasisSet B ∧ B ⊆ g • O} := by
  sorry

/-! ### Wedges -/

/-- A set `W` of spacetime points is a wedge if `W = g W_R` for some `g` in the inhomogeneous
Lorentz group. The element `g` is not unique; objects attached to a wedge through `g`, such as
the boosts `wedgeBoostAlong g`, are indexed by `g` rather than by `W`.

Blueprint: def:wedge -/
def IsWedge (W : Set StandardMinkowskiSpacetime.Carrier) : Prop :=
  ∃ g : InhomogeneousLorentzGroup, W = g • rightWedge

/-- The rotation by `π` in the `(x¹, x²)`-plane, `R(x⁰, x¹, x², x³) = (x⁰, -x¹, -x², x³)`, is a
proper orthochronous Lorentz transformation with `R⁻¹ = R`.

Blueprint: lmm:rotation-pi-lorentz -/
theorem exists_rotationPi_lorentz :
    ∃ R : SpacetimeModel ≃ₗ[ℝ] SpacetimeModel,
      (∀ x : SpacetimeModel, R x = !₂[x 0, -x 1, -x 2, x 3]) ∧
        IsLorentz R ∧ IsProper R ∧ IsOrthochronous R ∧ R.symm = R := by
  sorry

/-- The left wedge is a wedge: the element `(R, 0)`, with `R` the rotation by `π` in the
`(x¹, x²)`-plane, maps `W_R` onto `W_L`. Hence `W_L` is a wedge, and so is `g W_L` for every `g`.

Blueprint: lmm:left-wedge-is-wedge -/
theorem leftWedge_isWedge :
    (∀ r : InhomogeneousLorentzGroup,
        (∀ x : SpacetimeModel, r.linear x = !₂[x 0, -x 1, -x 2, x 3]) → r.translation = 0 →
          r • rightWedge = leftWedge) ∧
      IsWedge leftWedge ∧ ∀ g : InhomogeneousLorentzGroup, IsWedge (g • leftWedge) := by
  sorry

/-- A coordinate bound in the open forward cone: if `η(v, v) < 0` and `v⁰ > 0`, then
`|vⁱ| < v⁰` for `i = 1, 2, 3`.

Blueprint: lmm:open-cone-coordinate-bound -/
theorem abs_coord_lt_of_minkowskiForm_neg {v : SpacetimeModel} (hv : minkowskiForm v v < 0)
    (h0 : 0 < v 0) (i : Fin 4) (hi : i ≠ 0) : |v i| < v 0 := by
  sorry

/-- The diamond `B₊ = I⁺(p₊) ∩ I⁻(q₊)` with `p₊ = (-1, 2, 0, 0)` and `q₊ = (1, 2, 0, 0)` is a
nonempty diamond contained in the right wedge.

Blueprint: lmm:wedges-contain-diamonds -/
theorem rightWedge_contains_diamond :
    IsAlexandrovBasisSet ◇[(!₂[-1, 2, 0, 0] : SpacetimeModel), (!₂[1, 2, 0, 0] : SpacetimeModel)] ∧
      (◇[(!₂[-1, 2, 0, 0] : SpacetimeModel), (!₂[1, 2, 0, 0] : SpacetimeModel)]).Nonempty ∧
      ◇[(!₂[-1, 2, 0, 0] : SpacetimeModel), (!₂[1, 2, 0, 0] : SpacetimeModel)] ⊆
        rightWedge := by
  sorry

/-- Every wedge contains a nonempty diamond. With `B₊` as in `rightWedge_contains_diamond` and
`B₋ = (R, 0) B₊ = I⁺(-1, -2, 0, 0) ∩ I⁻(1, -2, 0, 0)`, for every `g` the set `g B₊` is a nonempty
diamond contained in `g W_R` and `g B₋` is a nonempty diamond contained in `g W_L`.

Blueprint: crllr:wedge-contains-diamond -/
theorem wedge_contains_diamond :
    (∀ g : InhomogeneousLorentzGroup,
      (IsAlexandrovBasisSet
          (g • ◇[(!₂[-1, 2, 0, 0] : SpacetimeModel), (!₂[1, 2, 0, 0] : SpacetimeModel)]) ∧
        (g • ◇[(!₂[-1, 2, 0, 0] : SpacetimeModel), (!₂[1, 2, 0, 0] : SpacetimeModel)]).Nonempty ∧
        g • ◇[(!₂[-1, 2, 0, 0] : SpacetimeModel), (!₂[1, 2, 0, 0] : SpacetimeModel)] ⊆
          g • rightWedge) ∧
      (IsAlexandrovBasisSet
          (g • ◇[(!₂[-1, -2, 0, 0] : SpacetimeModel), (!₂[1, -2, 0, 0] : SpacetimeModel)]) ∧
        (g • ◇[(!₂[-1, -2, 0, 0] : SpacetimeModel), (!₂[1, -2, 0, 0] : SpacetimeModel)]).Nonempty ∧
        g • ◇[(!₂[-1, -2, 0, 0] : SpacetimeModel), (!₂[1, -2, 0, 0] : SpacetimeModel)] ⊆
          g • leftWedge)) ∧
    ∀ W : Set StandardMinkowskiSpacetime.Carrier, IsWedge W →
      ∃ B : Set StandardMinkowskiSpacetime.Carrier,
        IsAlexandrovBasisSet B ∧ B.Nonempty ∧ B ⊆ W := by
  sorry

/-- Translations into the right wedge: if `|a⁰| ≤ a¹`, then `W_R + a ⊆ W_R`, where
`W_R + a = translationSub a • W_R`. In particular this holds for `a = t l₊` and `a = -t l₋` with
`t ≥ 0`.

Blueprint: lmm:wedge-translations -/
theorem translationSub_smul_rightWedge_subset :
    (∀ a : SpacetimeModel, |a 0| ≤ a 1 → translationSub a • rightWedge ⊆ rightWedge) ∧
      ∀ t : ℝ, 0 ≤ t →
        translationSub (t • l₊) • rightWedge ⊆ rightWedge ∧
          translationSub (-(t • l₋)) • rightWedge ⊆ rightWedge := by
  sorry

/-- Transverse translations preserve the right wedge: if `a⁰ = a¹ = 0`, then `W_R + a = W_R`.

Blueprint: lmm:wedge-transverse-translations -/
theorem translationSub_smul_rightWedge_of_transverse {a : SpacetimeModel} (h0 : a 0 = 0)
    (h1 : a 1 = 0) : translationSub a • rightWedge = rightWedge := by
  sorry

/-- Opposite wedges are completely spacelike: `W_R` and `W_L` are completely spacelike for the
standard time orientation, and for every `g` and all sets `O₁ ⊆ g W_R` and `O₂ ⊆ g W_L`, the sets
`O₁` and `O₂` are completely spacelike in either order.

Blueprint: lmm:opposite-wedges-completely-spacelike -/
theorem oppositeWedges_isCompletelySpacelike :
    Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime standardMinkowskiTimeOrientation
        rightWedge leftWedge ∧
      ∀ (g : InhomogeneousLorentzGroup) (O₁ O₂ : Set StandardMinkowskiSpacetime.Carrier),
        O₁ ⊆ g • rightWedge → O₂ ⊆ g • leftWedge →
          Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
              standardMinkowskiTimeOrientation O₁ O₂ ∧
            Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
              standardMinkowskiTimeOrientation O₂ O₁ := by
  sorry

/-! ### Boosts -/

set_option linter.flexible false in
/-- The boost matrix `Λ(s)` with rapidity `s`, the linear automorphism of `ℝ⁴`
`Λ(s)(x⁰, x¹, x², x³) = (cosh s x⁰ + sinh s x¹, sinh s x⁰ + cosh s x¹, x², x³)`, with inverse
`Λ(-s)`. The sign of `s` is fixed by `Λ(s) l₊ = eˢ l₊` and `Λ(s) l₋ = e⁻ˢ l₋`
(`boostMatrix_lightCone`). The boost `Λ_{W₁}(t)` of Brunetti, Guido and Longo is `Λ(-2πt)`.

Implementation note: `Λ(s)` is the operator of the matrix
`[[cosh s, sinh s, 0, 0], [sinh s, cosh s, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]` on
`EuclideanSpace ℝ (Fin 4)` (`Matrix.toEuclideanCLM`), packaged as a `LinearEquiv` whose inverse
is the operator of the matrix at `-s`.

Blueprint: def:boost-matrix -/
noncomputable def boostMatrix (s : ℝ) : SpacetimeModel ≃ₗ[ℝ] SpacetimeModel :=
  let B : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun r =>
    !![Real.cosh r, Real.sinh r, 0, 0; Real.sinh r, Real.cosh r, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  have hB : ∀ r, B r * B (-r) = 1 := fun r => by
    have h := Real.cosh_sq_sub_sinh_sq r
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_four, Real.cosh_neg, Real.sinh_neg] <;>
      first | ring1 | linear_combination h
  have hT : ∀ r, Matrix.toEuclideanCLM (𝕜 := ℝ) (B r) * Matrix.toEuclideanCLM (𝕜 := ℝ) (B (-r)) =
      1 := fun r => by rw [← map_mul, hB, map_one]
  LinearEquiv.ofLinearMap
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (B s)).toLinearMap
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (B (-s))).toLinearMap
    (LinearMap.ext fun x => by simpa using congrArg (fun T => T x) (hT s))
    (LinearMap.ext fun x => by
      have h := hT (-s)
      rw [neg_neg] at h
      simpa using congrArg (fun T => T x) h)

/-- The boost matrix in coordinates:
`Λ(s) x = (cosh s x⁰ + sinh s x¹, sinh s x⁰ + cosh s x¹, x², x³)`.

Blueprint: def:boost-matrix -/
theorem boostMatrix_apply (s : ℝ) (x : SpacetimeModel) :
    boostMatrix s x =
      !₂[Real.cosh s * x 0 + Real.sinh s * x 1, Real.sinh s * x 0 + Real.cosh s * x 1,
        x 2, x 3] := by
  sorry

/-- The boost matrices preserve the Minkowski form: `η(Λ(s)v, Λ(s)w) = η(v, w)`.

Blueprint: lmm:boost-matrix-lorentz -/
theorem boostMatrix_isLorentz (s : ℝ) : IsLorentz (boostMatrix s) := by
  sorry

/-- The boost matrices are proper: `det Λ(s) = 1`.

Blueprint: lmm:boost-matrix-proper -/
theorem boostMatrix_isProper (s : ℝ) : IsProper (boostMatrix s) := by
  sorry

/-- The boost matrices are orthochronous: `(Λ(s)e₀)⁰ = cosh s > 0`.

Blueprint: lmm:boost-matrix-orthochronous -/
theorem boostMatrix_isOrthochronous (s : ℝ) : IsOrthochronous (boostMatrix s) := by
  sorry

/-- The boost matrices form a one-parameter group: `Λ(0) = 1` and `Λ(s + t) = Λ(s)Λ(t)`, and
`Λ(s)⁻¹ = Λ(-s)`.

Blueprint: lmm:boost-matrix-group-law -/
theorem boostMatrix_groupLaw :
    boostMatrix 0 = LinearEquiv.refl ℝ SpacetimeModel ∧
      (∀ s t : ℝ, boostMatrix (s + t) = (boostMatrix t).trans (boostMatrix s)) ∧
      ∀ s : ℝ, (boostMatrix s).symm = boostMatrix (-s) := by
  sorry

/-- Boosts in light-cone coordinates: with `y = Λ(s)x`, `y¹ + y⁰ = eˢ(x¹ + x⁰)` and
`y¹ - y⁰ = e⁻ˢ(x¹ - x⁰)`. In particular `Λ(s) l₊ = eˢ l₊` and `Λ(s) l₋ = e⁻ˢ l₋`.

Blueprint: lmm:boost-light-cone -/
theorem boostMatrix_lightCone (s : ℝ) :
    (∀ x : SpacetimeModel,
      boostMatrix s x 1 + boostMatrix s x 0 = Real.exp s * (x 1 + x 0) ∧
        boostMatrix s x 1 - boostMatrix s x 0 = Real.exp (-s) * (x 1 - x 0)) ∧
      boostMatrix s l₊ = Real.exp s • l₊ ∧ boostMatrix s l₋ = Real.exp (-s) • l₋ := by
  sorry

/-- The boost of the right wedge with rapidity `s`, the element `b(s) = (Λ(s), 0)` of the
inhomogeneous Lorentz group.

Blueprint: def:wedge-boost -/
noncomputable def wedgeBoost (s : ℝ) : InhomogeneousLorentzGroup where
  linear := boostMatrix s
  translation := 0
  isLorentz := boostMatrix_isLorentz s
  isProper := boostMatrix_isProper s
  isOrthochronous := boostMatrix_isOrthochronous s

/-- The boost of the wedge `g W_R` along `g` with rapidity `s`: `b_g(s) = g b(s) g⁻¹`. It is
indexed by `g`, not by the wedge `g W_R`.

Blueprint: def:wedge-boost -/
noncomputable def wedgeBoostAlong (g : InhomogeneousLorentzGroup) (s : ℝ) :
    InhomogeneousLorentzGroup :=
  g * wedgeBoost s * g⁻¹

/-- Boosts preserve the standard wedges: `b(s) W_R = W_R` and `b(s) W_L = W_L`.

Blueprint: lmm:boost-preserves-wedge -/
theorem wedgeBoost_smul_wedge (s : ℝ) :
    wedgeBoost s • rightWedge = rightWedge ∧ wedgeBoost s • leftWedge = leftWedge := by
  sorry

/-- Conjugates stabilise transformed sets: if `h W = W`, then `(g h g⁻¹)(g W) = g W`, and
`(g h g⁻¹) B` is a diamond contained in `g W` for every diamond `B ⊆ g W`. In particular
`b_g(s)(g W_R) = g W_R` and `b_g(s)(g W_L) = g W_L`.

Blueprint: lmm:conjugate-stabilises-wedge -/
theorem conj_smul_stabilises :
    (∀ (g h : InhomogeneousLorentzGroup) (W : Set StandardMinkowskiSpacetime.Carrier),
      h • W = W →
        (g * h * g⁻¹) • (g • W) = g • W ∧
          ∀ B : Set StandardMinkowskiSpacetime.Carrier, IsAlexandrovBasisSet B → B ⊆ g • W →
            IsAlexandrovBasisSet ((g * h * g⁻¹) • B) ∧ (g * h * g⁻¹) • B ⊆ g • W) ∧
      ∀ (g : InhomogeneousLorentzGroup) (s : ℝ),
        wedgeBoostAlong g s • (g • rightWedge) = g • rightWedge ∧
          wedgeBoostAlong g s • (g • leftWedge) = g • leftWedge := by
  sorry

/-- A continuous one-parameter subgroup of the inhomogeneous Lorentz group: `γ 0 = 1`,
`γ (s + t) = γ s * γ t` (`IsOneParameterSubgroup`, which has no continuity clause), and `γ` is
continuous for the topology induced by `(Λ, a) ↦ (Λ, Λ⁻¹, a)`.

Blueprint: def:continuous-one-parameter-subgroup -/
def IsContinuousOneParameterSubgroup (γ : ℝ → InhomogeneousLorentzGroup) : Prop :=
  IsOneParameterSubgroup γ ∧ Continuous γ

/-- The boost group law: `b(0) = 1` and `b(s + t) = b(s) b(t)`.

Blueprint: lmm:boost-group-law -/
theorem wedgeBoost_groupLaw :
    wedgeBoost 0 = 1 ∧ ∀ s t : ℝ, wedgeBoost (s + t) = wedgeBoost s * wedgeBoost t := by
  sorry

/-- The boost `s ↦ b(s)` is a continuous one-parameter subgroup.

Blueprint: lmm:boost-continuous-subgroup -/
theorem isContinuousOneParameterSubgroup_wedgeBoost :
    IsContinuousOneParameterSubgroup wedgeBoost := by
  sorry

/-- Conjugates of continuous one-parameter subgroups: if `γ` is a continuous one-parameter
subgroup, so is `s ↦ g γ(s) g⁻¹`. In particular so is `s ↦ b_g(s)`.

Blueprint: lmm:conjugate-continuous-subgroup -/
theorem isContinuousOneParameterSubgroup_conj :
    (∀ γ : ℝ → InhomogeneousLorentzGroup, IsContinuousOneParameterSubgroup γ →
      ∀ g : InhomogeneousLorentzGroup, IsContinuousOneParameterSubgroup fun s => g * γ s * g⁻¹) ∧
      ∀ g : InhomogeneousLorentzGroup, IsContinuousOneParameterSubgroup (wedgeBoostAlong g) := by
  sorry

/-- Translation flows are continuous one-parameter subgroups: for every `n`,
`s ↦ translationFlow n s = (1, s n)` is one.

Blueprint: lmm:translation-flow-continuous-subgroup -/
theorem isContinuousOneParameterSubgroup_translationFlow
    (n : StandardMinkowskiSpacetime.Carrier) :
    IsContinuousOneParameterSubgroup (translationFlow n) := by
  sorry

end HaagKastler
end AQFT
end Physicslib4
