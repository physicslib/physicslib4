/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Physicslib4.Geometry.PseudoRiemannian.Basic

/-!
# The Levi-Civita connection of a pseudo-Riemannian metric

This file adapts Mathlib's Levi-Civita connection of a Riemannian manifold
(`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`) to a
pseudo-Riemannian metric `g`, which need not be positive definite. Mathlib's covariant
derivatives (`CovariantDerivative`) and torsion (`CovariantDerivative.torsion`) are used as they
are; the inner product of Mathlib's `IsMetricCompatible` is replaced by `g`.

## Main definitions

* `CovariantDerivative.IsMetricCompatibleWith`: `X g(σ, τ) = g(∇_X σ, τ) + g(σ, ∇_X τ)`.
* `CovariantDerivative.IsLeviCivitaFor`: torsion-free and metric-compatible.
* `PseudoRiemannianMetric.leviCivita`: the Levi-Civita connection of `g`.

## Main results

* `CovariantDerivative.IsLeviCivitaFor.koszul`: the Koszul formula.
* `CovariantDerivative.IsLeviCivitaFor.uniqueness`: uniqueness on differentiable vector fields.
* `PseudoRiemannianMetric.exists_isLeviCivitaFor`: existence.

Blueprint reference: `def:metric-compatible-connection`, `def:levi-civita-connection`,
`lmm:koszul-formula`, `thrm:levi-civita-exists-unique`.
-/

open Bundle VectorField
open scoped Manifold ContDiff

namespace Physicslib4

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E]

namespace CovariantDerivative

/-- A covariant derivative `∇` on `TM` is **compatible** with the pseudo-Riemannian metric `g`
if `X g(σ, τ) = g(∇_X σ, τ) + g(σ, ∇_X τ)` at every point where the vector fields `X`, `σ`
and `τ` are differentiable. This is the condition of Mathlib's
`CovariantDerivative.isMetricCompatible_iff`, with `g` in place of the inner product.

Blueprint reference: `def:metric-compatible-connection`. -/
def IsMetricCompatibleWith (g : PseudoRiemannianMetric I M)
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ ⦃x : M⦄ ⦃X σ τ : Π x : M, TangentSpace I x⦄,
    MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (σ y) (τ y)) x (X x))
        = g.val x (cov σ x (X x)) (τ x) + g.val x (σ x) (cov τ x (X x))

/-- A covariant derivative on `TM` is a **Levi-Civita connection** for `g` if it is
torsion-free and compatible with `g`.

Blueprint reference: `def:levi-civita-connection`. -/
structure IsLeviCivitaFor (g : PseudoRiemannianMetric I M)
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop where
  /-- Compatibility with `g`. -/
  isMetricCompatibleWith : IsMetricCompatibleWith g cov
  /-- Vanishing torsion. -/
  torsion : cov.torsion = 0

variable {g : PseudoRiemannianMetric I M}
  {cov cov' : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- **The Koszul formula.** For a Levi-Civita connection of `g` and vector fields `X`, `Y`, `Z`
differentiable at `x`, `2 g(∇_X Y, Z)` is expressed through derivatives of `g` and Lie brackets
alone, without reference to `∇`. This is Mathlib's `IsLeviCivitaConnection.apply_eq` multiplied
by 2, with `g` in place of the inner product; the blueprint's form of the formula is the same
statement after `mlieBracket_swap` and the symmetry of `g`.

Blueprint reference: `lmm:koszul-formula`. -/
theorem IsLeviCivitaFor.koszul (h : IsLeviCivitaFor g cov) {x : M}
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g.val x (cov Y x (X x)) (Z x) =
      (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (Y y) (Z y)) x (X x))
      + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (Z y) (X y)) x (Y x))
      - (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (X y) (Y y)) x (Z x))
      - g.val x (Y x) (mlieBracket I X Z x)
      - g.val x (Z x) (mlieBracket I Y X x)
      + g.val x (X x) (mlieBracket I Z Y x) := by
  -- use the compatibility with `g` in three ways
  have eq1a := h.isMetricCompatibleWith hX hY hZ
  have eq2a := h.isMetricCompatibleWith hY hZ hX
  have eq3a := h.isMetricCompatibleWith hZ hX hY
  -- use the torsion-freeness in three ways
  have eq1b := congr(g.val x (Y x) ($(h.torsion) x (X x) (Z x)))
  have eq2b := congr(g.val x (Z x) ($(h.torsion) x (Y x) (X x)))
  have eq3b := congr(g.val x (X x) ($(h.torsion) x (Z x) (Y x)))
  rw [cov.torsion_apply hX hZ] at eq1b
  rw [cov.torsion_apply hY hX] at eq2b
  rw [cov.torsion_apply hZ hY] at eq3b
  simp only [map_sub, Pi.zero_apply, zero_apply, map_zero] at eq1b eq2b eq3b
  -- align the order of the arguments of `g`
  rw [g.symm x (cov Z x (Y x)) (X x)] at eq2a
  rw [g.symm x (cov X x (Z x)) (Y x)] at eq3a
  rw [g.symm x (Z x) (cov Y x (X x))] at eq2b
  linear_combination -(eq1a + eq2a - eq3a + eq1b + eq2b - eq3b)

/-- **Uniqueness of the Levi-Civita connection.** Two Levi-Civita connections of `g` agree on
every vector field differentiable at `x`. (Covariant derivatives are unconstrained on
non-differentiable vector fields, as in Mathlib's `IsLeviCivitaConnection.uniqueness`.)

Blueprint reference: `thrm:levi-civita-exists-unique`. -/
theorem IsLeviCivitaFor.uniqueness (hcov : IsLeviCivitaFor g cov)
    (hcov' : IsLeviCivitaFor g cov') {x : M} {Y : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (X₀ : TangentSpace I x) :
    cov Y x X₀ = cov' Y x X₀ := by
  set X := FiberBundle.extend E X₀
  have hX : MDiffAt (T% X) x := FiberBundle.mdifferentiableAt_extend I E X₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have key : g.val x (cov Y x X₀) = g.val x (cov' Y x X₀) := by
    apply VectorBundle.injective_eval_mdifferentiableAt_sec I E (TangentSpace I) ℝ x
    ext Z hZ
    have h1 := hcov.koszul hX hY hZ
    have h2 := hcov'.koszul hX hY hZ
    rw [hXx] at h1 h2
    simp only
    linarith
  have h := g.nondegenerate x (cov Y x X₀ - cov' Y x X₀) fun w ↦ by
    rw [map_sub, key, sub_self, zero_apply]
  exact sub_eq_zero.mp h

end CovariantDerivative

namespace PseudoRiemannianMetric

/-! ### Existence

The construction follows Mathlib's `CovariantDerivative.leviCivitaConnection`: the right-hand
side of the Koszul formula (`koszulAux`) is tensorial in `X` and `Z`, hence a bilinear form at
each point, and the musical isomorphism `flatEquiv` turns it into the desired `∇_X Y`. -/

variable (g : PseudoRiemannianMetric I M)

variable {X Y Z : Π x : M, TangentSpace I x}

variable (X Y Z) in
/-- The right-hand side of the Koszul formula, divided by 2: for the Levi-Civita connection
this is `g(∇_X Y, Z)`.

Blueprint reference: `lmm:koszul-expression-tensorial`. -/
noncomputable def koszulAux (x : M) : ℝ :=
  ((show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (Y y) (Z y)) x (X x))
    + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (Z y) (X y)) x (Y x))
    - (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (X y) (Y y)) x (Z x))
    - g.val x (Y x) (mlieBracket I X Z x)
    - g.val x (Z x) (mlieBracket I Y X x)
    + g.val x (X x) (mlieBracket I Z Y x)) / 2

omit [FiniteDimensional ℝ E] in
/-- `y ↦ g_y(Y y, Z y)` is differentiable at `x` if `Y` and `Z` are. -/
theorem mdifferentiableAt_val_apply {x : M} (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ g.val y (Y y) (Z y)) x := by
  have := MDifferentiableAt.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    ((g.contMDiff x).mdifferentiableAt (by simp)) hY hZ
  simp only [mdifferentiableAt_totalSpace] at this
  exact this.2

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- The real-valued `mfderiv` terms of `koszulAux` are `mvfderiv` terms. -/
theorem mfderiv_apply_eq_mvfderiv (F : M → ℝ) {x : M} (v : TangentSpace I x) :
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) F x v) = d% F x v := rfl

/-- `koszulAux` is tensorial in its first argument.

Blueprint reference: `lmm:koszul-expression-tensorial`. -/
theorem tensorialAt_koszulAux₁ (x : M) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (g.koszulAux · Y Z x) x where
  smul {f X} hf hX := by
    simp only [koszulAux, mfderiv_apply_eq_mvfderiv]
    simp (disch := first | assumption | exact g.mdifferentiableAt_val_apply ‹_› ‹_›) only
      [Pi.smul_apply', map_smul, smul_apply, smul_eq_mul, mvfderiv_fun_mul, add_apply,
        mlieBracket_smul_left hf hX, mlieBracket_smul_right hf hX, map_add, neg_mul]
    rw [g.symm x (X x) (Y x)]
    ring
  add {X X'} hX hX' := by
    simp only [koszulAux, mfderiv_apply_eq_mvfderiv]
    simp (disch := first | assumption | exact g.mdifferentiableAt_val_apply ‹_› ‹_›) only
      [Pi.add_apply, map_add, add_apply, mvfderiv_fun_add, mlieBracket_add_left hX hX',
        mlieBracket_add_right hX hX']
    ring

/-- `koszulAux` is tensorial in its third argument.

Blueprint reference: `lmm:koszul-expression-tensorial`. -/
theorem tensorialAt_koszulAux₃ (x : M) (hY : MDiffAt (T% Y) x) (hX : MDiffAt (T% X) x) :
    TensorialAt I E (g.koszulAux X Y · x) x where
  smul {f Z} hf hZ := by
    simp only [koszulAux, mfderiv_apply_eq_mvfderiv]
    simp (disch := first | assumption | exact g.mdifferentiableAt_val_apply ‹_› ‹_›) only
      [Pi.smul_apply', map_smul, smul_apply, smul_eq_mul, mvfderiv_fun_mul, add_apply,
        mlieBracket_smul_left hf hZ, mlieBracket_smul_right hf hZ, map_add, neg_mul]
    rw [g.symm x (Y x) (Z x), g.symm x (X x) (Z x)]
    ring
  add {Z Z'} hZ hZ' := by
    simp only [koszulAux, mfderiv_apply_eq_mvfderiv]
    simp (disch := first | assumption | exact g.mdifferentiableAt_val_apply ‹_› ‹_›) only
      [Pi.add_apply, map_add, add_apply, mvfderiv_fun_add, mlieBracket_add_left hZ hZ',
        mlieBracket_add_right hZ hZ']
    ring

/-- The candidate `∇ Y` at `x` for a vector field `Y` differentiable at `x`. -/
noncomputable def leviCivitaAuxOfMDiffAt {x : M} (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (g.flatEquiv x).symm.toContinuousLinearMap ∘L
    TensorialAt.mkHom₂ (fun X Z ↦ g.koszulAux X Y Z x) x
      (fun _Z hZ ↦ g.tensorialAt_koszulAux₁ x hY hZ)
      (fun _X hX ↦ g.tensorialAt_koszulAux₃ x hY hX)

open scoped Classical in
/-- The function underlying the Levi-Civita connection of `g` (zero on vector fields that are
not differentiable at the point). -/
noncomputable def leviCivitaAux (Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then g.leviCivitaAuxOfMDiffAt hY else 0

/-- `g(∇_X Y, Z) = koszulAux X Y Z` for the constructed connection. -/
theorem leviCivitaAux_apply_val {x : M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.val x (g.leviCivitaAux Y x (X x)) (Z x) = g.koszulAux X Y Z x := by
  rw [leviCivitaAux, dite_eq_left hY, leviCivitaAuxOfMDiffAt, ← flatEquiv_apply]
  simp [TensorialAt.mkHom₂_apply _ _ hX hZ]

omit [FiniteDimensional ℝ E] in
/-- A tangent vector is determined by its `g`-pairings with vector fields differentiable at the
point. -/
theorem eq_of_forall_val_apply_eq {x : M} {v w : TangentSpace I x}
    (h : ∀ Z : Π x : M, TangentSpace I x, MDiffAt (T% Z) x →
      g.val x v (Z x) = g.val x w (Z x)) : v = w := by
  have key : g.val x v = g.val x w := by
    apply VectorBundle.injective_eval_mdifferentiableAt_sec I E (TangentSpace I) ℝ x
    ext Z hZ
    exact h Z hZ
  exact sub_eq_zero.mp <| g.nondegenerate x (v - w) fun u ↦ by
    rw [map_sub, key, sub_self, zero_apply]

/-- The constructed operator is a covariant derivative.

Blueprint reference: `lmm:koszul-connection-is-covariant-derivative`. -/
theorem isCovariantDerivativeOn_leviCivitaAux :
    IsCovariantDerivativeOn E (g.leviCivitaAux (M := M)) where
  add {Y Y' x} hY hY' _ := by
    have hYY' : MDiffAt (T% (Y + Y')) x := mdifferentiableAt_add_section hY hY'
    apply injective_eval_mdifferentiableAt_vectorField I (TangentSpace I x) x
    ext X hX
    apply g.eq_of_forall_val_apply_eq
    intro Z hZ
    simp only [add_apply, map_add,
      g.leviCivitaAux_apply_val hX hYY' hZ, g.leviCivitaAux_apply_val hX hY hZ,
      g.leviCivitaAux_apply_val hX hY' hZ]
    simp only [koszulAux, mfderiv_apply_eq_mvfderiv]
    simp (disch := first | assumption | exact g.mdifferentiableAt_val_apply ‹_› ‹_›) only
      [Pi.add_apply, map_add, add_apply, mvfderiv_fun_add, mlieBracket_add_left hY hY',
        mlieBracket_add_right hY hY']
    ring
  leibniz {Y f x} hY hf _ := by
    have hfY : MDiffAt (T% (f • Y)) x := hf.smul_section hY
    apply injective_eval_mdifferentiableAt_vectorField I (TangentSpace I x) x
    ext X hX
    apply g.eq_of_forall_val_apply_eq
    intro Z hZ
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      g.leviCivitaAux_apply_val hX hfY hZ, g.leviCivitaAux_apply_val hX hY hZ]
    simp only [koszulAux, mfderiv_apply_eq_mvfderiv]
    simp (disch := first | assumption | exact g.mdifferentiableAt_val_apply ‹_› ‹_›) only
      [Pi.smul_apply', map_smul, smul_apply, smul_eq_mul, mvfderiv_fun_mul, add_apply,
        mlieBracket_smul_left hf hY, mlieBracket_smul_right hf hY, map_add, neg_mul]
    rw [g.symm x (Z x) (Y x)]
    ring

/-- The covariant derivative constructed from the Koszul formula. -/
noncomputable def koszulConnection :
    _root_.CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := g.leviCivitaAux
  isCovariantDerivativeOnUniv := g.isCovariantDerivativeOn_leviCivitaAux

/-- The Koszul connection is compatible with `g`.

Blueprint reference: `lmm:koszul-connection-is-levi-civita`. -/
theorem isMetricCompatibleWith_koszulConnection :
    CovariantDerivative.IsMetricCompatibleWith g g.koszulConnection := by
  intro x X σ τ hX hσ hτ
  change _ = g.val x (g.leviCivitaAux σ x (X x)) (τ x)
    + g.val x (σ x) (g.leviCivitaAux τ x (X x))
  rw [g.symm x (σ x) (g.leviCivitaAux τ x (X x)),
    g.leviCivitaAux_apply_val hX hσ hτ, g.leviCivitaAux_apply_val hX hτ hσ]
  have h₁ : (fun y ↦ g.val y (τ y) (σ y)) = fun y ↦ g.val y (σ y) (τ y) :=
    funext fun y ↦ g.symm y _ _
  have h₂ : (fun y ↦ g.val y (σ y) (X y)) = fun y ↦ g.val y (X y) (σ y) :=
    funext fun y ↦ g.symm y _ _
  have h₃ : (fun y ↦ g.val y (τ y) (X y)) = fun y ↦ g.val y (X y) (τ y) :=
    funext fun y ↦ g.symm y _ _
  simp only [koszulAux, mfderiv_apply_eq_mvfderiv, h₁, h₂, h₃]
  rw [mlieBracket_swap (V := τ) (W := σ), mlieBracket_swap (V := τ) (W := X),
    mlieBracket_swap (V := σ) (W := X)]
  simp only [Pi.neg_apply, map_neg]
  ring

/-- The Koszul connection is torsion-free.

Blueprint reference: `lmm:koszul-connection-is-levi-civita`. -/
theorem torsion_koszulConnection_eq_zero : g.koszulConnection.torsion = 0 := by
  rw [_root_.CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  have key : g.val x (g.koszulConnection Y x (X x) - g.koszulConnection X x (Y x)) =
      g.val x (mlieBracket I X Y x) := by
    apply VectorBundle.injective_eval_mdifferentiableAt_sec I E (TangentSpace I) ℝ x
    ext Z hZ
    have h1 := g.leviCivitaAux_apply_val hX hY hZ
    have h2 := g.leviCivitaAux_apply_val hY hX hZ
    have e1 : (fun y ↦ g.val y (Z y) (Y y)) = fun y ↦ g.val y (Y y) (Z y) :=
      funext fun y ↦ g.symm y _ _
    have e2 : (fun y ↦ g.val y (Z y) (X y)) = fun y ↦ g.val y (X y) (Z y) :=
      funext fun y ↦ g.symm y _ _
    have e3 : (fun y ↦ g.val y (Y y) (X y)) = fun y ↦ g.val y (X y) (Y y) :=
      funext fun y ↦ g.symm y _ _
    simp only [koszulAux, mfderiv_apply_eq_mvfderiv] at h1 h2
    rw [e2] at h1
    rw [e1, e3] at h2
    change g.val x (g.leviCivitaAux Y x (X x) - g.leviCivitaAux X x (Y x)) (Z x) =
      g.val x (mlieBracket I X Y x) (Z x)
    rw [map_sub, sub_apply, h1, h2, mlieBracket_swap (V := Y) (W := X),
      mlieBracket_swap (V := Z) (W := X), mlieBracket_swap (V := Z) (W := Y)]
    simp only [Pi.neg_apply, map_neg]
    rw [g.symm x (Y x) (mlieBracket I X Z x), g.symm x (X x) (mlieBracket I Y Z x),
      g.symm x (Z x) (mlieBracket I X Y x)]
    ring
  have h := g.nondegenerate x (g.koszulConnection Y x (X x) - g.koszulConnection X x (Y x) -
    mlieBracket I X Y x) fun w ↦ by rw [map_sub, key, sub_self, zero_apply]
  exact sub_eq_zero.mp h

/-- **Existence of the Levi-Civita connection.** Every pseudo-Riemannian metric has a
Levi-Civita connection.

Blueprint reference: `thrm:levi-civita-exists-unique`. -/
theorem exists_isLeviCivitaFor (g : PseudoRiemannianMetric I M) :
    ∃ cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _),
      CovariantDerivative.IsLeviCivitaFor g cov :=
  ⟨g.koszulConnection, g.isMetricCompatibleWith_koszulConnection,
    g.torsion_koszulConnection_eq_zero⟩

/-- A choice of **Levi-Civita connection** of `g`. It is unique on differentiable vector fields
(`CovariantDerivative.IsLeviCivitaFor.uniqueness`).

Blueprint reference: `thrm:levi-civita-exists-unique`. -/
noncomputable def leviCivita (g : PseudoRiemannianMetric I M) :
    _root_.CovariantDerivative I E (TangentSpace I : M → Type _) :=
  g.exists_isLeviCivitaFor.choose

/-- The chosen `leviCivita` connection is a Levi-Civita connection of `g`. -/
theorem isLeviCivitaFor_leviCivita (g : PseudoRiemannianMetric I M) :
    CovariantDerivative.IsLeviCivitaFor g g.leviCivita :=
  g.exists_isLeviCivitaFor.choose_spec

end PseudoRiemannianMetric

end Geometry

end Physicslib4
