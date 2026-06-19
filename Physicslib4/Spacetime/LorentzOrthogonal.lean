/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.LorentzCauchySchwarz
import Physicslib4.Spacetime.LorentzCone

/-!
# Orthogonal decomposition relative to a timelike vector

This file develops the infrastructure needed for the *sign lemma* for cones:
two timelike vectors that are future-pointing with respect to a common time
orientation have negative inner product.

For a symmetric Lorentzian bilinear form `B` and a timelike vector `t`
(`B t t < 0`), the orthogonal complement `t^⊥ = {u | B t u = 0}` is the
*spacelike complement*. The two key facts are:

* `nonneg_of_orthogonal_timelike`: `B` is positive *semidefinite* on `t^⊥`
  (it would be positive definite under nondegeneracy, but semidefiniteness is
  all that the sign lemma needs and it follows directly from reverse
  Cauchy-Schwarz);
* `cauchy_schwarz_on_orthogonal`: the ordinary (forward) Cauchy-Schwarz
  inequality holds for vectors in `t^⊥`.

Combining these with the explicit `t`-orthogonal decomposition
`(B t t) • v - (B t v) • t ∈ t^⊥` yields `bilin_neg_of_inner_t_neg`, the sign
lemma.

All statements are abstract (they depend only on the algebraic `LorentzianAt`
condition), so they transfer to the metric `g|_p` of any spacetime.
-/

namespace Physicslib4

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The `t`-orthogonal component of `v`, cleared of denominators by the factor
`B t t`: the vector `(B t t) • v - (B t v) • t` is orthogonal to `t`. -/
theorem inner_orthogonal_component
    {B : LinearMap.BilinForm ℝ V} (t v : V) :
    B t ((B t t) • v - (B t v) • t) = 0 := by
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- **Positive semidefiniteness of the spacelike complement.** If `t` is
timelike and `u` is orthogonal to `t`, then `0 ≤ B u u`: were `B u u < 0`, the
vector `u` would be timelike and reverse Cauchy-Schwarz would force
`(B t u)^2 > 0`, contradicting orthogonality. -/
theorem nonneg_of_orthogonal_timelike
    {B : LinearMap.BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    (hL : LorentzianAt (fun v w => B v w))
    {t u : V} (ht : B t t < 0) (h : B t u = 0) : 0 ≤ B u u := by
  by_contra hcon
  have hneg : B u u < 0 := not_le.mp hcon
  have hcs := reverse_cauchy_schwarz_of_lorentzianAt hsymm hL ht hneg
  rw [h] at hcs
  nlinarith [mul_pos_of_neg_of_neg ht hneg]

/-- Cauchy-Schwarz for two vectors along whose span the symmetric form `B` is
positive semidefinite. Proved via the nonpositivity of the discriminant of the
nonnegative quadratic `s ↦ B (s • x + y) (s • x + y)`. -/
theorem cauchy_schwarz_of_nonneg_on_span
    {B : LinearMap.BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    {x y : V} (h : ∀ s : ℝ, 0 ≤ B (s • x + y) (s • x + y)) :
    (B x y) ^ 2 ≤ (B x x) * (B y y) := by
  have expand : ∀ s : ℝ,
      B (s • x + y) (s • x + y) = (B x x) * (s * s) + (2 * B x y) * s + B y y := by
    intro s
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm y x]
    ring
  have hdisc : discrim (B x x) (2 * B x y) (B y y) ≤ 0 := by
    apply discrim_le_zero
    intro s
    rw [← expand s]
    exact h s
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- **Forward Cauchy-Schwarz on the spacelike complement.** For two vectors
orthogonal to a timelike vector `t`, the ordinary Cauchy-Schwarz inequality
holds. -/
theorem cauchy_schwarz_on_orthogonal
    {B : LinearMap.BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    (hL : LorentzianAt (fun v w => B v w))
    {t x y : V} (ht : B t t < 0) (hx : B t x = 0) (hy : B t y = 0) :
    (B x y) ^ 2 ≤ (B x x) * (B y y) := by
  apply cauchy_schwarz_of_nonneg_on_span hsymm
  intro s
  apply nonneg_of_orthogonal_timelike hsymm hL ht
  simp only [map_add, map_smul, smul_eq_mul, hx, hy, mul_zero, add_zero]

/-- **Nondegeneracy from the Lorentzian basis.** A Lorentzian bilinear form is
nondegenerate: if `B v w = 0` for every `w`, then `v = 0`. This is extracted
from the signature basis, on which the Gram matrix `diag(-1,1,1,1)` is
invertible. -/
theorem eq_zero_of_forall_bilin_eq_zero
    {B : LinearMap.BilinForm ℝ V} (hL : LorentzianAt (fun v w => B v w))
    {v : V} (h : ∀ w, B v w = 0) : v = 0 := by
  obtain ⟨b, hb⟩ := hL
  have hb' : ∀ i j : Fin 4, B (b i) (b j) = lorentzSignature i j := hb
  have hcoord : ∀ j, b.repr v j = 0 := by
    intro j
    have key : B v (b j) = b.repr v j * lorentzSignature j j := by
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
      · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hb']
      · intro i _ hij
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hb', lorentzSignature,
          Matrix.diagonal_apply_ne _ hij, mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [h (b j)] at key
    have hsig : lorentzSignature j j ≠ 0 := by
      simp only [lorentzSignature, Matrix.diagonal_apply_eq]
      split <;> norm_num
    exact (mul_eq_zero.mp key.symm).resolve_right hsig
  have hbr : b.repr v = 0 := by
    ext j; rw [Finsupp.zero_apply]; exact hcoord j
  exact b.repr.injective (hbr.trans (map_zero b.repr).symm)

/-- **Strict positive-definiteness of the spacelike complement.** If `t` is
timelike and `u ≠ 0` is orthogonal to `t`, then `0 < B u u`. A null vector in
`t^⊥` would, by Cauchy-Schwarz on `t^⊥`, be orthogonal to all of `t^⊥`, hence to
everything, contradicting nondegeneracy. -/
theorem pos_of_orthogonal_timelike
    {B : LinearMap.BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    (hL : LorentzianAt (fun v w => B v w))
    {t u : V} (ht : B t t < 0) (h : B t u = 0) (hu : u ≠ 0) : 0 < B u u := by
  rcases (nonneg_of_orthogonal_timelike hsymm hL ht h).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    apply hu
    apply eq_zero_of_forall_bilin_eq_zero hL
    intro x
    have hxperp : B t ((B t t) • x - (B t x) • t) = 0 := inner_orthogonal_component t x
    have hcs := cauchy_schwarz_on_orthogonal hsymm hL ht h hxperp
    have hz2 : (B u u) * (B ((B t t) • x - (B t x) • t) ((B t t) • x - (B t x) • t)) = 0 := by
      rw [← hzero]; ring
    rw [hz2] at hcs
    have hsq : (B u ((B t t) • x - (B t x) • t)) ^ 2 = 0 := le_antisymm hcs (sq_nonneg _)
    have huxp : B u ((B t t) • x - (B t x) • t) = 0 := (pow_eq_zero_iff (by norm_num)).mp hsq
    have hut : B u t = 0 := by rw [hsymm u t]; exact h
    have expand : B u ((B t t) • x - (B t x) • t)
        = (B t t) * (B u x) - (B t x) * (B u t) := by
      simp only [map_sub, map_smul, smul_eq_mul]
    rw [hut, mul_zero, sub_zero] at expand
    rw [expand] at huxp
    rcases mul_eq_zero.mp huxp with h1 | h2
    · exact absurd h1 (ne_of_lt ht)
    · exact h2

/-- Pure-real algebraic core of the sign lemma. Given the scalars produced by
the `t`-orthogonal decomposition, with their reverse Cauchy-Schwarz bounds and
the forward Cauchy-Schwarz inequality on the spacelike complement, the cross
term `bvw` is negative. -/
private theorem sign_algebra {a bvv bww btv btw bvw : ℝ}
    (ha : a < 0) (hbvv : bvv < 0) (hbww : bww < 0) (hbtv : btv < 0) (hbtw : btw < 0)
    (hrcsv : a * bvv ≤ btv ^ 2) (hrcsw : a * bww ≤ btw ^ 2)
    (hcs : (a ^ 2 * bvw - a * btv * btw) ^ 2
        ≤ (a ^ 2 * bvv - a * btv ^ 2) * (a ^ 2 * bww - a * btw ^ 2)) :
    bvw < 0 := by
  have hτ2 : 0 < a ^ 2 := by nlinarith [mul_pos_of_neg_of_neg ha ha]
  -- Clear the common factor `a^2 > 0` from the Cauchy-Schwarz inequality.
  have hdiv : (a * bvw - btv * btw) ^ 2 ≤ (btv ^ 2 - a * bvv) * (btw ^ 2 - a * bww) := by
    have hmul : a ^ 2 * ((a * bvw - btv * btw) ^ 2)
        ≤ a ^ 2 * ((btv ^ 2 - a * bvv) * (btw ^ 2 - a * bww)) := by
      have e1 : a ^ 2 * ((a * bvw - btv * btw) ^ 2)
          = (a ^ 2 * bvw - a * btv * btw) ^ 2 := by ring
      have e2 : a ^ 2 * ((btv ^ 2 - a * bvv) * (btw ^ 2 - a * bww))
          = (a ^ 2 * bvv - a * btv ^ 2) * (a ^ 2 * bww - a * btw ^ 2) := by ring
      rw [e1, e2]; exact hcs
    exact le_of_mul_le_mul_left hmul hτ2
  -- Strictness of the `N`s, and positivity of the `(B t ·)` squares.
  have hNvlt : btv ^ 2 - a * bvv < btv ^ 2 := by nlinarith [mul_pos_of_neg_of_neg ha hbvv]
  have hNwlt : btw ^ 2 - a * bww < btw ^ 2 := by nlinarith [mul_pos_of_neg_of_neg ha hbww]
  have hNv : 0 ≤ btv ^ 2 - a * bvv := by linarith [hrcsv]
  have hNw : 0 ≤ btw ^ 2 - a * bww := by linarith [hrcsw]
  have hBtv2 : 0 < btv ^ 2 := by nlinarith [mul_pos_of_neg_of_neg hbtv hbtv]
  have hBtw2 : 0 < btw ^ 2 := by nlinarith [mul_pos_of_neg_of_neg hbtw hbtw]
  -- The product of the `N`s is strictly dominated by the product of the squares.
  have hNN : (btv ^ 2 - a * bvv) * (btw ^ 2 - a * bww) < btv ^ 2 * btw ^ 2 := by
    nlinarith [hNv, hNw, hNvlt, hNwlt, hBtv2, hBtw2]
  have hP2 : (a * bvw - btv * btw) ^ 2 < (btv * btw) ^ 2 := by nlinarith [hdiv, hNN]
  have hkey : 0 < a * bvw := by
    nlinarith [hP2, mul_pos_of_neg_of_neg hbtv hbtw, sq_nonneg (a * bvw)]
  nlinarith [hkey, ha]

/-- **Sign lemma for cones.** Let `B` be a symmetric Lorentzian bilinear form,
`t` a timelike vector, and `v, w` timelike vectors that are future-pointing with
respect to `t` (`B t v < 0` and `B t w < 0`). Then `B v w < 0`: future-pointing
timelike vectors lie in a common cone, on which the inner product is negative. -/
theorem bilin_neg_of_inner_t_neg
    {B : LinearMap.BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    (hL : LorentzianAt (fun v w => B v w))
    {t v w : V} (ht : B t t < 0) (hv : B v v < 0) (hw : B w w < 0)
    (htv : B t v < 0) (htw : B t w < 0) : B v w < 0 := by
  have hvp : B t ((B t t) • v - (B t v) • t) = 0 := inner_orthogonal_component t v
  have hwp : B t ((B t t) • w - (B t w) • t) = 0 := inner_orthogonal_component t w
  have hcs := cauchy_schwarz_on_orthogonal hsymm hL ht hvp hwp
  have evp : B ((B t t) • v - (B t v) • t) ((B t t) • v - (B t v) • t)
      = (B t t) ^ 2 * (B v v) - (B t t) * (B t v) ^ 2 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm v t]
    ring
  have ewp : B ((B t t) • w - (B t w) • t) ((B t t) • w - (B t w) • t)
      = (B t t) ^ 2 * (B w w) - (B t t) * (B t w) ^ 2 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm w t]
    ring
  have evw : B ((B t t) • v - (B t v) • t) ((B t t) • w - (B t w) • t)
      = (B t t) ^ 2 * (B v w) - (B t t) * (B t v) * (B t w) := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm v t]
    ring
  rw [evp, ewp, evw] at hcs
  exact sign_algebra ht hv hw htv htw
    (reverse_cauchy_schwarz_of_lorentzianAt hsymm hL ht hv)
    (reverse_cauchy_schwarz_of_lorentzianAt hsymm hL ht hw) hcs

namespace Spacetime

/-- **Spacetime sign lemma.** Two timelike tangent vectors at a point that are
future-pointing with respect to the same time orientation `τ` (`g|_p(τ,v) < 0`
and `g|_p(τ,w) < 0`) have negative inner product `g|_p(v,w) < 0`. -/
theorem inner_neg_of_future_timelike (M : Spacetime) (x : M.Carrier)
    (τ : M.TimeOrientation) {v w : TangentSpace M.model x}
    (hv : M.IsTimelike v) (hw : M.IsTimelike w)
    (hfv : M.val x (τ.field x) v < 0) (hfw : M.val x (τ.field x) w < 0) :
    M.val x v w < 0 := by
  let B : LinearMap.BilinForm ℝ (TangentSpace M.model x) :=
    LinearMap.mk₂ ℝ (fun a c => M.val x a c)
      (fun a₁ a₂ c => by simp) (fun r a c => by simp)
      (fun a c₁ c₂ => by simp) (fun r a c => by simp)
  have hBapp : ∀ a c, B a c = M.val x a c := fun a c => rfl
  have hsymm : ∀ a c, B a c = B c a := by
    intro a c; rw [hBapp, hBapp]; exact M.symm x a c
  have hL : LorentzianAt (fun a c => B a c) := by simpa only [hBapp] using M.lorentzian x
  have ht : B (τ.field x) (τ.field x) < 0 := by rw [hBapp]; exact τ.timelike_at x
  have hv' : B v v < 0 := by rw [hBapp]; exact hv
  have hw' : B w w < 0 := by rw [hBapp]; exact hw
  have hfv' : B (τ.field x) v < 0 := by rw [hBapp]; exact hfv
  have hfw' : B (τ.field x) w < 0 := by rw [hBapp]; exact hfw
  have h := bilin_neg_of_inner_t_neg hsymm hL ht hv' hw' hfv' hfw'
  rwa [hBapp] at h

/-- **Spacelike complement, pointwise.** A nonzero tangent vector orthogonal to
a timelike vector is spacelike: the metric is positive definite on the spacelike
complement. -/
theorem isSpacelike_of_orthogonal_timelike (M : Spacetime) (x : M.Carrier)
    {t u : TangentSpace M.model x} (ht : M.IsTimelike t)
    (h : M.val x t u = 0) (hu : u ≠ 0) : M.IsSpacelike u := by
  let B : LinearMap.BilinForm ℝ (TangentSpace M.model x) :=
    LinearMap.mk₂ ℝ (fun a c => M.val x a c)
      (fun a₁ a₂ c => by simp) (fun r a c => by simp)
      (fun a c₁ c₂ => by simp) (fun r a c => by simp)
  have hBapp : ∀ a c, B a c = M.val x a c := fun a c => rfl
  have hsymm : ∀ a c, B a c = B c a := by
    intro a c; rw [hBapp, hBapp]; exact M.symm x a c
  have hL : LorentzianAt (fun a c => B a c) := by simpa only [hBapp] using M.lorentzian x
  have ht' : B t t < 0 := by rw [hBapp]; exact ht
  have h' : B t u = 0 := by rw [hBapp]; exact h
  have hpos := pos_of_orthogonal_timelike hsymm hL ht' h' hu
  rw [hBapp] at hpos
  exact hpos

/-- **Convexity of the future cone (timelike part).** The sum of two timelike
future-pointing tangent vectors is again timelike and future-pointing with
respect to the same time orientation. This is the cone-convexity payoff of the
sign lemma. -/
theorem isFuturePointing_add (M : Spacetime) (x : M.Carrier)
    (τ : M.TimeOrientation) {v w : TangentSpace M.model x}
    (hv : M.IsTimelike v) (hw : M.IsTimelike w)
    (hfv : M.IsFuturePointing τ v) (hfw : M.IsFuturePointing τ w) :
    M.IsFuturePointing τ (v + w) := by
  -- Extract the time-orientation sign from the (timelike branch of the) hypotheses.
  have hfv1 : M.val x (τ.field x) v < 0 := by
    rcases hfv with ⟨_, h⟩ | ⟨hn, _⟩
    · exact h
    · exact absurd hn (M.not_isNull_of_isTimelike hv)
  have hfw1 : M.val x (τ.field x) w < 0 := by
    rcases hfw with ⟨_, h⟩ | ⟨hn, _⟩
    · exact h
    · exact absurd hn (M.not_isNull_of_isTimelike hw)
  -- The sign lemma aligns `v` and `w`, so the sum stays timelike.
  have hsign : M.val x v w < 0 := inner_neg_of_future_timelike M x τ hv hw hfv1 hfw1
  have hvw : M.IsTimelike (v + w) := M.add_isTimelike x hv hw (le_of_lt hsign)
  -- The time-orientation sign is additive, hence negative on the sum.
  have hsum : M.val x (τ.field x) (v + w) < 0 := by
    rw [map_add]; linarith [hfv1, hfw1]
  exact Or.inl ⟨hvw, hsum⟩

/-- Every future-pointing vector (timelike or null) is the limit of a sequence of
future-pointing timelike vectors. For a timelike vector this is the constant
sequence; for a null vector it is exactly the approximating sequence in the
definition of `IsFuturePointing`. -/
theorem exists_seq_of_isFuturePointing (M : Spacetime) (x : M.Carrier)
    (τ : M.TimeOrientation) {v : TangentSpace M.model x} (hv : M.IsFuturePointing τ v) :
    ∃ vs : ℕ → TangentSpace M.model x,
      (∀ n, M.IsTimelike (vs n) ∧ M.val x (τ.field x) (vs n) < 0) ∧
      Filter.Tendsto vs Filter.atTop (nhds v) := by
  rcases hv with ⟨htl, hsgn⟩ | ⟨_, hseq⟩
  · exact ⟨fun _ => v, fun _ => ⟨htl, hsgn⟩, tendsto_const_nhds⟩
  · exact hseq

/-- The time-orientation pairing is nonpositive on any future-pointing vector:
`g|_p(τ, v) ≤ 0`. For timelike `v` this is the defining strict inequality; for
null `v` it follows by passing to the limit along the approximating sequence
(continuity of the fixed continuous linear functional `g|_p(τ, ·)`). -/
theorem inner_t_nonpos_of_future (M : Spacetime) (x : M.Carrier)
    (τ : M.TimeOrientation) {v : TangentSpace M.model x} (hfv : M.IsFuturePointing τ v) :
    M.val x (τ.field x) v ≤ 0 := by
  obtain ⟨vs, hvs, hvtend⟩ := exists_seq_of_isFuturePointing M x τ hfv
  have htend : Filter.Tendsto (fun n => M.val x (τ.field x) (vs n)) Filter.atTop
      (nhds (M.val x (τ.field x) v)) :=
    ((M.val x (τ.field x)).continuous.tendsto v).comp hvtend
  exact le_of_tendsto' htend (fun n => le_of_lt (hvs n).2)

/-- **Generalized sign lemma.** Any two future-pointing vectors (timelike or
null) have nonpositive inner product `g|_p(v,w) ≤ 0`. Only continuity of the
fixed continuous linear maps `g|_p(a, ·)` is used (with symmetry to keep the
varying vector in the second slot), so no normed structure on the tangent space
is required. -/
theorem inner_nonpos_of_future (M : Spacetime) (x : M.Carrier)
    (τ : M.TimeOrientation) {v w : TangentSpace M.model x}
    (hfv : M.IsFuturePointing τ v) (hfw : M.IsFuturePointing τ w) :
    M.val x v w ≤ 0 := by
  obtain ⟨vs, hvs, hvtend⟩ := exists_seq_of_isFuturePointing M x τ hfv
  obtain ⟨ws, hws, hwtend⟩ := exists_seq_of_isFuturePointing M x τ hfw
  -- For each `n`, the strict sign lemma on the timelike approximants `ws m`, then a limit.
  have step2 : ∀ n, M.val x (vs n) w ≤ 0 := by
    intro n
    have hlt : ∀ m, M.val x (vs n) (ws m) < 0 := fun m =>
      inner_neg_of_future_timelike M x τ (hvs n).1 (hws m).1 (hvs n).2 (hws m).2
    have htend : Filter.Tendsto (fun m => M.val x (vs n) (ws m)) Filter.atTop
        (nhds (M.val x (vs n) w)) := ((M.val x (vs n)).continuous.tendsto w).comp hwtend
    exact le_of_tendsto' htend (fun m => le_of_lt (hlt m))
  have step2' : ∀ n, M.val x w (vs n) ≤ 0 := fun n => by rw [M.symm x w (vs n)]; exact step2 n
  have htend : Filter.Tendsto (fun n => M.val x w (vs n)) Filter.atTop (nhds (M.val x w v)) :=
    ((M.val x w).continuous.tendsto v).comp hvtend
  have hwv : M.val x w v ≤ 0 := le_of_tendsto' htend step2'
  rw [M.symm x v w]; exact hwv

/-- **Convexity of the future cone (general form).** The sum of any two
future-pointing tangent vectors (timelike or null) is future-pointing with
respect to the same time orientation. The timelike summands are handled by
`isFuturePointing_add`; the null branch is treated by approximating each summand
by future-pointing timelike vectors and passing to the limit. -/
theorem isFuturePointing_add_general (M : Spacetime) (x : M.Carrier)
    (τ : M.TimeOrientation) {v w : TangentSpace M.model x}
    (hfv : M.IsFuturePointing τ v) (hfw : M.IsFuturePointing τ w) :
    M.IsFuturePointing τ (v + w) := by
  obtain ⟨vs, hvs, hvtend⟩ := exists_seq_of_isFuturePointing M x τ hfv
  obtain ⟨ws, hws, hwtend⟩ := exists_seq_of_isFuturePointing M x τ hfw
  -- The summed sequence is timelike and future-pointing at every stage.
  have htl : ∀ n, M.IsTimelike (vs n + ws n) := fun n =>
    M.add_isTimelike x (hvs n).1 (hws n).1
      (le_of_lt (inner_neg_of_future_timelike M x τ (hvs n).1 (hws n).1 (hvs n).2 (hws n).2))
  have hsgn : ∀ n, M.val x (τ.field x) (vs n + ws n) < 0 := fun n => by
    rw [map_add]; linarith [(hvs n).2, (hws n).2]
  have hsum : Filter.Tendsto (fun n => vs n + ws n) Filter.atTop (nhds (v + w)) :=
    hvtend.add hwtend
  -- Causality of the limit from the additive expansion and the generalized sign lemma.
  have hvv : M.val x v v ≤ 0 := by
    rcases hfv with ⟨h, _⟩ | ⟨h, _⟩
    · exact le_of_lt h
    · exact le_of_eq h
  have hww : M.val x w w ≤ 0 := by
    rcases hfw with ⟨h, _⟩ | ⟨h, _⟩
    · exact le_of_lt h
    · exact le_of_eq h
  have hvw : M.val x v w ≤ 0 := inner_nonpos_of_future M x τ hfv hfw
  have hexp : M.val x (v + w) (v + w) = M.val x v v + 2 * (M.val x v w) + M.val x w w := by
    simp only [map_add, ContinuousLinearMap.add_apply]
    rw [M.symm x w v]; ring
  have hcausal : M.val x (v + w) (v + w) ≤ 0 := by rw [hexp]; linarith [hvv, hww, hvw]
  -- The time-orientation pairing is nonpositive on the sum.
  have htsum : M.val x (τ.field x) (v + w) ≤ 0 := by
    rw [map_add]
    linarith [inner_t_nonpos_of_future M x τ hfv, inner_t_nonpos_of_future M x τ hfw]
  rcases lt_or_eq_of_le hcausal with hneg | hzero
  · -- Timelike limit: future-pointing via the timelike branch.
    refine Or.inl ⟨hneg, ?_⟩
    have ht0 : M.val x (τ.field x) (τ.field x) < 0 := τ.timelike_at x
    have hne : M.val x (τ.field x) (v + w) ≠ 0 := by
      intro h0
      have hrcs := M.reverse_cauchy_schwarz x (τ.timelike_at x) hneg
      rw [h0] at hrcs
      nlinarith [mul_pos_of_neg_of_neg ht0 hneg]
    exact lt_of_le_of_ne htsum hne
  · -- Null limit: future-pointing via the null branch, witnessed by the summed sequence.
    exact Or.inr ⟨hzero, fun n => vs n + ws n, fun n => ⟨htl n, hsgn n⟩, hsum⟩

end Spacetime

end Physicslib4
