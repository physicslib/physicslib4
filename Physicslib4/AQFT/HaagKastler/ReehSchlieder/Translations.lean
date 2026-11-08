/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.VacuumState
import Physicslib4.AQFT.PositiveEnergyHolomorphic
import Physicslib4.Analysis.EdgeVanishing
import Physicslib4.Spacetime.LorentzCausality
import Physicslib4.Spacetime.MinkowskiDirected

/-!
# Translations of diamonds and timelike spreading

The geometric and analytic lemmas on spacetime translations used by the Reeh–Schlieder
theorem.

* `translationSub_smul_diamond` — the translate `B + x = translationSub x • B` of the diamond
  `I⁺(p) ∩ I⁻(q)` is the diamond `I⁺(p + x) ∩ I⁻(q + x)`.
* `exists_diamond_translate_subset` — a nonempty diamond contains every small translate of
  some smaller nonempty diamond.
* `exists_isOpen_sum_mem_of_mem_nhds` — small enough summands keep a bounded number of partial
  sums inside a given neighbourhood of `0`.
* `futureTimelike_basis` — the vectors `e₀` and `e₀ + ½ eᵢ` are future-pointing timelike and
  form a basis of `ℝ⁴`.
* `inner_translation_eq_zero_add_smul` and `inner_translation_eq_zero` — under positive energy
  a matrix coefficient `x ↦ ⟨χ, U(x)φ⟩` that vanishes on an open set spreads its vanishing along
  every future-timelike direction, and hence vanishes identically when the open set is nonempty.

Throughout, `ℝ⁴` is the carrier of standard Minkowski spacetime with its manifold topology,
which is the Euclidean topology of `EuclideanSpace ℝ (Fin 4)`. A family of unitaries indexed by
translations is a function `U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H)`; the
unitaries `U' : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H)` of a vacuum state give such a family
as `fun x => U' (translationSub x)`, and then `fun t => U' (translationFlow n t)` is
definitionally `fun t => U' (translationSub (t • n))`.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open scoped InnerProductSpace Pointwise
open Spacetime

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The translate of a diamond is a diamond: for all `p, q, x ∈ ℝ⁴`,
`translationSub x • (I⁺(p) ∩ I⁻(q)) = I⁺(p + x) ∩ I⁻(q + x)`.

Blueprint: lmm:diamond-translate -/
theorem translationSub_smul_diamond (p q x : StandardMinkowskiSpacetime.Carrier) :
    translationSub x •
        (chronologicalFuture StandardMinkowskiSpacetime standardMinkowskiTimeOrientation p ∩
          chronologicalPast StandardMinkowskiSpacetime standardMinkowskiTimeOrientation q) =
      chronologicalFuture StandardMinkowskiSpacetime standardMinkowskiTimeOrientation (p + x) ∩
        chronologicalPast StandardMinkowskiSpacetime standardMinkowskiTimeOrientation (q + x) := by
  have hg : ∀ y, translationSub x • y = y + x := fun _ => rfl
  ext y
  simp only [Set.mem_inter_iff, chronologicalFuture, chronologicalPast, Set.mem_ofPred_eq,
    Set.mem_smul_set_iff_inv_smul_mem, ← hg p, ← hg q]
  conv_rhs => rw [← smul_inv_smul (translationSub x) y]
  rw [chronologicallyPrecedes_smul_iff, chronologicallyPrecedes_smul_iff]

/-- Every nonempty diamond `B` contains all small translates of a smaller nonempty diamond:
there are a nonempty diamond `B₁` and an open neighbourhood `V` of `0` in `ℝ⁴` with
`B₁ + x = translationSub x • B₁ ⊆ B` for every `x ∈ V`.

Openness of `V` refers to the manifold topology of standard Minkowski spacetime, the Euclidean
topology of `ℝ⁴`.

Blueprint: lmm:diamond-small-translates -/
theorem exists_diamond_translate_subset {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B) (hBne : B.Nonempty) :
    ∃ B₁ : Set StandardMinkowskiSpacetime.Carrier, IsAlexandrovBasisSet B₁ ∧ B₁.Nonempty ∧
      ∃ V : Set StandardMinkowskiSpacetime.Carrier, IsOpen V ∧ 0 ∈ V ∧
        ∀ x ∈ V, translationSub x • B₁ ⊆ B := by
  have trans := @StandardMinkowskiSpacetime.chronologicallyPrecedes_trans
    standardMinkowskiTimeOrientation
  have interp : ∀ a c : StandardMinkowskiSpacetime.Carrier,
      (a ≪[StandardMinkowskiSpacetime, standardMinkowskiTimeOrientation] c) →
      ∃ b, (a ≪[StandardMinkowskiSpacetime, standardMinkowskiTimeOrientation] b) ∧
        b ≪[StandardMinkowskiSpacetime, standardMinkowskiTimeOrientation] c := by
    intro a c h
    have e := fun c => Set.ext_iff.mp (chronologicalPast_standardMinkowski c)
    obtain ⟨b, hb, -, hab⟩ :=
      exists_future_between_standardMinkowski ((e c a).mp h) ((e c a).mp h)
    exact ⟨b, (e b a).mpr hab, (e c b).mpr hb⟩
  obtain ⟨p, q, rfl⟩ := hB
  obtain ⟨y, hpy, hyq⟩ := hBne
  obtain ⟨p', hpp', hp'q⟩ := interp p q (trans hpy hyq)
  obtain ⟨q', hp'q', hq'q⟩ := interp p' q hp'q
  obtain ⟨z, hp'z, hzq'⟩ := interp p' q' hp'q'
  refine ⟨_, ⟨p', q', rfl⟩, ⟨z, hp'z, hzq'⟩,
    (p' + ·) ⁻¹' chronologicalFuture StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation p ∩
      (q' + ·) ⁻¹' chronologicalPast StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation q, ?_, ?_, ?_⟩
  · exact ((isOpen_chronologicalFuture_standardMinkowski p).preimage
      (continuous_const.add continuous_id)).inter
      ((isOpen_chronologicalPast_standardMinkowski q).preimage
      (continuous_const.add continuous_id))
  · exact ⟨by simp only [Set.mem_preimage, add_zero]; exact hpp',
      by simp only [Set.mem_preimage, add_zero]; exact hq'q⟩
  · rintro x ⟨hx₁, hx₂⟩
    rw [translationSub_smul_diamond]
    rintro w ⟨hw₁, hw₂⟩
    exact ⟨trans hx₁ hw₁, trans hw₂ hx₂⟩

/-- For every neighbourhood `V` of `0` and every `n` there is an open neighbourhood `V₀` of `0`
such that `ξ₁ + ⋯ + ξₖ ∈ V` whenever `k ≤ n` and `ξ₁, …, ξₖ ∈ V₀`.

The statement is made for any commutative topological additive monoid with continuous addition;
the blueprint uses it for `ℝ⁴`. The blueprint's side conditions `n ≥ 1` and `k ≥ 1` are
omitted: the case `k = 0` holds because the empty sum `0` lies in `V`.

Blueprint: lmm:neighbourhood-partial-sums -/
theorem exists_isOpen_sum_mem_of_mem_nhds {G : Type*} [AddCommMonoid G] [TopologicalSpace G]
    [ContinuousAdd G] {V : Set G} (hV : V ∈ nhds (0 : G)) (n : ℕ) :
    ∃ V₀ : Set G, IsOpen V₀ ∧ (0 : G) ∈ V₀ ∧
      ∀ k ≤ n, ∀ ξ : Fin k → G, (∀ i, ξ i ∈ V₀) → ∑ i, ξ i ∈ V := by
  have key : ∀ k, ∃ W ∈ nhds (0 : G), ∀ ξ : Fin k → G, (∀ i, ξ i ∈ W) → ∑ i, ξ i ∈ V := by
    intro k
    have h : Filter.Tendsto (fun ξ : Fin k → G => ∑ i, ξ i) (nhds 0) (nhds 0) := by
      simpa using (continuous_finsetSum Finset.univ fun i _ => continuous_apply i).tendsto
        (0 : Fin k → G)
    have h2 := h hV
    rw [nhds_pi] at h2
    obtain ⟨I, t, ht, hs⟩ := Filter.mem_pi'.1 h2
    exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun ξ hξ => hs fun i _ => Set.mem_iInter.1 (hξ i) i⟩
  choose W hW hWV using key
  refine ⟨interior (⋂ k ∈ Finset.range (n + 1), W k), isOpen_interior,
    mem_interior_iff_mem_nhds.2 ((Filter.biInter_finset_mem _).2 fun k _ => hW k),
    fun k hk ξ hξ => hWV k ξ fun i => ?_⟩
  exact Set.mem_iInter₂.1 (interior_subset (hξ i)) k (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- The vectors `n₀ = e₀` and `nᵢ = e₀ + ½ eᵢ`, `i = 1, 2, 3`, are future-pointing timelike (they
lie in the open forward cone `minkowskiForwardCone 0`, the notion used by
`IsFutureTimelikeTranslation`) and form a basis of `ℝ⁴`.

The family is passed as `n` together with its defining equation `hn`; "form a basis" is the
existence of a basis of `ℝ⁴` indexed by `Fin 4` whose vectors are `n`.

Blueprint: lmm:future-timelike-basis -/
theorem futureTimelike_basis (n : Fin 4 → SpacetimeModel)
    (hn : ∀ i, n i = EuclideanSpace.single 0 1 +
      (if i = 0 then 0 else (2⁻¹ : ℝ) • EuclideanSpace.single i 1)) :
    (∀ i, n i ∈ minkowskiForwardCone 0) ∧ ∃ b : Module.Basis (Fin 4) ℝ SpacetimeModel, ⇑b = n := by
  obtain rfl : n = _ := funext hn
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [minkowskiForwardCone] <;> norm_num
  · have hli : LinearIndependent ℝ (fun i : Fin 4 => EuclideanSpace.single (0 : Fin 4) (1 : ℝ) +
        (if i = 0 then 0 else (2⁻¹ : ℝ) • EuclideanSpace.single i 1)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have h0 := congrArg (· 0) hg; have h1 := congrArg (· 1) hg
      have h2 := congrArg (· 2) hg; have h3 := congrArg (· 3) hg
      simp [Fin.sum_univ_four] at h0 h1 h2 h3
      intro i; fin_cases i <;> simp <;> linarith
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp), ?_⟩
    simp

/-- **Timelike spreading in one direction.** Let `x ↦ U(x)` be unitaries on `H` indexed by the
translations `ℝ⁴`, let `φ ∈ H` satisfy `U(x + y)φ = U(x)U(y)φ`, and let `n` be a direction for
which `t ↦ U(t n)` has positive energy. If `h(x) = ⟨χ, U(x)φ⟩` vanishes on an open set `W`, it
vanishes on `W + ℝn = {x + t n | x ∈ W, t ∈ ℝ}`.

The unitaries are a function of the translation vector; for a vacuum state with unitaries `U'`
indexed by the inhomogeneous Lorentz group, take `U = fun x => U' (translationSub x)`. Only the
group law at `φ` is used; the blueprint's closed invariant subspace `K₀ ∋ φ`, on which the group law
holds, supplies it, and its timelike condition on `n` enters only through positive energy, which
is assumed directly. Openness of `W` refers to the Euclidean topology of `ℝ⁴`.

Blueprint: lmm:timelike-spreading-direction -/
theorem inner_translation_eq_zero_add_smul
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    {φ : H} (hmul : ∀ x y, U (x + y) φ = U x (U y φ))
    {n : StandardMinkowskiSpacetime.Carrier} (hpos : IsPositiveEnergy (fun t : ℝ => U (t • n)))
    (χ : H)
    {W : Set StandardMinkowskiSpacetime.Carrier} (hW : IsOpen W)
    (hzero : ∀ x ∈ W, ⟪χ, U x φ⟫_ℂ = 0) :
    ∀ x ∈ W, ∀ t : ℝ, ⟪χ, U (x + t • n) φ⟫_ℂ = 0 := by
  intro x hx t
  obtain ⟨F, hFd, hFc, -, hF⟩ := hpos.exists_holomorphic_extension χ (U x φ)
  have hsh : ∀ s : ℝ, ⟪χ, U (x + s • n) φ⟫_ℂ = F s := fun s => by
    rw [hF, add_comm, hmul]
  have hcont : Continuous fun s : ℝ => x + s • n :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : {s : ℝ | x + s • n ∈ W} ∈ nhds (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hx)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  have hvan : ∀ s ∈ Set.Ioo (-ε) ε, F s = 0 := fun s hs => by
    rw [← hsh]
    exact hzero _ (hball (by rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_lt]; exact hs))
  rw [hsh]
  exact eq_zero_of_eq_zero_on_Ioo (by linarith) hFc hFd hvan t (by simp)

/-- **Timelike spreading.** Let `U` and `φ` be as in `inner_translation_eq_zero_add_smul`, and
suppose every future-timelike translation subgroup `t ↦ U(t n)`, `n` in the open forward cone,
has positive energy. If `χ ∈ H` and `x ↦ ⟨χ, U(x)φ⟩` vanishes on a nonempty open set `W`, it
vanishes identically.

Only the group law at `φ` is used; the blueprint's closed invariant subspace `K₀ ∋ φ` supplies it.

For a vacuum state with unitaries `U'` indexed by the inhomogeneous Lorentz group, the
positive-energy hypothesis for `U = fun x => U' (translationSub x)` is the spectrum condition of
`HaagKastlerNet.IsVacuumStateConcrete` applied to `translationFlow n`.

Blueprint: lmm:timelike-spreading -/
theorem inner_translation_eq_zero
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    {φ : H} (hmul : ∀ x y, U (x + y) φ = U x (U y φ))
    (hpos : ∀ n : StandardMinkowskiSpacetime.Carrier,
      (n : SpacetimeModel) ∈ minkowskiForwardCone 0 → IsPositiveEnergy (fun t : ℝ => U (t • n)))
    (χ : H)
    {W : Set StandardMinkowskiSpacetime.Carrier} (hW : IsOpen W) (hWne : W.Nonempty)
    (hzero : ∀ x ∈ W, ⟪χ, U x φ⟫_ℂ = 0) :
    ∀ x, ⟪χ, U x φ⟫_ℂ = 0 := by
  obtain ⟨hcone, b, hb⟩ := futureTimelike_basis _ fun _ => rfl
  let n : Fin 4 → StandardMinkowskiSpacetime.Carrier := fun i => b i
  have hn : ∀ i, (n i : SpacetimeModel) ∈ minkowskiForwardCone 0 := fun i =>
    show b i ∈ _ by rw [hb]; exact hcone i
  let P : StandardMinkowskiSpacetime.Carrier → Prop := fun v => ∀ y ∈ W, ⟪χ, U (y + v) φ⟫_ℂ = 0
  have step : ∀ v, P v → ∀ i (t : ℝ), P (v + t • n i) := by
    intro v hv i t y hy
    have h := inner_translation_eq_zero_add_smul U hmul (hpos _ (hn i)) χ
      (W := (· - v) ⁻¹' W) (hW.preimage (continuous_id.sub continuous_const))
      (fun z hz => by simpa using hv _ hz) (y + v) (by simpa using hy) t
    rwa [← add_assoc]
  have key : ∀ s : Finset (Fin 4), ∀ c : Fin 4 → ℝ, P (∑ i ∈ s, c i • n i) := by
    intro s c
    induction s using Finset.induction_on with
    | empty => simpa [P] using hzero
    | insert j s hj ih => rw [Finset.sum_insert hj, add_comm]; exact step _ ih j (c j)
  obtain ⟨w, hw⟩ := hWne
  intro x
  have hx : ∑ i, b.repr (x - w) i • n i = x - w := b.sum_repr (x - w)
  have := key Finset.univ (b.repr (x - w)) w hw
  rwa [hx, add_sub_cancel] at this

end HaagKastler
end AQFT
end Physicslib4
