/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Unbounded.Commuting

/-!
# Unitary conjugation of unbounded operators

For a unitary `V` and an operator `A` on `H`, the conjugate `V A V⁻¹` has domain
`{ψ | V⁻¹ψ ∈ Dom A}` and value `V (A (V⁻¹ψ))`. Its graph is the image of the graph of `A` under
`Φ_V (φ, ψ) = (V φ, V ψ)`. The statements below say "`B = V A V⁻¹`, including domains" as the
graph identity `B.graph = A.graph.map Φ_V`, which determines `B` (`LinearPMap.eq_of_eq_graph`).
`Φ_V` is written `Φ[V]`, a local notation for `LinearMap.prodMap V V`.

## Main statements

* `image_closure_prodMap_unitary`: `Φ_V` is a homeomorphism of `H × H` and commutes with closure.
* `graph_antiunitaryConj_trans_antiunitaryConj`: `(VC)(CAC⁻¹)(VC)⁻¹ = VAV⁻¹`.
* `unitaryCommutes_of_graph_map_eq`: an operator invariant under conjugation by `V` commutes
  with `V`.
* `functionalCalculus_unitaryConj`: `V f(A) V⁻¹ = f(V A V⁻¹)` for real measurable `f`.
* `functionalCalculus_unitaryConj_of_bounded`: the same for bounded measurable complex `f`.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The map `Φ_V (φ, ψ) = (V φ, V ψ)` of `H × H` induced by a unitary `V`. -/
local notation "Φ[" V "]" =>
  LinearMap.prodMap (LinearEquiv.toLinearMap (LinearIsometryEquiv.toLinearEquiv V))
    (LinearEquiv.toLinearMap (LinearIsometryEquiv.toLinearEquiv V))

omit [CompleteSpace H] in
/-- For a unitary `V`, the map `Φ_V (φ, ψ) = (V φ, V ψ)` is a homeomorphism of `H × H`, so
`Φ_V (closure G) = closure (Φ_V G)` for every `G ⊆ H × H`.

Blueprint: lmm:unitary-conjugate-graph -/
theorem image_closure_prodMap_unitary (V : H ≃ₗᵢ[ℂ] H) :
    IsHomeomorph (Prod.map V V) ∧
      ∀ G : Set (H × H), Prod.map V V '' closure G = closure (Prod.map V V '' G) :=
  let e := V.toHomeomorph.prodCongr V.toHomeomorph
  ⟨e.isHomeomorph, e.image_closure⟩

omit [CompleteSpace H] in
/-- For a unitary `V`, an antiunitary involution `C` and a linear operator `A`, the antiunitary
`VC` satisfies `(VC)(CAC⁻¹)(VC)⁻¹ = VAV⁻¹`, including domains: the graph of the double conjugate
is `Φ_V` of the graph of `A`. (`VC` is antiunitary by its type `H ≃ₗᵢ⋆[ℂ] H`.)

Blueprint: lmm:unitary-conjugate-double-antiunitary -/
theorem graph_antiunitaryConj_trans_antiunitaryConj (V : H ≃ₗᵢ[ℂ] H) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (A : H →ₗ.[ℂ] H) :
    (antiunitaryConj (C.trans V) (antiunitaryConj C A)).graph = A.graph.map Φ[V] := by
  have hCs : ∀ y, C.symm (C.symm y) = y := fun y => by
    rw [C.symm_apply_eq.2 (hC y).symm, C.symm_apply_eq.2 (hC (C y)).symm, hC]
  have hmem : ∀ x, x ∈ (antiunitaryConj (C.trans V) (antiunitaryConj C A)).domain ↔
      V.symm x ∈ A.domain := fun x => by
    change C.symm (C.symm (V.symm x)) ∈ A.domain ↔ _
    rw [hCs]
  have hval : ∀ x (hx : x ∈ (antiunitaryConj (C.trans V) (antiunitaryConj C A)).domain),
      (antiunitaryConj (C.trans V) (antiunitaryConj C A)) ⟨x, hx⟩ =
        V (A ⟨V.symm x, (hmem x).1 hx⟩) := fun x hx => by
    change V (C (C (A ⟨C.symm (C.symm (V.symm x)), _⟩))) = _
    rw [hC]
    congr 3
    exact hCs _
  ext ⟨x, y⟩
  rw [LinearPMap.mem_graph_iff, Submodule.mem_map]
  constructor
  · rintro ⟨⟨z, hz⟩, rfl, rfl⟩
    refine ⟨(V.symm z, A ⟨V.symm z, (hmem z).1 hz⟩), A.mem_graph ⟨V.symm z, (hmem z).1 hz⟩, ?_⟩
    simp [hval]
  · rintro ⟨⟨a, b⟩, hab, he⟩
    rw [LinearPMap.mem_graph_iff] at hab
    obtain ⟨⟨a', ha'⟩, rfl, rfl⟩ := hab
    simp only [LinearMap.prodMap_apply, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hx : V a' ∈ (antiunitaryConj (C.trans V) (antiunitaryConj C A)).domain :=
      (hmem _).2 (by simpa using ha')
    refine ⟨⟨V a', hx⟩, rfl, ?_⟩
    rw [hval]
    simp

omit [CompleteSpace H] in
/-- A linear operator `A` with `V A V⁻¹ = A`, including domains, commutes with the unitary `V`:
`V` and `V⁻¹` map `Dom A` into itself and commute with `A` there.

The case of an everywhere-defined, possibly antilinear, map is
`comm_of_unitary_conj_eq`.

Blueprint: lmm:unitary-commutes-of-conj-eq -/
theorem unitaryCommutes_of_graph_map_eq (V : H ≃ₗᵢ[ℂ] H) {A : H →ₗ.[ℂ] H}
    (hA : A.graph.map Φ[V] = A.graph) :
    UnitaryCommutes V A := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hm : ((V x, V (A ⟨x, hx⟩)) : H × H) ∈ A.graph :=
      hA ▸ Submodule.mem_map_of_mem (f := Φ[V]) (A.mem_graph ⟨x, hx⟩)
    obtain ⟨⟨y, hy⟩, h1, h2⟩ := (A.mem_graph_iff).1 hm
    obtain rfl : y = V x := h1
    exact ⟨hy, h2⟩
  · have hm : ((x, A ⟨x, hx⟩) : H × H) ∈ A.graph.map Φ[V] := by
      rw [hA]; exact A.mem_graph ⟨x, hx⟩
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hm
    obtain ⟨⟨z, hz⟩, h1, h2⟩ := (A.mem_graph_iff).1 hp
    obtain ⟨e1, e2⟩ := Prod.ext_iff.1 hpe
    simp only [LinearMap.prodMap_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] at e1 e2
    have hz' : V.symm x = z := by rw [← e1, V.symm_apply_apply]; exact h1.symm
    subst hz'
    refine ⟨hz, ?_⟩
    rw [h2, ← e2, V.symm_apply_apply]

omit [CompleteSpace H] in
/-- An everywhere-defined map `A : H → H`, linear or antilinear, with `V A V⁻¹ = A` commutes
with the unitary `V`: `V (A ψ) = A (V ψ)` for every `ψ`.

Blueprint: lmm:unitary-commutes-of-conj-eq -/
theorem comm_of_unitary_conj_eq (V : H ≃ₗᵢ[ℂ] H) {A : H → H}
    (hA : ∀ ψ, V (A (V.symm ψ)) = A ψ) :
    ∀ ψ, V (A ψ) = A (V ψ) := fun ψ => by
  rw [← hA (V ψ), V.symm_apply_apply]

/-- Unitary conjugation transports the functional calculus: if `A` is self-adjoint and
`B = V A V⁻¹`, including domains, then `B` is self-adjoint and `V f(A) V⁻¹ = f(B)`, including
domains, for every real measurable `f`.

The operator `V A V⁻¹` is named by its graph, `B.graph = Φ_V (A.graph)`, so that `f(B)` can be
taken for any operator `B` known to equal `V A V⁻¹`.

Blueprint: lmm:unitary-transport-functional-calculus -/
theorem functionalCalculus_unitaryConj (V : H ≃ₗᵢ[ℂ] H) {A B : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : B.graph = A.graph.map Φ[V]) :
    IsSelfAdjoint B ∧ ∀ (hB' : IsSelfAdjoint B) (f : ℝ → ℝ), Measurable f →
      (functionalCalculus hB' fun x => (f x : ℂ)).graph =
        (functionalCalculus hA fun x => (f x : ℂ)).graph.map Φ[V] := by
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis ℂ H
  let C : H ≃ₗᵢ⋆[ℂ] H := (b.repr.trans (starₗᵢ ℂ)).trans b.repr.symm
  have hC : ∀ x, C (C x) = x := fun x => by simp [C]
  obtain ⟨h1, e1⟩ := functionalCalculus_antiunitaryConj C hA
  obtain ⟨h2, e2⟩ := functionalCalculus_antiunitaryConj (C.trans V) h1
  obtain rfl : B = antiunitaryConj (C.trans V) (antiunitaryConj C A) :=
    LinearPMap.eq_of_eq_graph (by rw [hB, graph_antiunitaryConj_trans_antiunitaryConj V C hC])
  refine ⟨h2, fun _ f hf => ?_⟩
  rw [← e2 f hf, ← e1 f hf, graph_antiunitaryConj_trans_antiunitaryConj V C hC]

/-- Unitary conjugation of a bounded complex function: if `A` is self-adjoint, `B = V A V⁻¹`
(including domains, hence self-adjoint) and `f : ℝ → ℂ` is bounded and measurable, then
`V f(A) V⁻¹ ψ = f(B) ψ` for every `ψ ∈ H`. Both `f(A)` and `f(B)` are everywhere defined, and
the identity is stated as the graph identity `f(B) = V f(A) V⁻¹`.

Blueprint: lmm:unitary-transport-bounded-fc -/
theorem functionalCalculus_unitaryConj_of_bounded (V : H ≃ₗᵢ[ℂ] H) {A B : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : B.graph = A.graph.map Φ[V])
    {f : ℝ → ℂ} (hf : Measurable f) (hfb : ∃ c, ∀ x, ‖f x‖ ≤ c) :
    (functionalCalculus hB f).graph = (functionalCalculus hA f).graph.map Φ[V] := by
  have hfB : f ∈ BddMeasurable ℝ := ⟨hf, hfb⟩
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis ℂ H
  let C : H ≃ₗᵢ⋆[ℂ] H := (b.repr.trans (starₗᵢ ℂ)).trans b.repr.symm
  have hC : ∀ x, C (C x) = x := fun x => by simp [C]
  have hCs : ∀ y, C.symm (C.symm y) = y := fun y => by
    rw [C.symm_apply_eq.2 (hC y).symm, C.symm_apply_eq.2 (hC (C y)).symm, hC]
  obtain ⟨h1, e1⟩ := integral_antiunitaryConj C hA
  obtain ⟨h2, e2⟩ := integral_antiunitaryConj (C.trans V) h1
  obtain rfl : B = antiunitaryConj (C.trans V) (antiunitaryConj C A) :=
    LinearPMap.eq_of_eq_graph (by rw [hAB, graph_antiunitaryConj_trans_antiunitaryConj V C hC])
  have hfc : (fun x => starRingEnd ℂ (f x)) ∈ BddMeasurable ℝ :=
    ⟨Complex.continuous_conj.measurable.comp hf, hfb.imp fun c hc x => by simpa using hc x⟩
  have key : ∀ ψ, (spectralMeasure hB).integral f ψ =
      V ((spectralMeasure hA).integral f (V.symm ψ)) := fun ψ => by
    have := e2 _ hfc ψ
    simp only [Complex.conj_conj] at this
    rw [← this, ← e1 f hfB]
    simp [hCs, hC]
  rw [(functionalCalculus_of_bddMeasurable hB hfB).2,
    (functionalCalculus_of_bddMeasurable hA hfB).2]
  ext ⟨x, y⟩
  simp only [LinearPMap.mem_graph_iff, Submodule.mem_map]
  constructor
  · rintro ⟨⟨x, -⟩, rfl, rfl⟩
    exact ⟨(V.symm x, (spectralMeasure hA).integral f (V.symm x)),
      ⟨⟨V.symm x, Submodule.mem_top⟩, rfl, rfl⟩, by simp [key]⟩
  · rintro ⟨⟨a, c⟩, hac, he⟩
    simp only [LinearMap.prodMap_apply, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨⟨a', -⟩, rfl, rfl⟩ := hac
    exact ⟨⟨_, Submodule.mem_top⟩, rfl, by simp [key]⟩

end Unbounded
end Spectral
end Physicslib4
