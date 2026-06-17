/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Isometry
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Topology on the isometry group and the identity component

This file makes the isometry group `Physicslib4.Spacetime.Isometry M` a
**topological group** and carves out the **identity-component subgroup** —
the isometries "connected to the identity" used by Axiom 5 of the
curved-spacetime Haag-Kastler axioms
(`def:isometric-covariance-in-curved-spacetime`).

## Main definitions / results

* `TopologicalSpace (Isometry M)`: the topology induced from the inclusion
  `g ↦ (g, g⁻¹)` into `C(M, M) × C(M, M)` (the standard topological-group
  topology on a transformation group).
* `IsTopologicalGroup (Isometry M)`.
* `Physicslib4.Spacetime.Isometry.identityComponent`: the identity-component
  subgroup `Subgroup.connectedComponentOfOne (Isometry M)`.

## Modelling notes

Taking the *bare* compact-open topology (induced from the forward map alone)
does not obviously make inversion continuous (the Arens problem). The
standard remedy, used here, is to induce the topology from **both** the map
and its inverse, `g ↦ (g, g⁻¹) ∈ C(M,M) × C(M,M)`:

* **Inversion** `g ↦ g⁻¹` corresponds to swapping the two coordinates, hence
  is continuous by construction.
* **Multiplication** is continuous because a finite-dimensional manifold `M`
  is locally compact (`ChartedSpace.locallyCompactSpace`), so composition
  `C(M,M) × C(M,M) → C(M,M)` is continuous (`ContinuousMap.continuous_comp'`).

This is exactly the Arens-style construction, and it discharges
`IsTopologicalGroup` outright, so the identity-component subgroup is
unconditional.
-/

namespace Physicslib4

namespace Spacetime

namespace Isometry

variable {M : Spacetime}

/-- A finite-dimensional manifold is locally compact, since its model space
`ℝ⁴` is. -/
instance instLocallyCompactSpace : LocallyCompactSpace M.Carrier :=
  ChartedSpace.locallyCompactSpace (H := SpacetimeModel) (M := M.Carrier)

/-- An isometry as a continuous self-map of the spacetime (its underlying
diffeomorphism, which is continuous). -/
noncomputable def toContinuousMap (g : Isometry M) : C(M.Carrier, M.Carrier) :=
  ⟨(g.toDiffeo : M.Carrier → M.Carrier), g.toDiffeo.continuous⟩

/-- An isometry as the pair of its underlying continuous self-map and the map
of its inverse. The group topology is induced from this inclusion into
`C(M,M) × C(M,M)`. -/
noncomputable def toProd (g : Isometry M) :
    C(M.Carrier, M.Carrier) × C(M.Carrier, M.Carrier) :=
  (toContinuousMap g, toContinuousMap g⁻¹)

/-- The topological-group topology on the isometry group, induced from the
inclusion `g ↦ (g, g⁻¹)` into `C(M,M) × C(M,M)`. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (Isometry M) :=
  TopologicalSpace.induced toProd inferInstance

theorem continuous_toProd : Continuous (toProd : Isometry M → _) :=
  continuous_induced_dom

theorem continuous_toContinuousMap :
    Continuous (toContinuousMap : Isometry M → C(M.Carrier, M.Carrier)) :=
  continuous_fst.comp continuous_toProd

theorem continuous_toContinuousMap_inv :
    Continuous (fun g : Isometry M => toContinuousMap g⁻¹) :=
  continuous_snd.comp continuous_toProd

/-- The forward map of a product is the composition of the forward maps. -/
theorem toContinuousMap_mul (a b : Isometry M) :
    toContinuousMap (a * b) = (toContinuousMap a).comp (toContinuousMap b) := by
  ext x
  exact congrFun (Diffeomorph.coe_trans b.toDiffeo a.toDiffeo) x

noncomputable instance : ContinuousInv (Isometry M) where
  continuous_inv := by
    rw [continuous_induced_rng]
    have h : toProd ∘ (fun g : Isometry M => g⁻¹) = Prod.swap ∘ toProd := by
      funext g
      simp only [Function.comp_apply, toProd, Prod.swap_prod_mk, inv_inv]
    rw [h]
    exact continuous_swap.comp continuous_toProd

noncomputable instance : ContinuousMul (Isometry M) where
  continuous_mul := by
    rw [continuous_induced_rng]
    have key : (toProd ∘ fun p : Isometry M × Isometry M => p.1 * p.2)
        = fun p => ((toContinuousMap p.1).comp (toContinuousMap p.2),
            (toContinuousMap p.2⁻¹).comp (toContinuousMap p.1⁻¹)) := by
      funext p
      simp only [Function.comp_apply, toProd, Prod.mk.injEq]
      refine ⟨toContinuousMap_mul p.1 p.2, ?_⟩
      rw [mul_inv_rev]
      exact toContinuousMap_mul p.2⁻¹ p.1⁻¹
    rw [key]
    refine Continuous.prodMk ?_ ?_
    · exact ContinuousMap.continuous_comp'.comp
        ((continuous_toContinuousMap.comp continuous_snd).prodMk
          (continuous_toContinuousMap.comp continuous_fst))
    · exact ContinuousMap.continuous_comp'.comp
        ((continuous_toContinuousMap_inv.comp continuous_fst).prodMk
          (continuous_toContinuousMap_inv.comp continuous_snd))

instance : IsTopologicalGroup (Isometry M) := ⟨⟩

/--
The **identity-component subgroup** of the isometry group: the isometries
*connected to the identity*, formalising the group used in Axiom 5
(`def:isometric-covariance-in-curved-spacetime`). It is the connected
component of `1`, a (normal) subgroup of the topological group.
-/
noncomputable def identityComponent (M : Spacetime) : Subgroup (Isometry M) :=
  Subgroup.connectedComponentOfOne (Isometry M)

end Isometry

end Spacetime

end Physicslib4
