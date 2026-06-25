/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.Net
import Physicslib4.GNS.UnitaryRepresentation
import Physicslib4.GNS.RadonNikodym

/-!
# Stabilizer action on a curved local algebra and its GNS unitary

In curved spacetime there is no quasilocal algebra, so the covariance
equivalences `covEquiv φ B : 𝔘(B) ≃⋆ₐ[ℂ] 𝔘(φ·B)` map *between different* local
algebras and do not assemble into a single unitary representation of the full
isometry group. They *do* restrict to a genuine action by automorphisms of a
single local algebra `𝔘(B)` on the **stabilizer subgroup**
`Stab(B) = {φ : φ·B = B}` of the region `B`: for such `φ`, `φ·B = B`, so
`covEquiv φ B : 𝔘(B) ≃⋆ₐ[ℂ] 𝔘(φ·B) = 𝔘(B)` is an automorphism of `𝔘(B)`.

This file builds that automorphism `stabAut`, proves it is a monoid action
(`stabAut_one`, `stabAut_mul`) using the curved covariance coherence
(`covEquiv_one`, `covEquiv_mul`), and instantiates the algebra-agnostic GNS
unitary `GNS.exists_gns_unitary_of_invariant` to produce a unitary
representation of `Stab(B)` on the GNS space of a `Stab(B)`-invariant state on
`𝔘(B)`.

## Main definitions / results

* `HaagKastlerNet.stabAut`: for `φ` with `φ·B = B`, the covariance
  automorphism of `𝔘(B)`.
* `HaagKastlerNet.stabAut_one`, `HaagKastlerNet.stabAut_mul`: it is a monoid
  action of `Stab(B)`.
* `HaagKastlerNet.exists_gns_unitary_stabilizer`: the GNS unitary representation
  of `Stab(B)` for a `Stab(B)`-invariant state on `𝔘(B)`.

## Physical interpretation

`Stab(B)` is the curved-spacetime stand-in for the global symmetry group: it is
the subgroup acting on the single algebra one actually has. Concretely it is
typically a Killing flow (e.g. the stationary `∂_t` flow of a Schwarzschild
exterior, giving a KMS/Hartle-Hawking state, or the de Sitter static-patch boost
giving the Gibbons-Hawking temperature) or a spatial-symmetry subgroup (e.g. the
rotation subgroup fixing a comoving ball in an FLRW cosmology).
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

open scoped Pointwise InnerProductSpace
open Physicslib4 Physicslib4.GNS

namespace HaagKastlerNet

variable {M : LorentzianSpacetime} (N : HaagKastlerNet M)

/-- Transport a local algebra along an equality of regions. -/
noncomputable def algCongr {B₁ B₂ : Set M.Carrier} (h : B₁ = B₂) :
    N.algebra B₁ ≃⋆ₐ[ℂ] N.algebra B₂ := by
  subst h; exact StarAlgEquiv.refl

theorem algCongr_apply {B₁ B₂ : Set M.Carrier} (h : B₁ = B₂) (a : N.algebra B₁) :
    N.algCongr h a = cast (congrArg N.algebra h) a := by
  subst h; rfl

/-- **Stabilizer automorphism.** For an isometry `φ` fixing the region `B`
(`φ·B = B`), the covariance equivalence `covEquiv φ B` lands back in `𝔘(B)` and
is therefore an automorphism of the single algebra `𝔘(B)`. -/
noncomputable def stabAut {B : Set M.Carrier} (φ : M.Isom) (h : φ • B = B) :
    N.algebra B ≃⋆ₐ[ℂ] N.algebra B :=
  (N.covEquiv φ B).trans (N.algCongr h)

theorem stabAut_apply {B : Set M.Carrier} (φ : M.Isom) (h : φ • B = B)
    (a : N.algebra B) :
    N.stabAut φ h a = cast (congrArg N.algebra h) (N.covEquiv φ B a) := by
  rw [stabAut, StarAlgEquiv.trans_apply, algCongr_apply]

/-- Naturality of `covEquiv` under an equality of regions. -/
theorem covEquiv_congr_region {B₁ B₂ : Set M.Carrier} (h : B₁ = B₂) (φ : M.Isom)
    (a : N.algebra B₁) :
    N.covEquiv φ B₂ (cast (congrArg N.algebra h) a)
      = cast (congrArg N.algebra (congrArg (φ • ·) h)) (N.covEquiv φ B₁ a) := by
  subst h; rfl

/-- **The stabilizer action is trivial at the identity.** -/
theorem stabAut_one {B : Set M.Carrier} (a : N.algebra B) :
    N.stabAut (1 : M.Isom) (one_smul M.Isom B) a = a := by
  rw [stabAut_apply, covEquiv_one]
  simp only [eq_mp_eq_cast, cast_cast, cast_eq]

/-- **The stabilizer action is multiplicative.** -/
theorem stabAut_mul {B : Set M.Carrier} (φ φ' : M.Isom)
    (hφ : φ • B = B) (hφ' : φ' • B = B) (hφφ' : (φ' * φ) • B = B)
    (a : N.algebra B) :
    N.stabAut (φ' * φ) hφφ' a = N.stabAut φ' hφ' (N.stabAut φ hφ a) := by
  rw [stabAut_apply, stabAut_apply, stabAut_apply, covEquiv_mul,
    N.covEquiv_congr_region hφ φ' (N.covEquiv φ B a)]
  simp only [eq_mp_eq_cast, cast_cast]

/-- The stabilizer automorphism as a function on the stabilizer subgroup
`Stab(B) = {φ : φ·B = B}`, packaged so the monoid-action laws are syntactic. -/
noncomputable def stabAutHom (B : Set M.Carrier)
    (φ : ↥(MulAction.stabilizer M.Isom B)) : N.algebra B ≃⋆ₐ[ℂ] N.algebra B :=
  N.stabAut φ.val (MulAction.mem_stabilizer_iff.mp φ.2)

theorem stabAutHom_one (B : Set M.Carrier) (a : N.algebra B) :
    N.stabAutHom B 1 a = a :=
  N.stabAut_one a

theorem stabAutHom_mul (B : Set M.Carrier)
    (g g' : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B) :
    N.stabAutHom B (g' * g) a = N.stabAutHom B g' (N.stabAutHom B g a) :=
  N.stabAut_mul g.val g'.val (MulAction.mem_stabilizer_iff.mp g.2)
    (MulAction.mem_stabilizer_iff.mp g'.2)
    (MulAction.mem_stabilizer_iff.mp (g' * g).2) a

/-- **GNS unitary representation of the stabilizer.** For a state `ω` on the
local algebra `𝔘(B)` that is invariant under the stabilizer action of
`Stab(B) = {φ : φ·B = B}`, the action is implemented on the GNS Hilbert space by
a unitary representation `U` of `Stab(B)`: there is a GNS triple `(H, π, Ω)` and
unitaries `U g` with `U g (π a Ω) = π (g · a) Ω`, `U g Ω = Ω`, the group laws,
and `U 1 = id`.

This is the curved-spacetime instantiation of
`GNS.exists_gns_unitary_of_invariant`, with the single algebra `A = 𝔘(B)` and
the stabilizer action `γ = stabAutHom`. -/
theorem exists_gns_unitary_stabilizer (B : Set M.Carrier)
    (ω : State (N.algebra B))
    (hinv : ∀ (g : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B),
        ω (N.stabAutHom B g a) = ω a) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : ↥(MulAction.stabilizer M.Isom B) → (H ≃ₗᵢ[ℂ] H)),
        (∀ a : N.algebra B, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (g : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B),
          U g (π a Ω) = π (N.stabAutHom B g a) Ω) ∧
        (∀ g : ↥(MulAction.stabilizer M.Isom B), U g Ω = Ω) ∧
        (∀ g g' : ↥(MulAction.stabilizer M.Isom B),
          U (g' * g) = (U g).trans (U g')) ∧
        U 1 = LinearIsometryEquiv.refl ℂ H ∧
        (∀ (g : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B) (x : H),
          U g (π a ((U g).symm x)) = π (N.stabAutHom B g a) x) ∧
        IsCyclicVector π Ω :=
  Physicslib4.GNS.exists_gns_unitary_of_invariant (N.stabAutHom B) ω hinv
    (fun g g' a => N.stabAutHom_mul B g g' a) (fun a => N.stabAutHom_one B a)

/-- **Strongly continuous GNS unitary representation of the stabilizer.**

Strengthening of `exists_gns_unitary_stabilizer`: if the isometry group `M.Isom`
carries a topology (passed as an instance argument, since the abstract
`LorentzianSpacetime` interface provides none) and the matrix coefficients
`g ↦ ω(a⋆ · g·b)` are continuous on `Stab(B)`, then the unitary representation
`U` of `Stab(B)` is strongly continuous: `g ↦ U g ψ` is continuous for every
GNS vector `ψ`.

The stabilizer subgroup `↥(MulAction.stabilizer M.Isom B)` inherits its topology
as a subspace of `M.Isom`. This is the curved-spacetime specialization of
`GNS.exists_gns_unitary_of_invariant_strongContinuous`. -/
theorem exists_gns_unitary_stabilizer_strongContinuous [TopologicalSpace M.Isom]
    (B : Set M.Carrier) (ω : State (N.algebra B))
    (hinv : ∀ (g : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B),
        ω (N.stabAutHom B g a) = ω a)
    (hwc : ∀ a b : N.algebra B,
        Continuous fun g : ↥(MulAction.stabilizer M.Isom B) =>
          (ω (star a * N.stabAutHom B g b) : ℂ)) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : ↥(MulAction.stabilizer M.Isom B) → (H ≃ₗᵢ[ℂ] H)),
        (∀ a : N.algebra B, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (g : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B),
          U g (π a Ω) = π (N.stabAutHom B g a) Ω) ∧
        (∀ g : ↥(MulAction.stabilizer M.Isom B), U g Ω = Ω) ∧
        (∀ g g' : ↥(MulAction.stabilizer M.Isom B),
          U (g' * g) = (U g).trans (U g')) ∧
        U 1 = LinearIsometryEquiv.refl ℂ H ∧
        (∀ ψ : H,
          Continuous fun g : ↥(MulAction.stabilizer M.Isom B) => U g ψ) ∧
        (∀ (g : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B) (x : H),
          U g (π a ((U g).symm x)) = π (N.stabAutHom B g a) x) :=
  Physicslib4.GNS.exists_gns_unitary_of_invariant_strongContinuous (N.stabAutHom B)
    ω hinv (fun g g' a => N.stabAutHom_mul B g g' a)
    (fun a => N.stabAutHom_one B a) hwc

/-- **The vacuum representation (curved spacetime).** A state `ω` on a local
algebra `𝔘(B)` that is invariant under the stabilizer action and pure yields a GNS
representation that is simultaneously *covariant* - implemented by a unitary
representation `U` of the stabilizer `Stab(B)` fixing the cyclic vector `Ω`, with
the operator covariance `U(g) π(a) U(g)⁻¹ = π(g · a)` - and *irreducible*. This is
the curved analogue of the Minkowski vacuum representation, valid per region since
there is no quasilocal algebra: it combines `exists_gns_unitary_stabilizer` with
purity ⟹ irreducibility (`isPure_iff_isIrreducible`). -/
theorem exists_gns_vacuum_stabilizer (B : Set M.Carrier)
    (ω : State (N.algebra B))
    (hinv : ∀ (g : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B),
        ω (N.stabAutHom B g a) = ω a)
    (hpure : IsPure ω) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
      (U : ↥(MulAction.stabilizer M.Isom B) → (H ≃ₗᵢ[ℂ] H)),
        IsCyclicVector π Ω ∧
        (∀ a : N.algebra B, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (∀ (g : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B),
          U g (π a Ω) = π (N.stabAutHom B g a) Ω) ∧
        (∀ g : ↥(MulAction.stabilizer M.Isom B), U g Ω = Ω) ∧
        (∀ g g' : ↥(MulAction.stabilizer M.Isom B),
          U (g' * g) = (U g).trans (U g')) ∧
        U 1 = LinearIsometryEquiv.refl ℂ H ∧
        (∀ (g : ↥(MulAction.stabilizer M.Isom B)) (a : N.algebra B) (x : H),
          U g (π a ((U g).symm x)) = π (N.stabAutHom B g a) x) ∧
        IsIrreducible π := by
  obtain ⟨H, i1, i2, i3, π, Ω, U, hrepro, himpl, hUΩ, hmul, hUone, hopcov, hcyc⟩ :=
    N.exists_gns_unitary_stabilizer B ω hinv
  exact ⟨H, i1, i2, i3, π, Ω, U, hcyc, hrepro, himpl, hUΩ, hmul, hUone, hopcov,
    (isPure_iff_isIrreducible hcyc hrepro).mp hpure⟩

end HaagKastlerNet

end HaagKastlerCurved
end AQFT
end Physicslib4
