/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.EinsteinCausality
import Physicslib4.GNS.Irreducibility
import Physicslib4.Operators.Conjugation

/-!
# Local von Neumann algebras and spacelike commutation (curved spacetime)

This is the curved-spacetime counterpart of the Minkowski local von Neumann
algebra construction. There is no quasilocal algebra in curved spacetime, so the
relevant representations are of a containing basis algebra `𝔘(B)`. Given such a
representation `π`, the *local von Neumann algebra* of a subregion `B' ⊆ B` is the
bicommutant `R(B') = π(𝔘(B'))''` of the local observable operators (the embedding
`𝔘(B') → 𝔘(B)` being the isotony witness `commIsotony`). Mathlib models the
commutant by `Set.centralizer`, so `R(B')` is the double centralizer.

The headline result is **microcausality at the von Neumann level**: for completely
spacelike-separated subregions `B₁, B₂ ⊆ B`, the local algebras commute,
`R(B₁) ⊆ R(B₂)'`. It is the von Neumann form of curved Einstein causality
(`einstein_causality`): elementwise commutation of the local operators, pushed
through the centralizer.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved
namespace HaagKastlerNet

open Physicslib4.GNS

variable {M : LorentzianSpacetime} (N : HaagKastlerNet M)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The local observable operators of a subregion `B' ⊆ B` in a representation `π`
of the containing algebra `𝔘(B)`: the image `π(𝔘(B'))` of the local algebra under
the isotony embedding. -/
def localOperators {B : Set M.Carrier} (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B' : Set M.Carrier⦄ (hB' : M.IsBasisSet B') (hB : M.IsBasisSet B)
    (h : B' ⊆ B) : Set (H →L[ℂ] H) :=
  Set.range fun a : N.algebra B' => π (N.commIsotony hB' hB h a)

/-- The **local von Neumann algebra** `R(B') = π(𝔘(B'))''`, the bicommutant of the
local observable operators (the commutant being `Set.centralizer`). -/
def localVonNeumann {B : Set M.Carrier} (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B' : Set M.Carrier⦄ (hB' : M.IsBasisSet B') (hB : M.IsBasisSet B)
    (h : B' ⊆ B) : Set (H →L[ℂ] H) :=
  Set.centralizer (Set.centralizer (N.localOperators π hB' hB h))

/-- **Microcausality at the von Neumann level (curved spacetime).** For completely
spacelike-separated basis subregions `B₁, B₂ ⊆ B`, the local von Neumann algebras
commute: `R(B₁) ⊆ R(B₂)'`. This is the von Neumann form of curved Einstein
causality. -/
theorem localVonNeumann_subset_centralizer
    {B : Set M.Carrier} (hB : M.IsBasisSet B)
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
    N.localVonNeumann π hB₁ hB h₁ ⊆ Set.centralizer (N.localVonNeumann π hB₂ hB h₂) := by
  have hcomm :
      N.localOperators π hB₂ hB h₂ ⊆ Set.centralizer (N.localOperators π hB₁ hB h₁) := by
    rintro y ⟨b, rfl⟩
    rw [Set.mem_centralizer_iff]
    rintro x ⟨a, rfl⟩
    exact N.einstein_causality hB π hB₁ hB₂ hs h₁ h₂ a b
  have h1 : N.localVonNeumann π hB₁ hB h₁ ⊆ Set.centralizer (N.localOperators π hB₂ hB h₂) :=
    Set.centralizer_subset hcomm
  change N.localVonNeumann π hB₁ hB h₁
    ⊆ Set.centralizer (Set.centralizer (Set.centralizer (N.localOperators π hB₂ hB h₂)))
  rwa [Set.centralizer_centralizer_centralizer]

/-- **Isotony of the net of von Neumann algebras (curved spacetime).** For nested
basis subregions `B₁ ⊆ B₂ ⊆ B`, the local von Neumann algebras are nested:
`R(B₁) ⊆ R(B₂)`. Unlike Minkowski, the curved Axiom 3 isotony embeddings
(`commIsotony`) are chosen witnesses with no built-in composition law, so the
coherence `commIsotony (B₁ ⊆ B) = commIsotony (B₂ ⊆ B) ∘ commIsotony (B₁ ⊆ B₂)`
is taken as an explicit hypothesis `hcoh` (it is automatic whenever the embeddings
are coherent, e.g. for a net whose Axiom 3 witnesses come from a genuine inclusion
family). Given it, the local observables of `B₁` embed into those of `B₂` and the
double commutant is monotone. -/
theorem localVonNeumann_mono
    {B : Set M.Carrier} (hB : M.IsBasisSet B)
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄
    (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁₂ : B₁ ⊆ B₂) (h₂ : B₂ ⊆ B)
    (hcoh : ∀ a : N.algebra B₁,
        N.commIsotony hB₁ hB (h₁₂.trans h₂) a
          = N.commIsotony hB₂ hB h₂ (N.commIsotony hB₁ hB₂ h₁₂ a)) :
    N.localVonNeumann π hB₁ hB (h₁₂.trans h₂) ⊆ N.localVonNeumann π hB₂ hB h₂ := by
  have hsub : N.localOperators π hB₁ hB (h₁₂.trans h₂)
      ⊆ N.localOperators π hB₂ hB h₂ := by
    rintro x ⟨a, rfl⟩
    exact ⟨N.commIsotony hB₁ hB₂ h₁₂ a, congrArg π (hcoh a).symm⟩
  exact Set.centralizer_subset (Set.centralizer_subset hsub)

omit [CompleteSpace H] in
/-- **Statistical independence (abstract form).** If `Ω` is cyclic for a set `S` of
operators (the vectors `T Ω`, `T ∈ S`, are dense), then any operator `R` commuting
with every element of `S` and annihilating `Ω` is zero. Equivalently, `Ω` is
separating for the commutant of `S`. -/
theorem eq_zero_of_commute_of_cyclic {S : Set (H →L[ℂ] H)} {Ω : H}
    (hcyc : Dense ((fun T => T Ω) '' S)) {R : H →L[ℂ] H}
    (hcomm : ∀ T ∈ S, R * T = T * R) (hRΩ : R Ω = 0) : R = 0 := by
  have hzero : Set.EqOn (⇑R) (fun _ => (0 : H)) ((fun T => T Ω) '' S) := by
    rintro _ ⟨T, hT, rfl⟩
    change R (T Ω) = 0
    rw [← mul_apply_eq_comp, hcomm T hT, mul_apply_eq_comp, hRΩ,
      map_zero]
  have hRx : (⇑R) = fun _ => (0 : H) :=
    Continuous.ext_on hcyc R.continuous continuous_const hzero
  exact ContinuousLinearMap.ext fun x =>
    (congrFun hRx x).trans (zero_apply x).symm

/-- **Statistical independence (Schlieder property) for spacelike curved regions.**
If `Ω` is cyclic for the local observables of `B₁` - the role supplied in
Minkowski spacetime by Reeh-Schlieder - then a nonzero element of the
spacelike-separated local von Neumann algebra `R(B₂)` cannot annihilate `Ω`:
`R Ω = 0 ⟹ R = 0`. So `Ω` is separating for `R(B₂)`, the operator-algebraic form
of the statistical independence of spacelike-separated local algebras. -/
theorem localVonNeumann_separating
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) {Ω : H}
    (hcyc : Dense ((fun T => T Ω) '' N.localOperators π hB₁ hB h₁))
    {R : H →L[ℂ] H} (hR : R ∈ N.localVonNeumann π hB₂ hB h₂) (hRΩ : R Ω = 0) :
    R = 0 := by
  refine eq_zero_of_commute_of_cyclic hcyc (fun A hA => ?_) hRΩ
  have hA' : A ∈ Set.centralizer (N.localVonNeumann π hB₂ hB h₂) :=
    N.localVonNeumann_subset_centralizer hB π hB₁ hB₂ hs h₁ h₂
      (Set.subset_centralizer_centralizer hA)
  exact (Set.mem_centralizer_iff.mp hA') R hR

/-- The local observable operators `π(𝔘(B'))` form a self-adjoint set: `π` and the
isotony embedding `commIsotony` are `*`-homomorphisms. -/
theorem localOperators_selfAdjoint {B : Set M.Carrier}
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B' : Set M.Carrier⦄ (hB' : M.IsBasisSet B') (hB : M.IsBasisSet B) (h : B' ⊆ B) :
    ∀ x ∈ N.localOperators π hB' hB h, star x ∈ N.localOperators π hB' hB h := by
  rintro x ⟨a, rfl⟩
  exact ⟨star a, by simp only [map_star]⟩

/-- The **local von Neumann algebra** `R(B')` as a genuine `VonNeumannAlgebra`: the
bicommutant of the self-adjoint set of local observable operators inside `B(H)`.
Its underlying set is `localVonNeumann π hB' hB h`. -/
noncomputable def localVonNeumannAlgebra {B : Set M.Carrier}
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B' : Set M.Carrier⦄ (hB' : M.IsBasisSet B') (hB : M.IsBasisSet B) (h : B' ⊆ B) :
    VonNeumannAlgebra H :=
  vonNeumannOfSelfAdjoint (N.localOperators π hB' hB h)
    (N.localOperators_selfAdjoint π hB' hB h)

@[simp] theorem coe_localVonNeumannAlgebra {B : Set M.Carrier}
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B' : Set M.Carrier⦄ (hB' : M.IsBasisSet B') (hB : M.IsBasisSet B) (h : B' ⊆ B) :
    (N.localVonNeumannAlgebra π hB' hB h : Set (H →L[ℂ] H))
      = N.localVonNeumann π hB' hB h :=
  coe_vonNeumannOfSelfAdjoint _ _

/-- **Microcausality, bundled (curved spacetime).** For completely spacelike-separated
subregions `B₁, B₂ ⊆ B`, the bundled local von Neumann algebras commute,
`R(B₁) ≤ R(B₂)'`. -/
theorem localVonNeumannAlgebra_le_commutant {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
    N.localVonNeumannAlgebra π hB₁ hB h₁
      ≤ (N.localVonNeumannAlgebra π hB₂ hB h₂).commutant := by
  rw [← SetLike.coe_subset_coe]
  simp only [coe_localVonNeumannAlgebra, VonNeumannAlgebra.coe_commutant]
  exact N.localVonNeumann_subset_centralizer hB π hB₁ hB₂ hs h₁ h₂

/-- **Isotony, bundled (curved spacetime).** `B₁ ⊆ B₂ ⊆ B` (with the isotony
coherence) gives `R(B₁) ≤ R(B₂)`. -/
theorem localVonNeumannAlgebra_mono {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁₂ : B₁ ⊆ B₂) (h₂ : B₂ ⊆ B)
    (hcoh : ∀ a : N.algebra B₁,
        N.commIsotony hB₁ hB (h₁₂.trans h₂) a
          = N.commIsotony hB₂ hB h₂ (N.commIsotony hB₁ hB₂ h₁₂ a)) :
    N.localVonNeumannAlgebra π hB₁ hB (h₁₂.trans h₂)
      ≤ N.localVonNeumannAlgebra π hB₂ hB h₂ := by
  rw [← SetLike.coe_subset_coe]
  simp only [coe_localVonNeumannAlgebra]
  exact N.localVonNeumann_mono hB π hB₁ hB₂ h₁₂ h₂ hcoh

/-- **Statistical independence, bundled (curved spacetime).** If `Ω` is cyclic for the
local observables of `B₁`, then `Ω` is separating for the bundled local von Neumann
algebra `R(B₂)` of a spacelike-separated subregion: any `R ∈ R(B₂)` with `R Ω = 0` is
zero. -/
theorem localVonNeumannAlgebra_separating {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) {Ω : H}
    (hcyc : Dense ((fun T => T Ω) '' N.localOperators π hB₁ hB h₁))
    {R : H →L[ℂ] H} (hR : R ∈ N.localVonNeumannAlgebra π hB₂ hB h₂) (hRΩ : R Ω = 0) :
    R = 0 := by
  refine N.localVonNeumann_separating hB π hB₁ hB₂ hs h₁ h₂ hcyc ?_ hRΩ
  rwa [← SetLike.mem_coe, coe_localVonNeumannAlgebra] at hR

/-- The chosen Axiom-3 isotony embeddings `commIsotony` are **coherent below `B`**:
for nested basis subregions `B₁ ⊆ B₂ ⊆ B`, the direct embedding `𝔘(B₁) → 𝔘(B)` factors
through `𝔘(B₂)`.

Unlike Minkowski spacetime — whose `QuasilocalAlgebra` carries the `ι_inclusion` coherence
as *data*, making von Neumann isotony unconditional — the curved Axiom 3 selects its
isotony witnesses via `Classical.choose` (`commIsotony`). The composition law below is
therefore not available for free for *any* net: even the trivial net, whose witness is the
identity, hides it behind `Classical.choose` (which does not reduce to the witness), and
`toAbstract` does not touch the net's Axiom-3 data. It must be assumed; it holds for any
net whose Axiom-3 witnesses form a genuine inclusion family. -/
def IsIsotonyCoherentBelow {B : Set M.Carrier} (hB : M.IsBasisSet B) : Prop :=
  ∀ ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁₂ : B₁ ⊆ B₂) (h₂ : B₂ ⊆ B) (a : N.algebra B₁),
      N.commIsotony hB₁ hB (h₁₂.trans h₂) a
        = N.commIsotony hB₂ hB h₂ (N.commIsotony hB₁ hB₂ h₁₂ a)

/-- **The net of von Neumann algebras as an order-preserving map (curved spacetime).**
Fixing a containing basis region `B` and a representation `π` of `𝔘(B)`, and assuming the
isotony embeddings are coherent below `B` (`IsIsotonyCoherentBelow`), the assignment
`B' ↦ R(B')` is a monotone map from the poset of basis subregions of `B` (ordered by
inclusion) to the von Neumann algebras of `B(H)`. This is the curved counterpart of the
Minkowski `vonNeumannNet`: the local net restricted to a containing region is a functor on
the inclusion poset, sending containment of regions to containment of algebras.

The coherence enters as a single hypothesis rather than being discharged geometrically:
unlike spacelike-monotonicity (a spacetime fact discharged over `toAbstract` by
`commute_of_spacelike_mono_geometric`), it is a property of the net's chosen Axiom-3
embeddings, not of the underlying spacetime. The map is nonetheless *unconditional* in
that its monotonicity field carries no per-edge side condition. -/
noncomputable def vonNeumannNet {B : Set M.Carrier} (hB : M.IsBasisSet B)
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hcoh : N.IsIsotonyCoherentBelow hB) :
    {B' : Set M.Carrier // M.IsBasisSet B' ∧ B' ⊆ B} →o VonNeumannAlgebra H where
  toFun B' := N.localVonNeumannAlgebra π B'.2.1 hB B'.2.2
  monotone' B₁ B₂ h :=
    N.localVonNeumannAlgebra_mono hB π B₁.2.1 B₂.2.1 h B₂.2.2
      (hcoh B₁.2.1 B₂.2.1 h B₂.2.2)

/-- The **relative commutant** of a nested pair `R(B₁) ⊆ R(B₂)` of subregions of a
containing region `B`, in a representation `π` of `𝔘(B)`: the von Neumann algebra
`R(B₁)' ∩ R(B₂)`, built as the meet of the star-subalgebras of the commutant of
`R(B₁)` and of `R(B₂)`. Its underlying set is `R(B₁)' ∩ R(B₂)`. Curved counterpart
of the Minkowski relative commutant; the basic object of local-algebra inclusion
theory. -/
noncomputable def relativeCommutant {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) : VonNeumannAlgebra H where
  toStarSubalgebra :=
    (N.localVonNeumannAlgebra π hB₁ hB h₁).commutant.toStarSubalgebra ⊓
      (N.localVonNeumannAlgebra π hB₂ hB h₂).toStarSubalgebra
  centralizer_centralizer' := by
    -- Compute the carrier of the meet as the intersection of the two factors
    have hcarrier : ((N.localVonNeumannAlgebra π hB₁ hB h₁).commutant.toStarSubalgebra ⊓
        (N.localVonNeumannAlgebra π hB₂ hB h₂).toStarSubalgebra).carrier =
      Set.centralizer (N.localVonNeumann π hB₁ hB h₁) ∩ N.localVonNeumann π hB₂ hB h₂ := by
      ext x; simp
    -- Both factors are centralizers, so the intersection is `centralizer (_ ∪ _)`,
    -- hence commutant-closed by the triple centralizer theorem.
    rw [hcarrier,
      show N.localVonNeumann π hB₂ hB h₂
          = Set.centralizer (Set.centralizer (N.localOperators π hB₂ hB h₂)) from rfl,
      ← Set.centralizer_union, Set.centralizer_centralizer_centralizer]

/-- The underlying set of the relative commutant is `R(B₁)' ∩ R(B₂)`. -/
@[simp] theorem coe_relativeCommutant {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
    (N.relativeCommutant hB π hB₁ hB₂ h₁ h₂ : Set (H →L[ℂ] H))
      = Set.centralizer (N.localVonNeumann π hB₁ hB h₁) ∩ N.localVonNeumann π hB₂ hB h₂ := by
  simp [relativeCommutant, VonNeumannAlgebra.coe_commutant, coe_localVonNeumannAlgebra,
    StarSubalgebra.coe_inf]

/-- **The relative commutant lies in the larger algebra:** `R(B₁)' ∩ R(B₂) ≤ R(B₂)`. -/
theorem relativeCommutant_le_right {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
    N.relativeCommutant hB π hB₁ hB₂ h₁ h₂ ≤ N.localVonNeumannAlgebra π hB₂ hB h₂ := by
  rw [← SetLike.coe_subset_coe]
  simp only [coe_relativeCommutant, coe_localVonNeumannAlgebra]
  exact Set.inter_subset_right

/-- **The relative commutant commutes with the smaller algebra:** its underlying set
is contained in `R(B₁)'`. -/
theorem relativeCommutant_coe_subset_commutant {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
    (N.relativeCommutant hB π hB₁ hB₂ h₁ h₂ : Set (H →L[ℂ] H))
      ⊆ Set.centralizer (N.localVonNeumann π hB₁ hB h₁) := by
  simp [relativeCommutant, coe_localVonNeumannAlgebra, VonNeumannAlgebra.coe_commutant,
    StarSubalgebra.coe_inf]

/-- **The relative commutant contains the center of the ambient algebra.** For nested
basis subregions `B₁ ⊆ B₂ ⊆ B` (with the isotony coherence `hcoh`), the center
`R(B₂) ∩ R(B₂)'` is contained in `R(B₁)' ∩ R(B₂)`. Via isotony `R(B₁) ≤ R(B₂)` and
antitonicity of the commutant. -/
theorem center_le_relativeCommutant {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁₂ : B₁ ⊆ B₂) (h₂ : B₂ ⊆ B)
    (hcoh : ∀ a : N.algebra B₁,
        N.commIsotony hB₁ hB (h₁₂.trans h₂) a
          = N.commIsotony hB₂ hB h₂ (N.commIsotony hB₁ hB₂ h₁₂ a)) :
    N.localVonNeumann π hB₂ hB h₂ ∩ Set.centralizer (N.localVonNeumann π hB₂ hB h₂)
      ⊆ (N.relativeCommutant hB π hB₁ hB₂ (h₁₂.trans h₂) h₂ : Set (H →L[ℂ] H)) := by
  rw [coe_relativeCommutant]
  rintro x ⟨hx1, hx2⟩
  have hsub : N.localVonNeumann π hB₁ hB (h₁₂.trans h₂) ⊆ N.localVonNeumann π hB₂ hB h₂ :=
    N.localVonNeumann_mono hB π hB₁ hB₂ h₁₂ h₂ hcoh
  exact ⟨Set.centralizer_subset hsub hx2, hx1⟩

/-- The inclusion `R(B₁) ⊆ R(B₂)` of subregions of `B` is **irreducible** when its
relative commutant is trivial: `R(B₁)' ∩ R(B₂) = ℂ·1`. Curved counterpart of the
subfactor-theoretic notion of an irreducible inclusion. -/
def IsIrreducibleInclusion {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) : Prop :=
  (N.relativeCommutant hB π hB₁ hB₂ h₁ h₂ : Set (H →L[ℂ] H)) = scalarOperators H

/-- **An irreducible inclusion forces the ambient algebra to be a factor (curved
spacetime).** For nested basis subregions `B₁ ⊆ B₂ ⊆ B` (with the isotony coherence
`hcoh`), if the inclusion `R(B₁) ⊆ R(B₂)` is irreducible then `R(B₂)` is a factor. The
center `R(B₂) ∩ R(B₂)'` lies in the relative commutant (`center_le_relativeCommutant`),
which is the scalars by hypothesis; the scalars are always central, giving equality. -/
theorem isFactor_of_isIrreducibleInclusion {B : Set M.Carrier}
    (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁₂ : B₁ ⊆ B₂) (h₂ : B₂ ⊆ B)
    (hcoh : ∀ a : N.algebra B₁,
        N.commIsotony hB₁ hB (h₁₂.trans h₂) a
          = N.commIsotony hB₂ hB h₂ (N.commIsotony hB₁ hB₂ h₁₂ a))
    (hirr : N.IsIrreducibleInclusion hB π hB₁ hB₂ (h₁₂.trans h₂) h₂) :
    IsFactor (N.localVonNeumann π hB₂ hB h₂) := by
  rw [IsFactor]
  let R := N.localVonNeumann π hB₂ hB h₂
  let rel : Set (H →L[ℂ] H) := N.relativeCommutant hB π hB₁ hB₂ (h₁₂.trans h₂) h₂
  have hcenter_sub_rel : R ∩ Set.centralizer R ⊆ rel :=
    N.center_le_relativeCommutant hB π hB₁ hB₂ h₁₂ h₂ hcoh
  have hrel_eq_scalar : rel = scalarOperators H := hirr
  rw [hrel_eq_scalar] at hcenter_sub_rel
  apply Set.Subset.antisymm
  · exact hcenter_sub_rel
  · rintro T ⟨c, rfl⟩
    have hmem_R : (c • 1 : H →L[ℂ] H) ∈ R := by
      dsimp [R, localVonNeumann]
      apply Set.mem_centralizer_iff.mpr
      intro M hM
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    have hmem_centralizer : (c • 1 : H →L[ℂ] H) ∈ Set.centralizer R := by
      apply Set.mem_centralizer_iff.mpr
      intro M hM
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    exact ⟨hmem_R, hmem_centralizer⟩

end HaagKastlerNet
end HaagKastlerCurved
end AQFT
end Physicslib4
