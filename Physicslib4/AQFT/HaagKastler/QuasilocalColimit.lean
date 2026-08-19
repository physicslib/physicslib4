/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.Isotony
import Physicslib4.Spacetime.MinkowskiDirected
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Physicslib4.Analysis.CStarCompletion

/-!
# The quasilocal colimit: index type and directed system

This file begins the construction of the quasilocal algebra *from the net alone*,
as the directed colimit of the local algebras along the Axiom 2 isotony family,
later completed. It supplies the two foundational ingredients that everything
downstream needs:

* the index type of Alexandrov diamonds, ordered by inclusion, together with the
  fact that it is directed (blueprint `lmm:alexandrov-diamonds-isDirected`);
* the isotony family as a `DirectedSystem` in Mathlib's sense
  (blueprint `lmm:isotony-directed-system`).

## Modelling notes

Mathlib's `DirectLimit` API is indexed by a `Preorder` and takes the transition
maps in the shape `f : ∀ i j (h : i ≤ j), T h`, where `T h` is a `FunLike` type.
`Isotony.map` is indexed instead by *subsets together with a proof* of
`IsAlexandrovBasisSet`, so the index is packaged here as the subtype `Diamond`,
whose order is the inclusion order inherited from `Set`. `IsAlexandrovBasisSet B`
is by definition `B ∈ Spacetime.alexandrovBasis ..`, so the geometry proved in
`Physicslib4/Spacetime/MinkowskiDirected.lean` applies to it unchanged.

The transition maps are kept as `StarAlgHom`s rather than bare functions, since
`StarAlgHom` is `FunLike` and satisfies the `RingHomClass`/`StarHomClass`/
`AlgHomClass`/`LinearMapClass` hypotheses under which `DirectLimit` carries its
`Ring`, `StarRing`, `Algebra` and `StarModule` structures.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

universe u

/-- The **Alexandrov diamonds** of standard Minkowski spacetime, as a type,
ordered by inclusion. This is the index type of the directed system of local
algebras.

Blueprint reference: `lmm:alexandrov-diamonds-isDirected`. -/
abbrev Diamond : Type :=
  {B : Set StandardMinkowskiSpacetime.Carrier // IsAlexandrovBasisSet B}

/-- **The Alexandrov diamonds are directed under inclusion** (set-level form):
any two basis diamonds are contained in a common one. This is the order-theoretic
repackaging of `Physicslib4.Spacetime.alexandrovBasis_directed`.

Blueprint reference: `lmm:alexandrov-diamonds-isDirected`. -/
theorem directedOn_alexandrovBasis :
    DirectedOn (· ⊆ ·)
      (Spacetime.alexandrovBasis StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation) := by
  intro B₁ h₁ B₂ h₂
  exact Spacetime.alexandrovBasis_directed h₁ h₂

/-- **The Alexandrov diamonds are directed under inclusion** (subtype form).
This is the instance the colimit construction consumes, so that downstream nodes
can cite an instance rather than restate a `∀∃` statement.

Blueprint reference: `lmm:alexandrov-diamonds-isDirected`. -/
instance instIsDirectedOrderDiamond : IsDirectedOrder Diamond := by
  constructor
  intro D₁ D₂
  obtain ⟨B, hB, h₁, h₂⟩ :=
    Spacetime.alexandrovBasis_directed D₁.2 D₂.2
  refine ⟨⟨B, hB⟩, h₁, h₂⟩

/-- The transition maps of the directed system of local algebras, in the shape
Mathlib's `DirectLimit` expects: explicit index binders, with the map itself a
`StarAlgHom` (hence `FunLike`). -/
def transitionHom (U : LocalNet) (i : Isotony U) (D₁ D₂ : Diamond) (h : D₁ ≤ D₂) :
    StarAlgHom ℂ (U.algebra D₁.1) (U.algebra D₂.1) :=
  i.map D₁.2 D₂.2 h

/-- **The isotony family is a directed system.** Mathlib's `DirectedSystem` is a
two-field class whose fields are exactly Axiom 2's identity and composition laws,
so the instance is built by supplying `Isotony.map_self` and `Isotony.map_comp`.

Blueprint reference: `lmm:isotony-directed-system`. -/
instance instDirectedSystemIsotony (U : LocalNet) (i : Isotony U) :
    DirectedSystem (fun D : Diamond => U.algebra D.1)
      (transitionHom U i · · ·) where
  map_self := by
    intro D x
    change i.map D.2 D.2 (subset_refl D.1) x = x
    rw [i.map_self D.2]
    rfl
  map_map := by
    intro Dₖ Dⱼ Dᵢ hij hjk x
    change ((i.map Dⱼ.2 Dₖ.2 hjk).comp (i.map Dᵢ.2 Dⱼ.2 hij)) x =
      i.map Dᵢ.2 Dₖ.2 (hij.trans hjk) x
    rw [i.map_comp Dᵢ.2 Dⱼ.2 Dₖ.2 hij hjk]

/-- The **colimit of the local algebras** along the Axiom 2 isotony family: the
directed colimit `lim_{→ 𝐁} 𝔘(𝐁)`, taken over the Alexandrov diamonds ordered by
inclusion.

Mathlib supplies its algebraic structure (`Ring`, `StarRing`, `Algebra ℂ`,
`StarModule ℂ`) but puts no norm on any colimit; that is built by hand below. -/
abbrev QuasilocalColimit (U : LocalNet.{u}) (i : Isotony U) : Type u :=
  DirectLimit (fun D : Diamond => U.algebra D.1) (transitionHom U i)

/-- **The isotony embeddings are isometric.** A `*`-homomorphism of complex
C*-algebras is isometric as soon as it is injective, and Axiom 2(a) supplies
injectivity. This is what makes the colimit norm well defined.

Blueprint reference: `lmm:quasilocal-colimit-norm-well-defined`. -/
theorem norm_transitionHom (U : LocalNet) (i : Isotony U)
    (D₁ D₂ : Diamond) (h : D₁ ≤ D₂) (a : U.algebra D₁.1) :
    ‖transitionHom U i D₁ D₂ h a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (transitionHom U i D₁ D₂ h) (i.injective D₁.2 D₂.2 h) a

/-- **The colimit norm.** `‖[a]‖ := ‖a‖` for any representative `a`. It is well
defined precisely because the transition maps are isometric
(`norm_transitionHom`): the universal property of the colimit takes that isometry
as its compatibility obligation.

Blueprint reference: `lmm:quasilocal-colimit-norm-well-defined`. -/
noncomputable def colimitNorm (U : LocalNet) (i : Isotony U) :
    QuasilocalColimit U i → ℝ :=
  DirectLimit.lift _ (fun _ a => ‖a‖)
    (fun D₁ D₂ h a => (norm_transitionHom U i D₁ D₂ h a).symm)

/-- The colimit norm of a class is the norm of any representative: the defining
equation of `colimitNorm`, and the reason the node is stated as a
well-definedness claim. -/
@[simp] theorem colimitNorm_mk (U : LocalNet) (i : Isotony U)
    (D : Diamond) (a : U.algebra D.1) :
    colimitNorm U i ⟦⟨D, a⟩⟧ = ‖a‖ := rfl

/-- **Common representatives for two colimit elements.** Any two elements of the
colimit are the classes of two elements of one and the same diamond. This is what
lets the binary algebraic and norm identities be checked on representatives, and
it is available exactly because the index type is directed.

Blueprint reference: `lmm:quasilocal-colimit-common-representatives`. -/
theorem exists_common_representatives (U : LocalNet) (i : Isotony U)
    (x y : QuasilocalColimit U i) :
    ∃ (D : Diamond) (a b : U.algebra D.1), x = ⟦⟨D, a⟩⟧ ∧ y = ⟦⟨D, b⟩⟧ := by
  exact DirectLimit.exists_eq_mk₂ _ x y

/-- **There is at least one Alexandrov diamond.** Every set of the form
`I⁺(p) ∩ I⁻(q)` is a basis element, so the index type is inhabited.

This is needed as an instance, not merely as a fact: the colimit's `Zero` and
`One` are built by choosing a component (`DirectLimit.map₀` picks
`Classical.arbitrary ι`), so Mathlib's algebraic instances on the colimit all
carry `[Nonempty ι]`. Without it none of `Ring`, `Module ℂ` or `Algebra ℂ`
resolves on the colimit. -/
instance instNonemptyDiamond : Nonempty Diamond := by
  exact ⟨⟨Spacetime.chronologicalFuture StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation 0 ∩
      Spacetime.chronologicalPast StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation 0,
    ⟨0, 0, rfl⟩⟩⟩

/-- **The colimit norm is a ring norm.** Its five `RingNorm` fields are the first
five clauses of the blueprint node: `map_zero'` and `neg'` come from
`AddGroupSeminorm`, `add_le'` and `mul_le'` are subadditivity and
submultiplicativity, and `eq_zero_of_map_eq_zero'` is positive definiteness.

Each is checked on common representatives (`exists_common_representatives`) and
transported by `colimitNorm_mk`. Positive definiteness is the only clause with
real content: it is where injectivity of the canonical maps into the colimit is
spent, via `DirectLimit.mk_injective` fed by Axiom 2(a).

Blueprint reference: `lmm:quasilocal-colimit-norm-axioms`. -/
noncomputable def colimitRingNorm (U : LocalNet) (i : Isotony U) :
    RingNorm (QuasilocalColimit U i) where
  toFun := colimitNorm U i
  map_zero' := by
    rw [DirectLimit.zero_def (Classical.arbitrary Diamond), colimitNorm_mk]
    exact norm_zero
  add_le' := by
    intro x y
    rcases exists_common_representatives U i x y with ⟨D, a, b, rfl, rfl⟩
    rw [DirectLimit.add_def, colimitNorm_mk, colimitNorm_mk, colimitNorm_mk]
    exact norm_add_le a b
  neg' := by
    intro x
    rcases exists_common_representatives U i x x with ⟨D, a, b, rfl, _⟩
    rw [DirectLimit.neg_def, colimitNorm_mk, colimitNorm_mk]
    exact norm_neg a
  mul_le' := by
    intro x y
    rcases exists_common_representatives U i x y with ⟨D, a, b, rfl, rfl⟩
    rw [DirectLimit.mul_def, colimitNorm_mk, colimitNorm_mk, colimitNorm_mk]
    exact norm_mul_le a b
  eq_zero_of_map_eq_zero' := by
    intro x hx
    rcases exists_common_representatives U i x x with ⟨D, a, b, rfl, _⟩
    have ha : ‖a‖ = 0 := by
      simpa [colimitNorm_mk] using hx
    have hzero : a = 0 := (norm_eq_zero.mp ha)
    rw [hzero]
    exact (DirectLimit.zero_def D).symm

/-- The colimit as a `NormedRing`, obtained from `colimitRingNorm`.

The `RingNorm` detour is forced rather than bureaucratic: `NormedRing` bundles a
`MetricSpace`, and there is no metric on the colimit quotient until this norm
supplies one, so `NormedRing` cannot be stated first and filled in field by field.

Blueprint reference: `lmm:quasilocal-colimit-norm-axioms`. -/
noncomputable instance colimitNormedRing (U : LocalNet) (i : Isotony U) :
    NormedRing (QuasilocalColimit U i) :=
  (colimitRingNorm U i).toNormedRing

/-- **Absolute homogeneity of the colimit norm**, the sixth clause. It is listed
separately from the `RingNorm` fields because a `RingNorm` knows nothing about the
scalars; its role is to supply the `norm_smul_le` field of `NormedSpace ℂ` over
the `NormedRing` structure just obtained.

Blueprint reference: `lmm:quasilocal-colimit-norm-axioms`. -/
theorem colimitNorm_smul (U : LocalNet) (i : Isotony U)
    (c : ℂ) (x : QuasilocalColimit U i) :
    colimitNorm U i (c • x) = ‖c‖ * colimitNorm U i x := by
  exact DirectLimit.induction (f := transitionHom U i)
    (C := fun y => colimitNorm U i (c • y) = ‖c‖ * colimitNorm U i y)
    (by
      intro D a
      rw [DirectLimit.smul_def, colimitNorm_mk, colimitNorm_mk]
      exact norm_smul c a)
    x

/-! ### Next step, and the obstacle in front of it

The next blueprint node, `lmm:quasilocal-colimit-norm-axioms`, builds a `RingNorm`
on the colimit from `colimitNorm` and then a `NormedRing` via
`RingNorm.toNormedRing`, followed by `NormedSpace ℂ` from absolute homogeneity.

It is blocked, and not on the mathematics. Mathlib's `Algebra/Colimit/DirectLimit.lean`
does carry `Ring`, `StarRing`, `Module`, `Algebra` and `StarModule` instances on a
direct limit, but they are stated under a variable block of the shape

    {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}  {f : ∀ _ _ h, T h}
    [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
    [∀ i j h, RingHomClass (T h) (G i) (G j)]   -- and LinearMapClass, AlgHomClass, …

and they do not fire for the family here: attempting the `RingNorm` produces
`failed to synthesize NonUnitalNonAssocRing (QuasilocalColimit U i)`, and the
scalar action produces `failed to synthesize HSMul ℂ (QuasilocalColimit U i) ?m`.
Writing the family as `(transitionHom U i · · ·)` rather than an eta-expanded
lambda was necessary but not sufficient.

So the obstacle is getting Lean to see the isotony family as a `T`-family with the
requisite `…HomClass` instances, which is exactly the dependent-type plumbing
flagged as the main friction of this construction. Everything above this point is
proved and this file builds clean; the work resumes here.

Note when resuming: every instance in `Algebra/Colimit/DirectLimit.lean` is
anonymous, so none may be cited by name — use `inferInstance` / `inferInstanceAs`.
-/

/-- The `NormedRing` norm on the colimit is the norm of `colimitNorm`, by
construction. This is the bridge that lets the representative-level lemmas above
be used against the ambient `‖·‖`. -/
@[simp] theorem norm_eq_colimitNorm (U : LocalNet) (i : Isotony U)
    (x : QuasilocalColimit U i) :
    ‖x‖ = colimitNorm U i x := rfl

/-- **The colimit is a normed algebra over `ℂ`.** Together with the `StarRing` and
`StarModule ℂ` instances, which Mathlib's `DirectLimit` supplies by typeclass
inference from the corresponding structures on each local algebra, this is the
normed `*`-algebra structure the blueprint node asserts.

`NormedAlgebra` has no field beyond `Algebra` other than `norm_smul_le`, which is
absolute homogeneity (`colimitNorm_smul`) weakened to an inequality. It is stated
in the `NormedAlgebra` form because that is what the completion hypotheses consume
downstream.

Blueprint reference: `lmm:quasilocal-union-normed-star-algebra`. -/
noncomputable instance colimitNormedAlgebra (U : LocalNet) (i : Isotony U) :
    NormedAlgebra ℂ (QuasilocalColimit U i) where
  norm_smul_le := by
    intro r x
    rw [norm_eq_colimitNorm, colimitNorm_smul, ← norm_eq_colimitNorm]

/-- **The colimit satisfies the C\*-inequality** `‖x‖ * ‖x‖ ≤ ‖x⋆ * x‖`.

Only the inequality is asserted, because it is literally the single field
`norm_mul_self_le` of Mathlib's `CStarRing`, so establishing it *is* establishing
the instance. The familiar equality `‖x⋆ * x‖ = ‖x‖ ^ 2` then comes back free from
`CStarRing.norm_star_mul_self`, and `‖x⋆‖ = ‖x‖` from
`CStarRing.to_normedStarGroup`; neither needs a proof of its own.

Note `CStarRing` does not require completeness, which is why this holds on the
colimit even though the colimit is in general *not* a C\*-algebra. Only one
element is involved, so no directedness is needed: take a representative `a`, note
`x⋆ * x` has representative `a⋆ * a` in the same local algebra, and apply the
`CStarRing` instance there.

Blueprint reference: `lmm:quasilocal-colimit-cstar-identity`. -/
instance colimitCStarRing (U : LocalNet) (i : Isotony U) :
    CStarRing (QuasilocalColimit U i) where
  norm_mul_self_le := by
    intro x
    exact DirectLimit.induction (f := transitionHom U i)
      (C := fun y => ‖y‖ * ‖y‖ ≤ ‖star y * y‖)
      (by
        intro D a
        rw [DirectLimit.star_def, DirectLimit.mul_def]
        simpa [colimitNorm_mk] using CStarRing.norm_mul_self_le a)
      x

/-- The **quasilocal algebra built from the net**: the completion of the colimit of
the local algebras along the Axiom 2 isotony family.

This is the object the blueprint claims exists, constructed from the net alone,
with no ambient C*-algebra presupposed anywhere. -/
abbrev QuasilocalCompletion (U : LocalNet.{u}) (i : Isotony U) : Type u :=
  UniformSpace.Completion (QuasilocalColimit U i)

/-- **The completion of the quasilocal colimit is a C\*-algebra**
(`lmm:quasilocal-completion-cstar`).

This is the general completion theory of `Physicslib4/Analysis/CStarCompletion.lean`
instantiated at the colimit. Its five standing hypotheses — `NormedRing`,
`StarRing`, `NormedAlgebra ℂ`, `StarModule ℂ` and `CStarRing` — are exactly what
the colimit development above establishes, so the C\*-algebra structure follows by
instance resolution with nothing further to prove.

In particular isometry of the involution is not a separate obligation: it comes
from the C\*-inequality through `CStarRing.to_normedStarGroup`. -/
noncomputable instance quasilocalCompletionCStarAlgebra (U : LocalNet) (i : Isotony U) :
    CStarAlgebra (QuasilocalCompletion U i) :=
  inferInstance

end HaagKastler
end AQFT
end Physicslib4
