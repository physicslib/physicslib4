/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.Antiunitary
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The Tomita operator

Stage 1 of the Tomita–Takesaki section of the blueprint: the reference conjugation `C`, the
von Neumann algebra setting with the project's commutant convention (`Set.centralizer`), cyclic
and separating vectors, the Tomita pre-operators `S₀`, `F₀`, the linearized pre-operator
`S₀′ = C ∘ S₀`, and the Tomita operator `S = C ∘ closure S₀′`.

## Representation

* **Setting.** A von Neumann algebra is a set `M : Set (H →L[ℂ] H)` satisfying
  `IsVonNeumannSet M`: self-adjoint and equal to `Set.centralizer (Set.centralizer M)`.
* **Antilinear partial maps.** Mathlib's `LinearPMap` is semilinear (`E →ₛₗ.[σ] F`), but its
  graph, `Submodule.toLinearPMap`, `closure`, `IsClosable` and `adjoint` exist only for linear
  partial maps; this is why closure and adjoint are taken of the linear `S₀′ = C ∘ S₀`. The
  pre-operator `S₀` is a domain `D : Submodule ℂ H` together with a function `D → H`, defined
  without `C` from a classically chosen representative.
  `S₀` is `tomitaPre M Ω` on `tomitaPreDomain M Ω`, and `F₀` is
  `tomitaPre (Set.centralizer M) Ω` on `tomitaPreDomain (Set.centralizer M) Ω`.
* **Conjugation.** Lemmas take an arbitrary antiunitary `C : H ≃ₗᵢ⋆[ℂ] H`, with the
  involution hypothesis `∀ x, C (C x) = x` where it is used. The reference conjugation
  `referenceConjugation b` of a Hilbert basis `b` is one such `C`; statements about an
  arbitrary `C` cover independence of the choice.
* **Linearization.** `S₀′ = linearizedTomitaPre M Ω C : H →ₗ.[ℂ] H` is defined from its graph
  `{(aΩ, C(a⋆Ω)) | a ∈ span M}`, which is a `ℂ`-submodule of `H × H`, via
  `Submodule.toLinearPMap`. The Tomita operator is `tomitaOperator M Ω C`, the function
  `x ↦ C (S₀′.closure x)` on the domain of the closure.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The reference conjugation -/

/-- The reference conjugation of a Hilbert basis `b`: the map conjugating coordinates,
`C (∑ cᵢ eᵢ) = ∑ conj cᵢ eᵢ`, realised as `b.repr⁻¹ ∘ star ∘ b.repr` with `star` the
coordinatewise conjugation on `ℓ²(ι, ℂ)`. It is antilinear and isometric by its type.
Blueprint: def:reference-conjugation -/
noncomputable def referenceConjugation {ι : Type*} (b : HilbertBasis ι ℂ H) :
    H ≃ₗᵢ⋆[ℂ] H :=
  (b.repr.trans (starₗᵢ ℂ)).trans b.repr.symm

/-- The reference conjugation is an involution and conjugates inner products; antilinearity,
isometry and bijectivity hold by its type `H ≃ₗᵢ⋆[ℂ] H`, so it is an antiunitary involution.
Blueprint: lmm:reference-conjugation-properties -/
theorem referenceConjugation_properties {ι : Type*} (b : HilbertBasis ι ℂ H) :
    (∀ x, referenceConjugation b (referenceConjugation b x) = x) ∧
      ∀ x y, ⟪referenceConjugation b x, referenceConjugation b y⟫_ℂ = conj ⟪x, y⟫_ℂ := by
  sorry

/-! ### Von Neumann algebras, cyclic and separating vectors -/

/-- A von Neumann algebra on `H`, as a set of bounded operators: `M` is self-adjoint and equals
its bicommutant `M''`, where the commutant is `Set.centralizer`.
Blueprint: def:von-neumann-algebra-commutant-convention -/
def IsVonNeumannSet (M : Set (H →L[ℂ] H)) : Prop :=
  (∀ a ∈ M, star a ∈ M) ∧ Set.centralizer (Set.centralizer M) = M

/-- The commutant `M'` of a von Neumann algebra `M` is a von Neumann algebra with `M'' = M`, and
both `M` and `M'` are the carriers of unital `*`-subalgebras of `B(H)`.
Blueprint: lmm:commutant-von-neumann-algebra -/
theorem isVonNeumannSet_centralizer {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) :
    IsVonNeumannSet (Set.centralizer M) ∧ Set.centralizer (Set.centralizer M) = M ∧
      (∃ A : StarSubalgebra ℂ (H →L[ℂ] H), (A : Set (H →L[ℂ] H)) = M) ∧
      ∃ A : StarSubalgebra ℂ (H →L[ℂ] H), (A : Set (H →L[ℂ] H)) = Set.centralizer M := by
  sorry

/-- A vector `Ω` is separating for a set `S` of bounded operators if `a ∈ S` and `a Ω = 0`
imply `a = 0`.
Blueprint: def:separating-vector -/
def IsSeparatingVector (S : Set (H →L[ℂ] H)) (Ω : H) : Prop :=
  ∀ a ∈ S, a Ω = 0 → a = 0

/-- A vector `Ω` is cyclic and separating for `M` if it is cyclic for `M` and for its
commutant `M'`: the vectors `a Ω`, `a ∈ M`, and `b Ω`, `b ∈ M'`, are dense. Cyclicity for a set
of operators is stated as density of the image, the form used by `localVonNeumann_separating`.
Blueprint: def:cyclic-separating-vector -/
def IsCyclicSeparatingVector (M : Set (H →L[ℂ] H)) (Ω : H) : Prop :=
  Dense ((fun a => a Ω) '' M) ∧ Dense ((fun b => b Ω) '' Set.centralizer M)

/-- A cyclic and separating vector for `M` is separating for `M` and for `M'`.
Blueprint: lmm:cyclic-commutant-separating -/
theorem isSeparatingVector_of_isCyclicSeparatingVector {M : Set (H →L[ℂ] H)} {Ω : H}
    (hΩ : IsCyclicSeparatingVector M Ω) :
    IsSeparatingVector M Ω ∧ IsSeparatingVector (Set.centralizer M) Ω := by
  sorry

/-! ### The Tomita pre-operators -/

/-- The vectors `a Ω` with `a` in a von Neumann algebra `M` and `b Ω` with `b ∈ M'` determine
`a⋆ Ω` and `b⋆ Ω`.
Blueprint: lmm:tomita-pre-operators-well-defined -/
theorem tomitaPre_wellDefined {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) :
    (∀ a ∈ M, ∀ b ∈ M, a Ω = b Ω → star a Ω = star b Ω) ∧
      ∀ a ∈ Set.centralizer M, ∀ b ∈ Set.centralizer M, a Ω = b Ω → star a Ω = star b Ω := by
  sorry

/-- The domain `MΩ` of the Tomita pre-operator, as a submodule: the image of `span ℂ M` under
evaluation at `Ω`. For a von Neumann algebra `M` the span is `M` itself, so this is `MΩ`.
Blueprint: def:tomita-pre-operators -/
noncomputable def tomitaPreDomain (M : Set (H →L[ℂ] H)) (Ω : H) : Submodule ℂ H :=
  (Submodule.span ℂ M).map (ContinuousLinearMap.apply ℂ H Ω).toLinearMap

/-- The Tomita pre-operator `S₀ = tomitaPre M Ω` on `tomitaPreDomain M Ω`, sending `a Ω` to
`a⋆ Ω` for `a ∈ span M`; `F₀` is `tomitaPre (Set.centralizer M) Ω`. The representative `a` is
chosen classically; for a cyclic and separating vector the value does not depend on the choice
(`tomitaPre_wellDefined`) and the map is antilinear.
Blueprint: def:tomita-pre-operators -/
noncomputable def tomitaPre (M : Set (H →L[ℂ] H)) (Ω : H) : tomitaPreDomain M Ω → H :=
  fun x => (star (Classical.choose (Submodule.mem_map.mp x.2) : H →L[ℂ] H)) Ω

/-- `Dom S₀ = MΩ` and `Dom F₀ = M'Ω` are dense, and `S₀`, `F₀` map their domains into themselves
with `S₀ S₀ x = x` and `F₀ F₀ y = y`, so each maps its domain onto itself.
Blueprint: lmm:tomita-pre-operators-dense-involutive -/
theorem tomitaPre_dense_involutive {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) :
    Dense (tomitaPreDomain M Ω : Set H) ∧ Dense (tomitaPreDomain (Set.centralizer M) Ω : Set H) ∧
      (∀ x : tomitaPreDomain M Ω, ∃ h : tomitaPre M Ω x ∈ tomitaPreDomain M Ω,
        tomitaPre M Ω ⟨_, h⟩ = x) ∧
      ∀ y : tomitaPreDomain (Set.centralizer M) Ω,
        ∃ h : tomitaPre (Set.centralizer M) Ω y ∈ tomitaPreDomain (Set.centralizer M) Ω,
          tomitaPre (Set.centralizer M) Ω ⟨_, h⟩ = y := by
  sorry

/-- The adjoint relation `⟪y, S₀ x⟫ = ⟪x, F₀ y⟫` for `x ∈ Dom S₀`, `y ∈ Dom F₀`.
Blueprint: lmm:tomita-adjoint-relation -/
theorem tomitaPre_adjoint_relation {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) (x : tomitaPreDomain M Ω)
    (y : tomitaPreDomain (Set.centralizer M) Ω) :
    ⟪(y : H), tomitaPre M Ω x⟫_ℂ = ⟪(x : H), tomitaPre (Set.centralizer M) Ω y⟫_ℂ := by
  sorry

/-! ### The linearized pre-operator -/

/-- The linearized Tomita pre-operator `S₀′ = C ∘ S₀ : H →ₗ.[ℂ] H`, defined by its graph
`{(a Ω, C (a⋆ Ω)) | a ∈ span M}`. The map `a ↦ (a Ω, C (a⋆ Ω))` is `ℂ`-linear (a composite of
two antilinear maps in the second coordinate), so the graph is a submodule of `H × H`, turned
into a partial linear map by `Submodule.toLinearPMap`. Its domain is `tomitaPreDomain M Ω`.
Blueprint: def:linearized-tomita-pre-operator -/
noncomputable def linearizedTomitaPre (M : Set (H →L[ℂ] H)) (Ω : H) (C : H ≃ₗᵢ⋆[ℂ] H) :
    H →ₗ.[ℂ] H :=
  ((Submodule.span ℂ M).map
    ((ContinuousLinearMap.apply ℂ H Ω).toLinearMap.prod
      (C.toLinearEquiv.toLinearMap.comp
        ((ContinuousLinearMap.apply ℂ H Ω).toLinearMap.comp
          (starLinearEquiv ℂ (A := H →L[ℂ] H)).toLinearMap)))).toLinearPMap

/-- For a von Neumann algebra `M` the linear span of `M` is `M` itself, since `M = M''` is a
centralizer and hence a `ℂ`-submodule.
Blueprint: lmm:tomita-pre-operators-apply -/
theorem span_eq_of_isVonNeumannSet {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) :
    (Submodule.span ℂ M : Set (H →L[ℂ] H)) = M := by
  sorry

/-- The pre-operators act as intended on representatives: `S₀ (a Ω) = a⋆ Ω` for `a ∈ M` and
`F₀ (b Ω) = b⋆ Ω` for `b ∈ M′`.
Blueprint: lmm:tomita-pre-operators-apply -/
theorem tomitaPre_apply {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) :
    (∀ a (ha : a ∈ M), tomitaPre M Ω
        ⟨a Ω, Submodule.mem_map_of_mem (Submodule.subset_span ha)⟩ = star a Ω) ∧
      ∀ b (hb : b ∈ Set.centralizer M), tomitaPre (Set.centralizer M) Ω
        ⟨b Ω, Submodule.mem_map_of_mem (Submodule.subset_span hb)⟩ = star b Ω := by
  sorry

/-- The domain of the linearized pre-operator is the domain of `S₀`: `Dom S₀′ = Dom S₀`.
Blueprint: lmm:tomita-pre-operators-apply -/
theorem linearizedTomitaPre_domain (M : Set (H →L[ℂ] H)) (Ω : H) (C : H ≃ₗᵢ⋆[ℂ] H) :
    (linearizedTomitaPre M Ω C).domain = tomitaPreDomain M Ω := by
  sorry

/-- The linearized pre-operator is `C ∘ S₀`: `S₀′ x = C (S₀ x)` for `x ∈ Dom S₀`.
Blueprint: lmm:tomita-pre-operators-apply -/
theorem linearizedTomitaPre_apply {M : Set (H →L[ℂ] H)} {Ω : H} (hM : IsVonNeumannSet M)
    (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H) (x : tomitaPreDomain M Ω) :
    linearizedTomitaPre M Ω C ⟨x, by rw [linearizedTomitaPre_domain]; exact x.2⟩ =
      C (tomitaPre M Ω x) := by
  sorry

/-- `C (M′Ω)` lies in the domain of `(S₀′)⋆`, with `(S₀′)⋆ (C y) = F₀ y` for `y ∈ M′Ω`, and
`(S₀′)⋆` is densely defined.
Blueprint: lmm:linearized-adjoint-extends -/
theorem linearizedTomitaPre_adjoint_extends {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H) :
    (∀ y : tomitaPreDomain (Set.centralizer M) Ω,
      ∃ h : C y ∈ (linearizedTomitaPre M Ω C).adjoint.domain,
        (linearizedTomitaPre M Ω C).adjoint ⟨C y, h⟩ = tomitaPre (Set.centralizer M) Ω y) ∧
      Dense ((linearizedTomitaPre M Ω C).adjoint.domain : Set H) := by
  sorry

/-- The linearized pre-operator `S₀′` is closable.
Blueprint: crllr:linearized-tomita-closable -/
theorem linearizedTomitaPre_isClosable {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H) :
    (linearizedTomitaPre M Ω C).IsClosable := by
  sorry

/-! ### The Tomita operator -/

/-- The Tomita operator `S = C ∘ S′` on `Dom S = Dom S′`, where `S′` is the closure of the
linearized pre-operator `S₀′`. As an antilinear partial map it is a function on the domain
of `S′`.
Blueprint: def:tomita-operator -/
noncomputable def tomitaOperator (M : Set (H →L[ℂ] H)) (Ω : H) (C : H ≃ₗᵢ⋆[ℂ] H) :
    (linearizedTomitaPre M Ω C).closure.domain → H :=
  fun x => C ((linearizedTomitaPre M Ω C).closure x)

/-- The graph of `S` is the closure in `H × H` of the graph of `S₀`. Since the right side does
not involve `C`, the Tomita operator and its domain are independent of the antiunitary
involution `C`.
Blueprint: lmm:tomita-operator-independent-of-c -/
theorem tomitaOperator_graph_eq_closure {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    Set.range (fun x : (linearizedTomitaPre M Ω C).closure.domain =>
      ((x : H), tomitaOperator M Ω C x)) =
      closure (Set.range (fun x : tomitaPreDomain M Ω => ((x : H), tomitaPre M Ω x))) := by
  sorry

/-- The graph of the Tomita operator is invariant under swapping coordinates:
`(φ, ψ) ∈ Γ(S)` implies `(ψ, φ) ∈ Γ(S)`.
Blueprint: lmm:tomita-graph-flip -/
theorem tomitaOperator_graph_swap {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    ∀ p ∈ Set.range (fun x : (linearizedTomitaPre M Ω C).closure.domain =>
      ((x : H), tomitaOperator M Ω C x)),
      p.swap ∈ Set.range (fun x : (linearizedTomitaPre M Ω C).closure.domain =>
      ((x : H), tomitaOperator M Ω C x)) := by
  sorry

/-- The Tomita operator is an involution: `S` is injective, maps `Dom S` into itself with
`S S φ = φ` (hence onto `Dom S`), and its domain and range are dense.
Blueprint: thrm:tomita-operator-involution -/
theorem tomitaOperator_involution {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    Function.Injective (tomitaOperator M Ω C) ∧
      (∀ x, ∃ h : tomitaOperator M Ω C x ∈ (linearizedTomitaPre M Ω C).closure.domain,
        tomitaOperator M Ω C ⟨_, h⟩ = x) ∧
      Dense ((linearizedTomitaPre M Ω C).closure.domain : Set H) ∧
      Dense (Set.range (tomitaOperator M Ω C)) := by
  sorry

/-- The closure `S′` of the linearized pre-operator is closed, densely defined and injective,
with dense range.
Blueprint: crllr:linearized-tomita-properties -/
theorem linearizedTomita_closure_properties {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (linearizedTomitaPre M Ω C).closure.IsClosed ∧
      Dense ((linearizedTomitaPre M Ω C).closure.domain : Set H) ∧
      Function.Injective (linearizedTomitaPre M Ω C).closure ∧
      Dense (Set.range (linearizedTomitaPre M Ω C).closure) := by
  sorry

end Physicslib4.Modular
