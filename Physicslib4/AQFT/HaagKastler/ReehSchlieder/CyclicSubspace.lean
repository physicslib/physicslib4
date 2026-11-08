/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.ReehSchlieder.Translations

/-!
# Translations on the cyclic subspace

Let `π` be a `*`-representation of the quasilocal algebra on `H`, `Ω ∈ H`, and `x ↦ U(x)`
unitaries indexed by the translations `ℝ⁴` with `U(x)π(a)Ω = π(β_x a)Ω`, where
`β_x = N.action (translationSub x)`. The cyclic subspace `K₀` is the closure of
`π(𝔘)Ω`, written `(Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure`; the span
is the range itself since `π` is linear, but the closed-submodule form is the one used throughout.
Cyclicity of `Ω` is not assumed.

* `apply_eq_of_mem_cyclicSubspace` — bounded operators agreeing on every `π(a)Ω` agree on `K₀`.
* `translations_cyclicSubspace_invariant` — `U(x)Ω = Ω`, and `K₀` is invariant under every
  `π(a)` and every `U(x)`.
* `translations_intertwine_cyclicSubspace` — `U(x)π(a) = π(β_x a)U(x)` on `K₀`.
* `translations_add_cyclicSubspace` — `U(x + y) = U(x)U(y)` on `K₀`.
* `covariant_translations_cyclicSubspace` — the conjunction of the three preceding lemmas.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Spacetime

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Let `π` be a `*`-representation of the quasilocal algebra on `H` and `Ω ∈ H`. Bounded
operators `S, T` on `H` with `S π(a) Ω = T π(a) Ω` for every `a` agree on the cyclic subspace
`K₀`, the closure of `π(𝔘)Ω`.

Blueprint: lmm:agree-on-cyclic-subspace -/
theorem apply_eq_of_mem_cyclicSubspace {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) {S T : H →L[ℂ] H}
    (h : ∀ a, S (π a Ω) = T (π a Ω)) :
    ∀ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure, S φ = T φ :=
  fun _ hφ => ContinuousLinearMap.eqOn_closure_span (by rintro _ ⟨a, rfl⟩; exact h a) hφ

/-- Let `π` be a `*`-representation of the quasilocal algebra on `H`, `Ω ∈ H`, and `x ↦ U(x)`
unitaries indexed by the translations with `U(x) π(a) Ω = π(β_x a) Ω`. Then `U(x)Ω = Ω`, and the
cyclic subspace `K₀`, the closure of `π(𝔘)Ω`, is invariant under every `π(a)` and every `U(x)`.

Blueprint: lmm:translations-cyclic-subspace-invariant -/
theorem translations_cyclicSubspace_invariant {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x a, U x (π a Ω) = π (N.action (translationSub x) a) Ω) :
    (∀ x, U x Ω = Ω) ∧
      (∀ a, ∀ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure,
        π a φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure) ∧
      (∀ x, ∀ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure,
        U x φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure) := by
  set K := (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure
  have gen : ∀ b, π b Ω ∈ K := fun b =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨b, rfl⟩)
  have key : ∀ T : H →L[ℂ] H, (∀ b, T (π b Ω) ∈ K) → ∀ φ ∈ K, T φ ∈ K := fun T hT φ hφ =>
    Submodule.topologicalClosure_minimal _ (t := K.comap (T : H →ₗ[ℂ] H))
      (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hT b))
      ((Submodule.isClosed_topologicalClosure _).preimage T.continuous) hφ
  refine ⟨fun x => by simpa using hU x 1, fun a => key (π a) fun b => ?_,
    fun x => key (U x).toLinearIsometry.toContinuousLinearMap fun b => ?_⟩
  · simpa using gen (a * b)
  · exact (hU x b).symm ▸ gen _

/-- Under the hypotheses of `translations_cyclicSubspace_invariant`,
`U(x) π(a) = π(β_x a) U(x)` on the cyclic subspace `K₀` for every translation `x` and every `a`.

Blueprint: lmm:translations-intertwine-cyclic-subspace -/
theorem translations_intertwine_cyclicSubspace {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x a, U x (π a Ω) = π (N.action (translationSub x) a) Ω) :
    ∀ x a, ∀ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure,
      U x (π a φ) = π (N.action (translationSub x) a) (U x φ) := by
  intro x a φ hφ
  exact apply_eq_of_mem_cyclicSubspace π Ω
    (S := ((U x).toContinuousLinearEquiv : H →L[ℂ] H).comp (π a))
    (T := (π (N.action (translationSub x) a)).comp ((U x).toContinuousLinearEquiv : H →L[ℂ] H))
    (fun b => by
      change U x (π a (π b Ω)) = π (N.action (translationSub x) a) (U x (π b Ω))
      rw [← mul_apply_eq_comp, ← map_mul, hU, hU, map_mul, map_mul,
        mul_apply_eq_comp]) φ hφ

/-- Under the hypotheses of `translations_cyclicSubspace_invariant`, `U(x + y) = U(x) U(y)` on
the cyclic subspace `K₀`: for every `φ ∈ K₀`, `U(x + y)φ = U(x)U(y)φ` for all translations
`x, y`. This is the hypothesis `hmul` of `inner_translation_eq_zero`.

Blueprint: lmm:translations-group-law-cyclic-subspace -/
theorem translations_add_cyclicSubspace {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x a, U x (π a Ω) = π (N.action (translationSub x) a) Ω) :
    ∀ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure,
      ∀ x y, U (x + y) φ = U x (U y φ) := fun φ hφ x y =>
  apply_eq_of_mem_cyclicSubspace π Ω (S := ((U (x + y) : H ≃L[ℂ] H) : H →L[ℂ] H))
    (T := ((U x : H ≃L[ℂ] H) : H →L[ℂ] H) ∘L ((U y : H ≃L[ℂ] H) : H →L[ℂ] H))
    (fun a => show U (x + y) (π a Ω) = U x (U y (π a Ω)) by
      rw [hU, hU, hU, translationSub_mul, HaagKastlerNet.action_mul_apply]) φ hφ

/-- **Translations on the cyclic subspace.** Let `π` be a `*`-representation of the quasilocal
algebra on `H`, `Ω ∈ H`, and `x ↦ U(x)` unitaries indexed by the translations with
`U(x) π(a) Ω = π(β_x a) Ω`, and let `K₀` be the closure of `π(𝔘)Ω`. Then `U(x)Ω = Ω`; `K₀` is
invariant under every `π(a)` and `U(x)`; and on `K₀`, `U(x)π(a) = π(β_x a)U(x)` and
`U(x + y) = U(x)U(y)`.

Blueprint: lmm:covariant-translations-cyclic-subspace -/
theorem covariant_translations_cyclicSubspace {N : HaagKastlerNet}
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (U : StandardMinkowskiSpacetime.Carrier → (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x a, U x (π a Ω) = π (N.action (translationSub x) a) Ω) :
    (∀ x, U x Ω = Ω) ∧
      (∀ a, ∀ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure,
        π a φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure) ∧
      (∀ x, ∀ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure,
        U x φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure) ∧
      (∀ x a, ∀ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure,
        U x (π a φ) = π (N.action (translationSub x) a) (U x φ)) ∧
      (∀ φ ∈ (Submodule.span ℂ (Set.range fun a => π a Ω)).topologicalClosure,
        ∀ x y, U (x + y) φ = U x (U y φ)) :=
  let ⟨h1, h2, h3⟩ := translations_cyclicSubspace_invariant π Ω U hU
  ⟨h1, h2, h3, translations_intertwine_cyclicSubspace π Ω U hU,
    translations_add_cyclicSubspace π Ω U hU⟩

end HaagKastler
end AQFT
end Physicslib4
