# Design memo: stating Takesaki's KMS theorem (2026-11-15)

Scope: a new subsection of blueprint §10.10, after Tomita's theorem. Its main theorem says that the
vector state of a cyclic and separating vector is a KMS state for the modular flow, stated with
`Physicslib4.AQFT.IsKMSState` (`Physicslib4/AQFT/KMS.lean`). This memo proposes how to package the
inputs. Every new `def` or `instance` below needs the user's approval through the lean-kit guard.

## 1. What `IsKMSState` expects

```
variable {A : Type*} [CStarAlgebra A]
def IsKMSState (α : ℝ → (A ≃⋆ₐ[ℂ] A)) (β : ℝ) (ω : State A) : Prop :=
  ∀ a b : A, ∃ F : ℂ → ℂ, ContinuousOn F (kmsStrip β) ∧ DifferentiableOn ℂ F (kmsStripInterior β) ∧
    (∃ C, ∀ z ∈ kmsStrip β, ‖F z‖ ≤ C) ∧
    (∀ t : ℝ, F t = ω (a * α t b)) ∧ (∀ t : ℝ, F (t + β * I) = ω (α t b * a))
```

`State A` (`Physicslib4/GNS/Basic.lean`) is a continuous linear functional with
`0 ≤ ω (star a * a)` and `‖ω‖ = 1`. `IsOneParameterAut α` covers only the group law. Continuity in
`t` is not part of the KMS definition.

The modular side has three mismatches:
- M is a `Set (H →L[ℂ] H)` with `IsVonNeumannSet M`, not a type carrying a `CStarAlgebra` instance.
- Tomita's theorem gives `(fun x => U t ∘L x ∘L U (-t)) '' M = M`, not a `≃⋆ₐ`.
- The library has no vector state.

## 2. Sign convention: reversed flow, β = 1

Write σₜ(x) = Δ^{it}xΔ^{-it} and ω(x) = ⟨Ω, xΩ⟩. The function t ↦ ω(aσₜ(b)) continues to the strip
−1 ≤ Im z ≤ 0, and F(t − i) = ω(σₜ(b)a). In Bratteli–Robinson's convention this is "KMS at β = −1".
The library's `kmsStrip β` is {0 ≤ Im z ≤ β}, which is empty for β = −1, so the statement must use
the reversed flow:

  IsKMSState (fun t => σ₋ₜ) 1 ω,   with G(z) = F(−z).

Check: G(t) = ω(a σ₋ₜ b), and G(t + i) = F(−t − i) = ω(σ₋ₜ(b) a).
The blueprint states the theorem in this form and remarks on the β = −1 convention. The manual
appendix already phrases it as "for the reversed flow at inverse temperature 1".

## 3. Packaging M as a C*-algebra

Mathlib provides `StarSubalgebra.cstarAlgebra : [IsClosed (s : Set A)] → CStarAlgebra s`
(`Mathlib/Analysis/CStarAlgebra/Classes.lean`). Two facts already make M a closed star-subalgebra:
- `isVonNeumannSet_centralizer` shows M is the carrier of
  `StarSubalgebra.centralizer ℂ (Set.centralizer M)`.
- `Set.isClosed_centralizer` shows that carrier is norm-closed.

Options:

- **P1 (recommended): one bundling def plus one instance.**
  - `modularAlgebra hM : StarSubalgebra ℂ (H →L[ℂ] H)` is defined as
    `StarSubalgebra.centralizer ℂ (Set.centralizer M)`, with `coe_modularAlgebra : ↑(modularAlgebra hM) = M`.
  - `instance : IsClosed (modularAlgebra hM : Set _)`, by `Set.isClosed_centralizer`.
  - Then `CStarAlgebra (modularAlgebra hM)` comes from Mathlib.
  - Cost: 1 def and 1 instance.
- **P2: quantify over a bundled algebra in the theorem.**
  The theorem takes `A : StarSubalgebra ℂ (H →L[ℂ] H)`, `[IsClosed (A : Set _)]` and
  `hA : IsVonNeumannSet (A : Set _)`, and applies the modular objects to `(A : Set _)`.
  - Advantage: no def for the algebra.
  - Cost: callers holding a `Set` must build `A` themselves.
- **P3: use Mathlib's `VonNeumannAlgebra H`.**
  It matches `localVonNeumannAlgebra`, which is already a `VonNeumannAlgebra H`, so AQFT callers
  would plug in directly.
  - Cost: Mathlib supplies no `IsClosed` or `CStarAlgebra` instance for it, so this still needs an
    instance, plus a bridge lemma `IsVonNeumannSet (M : Set _)`.

P1 keeps the `Set`-based modular API unchanged. A one-line corollary can serve P3 callers later.

## 4. The modular automorphism group

- **Proposed def:** `modularAutomorphism hM hΩ C hC (t : ℝ) : modularAlgebra hM ≃⋆ₐ[ℂ] modularAlgebra hM`, with
  - `toFun x := ⟨Δ^{it} ∘L x ∘L Δ^{-it}, _⟩`, membership from `modularUnitaryGroup_conj_mem_of_mem`;
  - `invFun x := ⟨Δ^{-it} ∘L x ∘L Δ^{it}, _⟩`;
  - multiplicativity from the group law, and `map_star` from `(Δ^{it})* = Δ^{-it}`
    (`modularUnitaryGroup_properties`).
- **New lemma:** `isOneParameterAut_modularAutomorphism`.
- **Corollary (optional):** the automorphism does not depend on C, since Δ does not
  (`thrm:modular-objects-independent-of-c`). It is not needed for the KMS statement.

## 5. The vector state

- **Proposed def**, general and placed in `GNS/` or `Operators/Modular/`:
  `vectorState (A : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (A : Set _)] (Ω : H) (hΩ : ‖Ω‖ = 1) : State A`,
  with `ω x = ⟪Ω, x Ω⟫`. Its proof obligations:
  - positivity: ⟪Ω, x*xΩ⟫ = ‖xΩ‖²;
  - norm: ‖ω‖ ≤ ‖Ω‖² = 1, with equality at x = 1.
- **The ‖Ω‖ = 1 hypothesis** is a normalization, not a restriction. A cyclic and separating Ω can be
  rescaled, and Δ and J do not change under rescaling. Whether that invariance is proved is still to
  check; it is not needed if the hypothesis is kept.

## 6. Proposed statement

```
theorem isKMSState_modularAutomorphism (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (hΩ1 : ‖Ω‖ = 1) :
    IsKMSState (fun t => modularAutomorphism hM hΩ C hC (-t)) 1
      (vectorState (modularAlgebra hM) Ω hΩ1)
```

- **Fallback if no new defs are approved:** state the analytic content directly on the `Set`, with
  `a, b ∈ M` and F(t) = ⟪Ω, a Δ^{-it} b Δ^{it} Ω⟫, and so on. This does not reuse
  `IsKMSState`, so the convexity and invariance API in `KMS.lean` would not apply. Not recommended.

## 7. Proof outline (sizes the blueprint)

Fix a, b ∈ M. Put μ for the complex spectral measure of Δ at the vectors (a*Ω, bΩ).
1. **Fixed point.** Δ^{it}Ω = Ω. Not found as a stated lemma; it follows from SΩ = Ω, so ΔΩ = Ω,
   so Ω lies in the range of E({1}). New node.
2. **Domain facts.** a*Ω, bΩ ∈ Dom Δ^{1/2}, Δ^{1/2}a*Ω = JaΩ and Δ^{1/2}bΩ = Jb*Ω. All exist:
   S = JΔ^{1/2} and Dom S ⊇ MΩ.
3. **The function.** G(z) = ⟪a*Ω, Δ^{-iz} bΩ⟫ := ∫ λ^{-iz} dμ(λ). Two ways to define it:
   - reuse the cut-off machinery: G_n(z) = ⟪a*Ω, p_{−iz,n}(Δ) bΩ⟫ is entire
     (`differentiable_inner_modularOperator_indicatorCpow_conj`-style results), and G_n → G uniformly
     on the strip because ‖(1 − E_n)Δ^{1/2}ξ‖ → 0. Holomorphy then follows from
     `TendstoLocallyUniformlyOn.differentiableOn`, and continuity from uniform limits.
   - or apply dominated differentiation of the integral directly.

   The first reuses the most existing code.
4. **Bound.** |G(z)| ≤ ‖a*Ω‖‖bΩ‖ + ‖Δ^{1/2}a*Ω‖‖Δ^{1/2}bΩ‖ on 0 ≤ Im z ≤ 1, since |λ^s| ≤ 1 + λ.
5. **Lower edge.** G(t) = ⟪a*Ω, Δ^{-it}bΔ^{it}Ω⟫ = ω(a σ₋ₜ(b)), using step 1.
6. **Upper edge.** G(t + i) = ⟪Δ^{1/2}a*Ω, Δ^{-it}Δ^{1/2}bΩ⟫ = ⟪JaΩ, Δ^{-it}Jb*Ω⟫ = ⟪σ₋ₜ(b)*Ω, aΩ⟫ = ω(σ₋ₜ(b)a).
   This needs JΔ^{it} = Δ^{it}J. Only the cut-off form exists
   (`modularConjugation_indicatorCpow_modularConjugation`), so the full form is a new node, a limit
   n → ∞.

Estimate: about 12 to 18 blueprint nodes. Of these, 3 are definitions (`modularAlgebra`,
`modularAutomorphism`, `vectorState`) and 1 is an instance. Steps 3, 4 and 6 carry the analytic work.

## Decisions for the user

- **D1.** Packaging of M: P1 (recommended), P2 or P3.
- **D2.** Approve the defs `modularAutomorphism` and `vectorState`, plus those that P1 needs.
- **D3.** State the theorem as the reversed flow at β = 1 (forced by `kmsStrip`), with a remark
  on β = −1.
- **D4.** Keep `‖Ω‖ = 1` as a hypothesis, or also prove that the modular objects are invariant
  under rescaling Ω.
- **D5.** Where `vectorState` lives: `GNS/` (general) or `Operators/Modular/`.
