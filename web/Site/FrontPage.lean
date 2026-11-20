import VersoBlog
import Site.Components
import Physicslib4.Spacetime.LorentzCausality
import Physicslib4.AQFT.HaagKastler.Net
import Physicslib4.AQFT.HaagKastler.ReehSchlieder.Additivity
import Physicslib4.Operators.Modular.VanDaele
import Physicslib4.Operators.Modular.TakesakiKMS
import Physicslib4.AQFT.Borchers
import Physicslib4.AQFT.HaagKastler.BisognanoWichmann

open Verso Genre Blog
open Site

#doc (Page) "physicslib4" =>

%%%
showInNav := false
htmlId := some "frontpage"
%%%

:::hero
A Lean 4 formalisation of axiomatic physical theories.
:::

```leanInit physicslib4
```

```lean physicslib4 -show
set_option linter.unusedVariables false

open Physicslib4 Spacetime AQFT HaagKastler Modular GNS

/-- Minkowski space. -/
local notation "𝕄" => StandardMinkowskiSpacetime.Carrier

/-- Causal precedence in Minkowski space, for the standard time orientation. -/
local notation:50 p:51 " ≺ " q:51 =>
  CausallyPrecedes StandardMinkowskiSpacetime standardMinkowskiTimeOrientation p q

/- The Hilbert space `H`, a set `M` of bounded operators with a vector `Ω`, the antiunitary
involution `C` used to build the modular objects, and a Haag–Kastler net `N` with a
representation `π` of its quasilocal algebra and a representation `U` of the Poincaré group. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Set (H →L[ℂ] H)} {Ω : H} (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x)
  {N : HaagKastlerNet} {π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)}
  {U : InhomogeneousLorentzGroup → (H ≃ₗᵢ[ℂ] H)}

/-- The commutant `M′` of a set of bounded operators. -/
local postfix:max "′" => Set.centralizer

set_option hygiene false in
/-- `Δ^{it}`, the modular unitary group of `(M, Ω)`, as a bounded operator. -/
local notation "Δ[" t "]" =>
  (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap

set_option hygiene false in
/-- `J T J`, with `J` the modular conjugation of `(M, Ω)`. -/
local notation "J[" T "]" => modularConjugationConj hM hΩ C hC T

set_option hygiene false in
/-- The modular automorphism `σ_t = Δ^{it} · Δ^{-it}` of the von Neumann algebra `M`. -/
local notation "σ[" t "]" => modularAutomorphism hM hΩ C hC t

set_option hygiene false in
/-- The vector state `ω_Ω(a) = ⟨Ω, a Ω⟩` on `M`. -/
local notation "ω_Ω" => vectorState (modularAlgebra M) Ω hΩ1

set_option hygiene false in
/-- `V(t)` as a bounded operator. -/
local notation "V[" t "]" => (V t).toLinearIsometry.toContinuousLinearMap

set_option hygiene false in
/-- The von Neumann algebra `R(W_R)` of the right wedge. -/
local notation "ℛ(W_R)" => N.regionVonNeumann π rightWedge

set_option hygiene false in
/-- `Δ_{W_R}^{it}`, the modular unitary group of `(R(W_R), Ω)`. -/
local notation "Δ_W[" t "]" =>
  modularUnitaryGroup (N.regionVonNeumann_isVonNeumannSet π rightWedge).2 hΩ C hC t

set_option hygiene false in
/-- The wedge modular defect `Z(t) = Δ_{W_R}^{it} U(b(2πt))`. -/
local notation "Z[" t "]" => HaagKastlerNet.wedgeModularDefect N π U hΩ C hC t
```

::::::centeredSection "example" "Checked by Lean"

Hover over a name to see its type.

:::::gallery

Lorentz invariance

```lean physicslib4
/-- Causal precedence is invariant under the Poincaré group: an inhomogeneous Lorentz
transformation `g` maps causal curves to causal curves, so the event `g • p` can influence the
event `g • q` exactly when `p` can influence `q`. No choice of inertial frame changes which events
are causally related. -/
example (g : InhomogeneousLorentzGroup) (p q : 𝕄) :
    g • p ≺ g • q ↔ p ≺ q :=
  causallyPrecedes_smul_iff g p q
```

With 𝕄 for Minkowski space and ≺ for causal precedence: the statement of `causallyPrecedes_smul_iff`.

manual/Spacetime-and-geometry/

Consistent axioms

```lean physicslib4
/-- The Haag–Kastler axioms have a model: the net that assigns the trivial algebra `ℂ` to every
causal diamond satisfies isotony, local commutativity and Poincaré covariance. A theory whose
axioms had no model would prove everything, so this example is the consistency check of the
structure `HaagKastlerNet`. -/
example : Nonempty HaagKastlerNet.{0} :=
  ⟨trivialHaagKastlerNet⟩
```

A Haag–Kastler net exists, so the axioms are consistent.

manual/Haag-Kastler-axioms-in-Minkowski-spacetime/

Reeh–Schlieder

```lean physicslib4
/-- The Reeh–Schlieder theorem for a covariant vacuum representation `(π, Ω, U)` of a weakly
additive net: for every nonempty causal diamond `B`, the vectors `A Ω` with `A` a local operator
of `B` are dense in the Hilbert space. Operations in an arbitrarily small region of spacetime
approximate every state, which is the source of the entanglement of the vacuum. -/
example (h : N.IsCovariantVacuumRep π Ω U) (hwa : N.IsWeaklyAdditive)
    {B : Set 𝕄} (hB : IsAlexandrovBasisSet B) (hne : B.Nonempty) :
    Dense ((fun A => A Ω) '' N.localOperators π hB) :=
  reeh_schlieder_cyclic_of_vacuum hwa π Ω U h.vacuum_hypotheses.1
    (fun γ _ hγ => h.vacuum_hypotheses.2.1 γ hγ) h.cyclic hB hne
```

The vacuum is cyclic for the algebra of every nonempty diamond: `reeh_schlieder_cyclic_of_vacuum`.

manual/The-Reeh-Schlieder-theorem/

Tomita–Takesaki

```lean physicslib4
/-- Tomita's theorem: for a von Neumann algebra `M` with a cyclic and separating vector `Ω`, the
modular conjugation `J` maps `M` onto its commutant, `J M J = M′`, and the modular unitary group
`Δ^{it}` maps `M` onto itself for every real `t`. Here `Δ[t]` is `Δ^{it}` and `J[x]` is `J x J`,
built from the polar decomposition `S = J Δ^{1/2}` of the closure of `x Ω ↦ x* Ω`. -/
example (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) :
    (fun x => J[x]) '' M = M′ ∧ ∀ t : ℝ, (fun x => Δ[t] ∘L x ∘L Δ[-t]) '' M = M :=
  tomita_theorem hM hΩ C hC
```

Tomita's theorem, `J M J = M′` and `Δⁱᵗ M Δ⁻ⁱᵗ = M`: the statement of `tomita_theorem`.

manual/Tomita-Takesaki-theory/

Takesaki KMS

```lean physicslib4
/-- Takesaki's theorem: the vector state `ω_Ω` of a cyclic and separating unit vector is a KMS
state at inverse temperature `1` for the reversed modular flow `t ↦ σ_{-t}`. The modular group,
built from the pair `(M, Ω)` alone, is the time evolution for which `ω_Ω` is a thermal
equilibrium state. -/
example (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (hΩ1 : ‖Ω‖ = 1) :
    IsKMSState (fun t => σ[-t]) 1 ω_Ω :=
  isKMSState_modularAutomorphism hM hΩ C hC hΩ1
```

The vector state is KMS for the modular flow: `isKMSState_modularAutomorphism`.

manual/Tomita-Takesaki-theory/

Borchers

```lean physicslib4
/-- Borchers' theorem: if `V` is a half-sided translation for `(M, Ω)`, a positive-energy
unitary group fixing `Ω` with `V(t) M V(-t) ⊆ M` for `t ≥ 0`, then the modular group acts on it
as dilations, `Δ^{is} V(t) Δ^{-is} = V(e^{-2πs} t)`, and the modular conjugation reflects it,
`J V(t) J = V(-t)`. Applied to a wedge, it identifies the modular group with the boosts. -/
example (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω)
    {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsHalfSidedTranslation M Ω V) :
    (∀ s t : ℝ, Δ[s] ∘L V[t] ∘L Δ[-s] = V[Real.exp (-(2 * Real.pi * s)) * t]) ∧
      ∀ t : ℝ, J[V[t]] = V[-t] :=
  borchers hM hΩ C hC hV
```

Half-sided translations are dilated by the modular group: the statement of `borchers`.

manual/Borchers-theorem-and-the-wedge-modular-group/

Bisognano–Wichmann

```lean physicslib4
/-- Bisognano–Wichmann up to an internal symmetry: in a covariant vacuum representation with
modular covariance for the right wedge `W_R`, the wedge modular group is the boost group
`U(b(-2πt))` up to the factor `Z(t)`, an internal symmetry of `(π, Ω)` that commutes with the
translations. The theorem also gives `J U(a) J = U(j a)` for the wedge reflection `j`. -/
example (h : N.IsCovariantVacuumRep π Ω U) (hΩ : IsCyclicSeparatingVector ℛ(W_R) Ω)
    (hMC : N.IsWedgeModularCovariant π hΩ C hC) (t : ℝ) :
    (∀ ψ : H, Δ_W[t] ψ = Z[t] (U (wedgeBoost (-(2 * Real.pi * t))) ψ)) ∧
      N.IsInternalSymmetry π Ω Z[t] ∧
      ∀ (a : SpacetimeModel) (ψ : H),
        Z[t] (U (translationSub a) ψ) = U (translationSub a) (Z[t] ψ) :=
  (h.bisognanoWichmann_internal hΩ C hC hMC).1 t
```

The wedge modular group is the boost group up to an internal symmetry: `bisognanoWichmann_internal`.

manual/Borchers-theorem-and-the-wedge-modular-group/#borchers-wedges-bw-internal

:::::

::::::

::::::centeredSection "contents" "What is currently formalised"

:::features
:::

::::::
