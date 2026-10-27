import VersoManual
import Book.Meta
import Physicslib4.Spectral.SpectralTheorem

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book
-- Docstring code spans are elaborated in this scope; these namespaces let the names they mention,
-- written relative to the library's namespaces, resolve and link.
open Physicslib4 Physicslib4.Spectral Physicslib4.Spectral.ProjectionValuedMeasure
open Physicslib4.Spectral.IsBoundedQuadraticForm Physicslib4.Spectral.IsBorelGenerating

#doc (Manual) "Bounded spectral theory" =>

%%%
tag := "spectral"
file := "Bounded-spectral-theory"
%%%

This chapter describes how the library encodes the spectral theory of bounded self-adjoint
operators on a complex Hilbert space, up to the spectral theorem. It corresponds to
[Section 10.2](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:spectral-theorems)
of the blueprint, which follows the presentation of Hall's
[_Quantum Theory for Mathematicians_](https://doi.org/10.1007/978-1-4614-7116-5). The spectral
theorem for unbounded operators and Stone's theorem, in Sections 10.3 and 10.4 of the blueprint,
build on it.

# Overview
%%%
tag := "spectral-overview"
%%%

As you will recall, a Hermitian matrix $`A` has real eigenvalues $`\lambda_k` and mutually
orthogonal eigenprojections $`P_k` summing to $`\mathbf{1}`, so that
$`A = \sum_k \lambda_k P_k`, and a function of $`A` is $`f(A) = \sum_k f(\lambda_k) P_k`. The spectral theorem for a bounded
self-adjoint operator $`A` on a Hilbert space $`H` says the same with the sum over eigenvalues
replaced by an integral over the spectrum $`\sigma(A)` against a projection-valued measure
$`\mu^A`:

$$`A = \int_{\sigma(A)} \lambda \, d\mu^A(\lambda),
\qquad f(A) = \int_{\sigma(A)} f \, d\mu^A.`

For a unit vector $`\psi`, $`\langle \psi, \mu^A(E)\psi \rangle` is the probability that a
measurement of $`A` in the state $`\psi` gives a value in $`E`. The integral also covers
continuous spectrum: the multiplication operator $`(M\psi)(x) = x\,\psi(x)` on $`L^2([0, 1])` has
spectrum $`[0, 1]` and no eigenvalues.

The library proves the theorem as the blueprint does, in stages:

* _Spectrum and resolvent._ The spectrum of a bounded operator is compact, and nonempty when
  $`H \neq 0`; the resolvent set is open, and the resolvent is a power series near each of its
  points; the spectrum of a self-adjoint operator is real.
* _The continuous functional calculus._ For self-adjoint $`A`, $`f \mapsto f(A)` on the continuous
  real functions on $`\sigma(A)` is the unique bounded linear map that extends
  $`p \mapsto p(A)` on polynomials. It is multiplicative and isometric, $`f(A)` is self-adjoint,
  non-negative when $`f \ge 0`, and $`\sigma(f(A)) = f(\sigma(A))`.
* _The associated measures._ By the Riesz–Markov–Kakutani theorem, for each $`\psi` there is a
  unique finite positive measure $`\mu_\psi` on $`\sigma(A)` with
  $`\langle \psi, f(A)\psi \rangle = \int f \, d\mu_\psi` for continuous $`f`, of total mass
  $`\|\psi\|^2`.
* _Forms._ A bounded quadratic form $`Q` is $`\psi \mapsto \langle \psi, B\psi \rangle` for a
  unique bounded operator $`B`. This is how operators are constructed in the rest of the section.
* _The Borel functional calculus._ For a bounded Borel function $`f` on $`\sigma(A)`,
  $`Q_f(\psi) = \int f \, d\mu_\psi` is a bounded quadratic form, and $`f(A)` is its operator. The
  map $`f \mapsto f(A)` is linear and multiplicative, and $`f(A)` is self-adjoint for real $`f`.
  The boundedness of $`Q_f` and the multiplicativity are extended from continuous to Borel
  functions by a monotone-class argument.
* _Projection-valued measures and their integrals._ A projection-valued measure $`\mu` gives a
  measure $`\mu_\psi(E) = \langle \psi, \mu(E)\psi \rangle` for each vector and an operator
  $`\int f \, d\mu` for each bounded measurable $`f`, with
  $`\langle \psi, (\int f \, d\mu)\psi \rangle = \int f \, d\mu_\psi`. The integral is linear and
  multiplicative, bounded by $`\sup |f|`, and sends $`\bar f` to the adjoint.
* _The spectral theorem._ The projections $`\mu^A(E) = 1_E(A)` form a projection-valued measure on
  $`\sigma(A)` that integrates the identity function to $`A`, and it is the only one that does.
  For bounded Borel $`f`, $`f(A) = \int f \, d\mu^A`.

Every statement of the section is proved in Lean. The standard results the blueprint states
without proof, such as the Heine–Borel, Riesz representation, Stone–Weierstrass and bounded
convergence theorems, are Mathlib theorems or short derivations from them. The declarations are in
the namespace `Physicslib4.Spectral`, written without the prefix below.

# Design
%%%
tag := "spectral-design"
%%%

The conventions inherited from Mathlib, among them `realCalculus` as Mathlib's `cfcHom`, are
collected in the conventions chapter under {ref "conventions-implementation"}[Implementation choices].

The blueprint is the specification. Where the library departs from the blueprint's route, this
section says so; where the blueprint records the departure in a formalization note or a
convention, the section links to it.

## Operators, adjoints and the Hilbert space

A bounded operator is an element of `H →L[ℂ] H`, Mathlib's continuous linear maps, which is the
blueprint's $`\mathcal{B}(H)`. Mathlib supplies the operator norm, the adjoint
(`ContinuousLinearMap.adjoint`), self-adjointness (`IsSelfAdjoint`), orthogonal projections
(`IsStarProjection`), and a C\*-algebra structure on `H →L[ℂ] H`. Its inner product is
conjugate-linear in the first argument, the physics convention that the blueprint fixes in
[def:inner-product](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:inner-product).

The blueprint takes $`H` separable and nonzero, but only for convenience. No declaration assumes
separability; the convergence arguments use only completeness. Nonzero $`H` appears as a
`Nontrivial H` hypothesis on just the statements that use it, such as the nonemptiness of the
spectrum
([conv:nonzero-hilbert-space](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#conv:nonzero-hilbert-space)).

## Spectrum and resolvent are Mathlib's

The spectrum and the resolvent set are Mathlib's `spectrum ℂ A` and `resolventSet ℂ A`. Mathlib
defines them through $`\lambda\mathbf{1} - A`, the blueprint through $`A - \lambda\mathbf{1}`; the
two give the same set, which `mem_resolventSet_iff_isUnit_sub_smul` records. Mathlib's
`resolvent A λ` is $`(\lambda\mathbf{1} - A)^{-1}`, the negative of the blueprint's resolvent.

Once $`\sigma(A)` is known to be real for self-adjoint $`A` (`spectrum_subset_real`), every later
statement uses Mathlib's _real_ spectrum `spectrum ℝ A`, a compact subset of $`\mathbb{R}`, instead
of the blueprint's subset of $`\mathbb{C}`. It is the type on which Mathlib's functional calculus
is indexed, and it carries the Borel σ-algebra of its topology as a subspace of $`\mathbb{R}`.
Functions on the spectrum are functions on this subtype, and the identity function $`\lambda` is
`fun l => ((l : ℝ) : ℂ)`, which Lean prints as `fun l => ↑↑l`.

## The continuous calculus is Mathlib's

The blueprint builds $`f \mapsto f(A)` by hand: polynomials first, then the extension to
continuous functions by density (the Stone–Weierstrass theorem) and the bounded linear
transformation theorem. Mathlib already has the continuous functional calculus for self-adjoint
elements of a C\*-algebra, `cfcHom`, and the library uses it: `realCalculus hA` is `cfcHom hA`.
Its type, a \*-algebra homomorphism `C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H)`, records
multiplicativity and compatibility with the adjoint, and Mathlib proves the norm identity and
spectral mapping for it. What the library adds is the blueprint's characterisation: `realCalculus`
is the unique bounded linear map that sends each polynomial to $`p(A)`, proved from the density
of the polynomials (formalization note of
[prpstn:hall-8.3](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.3)).

As in the blueprint, the continuous calculus is for real functions; the Borel calculus below takes
complex ones.

## Measures from the Riesz–Markov–Kakutani theorem

The measure $`\mu_\psi` is Mathlib's Riesz–Markov–Kakutani measure `RealRMK.rieszMeasure` of the
positive functional $`f \mapsto \langle \psi, f(A)\psi \rangle`. Mathlib states that theorem for
compactly supported functions; on the compact $`\sigma(A)` these are all continuous functions.
Uniqueness of $`\mu_\psi` is Mathlib's uniqueness of the representing measure, so the
associated-measure theorem is fully proved.

## Operators from quadratic forms

Two constructions in the section produce operators: the Borel calculus $`f(A)` and the integral
$`\int f \, d\mu`. Both go through the same lemma
([prpstn:hall-a.63](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.63)):
a bounded quadratic form $`Q` determines a unique bounded $`B` with
$`Q(\psi) = \langle \psi, B\psi \rangle`. The form in both cases is
$`Q_f(\psi) = \int f \, d\mu_\psi`, so the hard work is to show that it is a bounded quadratic
form.

Sesquilinear forms are Mathlib's bundled semilinear maps: `H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ`, and, for bounded
ones, the continuous version `H →L⋆[ℂ] H →L[ℂ] ℂ`, whose continuity is the bound
$`|L(\varphi, \psi)| \le C\|\varphi\|\|\psi\|`. A quadratic form is a property of a plain function
`Q : H → ℂ` (`IsQuadraticForm`, `IsBoundedQuadraticForm`): $`Q_f` arrives as a function, and
these properties are what must be proved of it. The operator `IsBoundedQuadraticForm.toOperator`
comes from the polarization of $`Q` through Mathlib's Riesz representation of bounded sesquilinear
forms.

The operators `borelCalculus hA f` and `μ.integral f` are chosen from the existence-and-uniqueness
theorems, so their properties are theorems and not definitional: linearity is `borelCalculus_add`,
`integral_add` and their scalar versions. Both are defined on all functions, with the value $`0`
on functions that are not bounded and measurable, so every statement takes the hypothesis
`f ∈ BddMeasurable _` explicitly.

## Bounded Borel functions and the monotone-class bootstrap

The bounded measurable functions on $`X` form the complex subspace `BddMeasurable X`, a Mathlib
`Submodule`; membership is the pair "measurable, and bounded by a constant". It is the one spelling
of "bounded Borel function" in the section.

Three results extend a property from continuous to bounded Borel functions: that $`Q_f` is a bounded
quadratic form, that the Borel calculus is multiplicative, and that two spectral measures of
$`A` integrate every bounded Borel function to the same operator. All three use one lemma,
`IsBorelGenerating.eq_bddMeasurable`: a class of bounded measurable functions that is a subspace,
contains the continuous real functions, and is closed under uniformly bounded pointwise limits, is
all of `BddMeasurable X`. The proof follows the blueprint. The class $`\mathcal{L}_0` (`L0`) of
sets whose indicator is a bounded pointwise limit of continuous functions contains the closed sets
(by bump functions) and is an algebra of sets, and the monotone class theorem, proved in the
library, extends it to all Borel sets. Mathlib's dominated convergence theorem gives the bounded
convergence theorem, which is what passes the limits through $`\int \cdot \, d\mu_\psi`. Each
application then defines its class and checks the three conditions: `FClass` for boundedness,
`F1Class` and `F2Class` for multiplicativity.

The lemma needs a metric space with its Borel σ-algebra but not compactness. `L0` omits the
blueprint's requirement that the set be measurable, since that follows
(`measurableSet_of_mem_L0`).

## Projection-valued measures

`ProjectionValuedMeasure X H` is a structure, with the blueprint's axioms as fields
([def:projection-valued-measure](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:projection-valued-measure)).
As for Mathlib's vector measures, the underlying map is defined on all subsets of $`X`, and is
$`0` on non-measurable ones, so applying $`\mu` to a set needs no measurability proof. Countable
additivity is strong: $`\sum_j \mu(E_j)v` converges to $`\mu(\bigcup_j E_j)v` for each vector $`v`,
stated with Mathlib's unconditional `HasSum`, which for orthogonal vectors is the same as
convergence of the partial sums. $`\mu(\emptyset) = 0` is not a field, since it follows from
countable additivity. The blueprint's equivalence of projection-valued measures is equality.

## Two routes to f(A) and uniqueness

The section has two Borel calculi. `borelCalculus hA f` is built from $`Q_f` with the measures
$`\mu_\psi` of the Riesz–Markov–Kakutani theorem. The spectral measure is then
$`\mu^A(E) = 1_E(A)`, `spectralMeasure hA`, and `functionalCalculus hA f` is
$`\int f \, d\mu^A`. They agree (`borelCalculus_eq_integral`), so $`f(A)` is unambiguous.

The spectral theorem is stated with `∃!` over projection-valued measures on `spectrum ℝ A`.
Uniqueness follows the blueprint: two projection-valued measures that integrate $`\lambda` to $`A`
agree on polynomials, then on continuous functions by the complex Stone–Weierstrass theorem, then
on bounded Borel functions by the bootstrap, and so on indicator functions, which give the
projections themselves.

# Main definitions and theorems
%%%
tag := "spectral-main"
%%%

Definitions are shown with their docstrings, which give the mathematics and the blueprint entry;
theorems with their statements, as Lean prints them, and a line or two of explanation. Each
subsection opens with the blueprint entries it covers. In the printed statements, `inner ℂ x y` is
the inner product $`\langle x, y \rangle`, `hA : IsSelfAdjoint A` is the hypothesis that $`A` is
self-adjoint, `↑(spectrum ℝ A)` is the real spectrum as a type, and `fun l => ↑↑l` is the function
$`\lambda` on it. For the declarations not shown here, see the
[API documentation](https://physicslib.github.io/physicslib4/docs/Physicslib4/Spectral/SpectralTheorem.html)
and the files listed at the end of the chapter. The subsections follow the order of the proof; the
blueprint introduces projection-valued measures before the continuous calculus.

## Spectrum and resolvent

Blueprint: [def:bounded-operator-resolvent-and-spectrum][bp-res], [prpstn:hall-7.5][bp-75],
[prpstn:resolvent-holomorphy-and-neumann-series][bp-neu], [prpstn:hall-7.7][bp-77],
[lmm:spectrum-is-compact-metric-measurable][bp-cpt], [def:spectral-radius][bp-rad],
[thrm:gelfand-formula][bp-gel].

The spectrum and the resolvent set are Mathlib's. The library identifies them with the blueprint's,
in its sign convention:

```lean (name := checkResolvent)
open Physicslib4 Spectral in
#check mem_resolventSet_iff_isUnit_sub_smul
```

```leanOutput checkResolvent
Physicslib4.Spectral.mem_resolventSet_iff_isUnit_sub_smul.{u_1} {H : Type u_1} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (A : H →L[ℂ] H) (lam : ℂ) : lam ∈ resolventSet ℂ A ↔ IsUnit (A - lam • 1)
```

The spectrum is compact
({apiDocs Physicslib4.Spectral.isCompact_spectrum}[`isCompact_spectrum`]) and, for $`H \neq 0`,
nonempty ({apiDocs Physicslib4.Spectral.spectrum_nonempty}[`spectrum_nonempty`]); the resolvent set
is open, and near each of its points the resolvent is a norm-convergent power series
({apiDocs Physicslib4.Spectral.isOpen_resolventSet}[`isOpen_resolventSet`],
{apiDocs Physicslib4.Spectral.exists_hasSum_resolvent}[`exists_hasSum_resolvent`]). The spectral
radius and Gelfand's formula are Mathlib's {apiDocs spectralRadius}[`spectralRadius`] and
{apiDocs spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius}[`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`].
For a self-adjoint operator the spectrum is real:

```lean (name := checkReal)
open Physicslib4 Spectral in
#check spectrum_subset_real
```

```leanOutput checkReal
Physicslib4.Spectral.spectrum_subset_real.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) : spectrum ℂ A ⊆ {z | z.im = 0}
```

The proof takes this from Mathlib (`IsSelfAdjoint.spectrumRestricts`). The blueprint's estimate
behind it, $`\|(A - (a + ib)\mathbf{1})\psi\|^2 \ge b^2\|\psi\|^2` for real $`a` and $`b`, is
{apiDocs Physicslib4.Spectral.sq_norm_sub_smul_apply_le}[`sq_norm_sub_smul_apply_le`].

[bp-res]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-operator-resolvent-and-spectrum
[bp-75]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.5
[bp-neu]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:resolvent-holomorphy-and-neumann-series
[bp-77]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-7.7
[bp-cpt]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spectrum-is-compact-metric-measurable
[bp-rad]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spectral-radius
[bp-gel]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:gelfand-formula

## The continuous functional calculus

Blueprint: [prpstn:hall-8.3][bp-83], [prpstn:hall-8.4][bp-84], and its parts
[prpstn:cfc-multiplicative][bp-cfcm] to [prpstn:cfc-spectral-mapping][bp-cfcs].

{docstring Physicslib4.Spectral.realCalculus}

The blueprint's characterisation, with `polyOn A p` the polynomial $`p` restricted to
$`\sigma(A)`:

```lean (name := checkRealCalc)
open Physicslib4 Spectral in
#check existsUnique_realCalculus
```

```leanOutput checkRealCalc
Physicslib4.Spectral.existsUnique_realCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
  ∃! T, ∀ (p : Polynomial ℝ), T (polyOn A p) = (Polynomial.aeval A) p
```

Here `T` ranges over the bounded ℝ-linear maps `C(spectrum ℝ A, ℝ) →L[ℝ] (H →L[ℂ] H)`, and
{apiDocs Physicslib4.Spectral.realCalculus_polyOn}[`realCalculus_polyOn`] says that `realCalculus` is the one. The properties are separate theorems,
collected in {apiDocs Physicslib4.Spectral.realCalculus_properties}[`realCalculus_properties`]; for
example, the norm identity $`\|f(A)\| = \sup_{\sigma(A)} |f|`:

```lean (name := checkNormCalc)
open Physicslib4 Spectral in
#check norm_realCalculus
```

```leanOutput checkNormCalc
Physicslib4.Spectral.norm_realCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (f : C(↑(spectrum ℝ A), ℝ)) : ‖(realCalculus hA) f‖ = ‖f‖
```

[bp-83]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.3
[bp-84]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.4
[bp-cfcm]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:cfc-multiplicative
[bp-cfcs]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:cfc-spectral-mapping

## The associated measures

Blueprint: [thrm:riesz-representation][bp-rmk], [prpstn:associated-measures-self-adjoint][bp-am],
[lmm:associated-measures-are-finite][bp-amf].

{docstring Physicslib4.Spectral.assocMeasure}

The associated-measure theorem, existence and uniqueness:

```lean (name := checkAssocMeasure)
open Physicslib4 Spectral in
#check existsUnique_assocMeasure
```

```leanOutput checkAssocMeasure
Physicslib4.Spectral.existsUnique_assocMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H) :
  ∃! ν,
    MeasureTheory.IsFiniteMeasure ν ∧
      ∀ (f : C(↑(spectrum ℝ A), ℝ)), inner ℂ ψ (((realCalculus hA) f) ψ) = ↑(∫ (l : ↑(spectrum ℝ A)), f l ∂ν)
```

Here `ν` ranges over the measures on `spectrum ℝ A`; the integral is real, and `↑` embeds it in
$`\mathbb{C}`. The total mass is
{apiDocs Physicslib4.Spectral.assocMeasure_univ}[`assocMeasure_univ`],
$`\mu_\psi(\sigma(A)) = \|\psi\|^2`, stated in Mathlib's extended non-negative reals, where
measures take their values. The Riesz–Markov–Kakutani theorem itself,
for a positive functional on the continuous functions on a compact metric space, is
{apiDocs Physicslib4.Spectral.existsUnique_measure_of_positive_linear}[`existsUnique_measure_of_positive_linear`].

[bp-rmk]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:riesz-representation
[bp-am]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:associated-measures-self-adjoint
[bp-amf]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:associated-measures-are-finite

## Sesquilinear and quadratic forms

Blueprint: [def:bounded-sesquilinear-form][bp-bsf], [def:bounded-quadratic-form][bp-bqf],
[prpstn:hall-a.61][bp-a61], [prpstn:hall-a.63][bp-a63].

{docstring Physicslib4.Spectral.BoundedSesquilinearForm}

{docstring Physicslib4.Spectral.IsQuadraticForm}

{docstring Physicslib4.Spectral.IsBoundedQuadraticForm}

The representation theorem for bounded quadratic forms:

```lean (name := checkQuadOp)
open Physicslib4 Spectral in
#check existsUnique_operator_of_isBoundedQuadraticForm
```

```leanOutput checkQuadOp
Physicslib4.Spectral.existsUnique_operator_of_isBoundedQuadraticForm.{u_1} {H : Type u_1} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] {Q : H → ℂ} (hQ : IsBoundedQuadraticForm Q) :
  ∃! A, ∀ (ψ : H), Q ψ = inner ℂ ψ (A ψ)
```

The operator is {apiDocs Physicslib4.Spectral.IsBoundedQuadraticForm.toOperator}[`hQ.toOperator`],
and it is self-adjoint when $`Q` is real-valued ({apiDocs Physicslib4.Spectral.IsBoundedQuadraticForm.isSelfAdjoint_toOperator}[`IsBoundedQuadraticForm.isSelfAdjoint_toOperator`]).
The polarization formula is
{apiDocs Physicslib4.Spectral.polarization}[`polarization`]. To apply the theorem to a candidate
$`Q_f`, one proves the homogeneity $`Q_f(c\psi) = |c|^2 Q_f(\psi)`, the sesquilinearity of its
polarization and a bound $`|Q_f(\psi)| \le C\|\psi\|^2`; for the Borel calculus these are the
propositions from
[prpstn:F-homogeneous](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F-homogeneous)
to
[prpstn:F-bounded](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:F-bounded).

[bp-bsf]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-sesquilinear-form
[bp-bqf]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:bounded-quadratic-form
[bp-a61]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.61
[bp-a63]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-a.63

## Bounded Borel functions and the bootstrap

Blueprint: [thrm:bounded-convergence-theorem][bp-bct], [def:L0-class][bp-l0],
[thrm:monotone-class-theorem][bp-mct], [lmm:hall-prblm-8.3.3a][bp-33a],
[lmm:hall-prblm-8.3.3b][bp-33b], [lmm:hall-prblm-8.3.3c][bp-33c].

{docstring Physicslib4.Spectral.BddMeasurable}

{docstring Physicslib4.Spectral.BoundedPointwiseLimit}

{docstring Physicslib4.Spectral.IsBorelGenerating}

The conclusion of the bootstrap:

```lean (name := checkBootstrap)
open Physicslib4 Spectral in
#check IsBorelGenerating.eq_bddMeasurable
```

```leanOutput checkBootstrap
Physicslib4.Spectral.IsBorelGenerating.eq_bddMeasurable.{u_1} {X : Type u_1} [MetricSpace X] [MeasurableSpace X]
  [BorelSpace X] {𝒞 : Set (X → ℂ)} (h𝒞 : IsBorelGenerating 𝒞) : 𝒞 = ↑(BddMeasurable X)
```

Its ingredients are the class {apiDocs Physicslib4.Spectral.L0}[`L0`], an algebra of sets
containing the open sets ({apiDocs Physicslib4.Spectral.isSetAlgebra_L0}[`isSetAlgebra_L0`]), the
monotone class theorem
({apiDocs Physicslib4.Spectral.generateFrom_subset_of_isMonotoneClass}[`generateFrom_subset_of_isMonotoneClass`]),
and the indicator step
{apiDocs Physicslib4.Spectral.IsBorelGenerating.indicator_mem}[`IsBorelGenerating.indicator_mem`].

[bp-bct]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:bounded-convergence-theorem
[bp-l0]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:L0-class
[bp-mct]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:monotone-class-theorem
[bp-33a]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-prblm-8.3.3a
[bp-33b]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-prblm-8.3.3b
[bp-33c]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:hall-prblm-8.3.3c

## Projection-valued measures and the operator-valued integral

Blueprint: [def:projection-valued-measure][bp-pvm],
[thrm:projection-valued-measures-associated-measure][bp-pvma],
[thrm:operator-valued-integration][bp-ovi], [prpstn:integral-of-indicator][bp-ind],
[prpstn:integral-norm-bound][bp-nb], [prpstn:integral-multiplicative][bp-mul],
[prpstn:integral-conjugation][bp-conj].

{docstring Physicslib4.Spectral.ProjectionValuedMeasure}

{docstring Physicslib4.Spectral.ProjectionValuedMeasure.assoc}

{docstring Physicslib4.Spectral.ProjectionValuedMeasure.integral}

The integral comes from a unique linear map on the bounded measurable functions, characterised by
its expectation values:

```lean (name := checkIntegral)
open Physicslib4 Spectral in
#check ProjectionValuedMeasure.existsUnique_integral
```

```leanOutput checkIntegral
Physicslib4.Spectral.ProjectionValuedMeasure.existsUnique_integral.{u_1, u_2} {X : Type u_1} [MeasurableSpace X]
  {H : Type u_2} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (μ : ProjectionValuedMeasure X H) :
  ∃! T, ∀ (f : ↥(BddMeasurable X)) (ψ : H), inner ℂ ψ ((T f) ψ) = ∫ (x : X), ↑f x ∂μ.assoc ψ
```

Here `T` ranges over the ℂ-linear maps `BddMeasurable X →ₗ[ℂ] (H →L[ℂ] H)`, `↑f` is the function
underlying an element of the subspace, and `μ.assoc ψ` is $`\mu_\psi`. That
$`Q_f(\psi) = \int f \, d\mu_\psi` is a bounded quadratic form is proved in three stages, as in the
blueprint: for indicator functions, for simple functions, and for bounded measurable functions as
uniform limits of simple ones
({apiDocs Physicslib4.Spectral.ProjectionValuedMeasure.isBoundedQuadraticForm_integral_bddMeasurable}[`isBoundedQuadraticForm_integral_bddMeasurable`]).

It is multiplicative, the operator form of $`\int fg \, d\mu = (\int f \, d\mu)(\int g \, d\mu)`:

```lean (name := checkIntegralMul)
open Physicslib4 Spectral in
#check ProjectionValuedMeasure.integral_mul
```

```leanOutput checkIntegralMul
Physicslib4.Spectral.ProjectionValuedMeasure.integral_mul.{u_1, u_2} {X : Type u_1} [MeasurableSpace X] {H : Type u_2}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (μ : ProjectionValuedMeasure X H) {f g : X → ℂ}
  (hf : f ∈ BddMeasurable X) (hg : g ∈ BddMeasurable X) : μ.integral (f * g) = μ.integral f * μ.integral g
```

The bound $`\|\int f \, d\mu\| \le \sup_x |f(x)|` is
{apiDocs Physicslib4.Spectral.ProjectionValuedMeasure.norm_integral_le}[`norm_integral_le`]; its
proof first establishes the weaker bound $`6\sup_x |f(x)|`, which it uses to pass to the limit of
simple functions (formalization note of [prpstn:integral-norm-bound][bp-nb]). The identity
$`\int \bar f \, d\mu = (\int f \, d\mu)^*` is
{apiDocs Physicslib4.Spectral.ProjectionValuedMeasure.integral_conj}[`integral_conj`]. The measure
$`\mu_\psi` exists and is unique by
{apiDocs Physicslib4.Spectral.ProjectionValuedMeasure.existsUnique_assoc}[`existsUnique_assoc`].

[bp-pvm]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:projection-valued-measure
[bp-pvma]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:projection-valued-measures-associated-measure
[bp-ovi]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:operator-valued-integration
[bp-ind]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-of-indicator
[bp-nb]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-norm-bound
[bp-mul]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-multiplicative
[bp-conj]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:integral-conjugation

## The Borel functional calculus

Blueprint: [def:hall-8.6][bp-86], [prpstn:hall-8.7][bp-87], [def:F-class][bp-F],
[def:hall-8.8][bp-88], [lmm:lemma-3][bp-l3], [prpstn:hall-8.9][bp-89],
[def:F1-F2-classes][bp-F12].

{docstring Physicslib4.Spectral.borelForm}

Every bounded Borel function gives a bounded quadratic form, by the bootstrap applied to
{apiDocs Physicslib4.Spectral.FClass}[`FClass`]:

```lean (name := checkBorelForm)
open Physicslib4 Spectral in
#check isBoundedQuadraticForm_borelForm
```

```leanOutput checkBorelForm
Physicslib4.Spectral.isBoundedQuadraticForm_borelForm.{u_1} {H : Type u_1} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {f : ↑(spectrum ℝ A) → ℂ}
  (hf : f ∈ BddMeasurable ↑(spectrum ℝ A)) : IsBoundedQuadraticForm (borelForm hA f)
```

{docstring Physicslib4.Spectral.borelCalculus}

Multiplicativity, proved by the bootstrap twice, through the classes
{apiDocs Physicslib4.Spectral.F1Class}[`F1Class`] and
{apiDocs Physicslib4.Spectral.F2Class}[`F2Class`]:

```lean (name := checkBorelMul)
open Physicslib4 Spectral in
#check borelCalculus_mul
```

```leanOutput checkBorelMul
Physicslib4.Spectral.borelCalculus_mul.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {f g : ↑(spectrum ℝ A) → ℂ}
  (hf : f ∈ BddMeasurable ↑(spectrum ℝ A)) (hg : g ∈ BddMeasurable ↑(spectrum ℝ A)) :
  (borelCalculus hA fun l => f l * g l) = borelCalculus hA f * borelCalculus hA g
```

The first application shows that the bounded Borel $`f` with $`(fg)(A) = f(A)g(A)` for every
continuous real $`g` form a class satisfying `IsBorelGenerating`, starting from the
multiplicativity of the continuous calculus. The second does the same for the $`g` with
$`(fg)(A) = f(A)g(A)` for every bounded Borel $`f`, starting from the first.

[bp-86]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-8.6
[bp-87]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.7
[bp-F]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:F-class
[bp-88]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:hall-8.8
[bp-l3]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lemma-3
[bp-89]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:hall-8.9
[bp-F12]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:F1-F2-classes

## The spectral theorem

Blueprint: [thrm:hall-8.10][bp-810], [prpstn:mua-projection][bp-muap] to
[prpstn:mua-integrates-to-A][bp-muaA], [thrm:hall-prblm-8.3.4][bp-uniq],
[thrm:spectral-theorem-for-bounded-operators][bp-st], [def:functional-calculus][bp-fc].

{docstring Physicslib4.Spectral.spectralMeasure}

The headline theorem of the section:

```lean (name := checkSpectral)
open Physicslib4 Spectral in
#check existsUnique_spectralMeasure
```

```leanOutput checkSpectral
Physicslib4.Spectral.existsUnique_spectralMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) : ∃! μ, (μ.integral fun l => ↑↑l) = A
```

Here `μ` ranges over `ProjectionValuedMeasure (spectrum ℝ A) H`, and the integrand is
$`\lambda`. The blueprint's form of the existence half, with $`\mu^A(E) = 1_E(A)` on Borel sets,
is {apiDocs Physicslib4.Spectral.exists_spectralMeasure}[`exists_spectralMeasure`]. Existence is
{apiDocs Physicslib4.Spectral.spectralMeasure_integral_id}[`spectralMeasure_integral_id`] and
uniqueness {apiDocs Physicslib4.Spectral.pvm_eq_of_integral_id_eq}[`pvm_eq_of_integral_id_eq`].
The two Borel calculi agree:

```lean (name := checkAgree)
open Physicslib4 Spectral in
#check borelCalculus_eq_integral
```

```leanOutput checkAgree
Physicslib4.Spectral.borelCalculus_eq_integral.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {f : ↑(spectrum ℝ A) → ℂ}
  (hf : f ∈ BddMeasurable ↑(spectrum ℝ A)) : borelCalculus hA f = (spectralMeasure hA).integral f
```

{docstring Physicslib4.Spectral.functionalCalculus}

[bp-810]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-8.10
[bp-muap]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:mua-projection
[bp-muaA]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#prpstn:mua-integrates-to-A
[bp-uniq]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:hall-prblm-8.3.4
[bp-st]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:spectral-theorem-for-bounded-operators
[bp-fc]: https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:functional-calculus

# Where to look
%%%
tag := "spectral-files"
%%%

The section is formalised in the top-level files of `Physicslib4/Spectral/`, one topic per file.
Each entry links to the API documentation of a representative declaration, from which the rest of
the file can be browsed.

* `Basic.lean`: the prerequisites about bounded operators that Mathlib does not state in the
  blueprint's form, bounded measurable functions, the resolvent in the blueprint's sign convention,
  and the bounded convergence theorem, {apiDocs Physicslib4.Spectral.BddMeasurable}[`BddMeasurable`].
  Its module documentation lists the blueprint entries that are Mathlib declarations.
* `Spectrum.lean`: compactness and nonemptiness of the spectrum, the resolvent as a power series,
  and the reality of the spectrum of a self-adjoint operator,
  {apiDocs Physicslib4.Spectral.spectrum_subset_real}[`spectrum_subset_real`].
* `ContinuousCalculus.lean`: the continuous functional calculus and the associated measures,
  {apiDocs Physicslib4.Spectral.realCalculus}[`realCalculus`].
* `Forms.lean`: sesquilinear and quadratic forms, polarization, and the operator of a bounded
  quadratic form,
  {apiDocs Physicslib4.Spectral.existsUnique_operator_of_isBoundedQuadraticForm}[`existsUnique_operator_of_isBoundedQuadraticForm`].
* `BorelClasses.lean`: bump functions, the monotone class theorem, $`\mathcal{L}_0` and the
  bootstrap, {apiDocs Physicslib4.Spectral.IsBorelGenerating}[`IsBorelGenerating`].
* `ProjectionValuedMeasure.lean`: projection-valued measures, their associated measures, and sums of
  orthogonal projections,
  {apiDocs Physicslib4.Spectral.ProjectionValuedMeasure}[`ProjectionValuedMeasure`].
* `OperatorIntegral.lean`: the operator-valued integral and its properties,
  {apiDocs Physicslib4.Spectral.ProjectionValuedMeasure.integral}[`ProjectionValuedMeasure.integral`].
* `BorelCalculus.lean`: the quadratic forms $`Q_f`, the Borel functional calculus and its
  multiplicativity, {apiDocs Physicslib4.Spectral.borelCalculus}[`borelCalculus`].
* `SpectralTheorem.lean`: the spectral measure, uniqueness, the spectral theorem and the
  functional calculus,
  {apiDocs Physicslib4.Spectral.existsUnique_spectralMeasure}[`existsUnique_spectralMeasure`].

The subdirectories `Unbounded/` and `Stone/` formalise Sections 10.3 and 10.4 of the blueprint.
The blueprint section is
[Section 10.2](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#sctn:spectral-theorems),
and the [section page](https://physicslib.github.io/physicslib4/sec10-2-spectral.html) lists each
entry with the Lean declaration that formalises it.
