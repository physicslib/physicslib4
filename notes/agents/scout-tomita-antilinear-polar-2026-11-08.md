# Scout: antilinear closable operators and polar decomposition for Tomita–Takesaki

Target: S₀(aΩ) = a*Ω (antilinear, densely defined, closable), closure S = JΔ^{1/2}, Δ = S*S.
Paths are relative to the repo root; M = `.lake/packages/mathlib/Mathlib`. All signatures were read from source.

## 1. Antilinear unbounded operators

### (a) Semilinear partial maps in Mathlib
- `LinearPMap` is semilinear: `structure LinearPMap {R S} [Ring R] [Ring S] (σ : R →+* S) (E F)` (`M/LinearAlgebra/LinearPMap.lean:41`).
  Notation `E →ₛₗ.[σ] F`. `E →ₗ.[R] F` is notation for `LinearPMap (RingHom.id R) E F` (line 50-51).
  So `H →ₛₗ.[starRingEnd ℂ] H` is an antilinear partial map. The algebraic API (domain, sup/le, `graph`, `inverse`, `ker`) is general.
- Everything analytic is linear only:
  - `M/Topology/Algebra/Module/LinearPMap.lean` (`IsClosed`, `IsClosable`, `closure`, `closure_def`, `le_closure`, `IsClosable.closure_mono`, `closureHasCore`, `inverse_closure`) is stated for `E →ₗ.[R] F` with `[CommRing R]`.
  - `M/Analysis/InnerProductSpace/LinearPMap.lean` (`LinearPMap.adjoint`, `adjointDomain`, `adjoint_isFormalAdjoint`, `adjoint_graph_eq_graph_adjoint`, `adjoint_isClosed`, `instStar`, `IsSelfAdjoint.dense_domain`) is stated for `𝕜 := RCLike` and `E →ₗ.[𝕜] F`.
  - No antilinear adjoint and no antilinear closure exists.
- Verdict: the data structure exists. The closability/adjoint theory would have to be rewritten for σ = conj.

### (b) Option R: view H as a real Hilbert space, S : `LinearPMap ℝ H H`
- `Inner.rclikeToReal 𝕜 E` and `InnerProductSpace.rclikeToReal 𝕜 E` (`M/Analysis/InnerProductSpace/Basic.lean:944,956`) are an `@[instance_reducible] def` and an `abbrev`, deliberately NOT instances (diamond risk).
  Activate locally: `letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H`.
  The inner product is `Re⟪x,y⟫`. It is built on `NormedSpace.restrictScalars`, so the norm and topology are the same. Completeness is automatic (the same `NormedAddCommGroup`).
- The Mathlib `LinearPMap.adjoint`/`closure` then apply with 𝕜 = ℝ. `closure` depends only on the topology, so it is literally the same set-theoretic closure of the graph.
- Math check: the real adjoint equals the antilinear adjoint. Convention: inner product is conjugate-linear in the first slot (Mathlib), linear in the second.
  - Let S be antilinear and D = dom S dense (a ℂ-subspace). Say y ∈ dom S^R with Re⟨S^R y, x⟩ = Re⟨y, Sx⟩ for all x ∈ D.
  - Replace x by ix. Then S(ix) = -i Sx, so Re⟨y,S(ix)⟩ = Re(-i⟨y,Sx⟩) = Im⟨y,Sx⟩.
  - Also Re⟨S^R y, ix⟩ = Re(i⟨S^R y,x⟩) = -Im⟨S^R y,x⟩.
  - Hence ⟨y,Sx⟩ = Re⟨S^R y,x⟩ − i Im⟨S^R y,x⟩ = conj⟨S^R y,x⟩ = ⟨x,S^R y⟩.
  - Thus S^R satisfies the antilinear adjoint identity ⟨y,Sx⟩ = ⟨x,S*y⟩. Conversely, taking real parts of that identity shows any y with the identity is in dom S^R.
  - Boundedness of x ↦ Re⟨y,Sx⟩ on D gives boundedness of the complex functional via the phase trick (use ix). So the domains agree.
  - S^R is also antilinear, since it is the unique solution of the identity and is ℂ-antilinear by the same identity.
- S*S then has the ℝ-linear type `LinearPMap ℝ H H`. To feed it to the project's spectral theory (`H →ₗ.[ℂ] H`), one needs a bridge. The bridge must produce a ℂ-submodule domain from the ℝ-submodule domain, and show ℂ-homogeneity: S*S(ix) = (−i)(−i)... = i S*S x. The bridge is not in Mathlib or the project.
- Pros:
  - Reuses Mathlib adjoint/closure/graph machinery directly.
  - The closability of S₀ follows from `S₀† ` having dense domain (the project already does this in the linear case).
- Cons:
  - `letI` instance management and diamonds (ℝ-`NormedSpace` from `restrictScalars` vs `NormedSpace ℝ H` from `NormedSpace ℂ`).
  - Every ℂ-structure fact (domain is a ℂ-subspace, ℂ-homogeneity of Δ) must be re-proved.
  - The ℝ→ℂ bridge for Δ.
- Effort: medium (about 400-600 lines).

### (c) Option C: conjugate Hilbert space H̄
- No conjugate module or conjugate inner product space was found in Mathlib. Searches for `ConjugateSpace`, `Module.Conj`, and `ConjLinearMap` returned nothing.
- Available pieces:
  - `Complex.conjAe`, `Complex.conjLIE` (`M/Analysis/Complex/Basic.lean:205`), which are ℝ-linear isometries of ℂ.
  - `StarModule`, `starRingEnd`.
  - `RingHomInvPair`, `≃ₗᵢ⋆[𝕜]` notation for antilinear isometric equivalences (e.g. `ContinuousLinearMap.adjoint : (E →L E') ≃ₗᵢ⋆ ..`, `InnerProductSpace.toDual`).
  - `ContinuousLinearMap` and `LinearIsometryEquiv` over `σ` exist (`→SL[σ]`, `≃ₛₗᵢ[σ]`), so bounded antiunitaries (J) can be expressed.
- Defining H̄ requires a new type synonym with new `Module ℂ`, `Inner ℂ`, `NormedAddCommGroup` and `InnerProductSpace ℂ` instances (the defs are blocked by project policy until approved; they are design decisions).
- Pros: S : H →ₗ.[ℂ] H̄ is ℂ-linear, so the whole project `LinearPMap ℂ` theory applies to the pair (H, H̄).
- Cons:
  - The project's `Unbounded/Basic.lean` is stated for endomorphisms `H →ₗ.[ℂ] H`. The adjoint of S : H → H̄ is H̄ → H, which is Mathlib's general `F →ₗ.[𝕜] E`, but the project's lemmas are endomorphism-only.
  - S*S : H → H needs the identification H̄̄ = H, plus a new type and instances.
- Effort: medium-high.

### (d) Option P: graph-only
- The real subspace Γ(S) ⊆ H × H, with closability = `Γ ∩ ({0} × H) = 0` on the closure, and the adjoint via an orthogonal-complement formula on graphs of the form {(Sx, x)}.
- Pros: no instance trouble.
- Cons: re-derive everything (domain, injectivity, S^{-1}), and still has to produce the complex-linear Δ.
- Effort: high.

### (e) Option K (recommended, not in the task list): reference conjugation C
- Choose any antiunitary involution C : H → H (complex conjugation in a Hilbert basis). Replace S₀ by the ℂ-LINEAR operator S₀' := C∘S₀ (aΩ ↦ C(a*Ω)), a normal `H →ₗ.[ℂ] H`.
  - It is well defined since Ω is separating.
  - It is densely defined, and closable by `T†` having dense domain, using the project's `HasDenseDomain`, `IsClosable` and `adjoint_closure_eq_adjoint` (`Physicslib4/Spectral/Unbounded/Basic.lean:332,487`).
- Since C is isometric, antilinear, and an involution, (S₀')†S₀' = S₀*S₀. So Δ := (S')†S' falls out in the project's ℂ-linear framework with no ℝ or conjugate-space machinery.
- Cost: build C. This needs `HilbertBasis` plus coordinate conjugation on ℓ²: `HilbertBasis.repr`, `lp`, and `Complex.conjLIE` applied coordinatewise. A conjugation exists on any Hilbert space this way (Hilbert basis exists: `exists_hilbertBasis`). A Mathlib search found no ready-made antiunitary involution on a general H.
- The antiunitary J is recovered as J := C∘V with V a unitary from the (linear) polar decomposition of S'.
- The only antilinear fact needed at the end is: J = CV is antilinear, isometric, bijective and J² = 1. The last follows from S² = 1 on Dom(S) (S₀² = id on MΩ, then closure). It is a short argument.
- Effort: low-medium for C (~150 lines); everything else is linear theory.
- Risk: Δ is then defined via a non-canonical C. Canonical independence holds since S'†S' = S*S regardless of C, but must be proved if J, Δ are stated canonically. Also Tomita relations like JMJ = M' (J M J is the commutant) will use that C-dependence cancels (J = CV involves C, but J is intrinsic as the phase of S).

## 2. Polar decomposition

### (a) Existing polar decomposition
- None, for bounded or unbounded.
- Mathlib: `CFC.abs`/`CFC.sqrt` exist for C*-algebras (`M/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean:46`: `abs a := sqrt (star a * a)`) but no partial isometry or `polar` theory was found. Grep for `partialIsometry`, `IsPartialIsometry`, `polar` hit only convex-analysis/coordinate/LRAT files.
- Project: nothing (`Spectral/Forms.lean` `polarization` is sesquilinear polarization, unrelated).

### (b) von Neumann's theorem (T*T self-adjoint)
- Not in Mathlib or the project. `M/Analysis/InnerProductSpace/LinearPMap.lean` provides the ingredients:
  - `Submodule.adjoint` on graphs, `LinearPMap.adjoint_graph_eq_graph_adjoint` (line 292), `adjoint_isClosed` (line 332), `IsSelfAdjoint` via `Star` (line 229), `IsSelfAdjoint.isClosed`.
  - Missing: the graph-orthogonal decomposition H ⊕ H = Γ(T) ⊕ Γ'(T†), which is the key step.
- The project has `existsUnique_add_mem_orthogonal` (`Basic.lean:574`, `V` closed: ∃! p, p.1 ∈ V ∧ p.2 ∈ Vᗮ ∧ ψ = p.1+p.2`), `dense_iff_orthogonal_eq_bot` (595), `orthogonal_range_eq_ker_adjoint` (659), `adjoint_closure_eq_adjoint` (487), `eq_closure_of_isSelfAdjoint_of_le`, `existsUnique_isSelfAdjoint_extension`, `isClosed_range_subSmul`, `orthogonal_range_subSmul`, `adjoint_subSmul`.
- The proof route of von Neumann's theorem: (1+T†T) surjective, via Γ(T) ⊕ Γ'(T†) = H ⊕ H, then symmetric + range(A ± i) = H ⇒ self-adjoint. The project has criteria for symmetric operators (`existsUnique_isSelfAdjoint_extension`, `range_subSmul_*`).
- This is a new lemma to prove: roughly 200-300 lines.

### (c) √ of a positive self-adjoint operator
- `functionalCalculus (hA : IsSelfAdjoint A) (f : ℝ → ℂ) : H →ₗ.[ℂ] H := pmapIntegral (spectralMeasure hA) f` (`Spectral/Unbounded/FunctionalCalculus.lean:107`) takes arbitrary f, so f = fun x => ↑(Real.sqrt x) works definitionally.
- Domain: `functionalCalculus_domain : (functionalCalculus hA f).domain = integralDomain (spectralMeasure hA) f` (line 115).
- Norm identity: `norm_sq_pmapIntegral (hf : Measurable f) (ψ : integralDomain μ f)` (`Integral.lean:848`) and `inner_self_pmapIntegral` (815) give ‖f(A)ψ‖² = ∫|f|²dμ_ψ and ⟨ψ,f(A)ψ⟩ = ∫ f dμ_ψ.
  So ‖Δ^{1/2}ψ‖² = ∫ x dμ_ψ = ⟨ψ,Δψ⟩ for ψ ∈ Dom Δ follows by combining with `functionalCalculus_id`.
- Self-adjointness for real f: `isSelfAdjoint_pmapIntegral_of_real` (`Integral.lean:1219`) and `isSymmetric_pmapIntegral_of_real` (1090). `functionalCalculus_of_bddMeasurable` (line 144) handles bounded f.
- Missing:
  - A named `Real.sqrt`-calculus lemma.
  - f(A)g(A) ⊆ (fg)(A) with domain control, i.e. Δ^{1/2}Δ^{1/2} = Δ (a multiplicativity/composition theorem for the unbounded calculus; none found among `theorem .*(mul|comp|pow)` in FunctionalCalculus.lean or Integral.lean).
  - Positivity: `IsPositive` (`Basic.lean:236`) ⇒ spectrum in [0,∞), i.e. `spectralMeasure` concentrated on [0,∞). Not located; check `Spectral/Unbounded/Spectrum.lean` and `SpectralTheorem.lean`.
  - Domain facts "Dom(Δ) is a core for Δ^{1/2}" (needed to identify Dom Δ^{1/2} = Dom S).
  - A functional calculus for functions of the form x ↦ x^{it} (unitary group), for modular flow. Bounded f works via `functionalCalculus_of_bddMeasurable`; Stone's theorem (`Spectral/Stone/Theorem.lean:228 stone`) gives the converse direction.

### (d) Cheapest route to S = JΔ^{1/2} (use Option K: all in the ℂ-linear framework)
Let T := closure of C∘S₀ (linear, closed, densely defined, injective, dense range). Let A := T†T.
1. T closable, dense domain: from S₀'s adjoint having dense domain (Tomita's F₀ domain M'Ω, using Ω cyclic for M'). Project: `adjoint_closure_eq_adjoint`.
2. von Neumann: A = T†T is self-adjoint and positive, with Dom A a core for T. (New lemma, §2b.)
3. √A := functionalCalculus (hA) (fun x => ↑(Real.sqrt x)). Prove Dom √A = Dom T and ‖√A x‖ = ‖T x‖. Uses `norm_sq_pmapIntegral` plus the core property; closedness of both sides.
4. Define V on ran √A by √A x ↦ T x. It is a well-defined isometry, extended to the closure of ran √A. ker √A = ker T = 0 ⇒ ran √A dense (`orthogonal_range_eq_ker_adjoint`, as √A is self-adjoint). ran T is dense because T = C∘S and ran S ⊇ M'... (S is an involution on a dense set) ⇒ V is unitary.
5. J := C V. Then S = C T = C C V √A... check: T = V Δ^{1/2}, so S = C T = (C V) Δ^{1/2} = J Δ^{1/2}.
6. J antiunitary: C and V are. J² = 1: from S² = 1 on a core (S is injective with S⁻¹ = S), uniqueness of the polar decomposition (V√A injective ⇒ (JΔ^{1/2})(JΔ^{1/2}) = 1 gives J Δ^{1/2} J = Δ^{-1/2} and so J² = 1). That needs: S = S⁻¹ ⇒ F = S* and hence JΔJ = Δ⁻¹; uses `inverse_closure` (M/Topology/Algebra/Module/LinearPMap.lean:218) and the unbounded-operator inversion of the functional calculus (f(x)=1/x; need Δ injective).
7. Do NOT attempt uniqueness of polar decomposition in general; prove only what is needed above.

Lemma list, stage 2: von Neumann (T†T self-adjoint), Dom √A = Dom T with equal norms, V unitary extension, J² = 1 and JΔJ = Δ⁻¹, functional calculus composition for f(A)g(A) ⊆ (fg)(A) (or just the instance √A√A = A).

## 3. Other prerequisites
- Carlson's theorem: NOT in Mathlib (grep "Carlson" found nothing relevant).
- Phragmén–Lindelöf (`M/Analysis/Complex/PhragmenLindelof.lean`, namespace `PhragmenLindelof`):
  - `vertical_strip (hfd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b)) (hB : ∃ c < π/(b-a), ∃ B, f =O[comap (abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z ↦ expR (B * expR (c * |z.im|))) (hle_a : ∀ z, re z = a → ‖f z‖ ≤ C) (hle_b : ∀ z, re z = b → ‖f z‖ ≤ C) (hza : a ≤ re z) (hzb : re z ≤ b) : ‖f z‖ ≤ C` (line 275). Also `horizontal_strip` (113), `eq_zero_on_vertical_strip` (303), `eqOn_vertical_strip` (321).
  - `right_half_plane_of_bounded_on_real` (717), `right_half_plane_of_tendsto_zero_on_real` (646), `eq_zero_on_right_half_plane_of_superexponential_decay` (759), `eqOn_right_half_plane_of_superexponential_decay` (812).
  - Quadrants: `quadrant_I..IV`, `eq_zero_on_quadrant_*`, `eqOn_quadrant_*`.
  - The strip versions are the natural fit for KMS (strip 0 < Im z < β, `horizontal_strip`).
- Resolvents of unbounded self-adjoint operators (project): `IsResolvent T lam B` (`Spectral/Unbounded/Spectrum.lean:57`), `pmapResolventSet` (78), `IsCayleyTransform` (`Cayley.lean:227`), `exists_isCayleyTransform` (270), `integral_inv_sub_I_eq_resolvent` (932). Bounded: `Spectral/Spectrum.lean`/`Basic.lean` (`mem_resolventSet_iff_isUnit_sub_smul` etc.).
- Bicommutant / density: `Physicslib4/Operators/DensityTheorem.lean` has `exists_forall_norm_sub_lt_of_mem_bicommutant` (line 228, for a *-representation ρ), `apply_mem_closure_of_mem_bicommutant` (60), `starProjection_cyclic_mem_centralizer` (39), amplification `diagAmplification`, `ampDiag_mem_bicommutant`. This supplies von Neumann's density theorem.
- Mathlib `VonNeumannAlgebra H` (`M/Analysis/VonNeumannAlgebra/Basic.lean:67`): `centralizer_centralizer' : Set.centralizer (Set.centralizer carrier) = carrier`, `centralizer_centralizer` (line 118). The commutant is `Set.centralizer` (for sets of `H →L[ℂ] H`). The project's use is in `AQFT/HaagKastler/LocalVonNeumann.lean`, `StrongDensity.lean`, `GNS/Superselection.lean`, `GNS/Irreducibility.lean`.
- Separating vector: `Physicslib4/GNS/Separating.lean` (`separating_of_faithful`, `exists_gns_separating`) already names the Tomita starting point. There is no existing Tomita/modular/antiunitary code (grep of `Physicslib4/`).
- Stone's theorem exists (`Spectral/Stone/Theorem.lean:228 stone`), which gives Δ^{it} ↔ log Δ for the modular group.

## 4. Recommendation
Option K (reference conjugation C, S' = C∘S ℂ-linear), because:
- All analytic content (closure, adjoint, `IsSelfAdjoint`, `functionalCalculus`) is already in the project in the form `H →ₗ.[ℂ] H`. Options R/C/P need new bridges or new types (def/instance declarations are policy-blocked, so they need approval anyway).
- Δ = S'†S' is complex linear on the nose.
- The antilinearity is isolated in one object C. Fallback: Option R (the real adjoint = the antilinear adjoint, shown above) if one wants canonical statements with no C.

Stage 1 (antilinear closable operators and adjoints), minimal list:
1. Existence of an antiunitary involution C (Hilbert basis ⇒ coordinatewise conjugation); isometry, antilinearity, C² = 1, ⟨Cx,Cy⟩ = conj⟨x,y⟩.
2. S₀' : `H →ₗ.[ℂ] H` with domain MΩ, S₀'(aΩ) = C(a*Ω) (needs Ω separating for well-definedness; `GNS/Separating.lean`), plus the adjoint domain: M'Ω ⊆ Dom (S₀')† (a ∈ M, b ∈ M' ⇒ ⟨S₀'(aΩ), C... ⟩ identity).
3. Dense domains (Ω cyclic for M and M'; `M'` cyclicity from separating for M, via the bicommutant machinery).
4. `IsClosable S₀'` through `HasDenseDomain (S₀')†` and closure facts (`Basic.lean:332,370,487`).

Stage 2 (polar decomposition of S): von Neumann's theorem, √ identification, V unitary, J = CV, J² = 1, JΔJ = Δ⁻¹, then Tomita relations (σ_t, Δ^{it} via Stone's theorem plus bounded functional calculus).

## 5. Risks
- Von Neumann's theorem and f(A)g(A)-composition are genuinely missing. Together they are the largest cost (about 600+ lines).
- Domain equality Dom √Δ = Dom S (core argument) is delicate. There is no existing "core" API for the project's `functionalCalculus`; Mathlib has `closureHasCore`/`HasCore`.
- Non-canonical C: statements about J and Δ must be phrased independent of C, or fixed once and for all.
- The ℝ-viewing (Option R) has instance-diamond risk because `rclikeToReal` is deliberately not an instance.
- Carlson's theorem is absent; if needed (uniqueness of KMS analytic continuation) it must be added. Phragmén–Lindelöf strip versions may suffice.
- Definitions of C, the antiunitary J, S₀' are design decisions. The policy blocks agents from adding def/instance without approval.
- Present-tense docstrings and `**Restriction:**` markers: if stage 1 is stated only for separable H, mark it as a restriction. The functional calculus assumptions in the project (`TopologicalSpace.SeparableSpace H` in `Integral.lean:399`) point to the same.
