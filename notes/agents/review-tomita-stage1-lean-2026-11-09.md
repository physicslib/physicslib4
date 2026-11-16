# Review: Tomita–Takesaki stage-1 Lean statements (2026-11-09)

Scope: `Physicslib4/Operators/Modular/Antiunitary.lean` (6 nodes incl. `def:antiunitary-operator` →
`LinearIsometryEquiv`), `Physicslib4/Operators/Modular/Tomita.lean` (19 nodes). Blueprint
`blueprint/src/sections/sec10/tomita-takesaki.tex` §"The Tomita Operator". Decisions D1 (Option K),
D2a, D3 from `notes/agents/proposal-tomita-takesaki-2026-11-08.md`.

**Verdict: REVISE** (two blocking items; everything else is true and faithful).

## Checks that pass

- **Diagnostics.** Both files: only `declaration uses sorry` warnings (4 in Antiunitary, 12 in Tomita).
- **No sorry in definitions.** Every `sorry` is in a `theorem`; `referenceConjugation`, `IsVonNeumannSet`,
  `IsSeparatingVector`, `IsCyclicSeparatingVector`, `tomitaPreDomain`, `tomitaPre`,
  `linearizedTomitaPre`, `tomitaOperator` are sorry-free.
- **S₀′ via `Submodule.toLinearPMap`.** Mathlib's `Submodule.toLinearPMap (g)` takes *no* graph
  hypothesis: it is `open scoped Classical`, `toFun := if hg : (graph property) then toLinearPMapAux g hg
  else 0` (`Mathlib/LinearAlgebra/LinearPMap.lean` ~l.996). So the definition is sorry-free and total;
  when the submodule is not a graph the value is the zero map on the same domain. The graph property
  (aΩ = 0, a ∈ span M ⇒ C(a⋆Ω) = 0) holds under `hM` (span M = M, since a centralizer is a ℂ-submodule)
  and separation from `hΩ`. Every theorem mentioning `linearizedTomitaPre` carries `hM hΩ`, so no
  statement sees the junk branch. The linear map `a ↦ (aΩ, C(a⋆Ω))` is genuinely ℂ-linear
  (σ* ∘ σ* = id), and it typechecks.
- **Domain `(span ℂ M).map (apply Ω)`.** Under `IsVonNeumannSet M`, `M = M''` is a ℂ-submodule, so
  `span ℂ M = M` and the domain is exactly MΩ. For `F₀` (`Set.centralizer M`) it is MΩ' unconditionally.
- **`tomitaPre` (classical representative).** Value `star a Ω` for a chosen `a ∈ span M` with `aΩ = x`.
  Independent of the choice exactly when Ω separates span M; all statements about `tomitaPre` carry
  `hM hΩ`. Correct design for a sorry-free definition.
- **Adjoint relation.** With Mathlib's convention (conjugate-linear in the first slot), for x = aΩ,
  y = bΩ, b ∈ M': ⟪bΩ, a⋆Ω⟫ = ⟪abΩ, Ω⟫ = ⟪baΩ, Ω⟫ = ⟪aΩ, b⋆Ω⟫. True as stated, faithful.
- **`linearizedTomitaPre_adjoint_extends`.** ⟪Cy, S₀′x⟫ = conj⟪y, S₀x⟫ = ⟪S₀x, y⟫ = ⟪F₀y, x⟫, which is
  Mathlib's adjoint relation; needs no `hC`. Mathlib's `adjoint` is junk off dense domains, but the domain
  is dense under `hΩ`. True.
- **`isClosable_of_dense_adjoint`.** Mathlib has no such lemma (no `IsClosable`/adjoint lemma in
  `Analysis/InnerProductSpace/LinearPMap.lean`); not ALREADY_IN_MATHLIB. Hypotheses minimal.
- **`IsVonNeumannSet`, `IsCyclicSeparatingVector`, `IsSeparatingVector`.** Faithful to their nodes and to
  D3. (Mathlib's `VonNeumannAlgebra H` exists with the same `Set.centralizer` convention; D3 chose the
  set form for consistency with `localVonNeumann`; not reopened.)
- **`tomitaOperator := C ∘ S′.closure`** on `S′.closure.domain`; faithful to `def:tomita-operator`.
  `hC` is genuinely needed in `tomitaOperator_graph_eq_closure`, `_graph_swap`, `_involution` with this
  definition (otherwise Γ(S) = (id × C²)(closure Γ(S₀))).
- Antiunitary nodes: all true and faithful; `antiunitary_composition` is proved by `trans`.
- Signatures: at most 5 binder groups; docstrings present tense, each ends `Blueprint: <label>`.

## Blocking

1. **False module docstring (Tomita.lean, l.23–24).** "Mathlib's `LinearPMap` is linear only" is false:
   `LinearPMap σ E F` is semilinear, with notation `E →ₛₗ.[σ] F` (`LinearPMap.lean` l.40–48), and
   `map_smulₛₗ`, `ext`, `≤`, `eqLocus`, `mkSpanSingleton` are all semilinear. What is linear-only is
   `graph`, `Submodule.toLinearPMap`, `closure`, `IsClosable`, `adjoint`. Fix: rewrite the bullet to say
   precisely that (this is why Option K is still needed).

2. **Missing bridge lemma between S₀ and S₀′ (scope-wide).** `tomitaPre` and `linearizedTomitaPre` are
   two independent definitions; nothing states `Dom S₀′ = tomitaPreDomain M Ω` (the docstring of
   `linearizedTomitaPre` claims it; it is `Submodule.map_comp`, not `rfl`), nor
   `S₀′ x = C (S₀ x)`, nor `S₀(aΩ) = a⋆Ω` for `a ∈ M`. The proofs of `lmm:linearized-adjoint-extends`
   and `lmm:tomita-operator-independent-of-c` both need exactly this, and it is the only check that
   `linearizedTomitaPre` *is* the S₀′ of its node (rather than the zero-map junk branch).
   Fix: BLUEPRINT: add a lemma node, e.g. `lmm:tomita-pre-operators-apply`
   (uses `lmm:tomita-pre-operators-well-defined`, `lmm:commutant-von-neumann-algebra`): under hM, hΩ,
   (i) for a ∈ M, aΩ ∈ Dom S₀ and S₀(aΩ) = a⋆Ω (likewise F₀ on M');
   (ii) Dom S₀′ = Dom S₀ and S₀′x = C(S₀x).
   Lean shape: `tomitaPre_apply (hM) (hΩ) {a} (ha : a ∈ M) : tomitaPre M Ω ⟨a Ω, mem⟩ = star a Ω`
   and `linearizedTomitaPre_domain : (linearizedTomitaPre M Ω C).domain = tomitaPreDomain M Ω`
   (no hypotheses) plus `linearizedTomitaPre_apply (hM) (hΩ) (x) : linearizedTomitaPre M Ω C ⟨x, _⟩ =
   C (tomitaPre M Ω x)`. The proof of (i) also needs `span ℂ M = M` under `hM` (a centralizer is a
   submodule); state that as a helper or fold it into (i).

## Optional

3. **Semilinear representation for S.** Recommend `tomitaOperator M Ω C : H →ₛₗ.[starRingEnd ℂ] H :=
   { domain := S′.domain, toFun := C.toLinearEquiv.toLinearMap ∘ₛₗ S′.toFun }` (S′ := closure). Sorry-free,
   antilinearity built in, gets `ext`, `≤`, `map_smulₛₗ`, and the same coercion `S x` on `S.domain`, so the
   current statements port with `S.domain` in place of `S′.closure.domain`. For `tomitaPre` keep the
   C-free function: a semilinear `LinearPMap` from a classical representative needs the
   well-definedness proof inside the definition (hypotheses or sorry), which is worse; the only
   C-free semilinear alternative is `C.symm ∘ S₀′`, which reintroduces C into S₀. Gain for stage 2 is
   modest: Δ = S′†S′ and the polar decomposition of S′ live on the linear S′ either way (Option K
   stands); the gain is cleaner statements of J-relations (`S = J Δ^{1/2}`) and antilinearity of S
   for free.
4. **Drop `hC` where it is not needed.** `linearizedTomita_closure_properties` is true for every
   antiunitary C (S′ = (id × C)-image of closure Γ(S₀), Φ a homeomorphism); `hC` is there only for the
   intended proof route. Alternatively define `tomitaOperator := C.symm ∘ S′`; then
   `_graph_eq_closure`, `_graph_swap`, `_involution` hold without `hC` and agree with `C ∘ S′` when C is
   involutive. Either is a design choice; current statements are not wrong (blueprint assumes C a
   reference conjugation).
5. **State antilinearity of S₀.** `def:tomita-pre-operators` asserts S₀, F₀ are antilinear; no Lean
   statement records it (the docstring of `tomitaPre` asserts it). Either add it to the bridge lemma or
   note it is recovered from (ii) + linearity of S₀′.
6. **Redundant conjuncts** (faithful to nodes, harmless): `Function.Injective` and dense range in
   `tomitaOperator_involution` follow from the involution conjunct and dense domain;
   `isVonNeumannSet_centralizer`'s second conjunct is `hM.2`.
7. Blueprint `def:antiunitary-operator` says "bijectivity is not yet known": "yet" is history-flavoured;
   the Lean docstring's "is not known" is better.

## Stage-2 usability

Supported: S′ = `(linearizedTomitaPre M Ω C).closure : H →ₗ.[ℂ] H` feeds `def:adjoint-product-operator`
(S′†S′) and the linear polar decomposition directly; C-independence of Δ = S†S follows from
`tomitaOperator_graph_eq_closure` (Γ(S) C-free) plus S′†S′ = S⋆S. The bridge lemma (item 2) is the
missing API piece.
