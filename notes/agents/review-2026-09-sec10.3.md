# Review: Blueprint §10.3 "Unbounded Spectral Theorems" vs. Lean

Date: 2026-09-25
Reviewer: audit subagent (read-only)
Status: session interrupted by a network outage partway through; scope was
triaged toward the items named in the task and toward integrity/link checks
that are cheap to verify exhaustively. See "Coverage" under Method.

## Scope

- Blueprint: `blueprint/src/sections/sec10/unbounded-spectral-theorems.tex`
  (3170 lines / ~120 labelled items, all marked `\leanok`).
- Lean: `Physicslib4/Spectral/Unbounded/{Basic,Spectrum,DirectSum,Integral,
  Normal,AbstractCalculus,Cayley}.lean` (5644 lines total).
- No `.lean`/`.tex` file was modified. No fuse/lean-kit MCP tools
  (`lean_hover_info`, `lean_verify`, `lean_minimal_hypotheses`) were available
  as callable tools in this session; all checks were done by reading source
  and blueprint text and by `grep`/`git`/`lean_guard.py`.

## Method

- Extracted all 188 distinct identifiers named in `\lean{...}` macros in the
  section (118 `Physicslib4.*`, 70 root/Mathlib names) and checked each
  resolves to a real declaration: by exact grep against the 7 audited files
  for the `Physicslib4.*` names, and against `.lake/packages/mathlib/Mathlib`
  (lenient, namespace-aware grep) for the rest.
- Grepped the 7 files for `sorry`, `admit`, `native_decide`,
  `debug.skipKernelTC`, `implemented_by`, `nolint`, and the restriction
  marker `Restriction:`.
- Read the blueprint prose and proof for the items named in the task's
  "known context" (integral's `Measurable` guard, `cayleyPVM`/`mapPVM`
  measurability guards, `lmm:closed-subspace-is-hilbert`'s
  `[SeparableSpace H]`, the `hall-9.26`/`hall-9.26-internal` pair, the
  `hall-10.23`/`hall-10.26` gap, `inclSpectrum`), and read the corresponding
  Lean declarations, to classify each against the statement-audit rubric.
- Ran `python3 ~/.claude/lean-kit/lean_guard.py check --base HEAD` and read
  `.git/lean-kit/verify-receipt.json` / `.git/lean-kit/approvals.json`
  against `git log` to assess integrity/verify staleness.

### Coverage

Depth-read and cross-checked against Lean: `def:hall-3.1`, `def:hall-9.1`
through `def:hall-9.7`, `prpstn:hall-9.4`, `prpstn:hall-9.8`,
`prpstn:hall-9.10`, `def:product-hilbert-space`,
`prpstn:closure-linearity-and-sequential-description`,
`lmm:closure-of-symmetric-is-symmetric`,
`def:closed-linear-map-on-a-subspace`, `prpstn:hall-9.26` and
`prpstn:hall-9.26-internal`, `prpstn:hall-10.1`, `prpstn:hall-10.2`,
`lmm:closed-subspace-is-hilbert`, `lmm:hall-10.26`, `thrm:hall-10.23`,
`inclSpectrum`. Link existence was checked for every labelled item in the
file. Not depth-read this session (link existence only, statement content
unchecked): the Cayley-transform block (`lmm:cayley-map`,
`lmm:cayley-omits-one`, `def:hall-7.14`, `prpstn:hall-10.3`/`10.29`/`10.20`,
`thrm:hall-10.4`, `thrm:hall-10.28`), the abstract-calculus/DirectSum
external-form details beyond `hall-9.26`, and the projection-valued-measure
integral lemmas beyond `hall-10.1`/`10.2`. These are flagged as open follow-up
rather than reported as findings.

## Findings

### High

**H1. Verify receipt is stale relative to the audited material.**
- Location: `.git/lean-kit/verify-receipt.json` (time `2026-09-18T14:08:28Z`,
  commands `lake build`, `lake lint`, both `exit: 0`) vs. `git log`.
- Problem: `git log --since=2026-09-18T14:08:28+00:00` lists 11 later commits,
  including exactly the commits that finished the material under audit:
  `431a6fe` (remaining unbounded-operator results), `5b224c9`, `0773f3d`,
  `8b8eb0b`, `a40b591`, `0c684be`, `9aae0e6`, `7e54dd1` ("Prove the Cayley
  transform and unbounded spectral theorem (section 10.3)"), `453679b`
  ("Prove lmm:closed-subspace-is-hilbert under a separable H"), `26ca993`
  ("Fix lake lint and blueprint declaration-check failures"), `effd1f5`
  ("Replace Laurent's theorem by Gelfand's formula..."). All of these are
  dated 2026-09-24, six days after the receipt. There is no later receipt.
  So the recorded verify does not cover the current state of
  `Spectral/Unbounded/*`, including a commit whose stated purpose was fixing
  a lint failure — i.e. the last *known-passing* lint run predates the fix
  for a lint failure.
- Suggested fix: re-run `lake build && lake lint` (and
  `leanblueprint checkdecls`) and record a fresh receipt before treating this
  section as verified. I did not run the build myself in this session
  (time/network constrained); this is reported from the receipt/git-log
  evidence only.

**H2. Blueprint-math gap: `lmm:hall-10.26`'s constant is not stated uniform
in λ, but `thrm:hall-10.23`'s proof needs it to be.**
- Location: blueprint lines 2108-2113 (`lmm:hall-10.26` statement) and
  2231-2232 (`thrm:hall-10.23` proof).
- Problem: `lmm:hall-10.26` states: "there is a constant $C$ (depending on
  $p$, $A$, **and $\lambda$**, but not on $\varepsilon$ or $\psi$)...". The
  proof of `thrm:hall-10.23` then asserts (line 2232): "there is a single
  constant $C$, depending only on $p$ and $A$, valid for all $\lambda$ with
  $|\lambda| \le \|A\|$" — i.e. uniform over an infinite family of $\lambda$'s
  — and justifies this only by an aside ("Inspecting the recursion there, C
  is built from ..., and is non-decreasing in $|\lambda|$"), not by a cited
  proposition. This is exactly the gap noted in the task's known context: the
  blueprint's own chain of reasoning for 10.23 (via the almost-eigenvector
  route) needs a strengthening of 10.26 that 10.26 does not state and that
  is not separately proved as a citable fact.
- Suggested fix (blueprint, propose only): either restate `lmm:hall-10.26`
  with the uniformity built in (constant depending on $p$, $A$, and a bound
  $R$ on $|\lambda|$, valid for all $|\lambda|\le R$), or add a short
  corollary capturing the uniformity claim, with a `\uses` edge from
  `thrm:hall-10.23`.

### Medium

**M1. Lean's proof of `thrm:hall-10.23` takes a different, undocumented
route that happens to sidestep H2 — but the deviation isn't recorded
anywhere.**
- Location: `Physicslib4/Spectral/Unbounded/Normal.lean:806-830`
  (`mvApply_eq_cfc`, `spectrum_mvApply`).
- Problem: `spectrum_mvApply` (tagged "Blueprint reference: `thrm:hall-10.23`")
  is proved by rewriting `mvApply A p` as Mathlib's `cfc (mvEvalConj p) A`
  and invoking `cfc_map_spectrum`. It never calls
  `exists_const_isAlmostEigenvector_mvApply` (the Lean name for
  `lmm:hall-10.26`) at all, so the gap in H2 does not affect Lean's soundness
  — the theorem is correctly proved. But the blueprint text still presents
  the almost-eigenvector argument as *the* proof of 10.23, and nothing in
  the `.tex` or in the Lean docstring says the formalization uses a shorter
  Mathlib-CFC route instead. A reader relying on the blueprint to understand
  what was formalized would be misled about the proof actually checked by
  Lean (matching the task's note that "10.23 via Mathlib CFC" is one of
  several such deviations, alongside 10.29, 10.3, 9.26).
- Suggested fix: add a remark in the blueprint after `thrm:hall-10.23` (or in
  the Lean docstring) noting the formalized proof uses Mathlib's continuous
  functional calculus rather than the almost-eigenvector argument above, so
  H2 is moot for the Lean development. I did not have time this session to
  check the other three named deviations (10.29, 10.3, 9.26's *external*
  form) against blueprint prose in the same depth; recommend a follow-up
  pass on those three specifically. (Follow-up below now covers 10.29 and
  10.3: neither turns out to deviate from its blueprint proof route in a way
  that matters to the statement audit — see "Follow-up" section.)

**M2. `CompleteSpace (K n)` instance hypothesis on the internal-direct-sum
lemmas, marked `Restriction:` but argued to cost nothing — marker used
non-standardly.**
- Location: `Physicslib4/Spectral/Unbounded/DirectSum.lean:535-632`, five
  theorems (`isEssentiallySelfAdjoint_of_isInternalDirectSumOperator`,
  `domain_closure_eq_internalDomain`, `domain_adjoint_eq_internalDomain`,
  `hasSum_closure_apply_of_isInternalDirectSumOperator`,
  `hasSum_adjoint_apply_of_isInternalDirectSumOperator`).
- Blueprint (`prpstn:hall-9.26-internal`, lines 1015-1028): hypothesizes only
  that `{K_n}` is "an internal orthogonal decomposition of H into separable
  **closed** subspaces" — completeness of each `K_n` is a consequence (closed
  subset of a complete space), not a hypothesis.
- Lean: each of the five theorems takes `[∀ n, CompleteSpace (K n)]` as an
  explicit instance argument. Every docstring is honest about this, saying
  verbatim: "the instance `[∀ n, CompleteSpace (K n)]` ... is assumed rather
  than derived from `hK.isClosed` via `IsClosed.completeSpace_coe`; being
  `Prop`-valued it costs no generality, a caller supplying it with `haveI`."
- Problem: this is a real hypothesis in the Lean signature beyond what the
  blueprint states, even though it is derivable and therefore not a genuine
  restriction of the class of applicable `(K, A, T)`. Using the same
  `**Restriction:**` marker as a genuine scope-narrowing restriction (e.g.
  the bounded-generators note in `VacuumState.lean`) dilutes what the marker
  means for an auditor scanning for real restrictions — this one needs no
  "waiting on X" resolution, it's a convenience the theorem could remove
  itself.
- Suggested fix (propose only): either derive
  `haveI : ∀ n, CompleteSpace (K n) := fun n => (hK.isClosed n).completeSpace_coe`
  inside each theorem so no caller-visible hypothesis is added, or reword the
  docstring to say explicitly this is *not* a mathematical restriction (so it
  stops matching the auditor's `Restriction:` grep as if it were one).

### Low

**L1. `inclSpectrum`/`continuous_inclSpectrum` duplicate Mathlib.**
- Location: `Physicslib4/Spectral/Unbounded/AbstractCalculus.lean:727-737`.
- `inclSpectrum hsub := fun lam => ⟨(lam : ℂ), hsub lam.2⟩` is definitionally
  `Set.inclusion hsub`, and `continuous_inclSpectrum` restates Mathlib's
  `continuous_inclusion` (both confirmed present:
  `Mathlib/Topology/ContinuousMap/Basic.lean:413-416` even bundles
  `Set.inclusion` as a `ContinuousMap` already). Purely cosmetic; no
  soundness or scope issue.
- Suggested fix: replace with `Set.inclusion hsub` /
  `continuous_inclusion hsub` (propose only; a `def`/no new declaration
  change like this needs orchestrator sign-off per policy's
  `new_declarations` table treating `def` as `block` for new work).

**L2. Working-tree protected-file changes and no approvals on file (outside
sec10.3 content, noted for completeness).**
- `lean_guard.py check --base HEAD` reports `.claude/CLAUDE.md` and
  `.claude/lean-policy.json` as protected-file changes in the working tree
  (both appear as untracked in the session's initial git status).
  `.git/lean-kit/approvals.json` does not exist, so no approvals are in
  effect. Neither bears on the Lean/blueprint content of §10.3; not
  investigated further.

## Blueprint-math issues

- See H2 above (the substantive one found this session): `lmm:hall-10.26`
  vs. `thrm:hall-10.23`'s proof-time need for uniformity in λ.
- No other blueprint-internal inconsistency was found in the material that
  was depth-read (adjoint/closure/self-adjointness chain, `hall-9.26`
  external/internal pair, `hall-10.1`/`10.2` integral construction,
  `closed-subspace-is-hilbert`). The degenerate-summand case in `hall-9.26`
  (line 958, `H_j = {0}`) is explicitly and correctly handled as a separate
  case rather than silently assumed away — checked and is not a vacuity
  issue.
- The follow-up pass below found no additional blueprint-internal
  inconsistency in `thrm:hall-10.28`, `prpstn:hall-10.29`, `prpstn:hall-10.3`,
  `thrm:hall-10.4`, `thrm:hall-10.20`, or `lmm:borel-bijection-transports-pvm`.

## Items checked and cleared (verified, not just read)

- **Junk value in `integralApply`** (Integral.lean:667-675): returns `0`
  when `f` is not measurable or no representing vector exists. Confirmed
  harmless: `prpstn:hall-10.1`'s blueprint statement itself requires `f`
  measurable, and every downstream theorem using `pmapIntegral`/
  `integralApply` (`integralApply_eq`, `pmapIntegral_domain`, etc.) carries
  an explicit `Measurable f` hypothesis; the junk branch never appears in a
  proved theorem's hypotheses-satisfied case.
- **`lmm:closed-subspace-is-hilbert`'s `[SeparableSpace H]`**
  (Integral.lean:363-367): confirmed the ambient `variable {H ...}` in
  `Basic.lean:60` and `Integral.lean:58` does *not* include
  `[SeparableSpace H]` (Lean generalizes the whole development beyond the
  blueprint's standing "H is separable" convention), so this lemma
  re-introduces separability explicitly exactly where the conclusion needs
  it. This matches blueprint intent; not a mismatch.
- **All 118 `Physicslib4.*` `\lean{}` links**: resolve to real declarations
  in the 7 audited files (checked via anchored grep for
  `theorem|lemma|def|abbrev|structure|instance|class <name>`).
- **All 70 non-`Physicslib4` `\lean{}` links**: resolve in
  `.lake/packages/mathlib/Mathlib` (13 needed a second, namespace-aware pass
  after a naive grep first missed them — e.g. `Filter.Tendsto.cauchySeq` and
  `IsCompact.tendsto_subseq` are real Mathlib declarations reached via dot
  notation from `namespace Filter`/`IsCompact`, not literal top-level names).
- **No `sorry`/`admit`/`native_decide`/`debug.skipKernelTC`/
  `implemented_by`/`nolint`** anywhere in the 7 files (grep, exhaustive).
- **`Restriction:` markers**: only the 5 in DirectSum.lean (M2), all
  identical text; none elsewhere in the 7 files.

## Not verified (judged by reading only, or not reached)

- Actually running `lake build`/`lake lint` myself to get a fresh pass/fail
  (H1 is reported from receipt + git log evidence, not from a fresh run).
- `def:hall-7.14` (spectral subspace) and `IsResolvent`/`def:hall-9.16`
  themselves were re-used, not re-audited, in the follow-up below (they were
  in scope of an assumed-prior pass over `Spectrum.lean`); only their
  signatures were `#print`ed to confirm consistency with how the Cayley
  block cites them.

## Follow-up: statement audit of 10.28, 10.29, 10.3, 10.4, 10.20, mapPVM

This section closes out the six items left as open follow-up above. All six
were depth-read against the blueprint's statement text and checked against
Lean via `Read` plus `lake env lean` `#check`/`#print` (the fuse/lean-kit MCP
tools were still not available as callable tools this session either).

### thrm:hall-10.28 (Cayley transform existence) — **match**

- Blueprint (lines 2772-2789): fixes `A` self-adjoint, *defines*
  `U ψ ≡ (A+i1)(A-i1)⁻¹ψ`, and states four properties of this specific `U`
  (unitary; `U-1` injective; `Range(U-1) = Dom(A)` with the stated inverse
  formula; `U-1 = 2i(A-i1)⁻¹`).
- Lean (`Cayley.lean:191-235`, tool-verified via `#print`/`#check`):
  `structure IsCayleyTransform (A) (B U) : Prop` bundles `IsResolvent A i B`
  (i.e. `B = (A-i1)⁻¹` as a two-sided bounded inverse, `#print`ed and
  confirmed to match `def:hall-9.16`'s resolvent) with `U ψ = A⟨Bψ,_⟩ + i•Bψ`,
  and `exists_isCayleyTransform (hA : IsSelfAdjoint A) : ∃ B U,
  IsCayleyTransform A B U ∧ U ∈ unitary _ ∧ Injective (U-1) ∧
  range(U-1) = Dom(A) ∧ (∀ χ h, A⟨(U-1)χ,h⟩ = i•(U+1)χ) ∧ U-1 = 2i•B`.
- The one stylistic difference: the blueprint *defines* `U` by a formula and
  then proves properties of that `U`; Lean states existence of a `(B,U)`
  pair satisfying a defining predicate. This is not a narrowing — Lean
  separately proves `IsCayleyTransform.unitary_eq` (`Cayley.lean:553-557`,
  using `existsUnique_isResolvent` for `B`'s uniqueness), so the `(B,U)`
  produced is unique given `A`, exactly as if it had been introduced by a
  `def`. Point 3's `∀ ψ ∈ Range(U-1), Aψ = i(U+1)(U-1)⁻¹ψ` becomes
  `∀ χ h, A⟨(U-1)χ,h⟩ = i(U+1)χ` (quantifying over the pre-image `χ` rather
  than `ψ = (U-1)χ` and its inverse) — a routine reindexing, not a change of
  content. All four numbered points are present with matching hypotheses
  (`IsSelfAdjoint A`, no `Nontrivial H` needed, matching the blueprint, which
  also states this theorem without `H ≠ {0}`).

### prpstn:hall-10.29 (`A = ∫ D dμ^U`) — **match**

- Blueprint (lines 2962-2970): for self-adjoint `A` with `H ≠ {0}`, Cayley
  transform `U`, and `D` the inverse Cayley map, `A = ∫_{σ(U)} D dμ^U`, with
  equality of domains.
- Lean (`Cayley.lean:683-703`, tool-verified `#check`):
  `pmapIntegral_cayleyInv_eq [Nontrivial H] {A} (hA : IsSelfAdjoint A) {B U}
  (hU : IsCayleyTransform A B U) {μU} (hμU : μU.integral (fun u => u) = U) :
  pmapIntegral μU (fun u => (cayleyInv u : ℂ)) = A`. `pmapIntegral` returns a
  `LinearPMap`, so this single equality already asserts domain equality
  (`LinearPMap` equality is defined as equality of domain and of the map on
  it) — matching "with equality of domains" without needing a second clause.
  `[Nontrivial H]` matches the blueprint's `H ≠ {0}` hypothesis exactly (and
  the blueprint gives the reason: `μ^U` is supplied by `thrm:hall-10.20`,
  which assumes it — matching Lean's dependency on
  `existsUnique_spectralMeasure_normal` inside `existsUnique_spectralMeasure_unbounded`).

### prpstn:hall-10.3 (integral of a real function is self-adjoint) — **match**

- Blueprint (lines 1705-1710): `f` real-valued measurable on `X` ⟹
  `∫_X f dμ` is self-adjoint on `W_f`.
- Lean (`Integral.lean:1132-1140`, tool-verified `#check`):
  `isSelfAdjoint_pmapIntegral_of_real {f : X → ℂ} (hf : Measurable f)
  (hreal : ∀ x, (f x).im = 0) : IsSelfAdjoint (pmapIntegral μ f)`. `f : X → ℂ`
  with `∀ x, (f x).im = 0` is exactly "real-valued" represented as a
  complex-valued function with vanishing imaginary part (the encoding used
  uniformly for real-valued integrands throughout this file, e.g. in
  `prpstn:hall-10.29`'s use of `cayleyInv` composed with `Complex.ofReal`);
  `IsSelfAdjoint (pmapIntegral μ f)` is self-adjointness of the `LinearPMap`
  with domain `W_f` (`integralDomain μ f`), matching "self-adjoint on `W_f`"
  directly (`IsSelfAdjoint` for a `LinearPMap` already means `T = T†` as
  partial maps, domain included). No extra hypotheses beyond `Measurable f`
  and real-valuedness.

### thrm:hall-10.4 (spectral theorem for unbounded self-adjoint operators) — **match**

- Blueprint (lines 3077-3084): `A` unbounded self-adjoint on `H` (no stated
  `H ≠ {0}` here — the degenerate case is handled inside the proof) ⟹
  unique PVM `μ^A` on Borel(`ℝ`) with `∫_ℝ λ dμ^A = A`; moreover `μ^A` is
  concentrated on `σ(A)`.
- Lean, in two declarations that jointly cover the statement (tool-verified
  `#check`, `Cayley.lean:933-978`):
  - `existsUnique_spectralMeasure_unbounded {A} (hA : IsSelfAdjoint A) :
    ∃! μ, pmapIntegral μ (fun x => (x:ℂ)) = A` — the existence/uniqueness
    half, including the `H = {0}` degenerate case handled explicitly inside
    the proof (`rcases subsingleton_or_nontrivial H`), matching the
    blueprint's own explicit "degenerate case" paragraph in the proof
    (lines 3089).
  - `spectralMeasure_concentrated {A} (hA) {μ} (hμ : pmapIntegral μ id = A) :
    μ {x | x ∉ σ(A)} = 0 ∧ ∀ E, MeasurableSet E → μ E = μ (E ∩ σ(A))` —
    matches the "concentrated on the spectrum" clause verbatim, including
    the blueprint's own restated "equivalently" form
    (`μ^A(E) = μ^A(E ∩ σ(A))` for every Borel `E`).
  The blueprint's closing remark that restricting `μ^A` to `σ(A)` "therefore
  gives" a PVM there with `∫_{σ(A)} λ dμ^A = A` is explanatory (it follows
  from `spectralMeasure_concentrated` together with
  `lmm:borel-bijection-transports-pvm` Part 1, i.e. `restrictPVM`, both
  already in the development) rather than a separate claim needing its own
  `\lean` citation, and the tex's own `\lean` tag list for this theorem does
  not include a third identifier for it.

### thrm:hall-10.20 (bounded normal operators, incl. ambient/compact-`Y` form) — **match**

- Blueprint (lines 2647-2660): `A ∈ B(H)` normal, `H ≠ {0}` ⟹ unique PVM
  `μ^A` on Borel(`σ(A)`) with `∫_{σ(A)} λ dμ^A = A`; ambient form: for
  compact `X ⊇ σ(A)` and PVM `ν` on `X` with `∫_X λ dν = A`,
  `ν(E) = μ^A(E ∩ σ(A))` for every Borel `E ⊂ X`.
- Lean (`AbstractCalculus.lean:863-895`, tool-verified `#check`):
  - `existsUnique_spectralMeasure_normal {A} (hA : IsStarNormal A) :
    ∃! μ, μ.integral (fun lam => lam) = A` — the plain form, over
    `spectrum ℂ A` directly.
  - `eq_of_integral_id_eq_ambient {A} (hA : IsStarNormal A) {Y : Set ℂ}
    (hY : IsCompact Y) (hsub : σ(A) ⊆ Y) {μA} (hμA) {ν} (hν) {E}
    (hE : MeasurableSet E) : ν E = μA (inclSpectrum hsub ⁻¹' E)` — the
    ambient form, matching the blueprint's `ν(E) = μ^A(E∩σ(A))` (the
    preimage of `E` under the inclusion `σ(A) ↪ Y` is exactly `E ∩ σ(A)`
    read back in `σ(A)`'s coordinates).
  - One notable but *intentional* hypothesis difference:
    `existsUnique_spectralMeasure_normal` carries **no** `Nontrivial H`
    hypothesis, unlike the blueprint's stated `H ≠ {0}`. This is not a
    mismatch: the blueprint's own `conv:nonzero-hilbert-space`
    (`spectral-theorems.tex:58-64`) states `H ≠ {0}` as a section-wide
    *convention*, adopted purely for fidelity to Hall's text, and explicitly
    says: "the Lean formalization records it as a `Nontrivial H` hypothesis
    on just those declarations that actually depend on it ... rather than as
    a global assumption." `existsUnique_spectralMeasure_normal`'s proof
    (via `abstractPVM`/Riesz representation) does not need non-emptiness of
    `σ(A)` and so correctly omits the hypothesis, exactly per that
    documented policy; this was tool-verified by `#check`ing the signature
    and reading the proof (`AbstractCalculus.lean:863-879`), which never
    invokes non-emptiness of the spectrum.

### lmm:borel-bijection-transports-pvm (`restrictPVM`, `mapPVM`, `assoc_mapPVM`, `mapPVM_apply`) — **match**

- Blueprint (lines 2901-2914): Part 1 (Restriction) — `μ` a PVM on `Ω(Y)`,
  `Y₀ ∈ Ω(Y)` with `μ(Y\Y₀) = 0` ⟹ `Ω(Y₀)` is a σ-algebra on `Y₀` and `μ`
  restricted to it is a PVM on `Y₀`. Part 2 (Transport) — `T : Y → Z` a
  bijection with `T` and `T⁻¹` both measurable, `μ` a PVM on `Ω(Y)` ⟹
  `ν(F) := μ(T⁻¹F)` is a PVM on `Ω(Z)`, with `ν_ψ = T_*μ_ψ`.
- Lean (`Cayley.lean:405-483`, tool-verified `#check`):
  - `restrictPVM (μ) {Y₀} (hY₀ : MeasurableSet Y₀) (hmass : μ Y₀ᶜ = 0) :
    ProjectionValuedMeasure Y₀ H` — `Y₀ᶜ` here is the ordinary set
    complement in `Set Y`, i.e. `Y \ Y₀`, matching `μ(Y\Y₀)=0` exactly. The
    returned structure's fields were read directly (not just the type): its
    `toFun E := μ (Subtype.val '' E)` and proof obligations reconstruct
    Parts 1–4 of the PVM definition from `μ`'s, matching the blueprint proof
    step for step (e.g. `univ'` uses the disjoint decomposition
    `Y = Y₀ ⊔ (Y\Y₀)` exactly as in the blueprint's proof of Part 1).
  - `mapPVM (μ) (T) (hT : Measurable T) (hbij : Bijective T)
    (hinv : Measurable (Equiv.ofBijective T hbij).symm) :
    ProjectionValuedMeasure Z H` — requires precisely "`T` measurable, `T`
    bijective, and the inverse measurable", matching Part 2's hypotheses
    with no relaxation. Read the body: the `hinv` binder (underscore-named
    `_hinv` in the source but used) is genuinely used in `notMeasurable'` to
    rule out `T⁻¹' F` being measurable for non-measurable `F` — not a dead
    hypothesis.
  - `mapPVM_apply` and `assoc_mapPVM` restate `ν(F) = μ(T⁻¹F)` and
    `ν_ψ = T_*μ_ψ` respectively, matching Part 2's two conclusions verbatim
    (`assoc_mapPVM`'s statement `(mapPVM μ T hT hbij hinv).assoc ψ =
    Measure.map T (μ.assoc ψ)` is literally `ν_ψ = T_*μ_ψ`).
  - The blueprint's closing remark (line 2943) that bijectivity of `T` is
    only used for `ν(Z) = μ(Y)` in property 2, and that measurability of
    `T⁻¹` is not needed for Part 2 itself but only for later re-transport,
    is consistent with `mapPVM`'s signature carrying `hinv` as a hypothesis
    that is *not* used to derive any of the PVM axioms for `ν` (checked: it
    is used only in `notMeasurable'`, which is precisely the axiom that
    needs `T⁻¹` to behave like an actual inverse on measurable sets, not a
    substantive extra use).

### Definitions checked for junk values (as requested)

- **`IsCayleyTransform`**: no junk value risk — it is a `Prop`-valued
  structure (not a partial function with a fallback branch); soundness
  reduces to `IsResolvent`, `#print`ed (`Spectrum.lean:45`) and confirmed to
  require `B` to be a genuine two-sided inverse of `A - i1` on `Dom(A)`
  (`mem_domain`, `rightInverse`, `leftInverse` fields), matching
  `def:hall-9.16`.
- **`cayleyPVM`** (`Cayley.lean:713-737`): the `MeasurableSet E` guard
  (`if MeasurableSet E then ... else 0`) is the same convention used
  throughout for every `ProjectionValuedMeasure` (the structure's
  `notMeasurable'` field requires exactly this), not a shortcut specific to
  `cayleyPVM`; it does not create a vacuity risk because every theorem using
  `cayleyPVM` (`pmapIntegral_cayleyPVM_id`, `pmapIntegral_cayleyPVM_id_eq`)
  works with the integral against it, which by construction only ever probes
  measurable sets.
- **`cayleyInv`/`cayleyMap` division by zero at `u = 1`**: `cayleyInv u =
  (I*(u+1)/(u-1)).re`, undefined mathematically at `u=1`. Tool-verified
  (`lake env lean`, `#check`/proof of `cayleyInv 1 = 0`) that Mathlib's
  convention `x/0 = 0` makes `cayleyInv 1 = 0` *exactly* — which matches the
  blueprint's own explicit choice in the proof of `prpstn:hall-10.29`
  (line 2976: "Extend it to all of $S^1$ by setting $D(1) \equiv 0$"). So
  the junk value is not silently wrong; it coincides by construction with
  the blueprint's own stated extension, and this coincidence is exploited
  (not accidentally relied upon) by `spectralMeasure_singleton_one_eq_zero`
  and `pmapIntegral_cayleyInv_apply_sub_one`.
- **`mapPVM`'s `hinv` guard**: see above under
  `lmm:borel-bijection-transports-pvm` — genuinely required and used, no
  vacuity.
- **`pmapIntegral`/`integralApply`'s `Measurable f` guard**: already checked
  in the base session ("Items checked and cleared" above) and reconfirmed
  here for the two new theorems that depend on it directly
  (`isSelfAdjoint_pmapIntegral_of_real`, `pmapIntegral_cayleyInv_eq`), both
  of which carry `Measurable f`/`Measurable (fun u => ...)` explicitly as a
  hypothesis rather than relying on the junk branch.
- **`PVM` structure** (`ProjectionValuedMeasure.lean:71-88`): `#print`ed
  (reading the source, not the term) — `notMeasurable'` (non-measurable
  sets ↦ `0`) is a *field* of the structure, i.e. it is exactly
  `def:projection-valued-measure`'s own convention (this definition is
  outside today's file scope but is depended on for every vacuity check
  above; not re-audited against the blueprint text this session beyond
  confirming the convention is a structure field, matching how the
  blueprint's own definition treats it as declared for measurable sets and
  extended to `0` elsewhere).

No new vacuity or narrowing issue was found among these six items. All are
classified **match**, one (`thrm:hall-10.20`) with a documented,
convention-sanctioned hypothesis difference (Lean omits `Nontrivial H` where
the blueprint's global convention says it may), not a scope narrowing.

## Not verified (this follow-up)

- `def:hall-7.14` (spectral subspace) and `IsResolvent`/`def:hall-9.16`'s own
  statement text were not independently re-read against the blueprint this
  session (only `#print`ed for internal consistency with how the Cayley
  block cites them); a prior session is assumed to have covered them as part
  of the `hall-9.*`/`hall-10.1`/`10.2` chain.
- `def:projection-valued-measure` itself (in `spectral-theorems.tex`, a
  different file, outside the stated scope of both this and the prior
  session) was read only far enough to confirm the `notMeasurable'`
  convention, not depth-audited.
- No fresh `lake build`/`lake lint` run was performed this session either;
  H1's staleness finding still stands unresolved.

## Summary counts

- Statement-audit items depth-checked: 24 (23 match, 1 "Lean assumes more":
  `prpstn:hall-9.26-internal`'s derived lemmas / M2). The 6 items added this
  follow-up (`thrm:hall-10.28`, `prpstn:hall-10.29`, `prpstn:hall-10.3`,
  `thrm:hall-10.4`, `thrm:hall-10.20`, `lmm:borel-bijection-transports-pvm`)
  are all matches, one with a documented, convention-sanctioned hypothesis
  difference noted above (not counted as a mismatch).
- `\lean{}` links checked for existence: 188 (188 resolve; 0 missing),
  unchanged from the base session; the follow-up re-confirmed the specific
  15 identifiers named in the task via `#check`/`#print` rather than grep
  alone (`exists_isCayleyTransform`, `IsCayleyTransform`,
  `pmapIntegral_cayleyInv_eq`, `isSelfAdjoint_pmapIntegral_of_real`,
  `existsUnique_spectralMeasure_unbounded`, `spectralMeasure_concentrated`,
  `existsUnique_spectralMeasure_normal`, `eq_of_integral_id_eq_ambient`,
  `restrictPVM`, `mapPVM`, `assoc_mapPVM`, `mapPVM_apply`, `cayleyPVM`,
  `cayleyInv`, `cayleyMap`).
- Findings: 2 High, 2 Medium, 2 Low (unchanged; no new finding this
  follow-up — the six items audited were all matches).
- Hygiene grep (sorry/admit/native_decide/skipKernelTC/implemented_by/
  nolint): 0 hits (re-confirmed for `Integral.lean`, `AbstractCalculus.lean`,
  `Cayley.lean` this follow-up).
- Restriction markers found: 5 (all one family, M2); none in the six items
  audited this follow-up.
- Verified with a tool (grep/git/lean_guard.py/`lake env lean` `#check`,
  `#print`): H1, L1, L2, all link-existence and hygiene-grep items, the
  DirectSum instance-hypothesis text (M2), and — new this follow-up — the
  full signatures of `exists_isCayleyTransform`, `IsCayleyTransform`,
  `existsUnique_spectralMeasure_unbounded`, `spectralMeasure_concentrated`,
  `isSelfAdjoint_pmapIntegral_of_real`, `pmapIntegral_cayleyInv_eq`,
  `existsUnique_spectralMeasure_normal`, `eq_of_integral_id_eq_ambient`,
  `mapPVM`, `restrictPVM`, `assoc_mapPVM`, `IsResolvent`, and the fact
  `cayleyInv 1 = 0`.
- Judged by reading only: H2, M1 (blueprint prose vs. Lean proof structure),
  the "items checked and cleared" list's mathematical reasoning, and — new
  this follow-up — the line-by-line correspondence between each blueprint
  proof step and the corresponding Lean proof body for `restrictPVM`,
  `mapPVM`, `cayleyPVM`, and the `IsCayleyTransform`/`exists_isCayleyTransform`
  pair (signatures were tool-verified; the mathematical correspondence of
  full proof bodies was judged by reading).
