# Audit: blueprint §10.6 "Haag-Kastler Axioms in Curved Spacetime"

Date: 2026-09-25
Scope: `blueprint/src/sections/sec10/haag-kastler-axioms-in-curved-spacetime.tex`
(all nodes, `def:local-algebras-in-curved-spacetime` through
`def:ground-state-for-flow-in-curved-spacetime`), and the Lean it cites:
`Physicslib4/AQFT/HaagKastlerCurved/{LocalAlgebras, Isotony, LocalCommutativity,
LocalAlgebra, IsometricCovariance, Net, EinsteinCausality, LocalVonNeumann,
Concrete, GeometricCovariance, Purity, CovariantState, StabilizerAction,
StabilizerKMS, Spacetime}.lean`, plus the `Physicslib4.Spacetime.*` bridge
declarations these touch (`LorentzianSpacetime.toAbstract`, `Isometry`,
`CausalComplement`) and `Physicslib4.AQFT.PositiveEnergy`.

Read-only review. No `.lean`/`.tex` files were modified.
`notes/agents/review-2026-09-sec10.1-10.7.md` (§10.1/§10.7) and
`notes/agents/review-2026-09-sec10.4.md` (§10.4, spacetime) were read first;
their findings (the un-marked `IsGeodesic := True` restriction, the
`gns_construction`/`gns_unique` tagging gap) are not repeated here except
where they interact with §10.6 material.

## Method

Tool-verified:
- All 64 distinct `\lean{...}` names in this file resolve against
  `blueprint/lean_decls` (0 missing).
- `lake env lean` + `#print axioms` on five sampled theorems spanning
  geometric covariance, the Killing-flow KMS thermal representation, the
  purity/irreducibility equivalence, and the trivial-net satisfiability
  witnesses (`lieConj_image_localVonNeumann`,
  `IsKMSStateForFlow.exists_gns_unitary_strongContinuous`,
  `exists_gns_pure_iff_irreducible`, `trivialHaagKastlerNet`,
  `nonempty_haagKastlerNet`) — all five report exactly `[propext,
  Classical.choice, Quot.sound]`.
- `grep` for `sorry`, `admit`, `native_decide`, `debug.skipKernelTC`,
  `implemented_by`, `nolint`, `axiom`, `Restriction:` across
  `Physicslib4/AQFT/HaagKastlerCurved/*.lean`: no hits for any of these
  except the English word "axiom" in two docstrings (not a declaration).
  In particular **no `Restriction:` marker exists anywhere in this
  directory**, despite there being a restriction that needs one (see
  Medium-1).
- `git log --since <verify-receipt time> -- Physicslib4/AQFT/HaagKastlerCurved
  blueprint/src/.../haag-kastler-axioms-in-curved-spacetime.tex`: empty. The
  last commit touching any file in scope is `ac97898`
  (2026-09-06T00:05:20Z), before the recorded `verify-receipt.json`
  (`lake build` + `lake lint`, both exit 0, 2026-09-18T14:08:28Z), so the
  receipt is current for this section.
- `.git/lean-kit/approvals.json` does not exist — no approvals in effect to
  review.

Judged by reading: the statement-audit table below, all "match"
classifications, and the two structural findings (High-1, Medium-2) — these
were established by reading the blueprint's own prose (including its
unusually candid paragraphs about what Axioms 2/3 "used to" do) against the
Lean definitions side by side, and by tracing which Lean declaration each
downstream theorem actually invokes (`N.commIsotony` = Axiom 2's family vs.
the `ι` bound inside `IsometricCovariance`).

## Findings

### High

**H-1. Axiom 5 (`IsometricCovariance`) still has the exact defect the
blueprint says it fixed for Axiom 3: it existentially quantifies its own,
private isotony family, disconnected from Axiom 2's actual chosen family.**

- Blueprint text for Axiom 5 (`def:isometric-covariance-in-curved-spacetime`,
  `haag-kastler-axioms-in-curved-spacetime.tex:93-126`), clause (3): "for
  Alexandrov topology basis elements $\mathbf{B}_\iota \subset
  \mathbf{B}_\kappa$ and the unital $*$-monomorphism $i$ **of Axiom 2
  (Isotony)** $\alpha_\varphi$ commutes with $i$" — i.e. the blueprint reads
  clause (3) as referring to the *same* `i` that Axiom 2 supplies.
- Lean, `Physicslib4/AQFT/HaagKastlerCurved/IsometricCovariance.lean:78-108`:
  `IsometricCovariance` is
  ```
  def IsometricCovariance (U : LocalNet M) : Prop :=
    ∃ (α : ...) (ι : ∀ ⦃B₁ B₂⦄, M.IsBasisSet B₁ → M.IsBasisSet B₂ → B₁ ⊆ B₂ →
          StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂)),
      (... injective ι ...) ∧ (... α 1 = id ...) ∧ (... α composes ...) ∧
      (∀ φ ... , α φ B₂ (ι hB₁ hB₂ h a) = ι hφB₁ hφB₂ hφ (α φ B₁ a))
  ```
  — the `ι` that clause (3) commutes with is bound *inside* `Exists`, chosen
  independently of the net's actual `Isotony` structure. The module docstring
  at lines 65-70 confirms this reading explicitly: "for every inclusion
  `B₁ ⊆ B₂` ..., **a choice of isotony `*`-monomorphism**
  `ι B₁ B₂ : U.algebra B₁ →⋆ₐ[ℂ] U.algebra B₂`".
- `HaagKastlerNet` (`Net.lean:51-68`) bundles `isotony : Isotony U` (Axiom 2)
  and `isometricCovariance : IsometricCovariance U` (Axiom 5) as two
  *separate* fields; nothing forces `isometricCovariance`'s internal `ι` to
  equal `isotony.map`, and `Net.lean` never even projects out that
  component of the existential witness (only the `α` component is exposed,
  as `covEquiv`, `Net.lean:109-111`). Axiom 5's own promise "commutes with
  isotony" is therefore not usable against the net's real isotony family
  `commIsotony` at all — nothing connects the two.
- This is *exactly* the anti-pattern the blueprint spends two long remarks
  (`tex:45`, `tex:66`) explaining it eliminated from Axiom 3: "It previously
  introduced its own family of isotony embeddings existentially ... and it
  was those chosen witnesses --- not the Axiom 2 maps --- that every
  downstream result actually used ... The family and its injectivity now
  belong to Axiom 2." The identical bug is present, unremarked, in Axiom 5.
- The consequence is visible and *is* worked around, but silently, one theorem
  downstream: `GeometricCovariance.lean:47-60` (`lieConj_image_localOperators`,
  cited as `thrm:von-neumann-geometric-covariance-in-curved-spacetime`) has to
  take an extra explicit hypothesis
  ```
  (hcompat : ∀ a : N.algebra B₁,
    N.stabAutHom B g (N.commIsotony hB₁ hB h₁ a)
      = N.commIsotony hgB₁ hB h₁' (N.covEquiv (g : M.Isom) B₁ a))
  ```
  relating `stabAutHom` (built from Axiom 5's `α`) to `commIsotony` (Axiom
  2's real family) — precisely the kind of per-site "coherence" hypothesis
  the blueprint's Axiom-2/3 rewrite was designed to make unnecessary
  "throughout this chapter" (`tex:66`). The blueprint text for *this specific
  theorem* (`tex:281`) does flag `hcompat` as an added hypothesis ("neither
  basis-set preservation ... nor the coherence relating the stabilizer action
  ... to the chosen isotony embeddings ... both enter as explicit
  hypotheses"), so that one downstream use is honestly disclosed. What is not
  disclosed anywhere is *why* the hypothesis is needed: it is needed because
  Axiom 5 itself, as formalized, does not actually assert commutation with
  Axiom 2's isotony family, contrary to what its own blueprint statement says.
- Classification: **Lean concludes less** for `def:isometric-covariance-in-curved-spacetime`
  itself (it asserts "there exists *some* coherent isotony-commuting structure"
  rather than "the covariance commutes with the net's chosen isotony `i`"),
  which then forces **Lean assumes more** (`hcompat`) at
  `thrm:von-neumann-geometric-covariance-in-curved-spacetime`, `def:stabilizer-action-in-curved-spacetime`,
  and every later theorem built on `stabAut`/`stabAutHom`
  (`lmm:stabilizer-action-laws-in-curved-spacetime` through
  `thrm:kms-thermal-representation-in-curved-spacetime`) inherit an Axiom 5
  that is weaker than advertised, although none of those specific downstream
  statements happen to need the isotony-commutation clause of Axiom 5, so the
  practical blast radius is currently limited to the `GeometricCovariance.lean`
  family (`lieConj_image_localOperators/_localVonNeumann/_localVonNeumannAlgebra`,
  `localVonNeumann_isFactor_smul`, `localVonNeumannEquiv`).
- *Suggested fix (report only)*: change `IsometricCovariance` to take
  `Isotony U` as a parameter (as `LocalCommutativity` now does) and state
  clause (3) against `i.map` directly, dropping the internal existential
  `ι`. This mirrors the fix already applied to Axiom 3 and would let
  `hcompat` in `GeometricCovariance.lean` be discharged from Axiom 5 itself
  rather than assumed anew.

### Medium

**M-1. `IsPositiveEnergy`'s bounded-generator restriction — consumed by
`def:ground-state-for-flow-in-curved-spacetime`, in scope — is explained in
prose but never carries the project's `**Restriction:**` marker, even though
`CLAUDE.md` names this exact restriction as the one to convert.**

- `CLAUDE.md`: "Record a deliberate restriction in the docstring of the
  declaration, on a line starting `**Restriction:**` ... Example to convert:
  the positive-energy docstring in
  `Physicslib4/AQFT/HaagKastler/VacuumState.lean` (bounded generators until
  Stone's theorem is available)."
- The shared definition actually used here,
  `Physicslib4/AQFT/PositiveEnergy.lean:39-46` (`IsPositiveEnergy`), explains
  the same restriction in prose ("The generator of a physical translation is
  unbounded, so requiring `P` bounded is a restriction; the faithful
  unbounded form needs Stone's theorem ... absent from Mathlib") but has no
  line starting `**Restriction:**`. Neither does
  `Physicslib4/AQFT/HaagKastler/VacuumState.lean` (confirmed by grep — the
  conversion CLAUDE.md asks for has not happened).
- Blueprint `def:ground-state-for-flow-in-curved-spacetime`
  (`tex:688-695`) is honest about the same gap in its own prose: "The
  positive-energy condition is the bounded-generator scaffold; the faithful
  unbounded form is Stone-gated" — but this restriction is likewise not
  flagged in a way this audit's own §3 marker-grep would find (there is no
  restriction-marker convention on the *blueprint* side either).
- Grep confirms: zero occurrences of `Restriction:` anywhere in
  `Physicslib4/AQFT/HaagKastlerCurved/` or `Physicslib4/AQFT/PositiveEnergy.lean`.
  This restriction is otherwise well-documented in prose at every site
  (`PositiveEnergy.lean`, `StabilizerKMS.lean:137-145`, blueprint `tex:694`),
  so this is a marker-convention gap, not a hidden one — but it means an
  automated restriction sweep (the one this audit's §3 procedure specifies)
  finds nothing here.
- *Suggested fix*: add a `**Restriction:**` line to `IsPositiveEnergy`'s
  docstring (`PositiveEnergy.lean:39`), e.g. "**Restriction:** the generator
  `P` is required bounded until Stone's theorem and unbounded self-adjoint
  operators are available in Mathlib; the intended condition is positivity
  of the (possibly unbounded) self-adjoint generator of `V`." This single
  fix would also close the parallel gap already flagged for
  `VacuumState.lean` in `CLAUDE.md`.

**M-2. `LocalCommutativity.lean`'s module docstring is stale: it still
describes Axiom 3 in its pre-fix, existentially-quantified form, even though
the actual declaration (correctly) takes the Axiom 2 family as an explicit
parameter.**

- `Physicslib4/AQFT/HaagKastlerCurved/LocalCommutativity.lean:40-46`
  (docstring immediately above `LocalCommutativity`): "A local net `U` ...
  satisfies *local commutativity* if **there is a coherent family of isotony
  `*`-monomorphisms** `ι : 𝔘(B₁) ↪ 𝔘(B₂)` ... such that ...". This describes
  an existential (`∃ ι, ...`).
- The actual declaration, three lines below
  (`LocalCommutativity.lean:69-75`):
  ```
  def LocalCommutativity (U : LocalNet M) (i : Isotony U) : Prop :=
    ∀ ⦃B₁ B₂ B⦄ ..., Commute (i.map hB₁ hB h₁ a) (i.map hB₂ hB h₂ b)
  ```
  `i` is a *parameter*, supplied by the caller (in practice, the net's own
  `isotony` field via `HaagKastlerNet.localCommutativity : LocalCommutativity
  U isotony`, `Net.lean:58-62`) — not bound inside `LocalCommutativity`
  itself. `Net.lean:58-62`'s own docstring gets this right: "This *consumes*
  the Axiom 2 family rather than introducing its own."
  The file-level docstring (`LocalCommutativity.lean:30-46`, both the module
  doc and the declaration doc) is a leftover from before the Axiom 2/3
  rewrite the blueprint prose describes, and was not updated to match.
- This is purely a documentation staleness issue (the code and the blueprint
  agree; only the Lean docstring lags), but it is the kind of drift that
  could mislead a reader auditing exactly this axiom for exactly the defect
  found in H-1.
- *Suggested fix*: reword `LocalCommutativity.lean:40-46` to describe `i` as
  a hypothesis/parameter rather than an existentially-chosen family, matching
  `Net.lean:58-62`'s phrasing.

### Low

**L-1. `Concrete.lean`'s `toAbstract` bridge instantiates Axiom 5's `Isom`
with the *full* isometry group, not the identity-component subgroup the
blueprint's Axiom 5 quantifies over; this is flagged in the Lean docstring
but not cross-referenced from the blueprint.**

- Blueprint Axiom 5 (`tex:93-94`): "A member $\varphi$ of the group of
  isometries of $M$ **connected to the identity**."
- `Physicslib4/AQFT/HaagKastlerCurved/Concrete.lean:65-72`:
  `LorentzianSpacetime.toAbstract` sets `Isom := Isometry L.toSpacetime` (the
  *full* isometry group), with the identity-component restriction deferred to
  a sibling bridge `toAbstractIdentityComponent`
  (`IdentityComponent.lean`, cited by `sec10/spacetime.tex`, outside this
  file's `\lean{}` list but reachable from it). The Lean docstring
  (`Concrete.lean:40-51`) discloses this honestly ("this full-group bridge is
  retained for the axioms that hold under the whole isometry group"), so this
  is not a hidden gap for a reader of the Lean source. Using the full group is
  a strictly *stronger* hypothesis on the net (harder to satisfy, not a
  vacuous widening), so no theorem is falsified by it.
- Not a defect in itself — `Concrete.lean` is cited by this section only for
  `thrm:additive-free-locality-in-curved-spacetime`
  (`commute_of_spacelike_mono_geometric`,
  `localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric`),
  neither of which touches `Isom`/Axiom 5 at all — but a reader following
  `\uses{def:isometric-covariance-in-curved-spacetime}` through this file to
  find "the" concrete instantiation of Axiom 5 would land on the wrong
  bridge. *Suggested fix*: none required in Lean; if a concrete Axiom-5 net is
  ever added to this blueprint section, cite `toAbstractIdentityComponent`
  explicitly rather than `toAbstract`.

## Statement audit (classification table)

All `\lean{}`-tagged nodes in this section were checked. Only non-matches are
detailed above (H-1); everything else classifies as **match**:

| Blueprint node | Lean | Classification |
|---|---|---|
| `def:local-algebras-in-curved-spacetime` | `LocalNet` | match |
| `def:isotony-in-curved-spacetime` | `Isotony` | match (blueprint text was itself amended to match the `⊆`/composition-law Lean; both now agree) |
| `def:local-commutativity-in-curved-spacetime` | `LocalCommutativity` | match (code correct; see M-2 for a stale docstring) |
| `def:local-observable` | `IsLocalObservable` | match |
| `def:local-completeness-in-curved-spacetime` | `LocalAlgebra` | match |
| `def:isometric-covariance-in-curved-spacetime` | `IsometricCovariance` | **Lean concludes less** — see H-1 |
| `def:haag-kastler-net-in-curved-spacetime` | `HaagKastlerNet` | match (bundling is faithful; inherits H-1) |
| `thrm:einstein-causality-in-curved-spacetime` | `einstein_causality`, `exists_gns_einstein_causality` | match |
| `def:local-von-neumann-in-curved-spacetime`, `def:local-von-neumann-algebra-in-curved-spacetime` | `localOperators`, `localVonNeumann`, `localVonNeumannAlgebra` | match |
| `thrm:von-neumann-microcausality-in-curved-spacetime`, `thrm:von-neumann-isotony-in-curved-spacetime`, `thrm:von-neumann-bundled-order-in-curved-spacetime` | `localVonNeumann_subset_centralizer`, `localVonNeumann_mono`, bundled variants | match |
| `def:von-neumann-net-in-curved-spacetime` | `vonNeumannNet` | match |
| `thrm:statistical-independence-in-curved-spacetime`, bundled variant | `localVonNeumann_separating`, `eq_zero_of_commute_of_cyclic`, `localVonNeumannAlgebra_separating` | match |
| `thrm:additive-free-locality-in-curved-spacetime` | `..._geometric` (`Concrete.lean`) | match (see L-1 for an adjacent, non-cited nuance) |
| `thrm:von-neumann-geometric-covariance-in-curved-spacetime` and family | `lieConj_image_*`, `localVonNeumannEquiv`, `localVonNeumann_isFactor_smul` | match *as stated* (blueprint honestly discloses the `hcompat`/`hgB₁`/`h₁'` hypotheses); root cause is H-1 |
| `def:relative-commutant-in-curved-spacetime` and family (irreducible inclusion, center, abelian, center-duality) | `relativeCommutant`, `IsIrreducibleInclusion`, etc. | match |
| `thrm:pure-iff-extreme-in-curved-spacetime`, `thrm:pure-iff-irreducible-in-curved-spacetime`, `thrm:pure-factor-generates-in-curved-spacetime`, `thrm:irreducible-dichotomy-in-curved-spacetime`, `thrm:gns-covariance-local-in-curved-spacetime` | `Purity.lean` declarations | match |
| `def:covariant-state-family-in-curved-spacetime`, `lmm:covariant-state-family-compose-in-curved-spacetime` | `IsCovariantFamily`, `.comp` | match |
| `def:stabilizer-action-in-curved-spacetime`, `lmm:stabilizer-action-laws-in-curved-spacetime`, `thrm:gns-unitary-stabilizer-in-curved-spacetime` (+ strongly-continuous, irreducible-covariant, purity-invariant, GNS-covariance-stabilizer variants) | `StabilizerAction.lean` declarations | match |
| `def:flow-aut-in-curved-spacetime`, `lmm:one-parameter-aut-flow-in-curved-spacetime`, `def:kms-state-for-flow-in-curved-spacetime`, `thrm:kms-thermal-representation-in-curved-spacetime`, `thrm:kms-convex-for-flow-in-curved-spacetime` | `StabilizerKMS.lean` declarations | match |
| `def:ground-state-for-flow-in-curved-spacetime` | `IsGroundStateForFlow` (+ `.invariant`, `.exists_strongContinuous_unitary`) | match *as stated*; restriction-marker gap, see M-1 |

**Counts**: match 27 (grouped rows above), Lean-concludes-less 1 (H-1),
notation-only 0, Lean-assumes-more 0 (as a *primary* classification; H-1's
downstream `hcompat` is a consequence, not a separately-mis-stated node),
different-objects 0, edge-cases-differ 0, can't-determine 0.

## \lean{}/\leanok audit

- 0 of 64 cited names missing from `blueprint/lean_decls` (tool-verified).
- Every `\leanok`-marked node checked has a Lean declaration with no `sorry`
  and standard axioms (tool-verified on 5 samples spanning the file; the
  full-directory grep for `sorry`/`admit`/etc. found none). `\leanok` is
  honest throughout in the sense of "this compiles"; H-1 is a faithfulness
  gap, not a `\leanok` integrity gap.
- `\uses{}` edges spot-checked for the highest-traffic nodes
  (`def:haag-kastler-net-in-curved-spacetime`,
  `thrm:von-neumann-geometric-covariance-in-curved-spacetime`,
  `def:kms-state-for-flow-in-curved-spacetime`) all resolve to labels defined
  earlier in the same file or in already-reviewed sections (`gns-construction-details.tex`,
  `spacetime.tex`); no dangling `\ref`/`\uses` found.

## Blueprint-math issues

None found beyond H-1 (which is a Lean/blueprint faithfulness gap, not a
blueprint-math gap: the blueprint's own mathematical prose for Axiom 5 is
internally consistent and matches the *stated intent*; it is the Lean
formalization that falls short of it). The blueprint's self-critical
remarks about the Axiom 2/3 rewrite (`tex:43-46`, `tex:66`, `tex:226-228`)
are accurate against the current Lean and were independently re-verified by
reading `Net.lean`, `Isotony.lean`, `LocalCommutativity.lean`, and
`LocalVonNeumann.lean`. No incorrect proof sketches or convention
inconsistencies were found in the informal text.

## Mathlib duplication

None found. `localVonNeumann`/`localVonNeumannAlgebra` correctly reuse
`Set.centralizer`, `VonNeumannAlgebra`, and the shared
`vonNeumannOfSelfAdjoint`/`Set.centralizer_centralizer_centralizer` machinery
rather than reimplementing bicommutant theory; `relativeCommutant` is built
by hand only because (as the blueprint itself notes, `tex:326`) Mathlib's
`VonNeumannAlgebra` carries no lattice meet, which is a genuine gap rather
than avoidable duplication.

## Summary counts

- Statement-audit nodes: 27 match-groups (all directly-tagged declarations
  matched their blueprint prose except one), 1 Lean-concludes-less (H-1).
- Findings: 1 High (H-1), 2 Medium (M-1, M-2), 1 Low (L-1).
- `\lean{}` link integrity: 64/64 resolve; 0 dangling.
- Lean hygiene: 0 `sorry`/`admit`/`native_decide`/`debug.skipKernelTC`/
  `implemented_by`/`nolint`/`axiom` in scope; 0 `Restriction:` markers in
  scope despite one restriction (M-1) that needs one.
- Tool-verified: `\lean{}` name resolution (script against
  `blueprint/lean_decls`), axiom-cleanliness on 5 sampled theorems (`lake env
  lean` + `#print axioms`), hygiene greps, verify-receipt currency via `git
  log --since`, absence of approvals.
- Judged by reading: H-1's structural diagnosis (tracing `commIsotony` vs.
  the `ι` bound inside `IsometricCovariance` through `Net.lean` and
  `GeometricCovariance.lean`), M-2's docstring/code mismatch, L-1, and the
  blueprint-math and Mathlib-duplication sections.
