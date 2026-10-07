# Review: Blueprint §10.5 "Haag–Kastler Axioms (Minkowski)" vs Lean

Date: 2026-09-25
Reviewer: audit subagent (read-only)

## Scope

- Blueprint: `blueprint/src/sections/sec10/haag-kastler-axioms.tex` (2030 lines,
  `\label{sctn:haag-kastler-axioms}`). This single file covers not only Axioms 1–5
  and `HaagKastlerNet` but everything the blueprint hangs off them in chapter 10:
  the quasilocal colimit/completion chain, local von Neumann algebras, GNS
  irreducibility/purity, KMS states, vacuum states. Per task instructions this
  review goes deep on the five axioms, `HaagKastlerNet`, the quasilocal-algebra
  construction, Einstein causality and local von Neumann algebras, and spot-checks
  the remainder (GNS/KMS/vacuum) for hygiene (sorry/axiom/nolint) and `\lean{}`
  link integrity rather than re-deriving every one of the ~150 blueprint nodes.
- Lean: `Physicslib4/AQFT/HaagKastler/*.lean` (all files read except the
  `Curved*`/`HaagKastlerCurved` tree, which is out of scope for §10.5),
  `Physicslib4/AQFT/{KMS,PositiveEnergy}.lean`, spot checks into `Physicslib4/GNS/*`
  and `Physicslib4/Analysis/CStarCompletion.lean`.
- `scratch_*` files ignored (none found under this scope).
- No file was modified.

## Method

- Read the full blueprint tex once, then extracted every `\label`/`\lean`/`\leanok`
  line to map the node graph (`grep -n` outline, ~150 nodes).
- Read the Lean source for Axioms 1–5 (`LocalAlgebras.lean`, `Isotony.lean`,
  `LocalCommutativity.lean`, `ObservableBridge.lean`, `LorentzCovariance.lean`),
  `Net.lean` (`HaagKastlerNet`), `QuasilocalAlgebra.lean`, `EinsteinCausality.lean`,
  `LocalVonNeumann.lean`, `GeometricCovariance.lean`, `StrongDensity.lean`,
  `VacuumState.lean`, `PositiveEnergy.lean`, and translated each into ordinary
  mathematics for comparison against the tex.
- Grepped the whole scope for `sorry`, `admit`, `native_decide`,
  `skipKernelTC`, `implemented_by`, `axiom`, `nolint`, and the `Restriction:`
  marker.
- Extracted all 193 distinct `\lean{...}` identifiers cited in the file and
  checked each resolves to an actual Lean declaration; the first automated pass
  (regex on the bare final identifier) produced ~26 false "missing" flags because
  of dotted namespace declarations (e.g. `theorem CovariantQuasilocalAlgebra.
  IsVacuumState.invariant` inside `namespace HaagKastler`). Every flagged name was
  then checked by hand (`grep`/`Read`); all 193 resolve to a real declaration. No
  broken `\lean{}` link was found in this scope.
- Did not run `lake build`, `lean_verify`, or `lean_guard.py verify` (read-only
  bash tool only per policy for an auditor role); integrity claims below about
  proof completeness rest on grepping for `sorry`/`admit`/`axiom`, not on
  re-checking the kernel.

## Findings

### High

**H1 — Einstein causality and the entire "Local von Neumann Algebras" subsection
are proved about the wrong ambient algebra, with no bridge to the canonical
quasilocal algebra.**

- Location: `Physicslib4/AQFT/HaagKastler/LocalCommutativity.lean:62-69`,
  `EinsteinCausality.lean` (whole file), `LocalVonNeumann.lean` (whole file,
  defines `localOperators`, `localVonNeumann`, `localVonNeumannAlgebra`,
  `relativeCommutant`, `IsIrreducibleInclusion`), vs.
  `Net.lean:121-129` (`HaagKastlerNet.quasilocal`) and `Net.lean:201-205`
  (`HaagKastlerNet.commAlgebra`); blueprint `def:local-commutativity`
  (lines 386-407), `def:quasilocal-algebra` (371-384), `thrm:einstein-causality`
  (623-635), `def:local-von-neumann` through `thrm:self-inclusion-factor`
  (637-899).
- Problem: `HaagKastlerNet.quasilocal` is the *canonical* quasilocal algebra
  built by `exists_quasilocalAlgebra` (colimit-then-completion,
  `thrm:quasilocal-algebra-exists`) — this is the object the blueprint calls
  "the quasilocal algebra 𝔘" throughout `def:quasilocal-algebra` and everything
  downstream of it. But Axiom 3 (`LocalCommutativity`) is formalized as an
  *existential* over *some* `QuasilocalAlgebra U i` witness
  (`∃ Q : QuasilocalAlgebra U i, ... Commute ...`), and `HaagKastlerNet.commAlgebra
  := N.localCommutativity.choose` picks whatever witness the existential
  produces — which need **not** be `N.quasilocal`. The blueprint itself notes
  (`thrm:quasilocal-algebra-exists`, line 381) that uniqueness of the quasilocal
  algebra up to isomorphism is *deliberately not claimed*, so there is no
  general reason `commAlgebra ≅ quasilocal`, let alone `commAlgebra = quasilocal`.
  `Net.lean:202-203` even documents the gap in a comment: "(This may differ from
  the canonical `quasilocal` of Axiom 4.)"
  Consequently `einstein_causality`, `exists_gns_einstein_causality`
  (`EinsteinCausality.lean`), and every declaration in `LocalVonNeumann.lean`
  (microcausality, isotony of the von Neumann net, statistical independence,
  relative commutants, irreducible inclusions — blueprint's entire §"Local von
  Neumann Algebras" and §"Relative Commutants" subsections) are theorems about
  representations `π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)`, not about
  `N.quasilocal`. Nothing in the codebase connects the two: `grep -rn
  "localVonNeumann\|localOperators\|relativeCommutant\|IsIrreducibleInclusion"`
  across the rest of `Physicslib4/AQFT/HaagKastler/*.lean` finds no use outside
  `LocalVonNeumann.lean` itself. Meanwhile `GeometricCovariance.lean` (geometric
  covariance of the von Neumann net, orbit-invariance of factoriality, the vN
  isomorphism theorem — blueprint's `thrm:von-neumann-geometric-covariance`
  onward) independently re-defines its *own* `covLocalOperators`/
  `covLocalVonNeumann` against `C.quasilocal` (the algebra that states, GNS,
  purity and KMS are all actually stated against). So the blueprint presents one
  coherent "local von Neumann algebra of the net" object, but the Lean has two
  non-communicating constructions of it over two possibly-different ambient
  algebras, and the one that all the state/GNS/purity/KMS machinery is built on
  (`quasilocal`) is *not* the one Einstein causality, microcausality, statistical
  independence and relative commutants are proved about (`commAlgebra`).
- Why this matters: a reader following the blueprint would take "Einstein
  causality holds for the quasilocal algebra of the net" and "the GNS
  representation of a state on the quasilocal algebra has commuting local von
  Neumann algebras" to be facts about the *same* 𝔘. As formalized, the theorem
  that's actually available is weaker: causality/microcausality/statistical
  independence are proved for *an* ambient algebra satisfying Axiom 3, and it is
  an open question in the repository whether the canonical `quasilocal` algebra
  used everywhere else is one such algebra.
- Classification: **Lean concludes less** (Einstein causality, microcausality,
  statistical independence, relative-commutant results) / **different objects**
  (two independent `covLocalVonNeumann`-style constructions).
- Blueprint acknowledgment: line 383 of the tex claims "There is no longer any
  discrepancy between this blueprint's formalization markings and the Lean" —
  this claim is about `\lean`/`\leanok` tags resolving to real declarations
  (which is true), not about the two witnesses coinciding, so it should not be
  read as covering this gap, and the gap is not stated anywhere else in the tex.
- Suggested fix (propose only): either (a) prove
  `N.commAlgebra ≅⋆ₐ N.quasilocal` (or more precisely, that Local Commutativity
  can always be witnessed by the canonical `quasilocal` algebra, i.e. restate
  `LocalCommutativity` as commutation specifically in `N.quasilocal`, dropping the
  existential over the ambient algebra — the `LocalCommutativity.lean` docstring
  already gestures at this: "the existential above may be witnessed by that
  canonical algebra"), or (b) add an explicit blueprint restriction/note that
  Einstein causality and the local-von-Neumann-algebra results are about *an*
  algebra witnessing Axiom 3 and not proven to transport to the canonical
  quasilocal algebra used elsewhere.

### Medium

**M1 — The bounded-generator restriction on the spectrum condition does not use
the project's `Restriction:` marker, despite CLAUDE.md naming this file as the
example to convert.**

- Location: `Physicslib4/AQFT/PositiveEnergy.lean:14-21,45-47` and
  `Physicslib4/AQFT/HaagKastler/VacuumState.lean:18-28`.
- Problem: `.claude/CLAUDE.md` states: "Record a deliberate restriction in the
  docstring of the declaration, on a line starting `**Restriction:**`... Example
  to convert: the positive-energy docstring in
  `Physicslib4/AQFT/HaagKastler/VacuumState.lean` (bounded generators until
  Stone's theorem is available)." Both files clearly *describe* the restriction
  in prose ("requiring `P` bounded is a genuine restriction... the faithful
  unbounded form needs Stone's theorem... which Mathlib does not yet provide")
  but neither uses a line beginning `**Restriction:**`. `grep -rln
  'Restriction:'` across the whole `Physicslib4/AQFT` tree finds only
  `StrongDensity.lean` (which does follow the convention correctly, and is a
  useful positive contrast). Automated restriction audits/greps (as this very
  audit's §3 instructions describe) will silently miss the positive-energy /
  vacuum-state restriction as a result, and the conversion CLAUDE.md explicitly
  calls for has not happened.
- Classification: hygiene (unrecorded restriction, marker convention not
  followed) — verified by grep and by reading both files.
- Suggested fix (propose only): add a line starting `**Restriction:**` to the
  docstrings of `IsPositiveEnergy` (`PositiveEnergy.lean`) and
  `CovariantQuasilocalAlgebra.IsVacuumState`/`IsVacuumStateConcrete`
  (`VacuumState.lean`), naming the bounded-generator restriction and what it is
  waiting on (Stone's theorem / unbounded self-adjoint operators), matching the
  `StrongDensity.lean` example.

### Low

**L1 — Blueprint's own Axiom 5 text still uses strict inclusion `⊂`, which Axiom
2's own commentary says was a mistake.**

- Location: blueprint `haag-kastler-axioms.tex:590` ("for basis elements
  $\mathbf{B}_\iota \subset \mathbf{B}_\kappa$ ... $\alpha_L$ commutes with $i$"),
  vs. `haag-kastler-axioms.tex:43` (Axiom 2's own remark: "Earlier versions of
  this statement wrote $\subset$; that was a divergence from the Lean, and the
  non-strict form is the correct one... the strict reading would leave the
  diagonal of the inclusion order outside the axiom altogether"). The Lean
  (`LorentzCovariance.lean:358-388`, condition (3)) quantifies over non-strict
  `B₁ ⊆ B₂`, consistent with Axiom 2's stated correction and with the Lean, not
  with Axiom 5's own prose.
- Problem: this is the identical `⊂`-vs-`⊆` mistake that Axiom 2's commentary
  explicitly flags and corrects, reappearing uncorrected in Axiom 5's own
  statement three definitions later. It does not affect soundness (the Lean
  proves the stronger, correct statement over `⊆`, and a strict-inclusion
  reading is implied by it), but it is an internal inconsistency in the
  blueprint's own conventions, of exactly the kind Axiom 2 warns readers about.
- Classification: **notation only** (blueprint prose vs. Lean); also a
  blueprint-math inconsistency (see below).
- Suggested fix (propose only): change `\subset` to `\subseteq` at line 590,
  matching the correction already made to Axiom 2.

**L2 — `nolint` usage is isolated and justified; no action needed.**

- Location: `Physicslib4/Analysis/CStarCompletion.lean:84`,
  `@[nolint unusedArguments]` on `abbrev CStarCompletion`.
- The preceding docstring (lines 70-83) explicitly explains why two of the five
  listed hypotheses (`StarModule ℂ A`, `CStarRing A`) are unused by the
  abbreviation's right-hand side but kept anyway (naming the blueprint's
  "standing hypotheses" node faithfully), and why the lint is suppressed rather
  than the hypotheses dropped. This is a justified `nolint`, not a
  commit-gate workaround. Recorded for completeness, not as a finding requiring
  a fix.

## Blueprint-math issues

- **B1 (= L1 above).** Axiom 5's statement (line 590) contradicts Axiom 2's own
  correction regarding strict vs. non-strict inclusion; the blueprint should be
  internally consistent about this convention it explicitly cares about.
- **B2.** The tex's claim at line 383 ("There is no longer any discrepancy
  between this blueprint's formalization markings and the Lean") is true only
  in the narrow sense that `\lean`/`\leanok` tags resolve; it should not be read
  (and shouldn't be phrased in a way that invites being read) as covering the
  `commAlgebra`/`quasilocal` gap described in **H1**, which the surrounding prose
  does not address at all.
- No other proof gaps or incorrect derivations were found in the tex prose read
  during this review (the colimit/completion chain, Axioms 1–5, the bridge
  principle discussion, and the von Neumann algebra sections read as
  mathematically sound modulo B1/B2 and the disclosed non-formalization of the
  von Neumann density theorem at `thrm:quasilocal-strongly-dense`, which is
  correctly *not* marked `\leanok` on its proof block even though the theorem
  statement is).

## Hygiene summary (verified by grep, not by `lake build`)

- `sorry`/`admit`/`native_decide`/`skipKernelTC`/`implemented_by`: exactly one
  hit in scope, `Physicslib4/AQFT/HaagKastler/StrongDensity.lean:74`
  (`dense_range_in_bicommutant`). This is the known, already-disclosed von
  Neumann density theorem gap; it carries a correct `**Restriction:**` line
  (line 57) and the blueprint correctly declines to mark the *proof* block
  `\leanok` (only the *statement* is `\leanok`, at line 553) — this is the one
  place in the file that models the marker convention correctly and can be used
  as the template for fixing M1.
- Bare `axiom` declarations in scope: none.
- `nolint`: one use (see L2), justified.
- `Restriction:` marker: one use (`StrongDensity.lean`); two more restrictions
  exist in prose without the marker (M1).

## Classification counts (items audited in depth: 12)

- match: 7 (`def:local-algebras`/`LocalNet`, `def:isotony`/`Isotony`,
  `def:quasilocal-completeness`/`ObservableCorrespondence`,
  `def:haag-kastler-net`/`HaagKastlerNet`, `def:quasilocal-algebra`/
  `QuasilocalAlgebra`, `def:local-commutativity`/`LocalCommutativity` taken on
  its own literal terms, `thrm:quasilocal-strongly-dense`'s statement (the
  proof is honestly unclaimed))
- notation only: 1 (`def:lorentz-covariance`, the `⊂`/`⊆` prose slip, L1/B1)
- Lean assumes more: 1 (`def:positive-energy` / `IsVacuumState`, bounded
  generator vs. the intended unbounded one — a disclosed, intentional
  restriction, flagged for marker hygiene in M1 rather than as a faithfulness
  defect)
- Lean concludes less: 2 (`thrm:einstein-causality`; the
  `def:local-von-neumann` family) — both are the single root cause in H1
- different objects: 1 (the `commAlgebra`-based `LocalVonNeumann.lean` bicommutant
  vs. the `quasilocal`-based `GeometricCovariance.lean` bicommutant — the other
  face of H1)
- edge cases differ: 0
- can't determine: 0

154 further `\lean{}`-cited items in the file were spot-checked only for link
integrity (all 193 total identifiers resolve to real declarations; see Method)
and for `sorry`/`axiom`/`nolint` hygiene, not translated statement-by-statement
against the tex.

## What was verified by tool vs. by reading

- Verified by grep/tool: existence of all 193 `\lean{}`-cited declarations
  (with manual correction of ~26 automated false negatives caused by dotted
  Lean namespace declarations); absence of `sorry`/`admit`/`native_decide`/
  `skipKernelTC`/`implemented_by`/bare `axiom` outside `StrongDensity.lean`;
  the single `nolint` site and its justifying comment; the single correctly-used
  `Restriction:` marker and the absence of the marker in `PositiveEnergy.lean`/
  `VacuumState.lean`; the absence of any use of `localVonNeumann`/
  `localOperators`/`relativeCommutant`/`IsIrreducibleInclosure` outside
  `LocalVonNeumann.lean` (supporting H1).
- Judged by reading: the mathematical translation of each Lean declaration for
  Axioms 1–5, `HaagKastlerNet`, `QuasilocalAlgebra`, Einstein causality and the
  local-von-Neumann-algebra chain against the corresponding blueprint prose (the
  statement-audit comparisons and H1/L1/B1/B2 above); no `lean_verify`,
  `lake build`, or `lean_guard.py verify` was run (read-only bash only), so
  kernel-level axiom/proof-completeness claims rest on the grep sweep above, not
  on a fresh build.
