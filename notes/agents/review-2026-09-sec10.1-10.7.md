# Review: Blueprint §10.1 (GNS Construction Details) and §10.7 (General Covariance)

Scope: `blueprint/src/sections/sec10/gns-construction-details.tex`,
`blueprint/src/sections/sec10/general-covariance-in-curved-spacetime.tex`, and the Lean
they cite: `Physicslib4/GNS/{Basic,Construction,NullSpace,CauchySchwarz}.lean`,
`Physicslib4/AQFT/HaagKastlerCurved/GeneralCovariance.lean`, plus their direct
dependencies (`Physicslib4/AQFT/HaagKastlerCurved/{Net,Isotony,LocalCommutativity,
LocalAlgebra,LocalAlgebras,IsometricCovariance,Concrete}.lean`,
`Physicslib4/Spacetime/{LorentzianSpacetime,CrossMetricIsometry,Curves,Causality}.lean`
and the "Pullback metrics and cross-metric isometries" subsection of
`blueprint/src/sections/sec10/spacetime.tex`).

Read-only review. No `.lean`/`.tex` files were modified.

## Method

- Read both blueprint sections in full and cross-referenced every `\lean{...}` /
  `\leanfile{...}` tag against the cited declaration.
- Read `Physicslib4/GNS/Basic.lean`, `Construction.lean`, `NullSpace.lean`,
  `CauchySchwarz.lean`, and `Physicslib4/AQFT/HaagKastlerCurved/GeneralCovariance.lean`
  in full.
- Read the supporting chain in `Physicslib4/AQFT/HaagKastlerCurved/Net.lean`,
  `Isotony.lean`, and the "Pullback metrics and cross-metric isometries" part of
  `blueprint/src/sections/sec10/spacetime.tex` (defs/lemmas actually `\uses{}`'d by
  the in-scope theorem `def:general-covariance-in-curved-spacetime`).
- Verified via tool: `lake env lean` on a scratch file at `/tmp/axcheck.lean` running
  `#print axioms` on `gns_construction`, `gns_unique`, `lmm1`, `lmm2`,
  `cauchy_schwarz_inequality`, and `toAbstract_pullback_isBasisSet` — all report only
  `[propext, Classical.choice, Quot.sound]`. This also confirms the files compile
  against the current tree (no stale `.olean`).
- Verified via tool: `grep` for `sorry`, `admit`, `native_decide`,
  `debug.skipKernelTC`, `implemented_by`, `nolint`, `Restriction:` across the scoped
  files.
- Verified via tool: cross-checked every `\lean{...}` name in scope against
  `blueprint/lean_decls` (all present) and against `git log`/`lean_guard.py check`
  for changes since the last `verify-receipt`.
- Everything else (the blueprint proof sketches, the informal-to-Lean translation
  judgments, `\uses{}` accuracy) was judged by reading.

## Summary of classifications (statement audit)

| Blueprint node | Lean | Classification |
|---|---|---|
| `def:state` | `GNS.State`, `GNS.State.IsFaithful` | match |
| `def:cyclic-vector` | `GNS.IsCyclicVector` | match |
| `thrm:gns-construction-theorem` | `GNS.gns_construction` (+ `GNS.gns_unique`, uncited) | **match, with a tagging gap** (see Major 1) |
| `lmm:cauchy-schwarz-inequality` | `GNS.cauchy_schwarz_inequality`, `GNS.omega_star_swap_conj` | match (deliberately weaker hypotheses than `State`, exactly as the blueprint's own lemma statement requires) |
| `lmm:lmm1` | `GNS.lmm1` | match |
| `lmm:lmm2` | `GNS.lmm2` | match |
| `def:net-equivalence-in-curved-spacetime` | `HaagKastlerCurved.NetEquivalence` | match |
| `def:general-covariance-in-curved-spacetime` | `HaagKastlerCurved.NetTheory`, `IsGenerallyCovariant`, `LorentzianSpacetime.pullbackCarrierEquiv(_apply)`, `toAbstract_pullback_isBasisSet` | match |

No "Lean assumes more", "Lean concludes less", "different objects", or "edge cases
differ" items were found among the directly-tagged declarations in these two
sections. Every `\lean{}` name resolves to a real declaration with `\leanok` honestly
reflecting no `sorry` and clean axioms.

## Critical (false/unfaithful statements)

None found.

## Major

**1. `thrm:gns-construction-theorem`'s `\lean{}` tag omits `gns_unique`, the
declaration that actually proves the clause the blueprint text asserts.**

`blueprint/src/sections/sec10/gns-construction-details.tex:42-54`:
```
\lean{Physicslib4.GNS.gns_construction}
...
Furthermore, if $\omega$ is a faithful state, then the *-representation $\pi_\omega$
is faithful. In addition the GNS triple associated to $(\mathfrak{U}, \omega)$ is
unique up to unitary equivalence.
```
The uniqueness-up-to-unitary-equivalence clause is stated as part of "The GNS
Construction Theorem" in the blueprint's prose (and the proof node's `\uses{}`
list and body walk through a full "Uniqueness up to Unitary Equivalence" section).
In Lean this clause is proved separately, as `Physicslib4.GNS.gns_unique`
(`Physicslib4/GNS/Construction.lean:183-270`), a deliberate design choice explained
in that file's module docstring ("expressing the uniqueness clause as a conjunct
... is awkward"). That's a reasonable Lean-side decision, but the blueprint's
`\lean{}` tag for `thrm:gns-construction-theorem` cites only `gns_construction`, so
mechanical tools that resolve "what Lean backs this blueprint node" (including
`blueprint/lean_decls`, which lists `gns_construction` but not `gns_unique`) will
report the theorem as fully backed by a declaration that does *not* contain the
uniqueness clause the blueprint text claims. The mathematical content is present
and correctly proved (verified: `gns_unique` compiles, axioms clean); this is a
documentation/traceability gap, not an unsound proof.

*Suggested fix*: add `Physicslib4.GNS.gns_unique` to the `\lean{}` list of
`thrm:gns-construction-theorem` (or split the blueprint statement into two theorem
environments, one for existence+faithfulness and one for uniqueness, each with its
own accurate `\lean{}` tag).

**2. The blueprint's own "geodesic placeholder" restriction (used throughout
the causal-precedence chain feeding `\uses{}` of `def:general-covariance-in-curved-spacetime`)
is documented in prose but not marked with the project's `Restriction:` convention,
so an automated restriction sweep (grep for `Restriction:`) would miss it.**

`blueprint/src/sections/sec10/spacetime.tex:328` carries an explicit, well-written
remark:
```
\textbf{Remark (geodesic placeholder in the formalization).} ... the predicate
\texttt{Physicslib4.Spacetime.IsGeodesic} is defined to be \texttt{True}, so it
imposes no constraint. ... This is the one place where \ref{def:trip} and
\ref{def:causal-trip} diverge from their Lean implementations...
```
The corresponding Lean, `Physicslib4/Spacetime/Causality.lean:66-74`:
```lean
/--
A *geodesic* of a spacetime, as needed by section 10.4 of the blueprint.

Mathlib v4.31.0-rc1 does not provide a Lorentzian / pseudo-Riemannian
geodesic. We provide an opaque placeholder predicate. Downstream work
should replace this by the genuine geodesic condition...
-/
@[nolint unusedArguments]
def IsGeodesic (_μ : M.SmoothPath) : Prop := True
```
explains the restriction clearly, but the docstring never uses the literal marker
`**Restriction:**` that `CLAUDE.md` specifies ("Record a deliberate restriction in
the docstring of the declaration, on a line starting `**Restriction:**`"). Per
`.claude/lean-policy.json`, `restriction_marker` is `"Restriction:"`, and this audit's
own §3 procedure is to grep for exactly that marker — which finds nothing here.
`def:trip`/`def:causal-trip` (and hence chronological/causal precedence, the
Alexandrov basis, and everything `def:general-covariance-in-curved-spacetime`
`\uses{}` transitively through `def:lorentzian-spacetime` and the cross-metric
isometry chain) rest on this weakened notion.

Note on mathematical direction: this is *not* obviously narrowing in the direction
one might first assume. Standard Lorentzian geometry defines chronological
precedence via arbitrary future-directed timelike curves, not curves required to be
piecewise geodesic, so `IsGeodesic := True` likely makes the Lean `≪`/`≺` relations
coincide with the standard textbook notion rather than the blueprint's own (stricter,
geodesic-requiring) `def:trip`. Whether this is a widening or narrowing of any given
downstream theorem therefore needs a case-by-case check; it is flagged here because
it currently isn't discoverable by the marker convention the project relies on.

*Suggested fix*: add a line starting `**Restriction:**` to the `IsGeodesic` docstring
(e.g. "**Restriction:** `IsGeodesic` is `True` until a Lorentzian Levi-Civita
connection is available in Mathlib; the intended condition is auto-parallelism of the
tangent field along the curve.") so the marker-based sweep in future audits finds it.

## Minor

**3. Stale project-wide `verify-receipt.json`, though not for the audited files.**
`.git/lean-kit/verify-receipt.json` records a successful `lake build` + `lake lint`
at `2026-09-18T14:08:28+00:00`, but `HEAD` (`11768f7`, 2026-09-24) is 9 commits ahead.
`git log --since=<receipt time> -- Physicslib4/GNS Physicslib4/AQFT/HaagKastlerCurved
Physicslib4/Spacetime blueprint/src/sections/sec10` shows none of those 9 commits
touch the files in this review's scope (they are all in
`blueprint/src/sections/sec10/unbounded-spectral-theorems.tex` and
`Physicslib4/Spectral/Unbounded/*`), and I independently recompiled the scoped
declarations with `lake env lean` just now with clean results, so this is a
process/bookkeeping note rather than a soundness concern for §10.1/§10.7. No
`.git/lean-kit/approvals.json` exists, so no outstanding approvals need review.

**4. `nolint` usage in the dependency chain is justified.**
`Physicslib4/Spacetime/Causality.lean:75`: `@[nolint unusedArguments]` on
`IsGeodesic (_μ : M.SmoothPath) : Prop := True` — the unused argument is exactly the
placeholder pattern described in Finding 2 above; the docstring explains why the
argument is present but unused. Justified, no action needed beyond Finding 2.

## Lean quality (§4) notes

- `Physicslib4/GNS/Construction.lean` and `Physicslib4/GNS/NullSpace.lean` each
  independently define a private `State.toPositiveLinearMap` with identical bodies
  (`Construction.lean:54-71`, `NullSpace.lean:61-77`). Harmless (both `private`,
  scoped to their own file) but a minor duplication that a shared internal helper
  could remove.
- No one-conclusion-per-declaration violations, no duplicated-hypothesis issues, and
  no misleading docstrings were found in the six directly-scoped files.

## Integrity checklist

- Axioms: `gns_construction`, `gns_unique`, `lmm1`, `lmm2`,
  `cauchy_schwarz_inequality`, `LorentzianSpacetime.toAbstract_pullback_isBasisSet` —
  all `[propext, Classical.choice, Quot.sound]` only. Verified with `lake env lean`.
- `sorry` / `admit` / `native_decide` / `debug.skipKernelTC` / `implemented_by`: none
  in the scoped files or their direct dependency chain (grep-verified). (Elsewhere in
  the repo, out of scope: `Physicslib4/AQFT/HaagKastler/StrongDensity.lean:57` carries
  a properly marked `**Restriction:** the proof is left as sorry` — Minkowski chapter
  9 material, not part of this review's scope, noted only for completeness.)
- `nolint`: one use in the dependency chain (`Causality.lean:75`), justified — see
  Finding 4.
- `verify_commands` (`lake build`, `lake lint`) last recorded success predates HEAD by
  9 commits, none touching this review's scope — see Finding 3.
- Approvals: none in effect (`.git/lean-kit/approvals.json` absent).

## Blueprint soundness (§3)

The informal proofs in both sections are careful and internally consistent; I did not
find gaps or hidden assumptions in the GNS construction proof or in the general
covariance definitions/remarks. The `\uses{}` lists for the two in-scope theorem
nodes are accurate against what their Lean proofs actually invoke. The extensive
"Pullback metrics and cross-metric isometries" subsection of `spacetime.tex`
(dependency chain for `def:general-covariance-in-curved-spacetime`) is unusually
well-annotated about Mathlib API pitfalls (junk values of
`ContinuousLinearMap.inverse`, the two different meanings of "$(d\psi_x)^{-1}$",
etc.) and each such pitfall is explicitly resolved with a named lemma; no unflagged
gaps were found in the portion read for this review.
