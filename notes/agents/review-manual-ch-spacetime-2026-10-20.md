# Review: reference manual chapter "Spacetime and geometry" and its docstring pass (2026-10-20)

Scope: commit `be40b01` (docstrings in `Physicslib4/Spacetime/`, `Physicslib4/Geometry/PseudoRiemannian/`) and commit `8e50772` (`web/Manual/Spacetime.lean`). Read-only review.

Severity: error / should fix / nit.

## A. Docstring pass (`be40b01`)

### What was checked and is correct

- **Only docstrings/comments changed.** All 14 `Physicslib4/` files of `be40b01` compared with
  `be40b01^`, with every `--` and nested `/- -/` comment removed (string literals kept) and
  whitespace normalised: identical in all 14. No library file changed between `be40b01` and HEAD.
- **Cited names.** All 191 backticked names in the added lines resolve: in the library, or in Mathlib
  (`ContMDiff.clm_bundle_apply₂`, `CovariantDerivative.IsLeviCivitaConnection`,
  `CovariantDerivative.isMetricCompatible_iff`, `ContMDiff.mpullback_vectorField`,
  `Bundle.contMDiffAt_section`, `Subgroup.connectedComponentOfOne`,
  `Bundle.ContMDiffRiemannianMetric`, `Equivalence.eqvGen_iff`, ...).
- **≺ reflexive / `IsCausalTrip` strict** is stated consistently in `CausalSegmentPrecedes`,
  `IsCausalTrip`, `CausallyPrecedes`, `causalFuture/Past`, `IsSpacelikeRelated`,
  `NoClosedCausalCurve` (∀ p, ¬ IsCausalTrip t p p, and "not ¬(p ≺ p)"), `causalDiamond`; matches
  the code (`ReflTransGen` / `TransGen` of `CausalSegmentPrecedes`).
- **Basis hypotheses.** `alexandrovTopology` says the diamonds form a basis on a Lorentzian
  spacetime only under the hypothesis of `LorentzianSpacetime.isTopologicalBasis_alexandrovBasis`;
  on standard Minkowski unconditionally. Correct (but see A3 on wording).
- **D3.** `identityComponent`, `futureOrientationPreserving`, `orientedIdentityComponent` say: the
  groups coincide, the proof needs a Myers–Steenrod-type theorem, so orientation preservation is in
  the definition. No `**Restriction:**` line. Matches the formalization note of
  def:isometric-covariance-in-curved-spacetime (`haag-kastler-axioms-in-curved-spacetime.tex`
  l. 127) word for word in substance. Correct.
- **Levi-Civita / geodesic.** `IsMetricCompatibleWith` (Leibniz rule at points where X, σ, τ are
  differentiable) and `IsLeviCivitaFor` match the code; Christoffel formula correct; uniqueness only on
  differentiable fields correct; `leviCivita` as `Exists.choose` noted. `IsGeodesic` matches the
  code (interior s, every smooth X with X(μ(t)) = μ̇(t) eventually near s, ∇_X X (μ(s)) = 0); chart-free;
  affine parametrisation stated ("a reparametrisation μ ∘ σ is again a geodesic only when σ is
  affine").
- **Other facts checked:** `SmoothPath.nonvanishing` makes "null velocity is non-zero" right;
  `IsPastEndpoint`+`IsFutureEndpoint` force Σ = [a, b]; ∂₀ makes timelike v future-pointing iff
  v⁰ > 0; `chronologicallyPrecedes_pushforward` needs `PreservesFutureOrientation` (stated);
  `isLeviCivitaFor_flatConnection` needs a constant metric (stated); `FaithfulSMul` instance exists
  ("acting faithfully"); B⊥ causally convex (true and named); PT has det +1 (`IsProper` text right).
- **Format:** one-sentence first lines, "Implementation note:" last before "Blueprint: <label>",
  plain-text labels, parenthesised subscripts (g_(φ(x)), Γ^ρ_(μν), ∇_(μ̇)), present tense, no
  narrated history found.

### Findings

A1. **should fix**: `IsometryTopology.lean`, `identityComponent`, first sentence: "the isometries that
can be connected to the identity by a continuous path, or more precisely that lie in the connected
component of 1". Path component and connected component are different notions; the sentence leads
with the one that is not the definition. Replace with: "The identity component of the isometry
group: the connected component of the identity, for the compact-open group topology."

A2. **should fix**: `Causality.lean`, `alexandrovTopology`: "there the diamonds form a basis whenever
they are downward directed". The hypothesis `hdir` is the basis intersection property (every point
of B₁ ∩ B₂ lies in a diamond inside B₁ ∩ B₂), which is pointwise, not downward directedness of the
family; and the `Nontrivial` hypothesis is unmentioned. Replace with: "and there the diamonds form a
basis whenever every point of the intersection of two diamonds lies in a diamond inside that
intersection (`LorentzianSpacetime.isTopologicalBasis_alexandrovBasis`, for a spacetime with at least
two points). Mathematically this holds in every Lorentzian spacetime, through strong causality (the
chapter 9 theorem), which is not formalised." The same wording should go into the theorem's own
docstring (it says "downward-directed (the intersection property)"), and into the chapter (B3).

A3. **nit**: `Causality.lean`, `IsGeodesic`: "at an endpoint of Σ it follows by continuity" is a
claim the library neither states nor proves. Write "at an endpoint of Σ it would follow by
continuity of the velocity, which the library does not state."

A4. **nit**: `Minkowski.lean`, `IsLorentz`, `IsProper`, `IsOrthochronous`: "A linear map Λ : ℝ⁴ → ℝ⁴";
the argument is a linear equivalence `SpacetimeModel ≃ₗ[ℝ] SpacetimeModel`. Write "An invertible
linear map Λ of ℝ⁴".

A5. **nit**: `Minkowski.lean` module docstring has two near-duplicate bullets about `MinkowskiSpacetime`
(Main definitions l. 36 and Modelling notes l. 50); the first also says "the unique spacetime" for
`StandardMinkowskiSpacetime` (l. 31, pre-existing). Keep the transport detail only in the modelling
note; drop "unique".

A6. **nit** (blueprint, side finding): def:alexandrov-topology has
`\leanfile{Physicslib4/Spacetime/Minkowski.lean}`, but `alexandrovTopology` and `alexandrovBasis` are
in `Causality.lean`. Correct the `\leanfile`.

### A(4): the three declarations without a blueprint citation

- `alexandrovBasis` → add to `\lean{}` of **def:alexandrov-topology** (the node defines the family:
  "generated by the basis consisting of all sets I⁺(p) ∩ I⁻(q)"). Then replace the docstring's last
  sentence by `Blueprint: def:alexandrov-topology`.
- `standardMinkowskiTimeOrientation` → add to `\lean{}` of **def:lorentz-path**, whose last sentence
  defines it ("The standard time orientation ... is e₀ = ∂₀"). Better long-term: move that sentence
  into def:standard-minkowski-spacetime and list it there (blueprint prose: a proposal for the
  lean-blueprint agent, not a Lean change).
- `Isometry` → add to `\lean{}` of **lmm:isometry-preserves-classification** (the first isometry node,
  `\leanfile{Physicslib4/Spacetime/Isometry.lean}`, already listing `Isometry.preserves_self` etc.;
  lmm:isometry-pullback-metric refers back to it for "the sense used throughout"). A cleaner option is
  a new def:isometry node carrying the sentence now in lmm:isometry-pullback-metric; draft it as a
  proposal under `notes/agents/`. Either way, the docstring then ends `Blueprint: <label>`.

## B. Chapter `web/Manual/Spacetime.lean` (`8e50772`)

Rebuilt: `cd web && lake build && lake exe generate-manual --output _out/manual` passes (only
pre-existing unused-variable notices). Output: `web/_out/manual/html-multi/Spacetime-and-geometry/`.

### What was checked and is correct

- **Links.** All blueprint anchors (`#def:…`, `#lmm:…`, `#thrm:…`, `#sctn:…`) exist in
  `blueprint/web/chptr-haag-kastler-axioms-blueprint.html`; the chapter-2 page exists; all tutorial and
  Haag–Kastler-chapter anchors exist in `_out/` (pages carry `<base href="./../">`, so `../tutorial/`
  resolves to the sibling book); every `{apiDocs}` href points to the file that declares the name;
  `home_page/sec10-5-spacetime.md` exists.
- **Names.** Every name in a prose code span exists (library or Mathlib); all 21 files of the two
  directories are listed in "Where to look".
- **Claims checked against code/blueprint:** ∞ vs ω index; Riemannian class not instantiated
  (`pos`, `isVonNBounded`); `alexandrovTopology` reducible def and the `@IsOpen` idiom; endpoints by
  extremality; `causallyPrecedes_trans` is `ReflTransGen.trans`; the covering argument from T2 (a point
  in no diamond has only `univ` as neighbourhood); diamonds empty unless p ≪ q (holds in general);
  dilation lemmas; `orientedIdentityComponent` includes g⁻¹; `alexandrovBasis_image_of_mem_…` proof via
  φ(I^±(p)) = I^±(φ(p)) and injectivity; Levi-Civita on any finite-dimensional manifold, boundary
  allowed; `CrossIsometry` ψ*g₂ = g₁; all printed `#check` outputs match the build.
- **Coverage of §10.5:** spacetimes, vectors, time orientation, paths/curves/endpoints, geodesics,
  trips and the three relations, futures/pasts, spacelike separation, causality condition, both
  diamonds, causal convexity, Alexandrov topology and both basis theorems, Lorentzian spacetime,
  causal complements and the lattice, Lorentz group and `lorentzPath`, dilations, isometries and
  both components, the pseudo-Riemannian layer: all present. Only the subsection "Pullback metrics
  and cross-metric isometries" (spacetime.tex l. 1710 ff.) is reduced to one sentence (B11).
- **Style:** present tense, "As you will recall" for the Haag–Kastler needs and the topology; the
  tutorial is linked, not repeated; `check_temporal_wording.py` OK.

### Findings

B1. **error** (l. 216–218): "This is genuine geometry and is not implied by Hausdorffness". False as
mathematics, and it contradicts the `LorentzianSpacetime` docstring shown in the same chapter (a
Hausdorff Alexandrov topology is equivalent to strong causality; under strong causality every
neighbourhood of a point contains a diamond around it, which gives the intersection property). What
is true is that the library does not derive it. Replace the bullet with:
"* every point in the intersection of two diamonds lies in a diamond inside that intersection.
  Mathematically this follows from the Hausdorff condition, through strong causality (the chapter 9
  theorem, which is context and is not formalised), so
  `LorentzianSpacetime.isTopologicalBasis_alexandrovBasis` takes it as the hypothesis `hdir`. On
  standard Minkowski space it is proved, and the diamonds form a basis unconditionally."

B2. **should fix** (l. 216, 221–222, 546, 616; "Where to look" l. 914): "downward directed" names the
pointwise basis intersection property, which is stronger than downward directedness of the family
(a common diamond below B₁ ∩ B₂ need not contain a given point). Call it "the intersection property"
throughout, e.g. l. 221: "The intersection property should not be confused with upward
directedness, that any two diamonds lie in a common diamond (`alexandrovBasis_directed`). The first
makes the diamonds a basis; the second makes ..."; l. 546: "under the intersection hypothesis
`hdir`"; l. 616: "The diamonds of Minkowski space have the intersection property"; l. 914: "the
diamonds have the intersection property, are upward directed, and form a basis". Same for A2.

B3. **should fix** (l. 231–232): "they are closed when nonempty". True on Minkowski space; J^±(p) need
not be closed in a general spacetime. Write "but on Minkowski space they are closed, and they are
not the regions of the net".

B4. **should fix** (l. 693–694): "although a causal diamond need not be causally complete". Not in the
blueprint and not proved; on Minkowski space a closed double cone J⁺(p) ∩ J⁻(q) is causally complete
(a point of J⁻(q) \ J⁺(p) is causally related to a point outside J⁺(p) ∪ J⁻(q)). Drop the clause:
"..., as is every causal diamond (`causalDiamond_isCausallyConvex`)."

B5. **should fix** (l. 316–317): "at an endpoint of Σ it follows by continuity and is not imposed"
(unproved; mirrors A3). Write "the condition is imposed at interior parameters only; at an endpoint
it would follow by continuity."

B6. **should fix** (l. 279–285, the D3 paragraph; doubt 2): "convention" suggests a choice among
equivalent options (like a sign convention); here the definition differs from the intended one in Lean
and coincides with it only by an unproved theorem. Proposed:
"This is an implementation choice, not a restriction. Every isometry in the identity component
preserves the time orientation, so the oriented identity component is the whole identity component;
the proof needs a Myers–Steenrod-type rigidity theorem, which Mathlib does not provide, so the library
puts orientation preservation into the definition instead of proving it. Since the group is the
intended one, the docstrings record this as an implementation note, not as a restriction (blueprint
def:isometric-covariance-in-curved-spacetime, formalization note)."
This also removes the project-internal `**Restriction:**` marker from reader-facing prose; the
conventions chapter can explain restriction lines and link back.

B7. **should fix** (Design, ~2,150 words; doubt 3): much of it restates docstrings that the Main
section shows in full. Cuts (≈ 850 words, to ≈ 1,300):
- "A spacetime is a structure": keep the first paragraph and one sentence per bullet ("Smoothness is
  the bundle condition of Mathlib's Riemannian metrics, so Mathlib's bundle API applies; the
  Riemannian class itself is not used, since its positivity fields fail." / "Time orientation is
  separate data, an argument of every causal notion: `p ≪[M, t] q`."). Move the ∞ vs ω sentence to the
  conventions chapter. (−120)
- "Minkowski space and the Alexandrov topology": keep the reminder and the "two Minkowski spacetimes"
  point in three sentences; the transport details are in the `MinkowskiSpacetime` docstring. (−100)
- "Paths and curves": reduce to the two design points: non-vanishing velocity (null paths move) and
  endpoints by extremality; the rest is in the `Path`/`SmoothPath` docstrings and l. 375–378. (−130)
- "Causal precedence is defined by curves": drop the four-item list (the three docstrings follow in
  Main) and keep the reflexive/strict paragraph and the closure-operator remark; the convention's
  full rationale moves to the conventions chapter item "reflexive causal precedence". (−150)
- "Causal complements": keep the Galois-connection and orthocomplement sentences; the
  `ClosureOperator.Closeds` encoding is in the `CausallyCompleteRegion` docstring. (−80)
- "Symmetries": drop the first paragraph's predicate formulas (the three docstrings follow); keep
  the curved-spacetime paragraph, a two-sentence D3 summary with a forward reference to the
  conventions chapter (which the plan lists as "the oriented identity component (the D3 note)"), and
  the dilation paragraph. (−150)
- "The pseudo-Riemannian layer": the geodesic paragraph repeats the `IsGeodesic` docstring almost
  verbatim; keep one sentence ("A geodesic is defined chart-free, as ∇_(μ̇) μ̇ = 0 tested against
  smooth extensions of the velocity, so it is affinely parametrised"). (−120)

B8. **nit** (l. 202–203): "which needs the fact that the geodesics of η are the straight lines".
Only one direction is used (straight segments are geodesics, for ⊇). Write "whose proof uses that
straight segments are geodesics of η".

B9. **nit** (l. 302–304): "tensorial in two of its arguments, so it defines a bilinear form at each
point". Write "tensorial in X and Z, so for each Y it defines at every point a bilinear form in
X(x) and Z(x)".

B10. **nit** (rendering; doubt 1): of 190 highlighted inline spans in the docstring boxes, 11 stay
unresolved. Two are fixable by imports in `web/Manual/Spacetime.lean`:
`import Mathlib.Geometry.Manifold.VectorBundle.Riemannian` (for `Bundle.ContMDiffRiemannianMetric`
and `.contMDiff`) and `import Physicslib4.AQFT.HaagKastlerCurved.Concrete` (for
`AQFT.HaagKastlerCurved.LorentzianSpacetime` and `toAbstractIdentityComponent`). The rest are field
names (`pos`, `isVonNBounded`, `Isom`) and expressions with free variables (`p ≪[M, t] q`, `g • x`);
accept.

B11. **nit** (coverage, l. 865–867): the blueprint subsection "Pullback metrics and cross-metric
isometries" gets one sentence. Add: "The pullback metric ψ*g and cross-metric isometries
(`Pullback.lean`, `CrossMetricIsometry.lean`) carry all the results above between two spacetimes;
they serve general covariance and are described with it."

B12. **nit** (rendering, infrastructure): docstring spans `LorentzianSpacetime`, `toSpacetime` and
`alexandrov_t2` all link to the anchor `#Physicslib4___Spacetime___LorentzianSpacetime___mk` (the
constructor), not to the structure or the field. Verso quirk; record in `web/README.md` if it recurs.

## Answers to the writer's doubts

1. **Unlinked `Isometry`/`LorentzianSpacetime`.** In the docstring boxes these names do resolve and
   link (the file-level `open`s work). The unresolved `Isometry`, `LorentzianSpacetime`,
   `Spacetime`, `Physicslib4` tokens in the HTML are the namespace names in the `open … in` lines of
   the `#check` blocks, which Verso does not link; harmless. Plain Lean with the chapter's opens
   resolves both names uniquely (checked with `lake env lean`). Fully qualifying names in the
   library docstrings would not help and would hurt doc-gen4 and hovers. The real fixes are the two
   imports of B10.
2. **D3 wording.** "Implementation choice, not a restriction" is better than "convention"; see B6.
3. **Design length.** See B7: cut ≈ 850 words of restated docstrings; move the reflexive-≺ rationale
   (in full), the D3 discussion (in full) and the ∞/ω note to the conventions chapter, leaving
   two-sentence summaries with forward references here.
4. **`standardMinkowski_isGeodesic_iff` linked, not printed.** Right: its `#check` output shows the
   `have` of a `show` in the statement. The prose ("paths with zero acceleration ... straight lines at
   constant velocity") states the content. Do not change the library statement for the manual.

## Verdict and top 5

Verdict: **ready after small fixes.** The docstring pass changes no code (verified on all 14 files),
is accurate on every point the brief named (≺ reflexive / `IsCausalTrip` strict; D3 without a
Restriction line; chart-free Levi-Civita and affinely parametrised geodesics), and keeps the agreed
format. The chapter is accurate except for one false claim (B1) and three loose ones (B3–B5); all
links resolve. Counts: A 6 findings (2 should fix, 4 nits; no errors); B 12 findings (1 error,
6 should fix, 5 nits).

Top 5:
1. B1: "not implied by Hausdorffness" is false; the hypothesis follows via strong causality and is
   only not derived in the library.
2. B2 + A2: rename "downward directed" to "the intersection property" (chapter and
   `alexandrovTopology` / `isTopologicalBasis_alexandrovBasis` docstrings).
3. B7: cut the Design section by ≈ 850 words of restated docstrings; move the reflexive-≺ and D3
   rationales to the conventions chapter.
4. B6: D3 paragraph: "an implementation choice, not a restriction", without the internal marker.
5. B3/B4/B5 + A3: qualify "closed when nonempty" to Minkowski; drop "a causal diamond need not be
   causally complete"; "follows by continuity" at endpoints as an unproved remark. Then A(4): add
   `alexandrovBasis` to def:alexandrov-topology, `standardMinkowskiTimeOrientation` to
   def:lorentz-path, `Isometry` to lmm:isometry-preserves-classification.
