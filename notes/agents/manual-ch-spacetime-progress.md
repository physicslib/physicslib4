# Reference manual, chapter "Spacetime and geometry": progress log

Plan: `plan-verso-reference-manual-2026-10-17.md` (chapter 5). Part A is a docstring pass over the
declarations the chapter shows with `{docstring}`, in `Physicslib4/Spacetime/` and
`Physicslib4/Geometry/`; part B (the chapter text) is a later step. Appended after each file.

## Step 0: reconnaissance (2026-10-17)

- Read `.claude/CLAUDE.md`, the plan (chapter 5), the Haag–Kastler progress log and its review
  (docstring format rules A1–A11 and the subscript rule of doubt 1), and the blueprint section
  `blueprint/src/sections/sec10/spacetime.tex`.
- Format: first line a one-sentence summary; the mathematics for a first-year theoretical-physics
  PhD student; "Implementation note:" paragraph last; "Blueprint: <label>" as plain text;
  multi-character subscripts in parentheses (g_(φ(x))), or Unicode superscripts (I⁺(p), J⁻(q)).
- Conventions to keep consistent: ≺ is reflexive (`Relation.ReflTransGen` of
  `CausalSegmentPrecedes`); `IsCausalTrip` is strict (`Relation.TransGen`); ≪ is
  `Relation.TransGen` of single trip segments.
- `Isometry` and `identityComponent` have no blueprint node of their own (`Isometry` is described in
  lmm:isometry-pullback-metric); `orientedIdentityComponent` is in lmm:isometry-preserves-basis-sets.

## Step A1: `Spacetime/Basic.lean` (2026-10-17)

- `Spacetime` and its 15 fields. The bundle-section rationale of `contMDiff` and the
  instance-implicit `isManifold` are kept as "Implementation note:" paragraphs. Signature
  convention (-, +, +, +) stated. Built (only the pre-existing module-system notices).

## Step A2: `Spacetime/CausalStructure.lean` (2026-10-17)

- `IsTimelike`, `IsSpacelike`, `IsNull`, `TimeOrientation` and its 4 fields, `IsFuturePointing`,
  `IsPastPointing`. Checked: the zero vector is null and is both future- and past-pointing (limit
  of ±ε t(x)); `standardMinkowskiTimeOrientation` is the constant field ∂₀. The bundle-section
  rationale of `smooth` kept as "Implementation note:". Built.

## Step A3: `Spacetime/Curves.lean` (2026-10-17)

- `Path` and its 6 fields, `SmoothPath` and its 2 fields, `SmoothPath.tangent`, `Curve`,
  `SmoothCurve`, `SmoothPath.IsTimelike`, `SmoothPath.IsCausal`, `IsTimelikeSmoothCurve`,
  `IsCausalSmoothCurve`, `SmoothPath.IsFutureOriented`, `SmoothPath.IsPastOriented`,
  `IsFutureOrientedSmoothCurve`, `IsPastOrientedSmoothCurve`, `OrientedSmoothCurve`,
  `IsEndpoint`, `IsPastEndpoint`, `IsFutureEndpoint`.
- Corrected an old inaccuracy: `IsTimelikeSmoothCurve` said timelikeness is not invariant under
  orientation-reversing reparametrisations, and "all of whose representatives" for an existential
  definition. It is invariant under every reparametrisation (φ' ≠ 0); the new text states the
  existential and cites `isTimelikeSmoothCurve_ofPath_iff`.
- Noted that `IsFutureOrientedSmoothCurve` (existential, on unoriented curves) holds together with
  `IsPastOrientedSmoothCurve` for the reversed representative; the oriented notion is
  `IsFutureOrientedCurve` on `OrientedSmoothCurve`.
- Built; no line over 100 characters (checked by character count; macOS `awk length` counts
  bytes and over-reports Unicode lines).

## Step A4: `Spacetime/Causality.lean` (2026-10-17)

- `IsGeodesic`, `IsTripSegment`, `SegmentPrecedes`, `IsTrip`, `ChronologicallyPrecedes`,
  `IsCausalTripSegment`, `CausalSegmentPrecedes`, `IsCausalTrip`, `CausallyPrecedes`,
  `chronologicalFuture`, `chronologicalPast`, `causalFuture`, `causalPast`,
  `IsSpacelikeRelated`, `IsCompletelySpacelike`, `NoClosedCausalCurve`, `alexandrovBasis`,
  `alexandrovTopology`, `causalDiamond`, `chronologicalDiamond`, `IsCausallyConvex`.
- ≺ stated as reflexive (`ReflTransGen`, zero or more segments) and `IsCausalTrip` as strict
  (`TransGen`, one or more), consistently in all of them; `NoClosedCausalCurve` is ∀ p, ¬
  IsCausalTrip t p p.
- Checked: `alexandrov_eq_euclidean_standardMinkowski` (Alexandrov = Euclidean on ℝ⁴),
  `chronologicalFuture_standardMinkowski` (I⁺(p) = open forward cone), the basis theorems, and
  that `MinkowskiSpacetime` is a `Spacetime` on the type synonym `MinkowskiSpacetimeCarrier`
  (the Minkowski.lean module docstring, not in this pass's scope, still calls `MinkowskiSpacetime`
  itself a type synonym; see step on Minkowski.lean). One long line fixed. Built.

## Step A5: `Spacetime/CausalComplement.lean` (2026-10-17)

- `Spacetime.spacelikeComplement`, `LorentzianSpacetime.spacelikeComplement`, `causalClosure`,
  `IsCausallyComplete`, `CausallyCompleteRegion`, `causalComplement`. The `ClosureOperator`
  bundling and the anonymous `CompleteLattice` instance kept as "Implementation note:". All
  cited lemma names checked. The Minkowski example (causal closure of a ball is its double cone)
  is marked as not formalised. The spacetime-level `spacelikeComplement` has no blueprint line
  (the blueprint node lists the Lorentzian one). Built.

## Step A6: `Spacetime/LorentzianSpacetime.lean` (2026-10-17)

- `LorentzianSpacetime` and its 3 fields, `LorentzianSpacetime.IsBasisSet`,
  `LorentzianSpacetime.IsCompletelySpacelike`. The equivalence of the Hausdorff condition with
  strong causality is attributed to the chapter 9 theorem and marked as not formalised.
- Corrected in `Causality.lean` (`alexandrovTopology`): on a Lorentzian spacetime the diamonds
  form a basis only under the downward-directedness hypothesis of
  `isTopologicalBasis_alexandrovBasis` (and `Nontrivial`); the text now says so.
- Blueprint lines only where the node's `\lean{}` lists the declaration (the two restated
  predicates are not listed, so they have none). Built.

## Step A7: `Spacetime/Isometry.lean`, `IsometryTopology.lean`, `IsometryCausality.lean` (2026-10-18)

- `Isometry` and its 2 fields; `Isometry.identityComponent` (the Arens-style topology kept as
  "Implementation note:"); `Isometry.PreservesFutureOrientation`,
  `Isometry.futureOrientationPreserving`, `Isometry.orientedIdentityComponent`.
- D3 kept: the oriented identity component is the identity component (every connected isometry
  preserves the future orientation), not proved because it needs a Myers–Steenrod-type rigidity
  theorem; stated in `orientedIdentityComponent`'s "Implementation note:" and in
  `identityComponent`. No `**Restriction:**` line (per D3).
- The Minkowski identity component = proper orthochronous Poincaré group is marked as not
  formalised. `Isometry` has no "Blueprint:" line (no node lists it); the prose names
  lmm:isometry-pullback-metric. Built.

## Step A8: `Spacetime/Minkowski.lean` (2026-10-18)

- `StandardMinkowskiSpacetime`, `IsLorentz`, `IsProper`, `IsOrthochronous`,
  `standardMinkowskiTimeOrientation`, `MinkowskiSpacetime`.
- Module docstring (a comment) corrected: `MinkowskiSpacetime` is a `Spacetime` on the type
  synonym `MinkowskiSpacetimeCarrier`, not itself a type synonym; its manifold data is
  transported along `euclideanHomeoMinkowski`.
- Checked: `standardMinkowski_isGeodesic_iff` (geodesic iff the velocity has zero derivative at
  interior parameters: straight lines at constant velocity); ∂₀ makes v future-pointing iff
  v⁰ > 0 for timelike v; `isOrthochronous_pos_time_of_timelike`. `standardMinkowskiTimeOrientation`
  is in no `\lean{}` list, so its docstring names def:lorentz-path in prose. Built.

## Step A9: `Spacetime/LorentzCausality.lean` (2026-10-18)

- `lorentzPath`: s ↦ Λμ(s) + a; cites `lorentzPath_mfderivWithin`, `lorentzPath_isCausal`,
  `lorentzPath_isFutureOriented`, `lorentzPath_isGeodesic`, `causallyPrecedes_smul_iff` (all
  checked to exist). Called the Minkowski "counterpart" of `Isometry.pushforwardPath`, since it
  is a separate Lean definition. Built.

## Step A10: `Geometry/PseudoRiemannian/` (2026-10-18)

- `Basic.lean`: `PseudoRiemannianMetric` and its 4 fields, `Spacetime.toPseudoRiemannianMetric`.
  A drafted claim that the connection results assume `I.Boundaryless` was removed before the
  build: `LeviCivita.lean` does not use it (only the geodesic layer for spacetimes does).
- `LeviCivita.lean`: `IsMetricCompatibleWith`, `IsLeviCivitaFor` and its 2 fields,
  `koszulConnection`, `leviCivita` (the `Exists.choose` noted as "Implementation note:").
- `Flat.lean`: `flatConnection`. Built.

## Step A11: checks after the docstring pass (2026-10-18)

- Blueprint lines: every "Blueprint: <label>" added exists in `spacetime.tex`, and its `\lean{}`
  lists the declaration. `alexandrovBasis`, `standardMinkowskiTimeOrientation` and `Isometry` are
  in no `\lean{}` list, so their docstrings name the node in prose instead.
- Only docstrings and comments changed: all 14 files compared HEAD vs working tree with every
  comment removed and whitespace normalised; the code is identical. No edit was blocked by the
  guard; `lean_guard.py check --base HEAD` reports only the untracked `.claude/` files.
- Full `lake build`: passes (3403 jobs); no new warnings (the only non-module-system warnings in
  `Spacetime/` are the pre-existing "Try this" hints in the untouched `CrossMetricIsometry.lean`).
- `lake lint`: "Linting passed for Physicslib4." `python3 scripts/check_temporal_wording.py`: OK.
- No line over 100 characters; no docstring line starting with a Lean keyword in the edited text.
- Count: 73 declaration docstrings and 38 field docstrings in 14 files (declarations+fields:
  Basic 1+15; CausalStructure 6+4; Curves 17+8; Causality 21; CausalComplement 6;
  LorentzianSpacetime 3+3; Isometry 1+2; IsometryTopology 1; IsometryCausality 3; Minkowski 6;
  LorentzCausality 1; Geometry Basic 2+4, LeviCivita 4+2, Flat 1), plus the Minkowski.lean module
  docstring.

## Part B: the chapter text, `web/Manual/Spacetime.lean` (2026-10-18)

- B0: skeleton, imports and the namespaces opened before `#doc` (`Physicslib4`, `Spacetime`,
  `Spacetime.LorentzianSpacetime`, `Geometry`, `Geometry.PseudoRiemannianMetric`). Included in
  `web/Manual.lean` before the Haag–Kastler chapter, since the book follows the Chapter 10
  numbering (10.5 before 10.6).
- B1: Overview (five parts, list of main results). Built (`lake build`,
  `generate-manual`).
- B2: Design, eight subsections (structure; Minkowski and the Alexandrov topology; paths and
  curves; causal precedence by curves, ≺ reflexive and `IsCausalTrip` strict; diamonds and the
  basis theorem's hypotheses, downward vs upward directedness; causal complements and the
  orthocomplemented lattice; symmetries, isometries and the oriented identity component (D3, linked to
  the blueprint's formalization note in def:isometric-covariance-in-curved-spacetime, not the
  memo); the pseudo-Riemannian layer). Checked: dilation lemma names, `AlongPath` lemma names, the
  Levi-Civita layer does not assume `Boundaryless` (so "any finite-dimensional smooth manifold").
  Dropped a claim that the lattice is non-distributive (not in the blueprint) and a mention of Haag
  duality (not formalised). Built.
- B3: Main definitions, part 1: "Spacetimes and time orientations", "Paths, curves and geodesics",
  "Causal relations", "Diamonds and the Alexandrov topology". Statements taken from a scratch
  `lake env lean` run in /tmp (outside the repo), then confirmed by the Verso build. Added the import
  of `LorentzOrthogonal` for an `apiDocs` link; shortened a `#check` line to 60 columns. Built.
- B4: Main definitions, part 2: "Minkowski space" (three boxes, three `#check`s, the basis and
  geodesic theorems linked) and "Causal complements" (five boxes, `inf_`/`sup_causalComplement`).
  Opened `Spacetime.Isometry` and `Geometry.CovariantDerivative` before `#doc` for the later
  docstrings. Checked the proof sketch of `chronologicalFuture_standardMinkowski` against the
  lemma names in `Minkowski.lean`. Built.
- B5: Main definitions, part 3: "The Lorentz group and isometries" (seven boxes, two `#check`s)
  and "The Levi-Civita connection and geodesics" (four boxes, three `#check`s). The file-level
  opens also shorten the names in `#check` output (`IsLeviCivitaFor`, `orientedIdentityComponent`
  printed without prefix); the `leanOutput` blocks follow the build. Checked `CrossIsometry` (two
  spacetimes, ψ*g₂ = g₁), `Isometry.mfderiv_leviCivita_mpullback`; replaced a link to the home
  page's section page with the blueprint's Section 10.7. Built.
- B6: "Where to look": all 21 files of the two directories grouped in five lists, each with an
  `apiDocs` link (imports added for `LorentzCone`, `MinkowskiDilation`, `CrossMetricIsometry`, since
  the role resolves the name). Built.
- B7: full reread and checks. Fixed: the claim that bracketed `Spacetime` fields are found
  automatically (they are, because the library files register them with `attribute [instance]`;
  the text now says so); "the empty set is in `alexandrovBasis`" restricted to Minkowski space (in
  general it needs a pair with an empty diamond); `chronologicalDiamond M t p q`. All 50 blueprint
  anchors exist in `blueprint/web`; the chapter-2 anchor and the tutorial and Haag–Kastler anchors
  exist in the built HTML. `check_temporal_wording.py`: OK. Build and `generate-manual`: pass.
- Counts: 37 docstring boxes, 19 `#check`s; about 4,300 words of prose by a raw token count
  (Overview ~470, Design ~2,150, Main ~1,270, Where to look ~360), which includes URLs and inline
  maths, so somewhat over the 4,000 target in raw tokens.
- Doubts for the reviewer: (1) docstring code spans that name `Isometry` or `LorentzianSpacetime`
  stay unresolved (ambiguous with Mathlib's `Isometry` and with other namespaces), as do field
  names; the unknown-token count is comparable to the Haag–Kastler chapter. (2) The D3 paragraph
  calls the oriented identity component "a convention, not a restriction"; check this matches the
  intended reading of CLAUDE.md's `**Restriction:**` rule. (3) The Design section is long
  (~2,150 words); the curve and causal-precedence parts could be shortened if the conventions
  chapter takes them over. (4) `standardMinkowski_isGeodesic_iff` is linked, not printed, because
  its `#check` output shows a `have` from a `show` in the statement.

## Round 2: review fixes (`review-manual-ch-spacetime-2026-10-20.md`) (2026-10-20)

### Step 1: does the basis hypothesis follow from Hausdorffness? (reviewer's B1)

- The theorem: `LorentzianSpacetime.isTopologicalBasis_alexandrovBasis [Nontrivial M.Carrier]
  (hdir : ∀ B₁ ∈ alexandrovBasis M.toSpacetime M.timeOrientation, ∀ B₂ ∈ …, ∀ x ∈ B₁ ∩ B₂,
  ∃ B₃ ∈ …, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂) : IsTopologicalBasis (alexandrovBasis …)` (Alexandrov
  topology). `hdir` is verbatim the field `exists_subset_inter` of Mathlib's
  `TopologicalSpace.IsTopologicalBasis` (Mathlib's own field docstring: "the set of t ∈ s such that
  x ∈ t is directed downwards", i.e. pointwise). `sUnion_eq` is proved from the Hausdorff field and
  `Nontrivial` (`sUnion_alexandrovBasis_eq_univ`); `eq_generateFrom` is `rfl`. So `hdir` is a
  hypothesis only because the library has no proof of it for a general spacetime. Minkowski:
  `alexandrovBasis_exists_subset_inter_standardMinkowski` proves it by coordinate interpolation.
- Mathematics: the property holds in every spacetime, with no causality condition. If
  p₁, p₂ ≪ x ≪ q₁, q₂, then I⁺(p₁) ∩ I⁺(p₂) is a manifold-open neighbourhood of x (chronological
  futures are open in the manifold topology) and x is a limit of points of I⁻(x) along a past
  timelike geodesic, so some a has p₁, p₂ ≪ a ≪ x; dually b; then x ∈ I⁺(a) ∩ I⁻(b) ⊆ B₁ ∩ B₂ by
  transitivity. This is the standard fact that the diamonds are a basis of the Alexandrov topology
  of any spacetime (Kronheimer–Penrose); strong causality is what makes that topology equal to the
  manifold topology, not what makes the diamonds a basis. (Covering, too, holds in every spacetime,
  via a short timelike geodesic through each point; the library instead derives it from
  Hausdorffness.) None of this is proved in the library: openness of I⁺(p) in the manifold topology
  and the existence of short geodesics are absent.
- Verdict: the reviewer's claim ("follows via strong causality") is wrong in its reason; the
  orchestrator's doubt is right. The chapter's sentence "not implied by Hausdorffness" is also wrong
  as stated (a property that always holds is trivially implied by anything) and misleading. The
  blueprint's proof of thrm:alexandrov-topological-basis says the same ("not implied by
  Hausdorffness alone"); not edited here (blueprint prose is outside this task) — a proposal for the
  user: replace it by "holds in every spacetime (standard; not formalised), and is the hypothesis
  here because the library does not prove it".
- Wording adopted (chapter and the two docstrings): "the intersection property"; "In the standard
  theory it holds in every spacetime, since chronological futures are open in the manifold
  topology; this is not proved in the library, so the theorem takes it as the hypothesis `hdir`."

### Step 2: Part A docstring findings (2026-10-21)

- Done (uncommitted, kept): A1 (`identityComponent` first sentence), A2 (`alexandrovTopology` and
  `isTopologicalBasis_alexandrovBasis`: "the intersection property", Step 1 wording, `Nontrivial`
  mentioned; `alexandrovTopology` now also says "so the theorem takes it as the hypothesis `hdir`";
  one line over 100 characters reflowed), A3 (`IsGeodesic` endpoint remark), A4 (`IsLorentz`,
  `IsProper`, `IsOrthochronous`: "An invertible linear map Λ of ℝ⁴"), A5 (Minkowski.lean module
  docstring: "unique" dropped, transport detail only in the modelling note). Also
  `MinkowskiDirected.lean`: "downward intersection property" → "intersection property" (B2).
- Not done here: A6 and A(4) are blueprint edits (proposals in Step 4 below); the docstrings of
  `alexandrovBasis`, `standardMinkowskiTimeOrientation`, `Isometry` keep the prose node names until
  the blueprint lists them.
- `lake build` passes (3403 jobs); no warnings in the five edited files beyond the module-system notices; `lake lint` passes; no added line over 100 characters.

### Material moved out of the chapter Design section, for the conventions chapter (2026-10-21)

The Design section (B7) keeps one-sentence pointers to "the conventions chapter"; that chapter does
not exist yet, so the full text removed from `web/Manual/Spacetime.lean` is kept here verbatim.

Reflexive causal precedence (from "Causal precedence is defined by curves"):

```
On Minkowski space $`p \prec q` could be defined by vectors: $`q - p` is causal and
future-directed, or zero. The library defines it by curves, as the blueprint does, so that one
definition serves every spacetime.

* A _trip segment_ from $`p` to $`q` is a smooth curve with a representative that is a timelike,
  future-oriented geodesic with past endpoint $`p` and future endpoint $`q`; a _causal trip segment_
  has a causal (timelike or null) velocity instead.
* $`p \ll q` (`ChronologicallyPrecedes`) means a chain of _one or more_ trip segments from $`p` to
  $`q`: the transitive closure `Relation.TransGen` of single-segment precedence.
* `IsCausalTrip t p q` is the same with causal trip segments, also one or more.
* $`p \prec q` (`CausallyPrecedes`) means a chain of _zero or more_ causal trip segments: the
  reflexive-transitive closure `Relation.ReflTransGen`.

So $`\prec` is reflexive, $`p \prec p` for every $`p`, while `IsCausalTrip` is strict. This is the
Hawking–Ellis convention $`p \in J^+(p)`: the trivial case $`p = q` plays the role of a
degenerate causal curve, while causal trips are genuine curves with nowhere-vanishing velocity. The
theorem `causallyPrecedes_iff_eq_or_isCausalTrip` connects the two. Two consequences are worth
knowing. No point is spacelike to itself, so a region and its spacelike complement are disjoint.
And the causality condition `NoClosedCausalCurve` is stated with the strict relation, as "no causal
trip from $`p` to $`p`"; stated as $`\lnot(p \prec p)` it would fail in every spacetime. Under it,
$`\prec` is a partial order (blueprint
[def:causal-trip](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-trip)
and
[def:no-closed-causal-curve](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:no-closed-causal-curve)).

The closure operators are what make transitivity free: concatenating two chains is a chain, so
`causallyPrecedes_trans` is `Relation.ReflTransGen.trans`. A trip is never stored as a single
curve. On Minkowski space the definitions reproduce the usual cones: $`I^+(p)` is the open forward
light cone (`chronologicalFuture_standardMinkowski`), which needs the fact that the geodesics of
$`\eta` are the straight lines.
```

The oriented identity component, D3 (from "Symmetries"; to be reworded as in B6):

```
For a general spacetime, an `Isometry` is a $`C^\infty` diffeomorphism $`\varphi` with
$`g_{\varphi(x)}(d\varphi_x v, d\varphi_x w) = g_x(v, w)`. Isometries form a group, made a
topological group by the topology induced by $`\varphi \mapsto (\varphi, \varphi^{-1})` into
$`C(M,M) \times C(M,M)`, with the compact-open topology on each factor; including $`\varphi^{-1}`
makes inversion continuous. Its `identityComponent` is the connected component of the identity.
The curved-spacetime Axiom 5 asks for the isometries "connected to the identity", and these must
map diamonds to diamonds. An isometry preserves the causal type of vectors, but it may reverse the
time orientation, and then it can map $`I^+(p)` onto $`I^-(\varphi(p))`. The library therefore uses
`orientedIdentityComponent`: the isometries in the identity component that, with their inverses,
preserve the future orientation.

This is a convention, not a restriction. Every isometry in the identity component preserves the
time orientation, so the oriented identity component is the whole identity component; but the
proof needs a Myers–Steenrod-type rigidity theorem, which Mathlib does not provide. The library
builds orientation preservation into the definition instead of proving it, and the docstrings record
this, without a `**Restriction:**` line since the group is the intended one (blueprint
[def:isometric-covariance-in-curved-spacetime](https://physicslib.github.io/physicslib4/blueprint/chptr-haag-kastler-axioms-blueprint.html#def:isometric-covariance-in-curved-spacetime),
formalization note).
```

The regularity index (from "A spacetime is a structure"):

```
  Riemannian class itself is not instantiated, since its positivity and boundedness fields are false
  for a Lorentzian form. The regularity index is $`\infty`, which in Mathlib means $`C^\infty`; the
  top index $`\omega` would mean real-analytic.
```
- 2a done: basis-hypothesis bullet and the following paragraph use the Step 1 wording ("intersection property", hypothesis `hdir`); "not implied by Hausdorffness" removed. Web build and generate-manual pass.
- 2b done: Design shortened from ~2,170 to ~1,370 raw tokens (URLs and inline maths included,
  so about 1,300 words). Removed what the docstrings in Main repeat (field list, time-orientation
  details, transport of `MinkowskiSpacetime`, path/curve details, the four-item list of relations,
  the `ClosureOperator.Closeds` encoding, the Lorentz predicate formulas, the isometry topology, the
  geodesic definition). The reflexive-≺ rationale, the D3 discussion and the ∞/ω note are moved
  out (saved verbatim above), with one-sentence pointers to "the conventions chapter" (not linked:
  that chapter does not exist yet). The rewrite already carries 2c (D3 paragraph), the two Design
  claims of 2d (B3, B5) and the nits B8 (sentence removed with the Minkowski-cone remark, which Main
  repeats) and B9. Web build and generate-manual pass.
- 2c done (in the 2b rewrite): "This is an implementation choice, not a restriction"; no `**Restriction:**` marker in the chapter. Built with 2b.
- 2d done: "closed when nonempty" → "on Minkowski space they are closed" (B3); endpoint continuity marked as not proved in the library (B5); "a causal diamond need not be causally complete" dropped, replaced by the citation `causalDiamond_isCausallyConvex` (B4). Web build and generate-manual pass.
- 2e done: imports `Mathlib.Geometry.Manifold.VectorBundle.Riemannian` and `Physicslib4.AQFT.HaagKastlerCurved.Concrete` added (with a comment). They resolve `Bundle.ContMDiffRiemannianMetric`, `.contMDiff` and `toAbstractIdentityComponent` in the docstring boxes. Still unlinked: field names (`pos`, `isVonNBounded`, `Isom`, ...), the unqualified `ContMDiffRiemannianMetric` and the Mathlib-relative `IsLeviCivitaConnection`/`isMetricCompatible_iff` spans, and namespace names in `open … in` lines (`LorentzianSpacetime` there is now ambiguous with the AQFT namespace; harmless, Verso does not link them). Web build and generate-manual pass.
- 2f done: B2 "downward directed" → "the intersection property" in the remaining places (Main:
  basis theorem and Minkowski paragraph; "Where to look": `MinkowskiDirected.lean`). B11: sentence
  on pullback metrics and cross-metric isometries added after the cross-metric geodesic remark.
  B12: the constructor-anchor quirk recurs in both chapters for every structure shown
  (`…___mk` anchors), so it is recorded in `web/README.md` ("Writing the reference manual").
  B8, B9 and B10 done in 2b and 2e. Web build and generate-manual pass.

### Step 3: proposals for the user (blueprint not edited) (2026-10-21)

1. Proof of thrm:alexandrov-topological-basis (`blueprint/src/sections/sec10/spacetime.tex`,
   l. 1332). Current: "The intersection (downward-directedness) property is the standing
   hypothesis. [...] The directedness hypothesis is the genuinely geometric content: it is exactly
   the assertion that the Alexandrov topology has the diamonds as a base, and it is not implied by
   Hausdorffness alone; it is discharged for standard Minkowski in
   \ref{thrm:minkowski-alexandrov-basis}." Proposed replacement for those two sentences: "The
   intersection property (every point of the intersection of two diamonds lies in a diamond inside
   that intersection) is the standing hypothesis. [...] In the standard theory the intersection
   property holds in every spacetime, since chronological futures are open in the manifold
   topology; this is not proved here, so the theorem takes it as a hypothesis. It is proved for
   standard Minkowski spacetime in \ref{thrm:minkowski-alexandrov-basis}." (Drops "downward
   directedness", which names a weaker property of the family, and the false "not implied by
   Hausdorffness alone".)
2. `\lean{}` placements (reviewer's A(4)) and A6:
   - def:alexandrov-topology (l. 1137): `\lean{Physicslib4.Spacetime.alexandrovTopology,
     Physicslib4.Spacetime.alexandrovBasis}`; and correct `\leanfile` from
     `Physicslib4/Spacetime/Minkowski.lean` to `Physicslib4/Spacetime/Causality.lean` (A6).
   - def:lorentz-path (l. 1619): add `Physicslib4.standardMinkowskiTimeOrientation` (the node's
     last sentence defines it). Longer term: move that sentence into
     def:standard-minkowski-spacetime and list the declaration there.
   - lmm:isometry-preserves-classification (l. 1500): add `Physicslib4.Spacetime.Isometry`; or,
     cleaner, a new def:isometry node carrying the definition now stated in
     lmm:isometry-pullback-metric, listing `Physicslib4.Spacetime.Isometry`.
   Once listed, the three docstrings end with `Blueprint: <label>` instead of naming the node in
   prose (a docstring-only change, after the blueprint edit).

### Step 4: final checks (2026-10-21)

- `python3 scripts/check_temporal_wording.py`: OK. Word counts (raw tokens): Overview 477, Design
  1,372, Main 1,305, Where to look 364; total about 3,600. Nothing committed.
