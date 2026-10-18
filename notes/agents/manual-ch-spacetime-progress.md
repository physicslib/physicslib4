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
