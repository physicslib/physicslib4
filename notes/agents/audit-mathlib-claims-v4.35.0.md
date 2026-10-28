# Audit of Mathlib-coverage claims against v4.35.0

Scope: the 24 hits in `/tmp/claims.txt` plus a broader grep over
`blueprint/src/sections/sec10`, `Physicslib4` (excluding `scratch_*`), `home_page`,
`README.md` for other phrasings ("no Mathlib", "Mathlib provides", "would need",
"waiting on", "**Restriction:**", etc.). No `**Restriction:**` markers are currently
present in the tree.

Method: for each claim, grep `.lake/packages/mathlib/Mathlib` for the Mathlib
declaration that would falsify it, and in two cases (the `WeakDual` instance-search
claims) compile a standalone test file under `notes/agents/sources/` with
`lake env lean` to get a definitive answer rather than guessing from grep.

## 1. Pseudo-Riemannian / Lorentzian metric class

- `blueprint/src/sections/sec10/spacetime.tex:27` — "Mathlib has no pseudo-Riemannian
  class, and `Bundle.ContMDiffRiemannianMetric` carries two further fields beyond
  `contMDiff` ... `pos` ... `isVonNBounded`..."
- `Physicslib4/Spacetime/Basic.lean:35,164,174` — same claim, plus "Mathlib provides
  no lemma bridging" chart-local and bundle-section smoothness forms.

**STILL TRUE.** The Riemannian-bundle machinery was reorganized in this Mathlib
version (now spread across `Mathlib/Topology/VectorBundle/Riemannian.lean` and
`Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`, with new
`RiemannianBundle`/`IsContMDiffRiemannianBundle`/`IsRiemannianManifold` classes), but
`Bundle.ContMDiffRiemannianMetric` is still exactly the cited structure, under the
same namespace, with exactly the three fields `pos`, `isVonNBounded`, `contMDiff`
(`Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean:245-251`). No
pseudo-Riemannian/indefinite-signature variant exists anywhere (grepped
`PseudoRiemannian` across `Mathlib/Geometry/` — no hits). No bridging lemma between
`ContDiffWithinAt`-in-coordinates and the bundle-section `ContMDiff` form was found.

## 2. Diffeomorph global `mfderiv`/`symm` round-trip

- `blueprint/src/sections/sec10/spacetime.tex:1748` and `Physicslib4/Spacetime/Diffeo.lean:115`
  — "Mathlib has no `Diffeomorph` analogue of this identity ... only
  `Diffeomorph.apply_symm_apply` at the level of points."

**STILL TRUE.** `Mathlib/Geometry/Manifold/Diffeomorph.lean` has no `mfderiv`-level
cancellation lemma; grepping `mfderiv` in that file returns nothing. The only
`mfderivToContinuousLinearEquiv` machinery lives in `LocalDiffeomorph.lean` and is
for the *local* inverse (`IsLocalDiffeomorphAt`), matching the surrounding text's own
caveat, not the global `Diffeomorph.symm`.

## 3. Pullback of covariant tensor fields

- `blueprint/src/sections/sec10/spacetime.tex:1856` — "Mathlib has no pullback
  operation on covariant tensor fields."

**STILL TRUE.** `Mathlib/Geometry/Manifold/VectorField/Pullback.lean` defines
`VectorField.mpullback`/`mpullbackWithin` only for vector fields (sections of the
tangent bundle, via `(mfderiv ... x).inverse`), i.e. a contravariant pullback by
abuse of terminology, not a pullback of bilinear/covariant tensor fields. No
`Tensor`/bilinear pullback file exists under `Mathlib/Geometry/Manifold/`.

## 4. Bundle-level precomposition lemmas (`clm_precomp` etc.)

- `blueprint/src/sections/sec10/spacetime.tex:1882` — "Mathlib has no bundle-level
  precomposition lemma at all --- its composition statements, the `clm_precomp`,
  `clm_postcomp` and `clm_comp` families of
  `Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`, are for trivial bundles."

**STILL TRUE.** Read the current file: `ContMDiff.clm_precomp`, `.clm_postcomp`,
`.clm_comp` all have signatures of the shape `f : M → F₁ →L[𝕜] F₂` with `F₁, F₂`
fixed normed spaces (trivial-bundle codomain/domain), confirmed at
`Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean:118-176`. The companion route
`contMDiffAt_hom_bundle` does exist in `Mathlib/Geometry/Manifold/VectorBundle/Hom.lean`,
consistent with what the blueprint says to use instead.

## 5. `tangentCoordChange` round-trip packaging

- `blueprint/src/sections/sec10/spacetime.tex:1931` — "Mathlib has no lemma
  packaging the `tangentCoordChange` round trip (**the only** `M`-side statement
  about it, `continuousOn_tangentCoordChange`, gives mere continuity)."

**NOW FALSE (the parenthetical only).** `Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean`
now carries several other `M`-side statements about `tangentCoordChange` beyond
continuity: `tangentCoordChange_def` (unfolds to `fderivWithin`),
`tangentCoordChange_self`, `tangentCoordChange_comp` (an algebraic round-trip-style
composition law: `tangentCoordChange I x y z (tangentCoordChange I w x z v) =
tangentCoordChange I w y z v`), and `hasFDerivWithinAt_tangentCoordChange`. So
"the only M-side statement... gives mere continuity" is no longer accurate.
The main claim — that no single lemma packages the specific round trip needed to
convert between the chart-local and bundle-section smoothness idioms used here —
still appears to hold: `tangentCoordChange_comp`/`_self` are algebraic value
identities, not a smoothness-transfer lemma, and no such transfer lemma was found.
Proposed rewording (present tense, no version number): replace "the only `M`-side
statement about it, `continuousOn_tangentCoordChange`, gives mere continuity" with
"the other `M`-side statements about it (`tangentCoordChange_self`,
`tangentCoordChange_comp`, `hasFDerivWithinAt_tangentCoordChange`) are algebraic
value identities and a differentiability statement, none of which packages the
chart-to-bundle smoothness transfer needed here."

## 6. Myers–Steenrod rigidity theorem

- `blueprint/src/sections/sec10/haag-kastler-axioms-in-curved-spacetime.tex:127`,
  `home_page/index.md:77`, `Physicslib4/AQFT/HaagKastlerCurved/Concrete.lean:64`,
  `Physicslib4/Spacetime/IsometryCausality.lean:204` — "Mathlib does not provide" a
  Myers–Steenrod-type rigidity theorem (isometries connected to the identity
  preserve orientation / isometry group is a Lie group).

**STILL TRUE.** Searched `Mathlib/` (whole tree) for `myers.?steenrod`
case-insensitively: no hits. Also searched for any Lie-group structure on an
isometry-group type (`IsometryGroup`, `ChartedSpace`+`IsometryEquiv`,
`SmoothManifoldWithCorners`+`Isometry`): no hits. This remains a genuine gap.

## 7. `Star`/`InvolutiveStar`/`StarRing` instance on `UniformSpace.Completion`

- `blueprint/src/sections/sec10/haag-kastler-axioms.tex:226` — "Mathlib provides no
  `Star`, `InvolutiveStar` or `StarRing` instance on `UniformSpace.Completion`."

**STILL TRUE.** Grepped every file matching `*Completion*` in Mathlib plus a direct
pattern search for `Star (Completion`, `StarRing (Completion`, etc.: no instance
exists. `UniformSpace.Completion.instNormedRing` (cited in the same paragraph) is
confirmed to exist with hypothesis `SeminormedRing` and no commutativity gate, as
claimed. By contrast, `Mathlib.Algebra.Colimit.DirectLimit` does carry `Star`,
`InvolutiveStar`, `StarMul`, `StarModule`, `StarAddMonoid` instances
(`Mathlib/Algebra/Colimit/DirectLimit.lean:96-248`), confirming the blueprint's
contrast is accurate.

## 8. No C*-completion construction anywhere in Mathlib

- `blueprint/src/sections/sec10/haag-kastler-axioms.tex:212`,
  `Physicslib4/Analysis/CStarCompletion.lean:24` — "no enveloping C*-algebra, no
  universal C*-algebra of a `*`-algebra, no full or reduced group C*-algebra."

**STILL TRUE.** No file or declaration under `Mathlib/Analysis/CStarAlgebra/`
matches "enveloping", "universal C\*", "group C\*-algebra", or "reduced group"
(case-insensitive). `Unitization` remains the only C*-norm construction present.

## 9. No `coeStarAlgHom` / algebra-homomorphism counterpart for `Completion.coeRingHom`

- `blueprint/src/sections/sec10/haag-kastler-axioms.tex:271` — "Mathlib supplies the
  coercion only as a ring homomorphism, `UniformSpace.Completion.coeRingHom`; there
  is no `coeStarAlgHom`, and no algebra-homomorphism counterpart either, anywhere in
  Mathlib's completion files."

**STILL TRUE.** `coeRingHom` is defined in `Mathlib/Topology/Algebra/UniformRing.lean`;
no `coeAlgHom`/`coeStarAlgHom` for `UniformSpace.Completion` exists anywhere in the
tree.

## 10. Von Neumann density theorem / Kaplansky density theorem

- `blueprint/src/sections/sec10/haag-kastler-axioms.tex:726`,
  `Physicslib4/AQFT/HaagKastler/StrongDensity.lean:73` — "Mathlib has the strong
  operator topology (`PointwiseConvergenceCLM`) and the double commutant property
  of bundled von Neumann algebras (`VonNeumannAlgebra.commutant_commutant`, not a
  density result), but not the von Neumann density theorem itself... The Kaplansky
  density theorem is out of scope [i.e. also absent]."

**STILL TRUE.** `PointwiseConvergenceCLM` exists
(`Mathlib/Topology/Algebra/Module/Spaces/PointwiseConvergenceCLM.lean`).
`VonNeumannAlgebra.commutant_commutant` exists exactly as cited
(`Mathlib/Analysis/VonNeumannAlgebra/Basic.lean:139`). Grepped for
`bicommutant|double.?commutant` and `kaplansky` (case-insensitive) across all of
Mathlib: the only hits are the two files already cited by the blueprint and
unrelated UFD/dimension-theory results (`Kaplansky` the person's other, unrelated
theorems in ring/dimension theory) — no von Neumann/Kaplansky density theorem.

## 11. `VonNeumannAlgebra H` has no `⊤`

- `Physicslib4/GNS/Irreducibility.lean:428` — "available even though Mathlib does
  not equip `VonNeumannAlgebra H` with a `⊤` element."

**STILL TRUE.** `Mathlib/Analysis/VonNeumannAlgebra/Basic.lean` has only a
*docstring* remark anticipating a future `⊤ : VonNeumannAlgebra H` ("...and instead
will use `⊤ : VonNeumannAlgebra H`", line 65) — this is aspirational prose, not an
instance. Grepped for any `Top`/`CompleteLattice`/`SupSet` instance on
`VonNeumannAlgebra` anywhere in Mathlib: none exists.

## 12. No packaged `State` type for C*-algebras

- `Physicslib4/GNS/Basic.lean:32` — "Mathlib has no packaged `State` type for
  C*-algebras."

**STILL TRUE.** Grepped `^structure State|^def State` across all of Mathlib: the
only hits are unrelated tactic-internal `State` structures (`FunProp`, `GCongr`,
`Export`, etc.), nothing in `Mathlib/Analysis/CStarAlgebra/`.

## 13. Amplification commutant theorem

- `Physicslib4/GNS/Amplification.lean:28` — "the amplification commutant theorem
  `(π ⊗ 1)' = π' ⊗ B(K)`... a von Neumann algebra result that Mathlib does not
  provide."

**STILL TRUE.** Grepped `amplification` (case-insensitive) across
`Mathlib/Analysis/`: no hits.

## 14. KMS strip-Liouville / Schwarz reflection

- `Physicslib4/AQFT/KMS.lean:82,102` — "Mathlib provides Liouville
  (`Differentiable.apply_eq_apply_of_bounded`) and Phragmén-Lindelöf for strips, but
  not the holomorphic gluing across a line... Mathlib does not package that
  reflection."

**STILL TRUE** for both halves. `Differentiable.apply_eq_apply_of_bounded` exists
exactly as named in `Mathlib/Analysis/Complex/Liouville.lean:112`.
`Mathlib/Analysis/Complex/PhragmenLindelof.lean` exists. Grepped
`schwarz.?reflection` (case-insensitive) across all of Mathlib: no hits — no
horizontal-line (or any) Schwarz reflection principle is packaged.

## 15. No single named type for smooth vector fields

- `Physicslib4/Spacetime/CausalStructure.lean:34` — "Mathlib has no single named
  type for smooth vector fields."

**STILL TRUE.** `Mathlib/Geometry/Manifold/VectorField/Pullback.lean` confirms the
`VectorField` namespace holds only dot-notation lemmas about bare functions
`Π (x : M), TangentSpace I x`; grepped `^structure VectorField|^def VectorField\b`:
no hits anywhere in Mathlib.

## 16. No C*-algebraic direct-limit / amalgamated-completion construction

- `Physicslib4/AQFT/HaagKastler/QuasilocalAlgebra.lean:30` — "`Mathlib.Algebra.Colimit.DirectLimit`
  is purely algebraic... no C*-completion anywhere in `Mathlib.Analysis.CStarAlgebra`."

**STILL TRUE.** Confirmed `DirectLimit.lean` has no norm/topology fields (only
algebraic `Star`/ring structure, see item 7). No completion-flavoured file exists
under `Mathlib/Analysis/CStarAlgebra/` other than `GelfandNaimarkSegal.lean`, which
uses `UniformSpace.Completion` for the GNS pre-Hilbert-space completion, not a
colimit of C*-algebras.

## 17. Geodesics / Levi-Civita connection

- `Physicslib4/Spacetime/Causality.lean:42` — "Mathlib has no geodesics and only a
  Riemannian Levi-Civita connection."

**STILL TRUE.** Grepped `geodesic` (case-insensitive) across
`Mathlib/Geometry/`: the only hit is `Mathlib/Geometry/Group/WordMetric.lean`
(geodesic metric spaces in group theory, unrelated to manifold geodesics).

## 18. `LocallyConvexSpace ℝ (WeakDual ℂ A)` does not synthesize

- `Physicslib4/GNS/PureStateExists.lean:35` — "Concluding the existence of a pure
  state by Krein-Milman needs `LocallyConvexSpace ℝ (WeakDual ℂ A)`, which Mathlib
  does not synthesize."

**STILL TRUE — verified by compiling a test file**, not just by grep. Mathlib does
have a generic instance `LinearMap.WeakBilin.locallyConvexSpace : LocallyConvexSpace
ℝ (WeakBilin B)` (`Mathlib/Analysis/LocallyConvex/WeakDual.lean:231`), and `WeakDual
𝕜 E` unfolds to `WeakBilin (topDualPairing 𝕜 E)`, so one might expect it to fire.
Wrote `notes/agents/sources/test_weakdual_lcs.lean` with
`example : LocallyConvexSpace ℝ (WeakDual ℂ A) := by infer_instance` for
`[CStarAlgebra A]` and ran `lake env lean` on it:
`failed to synthesize instance of type class LocallyConvexSpace ℝ (WeakDual ℂ A)`.
Confirmed still absent.

## 19. WeakDual convex-combination application lemma

- `Physicslib4/GNS/PureStateExists.lean:37` — "the extreme-point-to-state transfer
  also needs weak-* coercion-algebra lemmas (`(t • φ + (1-t) • ψ) a = t • φ a +
  (1-t) • ψ a`) which Mathlib does not provide for `WeakDual`."

**STILL TRUE, with a caveat worth recording.** No named simp lemma exists
(`WeakDual.coe_add`/`coe_smul`/`add_apply`/`smul_apply` do not exist for
`WeakDual`); `simp` alone does not close the goal
(`notes/agents/sources/test_weakdual_convex.lean`). However the identity is
immediate by `rfl`
(`notes/agents/sources/test_weakdual_convex2.lean` compiles), since `WeakDual`'s
`+`/`•` unfold definitionally to the pointwise operations. The claim "which Mathlib
does not provide" is accurate (no named lemma), but is worth a parenthetical that
it is a one-line `rfl`, not a proof obligation, if the docstring is ever revised.

## 20. Heine–Borel dimension hypothesis (not a coverage gap, included for completeness)

- `Physicslib4/Spectral/Spectrum.lean:51` — "the blueprint states it for `ℂⁿ` with
  `n ≥ 1`; Mathlib has no dimension hypothesis, because what the proof uses is that
  the space is proper and Hausdorff."

**STILL TRUE.** `Metric.isCompact_iff_isClosed_bounded` is stated for
`[MetricSpace α] [ProperSpace α]` with no dimension parameter
(`Mathlib/Topology/MetricSpace/Bounded.lean:335`), matching the claim exactly.

## 21. Adjoint facts "not stated in this form"

- `Physicslib4/Spectral/Basic.lean:327` — vague claim that Mathlib's
  `ContinuousLinearMap.eq_adjoint_iff` gives the defining property but not the
  packaged C*-identities/continuity facts recorded locally.

**STILL TRUE** (low-risk, descriptive claim). `eq_adjoint_iff` confirmed to exist
verbatim at `Mathlib/Analysis/InnerProductSpace/Adjoint.lean:161`; no broader claim
to falsify here.

---

## Summary

- **STILL TRUE:** 20 (items 1–4, 6–18, 20, 21; item 19 with a minor caveat noted).
- **NOW FALSE:** 1 — item 5, the parenthetical in
  `blueprint/src/sections/sec10/spacetime.tex:1931` claiming
  `continuousOn_tangentCoordChange` is "the only" `M`-side statement about
  `tangentCoordChange`. Reword to drop the exclusivity claim (see item 5 above for
  suggested text); the main point (no packaged chart-to-bundle smoothness transfer)
  still stands.
- **UNCLEAR:** 0.

Scratch test files used for verification: `notes/agents/sources/test_weakdual_lcs.lean`,
`notes/agents/sources/test_weakdual_convex.lean`, `notes/agents/sources/test_weakdual_convex2.lean`.
