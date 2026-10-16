# Review: tutorial chapter 3 "Worked examples" (2026-10-16)

Reviewed file: `web/Tutorial/WorkedExamples.lean` (with the plan and the writer's log). Read-only
review; the chapter is not edited. Rebuilt with `cd web && lake build && lake exe generate-tutorial
--output _out/tutorial`: build succeeds; the only warning from the chapter is Lake's module-system
warning for the Mathlib import (see 2c). Declarations checked against `Physicslib4/AQFT/HaagKastler/
{Net,LocalCommutativity,EinsteinCausality,VacuumState,QuasilocalIntertwiner}.lean`,
`GNS/{Basic,Construction,ExtremeState}.lean`, `Spacetime/{Causality,LorentzCausality}.lean`,
`AQFT/HaagKastlerCurved/{Net,Spacetime}.lean`. Side experiments were run in `/tmp/ch3rev/`
(outside the repo).

Severity: **error** (wrong), **should fix**, **nit**.

## 1. Lean and mathematics accuracy

Overall: every description of a library declaration matches its source (trivial net and its
stages, `trivialQuasilocalAlgebra`, `nonempty_haagKastlerNet` at `.{0}`, `LocalCommutativity`
binder order, `commute_ι_of_spacelike`, `LocalCommutativity.commute_ι` via
`alexandrovBasis_directed`, `localCommutativity_iff_exists_commute_ι`, `einstein_causality`,
`exists_gns_einstein_causality`, `State` fields, `gns_construction`, `gns_unique`, `IsVacuumState`,
`IsVacuumStateConcrete`, `causalSegmentPrecedes_smul`, `causallyPrecedes_smul` via
`ReflTransGen.lift`, the five `lorentzPath_*` lemmas, `covEquiv` via `choose`, `norm_covEquiv`,
`commute_covEquiv_iff`, `isSpacelikeRelated_congr`). Reflexivity of ≺ and strictness of
`IsCausalTrip` are used consistently: §3 derives irreflexivity of spacelike relatedness from
reflexivity of ≺; §4 says "chain of zero or more segments" for ≺ and "one or more" for a causal
trip; the worked proof splits `p = q` / `IsCausalTrip`. No inconsistency found.

**States.** `identityState` is a genuine `GNS.State ℂ`: positivity by `star_mul_self_nonneg`
under `ComplexOrder`, normalisation `‖id‖ = 1` (ℂ nontrivial). `vectorState Ω hΩ` is a genuine
state on `Cn n →L[ℂ] Cn n`: ⟨Ω, a*aΩ⟩ = ‖aΩ‖² ≥ 0, ‖ω‖ ≤ ‖Ω‖² = 1 by Cauchy–Schwarz and
`le_opNorm`, ‖ω‖ ≥ |ω(1)| = 1. The GNS reading of the identity state (H = ℂ, 𝒩 = {0},
⟨w,z⟩ = w̄z, π(z) = multiplication by z, Ω = 1) is correct and matches Mathlib's convention
(conjugate-linear in the first slot) and chapter 1's steps. "Its GNS representation is the defining
one on ℂⁿ" is correct up to unitary equivalence (Ω ≠ 0 is cyclic since B(H)Ω = H).

**Exercises.** All 8 solutions compile and are correct. All are solvable from the text, with one
gap (A6 below).

Findings:

- **A1 (should fix).** §2 opening: "A linear functional on ℂ is multiplication by the number ω(1),
  and normalisation forces ω(1) = 1." Normalisation gives only |ω(1)| = 1; positivity is needed
  for ω(1) ≥ 0. Fix: "…multiplication by the number ω(1). Positivity gives ω(1) = ω(1̄·1) ≥ 0
  and normalisation gives |ω(1)| = 1, so ω(1) = 1."
- **A2 (should fix).** §4 opening: "an element of the identity component of the Poincaré group is a
  map x ↦ Λx + a, where Λ preserves the Minkowski form and the direction of time." Omits det Λ = 1,
  which chapter 1 (Axiom 5) and the structure shown later (`isProper`) both include. Fix: "where Λ
  preserves the Minkowski form, has determinant 1 and preserves the direction of time."
- **A3 (should fix).** §4 "Covariance of the net", last paragraph: "Combined with the invariance of
  spacelike separation, it carries Axiom 3 for B₁, B₂ to Axiom 3 for LB₁, LB₂: the second exercise
  below." The exercise's solution uses no property of `covEquiv` at all
  (`N.commute_ι_of_spacelike _ _ (isCompletelySpacelike_smul L hs) _ _`): `covEquiv L B a` is just
  some element of `N.algebra (L • B)`. The prose and the exercise title ("covariance preserves local
  commutativity") overclaim. Fix the last sentence to: "With the invariance of spacelike separation,
  the hypothesis of Axiom 3 is itself Lorentz invariant: if B₁ and B₂ are completely spacelike
  diamonds, so are L • B₁ and L • B₂, and Axiom 3 applies to them. In particular the transported
  observables commute, as the second exercise below shows; the proof needs nothing about `covEquiv`
  beyond its type." And retitle the exercise sentence: "Show that transported observables of
  completely spacelike diamonds commute: …". Optionally add to its solution remark: "Commutation
  inside one algebra is carried by `commute_covEquiv_iff` instead."
- **A4 (should fix).** §4: "`≺` is its reflexive-transitive closure `Relation.ReflTransGen`
  ({ref "lean-in-brief-propositions"}[chapter 2, section 3])". Chapter 2 §3 covers the reflexivity of
  ≺ and `causallyPrecedes_iff_eq_or_isCausalTrip`, but never mentions `ReflTransGen`. Fix: "In Lean
  the one-segment relation is `CausalSegmentPrecedes`, and `≺` is its reflexive-transitive closure,
  Mathlib's `Relation.ReflTransGen`; this is why `≺` is reflexive
  ({ref "lean-in-brief-propositions"}[chapter 2, section 3])."
- **A5 (should fix).** §1 axiom list: "*Axiom 4.* The quasilocal algebra is ℂ again." True up to
  isomorphism only, and §2 turns on exactly this distinction. Fix: "*Axiom 4.* The quasilocal
  algebra is ℂ again, up to isomorphism."
- **A6 (should fix, solvability).** §2 vector-state exercise hint: the reverse inequality needs
  `‖(1 : Cn n →L[ℂ] Cn n)‖ = 1`, which Lean only gives once `Nontrivial (Cn n)` is in context; the
  hint does not say so, and a reader will be stuck at `norm_one`. Append to the hint: "The unit
  operator has norm 1 only on a nonzero space: first give Lean an instance `Nontrivial (Cn n)`,
  using `Ω ≠ 0`."
- **A7 (nit).** §1: "The algebras of the trivial net lie in `Type`, so the theorem is stated for
  `HaagKastlerNet.{0}`" directly under output that shows `Nonempty HaagKastlerNet`. Add: "(Lean's
  display omits the universe)".
- **A8 (nit).** §1 bullet on `noncomputable`: "Mathlib defines parts of the structure of `ℂ`, such
  as its norm, by non-constructive means." More precise: "the real numbers, and with them the norm
  of `ℂ`, are not computable in Lean."
- **A9 (nit).** §1 curved aside: "a group of isometries connected to the identity" — the interface
  `HaagKastlerCurved.LorentzianSpacetime` has an abstract group `Isom` acting on `Carrier`; nothing
  says "connected to the identity". Fix: "a group, standing for the isometries connected to the
  identity, acting on the points…". Also "The proofs of isotony, locality and covariance are those
  above" → "repeat those above".
- **A10 (nit).** §2 "builds `H` as Mathlib's `PositiveLinearMap.GNS`, the completion of the quotient
  𝔄/𝒩". Mathlib's `GNS` is `UniformSpace.Completion f.PreGNS`, with `PreGNS f := A` carrying the
  semi-inner product; the Hausdorff completion identifies null vectors, so the quotient is implicit.
  Fix: "the completion of 𝔄 with the semi-inner product ω(a\*b), in which the null vectors are
  identified with 0: steps 2 and 3 of chapter 1 at once."
- **A11 (nit).** §2 `IsVacuumState` prose: "in a GNS representation of ω with unitaries implementing
  the action" — the definition asks for some representation reproducing ω, with no cyclicity. Fix:
  "in some representation reproducing ω, with unitaries implementing the action".
- **A12 (nit).** §3 overlap remark: "an observable localised in the overlap belongs to both
  algebras". The overlap of two diamonds need not be a diamond, and by isotony an observable is
  embedded, not shared. Fix: "an observable localised in a diamond inside the overlap embeds, by
  isotony, into both algebras, and nothing makes it commute with the other observables of either."
- **A13 (nit).** §3 first exercise: "A proof of `IsCompletelySpacelike M t B₁ B₂` is a function:
  given points of `B₁` and `B₂`, it returns a proof…". The solution `hs x hx₁ x hx₂` also passes
  membership proofs. Fix: "given a point of `B₁` with a proof of membership, and a point of `B₂` with
  one, it returns…".
- **A14 (nit).** §4 worked proof: the two `_` in `(causallyPrecedes_iff_eq_or_isCausalTrip _ _).mp h`
  (spacetime and time orientation) are not explained, whereas later `_`s are. Add to the `rcases`
  bullet: "The two `_` are the spacetime and the time orientation."

## 2. The writer's four flagged points

**2a. No state on `trivialHaagKastlerNet.quasilocal`.** Confirmed: `trivialHaagKastlerNet.quasilocal
.carrier = ℂ` is not provable by `rfl` (checked), since `quasilocal` is
`Classical.choice (exists_quasilocalAlgebra …)`. The prose is accurate ("is not literally ℂ";
"The library constructs no vacuum state"). It is adequate for chapter 3; building the state is not
a tutorial-sized step: it needs a unital \*-homomorphism `N.quasilocal.carrier →⋆ₐ[ℂ] ℂ` (every
element is a norm limit of elements of ℂ·1, a closed subspace), after which the library's
`GNS.State.comp` (`GNS/ExtremeState.lean:489`) pulls `identityState` back. Proposed fix
(should fix, clarity), in "States of a net":
- After "For a general net `N`, the quasilocal algebra is `N.quasilocal`, chosen once and for all
  from the existence theorem" add "by `Classical.choice`", and after the `noncomputable example`
  add: "`trivialQuasilocalAlgebra` is a quasilocal algebra of the trivial net, but not the one
  `trivialHaagKastlerNet.quasilocal` chosen by the library, and the predicates below are stated for
  the chosen one."
- Replace the last sentence by: "…but proving it means first building a state on the chosen
  `N.quasilocal.carrier`, which is isomorphic to ℂ but not literally ℂ. One route: show that every
  element is a scalar multiple of the unit, which gives a unital \*-homomorphism to ℂ, and pull
  `identityState` back along it with the library's `GNS.State.comp`." This is a natural project
  for chapter 4.

**2b. `mul_comm (G := ℂ)`.** The explanation is correct, not misleading. Checked: `mul_comm a b`
fails with "failed to synthesize `CommMagma (trivialLocalNet.algebra B)`"; so do
`mul_comm (a : ℂ) b` (the ascription does not change the type of the local `a`) and
`unfold trivialLocalNet at *` followed by `mul_comm a b`. Type class search unfolds only reducible
definitions and instances, and `trivialLocalNet` is a plain `def`; the instance it does find is
`instCStarAlgebra`, which says nothing about commutativity. Proposed wording (nit, more precise)
for the last two sentences of the `exact` bullet:
> The named argument `(G := ℂ)` tells Lean which type to use. Without it, Lean takes the type from
> `a`, which is `trivialLocalNet.algebra B`, and looks for a commutative multiplication on it. Type
> class search unfolds only definitions marked reducible, and `trivialLocalNet` is an ordinary
> `def`, so the search sees only the C\*-algebra instance supplied by the field `instCStarAlgebra`,
> which does not include commutativity. With `G := ℂ`, Lean instead checks, unfolding definitions,
> that `a` and `b` have type `ℂ` and that the two multiplications agree.
Optionally contrast with chapter 2, where `mul_comm _ _` works because the goal is already in `ℂ`.

**2c. The Mathlib import.** Harmless (the library's own files trigger the same warning, e.g.
`HaagKastlerCurved/Net.lean`), but **avoidable**: the import is redundant. With only the three
`Physicslib4` imports, `CStarAlgebra (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))`
and `StarOrderedRing (…)` are found by `inferInstance`/`#synth`, and the full vector-state code
(`Cn`, `vectorFun`, `vectorFun_nonneg`, `norm_vectorFun`, `vectorState`) elaborates (checked in
`/tmp/ch3rev/V.lean`). Fix (should fix): delete line 7,
`import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`, rebuild, and drop the warning note from
the log.

**2d. Section 1 length (≈1,220 words).** Proposed cuts, target ≈ 950:
1. Opening paragraph: merge "Before building anything physical … would prove nothing." into one
   sentence: "First, can the conditions be met at all? If not, every theorem about Haag–Kastler nets
   would hold vacuously." (−25)
2. Isotony paragraph ("The field `map` takes five arguments…"): keep the first two sentences; replace
   the `change`/`simpa` explanation with "The three laws are statements about the identity, proved
   by `simpa` with `Function.injective_id` and by `rfl`." (−55)
3. `noncomputable` bullet: shorten as in A8. (−10)
4. Paragraph after `#check nonempty_haagKastlerNet`: move the sentence "The quasilocal algebra needs
   no extra work … `trivialQuasilocalAlgebra`" to §2 "States of a net", where it is used. (−40 here)
5. "The lesson cuts both ways." paragraph: drop "Nothing is measured, and nothing propagates." and
   shorten the blueprint sentence to "The trivial net has no blueprint entry of its own; it is the
   library's witness that `def:haag-kastler-net` is consistent." (−30)
6. Curved aside: cut the interface sentence ("The type `HaagKastlerCurved.LorentzianSpacetime` is an
   interface that records …") to "It takes as argument an interface recording only what the axioms
   use: points, diamonds, complete spacelike separation and a group acting on points." and the
   fields sentence to "Two fields differ: `localAlgebra` (the curved Axiom 4, which holds for every
   net by `HaagKastlerCurved.localAlgebra_of`) and `isometricCovariance`." (−70)
7. Exercise 2 solution remark: drop the `finrank_algebra_smul` sentence or shorten to one clause.
   (−20)

## 3. Prose and style

Generally clear, crisp and present tense; no history narration; no version claims. Continuity with
chapters 1–2 is good (the M₂(ℂ) exercise, the four GNS steps, the Weyl exercise, chapter 2's
`mul_comm_algebra_empty` all exist as referenced).

- **P1 (nit).** Openings: §1 and §4 both begin "As you will recall from chapter 1"; §2 "Recall from
  chapter 1", §3 "You will remember". Vary §4: "Chapter 1 described the identity component of the
  Poincaré group: its elements are the maps …".
- **P2 (nit).** §3 exercise solution: "`¬ P` is `P → False`" re-explains chapter 2 §3 (line 295).
  Write "As in chapter 2, `¬ P` is `P → False`, so…".
- **P3 (nit).** §3 "exists_gns_einstein_causality: … the GNS triple of the previous example can be
  chosen so that spacelike observables commute" suggests a choice matters; the commutation holds in
  every representation. Fix: "for every state on 𝔘 there is a GNS triple, as in the previous
  example, in which spacelike observables commute as operators on ℋ_ω."
- **P4 (nit).** §5 "the Lean declaration is checked against it" — passive and vague. Fix: "the Lean
  statement is reviewed against it."
- **P5 (nit).** §2 vector-state solution: "Its GNS representation is the defining one on ℂⁿ" — add
  "up to unitary equivalence, since every vector of ℂⁿ is aΩ for some a" to make the claim checkable.
- **P6 (nit).** §3 "Lean shows the law as follows:" — "The law reads:" is crisper.

## 4. Rendering

Checked `web/_out/tutorial/html-multi/Worked-examples/index.html` and a headless-Chrome DOM dump
(after KaTeX ran).

- Maths: 127 inline and 2 display spans, all rendered by KaTeX; 0 `katex-error`.
- Code: 44 highlighted Lean blocks. The 4 library-source excerpts (`trivialLocalNet`,
  `trivialLocalNetIsotony`, `trivialHaagKastlerNet`, `InhomogeneousLorentzGroup`) are plain ```
  blocks and so unhighlighted, the same convention as chapter 2; the last two are pinned by hidden
  checks, the first two only partly (by the `rfl` examples). Nit: acceptable.
- `goals`: 9 `goals` blocks, goal states as described in the prose (spot-checked: `isPositive`,
  faithful exercise, trivial locality). 8 collapsible `<details class="solution">`.
- Figure "diamond" present.
- Links: all internal hrefs resolve to existing pages and ids, except the chapter-level fragments
  `AQFT-in-brief/#aqft-in-brief`, `Lean-in-brief/#lean-in-brief` (no matching `id`; the page opens at
  the top, so harmless; shared with chapters 1–2). Nit, infrastructure, not this chapter.
- Long `#check` output lines (>60 columns) wrap via the existing CSS, as the log says.

## Verdict and top 5 fixes

**Verdict:** accurate and close to ready. No errors in the Lean; every solution compiles and is
correct; the states are genuine states and the GNS reading is right; reflexive ≺ / strict causal
trip is consistent throughout. Six should-fix items (two small mathematical slips, one overclaim,
one wrong cross-reference, one solvability gap, one redundant import) plus the 2a clarification;
the rest are nits. Approve after the fixes below.

Counts: errors 0; should fix 8 (A1–A6, 2a, 2c); nits 16 (A7–A14, P1–P6, 2b wording, rendering
links/excerpts), plus the section 1 cuts.

Top 5:
1. A3: reword the covariance paragraph and the second §4 exercise so they do not claim that the
   proof uses properties of `covEquiv`.
2. A1 and A2: positivity, not normalisation alone, forces ω(1) = 1; add det Λ = 1 to the §4
   opening.
3. 2c: delete `import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap` (redundant; removes the
   warning).
4. A6: add the `Nontrivial (Cn n)` hint to the vector-state exercise.
5. A4 and 2a: fix the `ReflTransGen` cross-reference; in "States of a net" say that
   `trivialQuasilocalAlgebra` is not the chosen `N.quasilocal` and sketch the `State.comp` route.
