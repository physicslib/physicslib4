# Review: tutorial chapter 2 "Lean in brief" (2026-10-16)

Reviewed: `web/Tutorial/LeanInBrief.lean` and `web/_out/tutorial/html-multi/Lean-in-brief/index.html`,
rebuilt with `cd web && lake build && lake exe generate-tutorial --output _out/tutorial` (both succeed).
Read-only review; nothing else was edited. Severities: **error** / **should fix** / **nit**.

## 1. The ≺ question

### The library

`Physicslib4/Spacetime/Causality.lean:162-175`:

```lean
/-- A *causal trip* from `p` to `q`: a curve which is piecewise a
future-oriented causal geodesic, i.e. a finite chain of causal trip
segments. Encoded as the transitive closure of single-segment causal
precedence. -/
def IsCausalTrip (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  Relation.TransGen (CausalSegmentPrecedes M t) p q

/-- *Causal precedence*: `p ≺ q` iff there exists a causal trip from `p`
to `q`, relative to a fixed time orientation. -/
def CausallyPrecedes (t : M.TimeOrientation) (p q : M.Carrier) : Prop :=
  IsCausalTrip M t p q

@[inherit_doc] scoped notation:50 p " ≺[" M ", " t "] " q =>
  CausallyPrecedes M t p q
```

A segment (`IsCausalTripSegment`, l. 147) needs a `SmoothPath`, and `SmoothPath`
(`Curves.lean:105-125`) has a parameter space with two distinct points (`nontrivial`) and a
**non-vanishing** tangent (`nonvanishing`). `TransGen` is the transitive, not reflexive-transitive,
closure. So constant curves are excluded and `≺` is **not reflexive**: `p ≺[M, t] p` holds only if
there is a closed causal trip through `p`. In Minkowski spacetime (no closed causal curves) `≺` is
irreflexive, and `causalFuture M t p = J⁺(p)` does not contain `p`. The library is aware of this and
builds on it: `NoClosedCausalCurve t := ∀ p, ¬ M.CausallyPrecedes t p p` (l. 300), with the
docstring "a closed causal curve through `p` is exactly a causal trip `p ≺ p`", and
`causallyPrecedes_antisymm` calls `≺` "a strict partial order" under that condition.

### The blueprint

`blueprint/src/sections/sec10/spacetime.tex`, `def:causal-trip` (l. 611):

> A *causal trip segment* is a curve which is a future-oriented, causal geodesic. (Note a causal
> geodesic is possibly degenerate.) ... We write $p \prec q$ if and only if there exists a causal
> trip from $p$ to $q$.

`def:paths` (l. 239): "the parameter space -- a closed, connected subset $\Sigma$ of $\mathbb{R}$ that
contains more than a single point ... A *smooth path* is a path $\mu$ that is smooth and has a
non-vanishing derivative." So the blueprint also excludes constant curves. It says so outright at
l. 926: "the trip-based causal relation is irreflexive, so a point is spacelike-separated from
itself", and l. 638/649 (causality condition $\lnot(p \prec p)$; "$\prec$ is a strict partial
order").

### Chapter 1

`web/Tutorial/AQFTInBrief.lean:102-103`:

> * $`p \prec q`, read "$`p` causally precedes $`q`", if $`q - p` is causal and future-directed, or
>   zero.

and l. 134-136, which relies on that "or zero":

> With $`J^\pm`, the region $`J^+(p) \cap J^-(q)` is, when nonempty, compact, so not open, and for
> $`q = p` it is the single point $`\{p\}`

With the library's `≺`, $`J^+(p) \cap J^-(q)` omits its two vertices, so it is not compact, and for
$`q = p` it is empty. Chapter 1's l. 110 ("spacelike separated if neither causally precedes the other")
also gives a different answer for $`p` versus itself (the blueprint, l. 926, notes that in the library a
point is spacelike to itself).

### Verdict on point 1

- **Lean and blueprint agree.** Both define $`\prec` by non-trivial causal trips, and both treat it
  as irreflexive in causal spacetimes. There is **no blueprint–Lean mismatch** and no protected
  definition is at stake.
- **Chapter 1 deviates.** "or zero" is the common textbook convention (Hawking–Ellis put $`p` in
  $`J^+(p)`; O'Neill's $`p \le q` means "$`p = q` or there is a future causal curve", and his
  $`p < q`, which needs a curve, is not reflexive in general). The library's `≺` is O'Neill's $`<`, not
  his $`\le`. Chapter 1 is internally consistent, but it presents the definition as the project's own,
  with "In the library:" pointers, so it disagrees with the specification. **Severity: should fix
  (chapter 1).**
- **Blueprint wording (for the user; not a change for agents to make):** "(Note a causal geodesic is
  possibly degenerate.)" in `def:causal-trip` can be read as allowing constant curves, which
  `def:paths` forbids. It probably means "possibly null". Also, l. 926 says "the trip-based causal
  relation is irreflexive" without the qualifier "in a spacetime with no closed causal curve
  (e.g. Minkowski)". Both are clarifications of blueprint prose. Whether $`\prec` *should* be
  reflexive is a design decision for the user. The current choice is used downstream (the
  orthocomplement remark at l. 926, `NoClosedCausalCurve`), so it reads as deliberate. No docstring
  states the choice explicitly; a `CausallyPrecedes` docstring sentence would help ("Not reflexive:
  a causal trip has non-constant segments, so `p ≺ p` means a closed causal trip").

### Proposed fixes

1. **Chapter 1, l. 102-103** (should fix). Replace with:
   "* $`p \prec q`, read "$`p` causally precedes $`q`", if $`q - p` is causal and future-directed.
   (Many texts also let $`p \prec p`, so that $`p \in J^+(p)`. This project does not, and nothing below
   depends on the difference.)"
2. **Chapter 1, l. 134-136** (should fix). Replace the first sentence with:
   "Why chronological rather than causal cones? With $`J^\pm`, the region $`J^+(p) \cap J^-(q)` is not
   open: it contains points on the light cones of $`p` and $`q`, and points just outside the cones
   come arbitrarily close to them. (With the convention $`p \in J^+(p)` it is even compact, and for
   $`q = p` it is the single point $`\{p\}`.)" Keep the rest of the paragraph.
3. **Chapter 2, section 3, after "naming the spacetime and the time orientation"** (should fix;
   one sentence): "The library's $`\prec` asks for a causal curve from $`p` to $`q`, so in Minkowski
   spacetime $`p \prec p` is false (chapter 1)." No claim of chapter 2 depends on reflexivity (checked:
   the worked proof, its exercise and the `I⁺ ⊆ J⁺` exercise hold under both conventions).

## 2. Lean accuracy

Checked against source: `LocalNet` (`LocalAlgebras.lean:79`), `Isotony` (`Isotony.lean:61`),
`HaagKastlerNet` (`Net.lean:71`), `LocalCommutativity` (`LocalCommutativity.lean:64`),
`LorentzCovariance` (a `Prop`, `LorentzCovarianceAxiom.lean:69`), `IsAlexandrovBasisSet`
(`LocalAlgebras.lean:62`), `GNS.State` (`GNS/Basic.lean:59`), Mathlib's `CStarAlgebra`
(`Analysis/CStarAlgebra/Classes.lean:38`), `causalDiamond_subset_of` (`Causality.lean:573`, the chapter
reproduces it verbatim), `causallyPrecedes_of_causalDiamond_nonempty`, `HaagKastlerNet.quasilocal`
(`Net.lean:136`). Library sorry-free (no `sorry` term, no `axiom`). All 11 exercises are solvable
from the chapter, and every solution elaborates in the build (the `+error` and `leanOutput` blocks
are exact-match checked). The descriptions of types, propositions as types, dependent functions,
structures, strict-implicit binders, instance arguments, `rw` closing by `rfl`, and universes are
correct. Findings:

- **should fix — §5 "The Haag–Kastler net": the docstring box contradicts the prose.** The rendered
  `HaagKastlerNet` docstring says "the data of Axiom 1 ... together with proofs of Axioms 2, 3 and 5".
  But `Isotony` is data, which the chapter states correctly two lines later ("isotony data for it,
  and proofs of local commutativity and Lorentz covariance"). A careful reader sees a contradiction.
  Fix: in the library docstring (`Net.lean`, outside this task; needs approval), "the data of Axioms
  1 and 2 (`def:local-algebras`, `def:isotony`) together with proofs of Axioms 3 and 5". Or drop the
  box (see §3).
- **should fix — §5 "The net of local algebras", "only the diamonds and the empty set are used".**
  The empty set *is* a diamond (§6 says so). Fix: "only the diamonds (the empty one among them) are
  used, since the other axioms quantify over diamonds only."
- **should fix — §4 worked proof 2, the goal display shows `M.causalDiamond t p q`, the code
  `causalDiamond M t p q`.** The rendered states (checked in the DOM) print the dot form, and the
  bullet says "`hx : x ∈ causalDiamond M t p q`". Fix: add to the `intro` bullet, "(Lean displays
  `causalDiamond M t p q` as `M.causalDiamond t p q`, in dot notation; the two are the same term.)"
- **nit — §4 worked proof 1.** "The Lean proof has the same three steps": it is not the library's
  proof text (`U.emptyEquivComplex.injective <| by rw ...`). Add "(the library writes the first step
  as `U.emptyEquivComplex.injective`)", as worked proof 2 is introduced with "Here is its proof".
- **nit — §5 "Type classes", the `CStarAlgebra` parents.** Mathlib's class also extends
  `StarModule ℂ A`. Fix: "..., normed algebras over `ℂ`, and star modules over `ℂ`
  ($`(\lambda a)^* = \bar\lambda a^*`)."
- **nit — §4 "A small vocabulary", `constructor` example.** The goal is `x ∈ chronologicalDiamond …`,
  not visibly `P ∧ Q`. Add: "`constructor` sees through the definition of membership to the
  conjunction, as `Iff.rfl` showed in section 3."
- **nit — §4 proof by cases.** Prose says "$`x^2 \geq 0`", statement is `0 ≤ x * x`. Write
  "$`x \cdot x \geq 0`".
- **nit — §4 vocabulary, `rw [e]`.** "an equation or equivalence `e : a = b`": write "an equation
  `e : a = b` or an equivalence `e : P ↔ Q`, replacing the left side by the right".
- **nit — §4 "Worked proof: enlarging a causal diamond", "Chapter 1 used the fact".** Chapter 1 used it
  for chronological diamonds (second exercise, $`I^+(p_k) \subseteq I^+(p)`). Fix: "The second exercise
  of chapter 1 enlarged a diamond by moving its vertices outwards. For the causal diamonds ...".
- **nit — §4 exercise 2 (`[CStarAlgebra A]`) uses an instance argument before §5 explains it.**
  Add "(the square brackets are explained in section 5)".

## 3. Writer doubts

- **`{docstring}` boxes (should fix).** The four boxes show developer prose ("would-be
  Alexandrov-basis", "fiber", "universe polymorphism of `QuasilocalAlgebra.carrier` would be lost at
  the bundling level", "proofs of Axioms 2, 3 and 5"). The `State` box is the worst: it lists the
  inherited fields `toFun`, `map_add'`, `map_smul'`, `cont` with types like
  `(↑self.toContinuousLinearMap).toFun (x + y) = …`, which the reader is told to ignore. Field types
  are pretty-printed at width 40; any clipping comes from the box CSS (`.namedocs .text > pre {
  overflow-x: auto }`), so it scrolls rather than wraps. `#check` is no better (no wrapping, one
  line). **Proposal:** in §5 and §6, replace each box with (a) a plain, hand-wrapped excerpt of the
  `structure … where` and its fields, without docstrings (as the `signature` blocks do for `def`s),
  and (b) a hidden block, ```` ```lean (show := false) ```` (Verso's `show` flag,
  `InlineLean.lean:95`), with one `example` per field pinning its type, e.g.
  `example (U : LocalNet) : ∀ B, CStarAlgebra (U.algebra B) := U.instCStarAlgebra`. The build then
  fails on drift, as with the `Iff.rfl` restatements. Keep one box, for `Isotony` (the most readable
  docstring), and move it to §7 "Searching", where it illustrates "the docstrings in the library give
  the blueprint label". That turns the backtick-highlighted `def:isotony` into an illustration
  rather than noise. If boxes stay, use `+hideFields` on `State` at least, and fix the
  `HaagKastlerNet` docstring (§2).
- **Long `#check` outputs (should fix; easy).** Five outputs exceed the column width (`checkDiamond`,
  `checkCausalOfChrono`, `checkFutureSubset`, `axiomsEmpty`, `checkAlgebra`). The website already
  solves this: `web/Site/Theme.lean:184` has `.post-content pre.lean-output { white-space: pre-wrap;
  overflow-wrap: anywhere; }`. Add `pre.lean-output { white-space: pre-wrap; overflow-wrap: anywhere; }`
  to the tutorial's CSS (e.g. the `extraCss` of a block extension in `web/Tutorial/Meta.lean` used in
  every chapter, such as `exercise`). The `leanOutput` exact-match check is unaffected.
- **`goals` CSS depends on Verso class names (nit; low risk).** The failure mode is graceful. If
  `.tactic` / `.tactic-state` / the `kw-occ-Lean.Parser.Term.byTactic` binding change, the hiding
  rules stop matching and redundant states appear. If the `codeOptions.visibleProofStates` API
  changes, the build fails loudly. Fix: a comment above the CSS in `Meta.lean` naming the Verso
  markup it relies on, and a line in the Verso-upgrade checklist (or a CI grep that the generated
  chapter contains `class="goals"` with a `tactic-state` inside).
- **`web/README.md` lacks `goals` (should fix; one line).** l. 35: "- `Tutorial/Meta.lean`: the
  directives `exercise`, `solution` (collapsible) and `figure`." becomes "- `Tutorial/Meta.lean`: the
  directives `exercise`, `solution` (collapsible), `figure`, and `goals`, which shows the proof state
  after every tactic of the Lean block it wraps."
- **Side note:** `lake env lean Tutorial/LeanInBrief.lean` aborts here (`MD4Lean.parse` has no
  native implementation in the interpreter), so the log's "no warnings" check cannot be reproduced
  that way. The full `lake build` succeeds and reports no chapter warnings.

## 4. Prose and style

Overall: crisp, present tense, no history narration, correct level for the audience. Findings:

- **should fix — terminology clash with chapter 1: "causal diamond".** Chapter 1 (l. 122) calls
  $`I^+(p) \cap I^-(q)` "the _causal diamond_". Chapter 2 (following the library) calls it the
  chronological diamond and uses "causal diamond" for $`J^+(p) \cap J^-(q)` (§4 heading and exercise).
  A reader of chapter 1 will be confused. Fix in chapter 2, §2 "Points and regions", l. 181: "The
  diamond $`I^+(p) \cap I^-(q)` of chapter 1 is, in the library, the _chronological diamond_
  `chronologicalDiamond M t p q` ...; the library keeps the name `causalDiamond` for the closed
  version $`J^+(p) \cap J^-(q)`, which section 4 uses." In §4, l. 477: "For the library's causal
  diamonds $`J^+(p) \cap J^-(q)` (chapter 1 explains why the net does not use them) ...".
- **nit — the reminder "As you will recall" opens §2, §4 (cases) and §5.** The plan asks for
  variety. E.g. §4: "Recall that a proof by cases ..."; §5: "In algebra, a structure is a set together
  with ...".
- **nit — §2 "Dependent functions": "In mathematics such functions are common, but rarely named".**
  Physicists know them as sections. Write "...common: a vector field, a section of the tangent
  bundle, assigns to each point $`x` a vector in $`T_x M` ...".
- **nit — §2 "Points and regions": `M.Carrier`, `M.TimeOrientation` appear before dot notation is
  explained** (a paragraph later). Add to the first use: "`StandardMinkowskiSpacetime.Carrier`, the
  field `Carrier` of the structure `StandardMinkowskiSpacetime` (section 5)".
- **nit — §1 `#print axioms` output** breaks lines oddly (`[propext,` / ` Classical.choice,`). It is
  Lean's output and is exact-matched, so leave it. The CSS wrap fix above does not change it.
- **nit — `simp`** is in the vocabulary but used nowhere in the chapter. Either keep it as
  vocabulary (it is common in the library) or add a one-line example, e.g.
  `example (s : Set ℝ) : s ∩ s = s := by simp`.
- Not too elementary or advanced: the universe aside is the right length. §6's line-by-line
  reading of `LocalCommutativity` against Axiom 3 is the best passage in the chapter.

## 5. Rendering

- **Maths:** 78 math spans, 78 KaTeX renderings, **0 `katex-error`** (checked on the DOM after
  JavaScript, headless Chrome `--dump-dom`).
- **Code:** 46 highlighted Lean blocks, 59 inline; 12 information, 1 warning (the `sorry` example)
  and 1 error (`2 + 2 = 5`) output blocks, as intended.
- **Goals:** 5 `goals` blocks. The states extracted from the DOM are correct after each tactic
  (e.g. `⊢ U.emptyEquivComplex a * U.emptyEquivComplex b = U.emptyEquivComplex (b * a)` after the
  first `map_mul`; `hx : (p ≺[M, t] x) ∧ x ≺[M, t] q` after the `rw … at hx ⊢`). The CSS hides the
  nested and `by` states.
- **Solutions:** 11 `<details>`, one per exercise.
- **Links:** all 9 external links return HTTP 200 (Loogle, Mathlib docs, library docs, blueprint,
  TPIL, MIL, FPIL, reference, community). Internal section links resolve. Prose cross-references
  ("section 5", "section 7") are plain text; nit: make them Verso section links if the manual genre
  supports `{ref}` to section tags.
- Screenshots could not be taken in this session (headless Chrome returned blank images), so visual
  layout (box clipping, wrapping) was assessed from the CSS rather than seen.

## Verdict and top 5

**Verdict: accept after small revisions.** No errors in chapter 2's Lean or mathematics, and every
example and solution is checked by the build. 0 errors, 10 should-fix, 14 nits (counted above). The
≺ issue is a chapter 1 deviation from the blueprint, not a Lean–blueprint mismatch.

Top 5 fixes:

1. Chapter 1 l. 102-103 and 134-136: drop "or zero", and rewrite the $`J^\pm` sentence (texts in §1),
   plus one sentence in chapter 2 §3 on the library's non-reflexive $`\prec`.
2. Chapter 2 §2/§4: reconcile "causal diamond" (chapter 1: $`I^+ \cap I^-`; library: $`J^+ \cap J^-`).
3. Replace the `{docstring}` boxes in §5/§6 with hand-wrapped field excerpts plus hidden
   `(show := false)` field-type checks; keep one `Isotony` box in §7 as the docstring illustration.
   At a minimum, fix the `HaagKastlerNet` docstring ("proofs of Axioms 2, 3 and 5") and hide the
   `State` fields.
4. Add `pre.lean-output { white-space: pre-wrap; overflow-wrap: anywhere; }` to the tutorial CSS, as
   `Site/Theme.lean:184` does for the website.
5. §4: explain that the goal display prints `causalDiamond M t p q` as `M.causalDiamond t p q`; and
   in §5 correct "only the diamonds and the empty set" (the empty set is a diamond). Add `goals` to
   `web/README.md`.
