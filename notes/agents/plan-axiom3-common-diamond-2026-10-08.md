# Plan: restate Minkowski Axiom 3 through a common containing diamond

Date: 2026-10-08. Toolchain: Lean / Mathlib v4.34.1. Proposed branch: `numina/axiom3-common-diamond`
off `numina/aqft-in-lean`. Status: **approved 2026-10-08** (D1–D5 as recommended, including the Chapter 5 wording
and the D5 Chapter 9 sentence). Nothing is changed until
the user approves: `LocalCommutativity` is an axiom definition, so it is a protected design
decision under CLAUDE.md.

## Goal

Restate Definition 485 (`def:local-commutativity`, Minkowski Axiom 3) so that commutation happens
in the local algebra 𝔘(B) of any Alexandrov diamond B containing both B₁ and B₂, using the Axiom 2
isotony maps. This is the same shape as Definition 628 (`def:local-commutativity-in-curved-spacetime`).
The current form, commutation in the quasilocal algebra 𝔘, becomes a proved equivalent.

## Mathematical content

Write `LC_new` and `LC_old` for the two forms.

- **`LC_new`.** For all diamonds B₁, B₂, B with B₁, B₂ completely spacelike and B₁, B₂ ⊆ B, and
  all a ∈ 𝔘(B₁), b ∈ 𝔘(B₂): i_{B₁B}(a) and i_{B₂B}(b) commute in 𝔘(B).
- **`LC_old`** (today's Lean). There is a quasilocal algebra Q such that, for B₁, B₂ completely
  spacelike, ι_{B₁}(a) and ι_{B₂}(b) commute in Q.
- **The two are equivalent.** Everything needed is already proved.
  - **The bridge.** `QuasilocalAlgebra.commute_ι_iff_commute_map` (LocalCommutativity.lean): for any
    Q and any diamond B ⊇ B₁ ∪ B₂, ι_{B₁}(a), ι_{B₂}(b) commute in Q iff i_{B₁B}(a), i_{B₂B}(b) commute
    in 𝔘(B).
  - **old ⇒ new.** Apply the bridge to the given Q, for every B.
  - **new ⇒ old.** Take Q from `exists_quasilocalAlgebra` (QuasilocalExistence.lean, built from
    the net alone). Pick a common B by upward directedness (`Spacetime.alexandrovBasis_directed`) and
    apply the bridge.
- **The two forms are equivalent, not one strictly stronger than the other.** The gain is
  foundational, not logical. The axiom then speaks only of the net and isotony, with no
  quantifier over ambient C*-algebras. It no longer depends on `def:quasilocal-algebra`. It reads in
  parallel with the curved Axiom 3, so the one real difference is visible: whether a common
  containing diamond always exists. It does in Minkowski space; it may not in curved spacetime
  (the Schwarzschild example of Chapter 9).
- **"For every common B" vs "for some common B".** In Minkowski space these are equivalent, by
  directedness and injectivity of the isotony maps. The recommendation is "for every", so the Lean
  definition is the curved one with only the basis-set predicate swapped.

## Decisions needed

**D1. Quantifier over the containing diamond.**
- (a) **Recommended:** "for every diamond B ⊇ B₁ ∪ B₂", identical in shape to Definition 628.
- (b) "for some diamond B ⊇ B₁ ∪ B₂". This is closer to "they live in a common algebra", but
  it is no longer parallel to Definition 628.

**D2. Placement of Axiom 3 in §10.6.** Axiom 3 would no longer use `def:quasilocal-algebra`.
- (a) **Recommended:** keep its current position, after `def:quasilocal-algebra`. Only the
  dependency edge is dropped, the chapter is not reordered, and item numbers stay put except for
  the one new lemma.
- (b) Move Axiom 3 directly after Axiom 2 (Isotony). This reads more naturally, but it reorders
  your chapter, and every item number between the two positions shifts.

**D3. The equivalence as a new node.**
- **Recommended:** add `lmm:local-commutativity-iff-quasilocal`, "Local Commutativity in the
  Quasilocal Algebra". It says Axiom 3 holds iff, for some (equivalently every) quasilocal
  algebra, the images of completely spacelike local algebras commute. That keeps the old form
  citable.
- The existing `lmm:local-commutativity-any-quasilocal` (Lean `commute_ι`) stays as the "⇒, in
  every quasilocal algebra" direction, with a simpler proof.
- The alternative is to fold the equivalence into that existing lemma (no new node, so no
  renumbering), at the cost of a two-part statement.

**D4. Chapter 5 wording.** Chapter 5 is your motivation chapter. It is not formalised, but it is
read before Axiom 3. Its §5 "Quasilocal Algebra" argues that isotony cannot place 𝔘(B₁) and
𝔘(B₂) in a common algebra. That considers only B₁ ⊂ B₂ and misses a third diamond B containing
both, which always exists in Minkowski space. Under the new Axiom 3 the argument becomes
incorrect, not merely unused.
- (a) **Recommended:** replace the "Naively …" / "However, what does come to the rescue …"
  paragraphs and the two quotes with the proposed wording below.
- (b) Keep the text and add one corrective sentence.
- (c) Leave Chapter 5 unchanged. Not recommended, because it would contradict Axiom 3.

**D5. Chapter 9 cross-reference (optional).** Chapter 9 §"Axiom 3 (Local Commutativity)" says
the absence of a common containing diamond is why curved spacetime differs. With the new
Minkowski axiom that contrast is exact.
- **Recommended:** add one sentence to Chapter 9 pointing back to Chapter 5's "a common containing
  diamond always exists in Minkowski space".
- Alternatively, leave Chapter 9 as is.

## Proposed Chapter 5 wording (for D4(a))

File: `blueprint/src/sections/sec5/quasilocal-algebra.tex`. Keep the section heading and the
opening two paragraphs ("The second point that requires clarification is a bit more subtle." and
"When one requires that … in which products and sums of their elements are defined."). Replace
everything from "Naively one might hope that isotony would come to the rescue." up to, but not
including, "Clarification." with:

```latex
Isotony is the natural tool for this. If, say, $\mathbf{B_1} \subset \mathbf{B_2}$, isotony
places $\mathfrak{U}(\mathbf{B_1})$ inside $\mathfrak{U}(\mathbf{B_2})$, so that both live in the
single algebra $\mathfrak{U}(\mathbf{B_2})$. That case is of no use here, since nested regions are
never completely spacelike. But isotony does not require one of the two regions to contain the
other: it suffices to find a \emph{third} basis element $\mathbf{B}$ containing both. In Minkowski
spacetime such a $\mathbf{B}$ always exists --- any two double cones $I^+(p_1) \cap I^-(q_1)$ and
$I^+(p_2) \cap I^-(q_2)$ lie inside a larger double cone $I^+(p) \cap I^-(q)$, by taking $p$
far enough in the past of $p_1$ and $p_2$ and $q$ far enough in the future of $q_1$ and $q_2$.
Isotony then places $\mathfrak{U}(\mathbf{B_1})$ and $\mathfrak{U}(\mathbf{B_2})$ inside the single,
larger algebra $\mathfrak{U}(\mathbf{B})$, in which products and sums of their elements are
defined. We can thus interpret the statement

\begin{quote}
    If $\mathbf{B_1}$ and $\mathbf{B_2}$ are completely spacelike with respect to each other, then $\mathfrak{U}(\mathbf{B_1})$ and $\mathfrak{U}(\mathbf{B_2})$ commute.
\end{quote}

as the statement

\begin{quote}
    If $\mathbf{B_1}$ and $\mathbf{B_2}$ are completely spacelike with respect to each other, then $\mathfrak{U}(\mathbf{B_1})$ and $\mathfrak{U}(\mathbf{B_2})$ commute in $\mathfrak{U}(\mathbf{B})$ for every basis element $\mathbf{B}$ containing both $\mathbf{B_1}$ and $\mathbf{B_2}$.
\end{quote}

Two remarks. First, the choice of $\mathbf{B}$ does not matter: because the isotony embeddings
are injective and compatible, commutation in one containing algebra implies commutation in every
other. Second, the quasilocal algebra $\mathfrak{U}$ of the next chapter contains every
$\mathfrak{U}(\mathbf{B})$, so the statement can equally be read as commutation in
$\mathfrak{U}$; the two readings are equivalent. The formulation through a containing
$\mathfrak{U}(\mathbf{B})$ is preferred because it uses only the net and isotony, and because it
is the formulation that survives in curved spacetime (Chapter 9), where a containing basis element
need not exist and the quasilocal algebra need not exist either.
```

Notes on this wording:
- The containment claim is upward directedness of the Minkowski diamonds, which the project proves
  as `lmm:minkowski-diamonds-upward-directed`. Chapter 5 is not formalised and does not cite
  Chapter 10 labels, so the wording states the fact informally.
- The two `quote` environments mirror the existing text's structure. The second quote is the
  wording the new Definition 485 formalises.
- Check after the edit: the next section of Chapter 5 and the beginning of Chapter 6 may say
  "commute in the quasilocal algebra" or motivate 𝔘 by Axiom 3. Chapter 6's motivation for 𝔘
  (Axiom 4: all observables of interest) is independent of Axiom 3 and stays valid. Stage 1
  includes a grep of Chapters 5–6 for such sentences, and any change is proposed to you before it
  is made.

## Stages

Each stage: build, lint, `checkdecls`, commit on the branch, and a progress entry below.

### Stage 1: blueprint (writer, then reviewer; targeted edits)

1. **`def:local-commutativity`** (haag-kastler-axioms.tex, around line 384): new statement modelled
   on Definition 628.
   - Two diamonds B₁, B₂; Axiom 2's isotony family i. If B₁, B₂ are completely spacelike, then for
     every diamond B ⊇ B₁ ∪ B₂ (per D1), i_{B₁B}(a₁) and i_{B₂B}(a₂) commute in 𝔘(B).
   - Add one sentence: by upward directedness such a B always exists (cite
     `lmm:minkowski-diamonds-upward-directed` by `\ref`).
   - `\uses`: remove `def:quasilocal-algebra`, keep the rest.
   - Remove the ι / cocone paragraphs from this node (see item 2).
   - Replace "Note that the curved counterpart … has a different shape …" with the single real
     difference: in Minkowski a containing diamond always exists, in curved spacetime it may not.
   - Keep the final pointer, reworded: the equivalent form in 𝔘 is
     `lmm:local-commutativity-iff-quasilocal`.
2. **`def:quasilocal-algebra`** (around line 372): absorb the canonical embeddings ι_B and the
   cocone condition ι_{B₂} ∘ i_{B₁B₂} = ι_{B₁}. These are already fields of the Lean structure
   `QuasilocalAlgebra` and are now stated nowhere else. Fix its sentence "as recorded in
   \ref{def:local-commutativity}".
3. **New `lmm:local-commutativity-iff-quasilocal`** (after `lmm:local-commutativity-any-quasilocal`,
   per D3): statement as in D3. The proof uses the bridge, `thrm:quasilocal-algebra-exists` and
   `lmm:minkowski-diamonds-upward-directed`.
4. **`lmm:local-commutativity-any-quasilocal`:** the premise becomes "Suppose the net satisfies
   Axiom 3". The proof is the bridge in one direction: no second quasilocal algebra and no
   directedness needed.
5. **Einstein causality** (around line 767): "Local commutativity … is an algebraic statement
   about the quasilocal algebra" becomes "about the local algebras; in the quasilocal algebra it
   takes the form of `lmm:local-commutativity-any-quasilocal`". Add that lemma to the proof
   `\uses` of `thrm:einstein-causality`.
6. **Curved chapter:** grep for sentences contrasting the two Axiom 3 forms. The known passages
   (lines 45, 141 and 286: "there is no quasilocal algebra here") stay true. Change only
   sentences that describe the Minkowski axiom as "in the quasilocal algebra".
7. **Chapter 5** per D4, and **Chapter 9** per D5. Exact wording is above, and the user approves
   it before the writer applies it.
8. **`\leanok`.** Strip the stale `\leanok` from `def:local-commutativity` (its Lean changes in
   Stage 2). It is re-recorded after the Lean is updated.

The reviewer checks: faithfulness to D1–D5, the equivalence proof's grounding (the three Lean
names above), no other node depending on the removed `def:quasilocal-algebra` edge, and that no
prose still says Axiom 3 lives in 𝔘.

### Stage 2: Lean statements (orchestrator; protected definition)

**`Physicslib4/AQFT/HaagKastler/LocalCommutativity.lean`:**
- New definition (D1(a)):
  ```lean
  def LocalCommutativity (U : LocalNet) (i : Isotony U) : Prop :=
    ∀ ⦃B₁ B₂ B : Set StandardMinkowskiSpacetime.Carrier⦄
      (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
      (hB : IsAlexandrovBasisSet B),
      Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation B₁ B₂ →
      (h₁ : B₁ ⊆ B) → (h₂ : B₂ ⊆ B) →
      ∀ (a : U.algebra B₁) (b : U.algebra B₂),
        Commute (i.map hB₁ hB h₁ a) (i.map hB₂ hB h₂ b)
  ```
- Module docstring and definition docstring rewritten: commutation in a common containing diamond,
  parallel to `HaagKastlerCurved.LocalCommutativity`.
- `QuasilocalAlgebra.commute_ι_iff_commute_map`: unchanged.
- `LocalCommutativity.commute_ι` (`lmm:local-commutativity-any-quasilocal`): signature unchanged;
  the proof becomes directedness plus one use of the bridge.
- New `localCommutativity_iff_exists_commute_ι` (`lmm:local-commutativity-iff-quasilocal`):
  `LocalCommutativity U i ↔ ∃ Q : QuasilocalAlgebra U i, ∀ ⦃B₁ B₂⦄ hB₁ hB₂, IsCompletelySpacelike … →
  ∀ a b, Commute (Q.ι hB₁ a) (Q.ι hB₂ b)`, i.e. the old definition's body.
  - The ← direction needs only the bridge; the → direction needs `exists_quasilocalAlgebra`.
  - Import `Physicslib4.AQFT.HaagKastler.QuasilocalExistence`; no cycle, since QuasilocalExistence
    imports only QuasilocalAlgebra and QuasilocalColimit.
  - Optionally a companion `localCommutativity_iff_forall_commute_ι` (∀ Q).

**`Physicslib4/AQFT/HaagKastler/Net.lean`:**
- `trivialLocalNet_localCommutativity` (line 345): the old proof builds `trivialQuasilocalAlgebra`.
  The new one is "the algebras are ℂ, so everything commutes".
- `commute_ι_of_spacelike` (line 213) is unchanged, since it uses `commute_ι`. Its docstring ("Axiom
  3 only asserts this in *some* quasilocal algebra") is updated.

**Unchanged:**
- the `HaagKastlerNet.localCommutativity` field;
- `einstein_causality` and the other consumers (they go through `commute_ι_of_spacelike`);
- `Spacetime/LorentzCausality.lean`, whose docstring wording stays accurate.

**Verification:** a grep confirms that nothing else unfolds `LocalCommutativity`. Today only
`Net.lean:345` does.

Statements are sorry'd, then the formalizer-reviewer runs.

### Stage 3: proofs (provers, in parallel)

- `LocalCommutativity.commute_ι`: about 4 lines.
- `localCommutativity_iff_exists_commute_ι`: about 10 lines, possibly split into its two
  directions.
- `trivialLocalNet_localCommutativity`: about 3 lines (`mul_comm` in ℂ).

### Stage 4: verify and audit

- Build, lint, `checkdecls`, and `#print axioms` on the new and re-proved theorems.
- lean-auditor lists the protected change (one `def` body), confirms no consumer's statement
  changed, and checks blueprint/Lean agreement for the touched nodes.

### Stage 5: publish locally

- Rebuild the PDF and the web blueprint, and check the PDF for new overfull lines (the print
  preamble now wraps Lean names).
- Home page:
  - `axioms.md`: the Axiom 3 row (Minkowski) and a note under it, "Axiom 3 is now stated in a
    common containing diamond, parallel to the curved form; the quasilocal form is
    Lemma N".
  - `guide.md`: the Chapter 5 summary (line 26) currently repeats "isotony alone cannot place two
    spacelike-separated regions in a common algebra". Rewrite it per D4.
  - `sec10-6-haag-kastler.md`: the axioms overview, the new entry, and refreshed entries.
  - If D3 adds a node: renumber items after it and update the counts (one more lemma; with D2(b),
    more renumbering), as in earlier refreshes.
- Run a local Jekyll build and the link check, then commit and merge into `numina/aqft-in-lean`.
  Don't push unless asked.

## Risks

- **Protected definition.** The body of `LocalCommutativity` changes. The field and every theorem
  signature that uses it are unchanged, and the equivalence lemma makes the old form available
  under its own name.
- **Universe/import plumbing.** `exists_quasilocalAlgebra` is stated for `LocalNet.{u}`. The
  equivalence inherits that universe, and `LocalCommutativity` must stay universe-polymorphic in
  the same way. Easy to check in Stage 2.
- **Chapter 5 is your text.** Stage 1 applies D4 only after you approve the wording above.

## Estimate

- One definition change, one new lemma (two declarations if the ∀ Q companion is added) and two
  re-proofs, all short.
- About seven blueprint node edits plus Chapter 5 (and optionally Chapter 9) prose.
- One home-page refresh.

## Progress log

(empty)
- 2026-10-08, Stage 1 done (branch `numina/axiom3-common-diamond`). Chapter 5 rewritten with the
  approved wording (applied verbatim from this plan). Writer edits in haag-kastler-axioms.tex:
  def:local-commutativity restated through every common containing diamond (parallel to the
  curved form; \leanok/\leanfile removed), ι/cocone material moved into def:quasilocal-algebra,
  lmm:local-commutativity-any-quasilocal re-premised (\leanok removed), new
  lmm:local-commutativity-iff-quasilocal, Einstein-causality prose and proof \uses, "rejected
  alternative" sentence; Chapter 9 sentence added. Reviewer REVISE → fixed lines ≈50 and ≈369
  (no longer claim Axiom 3 needs the quasilocal algebra) and two optional \uses edges. Reviewer's
  optional Chapter 5 refinements (common upper bound in the first remark; "nonempty nested
  regions") NOT applied: they change user-approved wording, offered to the user. PDF builds
  without errors or overfull lines.
