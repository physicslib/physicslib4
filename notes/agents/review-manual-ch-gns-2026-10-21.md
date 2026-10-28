# Review: GNS manual chapter and docstring pass (2026-10-21)

Scope: commit `3b3cfcd` (docstrings, `Physicslib4/GNS/`) and the uncommitted chapter `web/Manual/GNS.lean`.

## A. Docstring pass (`3b3cfcd`)

### What was checked and is correct

- **Comments only.** All 15 `Physicslib4/GNS/` files of `3b3cfcd` compared with `3b3cfcd^` with
  `--` and nested `/- -/` comments removed and whitespace normalised: identical in all 15. No GNS
  file changed between `3b3cfcd` and HEAD.
- **Mathlib's GNS space.** `gns_construction` and `nullSet` docstrings are right: Mathlib's
  `PositiveLinearMap.PreGNS` is `def PreGNS f := A` with the seminorm from ⟨a, b⟩ = f(a* b), and
  `GNS` is `UniformSpace.Completion f.PreGNS`; π is `gnsStarAlgHom`. The quotient by N(ω) is
  implicit in the Hausdorff completion, as `nullSet` says.
- **Weak-* / Krein–Milman.** `stateSpace` (norm topology) vs `weakStateSet` (`WeakDual ℂ A`)
  stated correctly; `weakStateSet` says pure-state existence is not proved. Matches the module
  note of `PureStateExists.lean`.
- **`IsIrreducible` zero case** stated once, neutrally, as an implementation note; matches the
  definition (on H = 0 every T equals 0·1). `UnitaryEquiv.not_areDisjoint` does need
  `[Nontrivial H₁]`, as `AreDisjoint` says.
- **Other facts checked against code:** `IsPure` (continuous ψ, complex t, order on ℂ);
  `State.IsExtremePoint` (pointwise, real t); `exists_gns_unitary_of_invariant` (G a monoid,
  `U (g' * g) = (U g).trans (U g')` = U(g')U(g), cyclicity clause present; the strongly
  continuous forms have hypothesis `hwc` on ω(a* γ_g(b)) as stated); density theorem
  `exists_forall_norm_sub_lt_of_mem_bicommutant` (finitely many vectors, so "strong-operator
  limit" is right); Mathlib's `VonNeumannAlgebra` has only a `PartialOrder`, no meet (as
  `vonNeumannCenter` says); `isIrreducible_iff_gnsVonNeumann_eq_univ`,
  `intertwines_self_iff_mem_centralizer`, `Intertwines.add/smul/comp/adjoint`,
  `nullSubmodule_isClosed`, `lmm2` exist; `vonNeumannOfSelfAdjoint` is used by both
  `LocalVonNeumann.lean` files ("local von Neumann algebras R(B)" correct).
- **Format:** one-sentence first lines, Implementation note before Blueprint line, plain-text
  labels, parenthesised subscripts (γ_(g'g), γ_(g')), present tense.

### Findings

A1. **should fix**: `PureStateExists.lean`, `weakStateSet`: "so these are exactly the states
(`State.toWeakDual` and `State.toWeakDual_mem_weakStateSet`)". The library proves one inclusion
only (every state lies in the set); the converse (every element of `weakStateSet` comes from a
`State`) is not stated. Replace with: "For a positive functional φ(1) = 1 is the same as ‖φ‖ = 1,
so mathematically these are exactly the states; the library proves that every state lies in the
set (`State.toWeakDual_mem_weakStateSet`), not the converse."

A2. **should fix**: `Superselection.lean`, `QuasiEquiv`: broken line wrapping from an edit:
"...as a representation and its amplification do (the library does not prove\nthis). The normal
states of a\nrepresentation are its folium, ...". Reflow the paragraph to the 100-column width.
Also "and so have the same normal states" and "quasi-equivalence means having the same folium" are
mathematics the library does not state; prefix the folium sentence with "Mathematically," or keep
as is but reflowed (nit level for the second part).

A3. **should fix** (blueprint citation): `CauchySchwarz.lean`, `omega_star_swap_conj` ends
"Blueprint: lmm:cauchy-schwarz-inequality", but that node's `\lean{}` lists only
`cauchy_schwarz_inequality`. This is a 14th uncited declaration, missing from the log's list.
Proposal: add `Physicslib4.GNS.omega_star_swap_conj` to `\lean{}` of lmm:cauchy-schwarz-inequality
(its proof uses the Hermitian symmetry). Until then, write "Blueprint: the Hermitian symmetry used
in lmm:cauchy-schwarz-inequality".

A4. **nit** (consistency): `ExtremeState.lean`, `stateSpace` ends "Blueprint:
thrm:state-space-convex-bridge" as if listed, while `State.precomp` and `State.convexCombo` use the
descriptive form for the same situation (not in `\lean{}`). Write "Blueprint: the state space of
thrm:state-space-convex-bridge" until the proposal below lands.

A5. **nit**: `ExtremeState.lean`, `stateSpace`: "The weak-* compact version, to which the
Krein–Milman theorem applies, is `weakStateSet`." Add "mathematically" or "(the library proves the
compactness, not the application)", to match `weakStateSet`.

A6. **nit**: `UnitaryEquiv.lean`, `UnitaryEquiv`: "the classes of irreducible representations of
the algebra of observables are the superselection sectors". Sectors are classes of irreducible
representations selected by a criterion (e.g. DHR); write "superselection sectors are classes of
irreducible representations of the algebra of observables" (also matches the chapter's
"labelled by").

A7. **nit** (blueprint side finding, not a Lean change): the formalization note in the proof of
thrm:gns-construction-theorem (`gns-construction-details.tex` l. 325) says "the completion of the
quotient `PositiveLinearMap.PreGNS`"; `PreGNS` is a type synonym of A with a seminorm, not a
quotient. Proposal: "the completion of `PositiveLinearMap.PreGNS`, the algebra with the seminorm
a ↦ ω(a* a)^(1/2)". The `nullSet` docstring already has it right.

### A(13): the uncited declarations (proposals for the lean-blueprint agent)

- `nullSet`, `orthSet` → `\lean{}` of **lmm:lmm1** (states 𝒩 = 𝒩₁): confirmed.
- `nullSubmodule` → **lmm:lmm2** (`lmm2` is literally `⟨nullSubmodule ω, …⟩`): confirmed.
- `Intertwines` → **def:disjoint-representations** (its prose defines intertwiners and their
  closure properties): confirmed.
- `gnsVonNeumann`, `gnsVonNeumannAlgebra` → **not** def:local-von-neumann (net-specific, lists
  `HaagKastlerNet.localVonNeumann`). Propose a new node `def:generated-von-neumann-algebra` in §10.6
  just before thrm:irreducible-factor ("the von Neumann algebra π(A)'' generated by a
  representation", `\uses{lmm:bicommutant-of-selfadjoint-is-von-neumann}`), or, minimally, add
  `gnsVonNeumann` to thrm:irreducible-generates-all and `gnsVonNeumannAlgebra` to
  thrm:gns-generates-all-bundled.
- `State.precomp` → **thrm:purity-covariance-invariant** (`\leanfile` already ExtremeState.lean,
  lists `isPure_precomp_iff`): confirmed.
- `State.convexCombo`, `stateSpace` → **thrm:state-space-convex-bridge** (its prose names both):
  confirmed.
- The four `exists_gns_unitary*_of_invariant*` → a **new node** in §10.6 (e.g.
  `thrm:invariant-state-gns-unitary-general`, algebra-agnostic, G a monoid), which
  thrm:invariant-state-gns-unitary and its strongly continuous form `\uses`; adding them to the
  Minkowski nodes would mix the general and net-specific forms (they are also used by
  `HaagKastlerCurved/StabilizerAction.lean`). Confirmed as "needs a node".
- Plus `omega_star_swap_conj` (A3).

## B. Chapter `web/Manual/GNS.lean`

Rebuilt: `cd web && lake build && lake exe generate-manual --output _out/manual` passes (only
pre-existing notices). Page: `web/_out/manual/html-multi/The-GNS-construction/index.html`; 16
docstring boxes render.

### What was checked and is correct

- **Blueprint anchors:** every `#def:/#lmm:/#thrm:/#sctn:` href in the rendered page exists in
  `blueprint/web/chptr-haag-kastler-axioms-blueprint.html`. **Tutorial anchors**
  (`States-and-the-GNS-construction`, `worked-examples-gns`) and the Haag–Kastler subsection anchor
  exist in `_out/`. `{apiDocs}` hrefs point to the declaring file. `home_page/sec10-1-gns.md` and
  `sec10-6-haag-kastler.md` exist.
- **Printed `#check` outputs** match the build (Verso checks them).
- **Claims checked:** `State.apply_one` exists; Mathlib's GNS space description (see A); universe of
  H; `isIrreducible_iff_centralizer` (in `UnitaryEquiv.lean`) and `scalarOperators`; Schur lemma
  statement matches `eq_smul_one_of_commute_of_cyclic` (no state assumed); `rnOp` directions;
  `exists_gns_factor_of_isPure`, `exists_gns_generates_all_of_isPure` (RadonNikodym.lean);
  dichotomy argument; unitary-implementation formulas and conventions; `hwc` hypothesis; the
  amplification commutant formula; "not proved" items (pure-state existence, amplification
  quasi-equivalence) stated as not proved.
- **Coverage** of the plan's chapter 1 list (states, null spaces, construction and uniqueness,
  cyclic and separating vectors, purity and irreducibility, direct sums): complete; plus
  equivalence/disjointness and covariance.
- **Zero case** of `IsIrreducible` stated once in the prose (Design), neutrally; the docstring
  states it once too.
- **Style:** present tense, "As you will recall" openers, no internal memos linked, plain-text
  "Blueprint:" lines.

### Findings

B1. **error** (links; l. 54, 145, 662): `../Haag-Kastler-axioms-in-Minkowski-spacetime/...`. Pages
carry `<base href="./../">`, which points at the manual's root (`/physicslib4/manual/`, see
`web/README.md` l. 189–193), so `../X` resolves to `/physicslib4/X`, outside the manual: the three
links are broken when deployed (the tutorial links `../tutorial/...` are right). Verso's own
cross-chapter links are base-relative (`Haag-Kastler-axioms-in-Minkowski-spacetime/#haag-kastler`).
Fix: l. 54 `{ref "haag-kastler"}[Haag–Kastler chapter]` (the chapter's tag), and l. 145, 662
`Haag-Kastler-axioms-in-Minkowski-spacetime/#physicslib4-reference-manual--...` (drop `../`), or
`../manual/Haag-Kastler-...` per the README convention. **Side finding:** the Spacetime chapter has
the same bug (`web/Manual/Spacetime.lean` l. 187 and any other `](../Haag-` link); the Spacetime
review missed it.

B2. **should fix** (l. 158; doubt 2): "A GNS space is never zero, since ‖Ω‖² = ω(1) = 1." True and
immediate from the printed statement, but it reads as a library fact. Replace with: "A space
carrying a vector that reproduces a state is never zero, since ‖Ω‖² = ⟨Ω, π(1)Ω⟩ = ω(1) = 1; this
is immediate from the reproducing condition at a = 1, and the library has no separate lemma for it.
So the zero case does not arise in `isPure_iff_isIrreducible`."

B3. **should fix** (l. 339–340): "to distinguish it from Mathlib's irreducible topological spaces".
Mathlib's root `IsIrreducible` is about irreducible *subsets* of a topological space (spaces are
`IrreducibleSpace`). Write "to distinguish it from Mathlib's `IsIrreducible`, irreducibility of a
subset of a topological space."

B4. **should fix** (l. 170–172; doubt 3): accurate (checked: `#synth LocallyConvexSpace ℝ (WeakDual
ℂ A)` fails, and `IsCompact.extremePoints_nonempty` requires it), but it is one of two missing
pieces named in the module note. Write: "...is not proved: among the missing pieces, Mathlib has no
instance `LocallyConvexSpace ℝ (WeakDual ℂ A)`, which its Krein–Milman theorem needs."

B5. **should fix** (l. 515–516): "it is not a scalar when another summand is nonzero". The
projection onto summand j is a nontrivial projection only if H_j and some H_k (k ≠ j) are both
nonzero (`not_isIrreducible_directSum` takes v ≠ 0 in H j and w ≠ 0 in H k). Write "and it is not
a scalar when its own summand and another summand are both nonzero:".

B6. **nit** (l. 374–376): "an irreducible representation generates a factor
(`center_gnsVonNeumann_eq_of_isIrreducible`)". The factor form is
`isFactor_gnsVonNeumann_of_isIrreducible`, which lives in
`Physicslib4/AQFT/HaagKastler/GeometricCovariance.lean`; `IsFactor` is in
`Physicslib4/Operators/Conjugation.lean`. Cite both lemmas ("its centre is the scalars
(`center_gnsVonNeumann_eq_of_isIrreducible`), so it generates a factor
(`isFactor_gnsVonNeumann_of_isIrreducible`)"), and in "Where to look" change `Irreducibility.lean`
"the centre and factors" to "the centre (`IsFactor` itself is in `Operators/Conjugation.lean`)".

B7. **nit** (l. 33–37; doubt 4): the cited range "Irreducibility and Schur's Lemma" to "Direct Sums,
Amplification, and Reducibility" also contains quasilocal entries (thrm:pure-iff-extreme-quasilocal,
thrm:pure-iff-irreducible-quasilocal, thrm:gns-covariance-local). Write "...the subsections of
Section 10.6 that develop representation theory, mostly for an arbitrary C\*-algebra: ...".

B8. **nit** (l. 194): "(π ⊗ 1)' = π' ⊗ B(ℓ²)": write "(π(A) ⊗ 1)' = π(A)' ⊗̄ B(ℓ²(ι))" (von Neumann
tensor product), as in the `amplification` docstring's intent.

B9. **nit** (l. 214): "stated for any algebra" → "stated for any unital C\*-algebra".

B10. **nit** (l. 56): "The section has five parts" → "The chapter has five parts".

B11. **nit** (l. 475): "two pure states lie in the same superselection sector or in disjoint ones"
→ "the GNS representations of two pure states are unitarily equivalent (the same superselection
sector) or disjoint".

B12. **nit** (l. 157): "results that need a nonzero space assume `Nontrivial H`" → "assume it,
as `Nontrivial H` or as a nonzero vector".

B13. **nit** (l. 273–276; doubt 1): name the types: "Lean prints the three anonymous instance
arguments as `x : NormedAddCommGroup H`, `x_1 : InnerProductSpace ℂ H` and `x_2 : CompleteSpace H`".

B14. **nit** (Design length, ≈1,170 words): "States are a structure" restates the `State`
docstring's implementation note (ComplexOrder, `FunLike`), shown in full in Main. Cut those two
sentences (≈ 50 words). Otherwise the Design section adds reasons not in the boxes; no larger cut
needed.

## Writer's doubts B(1)-(4)

1. **Printing `gns_construction`:** keep. It is the headline theorem, its output is short, and the
   tutorial reads it line by line. Improve the decoding sentence (B13). Linking instead is right
   only for the long nested existentials (the `*_of_invariant*` theorems), as done.
2. **"A GNS space is never zero":** not marked; it should be (B2). It is a one-line consequence of
   the printed statement, so a remark with "the library has no separate lemma" suffices.
3. **Krein–Milman reason:** accurate; verified with `#synth` (no `LocallyConvexSpace ℝ (WeakDual ℂ
   A)` instance). Say "among the missing pieces" (B4); naming the evaluation lemmas is not needed.
4. **Citing §10.6 subsections:** appropriate and necessary, since those nodes carry the `\lean{}`
   entries for half the chapter; qualify "for an arbitrary C\*-algebra" (B7).

## Verdict and top 5

Verdict: **ready after small fixes.** The docstring pass changes no code (verified on all 15
files) and is accurate on every point the brief named (Mathlib's GNS space, weak-* set and
Krein–Milman, pure-state existence not proved, `IsIrreducible` zero case stated once, neutrally).
The chapter is accurate in its mathematics; its one error is three broken cross-chapter links
(B1), shared with the Spacetime chapter. Counts: A 7 findings (0 errors, 3 should fix, 4 nits);
B 14 findings (1 error, 4 should fix, 9 nits).

Top 5:
1. B1: `../Haag-Kastler-...` links leave the manual when deployed; use `{ref "haag-kastler"}` or
   base-relative paths. Same fix in `web/Manual/Spacetime.lean`.
2. A1: `weakStateSet` says "exactly the states", but only states ⊆ set is proved.
3. B2: mark "a GNS space is never zero" as immediate from the statement, with no library lemma.
4. A3: `omega_star_swap_conj` cites lmm:cauchy-schwarz-inequality without being in its `\lean{}`;
   add it to the proposals (14 uncited, not 13).
5. B3/B5/A2: Mathlib's `IsIrreducible` is about subsets; direct-sum projection needs both summands
   nonzero; reflow the broken `QuasiEquiv` docstring paragraph. Then the blueprint proposals: all
   confirmed except `gnsVonNeumann`/`gnsVonNeumannAlgebra` → a new def node in §10.6, not
   def:local-von-neumann; the four invariant theorems → a new algebra-agnostic node.
