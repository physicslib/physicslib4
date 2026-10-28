# Review: manual chapter on curved spacetime and general covariance (2026-10-21)

Scope: A. docstring pass `fe2a3f4` (58 docstrings, 15 files of `Physicslib4/AQFT/HaagKastlerCurved/`);
B. the uncommitted chapter `web/Manual/Curved.lean` and its rendered HTML. Read-only; nothing else
edited. Conventions applied are those of the three earlier manual reviews.

## A. Docstring pass (fe2a3f4)

### Checks that pass

- **Comments only.** For all 15 files, stripping `--` and nested `/- -/` comments (string
  literals kept) and normalising whitespace gives identical text at `fe2a3f4^` and `fe2a3f4`.
- **Blueprint labels.** Every `Blueprint: <label>` line in the 15 files names an existing
  `\label` (including `lmm:axiom5-basis-preservation` in `spacetime.tex`). Labels cited bare are
  in the node's `\lean{}`; the uncited ones use the descriptive form, as agreed.
- **Accuracy against the code and the blueprint:**
  - algebras in `Type v` independent of u (`LocalNet.{u, v}`); Axiom 4 Hilbert spaces and the
    ground-state K are in `Type v`; `exists_isLocalObservable` and `exists_gns_einstein_causality`
    put GNS witnesses in `Type v`; the trivial net is in universe 0;
  - isotony is data with non-strict ⊆, laws (a)–(c), and the blueprint design note;
  - Axiom 3 takes a common containing basis set and the Axiom 2 family as a parameter, and is
    vacuous when no such set exists;
  - Axiom 4: π is any unital *-homomorphism, not only a GNS representation; it holds for every
    net through the real part (b + b*)/2;
  - D3 note on `toAbstractIdentityComponent`: matches the blueprint formalization note word for
    word in substance; no Restriction line, correctly;
  - `stabAut` = `covEquiv` then `algCongr`; `stabAutMonoidHom` is a `MonoidHom` into
    `StarAlgEquiv.aut`;
  - KMS definition = `AQFT.IsKMSState (flowAut …)`; invariance needs only a one-parameter subgroup
    and β > 0, and continuity is needed only for the strongly continuous unitaries;
  - `IsGroundStateForFlow` is matched clause by clause;
  - `NetTheory` is over geometric spacetimes with one algebra universe, `NetEquivalence` has
    Θ as data, and ψ (not ψ⁻¹) carries the diamonds of ψ*L to those of L;
  - `relativeCommutant` and `IsIrreducibleInclusion` take any B₁, B₂ ⊆ B, and the closure
    argument is right.
- **Format.** One-sentence first lines; "Implementation note:" last before the Blueprint line;
  plain-text labels; parenthesised subscripts (α_(φ'φ), Θ_(B₂), 𝔘_(ψ*L), τ_t = α̂_(φ_t));
  present tense.
- ≺ reflexivity is not touched by this pass (no curved docstring mentions causal precedence).

### Findings

A1. **error** (rendering): `GeneralCovariance.lean` l. 65–70 (`pullbackCarrierEquiv`) and
l. 188–192 (`IsGenerallyCovariant`). The pullback is written `ψ*L`, `ψ*g`, `ψ*t`. Markdown reads
each pair of `*` as emphasis, so the rendered docstrings are garbled. In the manual you get
"The pullback ψ<em>L has the same manifold as L, with the pulled-back metric ψ</em>g …"; doc-gen4
renders it the same way. These are the only `<em>` artefacts in the chapter's HTML.
Fix: escape each one, writing `ψ\*L`, `ψ\*g`, `ψ\*t`, `𝔘_(ψ\*L)`. That is 11 occurrences, on
l. 65, 67, 68, 69, 70, 188, 190 and 191. Alternatively use code spans (`ψ^*L`) as the Spacetime
docstrings do. Rebuild the manual and check that no `<em>` remains.

A2. **should fix** (physical examples not covered by the definitions): `StabilizerAction.lean`
`stabAut` ("typically a Killing flow, such as the stationary flow of a black-hole exterior or the
boost of a de Sitter static patch"), `StabilizerKMS.lean` `flowAut` (same examples), and
`IsKMSStateForFlow` ("The Hartle–Hawking state … and the Bunch–Davies state … are the standard
examples").
- **Why they are not instances.** Neither the Schwarzschild exterior nor the static patch is a
  basis set I⁺(p) ∩ I⁻(q) with p, q in M; their "vertices" lie at infinity or on the horizon.
  In a globally hyperbolic spacetime a nonempty diamond is relatively compact. The orbits of a
  stationary or boost Killing flow are not relatively compact, apart from its fixed points (the
  bifurcation sphere). So no such flow fixes a nonempty basis set.
- **What the library then gives.** `flowAut` and `IsKMSStateForFlow` take any `B : Set`, so they
  can be applied to the exterior. But `LocalNet` constrains 𝔘(B) only on basis sets (its own
  docstring says so). For such a B neither 𝔘(B) nor `covEquiv φ B` is tied to the net's diamonds.
- **The blueprint.** It makes the same claim (§10.7 KMS subsection; "realized for the
  Hartle-Hawking and Gibbons-Hawking states" in thrm:kms-thermal-representation-in-curved-spacetime).
  This is a design question for the user; see the blueprint proposals below.
- **Fix in the docstrings.** Keep the examples as motivation and add, after them, in `stabAut`:
  "These regions are not basis sets, and no such flow fixes a nonempty diamond I⁺(p) ∩ I⁻(q) of a
  globally hyperbolic spacetime, so for basis sets the stabilizer consists of isometries such as
  rotations about a fixed timelike axis." In `IsKMSStateForFlow` replace "are the standard
  examples" by "are the motivating examples; their regions are not basis sets, on which alone the
  axioms constrain 𝔘(B), and the library constructs neither state".

A3. **nit**: `IsometricCovariance.lean`, implementation note: "𝔘(1B) and 𝔘(B), and 𝔘((φ'φ)B) and
𝔘(φ'(φB))". Write "𝔘(1 • B) and 𝔘(B), and 𝔘((φ'φ) • B) and 𝔘(φ' • (φ • B))", matching the
`φ • B` notation introduced in `LorentzianSpacetime`.

A4. **nit** (asserts what is not provided): `Net.lean`, `nonempty_haagKastlerNet` implementation
note: "a witness in an arbitrary universe would come from a `ULift` of this one". Mathlib has no
`CStarAlgebra (ULift ℂ)` instance (there is nothing under `Analysis/CStarAlgebra/`), so this is a
construction nobody has carried out. Write "the library gives no witness in other universes".
The Minkowski docstring (`HaagKastler/Net.lean` l. 385) has the same sentence; change both, or
leave both for consistency.

A5. **nit** (follow-ups outside the pass, module docstrings). The log lists the claims in
`LocalCommutativity.lean` ("genuinely diverge") and `Net.lean` (`Nonempty (Σ M, …)`). Add
`Isotony.lean`, whose module docstring calls `Isotony` "a `Prop`-valued predicate"; it is a
structure carrying data. Also `LocalAlgebra.lean`, which says Axiom 4 is "in **every** GNS
representation", the claim the pass corrected in the declaration docstring.

### A(6): the uncited declarations: proposed nodes (for the lean-blueprint agent)

I agree with the log's list. I checked each name against every `\lean{}` in `blueprint/src`;
none appears.

1. A **new node** `def:abstract-lorentzian-spacetime-interface` at the head of
   `haag-kastler-axioms-in-curved-spacetime.tex`, before Axiom 1. It would hold
   `\lean{Physicslib4.AQFT.HaagKastlerCurved.LorentzianSpacetime,
   Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent,
   Physicslib4.Spacetime.LorentzianSpacetime.instTopologicalSpaceToAbstractIdentityComponentIsom}`
   and `\uses{def:lorentzian-spacetime, def:alexandrov-topology, def:completely-spacelike,
   lmm:axiom5-basis-preservation}`. Its text: the five pieces the axioms use, the one law, and the
   bridge with the D3 note.
   - This is better than folding the interface into Axiom 1's `\lean{}`. The interface is the M
     of all five axioms, and the bridge is not part of Axiom 5.
   - Then change the Blueprint lines of `LorentzianSpacetime` and `toAbstractIdentityComponent`
     to that label.
2. thrm:haag-kastler-net-in-curved-spacetime-nonempty: add
   `HaagKastlerCurved.nonempty_haagKastlerNet` (already named in its text),
   `trivialHaagKastlerNet`, `trivialLocalNet` and `trivialLocalNetIsotony`. `trivialSpacetime`
   stays uncited.
3. def:isometric-covariance-in-curved-spacetime: add `HaagKastlerNet.covEquiv`.
   def:isotony-in-curved-spacetime: add `HaagKastlerNet.commIsotony`.
4. def:local-observable: add `HaagKastlerCurved.localObservables`.
5. def:stabilizer-action-in-curved-spacetime: add `HaagKastlerNet.stabAutHom`.
   lmm:stabilizer-action-laws-in-curved-spacetime: add `HaagKastlerNet.stabAutMonoidHom`.
6. Design question for the user, from A2 (blueprint prose; no Lean change proposed). The §10.7
   paragraphs introducing the stabilizer and KMS subsections should say that the Killing-flow
   examples act on regions that are not basis sets. They should also say that a nonempty diamond
   is fixed only by isometries such as rotations. Otherwise the blueprint needs to decide whether
   flows and KMS states should act on a class of regions larger than the basis sets (causally
   convex regions, domains of dependence). That would change `LocalNet`, a definition, so it is
   the user's decision.

## B. Chapter web/Manual/Curved.lean

### Checks that pass

- **Build.** `lake build` and `lake exe generate-manual --output _out/manual` succeed (exit 0).
  The six `leanOutput` blocks match.
- **Links.**
  - The page has `<base href="./../">`. All manual links are base-relative: `{ref}` targets, the
    Spacetime Symmetries anchor (present in its page) and the GNS/HK tags.
  - The tutorial links use `../tutorial/…`, and both tutorial anchors exist.
  - The blueprint anchors exist in `blueprint/web/`.
  - The home-page section pages `sec10-7-curved`, `sec10-8-general-covariance` exist.
- **Claims checked:**
  - the bridge pieces, including that inverses also preserve orientation;
  - the D3 wording (matches the blueprint note);
  - time reversal maps I⁺(p) onto I⁻(φ(p));
  - universes;
  - `localAlgebra_of` via (b + b*)/2;
  - Axiom 4 as a field (absent in Minkowski);
  - the Schwarzschild argument, flagged as informal, from the blueprint, and not formalised;
  - the Minkowski equivalence of Axiom 3 with quasilocal commutation (proved:
    `HaagKastler.localCommutativity_iff_exists_commute_ι`);
  - `nonempty_haagKastlerNet` printing without the second universe;
  - the Schlieder statement and its naming (the blueprint title is "Statistical Independence
    (Schlieder Property)");
  - stabiliser GNS clauses (blueprint);
  - "not a vacuum" (blueprint);
  - the dilation remark;
  - the BFV contrast;
  - the trivial theory being generally covariant mathematically: correct, since it is a
    `NetTheory.{0}` and Θ = id makes naturality trivial.
- **Style.**
  - Present tense, "As you will recall" openers, no internal memos, plain-text "Blueprint:"
    lines.
  - The Minkowski material is pointed to, not repeated.
  - About 3,000 words, inside the plan's range.

### Findings

B1. **error** (rendering, from A1): the `pullbackCarrierEquiv` and `IsGenerallyCovariant` boxes
show stray italics. The fix is A1 (in the library). Nothing to change in the chapter.

B2. **should fix** (l. 209–211, and l. 522–523): "Physically it stands in for the global
symmetry group: a Killing flow fixing the region, such as the stationary flow of a black-hole
exterior or the boost of a de Sitter static patch." By A2, no such flow fixes a basis set.
Replace with: "Physically one would like it to stand in for the global symmetry group, a Killing
flow such as the stationary flow of a black-hole exterior or the boost of a de Sitter static
patch. Those regions are not basis sets, and no such flow fixes a nonempty diamond; for a basis
set the stabiliser contains isometries such as rotations about a timelike axis. The stabiliser and
KMS definitions accept any region `B`, but the axioms constrain 𝔘(B) only on basis sets." At
l. 522–523 append: "The regions of those examples are not basis sets (see the Design section)."

B3. **should fix** (headline coverage of §10.7): additive-free locality
(thrm:additive-free-locality-in-curved-spacetime) is not mentioned. Its geometric form
`localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric` is one of the "two
results" in `Concrete.lean` (l. 584). Add after the microcausality `#check` (l. 402): "Over the
bridge, the hypothesis may be weakened to $`\mathbf{B}_1` lying in the spacelike complement of
$`\mathbf{B}_2`
({apiDocs …localVonNeumannAlgebra_le_commutant_of_subset_spacelikeComplement_geometric}[`…_geometric`]);
no algebra is attached to the complement itself."

B4. **nit** (coverage): add one sentence at l. 487–489, with `apiDocs` links, covering:
- the centre and factor results (`localVonNeumannAlgebra_center_eq_commutant`,
  `localVonNeumannAlgebra_isFactor_iff_center_eq_scalars`);
- the disjoint-or-equivalent dichotomy (`areDisjoint_or_unitaryEquiv_of_isIrreducible`);
- the invariance of the superselection type under covariance (`unitaryEquiv_gns_covEquiv`,
  `unitaryEquiv_gns_stabAut`);
- purity invariance (`isPure_precomp_stabAut_iff`).

All are §10.7 nodes; one line each keeps the chapter within length.

B5. **nit** (l. 470): `{ref "gns-design"}[unitary implementation theorems]` lands on the top of
the GNS Design section. Link the subsection instead:
`The-GNS-construction/#physicslib4-reference-manual--The-GNS-construction--Design--Covariance-and-unitary-implementation`
(anchor present, base-relative).

B6. **nit** (l. 175): back the Minkowski claim with its lemma, for example "(Minkowski:
{apiDocs Physicslib4.AQFT.HaagKastler.localCommutativity_iff_exists_commute_ι}[`localCommutativity_iff_exists_commute_ι`])".

B7. **nit** (l. 477): "being a factor is constant along a stabiliser orbit". The lemma gives
R(B₁) factor ⇒ R(gB₁) factor; constancy follows with g⁻¹. Write "being a factor is preserved
by the stabiliser".

B8. **nit** (l. 88–89 vs l. 475): the Overview writes $`R(\varphi(\mathbf{B}_1))`, Main
$`R(g\mathbf{B}_1)`. Use g for stabiliser elements in both.

B9. **should fix** (l. 236–238; doubt 3, the uncited BFV sentence): keep the sentence and cite
the paper. The manual has no citation set-up: `Manual` does not import `Tutorial`, and
`Papers.lean` lives in the `Tutorial` library. So use a plain link: "…of Brunetti, Fredenhagen
and Verch ([Commun. Math. Phys. 237 (2003) 31–68](https://doi.org/10.1007/s00220-003-0815-7);
compared in [tutorial chapter 1](../tutorial/AQFT-in-brief/…))". Point the second link at the
anchor of the section containing `AQFTInBrief.lean` l. 568. Later, move `Papers.lean` to the
shared `Book` library and use `{citep}` in both books; that belongs to the conventions chapter
round.

### The writer's doubts

1. **The three "not proved" statements.**
   - Reeh–Schlieder (l. 428): accurate (no such theorem in `Physicslib4/`) and well placed,
     right where cyclicity enters as a hypothesis.
   - Hartle–Hawking/Bunch–Davies (l. 522–523): accurate and well placed, directly after the KMS
     docstring that names them. It is incomplete, though: add the basis-set point (B2).
   - No theory proved generally covariant (l. 559–561): accurate (`IsGenerallyCovariant` and
     `NetEquivalence` have no uses outside `GeneralCovariance.lean`). The trivial-theory remark
     is correct and correctly hedged. Well placed, after the postulate.
2. **The `%28`/`%29` anchor (l. 244): robust; keep it.**
   - The target id is `sctn:axiom-3-(local-commutativity)` in
     `blueprint/web/chptr-haag-kastler-axioms-in-curved-spacetime.html`.
   - Browsers percent-decode the fragment before matching, as the HTML spec's "indicated part"
     algorithm requires, so `#sctn:axiom-3-%28local-commutativity%29` resolves.
   - The escaping also avoids raw parentheses ending the link destination.
   - The only alternative is linking the chapter page without an anchor, which loses precision.
     The parentheses come from the blueprint label itself (sec9, not ours to rename).
3. **The BFV sentence:** add the citation (B9), as a DOI link for now. It is accurate and
   useful: it tells the expert reader which notion of covariance this is not.

## Verdict and top 5

Verdict: **ready after small fixes.**
- The docstring pass changes no code (verified on all 15 files) and is accurate against the code
  and the blueprint. Its one error is a Markdown rendering defect in two docstrings.
- The chapter builds, its links resolve, and its claims hold.
- The one substantive issue is shared with the blueprint: the Killing-flow and Hartle–Hawking
  examples do not fall under the definitions, because those regions are not basis sets. The text
  should say so, and the user should decide whether the blueprint changes.

Counts: A: 1 error, 1 should fix, 3 nits (plus 6 blueprint proposals). B: 1 error (the same
defect as A1), 3 should fix, 5 nits.

Top 5:
1. A1/B1: escape `ψ*L`, `ψ*g`, `ψ*t` in `pullbackCarrierEquiv` and `IsGenerallyCovariant`
   (rendered as italics).
2. A2/B2: the Killing-flow examples (black-hole exterior, de Sitter static patch) are not basis
   sets, and no such flow fixes a nonempty diamond. Say so in `stabAut`, `IsKMSStateForFlow` and
   the chapter (l. 209–211, 522–523). Raise the design question (proposal 6) with the user.
3. B3: mention additive-free locality and its geometric form.
4. B9: cite Brunetti–Fredenhagen–Verch with a DOI link.
5. A(6): the new interface node and the five `\lean{}` additions for the uncited declarations.
