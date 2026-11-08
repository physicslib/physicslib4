# Review: manual chapter "The Reeh–Schlieder theorem" (2026-11-08)

Scope: `web/Manual/ReehSchlieder.lean`, and the edited passages in `web/Manual/NotProved.lean`,
`web/Manual/HaagKastler.lean`, `web/Manual/Curved.lean` and `web/Manual/Conventions.lean`.
Checked against `blueprint/src/sections/sec10/reeh-schlieder.tex` and the Lean statements and
docstrings in `Physicslib4/AQFT/HaagKastler/ReehSchlieder/*.lean`,
`Physicslib4/AQFT/PositiveEnergyHolomorphic.lean`, `Physicslib4/Analysis/EdgeVanishing.lean`, plus
`PositiveEnergy.lean`, `LocalVonNeumann.lean` and `VacuumState.lean` where the chapter relies on them.

VERDICT: REVISE (4 blocking findings, all one-sentence wording fixes; the mathematics and the
names are otherwise correct).

## What was verified (no action needed)

- Blueprint links: all 16 labels used in the chapter (`sctn:`, `def:`, `lmm:`, `thrm:`, `crllr:`)
  exist as `\label{...}` in `reeh-schlieder.tex`.
- Lean names: all 30 distinct `{docstring}` / `{apiDocs}` names exist with the exact fully
  qualified name (namespaces checked: `Physicslib4.AQFT.HaagKastler[.HaagKastlerNet]`,
  `Physicslib4.AQFT`, `Physicslib4`). None is `private`. `localVonNeumannAlgebra_separating` is in
  `HaagKastlerNet` (`HaagKastler/LocalVonNeumann.lean:29,206`). The `#check` outputs come from the
  successful build.
- No `sorry` in the six source files, so line 94 ("with no `sorry`") is accurate.
- `reeh_schlieder` hypotheses: π, Ω, U, hU, hpos, hB₁, hB, hB₁B. No additivity and no cyclicity
  (lines 68–74, 114–129 are accurate).
- Nonempty diamonds: `IsWeaklyAdditive` and `IsWeaklyAdditiveVonNeumann` quantify over nonempty B;
  every cyclicity corollary has `hne : B.Nonempty`; `hcyc` of `reeh_schlieder_cyclic` and
  `reeh_schlieder_separating` has `B'.Nonempty`; C may be empty in the separating corollary.
  The empty-diamond paragraph (lines 133–141) matches blueprint line 157.
- Chain (lines 160–169): `IsWeaklyAdditive.isWeaklyAdditiveVonNeumann` holds for every π; the
  second step needs Ω cyclic for π(𝔘) and uses `apply_mem_closure_translationGeneratedAlgebra`.
  Matches blueprint lines 193 and 480.
- Vacuum corollary: hypotheses are hwa, π, Ω, U (indexed by the Poincaré group), hU, hpos, hcyc.
  No state, no reproduction condition. Matches the docstring and blueprint line 501.
- Separating corollary uses `IsCompletelySpacelike ... B C`, matching blueprint line 514.
- Proof route: one complex variable, one future-timelike direction at a time, no joint spectral
  measure (blueprint line 3). The basis `e₀`, `e₀ + ½eᵢ` matches `futureTimelike_basis`. The group
  law only at φ (`hmul`) matches `inner_translation_eq_zero_add_smul`. `IsPositiveEnergy` allows an
  unbounded positive generator (`PositiveEnergy.lean:16–17,74`), so line 181 is accurate.
- Curved spacetime: NotProved.lean and Curved.lean say correctly that Reeh–Schlieder is proved
  only for Minkowski; the curved axioms carry no spectrum condition (`Curved.lean:511`).
  Conventions.lean: "the intersection property for general spacetimes" is a real appendix entry
  (`NotProved.lean:50`).
- Nothing claims that a vacuum state of a nontrivial net exists (`HaagKastler.lean:607` keeps "It
  does not construct a vacuum state of a nontrivial net").
- Style: `python3 scripts/check_temporal_wording.py` reports "OK: no temporal wording or stray
  version strings." No absolute paths and no version numbers. Every `lean` input code line is at
  most 60 columns. The long lines are in `leanOutput` blocks, which are verbatim Lean output and
  are also long in `Stone.lean` and `HaagKastler.lean`.

## Blocking findings

1. **`web/Manual/ReehSchlieder.lean:56-57`: "unconditionally" overclaims.** Cyclicity for local
   algebras needs an additivity hypothesis and Ω cyclic for π(𝔘) (see the chapter's own
   lines 116–118). Replace
   "Its cyclicity hypothesis is exactly what the Reeh–Schlieder theorem supplies,
   so for the vacuum the property holds unconditionally."
   with
   "Its cyclicity hypothesis is exactly what the Reeh–Schlieder theorem supplies,
   so for the vacuum of a weakly additive net the property needs no separate cyclicity
   hypothesis."

2. **`web/Manual/ReehSchlieder.lean:61-64`: the modular-theory bullet is not marked as
   unformalized.** Append to the end of the bullet (after "restricted to a wedge."):
   " None of these is formalized in the library; they are mentioned as context."

3. **`web/Manual/ReehSchlieder.lean:206-207`: "which is the case for the GNS representation"
   claims more than the library proves.** The library's covariant GNS result for a vacuum state
   (`IsVacuumState.exists_gns_irreducible_covariant`) assumes purity and, by its docstring
   (`VacuumState.lean:159-162`), does not use the spectrum condition. So no Lean result shows
   that the GNS data satisfy `hpos`. Replace
   "The statement therefore applies to the witnessing data of every vacuum state with $`\Omega`
   cyclic, which is the case for the GNS representation."
   with
   "The statement therefore applies to the witnessing data of every vacuum state for which
   $`\Omega` is cyclic for $`\pi(\mathfrak{U})`."

4. **`web/Manual/HaagKastler.lean:468-470` (edited passage): leaves out the additivity
   hypothesis.** The chapter itself says cyclicity cannot hold without one. Replace
   "In a vacuum representation the cyclicity is supplied by the
   Reeh–Schlieder theorem ({ref "reeh-schlieder"}[The Reeh–Schlieder theorem]), and the corollary
   `reeh_schlieder_separating` combines the two; here cyclicity is a hypothesis."
   with
   "In a vacuum representation of a weakly additive net, with $`\Omega` cyclic for
   $`\pi(\mathfrak{U})`, the cyclicity is supplied by the Reeh–Schlieder theorem
   ({ref "reeh-schlieder"}[The Reeh–Schlieder theorem]), and the corollary
   `reeh_schlieder_separating` combines the two; here cyclicity is a hypothesis."

## Optional findings

5. **`web/Manual/ReehSchlieder.lean:41-43`.** The overview states the theorem before mentioning
   additivity. Suggested: "For every nonempty diamond $`\mathbf{B}`, however small, and under a
   mild additivity assumption on the net discussed below, $`\Omega` is already cyclic for the
   local algebra $`\pi(\mathfrak{U}(\mathbf{B}))`: ..."

6. **`web/Manual/HaagKastler.lean:609-611`.** "The consequences that do use the spectrum
   condition, the Reeh–Schlieder theorem and its corollaries, are in ..." reads as an exhaustive
   list. Suggested: "The Reeh–Schlieder theorem and its corollaries, which use the spectrum
   condition, are in {ref "reeh-schlieder"}[The Reeh–Schlieder theorem]."

7. **`web/Manual/ReehSchlieder.lean:133`.** For precision, replace "for $`q` not in the future of
   $`p`" with "for $`q` not in the chronological future $`I^+(p)` of $`p`".

8. **`web/Manual/Conventions.lean:108-111`.** The source lines are ragged ("are marked where /
   they arise and collected / in the"). This is cosmetic only, since the rendering is unaffected.
   Reflow to: "existence of pure states and the intersection property for general spacetimes, are
   marked where they arise and collected in the {ref "not-proved"}[appendix]. Where ..."
