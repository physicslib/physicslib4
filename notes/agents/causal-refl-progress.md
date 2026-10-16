# Progress log: reflexive causal precedence (note `causal-refl`)

Plan: `notes/agents/plan-reflexive-causal-precedence-2026-10-16.md`.

## 2026-10-16 `Physicslib4/Spacetime/Causality.lean` compiles

- `CausallyPrecedes M t p q := Relation.ReflTransGen (M.CausalSegmentPrecedes t) p q`; docstring
  states reflexivity, the Hawking–Ellis convention and the relation to `IsCausalTrip`.
- `NoClosedCausalCurve t := ∀ p, ¬ M.IsCausalTrip t p p`; docstring updated.
- `causallyPrecedes_asymm` removed; `isCausalTrip_asymm` added.
- Added: `causallyPrecedes_refl` (`@[refl]`), `causallyPrecedes_iff_eq_or_isCausalTrip`,
  `causallyPrecedes_of_isCausalTrip`, `isCausalTrip_trans`, `isCausalTrip_of_chronologicallyPrecedes`,
  `isSpacelikeRelated_irrefl`.
- Repaired: `causallyPrecedes_trans`, `causallyPrecedes_of_chronologicallyPrecedes`,
  `chronologicallyPrecedes_irrefl`, `causallyPrecedes_antisymm` (statements unchanged).
- Docstrings: module header, `IsSpacelikeRelated`, `causallyPrecedes_antisymm` ("partial order").
- Blueprint `spacetime.tex` still has `\lean{...causallyPrecedes_asymm}`; for the blueprint stage.

## 2026-10-16 `Physicslib4/Spacetime/LorentzCausality.lean` compiles

- Repaired `causallyPrecedes_smul` (`Relation.ReflTransGen.lift`); docstring mentions the
  reflexive case. Other proofs compile unchanged.

## 2026-10-16 `Physicslib4/Spacetime/CausalComplement.lean` compiles

- Added `Spacetime.disjoint_spacelikeComplement`, `LorentzianSpacetime.disjoint_spacelikeComplement`,
  `LorentzianSpacetime.spacelikeComplement_univ`, `LorentzianSpacetime.inf_causalComplement`,
  `LorentzianSpacetime.sup_causalComplement`.
- Section comment on orthocomplementation rewritten (it claimed a point is spacelike to itself).
- No existing proof needed repair.

## 2026-10-16 Whole project

- `lake build` succeeds; no new warnings (the remaining warnings are the existing module-system
  and `haveI`/`letI` style warnings in untouched files). No downstream proof needed repair.
- `lake lint` passes.
- Axioms (`propext`, `Classical.choice`, `Quot.sound` only): `causallyPrecedes_trans`,
  `causallyPrecedes_refl`, `causallyPrecedes_iff_eq_or_isCausalTrip`, `causallyPrecedes_antisymm`,
  `isCausalTrip_asymm`, `isSpacelikeRelated_irrefl`, `causallyPrecedes_smul_iff`, both
  `disjoint_spacelikeComplement`, `inf_causalComplement`, `sup_causalComplement`, both
  `einstein_causality`.
- Docstring grep: no other stale claim found.

## 2026-10-16 Blueprint stage 3 (`blueprint/src/sections/sec10/spacetime.tex`)

- 1. `def:causal-trip`: $p \prec q$ iff $p = q$ or a causal trip; "possibly degenerate" parenthetical
  replaced by the Hawking–Ellis reflexivity sentence; `\lean{}` gains `causallyPrecedes_refl`,
  `causallyPrecedes_iff_eq_or_isCausalTrip`, `causallyPrecedes_of_isCausalTrip`.
- `thrm:precedence-transitive`: statement adds concatenation of causal trips; `\lean{}` gains
  `isCausalTrip_trans`; proof covers the trivial case of ≺.
- 2. `def:no-closed-causal-curve`: stated as "no causal trip from a point to itself"; notes that
  ¬(p ≺ p) fails since ≺ is reflexive.
- 3. `thrm:causal-order-refinements`: asymmetry stated for causal trips; antisymmetry of ≺ and
  irreflexivity of ≪ kept; "strict partial order" corrected to "partial order"; proof rewritten.
- 4. `def:causal-future-and-causal-past`: adds p ∈ J^±(p). `def:spacelike-related`: adds that no
  point is spacelike related to itself. `def:causal-diamond` / `lmm:causal-diamond-structure`:
  unchanged (no Lean lemma for J^+(p) ∩ J^-(p) = {p}).
- 5. `\lean{}` additions: `lmm:chronological-implies-causal` + `isCausalTrip_of_chronologicallyPrecedes`;
  `def:spacelike-related` + `isSpacelikeRelated_irrefl`; `def:spacelike-complement` + both
  `disjoint_spacelikeComplement`, `spacelikeComplement_univ` (statement: B ∩ B^⊥ = ∅, univ^⊥ = ∅);
  `thrm:causally-complete-lattice` + `inf_causalComplement`, `sup_causalComplement` (statement:
  orthocomplemented; the false "irreflexive, a point is spacelike to itself" parenthetical removed;
  proof cites `lmm:spacelike-complement-de-morgan`, not `thrm:causal-complement-de-morgan`, to
  avoid a cycle).
- 6. Checked the other affected nodes; statements still hold. `thrm:causal-precedence-lorentz-invariant`
  proof gains the trivial case p = q. Grep of `blueprint/src/sections/` and `home_page/`: two false
  claims in `home_page/sec10-5-spacetime.md` (line 16 "strict partial order"; line 17 "orthocomplement
  law fails … a point is spacelike-separated from itself") rewritten; the "(+N more)" counts there
  are updated for the six nodes with new `\lean{}` names.
- `leanDeclaration` recorded for the 7 edited nodes. `blueprint_refresh` OK; `blueprint_validate`:
  only the 14 known `conv:` errors; `check_temporal_wording.py` OK.
- Review fix: `lmm:spacelike-complement-de-morgan` block (tags unchanged) moved to directly before
  `thrm:causally-complete-lattice`, removing the forward reference; lattice proof cites it for
  ∅^⊥ = whole spacetime (empty-family case). Home page not renumbered. Refresh OK; validate: only
  the 14 known `conv:` errors.
