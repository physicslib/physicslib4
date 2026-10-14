# D4 progress: module-docstring listings for HELPER declarations

Per `notes/agents/d4-triage-2026-10-14.md`: add each HELPER declaration (and the
`IsResolvent` structure) to its file's module docstring, in a "Supporting lemmas"
list matching the file's existing docstring style. `isAlexandrovBasisSet_smul` is
skipped (list-generation anomaly, not an orphan). Docstring-only edits; no
statement, proof, or declaration docstring touched.

- `Physicslib4/AQFT/HaagKastler/LorentzCovariance.lean`: added "Supporting lemmas"
  listing `timelike_separated_smul_iff`, `spacelike_separated_smul_iff`,
  `null_separated_smul_iff`.
- `Physicslib4/AQFT/HaagKastler/Net.lean`: added "Supporting lemmas" listing
  `commute_ι_of_spacelike_symm`, `isQuasilocalObservable_of_isSelfAdjoint`,
  `isQuasilocalObservable_add`, `isQuasilocalObservable_smul`,
  `isQuasilocalObservable_smul_add_smul`.
- `Physicslib4/AQFT/HaagKastler/QuasilocalObservable.lean`: added "Supporting
  lemmas" listing `quasilocalObservables_eq`, `one_mem_quasilocalObservables`,
  `add_mem_quasilocalObservables`, `smul_mem_quasilocalObservables`.
- `Physicslib4/AQFT/HaagKastlerCurved/LocalAlgebra.lean`: added "Supporting
  lemmas" listing `localObservables_eq`, `one_mem_localObservables`,
  `add_mem_localObservables`, `smul_mem_localObservables`.
- `Physicslib4/AQFT/HaagKastlerCurved/Net.lean`: added "Supporting lemmas"
  listing `commIsotony_injective`, `commute_of_spacelike_symm`,
  `isLocalObservable_of_isSelfAdjoint`, `isLocalObservable_add`,
  `isLocalObservable_smul`, `isLocalObservable_smul_add_smul`, `trivialSpacetime`.
- `Physicslib4/AQFT/PositiveEnergy.lean`: added "Supporting lemmas" listing
  `exp_generator_unique`.
- `Physicslib4/GNS/PureStateExists.lean`: added "Supporting lemmas" listing
  `State.toWeakDual_mem_weakStateSet`.
- `Physicslib4/GNS/Superselection.lean`: added "Supporting lemmas" listing
  `intertwines_zero`, `restrictStarAlgEquiv'`. (The three HEADLINE items in this
  file — `not_areDisjoint_self`, `UnitaryEquiv.not_areDisjoint`,
  `UnitaryEquiv.quasiEquiv` — are left untouched; they are blueprint-citation
  proposals, not docstring listings.)
- `Physicslib4/Operators/DensityTheorem.lean`: added "Supporting lemmas" listing
  `blockEntry_apply`.
- `Physicslib4/Spacetime/CausalComplement.lean`: added "Supporting lemmas"
  listing `isCausallyComplete_causalClosure`,
  `spacelikeComplement_spacelikeComplement_of_isCausallyComplete`.
- `Physicslib4/Spacetime/CausalStructure.lean`: added "Supporting lemmas" listing
  the triad `isTimelike_smul_iff`, `isNull_smul_iff`, `isSpacelike_smul_iff`
  (only the last was flagged as an orphan; listed all three as siblings).
- `Physicslib4/Spacetime/Curves.lean`: added "Supporting lemmas" listing
  `OrientedSmoothCurve.toSmoothCurve_surjective`,
  `isTimelikeSmoothCurve_toSmoothCurve_ofPath`.
- `Physicslib4/Spacetime/LorentzCausality.lean`: added "Supporting lemmas"
  listing `chronologicallyPrecedes_smul_iff` and `isCompletelySpacelike_smul`
  (both tables in the memo point to this file).
- `Physicslib4/Spacetime/Minkowski.lean`: added "Supporting lemmas" listing
  `mfderiv_extChartAt_symm_minkowski`.
- `Physicslib4/Spectral/BorelCalculus.lean`: added "Supporting lemmas" listing
  `borelCalculus_of_notMem`.
- `Physicslib4/Spectral/Forms.lean`: added "Supporting lemmas" listing
  `norm_le_of_tendsto_of_bound`.
- `Physicslib4/Spectral/OperatorIntegral.lean`: added "Supporting lemmas" listing
  `isSelfAdjoint_integral_of_real`.
- `Physicslib4/Spectral/Unbounded/Spectrum.lean`: no edit. The memo marks
  `IsResolvent` "already documented" (named and explained in prose in this
  file's existing module docstring), matching the "already listed, leave it"
  instruction.

## Verification

- `lake build`: succeeds (3358/3358 jobs). Pre-existing warnings in
  `Physicslib4/Spectral/OperatorIntegral.lean` (unnecessary `simpa`, two long
  lines) and `Physicslib4/Spacetime/CrossMetricIsometry.lean` (`letI`/`haveI`
  style) are at proof lines far from the docstring edits and are unrelated to
  this task; no new warnings appeared.
- `python3 scripts/check_temporal_wording.py`: `OK: no temporal wording or
  stray version strings.`
