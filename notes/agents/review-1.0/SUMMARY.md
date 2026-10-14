# 1.0 pre-release review: consolidated summary

Date: 2026-10-11. Reports R01–R16 in this directory (R14–R16 are top-ups for ranges R02, R08, R12 skipped).
No blockers. 50 findings: 7 major, 23 minor, 20 nit (informational entries excluded).

## Major

- R13-8 / R11-1 / R13-7 / R10-1 / R01-5 / R14-2: no `**Restriction:**` line exists anywhere in `Physicslib4/`,
  yet several restrictions are unrecorded: oriented identity component in curved Axiom 5 (`Concrete.lean`);
  GNS witnesses pinned to `Type` rather than `Type u` (~14 declarations, incl. `IsGroundStateForFlow`, protected);
  `[Nontrivial A]` on `isCompact_weakStateSet`; `IsGeodesic` only for `Spacetime` (protected).
- R13-6 / R06-1 / R10-2: proved, documented theorems with no blueprint `\lean{}` citation
  (`exists_isLocalObservable`, `nonempty_haagKastlerNet_identityComponent`, `strongContinuous_of_weak`, ...).
- R07-2, R07-4: the orthochronous Lorentz group section of `Minkowski.lean` and most of `LorentzCausality.lean`
  have no blueprint nodes.
- R01-1: `thrm:gns-construction-theorem` `\uses{lmm1, lmm2, cauchy_schwarz_inequality}` is spurious; the Lean proof
  uses Mathlib's GNS (R01-2: those lemmas are then unused).
- R16-1: `scripts/check_temporal_wording.py` misses bare "no longer", "now", "previously".

## Themes for a staged fix plan

1. Restriction lines (protected decisions first: universe of GNS witnesses, `IsGeodesic` generality).
2. Blueprint coverage: new nodes or `\lean{}` entries for uncited Lean (R06-1, R07-2, R07-4, R10-2, R13-6, R02-1, R15-4, R06-2).
3. `\uses{}` accuracy: R01-1, R04-1, R15-1, R03-1 (decide a convention: direct vs. transitive).
4. Unexplained `set_option`/`erw`: R07-3, R08-1, R13-1, R13-2, R13-4, R04-2, R03-2.
5. Docstrings and comments: R13-3 (misplaced docstring), R13-5, R15-2 (leaked "another prover" comment), R01-4, R10-3, R14-1.
6. Code tidying: R15-3 (duplicated 70-line proof), R01-3, R07-1 (unused hypothesis).
7. Prose and home page: R09-1 (wrong lemma range, `sec10-6-haag-kastler.md:90`), R05-1, R12-1, R12-2, R14-3, R15-5, R02-3.
8. CI and infrastructure: R16-1, R16-2, R16-3, R03-3 (stale verify receipt).
