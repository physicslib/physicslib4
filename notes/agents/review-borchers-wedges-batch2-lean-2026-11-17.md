# Review: Lean statements for borchers-wedges batch 2 (2026-11-17)

Files reviewed:
- `Hilbert6/AQFT/HaagKastler/Wedges.lean`
- `Hilbert6/AQFT/HaagKastler/RegionAlgebra.lean`
- `Hilbert6/AQFT/HaagKastler/CovariantVacuum.lean`

There are 48 labels, all sorry'd.

## Pass 1 — REVISE

The definitions are faithful:
- **`boostMatrix`:** the matrix and the convention Λ(s)l₊ = e^{s}l₊ are right, and its inverse
  proofs are real.
- **`IsCovariantVacuumRep`, covariance:** the covariance field is exactly the library's `lieConj`
  form.
- **`IsCovariantVacuumRep`, satisfiability:** a trivial net satisfies all its fields.

Required fixes:
1. Drop the unused `hM` from `isCyclicSeparatingVector_of_subset_centralizer`.
2. Remove the `hM` binders from `wedge_modular_covariance` and `wedge_stabiliser_commute`, passing
   `regionVonNeumann_isVonNeumannSet` inline instead.
3. Add a second **Restriction:** line to `IsCovariantVacuumRep`: positive energy is assumed along
   lightlike directions too.

## Pass 2

All three fixes are applied, and the module build succeeds.

Open item: `wedgeBoost` depends on `sorryAx` through the boost-matrix Lorentz, proper and
orthochronous lemmas until those lemmas are proved.
