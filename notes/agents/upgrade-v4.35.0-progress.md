# Upgrade to Lean/Mathlib v4.35.0: progress log

## Physicslib4/Geometry/PseudoRiemannian/Flat.lean

- Declaration: `Physicslib4.Geometry.isCovariantDerivativeOn_fderiv` (smul case).
- Cause: in Mathlib v4.35.0 the Leibniz term of `IsCovariantDerivativeOn` is stated with
  `d% g x` (`mvfderiv`, i.e. `fromTangentSpace (g x) ∘L mfderiv% g x`) rather than with a bare
  `mfderiv`, and `mfderiv_eq_fderiv` now reads
  `mfderiv% f x = (fromTangentSpace (f x)).symm ∘L fderiv 𝕜 f x ∘L fromTangentSpace x`.
  The old `rw [← mfderiv_eq_fderiv] at h` no longer finds its pattern.
- Fix: rewrite the goal with `mvfderiv_eq_fderiv`
  (`d% f x = fderiv 𝕜 f x ∘L fromTangentSpace x`), then close it with `exact h`
  (the composition with `fromTangentSpace x` is definitionally the identity).

## Physicslib4/GNS/Irreducibility.lean

- Declaration: `Physicslib4.GNS.isAbelian_iff_le_commutant` (deprecation warning only).
- Cause: `SetLike.le_def` is deprecated in Mathlib v4.35.0 in favour of `IsConcreteLE.le_iff`.
- Fix: one-line switch of the simp lemma to `IsConcreteLE.le_iff`.

## Verification

- `lake build`: succeeds (3403 jobs), no errors, no deprecation warnings.
- `lake lint`: passes.
- Axioms of both repaired theorems: `propext`, `Classical.choice`, `Quot.sound`.
- New warnings: Lake reports, for most files, "imports `Mathlib.…` from package `mathlib`,
  which is designed for use with the module system; consider adding `module` to the start of
  this file". Mathlib v4.35.0 uses the module system; silencing this means adding `module`
  headers project-wide, which is a design decision left open.
- Other warnings (`haveI`/`letI` style, flexible `simp`, unnecessary `simpa`, long lines,
  empty line in `GNS/Superselection.lean`) are style lints on unchanged source. No pre-upgrade
  build log is available to compare against line by line; the `haveI`/`letI` and
  `OperatorIntegral` warnings are recorded as pre-existing in `d4-progress.md`.
