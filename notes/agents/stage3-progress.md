# Stage 3 progress log

## Item 1 (R15-3): extract shared diagonal/product estimate in OperatorIntegral.lean

- File: `Physicslib4/Spectral/OperatorIntegral.lean`.
- Added a private lemma `norm_mul_sub_mul_lt` (placed in the `Physicslib4.Spectral` namespace,
  right before `namespace ProjectionValuedMeasure` opens, so it is visible both inside that
  namespace and later at the `Spectral` level) capturing the shared pointwise ε/2-splitting
  estimate: given bounds `Mf` on `‖f‖`, `Mr` on `‖r‖`, and closeness `‖f - s‖ < ε/(2*Mr)`,
  `‖g - r‖ < ε/(2*Mf)`, concludes `‖f*g - s*r‖ < ε`.
- `integral_bddMeasurable_mul`'s `hdiag` block now derives its final estimate from
  `norm_mul_sub_mul_lt` (instantiated with `Mf := Mf'+1`, `Mr := Mg'+1`) instead of reproving the
  calc chain inline; removed the stray "cannot be cited here" comment and replaced it with an
  accurate one explaining the diagonal vs. product-filter distinction.
- `tendstoUniformly_mul_of_bounded`'s final `intro i hi j hj x` branch now calls the same lemma
  (`Mf := M_f`, `Mr := M_r`) instead of re-deriving `hterm1`/`hterm2`/`hnorm`/`hsum`.
- Net diff: 46 insertions, 75 deletions (file shrinks by ~29 lines) despite adding a new
  documented lemma, since both call sites shrank by much more than the lemma's size.
- Verified: `lake env lean Physicslib4/Spectral/OperatorIntegral.lean` compiles with the same two
  pre-existing `unnecessarySimpa` warnings as before the change (at `simpa`s unrelated to this
  edit, confirmed by diffing against the pre-edit file via `git stash`). No new warnings or
  errors.

## Item 2 (R01-3): dedupe `nullSubmodule_isClosed` / `lmm2`

- File: `Physicslib4/GNS/NullSpace.lean`.
- Checked the current state: `lmm2` (lines 163-165) already derives its closedness clause
  directly from `nullSubmodule_isClosed`:
  `⟨nullSubmodule ω, nullSubmodule_coe ω, nullSubmodule_isClosed ω⟩`. There is no independent
  re-derivation of the closedness argument inside `lmm2` to remove; the helper lemma is already
  the single source of that proof, matching exactly what R01-3 (and this stage's item 2) asks for.
  (R01-3's own verdict was "plausible," not "confirmed," and noted the split is documented as
  deliberate in the module docstring.) No edit made; no diagnostics run needed since no code
  changed.

## Item 3 (R07-1): drop unused `_hv` in `reverse_cauchy_schwarz_of_lorentzianAt`

- SKIPPED. Checked `.git/lean-kit/approvals.json` for an approval covering
  `Physicslib4/Spacetime/LorentzCauchySchwarz.lean`; the only "D7"-noted entry present is for
  `Physicslib4/GNS/PureStateExists.lean` (a different decision also labelled D7 in this project's
  numbering), not for `LorentzCauchySchwarz.lean`. No approval is listed for this file, so per the
  task's instruction this item is skipped rather than applied.
- No edit made to `Physicslib4/Spacetime/LorentzCauchySchwarz.lean`; the unused `_hv : B v v < 0`
  hypothesis in `reverse_cauchy_schwarz_of_lorentzianAt` (lines 46-93) remains as committed.
- Blueprint node: `lmm:reverse-cauchy-schwarz` in
  `blueprint/src/sections/sec10/spacetime.tex:67-86`, tagged
  `\lean{Physicslib4.reverse_cauchy_schwarz_of_lorentzianAt, Physicslib4.Spacetime.reverse_cauchy_schwarz}`.
  Its statement explicitly requires both vectors timelike: "let $v, w$ be timelike, that is
  $g(v,v) < 0$ and $g(w,w) < 0$," so the blueprint's stated hypotheses match the Lean signature
  (symmetric in `v`/`w`) even though the proof only needs `w` timelike.
- If the user approves this file later (`lean_guard.py approve --file
  Physicslib4/Spacetime/LorentzCauchySchwarz.lean`), the callers that pass the now-unused argument
  and would need updating are: `Physicslib4/Spacetime/LorentzCone.lean:73`,
  `Physicslib4/Spacetime/LorentzOrthogonal.lean:57,219-220`.

## Item 3 follow-up: approval granted, change applied

- Re-checked `.git/lean-kit/approvals.json`: an entry for
  `Physicslib4/Spacetime/LorentzCauchySchwarz.lean` (note "D7", expires
  2026-10-14T17:22:03+00:00) is now present. Applied the change.
- `Physicslib4/Spacetime/LorentzCauchySchwarz.lean`: dropped `_hv : B v v < 0` from
  `reverse_cauchy_schwarz_of_lorentzianAt`'s signature (now `(hw : B w w < 0)` is the only
  vector hypothesis). Updated the theorem's docstring and the module docstring to say only `w`
  needs to be timelike, and to note this is stronger than the blueprint's `lmm:reverse-cauchy-schwarz`
  (which states both `v` and `w` timelike).
  `Spacetime.reverse_cauchy_schwarz` (the blueprint-tagged wrapper, same file) keeps both `hv`/`hw`
  unchanged to match the blueprint's symmetric statement; its proof no longer needs `hv` (only used
  to forward to the generalized lemma), so `hv` is renamed to `_hv` (binder rename only, not a
  statement change) and its docstring notes the hypothesis on `v` is now unused-by-design. The
  internal call site was updated to drop the obsolete `hv'` argument.
- Updated callers (grep-confirmed, no others found):
  - `Physicslib4/Spacetime/LorentzCone.lean:73` (`reverse_triangle_of_lorentzianAt`'s proof):
    dropped the `hv` argument from the call; `v` is still inferred, here from the `have hcs : ...`
    type ascription.
  - `Physicslib4/Spacetime/LorentzOrthogonal.lean:57` (`nonneg_of_orthogonal_timelike`'s proof):
    dropped `ht`'s positional use for the (now-removed) first hypothesis; since the surrounding
    `have hcs := ...` has no type ascription, `v` is no longer inferable from context, so added
    `(v := t)` explicitly.
  - `Physicslib4/Spacetime/LorentzOrthogonal.lean:219-220` (`bilin_neg_of_inner_t_neg`'s proof):
    same pattern, both calls updated to `(v := t) hsymm hL hv` / `(v := t) hsymm hL hw`.
  - No guard blocks encountered; all three call-site files are not themselves restricted beyond
    the normal proof-editing rules (only `LorentzCauchySchwarz.lean`'s statement needed approval,
    which was granted).
- Verified: `lake build Physicslib4.Spacetime.LorentzCauchySchwarz`,
  `...LorentzCone`, `...LorentzOrthogonal` each build clean individually (first attempt at
  `LorentzCone.lean` hit a stale-olean type mismatch from checking against the pre-edit compiled
  `LorentzCauchySchwarz.olean`; rebuilding that file first resolved it). Whole-project
  `lake build`: 3358/3358 jobs, succeeds, no warnings in any of the three edited files (confirmed
  by grepping the build output for the three filenames: no hits). `lake lint`: "Linting passed for
  Physicslib4" — in particular no `unusedArguments` warning fired on `Spacetime.reverse_cauchy_schwarz`
  despite `_hv` now being unused there, since the binder is prefixed with `_`.
