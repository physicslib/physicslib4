# Review: five named definitions in borchers-wedges.tex (2026-11-17)

This was a narrow review of the diff. **Verdict: PASS.**

The five definitions are:
- `def:wedge-modular-covariance`
- `def:internal-symmetry`
- `def:half-sided-translation`
- `def:wedge-modular-defect`
- `def:wedge-reflection`

All five are correct, well typed and faithful to the prose they replace. No statement was strengthened or weakened:
- the lemmas needing only (B1) or (B2) still assume only that;
- `crllr:borchers-reversed` is unchanged in content, with a remark on why it applies the predicate to (M′, Ω).

The optional fixes are applied:
- a `\uses` edge on `def:half-sided-translation`;
- the remarks moved out of the two definition environments;
- one sentence reworded.
