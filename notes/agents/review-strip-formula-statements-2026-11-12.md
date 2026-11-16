# Review: stage 4 Lean statements (StripFormula.lean), 2026-11-12

VERDICT: PASS. All 27 labels (3 definitions, 24 theorems) are faithful and chain to `strip_formula` and `eq_zero_of_integral_exp_mul_eq_zero`. The rectangle form in `strip_rectangle_subset` matches `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`; the Fourier hypothesis matches Mathlib's convention at θ = −2πw. The formalizer's generalizations (dropped unused M, continuity, differentiability, T > 0) are acceptable.

Notes for provers: boundary points are `(1/2 : ℂ) + t * I` in lemmas but `↑(1/2 : ℝ) + ↑t * I` when `stripVerticalIntegral` unfolds — expect a `push_cast`/`norm_num` step in `integral_stripQuotient_vertical` and `tendsto_stripVerticalIntegral`. Optional: `hT : 0 < T` is unneeded in `strip_rectangle_subset` and `strip_rectangle_identity`; it is needed in `norm_stripQuotient_horizontal_le`.
