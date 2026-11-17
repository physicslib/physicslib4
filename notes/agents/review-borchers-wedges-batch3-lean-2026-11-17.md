# Review: Lean statements for borchers-wedges batch 3 (2026-11-17)

Files reviewed:
- `Physicslib4/Analysis/StripRealBoundary.lean`
- `Physicslib4/AQFT/PositiveEnergyHalfPlane.lean`
- `Physicslib4/AQFT/Borchers.lean`

38 of 47 labels are sorry'd. The other nine use `def:half-sided-translation` and are deferred until
the guard is approved for `Borchers.lean`.

## Verdict

**REVISE.** There was one required fix, now applied: `StripRealBoundary.lean` imported
`Physicslib4.AQFT.KMS`, which made an Analysis file depend on AQFT.
- It now imports `Physicslib4.Analysis.StripPeriodicExtension`.
- It writes the strips literally, through local notations `Σ[β]` and `Σ°[β]` built with
  `Set.ofPred`. These agree definitionally with `kmsStrip`.

## Statements checked faithful

- **The reflection Φ_f** is encoded by an `ite` on Im z < 0.
- **The constancy lemma** has the right hypotheses.
- **Ṽ(w) = ∫ε_w dμ^P:**
  - P is the generator of V, via Stone.
  - The value 0 for Im w < 0 is never relied on.
- **F and F_n** are extended by 0 off the strip. Their boundary values and z♭ are correct.
- **(B2)** is read as V(t)xV(−t), consistent with the blueprint.
- **The reality lemmas** have minimal hypotheses.
- **Cyclicity for both M and M′** is part of `IsCyclicSeparatingVector`.

## Non-blocking points

- **Unneeded hypotheses:** `t ≥ 0` in the reflected-group-unitary lemma and `τ ≥ 0` in the two
  boundary lemmas are not needed. Both follow the blueprint.
- **Binder counts** are large. They shrink once `IsHalfSidedTranslation` replaces hV, hB1 and hB2.
- **Unhygienic notation:** the `z` binder in the `F[…]` and `Fn[…]` notations could capture a
  caller's `z`. Document this.
- **Duplicated notation:** `ε[·]` and `Ṽ[·]` are defined in two files.

## The nine deferred nodes — PASS

`IsHalfSidedTranslation` extends `IsPositiveEnergy V` with two fields:
- `apply_self`, which is (B1);
- `conj_mem`, which is (B2) in the form V(t)xV(−t).

The eight theorems are faithful:
- **Dilation:** Δ^{is}V(t)Δ^{−is} = V(e^{−2πs}t), with U[s] = Δ^{is}.
- **Reflection:** 𝒥[V[t]] = V[−t] is JV(t)J = V(−t).
- **`Fxy[τ]`:** it reproduces F with φ = xΩ and ψ = JyΩ.
- **Hypotheses:** none is over- or under-assumed.
