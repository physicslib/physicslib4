# Proposals: `unusedArguments` in `Physicslib4/Spectral/BorelClasses.lean`

Author: lean-simplifier agent, for kdavis@alum.mit.edu.
Scope note: `BorelClasses.lean` is outside this task's edit allowlist
(`Physicslib4/Spectral/Unbounded/{Basic,Spectrum}.lean` only), so nothing in this
file was changed. These are proposals only.

## 1. `L0` (line ~279) — unused `[MeasurableSpace X]`

```
def L0 (X : Type*) [TopologicalSpace X] [MeasurableSpace X] : Set (Set X) :=
  {E | ∃ (f : ℕ → C(X, ℝ)) (C : ℝ), (∀ n x, ‖f n x‖ ≤ C) ∧
    ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (E.indicator (1 : X → ℝ) x))}
```

The body only mentions `C(X, ℝ)` (needs `TopologicalSpace X`) and pointwise
convergence of real-valued functions; no `MeasurableSpace X` structure is used to
build the set. The instance is carried purely because later lemmas
(`measurableSet_of_mem_L0`, `isSetAlgebra_L0`, ...) state facts about `MeasurableSet`
for the *same* `X`, and putting `[MeasurableSpace X]` on `L0` lets those statements
read `L0 X` without re-deriving the instance — but Lean's elaborator does not need
that: instance arguments are synthesized automatically, so every call site `L0 X`
already resolves the ambient `[MeasurableSpace X]` from its own `variable` block
whether or not `L0`'s signature demands it.

**Assessment.** Dropping `[MeasurableSpace X]` from `L0`'s signature:
- does not change the set `L0 X` computes for a fixed `TopologicalSpace X` (the
  instance plays no role in the body), so it is a genuine simplification, not a
  generalization or restriction;
- does not break any call site's *syntax*: `L0 X` is written without the instance
  argument everywhere it is used (`empty_mem_L0`, `compl_mem_L0`, `union_mem_L0`,
  `measurableSet_of_mem_L0`, `isClosed_mem_L0`, `isSetAlgebra_L0`, and the
  `MeasurableSpace.generateFrom (L0 X)` uses near the end of the file), because those
  sites already have their own `[MeasurableSpace X]` in scope via `variable`;
- is orthogonal to the docstring's point about *not* re-asserting `MeasurableSet E`
  in the predicate (that is about a conjunct inside the set-builder, not about the
  type-class argument on `L0` itself), so the docstring would not need to change in
  substance.

**Recommendation.** Safe to drop `[MeasurableSpace X]` from `L0`'s signature (leave
`[TopologicalSpace X]`). This is a `def` signature change to a committed
declaration — a design decision reserved for the user per `.claude/CLAUDE.md`
("Definitions are design decisions... Agents may propose changes to them but not
make them") and blocked outright for edits to existing declarations by
`.claude/lean-policy.json`'s guard (a def-signature diff is flagged as "changes the
definition of the existing def `L0`"). No downstream statement changes are needed
if applied, since every `L0 X` occurrence already infers the instance from context.

## 2. `isSetAlgebra_L0` (line ~485) — unused `[CompactSpace X]` and `[BorelSpace X]`

```
theorem isSetAlgebra_L0 : IsSetAlgebra (L0 X) ∧ ∀ U : Set X, IsOpen U → U ∈ L0 X :=
  ⟨⟨empty_mem_L0, fun {_} h => compl_mem_L0 h, fun {_ _} h h' => union_mem_L0 h h'⟩,
    fun _U hU => by
      simpa using compl_mem_L0 (isClosed_mem_L0 hU.isClosed_compl)⟩
```

This sits in `section Compact` (`variable {X : Type*} [MetricSpace X] [CompactSpace X]
[MeasurableSpace X] [BorelSpace X]`), but its proof only calls `empty_mem_L0`,
`compl_mem_L0`, `union_mem_L0` (all proved in `section Topological`, needing only
`[TopologicalSpace X] [MeasurableSpace X]`) and `isClosed_mem_L0` (proved in this
same `section Compact`, but with a *local* `omit [CompactSpace X] [BorelSpace X] in`
already in front of it at line 415, because its own proof only needs
`[MetricSpace X]`). So `isSetAlgebra_L0` genuinely does not need `CompactSpace` or
`BorelSpace`; only `MetricSpace` (for `isClosed_mem_L0`) survives.

The theorem's docstring ("`𝓛₀` is an algebra of sets and contains every open subset
of `X`. This blueprint node is exactly the conjunction of `empty_mem_L0`,
`compl_mem_L0`, `union_mem_L0` and `isClosed_mem_L0`...") does not itself reason
about `BorelSpace X`; it just names the four lemmas being conjoined. So there is no
docstring text that would need to change.

**Assessment.** Mechanically this is exactly the same shape as the existing
`omit [CompactSpace X] [BorelSpace X] in` already sitting above `isClosed_mem_L0`
two lemmas earlier in the same file — i.e. it is the file's own established house
style, not a new pattern. Adding it here would be `omit`-only and would not touch
the docstring or proof body.

**Recommendation.** Add `omit [CompactSpace X] [BorelSpace X] in` immediately above
`theorem isSetAlgebra_L0`, matching the precedent at `isClosed_mem_L0`. This file is
outside this task's write allowlist, so it is left as a proposal; note also that
(per this session's separate finding in `Unbounded/Basic.lean` and
`Unbounded/Spectrum.lean`) the project's write guard treats inserting an
`omit ... in` line before a *committed* theorem as "changes the statement of the
existing theorem" and blocks it textually, even though it changes nothing
semantically. Whoever applies this should expect the guard to block a
`lean-simplifier`/`lean-prover` agent from making the edit directly; a human commit,
or a policy adjustment acknowledging `omit ... in` insertions as non-substantive,
would be needed first.
