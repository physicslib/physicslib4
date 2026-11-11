# Proposal: a Tomita–Takesaki section (§10.10)

Status: proposal. Decisions recorded 2026-11-08: D1 Option K, D3 the project's commutant
convention, D5 Bratteli–Robinson §2.5.2, D6 new section 10.10 — all approved. D4 decided 2026-11-10 (L2.2 replaced; see below). D2 open.
Stage-2 trial done (2026-11-08): von Neumann's theorem (T†T self-adjoint, positive, dense
domain for closed densely defined T) is FEASIBLE: proved in a spike, about 125 lines, no sorry, via
the existing criterion `adjoint_eq_of_range_eq_top`; verified code in `tomita-stage2-trial.md`.
This part of stage 2 is about 3–4 nodes and 150–180 lines, much less than the scout's estimate.
Trial 2 done (2026-11-08): the functional-calculus composition law f(A)g(A) ⊆ (fg)(A), with
Dom(f(A)g(A)) = Dom g(A) ∩ Dom (fg)(A) and μ_{g(A)x} = |g|² μ_x, is FEASIBLE (proved in a spike, about
200 lines, no sorry). Dom |T| = Dom T with ‖|T|x‖ = ‖Tx‖ is FEASIBLE WITH GAPS: the core fact for √D is
proved; about 150–200 more lines and 5 nodes remain. One gap, spectral support of a positive operator,
is already proved (`Physicslib4.AQFT.spectralMeasure_Iio_zero_eq_zero`), so the remainder is smaller.
Scout: `scout-tomita-antilinear-polar-2026-11-08.md` (representation of antilinear operators,
polar decomposition, available Mathlib and project API).

## Goal

For a von Neumann algebra M on a complex Hilbert space H with a cyclic and separating vector Ω:

1. **Tomita's theorem, first half:** the modular flow preserves M, Δ^{it} M Δ^{−it} = M for all real
   t. This follows J. Sorce, "A short proof of Tomita's theorem", arXiv:2309.16762, published in
   J. Funct. Anal. (2024). Use the published version: the author strengthened one proposition
   (Prop. 3.12) for it.
2. **Tomita's theorem, second half:** J M J = M′. Sorce does not prove this. Source: Bratteli–Robinson
   vol. 1, §2.5.2 (decision D5).
3. **Application (optional, later):** combined with the Reeh–Schlieder corollaries, every local von
   Neumann algebra R(B) of a weakly additive net in a vacuum representation has a modular flow and a
   modular conjugation.

The section is pure operator algebra in its core (stages 1–5), like §10.2–10.4. Only stage 6 uses
the net.

## The paper's structure

- **§2, cited and not proved:**
  - L2.2: the domain of S is the set of vectors TΩ with T closed, affiliated with M, and Ω in
    Dom T ∩ Dom T*;
  - L2.4: strip analyticity of z ↦ P^{−z} x P^{z};
  - L2.6 (Takesaki's lemma): for z in the resolvent set and a′ ∈ M′ there is a unique a ∈ M with
    aΩ = (z − Δ)^{−1} a′Ω, and ‖a‖ ≤ ‖a′‖ / √(2(|z| − Re z));
  - L2.8: the holomorphic functional calculus as a contour integral.
- **§3, proved:**
  - P3.1–P3.2: sigmoid cut-offs of Δ written as contour integrals of the resolvent;
  - Thm 3.3 (hardest): bounded a_{λ,n} ∈ M with a_{λ,n}Ω = Δ^n Θ(λ − Δ) a′Ω and
    ‖a_{λ,n}‖ ≤ α e^{βn};
  - Defs 3.5–3.6: tidy operators;
  - L3.8, P3.9: Δ^n a Δ^{−n} is bounded for tidy a;
  - P3.10: the tidy vectors form a core for every Δ^x;
  - Thm 3.11: F(z) = [Δ^{−z} a Δ^{z}, b′] vanishes, by Phragmén–Lindelöf and Carlson;
  - P3.12: the commutant of the tidy operators is M′;
  - Cor 3.13: all of M is preserved.

## Representation of antilinear operators (from the scout)

The Tomita operator S₀(aΩ) = a\*Ω is antilinear. Mathlib's `LinearPMap` is semilinear in general,
but its closure and adjoint exist only for linear partial maps.

**Recommended, Option K:** fix an antiunitary involution C on H, built classically from a Hilbert
basis (`exists_hilbertBasis`; no separability needed). Then work with the ℂ-linear partial map
S′ = C ∘ S₀ in `H →ₗ.[ℂ] H`.
- **Why it works:** (S′)† S′ = S\* S = Δ, so Δ lands directly in the project's unbounded spectral
  theory (`spectralMeasure`, `functionalCalculus`, `IsSelfAdjoint`, `IsPositive`). The modular
  conjugation is then J = C ∘ V, with V the unitary from the linear polar decomposition of S′.
- **Independence of C:** state the main results for J and Δ characterised intrinsically: Δ = S\*S on
  the closure, and J by S = J Δ^{1/2}. Prove that they do not depend on the choice of C, so C stays
  an implementation device.
- **Cost:** building C and its API is about 150 lines. C is a new `def`, which needs your guard
  approval.

**Alternatives considered:**
- **Option R:** view H as a real Hilbert space via `InnerProductSpace.rclikeToReal` (an `abbrev`,
  enabled with `letI`). The real adjoint of an antilinear S equals its antilinear adjoint (checked in
  the scout memo). But S\*S would have to be bridged back to `H →ₗ.[ℂ] H`.
- **Option C:** a conjugate Hilbert space. Mathlib has none, so it needs a new type and instances.
- **Option P:** work only with graphs as real subspaces of H × H. Most general, most work.

## Stages

Each stage is one or more writer–reviewer–formalize–prove cycles, logged to disk, as for
Reeh–Schlieder.

1. **Antilinear tools and the Tomita operator** (about 25–35 nodes):
   - the antiunitary involution C;
   - S₀′ = C ∘ S₀ on MΩ, and F₀′ on M′Ω;
   - dense domains (cyclicity) and the adjoint relation ⟨S₀x, y⟩ = conj⟨x, F₀y⟩ (separating);
   - closability, so S = closure;
   - injectivity and dense range.
2. **von Neumann's theorem and the polar decomposition of S** (about 30–45 nodes), the main
   infrastructure risk:
   - T†T is self-adjoint for closed, densely defined T. Ingredients exist in
     `Spectral/Unbounded/Basic.lean`, such as the orthogonal graph decomposition;
   - the square root Δ^{1/2} through `functionalCalculus`, with
     ‖Δ^{1/2}x‖ = ‖Sx‖ and Dom Δ^{1/2} = Dom S;
   - V unitary, J = C ∘ V antiunitary, J² = 1, JΔJ = Δ^{−1}, and independence from C.
   - Needs from the functional calculus:
     - the composition law f(A) g(A) ⊆ (fg)(A);
     - a core API;
     - spectral support of positive operators. That is proved:
       `Physicslib4.AQFT.spectralMeasure_Iio_zero_eq_zero` in
       `Physicslib4/AQFT/PositiveEnergyHolomorphic.lean`.
3. **The cited lemmas of §2** (about 25–40 nodes):
   - L2.2: the domain of S through closed operators affiliated with M. Possibly avoidable; check
     whether §3 needs it in full or only one direction;
   - Takesaki's lemma L2.6: resolvent and quadratic-form estimates, plus a commutant Radon–Nikodym
     step. Related library results are in `GNS/RadonNikodym.lean`;
   - L2.4 and L2.8, possibly replaced by scalar spectral-measure integrals rather than
     operator-valued contour integrals.
4. **Complex analysis** (about 10–20 nodes):
   - Carlson's theorem, which is absent from Mathlib: a function of exponential type less than π on
     the right half-plane that vanishes at the non-negative integers is zero;
   - Phragmén–Lindelöf: Mathlib's `PhragmenLindelof` file (vertical-strip and sector forms).
5. **Sorce §3** (about 30–50 nodes). Thm 3.3 and Thm 3.11 are each split into several nodes. Result:
   Δ^{it} M Δ^{−it} = M.
6. **J M J = M′** (about 20–40 nodes, following Bratteli–Robinson §2.5.2; see D5), and optionally the application to local von
   Neumann algebras via Reeh–Schlieder (about 5–10 nodes).

**Total:** roughly 145–240 nodes, against 41 for Reeh–Schlieder. Stages 1–2 are the gate: if
von Neumann's theorem and the functional-calculus composition law go through, the rest is
substantial but routine.

## Decisions needed

- **D1. Representation.** Option K (recommended), R, C or P.
- **D2a (decided 2026-11-09). Antiunitaries** are Mathlib's conjugate-linear isometric equivalences
  `H ≃ₗᵢ⋆[ℂ] H` (`LinearIsometryEquiv (starRingEnd ℂ)`), with `H →ₗᵢ⋆[ℂ] H` only where bijectivity
  is not yet known; J² = 1 is stated pointwise (∀ x, J (J x) = x). No new Lean definition is needed
  for "antiunitary". Two facts Mathlib lacks become the first lemmas: ⟨Cx, Cy⟩ = conj⟨x, y⟩, and a
  conjugate-linear norm-preserving bijection is antiunitary.
- **D2b (decided 2026-11-09). T\*T gets a Lean definition** (the product of a partial map with its
  adjoint, domain {x ∈ Dom T | Tx ∈ Dom T†}), not a graph hypothesis. Needs guard approval for the
  file that holds it when stage 2 is formalized.
- **D2. Other new definitions** (guard approval needed): C; the Tomita operator S₀ and its closure S; Δ;
  J; the tidy operators; probably a predicate "cyclic and separating" or a reuse of
  `IsCyclicVector` and `IsSeparating`. All in new files under `Physicslib4/Operators/Modular/` (or
  similar), approved file by file as for `Additivity.lean`.
- **D3. Setting.** Mathlib's `VonNeumannAlgebra` structure, or a set of operators equal to its
  bicommutant using the project's `Set.centralizer` convention (as `localVonNeumann` does).
  Recommended: the project convention, for consistency with the local von Neumann algebras.
- **D4 (decided 2026-11-10). Scope of stage 3: L2.2 is not formalized.** Close reading of
  arXiv:2309.16762v3 (the published version, with Prop. 3.12): L2.2 is used once, in the proof of
  Thm 3.3, and only to produce an operator a_{λ,n} with a_{λ,n}Ω = ψ that commutes with A′ on A′Ω.
  The proof then only ever evaluates a_{λ,n} on A′Ω, as b′ ↦ b′ψ, and shows that this map is bounded.
  So L2.2 is replaced by an elementary **commutant extension lemma**: if ψ ∈ H and
  ‖b′ψ‖ ≤ c‖b′Ω‖ for all b′ ∈ A′, then there is a unique a ∈ A with aΩ = ψ, and ‖a‖ ≤ c.
  Proof: b′Ω ↦ b′ψ is well defined because Ω is separating for A′. It is bounded, so it extends
  from the dense A′Ω to all of H. The extension commutes with A′, so it lies in A″ = A.
  No affiliated unbounded operators and no description of Dom S are needed. Takesaki's lemma
  (L2.6) ends with the same step. The other cited lemmas:
  - **L2.6 (Takesaki's lemma)** is formalized in full, for every z ∉ [0, ∞), since Thm 3.3
    evaluates it on a contour around the positive real axis.
  - **L2.8** (operator-valued contour integrals) is used once, in Prop. 3.1, for the bounded
    cut-offs Δ_(m). It is replaced by a scalar route: spectral-measure integrals, Fubini, and a
    scalar Cauchy formula.
  - **L2.4** (strip analyticity) is used once, in Thm 3.11, and is formalized in the form that
    proof needs.

  Stage 3 is drafted in two batches: 3a, the commutant extension lemma and Takesaki's lemma;
  then 3b, L2.4 and the scalar replacement for L2.8.
- **D5. Source for J M J = M′: Bratteli–Robinson, *Operator Algebras and Quantum Statistical
  Mechanics 1*, §2.5.2 (around Theorem 2.5.14; check the exact numbering in the edition used).**
  Chosen because Sorce describes his proof as similar to theirs for bounded Δ, so their notation and
  route are closest to his.

  The four-step argument, given Sorce's Δ^{it} M Δ^{−it} = M:
  1. **Symmetry.** Ω is cyclic and separating for M′, which has the same J and the modular operator
     Δ^{−1}. So Sorce's theorem also gives Δ^{it} M′ Δ^{−it} = M′.
  2. **Smooth elements.** Write σ_t(a) = Δ^{it} a Δ^{−it}. For a ∈ M, the Gaussian averages
     ∫ e^{−γt²} σ_t(a) dt lie in M, extend analytically in t to all of ℂ, and converge strongly to
     a as γ → ∞.
  3. **The key identity.** For such an analytic a, Δ^{1/2} a Δ^{−1/2} extends to the bounded
     σ_{−i/2}(a) ∈ M. With S = J Δ^{1/2} and S(xΩ) = x\*Ω, this shows J a J commutes with M, so
     J a J ∈ M′.
  4. **Closing up.** By density, J M J ⊆ M′. The same argument for M′ gives J M′ J ⊆ M, so
     J M J = M′ because J² = 1.

  Formalization needs, beyond stages 1–5:
  - strongly convergent operator-valued Gaussian integrals;
  - the analytic extension σ_{−i/2}, reusing the strip and holomorphy tools from Reeh–Schlieder
    (`PositiveEnergyHolomorphic.lean`, `EdgeVanishing.lean`) and from Sorce;
  - the commutation and density steps.

  This fits the stage 6 estimate of 20–40 nodes.

  Alternatives, not chosen:
  - Takesaki, *Theory of Operator Algebras II*, Ch. VI §1, via the Tomita algebra;
  - Kadison–Ringrose, vol. II, §9.2;
  - Rieffel–van Daele, *Pacific J. Math.* 69 (1977), a complete alternative route through real
    subspaces rather than a complement to Sorce.

  Before drafting stage 6: confirm the exact statements in Bratteli–Robinson, and check whether
  Sorce's published version cites a source for this half.
- **D6. Placement.** A new section 10.10, `sections/sec10/tomita-takesaki.tex`, after Reeh–Schlieder;
  nothing is renumbered.

## Risks

- **von Neumann's theorem and the composition law:** about 600 lines of new spectral theory (scout
  estimate).
- **Cores and domains:** P3.10 and the domain arguments around Δ^z are delicate.
- **Choice of C:** results about J and Δ must not depend on it, which needs a uniqueness argument
  for the polar decomposition.
- **Carlson's theorem:** a self-contained but non-trivial complex-analysis proof.
- **The paper's citations:** Sorce relies on cited lemmas (§2) whose standard proofs may be longer
  than the paper itself.
- **Budget:** at the Reeh–Schlieder pace, this is several weeks of sessions. Stages should end in
  commits, and progress logs must be kept per stage.

## Suggested first step

Stage 1 plus a spike on stage 2: draft the blueprint nodes for C, the Tomita operator and
closability, and in parallel scout whether von Neumann's theorem is provable from the project's
existing graph decomposition in a few nodes. If the spike fails, revisit D1 (Option R) before
committing to the full section.
