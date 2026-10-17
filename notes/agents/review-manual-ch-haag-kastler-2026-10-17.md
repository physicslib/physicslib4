# Review: manual chapter "Haag–Kastler" and docstring pass (2026-10-17)

Read-only review of the uncommitted docstring pass on `Physicslib4/AQFT/HaagKastler/` and the manual
chapter `web/Manual/HaagKastler.lean`. Read: `.claude/CLAUDE.md`, the plan
`plan-verso-reference-manual-2026-10-17.md`, the writer's log `manual-ch-haag-kastler-progress.md`,
the blueprint section `haag-kastler-axioms.tex` (and the 1964 axioms in `sec1/`).
Rebuilt: `cd web && lake build && lake exe generate-manual --output _out/manual` (passes; only
pre-existing module-system and unused-variable warnings).

## What was checked and is correct

- **Only docstrings/comments changed.** All 13 files compared HEAD vs working tree with every `--`
  and `/- -/` comment removed and whitespace normalised: identical code in all 13. No signature,
  field, type, proof or attribute change.
- **Blueprint labels.** All 20 `Blueprint:` labels in the new docstrings exist and their `\lean{}`
  lists the declaration carrying them.
- **Facts checked against code:** product (Λ₁Λ₂, a₁ + Λ₁a₂) (Group instance); topology induced by
  `toProd` g ↦ (Λ, Λ⁻¹, a) and `IsTopologicalGroup`; `IsOrthochronous` is (Λe₀)⁰ > 0; the empty set
  is a basis set (p = q); `LorentzCovariance` quantifies α over all subsets and transports with
  `.mp` (the old docstring said `Eq.mpr`; the new `Eq.mp` is right); vacuum and ground-state
  definitions are existential over any representation, not "the GNS" one (the new docstrings say
  this correctly); `AQFT.IsKMSState` boundary values ω(a α_t b) and ω(α_t b a) as stated;
  `IsPositiveEnergy` uses the unbounded generator (no hidden Restriction); every cited name exists
  (`exists_gns_unitary`, `ObservableCorrespondence.maximal`, `isQuasilocalObservable_iff`,
  `coe_localVonNeumannAlgebra`, `GNS.vonNeumannOfSelfAdjoint`, `action_one/mul`, `actionHom`,
  `QuasilocalLift.unique`, `covEquiv_one/mul/isotony`, `translationFlow`, `commute_ι_of_spacelike`,
  `exists_gns_einstein_causality`, `exists_gns_unitaryRep(_strongContinuous)`).
- **Implementation notes kept:** universe of `carrier` and of `HaagKastlerNet.U`, indexing of ι over
  diamonds, total `LocalNet.algebra`, `Eq.mp` transport, `StarAlgHom` unitality, `Set.centralizer`.
- **Chapter claims checked against the blueprint:** the junk-fibre net with no total ι
  (first design note of thrm:quasilocal-algebra-exists, the M₂(ℂ) example); curved spacetime has no
  quasilocal algebra and need not have a common diamond (curved section design notes);
  colimit norm ‖[a]‖ = ‖a‖ (`colimitNorm_mk`); the ambient-algebra alternative rejected (design note
  at line 362); primitivity abandoned (line 777); "Section 10.6" matches the home page.
- **Links.** All 29 `apiDocs` hrefs point to the file that declares the name, with the right
  anchor; all 5 tutorial anchors exist in `_out/tutorial`; all blueprint anchors exist in
  `blueprint/web/chptr-haag-kastler-axioms-blueprint.html`. The docs site responds (200).

## A. Docstring pass

A1. **should fix**: `LorentzCovariance.lean`, `InhomogeneousLorentzGroup` docstring, "Space and time
reflections are excluded, since they are not symmetries of nature." This overstates the physics (CPT
is a symmetry of every Wightman theory; the axioms do not say P and T fail, only that they are not
assumed). Replace with: "Space and time reflections are not included: a theory need not be invariant
under them (the weak interaction violates parity), and time reversal would act antilinearly."

A2. **should fix**: same docstring has no blueprint line. Add as last line
`Blueprint: def:inhomogeneous-lorentz-group` (the node is in `spacetime.tex`, line ~148).

A3. **should fix**: `QuasilocalKMS.lean`, `flowAut` summary "along a curve t ↦ L_t of Poincaré
maps". "Poincaré map" means something else to physicists (dynamical systems). Write "of Poincaré
transformations".

A4. **should fix**: `IsKMSStateForFlow` uses α_t for the dynamics, while every other docstring uses
α_L for the Axiom 5 maps between local algebras; and β is both the inverse temperature and the
action β_(L_t) in the same paragraph. Proposed: use τ_t for the dynamics, "the correlation function
t ↦ ω(a τ_t(b)) ... whose values on Im z = β are ω(τ_t(b) a). This definition is the general KMS
condition `AQFT.IsKMSState` for the automorphisms τ_t = β_(L_t) of 𝔘 (`flowAut`)." If the blueprint's
α_t is kept, add "(α_t is the dynamics, not the α_L of Axiom 5)".

A5. **nit**: `LocalVonNeumann.lean`: `localOperators` writes π(ι_B(𝔘(B))), and `localVonNeumann` and
`localVonNeumannAlgebra` write π(𝔘(B))''. Add to `localOperators`: "..., written π(𝔘(B)) for short."

A6. **nit**: `Isotony` docstring, "which is what gives the quasilocal algebra (`QuasilocalAlgebra`)
its product". The structure gets nothing from this; the construction does. Write "which is what makes
their directed colimit, and so the quasilocal algebra (`exists_quasilocalAlgebra`), an algebra."

A7. **nit**: `QuasilocalAlgebra.ι` implementation note leaves the contradiction implicit. Proposed:
"... density bounds 𝔘 by the algebras of the diamonds, while a unital *-homomorphism from a large
simple algebra on some other subset into the nonzero algebra 𝔘 would be injective, so 𝔘 would have
to be large too (blueprint: thrm:quasilocal-algebra-exists, first design note)."

A8. **nit**: `QuasilocalAlgebra` implementation note "the construction is carried out in
`QuasilocalColimit.lean`": the assembly is in `QuasilocalExistence.lean`. Write "in
`QuasilocalColimit.lean` and `QuasilocalExistence.lean`".

A9. **nit**: `LorentzCovariance` lost the name `Set.smul_set_mono` (the old text named both
lemmas used in condition 3). Developers grep for it: "(`isAlexandrovBasisSet_smul`,
`Set.smul_set_mono`)".

A10. **nit**: `IsGroundStateForFlow` summary "an invariant state whose generator of the flow is
positive" is awkward. Write "A ground state for a flow t ↦ L_t: a flow-invariant state in which the
flow has a positive generator."

A11. **nit**: `LocalCommutativity` displayed formula is indented two spaces, so it renders as an
ordinary paragraph (Verso and doc-gen4). Acceptable; if a display is wanted, put the equation alone
on its line and move ", for all a₁ ∈ 𝔘(B₁), a₂ ∈ 𝔘(B₂)," into the following sentence.

Format: first lines are one-sentence summaries throughout; "Blueprint: <label>" plain text last;
"Implementation note:" where needed; present tense; no narrated history found.

## B. Manual chapter

B1. **should fix** (lines 151–153): "the Poincaré group has four connected components, and only the
component of the identity ... consists of symmetries of nature." Same overclaim as A1. Replace with:
"As you will recall, the Poincaré group has four connected components. The axioms ask only for the
component of the identity, with det Λ = 1 and Λ preserving the direction of time: a theory need not
be invariant under parity or time reversal (the weak interaction violates parity)."

B2. **should fix** (lines 313–316): the proof sketch of `LocalCommutativity.commute_ι` says it "uses
the injectivity of ι_B". It does not: it uses `(commute_ι_iff_commute_map ...).2`, which needs only
that ι_B is a homomorphism. Injectivity is what the converse (`localCommutativity_iff_exists_commute_ι`)
needs. Replace "and uses the injectivity of ι_B:" with "and applies the homomorphism ι_B to the
commutation in 𝔘(B):", and add to the converse paragraph (line 332) "; this direction uses the
injectivity of ι_B".

B3. **should fix** (lines 453–456): the Schlieder property is stated without its hypothesis that
B₁ and B₂ are completely spacelike (`hs` in the printed statement). Write: "Statistical independence
(the Schlieder property): if B₁ and B₂ are completely spacelike and a vector Ω is cyclic for the local
operators of B₁, then Ω is separating for R(B₂), ...". The blueprint's name is "Statistical
Independence (Schlieder Property)".

B4. **should fix** (coverage): the blueprint section's subsections "Irreducibility and Schur's
Lemma", "Unitary Equivalence and Superselection", "Disjointness and Quasi-Equivalence", "Direct
Sums, Amplification, and Reducibility" and "The Separating Vector of a Faithful State" (blueprint
lines 1067–1763, 2143) are not mentioned. They are almost all `Physicslib4.GNS` declarations, so one
paragraph suffices, e.g. at the end of "Representations and local von Neumann algebras": "The
blueprint section also develops the representation theory used here: irreducibility and Schur's
lemma, unitary and quasi-equivalence, disjointness and direct sums. These hold for any C\*-algebra and
are formalised in `Physicslib4/GNS/`; the GNS chapter describes them. `Purity.lean` specialises
purity and irreducibility to the quasilocal algebra." Everything else of headline importance
(axioms, construction, Axiom 4, Einstein causality, R(B), density, β_L, invariant, vacuum, KMS and
ground states) is covered.

B5. **nit** (lines 70–71 and 483): "no finite set of measurements distinguishes" needs "to any
given accuracy"; as written it reads as exact indistinguishability.

B6. **nit** (lines 484–486): "Mathlib's strong operator topology is the topology of pointwise
convergence, reached through `UniformConvergenceCLM.ofFun`". Write: "The statement expresses the
strong operator topology as the topology of pointwise convergence, that is, uniform convergence on
finite sets, through `UniformConvergenceCLM.ofFun` with the family of finite sets."

B7. **nit** (line 178): "In the 1964 axioms, the quasilocal algebra is given together with the net."
More precisely: "The 1964 Axiom 4 takes the set-theoretic union of the local algebras to be a normed
\*-algebra and completes it, which presupposes that the algebras sit inside one another."

B8. **nit** (lines 187–191): "the properties that characterise a quasilocal algebra" next to "does not
claim that the quasilocal algebra is unique". Both are true, but the reader will ask. Suggest:
"The library does not prove that the quasilocal algebra is unique up to isomorphism (it is: injective
\*-homomorphisms of C\*-algebras are isometric, so the norm on the union of the images is forced)."

B9. **nit** (line 122–123): "every local algebra shares the unit of 𝔘(∅)" is vague. Write: "because
the maps are unital, the local algebras have in effect a common unit, as the 1964 Axiom 2 requires".

B10. **nit** (rendering, infrastructure): in the docstring boxes 55 of the 72 inline Lean spans
render as unresolved "unknown token" (unlinked, unhighlighted), because the docstrings name
declarations relative to the namespace (`QuasilocalAlgebra`, `exists_quasilocalAlgebra`,
`HaagKastlerNet.quasilocal`, ...), which doc-gen4 resolves but Verso's docstring elaboration does
not. Do not qualify the names in the source (that harms the docs and the hover). Check whether
Verso's `{docstring}` can elaborate code spans with the declaration's namespace open; otherwise
accept and record it in `web/README.md`.

Prose style: crisp, present tense, "As you will recall" reminders used for the net, the commutant,
states, the Poincaré group and KMS; the tutorial is linked, not repeated. Maths, docstring boxes,
link text and the 29 API links render correctly (not re-checked for column overflow in a browser;
the writer did this in headless Chrome).

## Writer's doubts

1. **Raw-brace subscripts (i(B₁, B₂), α_(L'L), β_(L_t))**: acceptable, and the best of the
   available options. Docstring boxes are plain Markdown without maths, and doc-gen4 and hovers show
   the same text, so Unicode with parentheses reads well everywhere. Keep one rule: use parentheses
   for every multi-character subscript (ι_(LB), as already done in `action`), and keep the bare
   form only for one-symbol subscripts (ι_B, α_L, ι_B₂).
2. **Blueprint design notes instead of the decision memos**: right. The blueprint is the
   specification (CLAUDE.md) and is published; the memos are internal and change. The
   conventions chapter (9) can collect the decisions later.
3. **GNS-unitary theorems linked, not printed**: right. Their `#check` output is anonymous
   nested existentials, and the prose already states what they give (U(L)π(a)Ω = π(β_L a)Ω,
   U(L)Ω = Ω, a group homomorphism, strong continuity under continuous matrix coefficients,
   irreducibility for pure ω), which matches the code.

## Verdict and top 5

Verdict: **ready after small fixes**. The docstring pass changes no code, keeps the implementation
notes, and corrects one old inaccuracy (`Eq.mpr` → `Eq.mp`). The chapter is accurate in all but three
places, its links all resolve, and it reads well for the intended reader. Counts: A 11 findings (4
should fix, 7 nits); B 10 findings (4 should fix, 6 nits); no errors.

Top 5:
1. B1 + A1: drop "only the identity component consists of symmetries of nature" in the chapter and
   in the `InhomogeneousLorentzGroup` docstring.
2. B2: the `commute_ι` proof sketch credits injectivity, which only the converse uses.
3. B3: the Schlieder property is stated without "completely spacelike".
4. A4: notation clash in `IsKMSStateForFlow` (α_t vs α_L; β for temperature and for the action).
5. B4: add one paragraph pointing to the GNS representation-theory subsections of the blueprint
   section; A2: add `Blueprint: def:inhomogeneous-lorentz-group`.
