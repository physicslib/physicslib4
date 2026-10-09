# Changelog

All notable changes to this project — the Lean formalization, the blueprint and the project web
page — are recorded in this file. The documentation itself describes the project as it is; this
file is where its history lives.

## Unreleased

The first release, 1.0, is in preparation.

## Pre-1.0 development notes

The project started in June 2026. The notes below summarise the changes made before the first
release that a reader of earlier drafts of the blueprint or of the web page may want to know
about. Blueprint labels (e.g. `def:local-commutativity`) and Lean names identify the current
declarations.

### The Haag–Kastler axioms (Minkowski and curved spacetime)

- **Axiom 2 (Isotony) supplies its embeddings as data.** Isotony was at first stated with strict
  inclusion ⊂ and only asserted the existence of embeddings; the embeddings used downstream were
  witnesses chosen existentially inside Axiom 3, with no composition law. Axiom 2 now fixes a
  family of unital \*-monomorphisms `i_{B₁B₂}` for `B₁ ⊆ B₂`, with identity and composition laws,
  in both the Minkowski and the curved setting (`def:isotony`, `def:isotony-in-curved-spacetime`).
- **Axiom 3 (Local Commutativity) consumes the Axiom 2 family.** It previously introduced its own
  isotony family and injectivity. In curved spacetime this removed the coherence hypotheses that
  three-fold inclusion results (von Neumann isotony, the von Neumann net, net equivalence) used to
  carry; `commIsotony` is now the Axiom 2 family, so `commIsotony_comp` holds for every net.
- **Minkowski Axiom 3 is stated in a common containing diamond.** It was previously stated as
  commutation of the images `ι_B` in some quasilocal algebra. It now requires completely spacelike
  local algebras to commute in every local algebra `𝔘(B)` containing both, exactly as the curved
  axiom does; the former statement is the equivalent `lmm:local-commutativity-iff-quasilocal`
  (`localCommutativity_iff_exists_commute_ι`). Chapter 5's discussion of where commutation takes
  place was revised accordingly.
- **Axiom 4 was split.** It previously carried `QuasilocalCompleteness`, a mathematical existence
  claim (`Nonempty (QuasilocalAlgebra U i)`), which `HaagKastlerNet` bundled as a field. The
  existence claim became the theorem `thrm:quasilocal-algebra-exists` (`exists_quasilocalAlgebra`),
  proved from the net alone; Axiom 4 is now the bridge principle `ObservableCorrespondence`, and the
  net carries no quasilocal-completeness field.
- **Axiom 5 (Lorentz covariance) and curved isometric covariance** restate their coherence
  condition for the Axiom 2 family. The abstract curved `LorentzianSpacetime` interface gained the
  field `isBasisSet_smul`, so basis-set preservation is no longer a hypothesis of the curved
  geometric-covariance results.
- **Positive energy uses an unbounded generator.** `IsPositiveEnergy` was first stated with a
  bounded positive generator, `V(t) = exp(itP)`, and carried a `**Restriction:**` note waiting on
  Stone's theorem. With Stone's theorem formalized it is stated through the infinitesimal
  generator, which must be a positive (unbounded) operator; the bounded case is the lemma
  `isPositiveEnergy_exp`. The project records no remaining restrictions.
- The blueprint label `thrm:vacuum-no-stone` was renamed `thrm:vacuum-invariance-consequences`.
- General covariance (`def:general-covariance-in-curved-spacetime`) was added as a property of the
  assignment of nets to spacetimes, not as a sixth axiom.

### The quasilocal algebra

- **Construction route.** The quasilocal algebra is constructed from the net as the directed colimit
  of the local algebras followed by completion. The alternative of realising it as a closed
  \*-subalgebra of an ambient C\*-algebra (`StarSubalgebra.cstarAlgebra`) was considered and
  rejected, because it assumes the ambient algebra. The dense-extension results
  (`dense_adjoin_iUnion_range_ι`, `exists_starAlgHom_extend_of_dense`) remained valid as consumers.
- **`QuasilocalAlgebra` is parametrised by the Axiom 2 isotony datum.** It formerly carried its own
  `inclusion` family, duplicating Axiom 2's; `trivialQuasilocalAlgebra` was re-indexed accordingly.
- **Universe fixes.** The existence theorem was at one point not provable as stated, because the
  embeddings `ι` were indexed over all subsets (now Alexandrov-basis sets only) and the carrier was
  pinned to `Type 0` (now `Type u`, the net's universe; a free `Type*` did not elaborate). A third
  universe pin was removed by making `HaagKastlerNet` universe-polymorphic.
- **Supporting results promoted.** The facts behind the quasilocal-algebra definition (directedness
  of the diamonds, the colimit as a normed \*-algebra, its completion as a C\*-algebra) were promoted
  from the informal discussion of Chapter 6 to blueprint declarations, and
  `lmm:quasilocal-colimit-union-of-insertions` was split out of the existence proof.
- **Retractions.** The quasilocal-completion node once also claimed uniqueness of the complete
  C\*-norm, citing `StarAlgEquiv.norm_map`, which does not support it; the clause was dropped. An
  earlier draft claimed that any two C\*-norms on a \*-algebra coincide, which is false (ℂ[F₂]
  carries distinct full and reduced norms). The `StarModule ℂ` field was missing from an earlier
  statement of `lmm:completion-of-cstar-normed-star-algebra`.

### Operator theory

- **Stone's theorem** (§10.4, `thrm:hall-10.15`, Lean `Physicslib4.Spectral.Stone.stone`) was added,
  together with the §10.3 nodes it uses: a self-adjoint operator has no proper symmetric extension
  (`lmm:self-adjoint-maximally-symmetric`), the spectral measure of a self-adjoint operator
  (`def:spectral-measure`), its functional calculus (`def:hall-10.5`) and its agreement with the
  bounded calculus (`lmm:functional-calculus-bounded`). The chapter-10 sections after §10.3 were
  renumbered by one.
- Positivity of unbounded operators (`def:positive-unbounded-operator`) was added for the
  positive-energy condition.
- **The von Neumann density theorem** (`thrm:quasilocal-strongly-dense`) was proved locally, with
  the supporting results of §10.6.2 (reducing subspaces, finite amplification, the strong
  neighbourhood basis), following Murphy, Lemma 4.1.4.
- `def:identity-and-indicator` was split into `def:identity-operator` and
  `def:indicator-function`; the old label is kept as a compound reference. Hall's Theorem A.52 was
  promoted to the citable `thrm:hall-a.52`.
- The strip-Liouville principle in `KMS.lean` was first an explicit hypothesis; it is proved for
  `β > 0` (`stripLiouville_of_pos`), which makes KMS invariance unconditional.

### Spacetime geometry

- **The Levi-Civita connection and geodesics** (§10.5): a pseudo-Riemannian layer was added
  (`def:pseudo-riemannian-metric`, existence and uniqueness of the Levi-Civita connection), and
  geodesics are defined through it, chart-free and affinely parametrised. Spacetimes were required to
  be modelled without boundary.
- **Smoothness fields in bundle-section form.** The metric smoothness field of `Spacetime` and the
  smoothness field of `TimeOrientation` were moved from a chart-local `ContDiffWithinAt` form to
  Mathlib's bundle-section (`ContMDiff` section) idiom. The blueprint label
  `lmm:pullback-metric-smooth-in-charts` keeps its earlier name because other nodes cite it.
- The Mathlib route to smoothness of `x ↦ dψ_x` for pullback metrics was settled via
  `ContMDiffAt.mfderiv_const` and `clm_precomp`/`clm_comp`; an earlier note wrongly claimed that
  `ContMDiff.clm_comp` was Mathlib's only precomposition lemma.
- The `mfderiv`/`symm` round-trip cancellation was split out as `lmm:mfderiv-symm-cancel-left` and
  `-right`, and `lmm:cross-metric-isometry-symm` was added to make the reverse inclusions of the
  chronological-future/past image lemmas explicit.
- Endpoints of curves were defined for arbitrary paths, `PathEquiv` was relaxed, and smoothness of
  the inverse musical isomorphism (`lmm:musical-inverse-smooth`), the last unformalised node of
  Chapter 10, was proved.

### Toolchain

- The project moved from Lean/Mathlib `v4.31.0-rc1` to `v4.34.1`. Documentation remarks about what
  Mathlib does or does not provide were written against the earlier version and have been restated
  for the current one.

### Documentation and web page

- The landing page was split into a guide, an axioms page and one page per Chapter 10 section,
  with collapsible item lists; MathJax moved from the retired `cdn.mathjax.org` to jsDelivr.
- Item links on the section pages use absolute URLs, so they resolve on the deployed site.
- Long Lean names in the blueprint PDF wrap instead of overflowing the margin.
