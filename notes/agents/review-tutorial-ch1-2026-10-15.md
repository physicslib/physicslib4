# Review: tutorial chapter 1, "AQFT in brief" (2026-10-15)

Read-only review of `web/Tutorial/AQFTInBrief.lean` and its rendered HTML.

## 1. Physics and mathematics

Overall: the mathematics is sound. Every exercise solution was checked line by line and is correct
(Weyl relations, diamond nonemptiness, upward directedness, C\*-unit facts, no-signalling,
GNS for $M_2$, $U(L)$ isometric, strip). The GNS sketch, the spectral-permanence argument, the
spectrum-condition paragraph and the "sharpens" list agree with Chapter 10 (`def:local-algebras`,
`def:isotony`, `def:local-commutativity`, `def:lorentz-covariance`, `def:vacuum-state`, the curved
axioms).

### 1a. "All observables of interest": strong density (settled)

**The chapter is correct; Chapter 6 of the blueprint is wrong; Chapter 10 is correct.**

- Chapter (Axiom 4): "its elements are approximated by those of $`\pi(\mathfrak{U})` on any finitely
  many state vectors to any accuracy, so no finite set of measurements distinguishes them." This is
  exactly strong-operator density (von Neumann density theorem for a unital \*-subalgebra).
- Blueprint `sec6/all-observables-of-interest.tex`, lines 32-36: "if one is presented with any $A''$
  in $\pi_\omega(\mathfrak{U})''$ then for any $\varepsilon$ ... there exists a $\pi_\omega(a)$ ...
  such that $\| \pi_\omega(a)\psi - A''\psi \| < \varepsilon$ **for all $\psi$ in
  $\mathcal{H}_\omega$**." With $a$ chosen before $\psi$ and no bound on $\|\psi\|$, this forces
  $\pi_\omega(a) = A''$ (scale $\psi$), i.e. it claims $\pi_\omega(\mathfrak{U}) = \pi_\omega(\mathfrak{U})''$,
  contradicting line 18 of the same section. Even restricted to unit vectors it is norm density,
  which is false in general: $\pi_\omega(\mathfrak{U})$ is a C\*-algebra, hence norm closed, so norm
  density would again give equality. Strong density only gives: for each **finite** set
  $\psi_1,\dots,\psi_n$ and $\varepsilon > 0$ there is $a$ with $\|\pi_\omega(a)\psi_k - A''\psi_k\| < \varepsilon$
  for $k = 1..n$. (This is a separate finding for the user; not edited.)
- Chapter 10 states it correctly: `thrm:quasilocal-strongly-dense` (haag-kastler-axioms.tex l. 708ff)
  and `lmm:strong-neighbourhood-basis` (l. 697ff, "for $s \subseteq H$ finite"); the Lean
  `dense_range_in_bicommutant` uses the strong operator topology. So the Lean is unaffected.
- **Proposed blueprint fix (sec6, lines 32-36):** replace "there exists a $\pi_\omega(a)$ in
  $\pi_\omega(\mathfrak{U})$ such that [eq] for all $\psi$ in $\mathcal{H}_\omega$" by "for any finite
  set of vectors $\psi_1, \dots, \psi_n$ in $\mathcal{H}_\omega$ there exists a $\pi_\omega(a)$ in
  $\pi_\omega(\mathfrak{U})$ such that $\|\pi_\omega(a)\psi_k - A''\psi_k\| < \varepsilon$ for
  $k = 1, \dots, n$"; and in line 38 replace "experimentally one is unable to measure if one is
  working with ..." by "no finite collection of measurements, each of finite precision, can tell
  $\pi_\omega(\mathfrak{U})$ from $\pi_\omega(\mathfrak{U})''$". Severity for the blueprint: error.
- Minor, same file line 14: "$\pi_\omega(\mathfrak{U}) \subseteq \pi_\omega(\mathfrak{U})''$, i.e.
  $\pi_\omega(\mathfrak{U})$ is generically a proper subset" - the inclusion does not imply properness;
  suggest "the inclusion is in general proper". Nit.

### 1b. Schwarzschild example

- Location: §"What this project sharpens", "a diamond near the singularity and a suitable one far
  outside the horizon have none, since it would have to extend beyond the singularity."
- The claim is correct with the right choice of diamonds, and matches the blueprint
  (`sec9/axiom-3-local-commutativity.tex` l. 12-17: $\mathbf{B}_1$ "$\varepsilon$ from the singularity",
  $\mathbf{B}_2$ "$\varepsilon$ from $i^+$"). The obstruction is the top vertex $q$: it must lie in the
  future of $\mathbf{B}_1$, which is a thin sliver just below the singularity, and in the future of
  $\mathbf{B}_2$; a late-time exterior region can only reach the part of the singularity near $i^+$ in
  the Penrose diagram, so the futures are disjoint. (The bottom vertex is no problem: an early exterior
  point lies in the past of both.) What matters is that $\mathbf{B}_2$ is at **late times** (near
  $i^+$), not that it is "far outside the horizon": an exterior diamond at large radius but early
  time can share a future point with $\mathbf{B}_1$ if $\mathbf{B}_1$ is placed suitably.
  Severity: should fix. **Fix:** "In a Schwarzschild black hole, a diamond just below the singularity
  and a diamond outside the horizon at sufficiently late times have none: the top vertex of a common
  diamond would have to lie in the future of both, and inside the hole the future of the first ends on
  the singularity before it meets the future of the second." Also confirm Schwarzschild satisfies the
  standing hypothesis (it does: globally hyperbolic, hence strongly causal), so the example is legitimate.
- The strip exercise is a good, correct toy version of the same phenomenon.

### 1c. Other flagged points

- **φ and φ + :φ³:** (§"Why algebras", "describe the same particles and the same scattering
  amplitudes"). Correct in substance (Borchers classes: relatively local fields with the same
  one-particle content give the same S-matrix, by Haag–Ruelle; Haag LQP §II.5), but two issues: (i) for
  the free field, which is the only $\phi$ mentioned, the S-matrix is trivial, so "same scattering
  amplitudes" is vacuous; (ii) the reason (relative locality) is not stated. Should fix. **Fix:**
  "Even for a scalar field, different fields, such as the free field $\phi$ and $\phi + {:}\phi^3{:}$
  with ${:}\phi^3{:}$ the Wick-ordered cube, commute with each other at spacelike separation; such
  relatively local fields belong to one _Borchers class_, and in an interacting theory any two fields
  of the class that create the same particles give the same scattering matrix." (Do not claim they
  generate the same local algebras; that is not needed and not true in general for arbitrary members
  of a Borchers class.)
- **Diamonds as domains of dependence** (§"Causal diamonds"). Correct: the open diamond is exactly
  $D$ of the open ball of radius $\tfrac12 (q^0 - p^0)$ at the midpoint time in the rest frame of
  $q - p$. No change. Nit: "a ball" -> "the open ball of radius $(q^0 - p^0)/2$ centred at the
  midpoint", so the reader can check it.
- **Haag DOI** 10.1007/978-3-642-61458-3: resolves to *Local Quantum Physics: Fields, Particles,
  Algebras*, Springer, published 1996 (2nd ed.), and is the DOI the blueprint uses (sec3, sec7, sec8,
  sec10). Correct.

### 1d. Further physics/maths findings

- **Notation clash, $\alpha_{\mathbf{1}}$** (§Axiom 5, "with $\alpha_{\mathbf{1}} = \mathrm{id}$").
  $\mathbf{1}$ is the unit of the algebra throughout the chapter; here it is the identity of the
  Poincaré group. Should fix. **Fix:** "$\alpha_{e} = \mathrm{id}$ for the identity $e$ of the group"
  (or $\alpha_{\mathrm{id}}$). (The blueprint also writes $\alpha_{\mathbf{1}}$; the tutorial need not copy it.)
- **Circular step in the C\*-identity remark** (§C\*-algebras, "$\|A^*A\| \le \|A^*\|\,\|A\| =
  \|A\|^2$"). Uses $\|A^*\| = \|A\|$, which is neither recalled nor proved before (the exercise proves
  it for abstract C\*-algebras, using the identity). Nit. **Fix:** "and $\|A^*A\| \le \|A^*\|\,\|A\|
  = \|A\|^2$, since $\|A^*\| = \|A\|$ for bounded operators".
- **Signalling argument** (§Axiom 3, "measuring one does not change the statistics of the other").
  Correct, and the exercise proves it. No change.
- **Spectrum condition** (§The vacuum). Matches `def:vacuum-state` and its remark. But "the
  spectrum condition requires the time translations to form such a group" says the strong continuity
  is part of the condition; in the project it is part of positive energy. Fine as written.
- **"Haag's later account ... omits it"** (primitivity aside) matches sec8 l. 17. "Its physical
  motivation is thin" matches sec8 l. 11-17. OK.
- **"The 1964 isotony axiom allows all local algebras to have a common unit or none"** matches
  `sec4/common-unit.tex` quote. OK. Precision nit: 1964 says the two algebras of each nested pair
  have a common unit or neither has one.
- **Curved covariance group** "the isometries connected to the identity" matches
  `def:isometric-covariance-in-curved-spacetime`. OK.
- **Why chronological cones** (§Causal diamonds, "With $J^\pm$, the region $J^+(p) \cap J^-(p) = \{p\}$
  would be a single point"). True but a weak argument: the diamonds of interest have $p \neq q$, and
  the real defect is that $J^+(p) \cap J^-(q)$ is closed (compact), never open. Should fix. **Fix:**
  "With $J^\pm$, the region $J^+(p) \cap J^-(q)$ is compact, so not open, and for $q = p$ it is the
  single point $\{p\}$; an operator-valued distribution has no value at a point, ..."
- **Generators of the local algebras** (§Why algebras, "bounded functions of the smeared fields
  $\phi(f)$ with $f$ supported in $\mathbf{B}$"). Self-adjointness needs real $f$. Nit. **Fix:** "with
  $f$ real and supported in $\mathbf{B}$".

## 2. Prose and style

Overall: crisp, present tense, pitched correctly for a first-year PhD student. Reminders open the
familiar topics ("As you will recall" for fields and the Poincaré group, "You will be familiar with"
for Minkowski space, "Recall that" for Hilbert spaces and Stone's theorem); new topics (C\*-algebras,
states, diamonds, Alexandrov topology, nets, GNS, superselection) are defined. Notation $(-,+,+,+)$,
$\mathfrak{U}(\mathbf{B})$, $\prec$, $\ll$, $I^\pm$ is consistent throughout. No history narration
about the project.

1. **Undefined: commutant, bicommutant, weak closure** (§Axiom 4, "In a given representation $\pi$
   the weak closure $\pi(\mathfrak{U})''$ is larger than $\pi(\mathfrak{U})$"). The primes are never
   defined, "weak closure" is not explained, and "is larger" should be "is in general larger".
   Should fix. **Fix:** "For a set $S$ of bounded operators, the _commutant_ $S'$ is the set of
   bounded operators that commute with every element of $S$. In a representation $\pi$, the
   bicommutant $\pi(\mathfrak{U})'' = (\pi(\mathfrak{U})')'$ is, by von Neumann's bicommutant theorem,
   the closure of $\pi(\mathfrak{U})$ in the weak operator topology, and it is in general larger than
   $\pi(\mathfrak{U})$. But by the von Neumann density theorem, for every $T \in \pi(\mathfrak{U})''$,
   every finite set of vectors $\psi_1, \dots, \psi_n$ and every $\varepsilon > 0$ there is an
   $a \in \mathfrak{U}$ with $\|\pi(a)\psi_k - T\psi_k\| < \varepsilon$ for all $k$, so no finite set
   of measurements distinguishes them."
2. **Vacuum paragraph flow** (§The vacuum, "...(see the second exercise below). And it has _positive
   energy_. Recall Stone's theorem: ..."). The two defining properties are split by a long aside, and
   "the spectrum condition requires the time translations to form such a group with $H \ge 0$, and
   more generally the same of every one-parameter group of future-directed timelike translations" is
   awkward ("the same of"). Should fix. **Fix:** open with "A _vacuum state_ is a state $\omega$ on
   $\mathfrak{U}$ that is invariant and has positive energy." Then one paragraph on invariance and
   $U(L)$, then: "Recall Stone's theorem: ... For the time translations, $H$ is the Hamiltonian.
   _Positive energy_, or the _spectrum condition_, requires that for every future-directed timelike
   vector $a$ the translations $t \mapsto U(ta)$ form such a group with nonnegative generator;
   equivalently, the joint spectrum of the energy-momentum operators lies in the closed forward light
   cone. This makes the vacuum a state of lowest energy."
3. **Curved-spacetime paragraph is overlong** (§What this project sharpens, "The sharpened axioms carry
   over ... in Lean.", about 200 words, five ideas). Should fix. **Fix:** split into three paragraphs:
   (i) what carries over (Hausdorff Alexandrov topology, local algebras, isotony, isometries);
   (ii) what fails (no common diamond, Schwarzschild, no quasilocal algebra, local commutativity and
   Axiom 4 become local); (iii) the contrast with Brunetti–Fredenhagen–Verch and the forward pointer.
   Also replace "(equivalently, the spacetime is strongly causal, and the Alexandrov and manifold
   topologies agree)" by "(equivalently, the spacetime is strongly causal; the Alexandrov and manifold
   topologies then agree)", which says which is the equivalence and which the consequence.
4. **"intertwines" undefined** (§Superselection sectors, "no nonzero operator intertwines them").
   Nit. **Fix:** "no nonzero bounded operator $T$ satisfies $T\pi_1(a) = \pi_2(a)T$ for all $a$".
5. **"directed colimit" for physicists** (§Axiom 4, "The result is the _directed colimit_ (or
   inductive limit)"). Nit. **Fix:** lead with the more familiar term: "the _inductive limit_ (in
   category-theory language, the directed colimit)".
6. **Repeated phrasing.** "whichever region it is regarded as belonging to" (§Axiom 2) repeats "which
   region we regard it as belonging to" (§C\*-algebras). Nit. **Fix:** in §Axiom 2 shorten to "and by
   spectral permanence an observable has the same spectrum in every algebra it is embedded in." The
   Cambridge sentence that follows can stay, but it adds little; consider cutting it.
7. **Axiom 5 title.** The subsection is "Lorentz covariance" but the group is the Poincaré group. Nit.
   **Fix:** add after the first sentence of the subsection: "(Haag and Kastler call it the
   inhomogeneous Lorentz group, hence the name of the axiom.)" or retitle "Axiom 5: Lorentz (Poincaré)
   covariance".
8. **Source wrapping.** Lines 199, 257, 284-285, 298, 400, 458 and 546 of `AQFTInBrief.lean` exceed
   the 100-column wrap used elsewhere. Nit (no effect on HTML). **Fix:** re-wrap.

## 3. Structure

- **Chapter goal: met.** The reader learns what a net is (§1, §Axiom 1), each axiom with what it rules
  out (§4), what states and GNS are for (§5: expectation values, recovering Hilbert space, vacuum,
  sectors), and what the project sharpens (§6, a clear seven-point list).
- **Balance:** §1 ~630, §2 ~830, §3 ~570, §4 ~1,200, §5 ~930, §6 ~510, §7 ~100 words. §4 and §5 are
  the heaviest, as they should be. No change.
- **Exercises (8, one or two per section):** all useful and correct. The Weyl-relation, signalling,
  $M_2$-GNS and strip exercises are especially good. One placement issue (nit): the signalling
  exercise belongs to Axiom 3 but sits after the primitivity aside and uses states before §5 defines
  them. **Fix:** acceptable as is ("see the exercise below" and "defined in the next section" are
  present); optionally move it to the end of §5 with a back-reference from Axiom 3.
- **"In the library" names:** all 14 project names exist in `blueprint/lean_decls`
  (`HaagKastlerNet`, `MinkowskiSpacetime`, `Spacetime.alexandrovTopology`,
  `Spacetime.chronologicalDiamond`, `LocalNet`, `Isotony`, `LocalCommutativity`, `QuasilocalAlgebra`,
  `LorentzCovariance`, `GNS.State`, `GNS.gns_construction`, `HaagKastlerNet.IsVacuumState`,
  `HaagKastlerCurved.HaagKastlerNet`, `ObservableCorrespondence`), and Mathlib's `CStarAlgebra` exists
  (unital, complex) and is what `LocalNet` uses. No change.
- **Further reading:** Haag (DOI correct), Haag–Kastler 1964 (DOI 10.1063/1.1704187, JMP 5(7)
  848-861, correct), BFV 2003 (DOI 10.1007/s00220-003-0815-7, CMP 237, 31-68, correct), Grossi
  arXiv:2410.16599 (title and author confirmed on arXiv; the blueprint's GNS details cite it), and the
  blueprint (URL returns 200).

## 4. Rendering

Rebuilt with `lake build && lake exe generate-tutorial --output _out/tutorial` (exit 0; only
unused-variable linter warnings).

- **Maths:** 399 math elements (387 inline, 12 display). KaTeX renders client-side
  (`-verso-data/katex/math.js`, `throwOnError: false`), so `katex-error` cannot appear in the static
  HTML; instead every element was rendered offline with the bundled `katex.js` in strict mode with
  `throwOnError: true`: **0 errors**. No raw `$`, backticks, `\command`s, `:::` or `{cite` left in the
  visible text.
- **Figures:** both appear as inline SVG (`cones`, `diamond`) with titles and descriptions; the cones
  labels sit in the right regions; dashes come from `.st-cone` (`stroke-dasharray`).
- **Solutions:** 8 `<details>` blocks with `<summary>Solution`, one per exercise.
- **Links:** all external links present (DOIs, arXiv, blueprint, GitHub, docs); internal section
  anchors resolve via `<base href="./../">`.
- **Citations:** `citet` renders "Haag and Kastler (1964)" and "Brunetti, Fredenhagen, and Verch
  (2003)" with margin notes; `citehere` renders full references. Nit: the arXiv entry renders as
  "Rafael Grossi, 2024." while articles render "Rudolf Haag and Daniel Kastler (1964)."; this is the
  Verso genre's `ArXiv` formatter, not the chapter. No change unless the theme is customised.

## Verdict and top 5 fixes

**Verdict: ready for the user's read after fixes.** No errors in the chapter itself; the mathematics,
exercise solutions, library names and rendering are all sound. Counts (chapter): 0 errors, 7 should
fix, 11 nits. Separate blueprint finding: 1 error (sec6 strong density), 1 nit.

Top 5 fixes:

1. §Axiom 4: define commutant/bicommutant and weak closure, say "in general larger", and state the
   finite-vector density precisely (fix 2.1).
2. §What this project sharpens: Schwarzschild example: "at sufficiently late times" in place of "far
   outside the horizon", with the one-clause reason (fix 1b); split the curved-spacetime paragraph into
   three (fix 2.3).
3. §The vacuum: state both properties up front and rewrite the spectrum-condition sentence (fix 2.2).
4. §Why algebras: φ and φ + :φ³: as relatively local fields of one Borchers class giving the same
   S-matrix, not a vacuous free-field claim (fix 1c).
5. §Axiom 5: $\alpha_{\mathbf{1}}$ -> $\alpha_e$ (clash with the unit $\mathbf{1}$); and §Causal
   diamonds: the "why chronological" argument via compactness of $J^+(p) \cap J^-(q)$ (fixes 1d).

Separately for the user: fix the blueprint's `sec6/all-observables-of-interest.tex` lines 32-38
(uniform "for all $\psi$" -> finitely many vectors), see 1a.
