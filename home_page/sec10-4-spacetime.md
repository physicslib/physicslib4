---
title: "§10.4 Spacetime and causal structure (pp. 233–270)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · **§10.4 Spacetime** · [§10.5 Minkowski](sec10-5-haag-kastler.html) · [§10.6 Curved](sec10-6-curved.html) · [§10.7 Covariance](sec10-7-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.5 Minkowski](sec10-5-haag-kastler.html) →

# §10.4 Spacetime and causal structure (pp. 233–270)

137 items (Definitions 283–419), building the entire causal and topological apparatus the axioms are indexed on. The trips underlying the chronological and causal relations $$\ll$$ and $$\prec$$ are genuine geodesics of the Levi-Civita connection of the metric, which the section constructs for an arbitrary pseudo-Riemannian metric on top of Mathlib's covariant derivatives (Mathlib itself has only a Riemannian Levi-Civita connection and no geodesics). It proceeds in nine layers.

- *Spacetime, tangent-vector causality, and curves (pp. 233–238, items 283–306).* Gives precise definitions of spacetime (Definition 283) and standard Minkowski spacetime (Definition 284); classifies tangent vectors as timelike, spacelike, or null (Definition 285) and proves the trichotomy (Lemma 286), the reverse Cauchy–Schwarz and reverse triangle inequalities for timelike vectors (Lemmas 287–288), and the cone geometry—orientation of pointing vectors, the sign lemma, definiteness of the spacelike complement of a timelike vector, and convexity of the cones (Lemmas 291–294)—alongside time orientations (Definition 289) and future- and past-pointing vectors (Definition 290). Then paths, curves, and oriented curves are defined as equivalence classes of paths up to reparametrisation (Definitions 295–300), with causal type and future/past orientation each shown well-defined on the quotient (Theorems 299 and 301) and a forgetful projection from oriented to unoriented curves (Theorem 302). Endpoints (Definition 303), shown to be well defined on curves and smooth curves (Lemma 304), come with two point-set lemmas—an extremal parameter lies in the frontier, and two endpoints force a compact parameter interval (Lemmas 305–306).
- *The Levi-Civita connection and geodesics (pp. 238–242, items 307–322).* A new layer. Pseudo-Riemannian metrics (Definition 307) are smooth, symmetric, non-degenerate families of bilinear forms, with no signature condition, so everything here applies to every spacetime. Covariant derivatives are Mathlib's `IsCovariantDerivativeOn`; metric compatibility and the Levi-Civita condition (compatible and torsion-free) are defined on top of them (Definitions 308–309). The musical isomorphism $$v \mapsto g_x(v, \cdot)$$ is a linear isomorphism at each point (Lemma 310); the smoothness of its inverse (Lemma 311) is stated and proved in the blueprint but is the one node of the layer not yet formalised, and nothing depends on it. The Koszul formula (Lemma 312), the tensoriality of the Koszul expression (Lemma 313), and the verification that the Koszul connection is a covariant derivative (Lemma 314) that is Levi-Civita (Lemma 315) give existence and uniqueness of the Levi-Civita connection (Theorem 316). Five lemmas about smooth paths—a function vanishing along a path has zero derivative along it, the covariant derivative along a curve is local, local vector fields globalise, a smooth path has a local left inverse, and its velocity extends to a smooth vector field (Lemmas 317–321)—make the geodesic condition chart-free, well defined and non-vacuous. A geodesic (Definition 322) is then an affinely parametrised smooth path $$\mu$$ with $$(\nabla_X X)(\mu(s)) = 0$$ at every interior parameter, for every smooth vector field $$X$$ extending the velocity near $$s$$.
- *Trips, futures and pasts (pp. 242–244, items 323–331).* Trips and causal trips (Definitions 323–324) are finite chains of future-oriented timelike (respectively causal) geodesic segments, geodesic in the sense of Definition 322, with matching past and future endpoints. Chronological and causal precedence are transitive (Theorem 325); the causality condition (Definition 326) makes them a strict partial order (Theorem 327); and chronological and causal futures and pasts (Definitions 328–329) come with their basic inclusion and monotonicity properties (Lemmas 330–331).
- *§10.4.1 Causal diamonds (p. 244, items 332–346).* Introduces the causal diamond $$J^+(p) \cap J^-(q)$$ and the chronological (Alexandrov) diamond $$I^+(p) \cap I^-(q)$$ (Definition 332), with the structural properties of the causal diamond—monotonicity under endpoint spread, causal convexity, and that nonemptiness forces $$p \prec q$$ (Lemma 333)—and the containment of chronological diamonds in causal ones, together with the identification of the Alexandrov basis as exactly the chronological diamonds (Theorem 334). It then develops spacelike separation of points and of regions (Definitions 335–336, Lemmas 337–338), the spacelike complement $$\mathbf{B}^\perp$$ (Definition 339) and its order structure—antitone, extensive on the double complement, with the triple complement collapsing, making complementation the Galois connection attached to the spacelike-separation relation (Lemma 340). The double complement is packaged as the causal closure operator (Definition 341, Lemma 342), whose fixed points are the causally complete regions (Definition 343). These form a complete lattice—meets are intersections, joins are causal closures of unions—on which the causal complement is an order-reversing involution (Theorem 344); the set-level De Morgan laws (Lemma 345) then lift to full binary and infinitary De Morgan laws on the lattice (Theorem 346). The blueprint is careful to record what does *not* hold: the full orthocomplement law $$\mathbf{B} \wedge \mathbf{B}^\perp = \bot$$ fails at this generality, because the trip-based causal relation is irreflexive and so a point is spacelike-separated from itself.
- *§10.4.2 Causal convexity (p. 248, items 347–349).* Defines a causally convex region as one containing every point causally between two of its own points (Definition 347), shows causal diamonds are causally convex (Lemma 348), and shows every spacelike complement—hence every causally complete region—is causally convex (Theorem 349).
- *§10.4.3 Causal convexity: closure structure, and the Alexandrov basis theorems (p. 249, items 350–373).* The causally convex regions are shown to form a closure system (Lemma 350), giving the causal-convex hull (Definition 351) as a genuine closure operator whose closed sets are exactly the causally convex regions (Lemmas 352, Theorem 353). The subsection then turns to the Alexandrov topology (Definition 354): every diamond is open (Lemma 355); chronological futures and pasts are open under an explicit "no endpoints" hypothesis (Lemma 356) and unconditionally on standard Minkowski spacetime, where the coordinate-cone description discharges the hypothesis (Lemma 357). On standard Minkowski spacetime the componentwise directional derivative is a Levi-Civita connection (Lemma 358), hence the Levi-Civita connection is flat (Lemma 359) and affinely parametrised straight lines are geodesics (Lemma 360), so trips there are the familiar straight-line segments. Minkowski spacetime and Lorentzian spacetime are then defined (Definitions 361–362, the latter as a spacetime whose Alexandrov topology is Hausdorff), with a bundled form of spacelike separation and basis openness (Lemma 363). A point lying in no diamond is pathological: its only Alexandrov neighbourhood is the whole space (Lemma 364), and the Hausdorff assumption rules this out, forcing the diamonds to cover the space (Lemma 365). Given downward-directedness the diamonds form a genuine topological basis (Theorem 366); past and future interpolation on standard Minkowski (Lemmas 367–368) supply downward-directedness there (Lemma 369), and common chronological predecessors and successors supply upward-directedness (Lemmas 370–372), so on standard Minkowski the diamonds are an unconditional basis (Theorem 373). Upward-directedness is what the quasilocal colimit of §10.5.1 later consumes.
- *§10.4.4 Dilations are causal automorphisms but not isometries (p. 255, items 374–376).* The dilations $$x \mapsto \lambda x$$ preserve the Minkowski cones (Lemma 374) and are therefore causal automorphisms (Theorem 375), yet scale the metric by $$\lambda^2$$ and so are not isometries for $$\lambda \neq 1$$ (Theorem 376). This is the counterexample that forces the general-covariance morphism of §10.7 to be specified geometrically rather than causally.
- *§10.4.5 Isometries and basis-set preservation (p. 256, items 377–387).* Single-metric transport: isometries preserve the causal classification of tangent vectors (Lemma 377), paths have unique differentials and well-defined pushforwards (Lemmas 378–379), and isometries respect the Levi-Civita structure: pullbacks of vector fields and of the metric pairing, their derivatives and Lie brackets transform naturally (Lemmas 380–382), so an isometry preserves the Levi-Civita connection (Lemma 383) and maps geodesics to geodesics and back (Lemma 384). Future-orientation-preserving isometries preserve chronology (Lemma 385) and map Alexandrov-basis diamonds to diamonds (Lemma 386), which is exactly the well-definedness condition for the Axiom 5 action (Lemma 387).
- *§10.4.6 Pullback metrics and cross-metric isometries (p. 258, items 388–419).* The single-metric lemmas above compare a spacetime with itself; general covariance instead compares two different metrics on one carrier, so the transport statements are redone cross-metric. This subsection defines the pullback $$\psi^* g$$ of a spacetime metric as a bundled family of continuous bilinear forms (Definition 388) and verifies every obligation in turn: the differential of a diffeomorphism is a linear equivalence (Lemma 389), with the two round-trip cancellation identities that Mathlib does not supply for a global `Diffeomorph` proved by hand (Lemmas 390–392); the pullback metric is symmetric, non-degenerate, Lorentzian, and a smooth section of the bilinear-form bundle (Lemmas 393–396), so the pullback of a spacetime is a spacetime (Theorem 397). Two-sided preservation of future orientation is then defined (Definition 398) and the pullback time orientation is shown to be bundle-smooth, nowhere vanishing, and everywhere timelike (Lemmas 399–402), with transport of future-pointing timelike and null vectors (Lemmas 403–404) giving two-sided orientation preservation (Lemma 405). Cross-metric isometries are defined (Definition 406) and shown closed under inverses (Lemma 407), to preserve causal classification (Lemma 408), to push paths forward preserving the timelike/causal conditions and endpoints (Lemmas 409–412), and to transport chronological precedence and the chronological future and past (Lemmas 413–415), hence to preserve Alexandrov-basis sets (Lemma 416). A general topological lemma—a bijection matching generating families is a homeomorphism (Lemma 417)—then identifies the pullback Alexandrov topology (Lemma 418) and yields that the pullback of a Lorentzian spacetime is again a Lorentzian spacetime (Theorem 419). Without Theorem 419 the phrase "the net over $$\psi^*(M,g)$$" in §10.7 would have no referent.

**Where the Lean lives:** `Physicslib4/Geometry/PseudoRiemannian/` (`Basic`, `LeviCivita`, `Flat`), `Physicslib4/Spacetime/` (`Causality`, `Curves`, `AlongPath`, `CausalComplement`, `CausalStructure`, `Minkowski`, `MinkowskiDirected`, `LorentzianSpacetime`, `IsometryCausality`, …)

## Items

Each blueprint subsection below is collapsed; click a heading to see its items. Every entry links to its node in the web blueprint and names the principal Lean declaration.

<details markdown="1">
<summary>§10.4 opening run — spacetime, tangent-vector causality, curves, the Levi-Civita connection and geodesics, trips, futures and pasts (p. 233) — 49 items</summary>

- [**Definition 283**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacetime) — Spacetime · `Physicslib4.Spacetime`
- [**Definition 284**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:standard-minkowski-spacetime) — Standard Minkowski Spacetime · `Physicslib4.StandardMinkowskiSpacetime`
- [**Definition 285**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:timelike-spacelike-null-vectors) — Timelike, Spacelike, or Null Vectors · `Physicslib4.Spacetime.IsTimelike` (+2 more)
- [**Lemma 286**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-classification) — Causal Classification · `Physicslib4.Spacetime.isTimelike_or_isNull_or_isSpacelike` (+5 more)
- [**Lemma 287**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:reverse-cauchy-schwarz) — Reverse Cauchy–Schwarz for Timelike Vectors · `Physicslib4.reverse_cauchy_schwarz_of_lorentzianAt` (+1 more)
- [**Lemma 288**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:timelike-cone-convexity) — Timelike Cone Convexity and Reverse Triangle Inequality · `Physicslib4.add_isTimelike_of_lorentzianAt` (+3 more)
- [**Definition 289**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:time-orientable) — Time Orientation · `Physicslib4.Spacetime.TimeOrientation` (+1 more)
- [**Definition 290**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-and-past-pointing-vectors) — Future and Past Pointing Vectors · `Physicslib4.Spacetime.IsFuturePointing` (+1 more)
- [**Lemma 291**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pointing-orientation) — Orientation of Pointing Vectors · `Physicslib4.Spacetime.isTimelike_or_isNull_of_isFuturePointing` (+2 more)
- [**Lemma 292**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cone-sign-lemma) — Sign Lemma for the Future Cone · `Physicslib4.nonneg_of_orthogonal_timelike` (+4 more)
- [**Lemma 293**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-definite) — Definiteness of the Spacelike Complement · `Physicslib4.eq_zero_of_forall_bilin_eq_zero` (+2 more)
- [**Lemma 294**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:future-cone-convexity) — Convexity of the Future Cone · `Physicslib4.Spacetime.isFuturePointing_add` (+10 more)
- [**Definition 295**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:paths) — Paths · `Physicslib4.Spacetime.Path` (+1 more)
- [**Definition 296**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:curves) — Curves · `Physicslib4.Spacetime.Curve` (+1 more)
- [**Definition 297**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:timelike-and-causal-smooth-curves) — Timelike and Causal Smooth Curves · `Physicslib4.Spacetime.IsTimelikeSmoothCurve` (+1 more)
- [**Definition 298**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-and-past-oriented-smooth-curves) — Future and Past Oriented Smooth Curves · `Physicslib4.Spacetime.IsFutureOrientedSmoothCurve` (+1 more)
- [**Theorem 299**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:smooth-curve-causal-well-defined) — Reparametrisation-Invariance of the Causal Type · `Physicslib4.Spacetime.isTimelikeSmoothCurve_ofPath_iff` (+1 more)
- [**Definition 300**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:oriented-smooth-curve) — Oriented Smooth Curve · `Physicslib4.Spacetime.OrientedSmoothCurve`
- [**Theorem 301**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:oriented-curve-well-defined) — Reparametrisation-Invariance of Orientation · `Physicslib4.Spacetime.isFutureOrientedCurve_ofPath_iff` (+1 more)
- [**Theorem 302**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:oriented-curve-projection) — The Forgetful Projection of Oriented Curves · `Physicslib4.Spacetime.OrientedSmoothCurve.toSmoothCurve` (+1 more)
- [**Definition 303**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:endpoints) — Endpoints · `Physicslib4.Spacetime.IsEndpoint` (+2 more)
- [**Lemma 304**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:curve-endpoint-well-defined) — Endpoints of curves are well defined · `Physicslib4.Spacetime.IsCurveEndpoint` (+5 more)
- [**Lemma 305**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:extremal-parameter-mem-frontier) — An extremal parameter lies in the frontier · `Physicslib4.Spacetime.mem_frontier_of_isMin` (+3 more)
- [**Lemma 306**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:endpoint-parameter-space-eq-Icc) — Two endpoints force a compact parameter interval · `Physicslib4.Spacetime.parameterSpace_eq_Icc_of_endpoints`
- [**Definition 307**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pseudo-riemannian-metric) — Pseudo-Riemannian Metric · `Physicslib4.Geometry.PseudoRiemannianMetric` (+1 more)
- [**Definition 308**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:metric-compatible-connection) — Covariant Derivative; Metric Compatibility · `Physicslib4.Geometry.CovariantDerivative.IsMetricCompatibleWith`
- [**Definition 309**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:levi-civita-connection) — Levi-Civita Connection · `Physicslib4.Geometry.CovariantDerivative.IsLeviCivitaFor`
- [**Lemma 310**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:musical-isomorphism) — Musical Isomorphism · `Physicslib4.Geometry.PseudoRiemannianMetric.bijective_val`
- [**Lemma 311**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:musical-inverse-smooth) — Smoothness of the Inverse Musical Isomorphism *(not yet formalised: no Lean declaration — see [Formalisation status](./#formalisation-status))*
- [**Lemma 312**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:koszul-formula) — Koszul Formula · `Physicslib4.Geometry.CovariantDerivative.IsLeviCivitaFor.koszul`
- [**Lemma 313**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:koszul-expression-tensorial) — Tensoriality of the Koszul Expression · `Physicslib4.Geometry.PseudoRiemannianMetric.tensorialAt_koszulAux₁` (+2 more)
- [**Lemma 314**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:koszul-connection-is-covariant-derivative) — The Koszul Connection is a Covariant Derivative · `Physicslib4.Geometry.PseudoRiemannianMetric.isCovariantDerivativeOn_leviCivitaAux`
- [**Lemma 315**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:koszul-connection-is-levi-civita) — The Koszul Connection is Levi-Civita · `Physicslib4.Geometry.PseudoRiemannianMetric.isMetricCompatibleWith_koszulConnection` (+1 more)
- [**Theorem 316**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:levi-civita-exists-unique) — Existence and Uniqueness of the Levi-Civita Connection · `Physicslib4.Geometry.PseudoRiemannianMetric.exists_isLeviCivitaFor` (+3 more)
- [**Lemma 317**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:derivative-vanishes-along-path) — A Function Vanishing Along a Path has Zero Derivative Along It · `Physicslib4.Spacetime.SmoothPath.mfderiv_apply_tangent_eq_zero`
- [**Lemma 318**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:covariant-derivative-along-curve-local) — Covariant Derivative Along a Curve is Local · `Physicslib4.Spacetime.SmoothPath.covDeriv_eq_of_eventuallyEq`
- [**Lemma 319**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:local-vector-field-globalises) — Local Vector Fields Globalise · `Physicslib4.Spacetime.exists_contMDiff_vectorField_eventuallyEq`
- [**Lemma 320**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:path-local-left-inverse) — Local Left Inverse of a Smooth Path · `Physicslib4.Spacetime.SmoothPath.exists_localLeftInverse`
- [**Lemma 321**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:velocity-extends) — The Velocity of a Smooth Path Extends to a Vector Field · `Physicslib4.Spacetime.SmoothPath.exists_vectorField_eq_tangent`
- [**Definition 322**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:geodesic) — Geodesic · `Physicslib4.Spacetime.IsGeodesic`
- [**Definition 323**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:trip) — Trip · `Physicslib4.Spacetime.IsTripSegment` (+2 more)
- [**Definition 324**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-trip) — Causal Trip · `Physicslib4.Spacetime.IsCausalTripSegment` (+2 more)
- [**Theorem 325**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:precedence-transitive) — Transitivity of chronological and causal precedence · `Physicslib4.Spacetime.chronologicallyPrecedes_trans` (+1 more)
- [**Definition 326**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:no-closed-causal-curve) — No Closed Causal Curve (Causality Condition) · `Physicslib4.Spacetime.NoClosedCausalCurve`
- [**Theorem 327**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-order-refinements) — Irreflexivity and Antisymmetry under Causality · `Physicslib4.Spacetime.chronologicallyPrecedes_irrefl` (+2 more)
- [**Definition 328**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:chronological-future-and-chronological-past) — Chronological Future and Chronological Past · `Physicslib4.Spacetime.chronologicalFuture` (+3 more)
- [**Definition 329**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-future-and-causal-past) — Causal Future and Causal Past · `Physicslib4.Spacetime.causalFuture` (+3 more)
- [**Lemma 330**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:chronological-implies-causal) — Chronological Precedence Implies Causal Precedence · `Physicslib4.Spacetime.isCausal_of_isTimelike` (+3 more)
- [**Lemma 331**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:future-past-monotone) — Monotonicity of Futures and Pasts · `Physicslib4.Spacetime.chronologicalFutureSet_mono` (+3 more)

</details>

<details markdown="1">
<summary>§10.4.1 Causal diamonds, spacelike complement, and causal closure (p. 244) — 15 items</summary>

- [**Definition 332**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-diamond) — Causal and chronological diamonds · `Physicslib4.Spacetime.causalDiamond` (+3 more)
- [**Lemma 333**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-diamond-structure) — Structural properties of the causal diamond · `Physicslib4.Spacetime.causalDiamond_subset_of` (+2 more)
- [**Theorem 334**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-diamond-vs-chronological) — Chronological diamonds inside causal diamonds · `Physicslib4.Spacetime.chronologicalDiamond_subset_causalDiamond` (+1 more)
- [**Definition 335**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-related) — Spacelike Related · `Physicslib4.Spacetime.IsSpacelikeRelated`
- [**Definition 336**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completely-spacelike) — Completely Spacelike · `Physicslib4.Spacetime.IsCompletelySpacelike`
- [**Lemma 337**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completely-spacelike-symm) — Symmetry of Spacelike Separation · `Physicslib4.Spacetime.isSpacelikeRelated_comm` (+1 more)
- [**Lemma 338**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completely-spacelike-structural) — Structural Properties of Complete Spacelike Separation · `Physicslib4.Spacetime.isCompletelySpacelike_mono` (+9 more)
- [**Definition 339**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-complement) — Spacelike Complement of a Region · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement`
- [**Lemma 340**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-order) — Order Structure of the Spacelike Complement · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement_antitone` (+3 more)
- [**Definition 341**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-closure) — Causal closure operator · `Physicslib4.Spacetime.LorentzianSpacetime.causalClosure`
- [**Lemma 342**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-closure-is-closure-operator) — The Causal Closure is a Closure Operator · `Physicslib4.Spacetime.LorentzianSpacetime.causalClosure` (+1 more)
- [**Definition 343**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-complete-region) — Causally complete region · `Physicslib4.Spacetime.LorentzianSpacetime.IsCausallyComplete`
- [**Theorem 344**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-lattice) — Lattice of causally complete regions · `Physicslib4.Spacetime.LorentzianSpacetime.CausallyCompleteRegion` (+8 more)
- [**Lemma 345**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-de-morgan) — De Morgan Laws for the Spacelike Complement · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement_union` (+1 more)
- [**Theorem 346**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-complement-de-morgan) — De Morgan Laws for the Causal Complement · `Physicslib4.Spacetime.LorentzianSpacetime.causalComplement_antitone` (+6 more)

</details>

<details markdown="1">
<summary>§10.4.2 Causal convexity (p. 248) — 3 items</summary>

- [**Definition 347**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-convex-region) — Causally convex region · `Physicslib4.Spacetime.IsCausallyConvex`
- [**Lemma 348**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-diamond-causally-convex) — Causal diamonds are causally convex · `Physicslib4.Spacetime.causalDiamond_isCausallyConvex`
- [**Theorem 349**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-convex) — Causally complete regions are causally convex · `Physicslib4.Spacetime.spacelikeComplement_isCausallyConvex` (+2 more)

</details>

<details markdown="1">
<summary>§10.4.3 Causal convexity: closure structure, and the Alexandrov basis theorems (p. 249) — 24 items</summary>

- [**Lemma 350**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causally-convex-closure-ops) — Causally convex regions form a closure system · `Physicslib4.Spacetime.isCausallyConvex_univ` (+4 more)
- [**Definition 351**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-convex-hull) — Causal-convex hull · `Physicslib4.Spacetime.causalConvexHull`
- [**Lemma 352**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-convex-hull-extensive) — The Causal-Convex Hull is Extensive and Causally Convex · `Physicslib4.Spacetime.subset_causalConvexHull` (+1 more)
- [**Theorem 353**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-convex-hull-closure) — The causal-convex hull is a closure operator · `Physicslib4.Spacetime.causalConvexHull_minimal` (+3 more)
- [**Definition 354**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:alexandrov-topology) — Alexandrov Topology · `Physicslib4.Spacetime.alexandrovTopology`
- [**Lemma 355**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-basis-open) — Basis Sets Are Alexandrov-Open · `Physicslib4.Spacetime.isOpen_alexandrov_of_mem_basis`
- [**Lemma 356**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:chronological-future-past-open) — Openness of Chronological Futures and Pasts · `Physicslib4.Spacetime.isOpen_chronologicalFuture_inter_chronologicalPast` (+2 more)
- [**Lemma 357**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-chronological-open) — Unconditional Openness of Chronological Futures and Pasts on Standard Minkowski · `Physicslib4.exists_chronologicalFuture_standardMinkowski` (+5 more)
- [**Lemma 358**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-directional-derivative-levi-civita) — The Directional Derivative is Levi-Civita on Standard Minkowski · `Physicslib4.Geometry.PseudoRiemannianMetric.isLeviCivitaFor_flatConnection` (+2 more)
- [**Lemma 359**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-levi-civita-flat) — The Minkowski Levi-Civita Connection is Flat · `Physicslib4.standardMinkowski_leviCivita_apply` (+1 more)
- [**Lemma 360**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-lines-are-geodesics) — Straight Lines are Geodesics in Standard Minkowski · `Physicslib4.standardMinkowskiLineSegmentPath_isGeodesic` (+1 more)
- [**Definition 361**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:minkowski-spacetime) — Minkowski Spacetime · `Physicslib4.MinkowskiSpacetime`
- [**Definition 362**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentzian-spacetime) — Lorentzian Spacetime · `Physicslib4.Spacetime.LorentzianSpacetime`
- [**Lemma 363**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lorentzian-causal-lifts) — Bundled Spacelike Separation and Basis Openness · `Physicslib4.Spacetime.LorentzianSpacetime.isCompletelySpacelike_comm` (+1 more)
- [**Lemma 364**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-nbhd-univ-of-no-diamond) — No-Diamond Points Have Only the Whole Space as Neighbourhood · `Physicslib4.Spacetime.alexandrov_nbhd_univ_of_no_diamond`
- [**Lemma 365**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-covering-hausdorff) — Covering from the Hausdorff Assumption · `Physicslib4.Spacetime.LorentzianSpacetime.sUnion_alexandrovBasis_eq_univ`
- [**Theorem 366**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:alexandrov-topological-basis) — The Alexandrov Diamonds Form a Topological Basis · `Physicslib4.Spacetime.LorentzianSpacetime.isTopologicalBasis_alexandrovBasis`
- [**Lemma 367**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-past-between) — Past Interpolation on Standard Minkowski · `Physicslib4.Spacetime.exists_past_between_standardMinkowski`
- [**Lemma 368**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-future-between) — Future Interpolation on Standard Minkowski · `Physicslib4.Spacetime.exists_future_between_standardMinkowski`
- [**Lemma 369**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-downward-directed) — Standard Minkowski Diamonds Are Downward-Directed · `Physicslib4.Spacetime.alexandrovBasis_exists_subset_inter_standardMinkowski`
- [**Lemma 370**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-exists-common-past) — Common Chronological Predecessor on Standard Minkowski · `Physicslib4.Spacetime.exists_common_past`
- [**Lemma 371**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-exists-common-future) — Common Chronological Successor on Standard Minkowski · `Physicslib4.Spacetime.exists_common_future`
- [**Lemma 372**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-upward-directed) — Standard Minkowski Diamonds Are Upward-Directed · `Physicslib4.Spacetime.alexandrovBasis_directed`
- [**Theorem 373**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-alexandrov-basis) — The Alexandrov Diamonds are a Basis on Standard Minkowski · `Physicslib4.Spacetime.isTopologicalBasis_alexandrovBasis_standardMinkowski`

</details>

<details markdown="1">
<summary>§10.4.4 Dilations are causal automorphisms but not isometries (p. 255) — 3 items</summary>

- [**Lemma 374**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-dilation-cone) — Dilations Preserve the Minkowski Cones · `Physicslib4.minkowskiForwardCone_smul` (+1 more)
- [**Theorem 375**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-dilation-causal-automorphism) — Dilations are Causal Automorphisms · `Physicslib4.alexandrovBasis_image_smul`
- [**Theorem 376**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-dilation-not-isometry) — Dilations are Not Isometries · `Physicslib4.minkowskiForm_smul` (+1 more)

</details>

<details markdown="1">
<summary>§10.4.5 Isometries and basis-set preservation (p. 256) — 11 items</summary>

- [**Lemma 377**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-classification) — Isometries Preserve the Causal Classification · `Physicslib4.Spacetime.Isometry.preserves_self` (+3 more)
- [**Lemma 378**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:path-parameter-unique-diff) — Unique Differentials Along a Path · `Physicslib4.Spacetime.Path.uniqueDiffOn_parameterSpace`
- [**Lemma 379**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pushforward-path) — Pushforward of a Path Under an Isometry · `Physicslib4.Spacetime.Isometry.pushforwardPath` (+5 more)
- [**Lemma 380**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-pullback-metric) — Pullback of Vector Fields and the Metric Under an Isometry · `Physicslib4.Spacetime.Isometry.val_mpullback` (+3 more)
- [**Lemma 381**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-pullback-metric-derivative) — Derivatives of Metric Pairings of Pulled-Back Fields · `Physicslib4.Spacetime.Isometry.mfderiv_val_mpullback` (+1 more)
- [**Lemma 382**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-pullback-lie-bracket) — Metric Pairings with Lie Brackets of Pulled-Back Fields · `Physicslib4.Spacetime.Isometry.val_mlieBracket_mpullback` (+1 more)
- [**Lemma 383**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-levi-civita) — Isometries Preserve the Levi-Civita Connection · `Physicslib4.Spacetime.Isometry.mfderiv_leviCivita_mpullback` (+1 more)
- [**Lemma 384**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-geodesics) — Isometries Preserve Geodesics · `Physicslib4.Spacetime.Isometry.pushforwardPath_isGeodesic` (+2 more)
- [**Lemma 385**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-chronology) — Isometries Preserve Chronology · `Physicslib4.Spacetime.Isometry.PreservesFutureOrientation` (+8 more)
- [**Lemma 386**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-basis-sets) — Isometries Preserve Basis Sets · `Physicslib4.Spacetime.Isometry.futureOrientationPreserving` (+8 more)
- [**Lemma 387**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:axiom5-basis-preservation) — Axiom 5 Basis-Set Preservation · `Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent_isBasisSet_smul`

</details>

<details markdown="1">
<summary>§10.4.6 Pullback metrics and cross-metric isometries (p. 258) — 32 items</summary>

- [**Definition 388**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pullback-metric) — Pullback of a Spacetime Metric · `Physicslib4.Spacetime.bilinearPrecomp` (+3 more)
- [**Lemma 389**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-diffeo-linear-equiv) — The Differential of a Diffeomorphism is a Linear Equivalence · `Physicslib4.Spacetime.Diffeo` (+4 more)
- [**Lemma 390**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-symm-cancel-left) — Round-Trip Cancellation: $$d\psi$$ After $$d(\psi^{-1})$$ · `Physicslib4.Spacetime.mfderiv_symm_cancel_left`
- [**Lemma 391**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-symm-cancel-right) — Round-Trip Cancellation: $$d(\psi^{-1})$$ After $$d\psi$$ · `Physicslib4.Spacetime.mfderiv_symm_cancel_right`
- [**Lemma 392**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-inverse-eq-symm) — The Formal Inverse of $$d\psi_x$$ is the Inverse Equivalence · `Physicslib4.Spacetime.inverse_mfderiv_eq_symm` (+2 more)
- [**Lemma 393**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-symm) — The Pullback Metric is Symmetric · `Physicslib4.Spacetime.pullbackVal_symm`
- [**Lemma 394**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-nondegenerate) — The Pullback Metric is Non-Degenerate · `Physicslib4.Spacetime.pullbackVal_nondegenerate`
- [**Lemma 395**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-lorentzian) — The Pullback Metric is Lorentzian · `Physicslib4.Spacetime.pullbackVal_lorentzian`
- [**Lemma 396**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-smooth-in-charts) — The Pullback Metric is a Smooth Section of the Bilinear-Form Bundle · `Physicslib4.Spacetime.pullbackVal_contMDiff`
- [**Theorem 397**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pullback-is-spacetime) — The Pullback of a Spacetime is a Spacetime · `Physicslib4.Spacetime.pullback` (+4 more)
- [**Definition 398**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:preserves-future-orientation) — Two-Sided Preservation of Future Orientation · `Physicslib4.Spacetime.PreservesFutureOrientation` (+1 more)
- [**Lemma 399**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mpullback-vectorField-contMDiff-of-diffeo) — The Pullback of a Bundle-Smooth Vector Field Along a Diffeomorphism is Bundle-Smooth · `Physicslib4.Spacetime.contMDiff_mpullback_vectorField`
- [**Lemma 400**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation-ne-zero) — The Pullback Time Orientation is Nowhere Vanishing · `Physicslib4.Spacetime.mpullback_field_ne_zero`
- [**Lemma 401**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation-timelike) — The Pullback Time Orientation is Everywhere Timelike · `Physicslib4.Spacetime.pullbackVal_mpullback_field_self` (+1 more)
- [**Lemma 402**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation) — Pullback of a Time Orientation · `Physicslib4.Spacetime.pullbackTimeOrientation` (+1 more)
- [**Lemma 403**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-future-pointing-timelike) — Transport of Future-Pointing Timelike Vectors · `Physicslib4.Spacetime.pullbackVal_mpullback_field_apply` (+1 more)
- [**Lemma 404**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-future-pointing-null) — Transport of Future-Pointing Null Vectors · `Physicslib4.Spacetime.isFuturePointing_pullback_iff_of_isNull`
- [**Lemma 405**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-preserves-future-orientation) — The Pullback Preserves the Future Orientation Two-Sidedly · `Physicslib4.Spacetime.pullback_preservesFutureOrientationTwoSided`
- [**Definition 406**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:cross-metric-isometry) — Isometry Between Two Metrics on One Manifold · `Physicslib4.Spacetime.CrossIsometry` (+4 more)
- [**Lemma 407**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-symm) — The Inverse of a Cross-Metric Isometry is a Cross-Metric Isometry · `Physicslib4.Spacetime.CrossIsometry.symm_preserves` (+1 more)
- [**Lemma 408**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-classification) — Cross-Metric Isometries Preserve the Causal Classification · `Physicslib4.Spacetime.CrossIsometry.preserves_self` (+3 more)
- [**Lemma 409**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-tangent) — The Tangent Chain Rule Along a Path · `Physicslib4.Spacetime.mfderivWithin_comp_diffeo` (+1 more)
- [**Lemma 410**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path) — Pushforward of a Path Under a Cross-Metric Isometry · `Physicslib4.Spacetime.pushforwardPath` (+2 more)
- [**Lemma 411**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-causal) — The Pushforward Preserves the Timelike and Causal Conditions · `Physicslib4.Spacetime.CrossIsometry.pushforwardPath_isTimelike` (+1 more)
- [**Lemma 412**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-endpoints) — The Pushforward Transports Endpoints · `Physicslib4.Spacetime.pushforwardPath_isPastEndpoint` (+1 more)
- [**Lemma 413**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-chronology) — Cross-Metric Isometries Transport Chronological Precedence · `Physicslib4.Spacetime.pushforwardPath_isFutureOriented` (+2 more)
- [**Lemma 414**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-chronological-future-image) — Image of the Chronological Future · `Physicslib4.Spacetime.CrossIsometry.chronologicalFuture_image`
- [**Lemma 415**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-chronological-past-image) — Image of the Chronological Past · `Physicslib4.Spacetime.CrossIsometry.chronologicalPast_image`
- [**Lemma 416**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-basis-sets) — Cross-Metric Isometries Preserve Basis Sets · `Physicslib4.Spacetime.CrossIsometry.alexandrovDiamond_image` (+1 more)
- [**Lemma 417**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bijection-generated-topology-homeomorphism) — A Bijection Matching Generating Families is a Homeomorphism · `Physicslib4.continuous_generateFrom_of_preimage_mem` (+4 more)
- [**Lemma 418**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-alexandrov-homeomorphism) — The Pullback Alexandrov Topology · `Physicslib4.Spacetime.pullback_alexandrovBasis_image` (+3 more)
- [**Theorem 419**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pullback-is-lorentzian-spacetime) — The Pullback of a Lorentzian Spacetime is a Lorentzian Spacetime · `Physicslib4.Spacetime.LorentzianSpacetime.pullback_alexandrov_t2` (+3 more)

</details>


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · **§10.4 Spacetime** · [§10.5 Minkowski](sec10-5-haag-kastler.html) · [§10.6 Curved](sec10-6-curved.html) · [§10.7 Covariance](sec10-7-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.5 Minkowski](sec10-5-haag-kastler.html) →
