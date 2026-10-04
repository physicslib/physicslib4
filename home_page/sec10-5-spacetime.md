---
title: "§10.5 Spacetime and causal structure (pp. 247–284)"
usemathjax: true
---

[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Stone](sec10-4-stone.html) · **§10.5 Spacetime** · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.4 Stone](sec10-4-stone.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) →

# §10.5 Spacetime and causal structure (pp. 247–284)

137 items (Definitions 322–458), building the entire causal and topological apparatus the axioms are indexed on. The trips underlying the chronological and causal relations $$\ll$$ and $$\prec$$ are genuine geodesics of the Levi-Civita connection of the metric, which the section constructs for an arbitrary pseudo-Riemannian metric on top of Mathlib's covariant derivatives (Mathlib itself has only a Riemannian Levi-Civita connection and no geodesics). It proceeds in nine layers.

- *Spacetime, tangent-vector causality, and curves (pp. 247–252, items 322–345).* Gives precise definitions of spacetime (Definition 322) and standard Minkowski spacetime (Definition 323); classifies tangent vectors as timelike, spacelike, or null (Definition 324) and proves the trichotomy (Lemma 325), the reverse Cauchy–Schwarz and reverse triangle inequalities for timelike vectors (Lemmas 326–327), and the cone geometry—orientation of pointing vectors, the sign lemma, definiteness of the spacelike complement of a timelike vector, and convexity of the cones (Lemmas 330–333)—alongside time orientations (Definition 328) and future- and past-pointing vectors (Definition 329). Then paths, curves, and oriented curves are defined as equivalence classes of paths up to reparametrisation (Definitions 334–339), with causal type and future/past orientation each shown well-defined on the quotient (Theorems 338 and 340) and a forgetful projection from oriented to unoriented curves (Theorem 341). Endpoints (Definition 342), shown to be well defined on curves and smooth curves (Lemma 343), come with two point-set lemmas—an extremal parameter lies in the frontier, and two endpoints force a compact parameter interval (Lemmas 344–345).
- *The Levi-Civita connection and geodesics (pp. 253–256, items 346–361).* A new layer. Pseudo-Riemannian metrics (Definition 346) are smooth, symmetric, non-degenerate families of bilinear forms, with no signature condition, so everything here applies to every spacetime. Covariant derivatives are Mathlib's `IsCovariantDerivativeOn`; metric compatibility and the Levi-Civita condition (compatible and torsion-free) are defined on top of them (Definitions 347–348). The musical isomorphism $$v \mapsto g_x(v, \cdot)$$ is a linear isomorphism at each point (Lemma 349); the smoothness of its inverse (Lemma 350) is stated and proved in the blueprint but is the one node of the layer not yet formalised, and nothing depends on it. The Koszul formula (Lemma 351), the tensoriality of the Koszul expression (Lemma 352), and the verification that the Koszul connection is a covariant derivative (Lemma 353) that is Levi-Civita (Lemma 354) give existence and uniqueness of the Levi-Civita connection (Theorem 355). Five lemmas about smooth paths—a function vanishing along a path has zero derivative along it, the covariant derivative along a curve is local, local vector fields globalise, a smooth path has a local left inverse, and its velocity extends to a smooth vector field (Lemmas 356–360)—make the geodesic condition chart-free, well defined and non-vacuous. A geodesic (Definition 361) is then an affinely parametrised smooth path $$\mu$$ with $$(\nabla_X X)(\mu(s)) = 0$$ at every interior parameter, for every smooth vector field $$X$$ extending the velocity near $$s$$.
- *Trips, futures and pasts (pp. 257–258, items 362–370).* Trips and causal trips (Definitions 362–363) are finite chains of future-oriented timelike (respectively causal) geodesic segments, geodesic in the sense of Definition 361, with matching past and future endpoints. Chronological and causal precedence are transitive (Theorem 364); the causality condition (Definition 365) makes them a strict partial order (Theorem 366); and chronological and causal futures and pasts (Definitions 367–368) come with their basic inclusion and monotonicity properties (Lemmas 369–370).
- *§10.5.1 Causal diamonds (p. 258, items 371–385).* Introduces the causal diamond $$J^+(p) \cap J^-(q)$$ and the chronological (Alexandrov) diamond $$I^+(p) \cap I^-(q)$$ (Definition 371), with the structural properties of the causal diamond—monotonicity under endpoint spread, causal convexity, and that nonemptiness forces $$p \prec q$$ (Lemma 372)—and the containment of chronological diamonds in causal ones, together with the identification of the Alexandrov basis as exactly the chronological diamonds (Theorem 373). It then develops spacelike separation of points and of regions (Definitions 374–375, Lemmas 376–377), the spacelike complement $$\mathbf{B}^\perp$$ (Definition 378) and its order structure—antitone, extensive on the double complement, with the triple complement collapsing, making complementation the Galois connection attached to the spacelike-separation relation (Lemma 379). The double complement is packaged as the causal closure operator (Definition 380, Lemma 381), whose fixed points are the causally complete regions (Definition 382). These form a complete lattice—meets are intersections, joins are causal closures of unions—on which the causal complement is an order-reversing involution (Theorem 383); the set-level De Morgan laws (Lemma 384) then lift to full binary and infinitary De Morgan laws on the lattice (Theorem 385). The blueprint is careful to record what does *not* hold: the full orthocomplement law $$\mathbf{B} \wedge \mathbf{B}^\perp = \bot$$ fails at this generality, because the trip-based causal relation is irreflexive and so a point is spacelike-separated from itself.
- *§10.5.2 Causal convexity (p. 262, items 386–388).* Defines a causally convex region as one containing every point causally between two of its own points (Definition 386), shows causal diamonds are causally convex (Lemma 387), and shows every spacelike complement—hence every causally complete region—is causally convex (Theorem 388).
- *§10.5.3 Causal convexity: closure structure, and the Alexandrov basis theorems (p. 263, items 389–412).* The causally convex regions are shown to form a closure system (Lemma 389), giving the causal-convex hull (Definition 390) as a genuine closure operator whose closed sets are exactly the causally convex regions (Lemmas 391, Theorem 392). The subsection then turns to the Alexandrov topology (Definition 393): every diamond is open (Lemma 394); chronological futures and pasts are open under an explicit "no endpoints" hypothesis (Lemma 395) and unconditionally on standard Minkowski spacetime, where the coordinate-cone description discharges the hypothesis (Lemma 396). On standard Minkowski spacetime the componentwise directional derivative is a Levi-Civita connection (Lemma 397), hence the Levi-Civita connection is flat (Lemma 398) and affinely parametrised straight lines are geodesics (Lemma 399), so trips there are the familiar straight-line segments. Minkowski spacetime and Lorentzian spacetime are then defined (Definitions 400–401, the latter as a spacetime whose Alexandrov topology is Hausdorff), with a bundled form of spacelike separation and basis openness (Lemma 402). A point lying in no diamond is pathological: its only Alexandrov neighbourhood is the whole space (Lemma 403), and the Hausdorff assumption rules this out, forcing the diamonds to cover the space (Lemma 404). Given downward-directedness the diamonds form a genuine topological basis (Theorem 405); past and future interpolation on standard Minkowski (Lemmas 406–407) supply downward-directedness there (Lemma 408), and common chronological predecessors and successors supply upward-directedness (Lemmas 409–411), so on standard Minkowski the diamonds are an unconditional basis (Theorem 412). Upward-directedness is what the quasilocal colimit of §10.6.1 later consumes.
- *§10.5.4 Dilations are causal automorphisms but not isometries (p. 269, items 413–415).* The dilations $$x \mapsto \lambda x$$ preserve the Minkowski cones (Lemma 413) and are therefore causal automorphisms (Theorem 414), yet scale the metric by $$\lambda^2$$ and so are not isometries for $$\lambda \neq 1$$ (Theorem 415). This is the counterexample that forces the general-covariance morphism of §10.8 to be specified geometrically rather than causally.
- *§10.5.5 Isometries and basis-set preservation (p. 270, items 416–426).* Single-metric transport: isometries preserve the causal classification of tangent vectors (Lemma 416), paths have unique differentials and well-defined pushforwards (Lemmas 417–418), and isometries respect the Levi-Civita structure: pullbacks of vector fields and of the metric pairing, their derivatives and Lie brackets transform naturally (Lemmas 419–421), so an isometry preserves the Levi-Civita connection (Lemma 422) and maps geodesics to geodesics and back (Lemma 423). Future-orientation-preserving isometries preserve chronology (Lemma 424) and map Alexandrov-basis diamonds to diamonds (Lemma 425), which is exactly the well-definedness condition for the Axiom 5 action (Lemma 426).
- *§10.5.6 Pullback metrics and cross-metric isometries (p. 272, items 427–458).* The single-metric lemmas above compare a spacetime with itself; general covariance instead compares two different metrics on one carrier, so the transport statements are redone cross-metric. This subsection defines the pullback $$\psi^* g$$ of a spacetime metric as a bundled family of continuous bilinear forms (Definition 427) and verifies every obligation in turn: the differential of a diffeomorphism is a linear equivalence (Lemma 428), with the two round-trip cancellation identities that Mathlib does not supply for a global `Diffeomorph` proved by hand (Lemmas 429–431); the pullback metric is symmetric, non-degenerate, Lorentzian, and a smooth section of the bilinear-form bundle (Lemmas 432–435), so the pullback of a spacetime is a spacetime (Theorem 436). Two-sided preservation of future orientation is then defined (Definition 437) and the pullback time orientation is shown to be bundle-smooth, nowhere vanishing, and everywhere timelike (Lemmas 438–441), with transport of future-pointing timelike and null vectors (Lemmas 442–443) giving two-sided orientation preservation (Lemma 444). Cross-metric isometries are defined (Definition 445) and shown closed under inverses (Lemma 446), to preserve causal classification (Lemma 447), to push paths forward preserving the timelike/causal conditions and endpoints (Lemmas 448–451), and to transport chronological precedence and the chronological future and past (Lemmas 452–454), hence to preserve Alexandrov-basis sets (Lemma 455). A general topological lemma—a bijection matching generating families is a homeomorphism (Lemma 456)—then identifies the pullback Alexandrov topology (Lemma 457) and yields that the pullback of a Lorentzian spacetime is again a Lorentzian spacetime (Theorem 458). Without Theorem 458 the phrase "the net over $$\psi^*(M,g)$$" in §10.8 would have no referent.

**Where the Lean lives:** `Physicslib4/Geometry/PseudoRiemannian/` (`Basic`, `LeviCivita`, `Flat`), `Physicslib4/Spacetime/` (`Causality`, `Curves`, `AlongPath`, `CausalComplement`, `CausalStructure`, `Minkowski`, `MinkowskiDirected`, `LorentzianSpacetime`, `IsometryCausality`, …)

## Items

Each blueprint subsection below is collapsed; click a heading to see its items. Every entry links to its node in the web blueprint and names the principal Lean declaration.

<details markdown="1">
<summary>§10.5 opening run — spacetime, tangent-vector causality, curves, the Levi-Civita connection and geodesics, trips, futures and pasts (p. 247) — 49 items</summary>

- [**Definition 322**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacetime) — Spacetime · `Physicslib4.Spacetime`
- [**Definition 323**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:standard-minkowski-spacetime) — Standard Minkowski Spacetime · `Physicslib4.StandardMinkowskiSpacetime`
- [**Definition 324**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:timelike-spacelike-null-vectors) — Timelike, Spacelike, or Null Vectors · `Physicslib4.Spacetime.IsTimelike` (+2 more)
- [**Lemma 325**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-classification) — Causal Classification · `Physicslib4.Spacetime.isTimelike_or_isNull_or_isSpacelike` (+5 more)
- [**Lemma 326**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:reverse-cauchy-schwarz) — Reverse Cauchy–Schwarz for Timelike Vectors · `Physicslib4.reverse_cauchy_schwarz_of_lorentzianAt` (+1 more)
- [**Lemma 327**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:timelike-cone-convexity) — Timelike Cone Convexity and Reverse Triangle Inequality · `Physicslib4.add_isTimelike_of_lorentzianAt` (+3 more)
- [**Definition 328**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:time-orientable) — Time Orientation · `Physicslib4.Spacetime.TimeOrientation` (+1 more)
- [**Definition 329**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-and-past-pointing-vectors) — Future and Past Pointing Vectors · `Physicslib4.Spacetime.IsFuturePointing` (+1 more)
- [**Lemma 330**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pointing-orientation) — Orientation of Pointing Vectors · `Physicslib4.Spacetime.isTimelike_or_isNull_of_isFuturePointing` (+2 more)
- [**Lemma 331**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cone-sign-lemma) — Sign Lemma for the Future Cone · `Physicslib4.nonneg_of_orthogonal_timelike` (+4 more)
- [**Lemma 332**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-definite) — Definiteness of the Spacelike Complement · `Physicslib4.eq_zero_of_forall_bilin_eq_zero` (+2 more)
- [**Lemma 333**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:future-cone-convexity) — Convexity of the Future Cone · `Physicslib4.Spacetime.isFuturePointing_add` (+10 more)
- [**Definition 334**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:paths) — Paths · `Physicslib4.Spacetime.Path` (+1 more)
- [**Definition 335**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:curves) — Curves · `Physicslib4.Spacetime.Curve` (+1 more)
- [**Definition 336**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:timelike-and-causal-smooth-curves) — Timelike and Causal Smooth Curves · `Physicslib4.Spacetime.IsTimelikeSmoothCurve` (+1 more)
- [**Definition 337**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:future-and-past-oriented-smooth-curves) — Future and Past Oriented Smooth Curves · `Physicslib4.Spacetime.IsFutureOrientedSmoothCurve` (+1 more)
- [**Theorem 338**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:smooth-curve-causal-well-defined) — Reparametrisation-Invariance of the Causal Type · `Physicslib4.Spacetime.isTimelikeSmoothCurve_ofPath_iff` (+1 more)
- [**Definition 339**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:oriented-smooth-curve) — Oriented Smooth Curve · `Physicslib4.Spacetime.OrientedSmoothCurve`
- [**Theorem 340**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:oriented-curve-well-defined) — Reparametrisation-Invariance of Orientation · `Physicslib4.Spacetime.isFutureOrientedCurve_ofPath_iff` (+1 more)
- [**Theorem 341**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:oriented-curve-projection) — The Forgetful Projection of Oriented Curves · `Physicslib4.Spacetime.OrientedSmoothCurve.toSmoothCurve` (+1 more)
- [**Definition 342**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:endpoints) — Endpoints · `Physicslib4.Spacetime.IsEndpoint` (+2 more)
- [**Lemma 343**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:curve-endpoint-well-defined) — Endpoints of curves are well defined · `Physicslib4.Spacetime.IsCurveEndpoint` (+5 more)
- [**Lemma 344**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:extremal-parameter-mem-frontier) — An extremal parameter lies in the frontier · `Physicslib4.Spacetime.mem_frontier_of_isMin` (+3 more)
- [**Lemma 345**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:endpoint-parameter-space-eq-Icc) — Two endpoints force a compact parameter interval · `Physicslib4.Spacetime.parameterSpace_eq_Icc_of_endpoints`
- [**Definition 346**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pseudo-riemannian-metric) — Pseudo-Riemannian Metric · `Physicslib4.Geometry.PseudoRiemannianMetric` (+1 more)
- [**Definition 347**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:metric-compatible-connection) — Covariant Derivative; Metric Compatibility · `Physicslib4.Geometry.CovariantDerivative.IsMetricCompatibleWith`
- [**Definition 348**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:levi-civita-connection) — Levi-Civita Connection · `Physicslib4.Geometry.CovariantDerivative.IsLeviCivitaFor`
- [**Lemma 349**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:musical-isomorphism) — Musical Isomorphism · `Physicslib4.Geometry.PseudoRiemannianMetric.bijective_val`
- [**Lemma 350**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:musical-inverse-smooth) — Smoothness of the Inverse Musical Isomorphism *(not yet formalised: no Lean declaration — see [Formalisation status](./#formalisation-status))*
- [**Lemma 351**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:koszul-formula) — Koszul Formula · `Physicslib4.Geometry.CovariantDerivative.IsLeviCivitaFor.koszul`
- [**Lemma 352**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:koszul-expression-tensorial) — Tensoriality of the Koszul Expression · `Physicslib4.Geometry.PseudoRiemannianMetric.tensorialAt_koszulAux₁` (+2 more)
- [**Lemma 353**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:koszul-connection-is-covariant-derivative) — The Koszul Connection is a Covariant Derivative · `Physicslib4.Geometry.PseudoRiemannianMetric.isCovariantDerivativeOn_leviCivitaAux`
- [**Lemma 354**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:koszul-connection-is-levi-civita) — The Koszul Connection is Levi-Civita · `Physicslib4.Geometry.PseudoRiemannianMetric.isMetricCompatibleWith_koszulConnection` (+1 more)
- [**Theorem 355**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:levi-civita-exists-unique) — Existence and Uniqueness of the Levi-Civita Connection · `Physicslib4.Geometry.PseudoRiemannianMetric.exists_isLeviCivitaFor` (+3 more)
- [**Lemma 356**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:derivative-vanishes-along-path) — A Function Vanishing Along a Path has Zero Derivative Along It · `Physicslib4.Spacetime.SmoothPath.mfderiv_apply_tangent_eq_zero`
- [**Lemma 357**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:covariant-derivative-along-curve-local) — Covariant Derivative Along a Curve is Local · `Physicslib4.Spacetime.SmoothPath.covDeriv_eq_of_eventuallyEq`
- [**Lemma 358**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:local-vector-field-globalises) — Local Vector Fields Globalise · `Physicslib4.Spacetime.exists_contMDiff_vectorField_eventuallyEq`
- [**Lemma 359**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:path-local-left-inverse) — Local Left Inverse of a Smooth Path · `Physicslib4.Spacetime.SmoothPath.exists_localLeftInverse`
- [**Lemma 360**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:velocity-extends) — The Velocity of a Smooth Path Extends to a Vector Field · `Physicslib4.Spacetime.SmoothPath.exists_vectorField_eq_tangent`
- [**Definition 361**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:geodesic) — Geodesic · `Physicslib4.Spacetime.IsGeodesic`
- [**Definition 362**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:trip) — Trip · `Physicslib4.Spacetime.IsTripSegment` (+2 more)
- [**Definition 363**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-trip) — Causal Trip · `Physicslib4.Spacetime.IsCausalTripSegment` (+2 more)
- [**Theorem 364**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:precedence-transitive) — Transitivity of chronological and causal precedence · `Physicslib4.Spacetime.chronologicallyPrecedes_trans` (+1 more)
- [**Definition 365**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:no-closed-causal-curve) — No Closed Causal Curve (Causality Condition) · `Physicslib4.Spacetime.NoClosedCausalCurve`
- [**Theorem 366**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-order-refinements) — Irreflexivity and Antisymmetry under Causality · `Physicslib4.Spacetime.chronologicallyPrecedes_irrefl` (+2 more)
- [**Definition 367**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:chronological-future-and-chronological-past) — Chronological Future and Chronological Past · `Physicslib4.Spacetime.chronologicalFuture` (+3 more)
- [**Definition 368**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-future-and-causal-past) — Causal Future and Causal Past · `Physicslib4.Spacetime.causalFuture` (+3 more)
- [**Lemma 369**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:chronological-implies-causal) — Chronological Precedence Implies Causal Precedence · `Physicslib4.Spacetime.isCausal_of_isTimelike` (+3 more)
- [**Lemma 370**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:future-past-monotone) — Monotonicity of Futures and Pasts · `Physicslib4.Spacetime.chronologicalFutureSet_mono` (+3 more)

</details>

<details markdown="1">
<summary>§10.5.1 Causal diamonds, spacelike complement, and causal closure (p. 258) — 15 items</summary>

- [**Definition 371**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-diamond) — Causal and chronological diamonds · `Physicslib4.Spacetime.causalDiamond` (+3 more)
- [**Lemma 372**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-diamond-structure) — Structural properties of the causal diamond · `Physicslib4.Spacetime.causalDiamond_subset_of` (+2 more)
- [**Theorem 373**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-diamond-vs-chronological) — Chronological diamonds inside causal diamonds · `Physicslib4.Spacetime.chronologicalDiamond_subset_causalDiamond` (+1 more)
- [**Definition 374**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-related) — Spacelike Related · `Physicslib4.Spacetime.IsSpacelikeRelated`
- [**Definition 375**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:completely-spacelike) — Completely Spacelike · `Physicslib4.Spacetime.IsCompletelySpacelike`
- [**Lemma 376**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completely-spacelike-symm) — Symmetry of Spacelike Separation · `Physicslib4.Spacetime.isSpacelikeRelated_comm` (+1 more)
- [**Lemma 377**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:completely-spacelike-structural) — Structural Properties of Complete Spacelike Separation · `Physicslib4.Spacetime.isCompletelySpacelike_mono` (+9 more)
- [**Definition 378**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:spacelike-complement) — Spacelike Complement of a Region · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement`
- [**Lemma 379**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-order) — Order Structure of the Spacelike Complement · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement_antitone` (+3 more)
- [**Definition 380**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-closure) — Causal closure operator · `Physicslib4.Spacetime.LorentzianSpacetime.causalClosure`
- [**Lemma 381**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-closure-is-closure-operator) — The Causal Closure is a Closure Operator · `Physicslib4.Spacetime.LorentzianSpacetime.causalClosure` (+1 more)
- [**Definition 382**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-complete-region) — Causally complete region · `Physicslib4.Spacetime.LorentzianSpacetime.IsCausallyComplete`
- [**Theorem 383**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-lattice) — Lattice of causally complete regions · `Physicslib4.Spacetime.LorentzianSpacetime.CausallyCompleteRegion` (+8 more)
- [**Lemma 384**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:spacelike-complement-de-morgan) — De Morgan Laws for the Spacelike Complement · `Physicslib4.Spacetime.LorentzianSpacetime.spacelikeComplement_union` (+1 more)
- [**Theorem 385**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-complement-de-morgan) — De Morgan Laws for the Causal Complement · `Physicslib4.Spacetime.LorentzianSpacetime.causalComplement_antitone` (+6 more)

</details>

<details markdown="1">
<summary>§10.5.2 Causal convexity (p. 262) — 3 items</summary>

- [**Definition 386**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causally-convex-region) — Causally convex region · `Physicslib4.Spacetime.IsCausallyConvex`
- [**Lemma 387**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-diamond-causally-convex) — Causal diamonds are causally convex · `Physicslib4.Spacetime.causalDiamond_isCausallyConvex`
- [**Theorem 388**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causally-complete-convex) — Causally complete regions are causally convex · `Physicslib4.Spacetime.spacelikeComplement_isCausallyConvex` (+2 more)

</details>

<details markdown="1">
<summary>§10.5.3 Causal convexity: closure structure, and the Alexandrov basis theorems (p. 263) — 24 items</summary>

- [**Lemma 389**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causally-convex-closure-ops) — Causally convex regions form a closure system · `Physicslib4.Spacetime.isCausallyConvex_univ` (+4 more)
- [**Definition 390**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:causal-convex-hull) — Causal-convex hull · `Physicslib4.Spacetime.causalConvexHull`
- [**Lemma 391**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:causal-convex-hull-extensive) — The Causal-Convex Hull is Extensive and Causally Convex · `Physicslib4.Spacetime.subset_causalConvexHull` (+1 more)
- [**Theorem 392**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:causal-convex-hull-closure) — The causal-convex hull is a closure operator · `Physicslib4.Spacetime.causalConvexHull_minimal` (+3 more)
- [**Definition 393**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:alexandrov-topology) — Alexandrov Topology · `Physicslib4.Spacetime.alexandrovTopology`
- [**Lemma 394**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-basis-open) — Basis Sets Are Alexandrov-Open · `Physicslib4.Spacetime.isOpen_alexandrov_of_mem_basis`
- [**Lemma 395**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:chronological-future-past-open) — Openness of Chronological Futures and Pasts · `Physicslib4.Spacetime.isOpen_chronologicalFuture_inter_chronologicalPast` (+2 more)
- [**Lemma 396**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-chronological-open) — Unconditional Openness of Chronological Futures and Pasts on Standard Minkowski · `Physicslib4.exists_chronologicalFuture_standardMinkowski` (+5 more)
- [**Lemma 397**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-directional-derivative-levi-civita) — The Directional Derivative is Levi-Civita on Standard Minkowski · `Physicslib4.Geometry.PseudoRiemannianMetric.isLeviCivitaFor_flatConnection` (+2 more)
- [**Lemma 398**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-levi-civita-flat) — The Minkowski Levi-Civita Connection is Flat · `Physicslib4.standardMinkowski_leviCivita_apply` (+1 more)
- [**Lemma 399**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-lines-are-geodesics) — Straight Lines are Geodesics in Standard Minkowski · `Physicslib4.standardMinkowskiLineSegmentPath_isGeodesic` (+1 more)
- [**Definition 400**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:minkowski-spacetime) — Minkowski Spacetime · `Physicslib4.MinkowskiSpacetime`
- [**Definition 401**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:lorentzian-spacetime) — Lorentzian Spacetime · `Physicslib4.Spacetime.LorentzianSpacetime`
- [**Lemma 402**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:lorentzian-causal-lifts) — Bundled Spacelike Separation and Basis Openness · `Physicslib4.Spacetime.LorentzianSpacetime.isCompletelySpacelike_comm` (+1 more)
- [**Lemma 403**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-nbhd-univ-of-no-diamond) — No-Diamond Points Have Only the Whole Space as Neighbourhood · `Physicslib4.Spacetime.alexandrov_nbhd_univ_of_no_diamond`
- [**Lemma 404**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:alexandrov-covering-hausdorff) — Covering from the Hausdorff Assumption · `Physicslib4.Spacetime.LorentzianSpacetime.sUnion_alexandrovBasis_eq_univ`
- [**Theorem 405**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:alexandrov-topological-basis) — The Alexandrov Diamonds Form a Topological Basis · `Physicslib4.Spacetime.LorentzianSpacetime.isTopologicalBasis_alexandrovBasis`
- [**Lemma 406**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-past-between) — Past Interpolation on Standard Minkowski · `Physicslib4.Spacetime.exists_past_between_standardMinkowski`
- [**Lemma 407**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-future-between) — Future Interpolation on Standard Minkowski · `Physicslib4.Spacetime.exists_future_between_standardMinkowski`
- [**Lemma 408**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-downward-directed) — Standard Minkowski Diamonds Are Downward-Directed · `Physicslib4.Spacetime.alexandrovBasis_exists_subset_inter_standardMinkowski`
- [**Lemma 409**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-exists-common-past) — Common Chronological Predecessor on Standard Minkowski · `Physicslib4.Spacetime.exists_common_past`
- [**Lemma 410**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-exists-common-future) — Common Chronological Successor on Standard Minkowski · `Physicslib4.Spacetime.exists_common_future`
- [**Lemma 411**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-diamonds-upward-directed) — Standard Minkowski Diamonds Are Upward-Directed · `Physicslib4.Spacetime.alexandrovBasis_directed`
- [**Theorem 412**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-alexandrov-basis) — The Alexandrov Diamonds are a Basis on Standard Minkowski · `Physicslib4.Spacetime.isTopologicalBasis_alexandrovBasis_standardMinkowski`

</details>

<details markdown="1">
<summary>§10.5.4 Dilations are causal automorphisms but not isometries (p. 269) — 3 items</summary>

- [**Lemma 413**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:minkowski-dilation-cone) — Dilations Preserve the Minkowski Cones · `Physicslib4.minkowskiForwardCone_smul` (+1 more)
- [**Theorem 414**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-dilation-causal-automorphism) — Dilations are Causal Automorphisms · `Physicslib4.alexandrovBasis_image_smul`
- [**Theorem 415**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:minkowski-dilation-not-isometry) — Dilations are Not Isometries · `Physicslib4.minkowskiForm_smul` (+1 more)

</details>

<details markdown="1">
<summary>§10.5.5 Isometries and basis-set preservation (p. 270) — 11 items</summary>

- [**Lemma 416**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-classification) — Isometries Preserve the Causal Classification · `Physicslib4.Spacetime.Isometry.preserves_self` (+3 more)
- [**Lemma 417**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:path-parameter-unique-diff) — Unique Differentials Along a Path · `Physicslib4.Spacetime.Path.uniqueDiffOn_parameterSpace`
- [**Lemma 418**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pushforward-path) — Pushforward of a Path Under an Isometry · `Physicslib4.Spacetime.Isometry.pushforwardPath` (+5 more)
- [**Lemma 419**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-pullback-metric) — Pullback of Vector Fields and the Metric Under an Isometry · `Physicslib4.Spacetime.Isometry.val_mpullback` (+3 more)
- [**Lemma 420**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-pullback-metric-derivative) — Derivatives of Metric Pairings of Pulled-Back Fields · `Physicslib4.Spacetime.Isometry.mfderiv_val_mpullback` (+1 more)
- [**Lemma 421**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-pullback-lie-bracket) — Metric Pairings with Lie Brackets of Pulled-Back Fields · `Physicslib4.Spacetime.Isometry.val_mlieBracket_mpullback` (+1 more)
- [**Lemma 422**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-levi-civita) — Isometries Preserve the Levi-Civita Connection · `Physicslib4.Spacetime.Isometry.mfderiv_leviCivita_mpullback` (+1 more)
- [**Lemma 423**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-geodesics) — Isometries Preserve Geodesics · `Physicslib4.Spacetime.Isometry.pushforwardPath_isGeodesic` (+2 more)
- [**Lemma 424**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-chronology) — Isometries Preserve Chronology · `Physicslib4.Spacetime.Isometry.PreservesFutureOrientation` (+8 more)
- [**Lemma 425**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:isometry-preserves-basis-sets) — Isometries Preserve Basis Sets · `Physicslib4.Spacetime.Isometry.futureOrientationPreserving` (+8 more)
- [**Lemma 426**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:axiom5-basis-preservation) — Axiom 5 Basis-Set Preservation · `Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent_isBasisSet_smul`

</details>

<details markdown="1">
<summary>§10.5.6 Pullback metrics and cross-metric isometries (p. 272) — 32 items</summary>

- [**Definition 427**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:pullback-metric) — Pullback of a Spacetime Metric · `Physicslib4.Spacetime.bilinearPrecomp` (+3 more)
- [**Lemma 428**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-diffeo-linear-equiv) — The Differential of a Diffeomorphism is a Linear Equivalence · `Physicslib4.Spacetime.Diffeo` (+4 more)
- [**Lemma 429**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-symm-cancel-left) — Round-Trip Cancellation: $$d\psi$$ After $$d(\psi^{-1})$$ · `Physicslib4.Spacetime.mfderiv_symm_cancel_left`
- [**Lemma 430**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-symm-cancel-right) — Round-Trip Cancellation: $$d(\psi^{-1})$$ After $$d\psi$$ · `Physicslib4.Spacetime.mfderiv_symm_cancel_right`
- [**Lemma 431**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mfderiv-inverse-eq-symm) — The Formal Inverse of $$d\psi_x$$ is the Inverse Equivalence · `Physicslib4.Spacetime.inverse_mfderiv_eq_symm` (+2 more)
- [**Lemma 432**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-symm) — The Pullback Metric is Symmetric · `Physicslib4.Spacetime.pullbackVal_symm`
- [**Lemma 433**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-nondegenerate) — The Pullback Metric is Non-Degenerate · `Physicslib4.Spacetime.pullbackVal_nondegenerate`
- [**Lemma 434**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-lorentzian) — The Pullback Metric is Lorentzian · `Physicslib4.Spacetime.pullbackVal_lorentzian`
- [**Lemma 435**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-metric-smooth-in-charts) — The Pullback Metric is a Smooth Section of the Bilinear-Form Bundle · `Physicslib4.Spacetime.pullbackVal_contMDiff`
- [**Theorem 436**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pullback-is-spacetime) — The Pullback of a Spacetime is a Spacetime · `Physicslib4.Spacetime.pullback` (+4 more)
- [**Definition 437**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:preserves-future-orientation) — Two-Sided Preservation of Future Orientation · `Physicslib4.Spacetime.PreservesFutureOrientation` (+1 more)
- [**Lemma 438**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:mpullback-vectorField-contMDiff-of-diffeo) — The Pullback of a Bundle-Smooth Vector Field Along a Diffeomorphism is Bundle-Smooth · `Physicslib4.Spacetime.contMDiff_mpullback_vectorField`
- [**Lemma 439**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation-ne-zero) — The Pullback Time Orientation is Nowhere Vanishing · `Physicslib4.Spacetime.mpullback_field_ne_zero`
- [**Lemma 440**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation-timelike) — The Pullback Time Orientation is Everywhere Timelike · `Physicslib4.Spacetime.pullbackVal_mpullback_field_self` (+1 more)
- [**Lemma 441**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-time-orientation) — Pullback of a Time Orientation · `Physicslib4.Spacetime.pullbackTimeOrientation` (+1 more)
- [**Lemma 442**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-future-pointing-timelike) — Transport of Future-Pointing Timelike Vectors · `Physicslib4.Spacetime.pullbackVal_mpullback_field_apply` (+1 more)
- [**Lemma 443**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-future-pointing-null) — Transport of Future-Pointing Null Vectors · `Physicslib4.Spacetime.isFuturePointing_pullback_iff_of_isNull`
- [**Lemma 444**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-preserves-future-orientation) — The Pullback Preserves the Future Orientation Two-Sidedly · `Physicslib4.Spacetime.pullback_preservesFutureOrientationTwoSided`
- [**Definition 445**](blueprint/chptr-haag-kastler-axioms-blueprint.html#def:cross-metric-isometry) — Isometry Between Two Metrics on One Manifold · `Physicslib4.Spacetime.CrossIsometry` (+4 more)
- [**Lemma 446**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-symm) — The Inverse of a Cross-Metric Isometry is a Cross-Metric Isometry · `Physicslib4.Spacetime.CrossIsometry.symm_preserves` (+1 more)
- [**Lemma 447**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-classification) — Cross-Metric Isometries Preserve the Causal Classification · `Physicslib4.Spacetime.CrossIsometry.preserves_self` (+3 more)
- [**Lemma 448**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-tangent) — The Tangent Chain Rule Along a Path · `Physicslib4.Spacetime.mfderivWithin_comp_diffeo` (+1 more)
- [**Lemma 449**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path) — Pushforward of a Path Under a Cross-Metric Isometry · `Physicslib4.Spacetime.pushforwardPath` (+2 more)
- [**Lemma 450**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-causal) — The Pushforward Preserves the Timelike and Causal Conditions · `Physicslib4.Spacetime.CrossIsometry.pushforwardPath_isTimelike` (+1 more)
- [**Lemma 451**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-pushforward-path-endpoints) — The Pushforward Transports Endpoints · `Physicslib4.Spacetime.pushforwardPath_isPastEndpoint` (+1 more)
- [**Lemma 452**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-chronology) — Cross-Metric Isometries Transport Chronological Precedence · `Physicslib4.Spacetime.pushforwardPath_isFutureOriented` (+2 more)
- [**Lemma 453**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-chronological-future-image) — Image of the Chronological Future · `Physicslib4.Spacetime.CrossIsometry.chronologicalFuture_image`
- [**Lemma 454**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-chronological-past-image) — Image of the Chronological Past · `Physicslib4.Spacetime.CrossIsometry.chronologicalPast_image`
- [**Lemma 455**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:cross-metric-isometry-preserves-basis-sets) — Cross-Metric Isometries Preserve Basis Sets · `Physicslib4.Spacetime.CrossIsometry.alexandrovDiamond_image` (+1 more)
- [**Lemma 456**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:bijection-generated-topology-homeomorphism) — A Bijection Matching Generating Families is a Homeomorphism · `Physicslib4.continuous_generateFrom_of_preimage_mem` (+4 more)
- [**Lemma 457**](blueprint/chptr-haag-kastler-axioms-blueprint.html#lmm:pullback-alexandrov-homeomorphism) — The Pullback Alexandrov Topology · `Physicslib4.Spacetime.pullback_alexandrovBasis_image` (+3 more)
- [**Theorem 458**](blueprint/chptr-haag-kastler-axioms-blueprint.html#thrm:pullback-is-lorentzian-spacetime) — The Pullback of a Lorentzian Spacetime is a Lorentzian Spacetime · `Physicslib4.Spacetime.LorentzianSpacetime.pullback_alexandrov_t2` (+3 more)

</details>


[Home](./) · [§10.1 GNS](sec10-1-gns.html) · [§10.2 Spectral](sec10-2-spectral.html) · [§10.3 Unbounded](sec10-3-unbounded.html) · [§10.4 Stone](sec10-4-stone.html) · **§10.5 Spacetime** · [§10.6 Minkowski](sec10-6-haag-kastler.html) · [§10.7 Curved](sec10-7-curved.html) · [§10.8 Covariance](sec10-8-general-covariance.html) · [Axioms](axioms.html) · [Guide](guide.html)

← [§10.4 Stone](sec10-4-stone.html) · [§10.6 Minkowski](sec10-6-haag-kastler.html) →
