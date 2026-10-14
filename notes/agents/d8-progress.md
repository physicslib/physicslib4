# D8 progress log: universe-polymorphic curved-spacetime net

Decision D8: the curved local algebras live in a universe `v` independent of the
carrier universe `u`, and the curved GNS witnesses live in `Type v`.

- `HaagKastlerCurved/LocalAlgebras.lean`: `LocalNet.{u, v} (M : LorentzianSpacetime.{u})`,
  `algebra : Set M.Carrier → Type v`. Compiles.
- `HaagKastlerCurved/LocalAlgebra.lean`: `IsLocalObservable`, `localObservables` and the
  observable lemmas take `{H : Type*}`; `LocalAlgebra (U : LocalNet.{u, v} M)` quantifies over
  `H : Type v`; `exists_isLocalObservable` witnesses `H : Type v`. Compiles.
- `Isotony.lean`, `LocalCommutativity.lean`, `IsometricCovariance.lean`: no change needed
  (universes auto-bound). Compile.
- `HaagKastlerCurved/Net.lean`: `HaagKastlerNet.{u, v} (M : LorentzianSpacetime.{u})` with
  `U : LocalNet.{u, v} M`; net-level observable section uses `H : Type v`;
  `trivialLocalNet`, `trivialHaagKastlerNet` and `nonempty_haagKastlerNet` are stated at
  `v := 0` (as the Minkowski `nonempty_haagKastlerNet` is). Compiles.
- `EinsteinCausality.lean`, `Purity.lean`, `StabilizerKMS.lean`, `StabilizerAction.lean`:
  `variable {M : LorentzianSpacetime.{u}} (N : HaagKastlerNet.{u, v} M)`; every GNS witness
  `∃ (H : Type)` / `∃ (K : Type)` (including the `IsGroundStateForFlow` definition) is
  `Type v`. Compile.
- `IdentityComponent.lean`: `nonempty_haagKastlerNet_identityComponent` is stated at
  `HaagKastlerNet.{_, 0}`. Compiles.
- `GeneralCovariance.lean`: `NetTheory` gains the algebra universe parameter (auto-bound,
  `NetTheory.{v}`); docstring notes it. `NetEquivalence` lets the two nets have independent
  algebra universes. Compiles.
- `Spacetime.lean`: modelling note rewritten (algebras in universe `v` independent of the
  carrier; GNS spaces of Axiom 4 in the algebras' universe, as in Minkowski). Compiles.
- Verification: `lake build` succeeds with no warnings in `HaagKastlerCurved/`; `lake lint`
  passes; `#print axioms` on `nonempty_haagKastlerNet_identityComponent`,
  `exists_gns_einstein_causality`, `IsKMSStateForFlow.exists_gns_unitary_strongContinuous`
  and `exists_gns_irreducible_covariant_stabilizer` gives `propext`, `Classical.choice`,
  `Quot.sound`.
