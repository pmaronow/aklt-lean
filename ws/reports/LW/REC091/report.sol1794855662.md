STATUS: PARTIAL

The exact closed declaration `AKLT.W.REC091.main : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2` remains open. The compiled submission proves the target from one explicit closed residual. It discharges the earlier attempt's departure-integration and removed-partition-positivity residuals completely.

## Files

All Lean files are under `/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/`:

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Main.lean): retained H1 termwise comparison and cancellation; new proofs of the two former residuals; target from one remaining residual.
- [Spin.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Spin.lean): exact icosahedral unit norms, ball dot bounds, six distinct atoms in an open half-space.
- [Positive.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Positive.lean): positivity of every frozen network partition, pair-mean bounds, and positive canonical J.
- [Graph.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Graph.lean): orientation and incident-bond reindexing.
- [Remove.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Remove.lean): deletion identities and the configuration equivalence splitting off one spin.
- [OneSite.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/OneSite.lean): exact finite Fubini identity for departure integration.
- [Departure.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Departure.lean): no original leg at an unprotected departure; trace/removal compatibility; both departure disintegrations.
- [Integrals.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Integrals.lean): explicit U three-factor and D two-factor integrals with the exact coefficients 1/3 and 1/5.
- [Factorizations.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Factorizations.lean): both frozen factorization statements and both true step-ratio identities.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Audit.lean): declaration types, axioms of every exported theorem, and exact conditional type checks.

The prior report is preserved in `report.luna.md`. Full verification logs are [build.log](/home/ubuntu/aklt/reports/LW/REC091/build.log) and [audit.log](/home/ubuntu/aklt/reports/LW/REC091/audit.log).

## Principal exported declarations

Every declaration below is in namespace `AKLT.W.REC091`. The complete types of every exported declaration appear in the audit transcript below.

- `network_partition_pos`: for every original finite G, every `D : Network G`, every original unit pin assignment τ, and either Boolean b, `0 < D.partition τ b (fun _ => 1)`. This needs no Auxiliary or consistency premise. Six candidate atoms have strictly positive mutual bond factors; at most four original pins at each site exclude at most four candidates.
- `removedPairMean_bounds`: for any D, τ, b, y, f, g, `-1 ≤ removedPairMean D τ b y f g ∧ removedPairMean D τ b y f g ≤ 1`.
- `responseJ_pos`: for any D, τ, b, y, f, g, `0 < responseJ D τ b y f g`.
- `partition_integrate_site`: when y is active and no original leg is based at y, the partition equals the departure-deleted partition applied to the exact single-site functional of its present incident factors.
- `departure_disintegration`: proves both current and post-step versions of that identity for every U Departure and either pin Boolean.
- `twoFactorization : AKLT.Blueprint.Rec.TwoFactorizationStatement`.
- `threeFactorization : AKLT.Blueprint.Rec.ThreeFactorizationStatement`.
- `stepRatio_two`: under the frozen two-neighbour hypotheses, `stepRatio a.D a.τ b a.y a.o = (responseI₂ a.D a.τ b a.y a.o f)⁻¹`.
- `stepRatio_three`: under the frozen three-neighbour hypotheses, `stepRatio a.D a.τ b a.y a.o = responseJ a.D a.τ b a.y f g / responseI a.D a.τ b a.y a.o f g`.
- `stepFactorizations : Residual_StepFactorizations` and `removedPartitionPositive : Residual_RemovedPartitionPositive` close those two residuals from the earlier file.
- `partitionLower_of_sharedCoverMixture : Residual_SharedCoverMixture → Residual_PartitionLower`.
- `main_of_partitionLower : Residual_PartitionLower → AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2`.
- `main_of_sharedCoverMixture : Residual_SharedCoverMixture → AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2`.

The retained `main_of_residuals` and `main_from_core_residuals` remain valid intermediate reductions. Their factorization and positivity premises now have unconditional proofs in this directory.

## Remaining residual and open issue

The only independent open construction in the shared-cover route is:

```lean
def Residual_SharedCoverMixture : Prop :=
  AKLT.Blueprint.Rec.LocalMixtureStatementV2
```

Unfolded, it says:

```lean
∀ a : AKLT.Blueprint.Rec.Departure, a.D.status a.y = .U →
  ∀ incoming outgoing : AKLT.Defs.Compass,
    a.o = a.y + outgoing.step →
    AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
    ∃ k : ℕ, ∃ π : Fin k → AKLT.Defs.PatternData,
      ∃ m : Fin k → (Fin 20 → AKLT.Defs.UnitVector),
      ∃ weight : Fin k → ℝ,
      (∀ i, 0 ≤ weight i ∧ (π i).Covered ∧
        ((π i).outgoing = .north ↔ outgoing = incoming)) ∧
      a.D.partition a.τ true (fun _ => 1) =
        ∑ i, weight i * AKLT.Defs.patternCurrent (π i) (m i) ∧
      (AKLT.Defs.traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) =
        ∑ i, weight i * AKLT.Defs.patternNext (π i) (m i)
```

I did not complete the finite outside-spin disintegration into these covered pattern sums, the replacement of actual tips by covering U tips, and the simultaneous convex filling of corner slots. These operations must share nonnegative weights and preserve the straight/turn Boolean under the template chart. The one-site integration infrastructure delivered here does not by itself prove that multi-site reconstruction.

A weaker sufficient residual, `Residual_PartitionLower`, is also explicit in Main.lean: for the same H1, U Departure, chart, and shared cover premises, it asserts `c * Z_next ≤ Z_current`, with exactly `c = (localThreshold (decide (outgoing = incoming)) : ℝ)`. `main_of_partitionLower` proves the requested conclusion from this single partition inequality. The shared-mixture residual implies it by the proved termwise H1 argument.

No counterexample or missing mathematical premise was established. The frozen statement, localThreshold Boolean, canonical responseI/responseI₂/responseJ, and all existing files outside this task directory were left unchanged. No theorem from another unproved blueprint leaf is used as a proved dependency.

## Build and verification

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC091.Main` — passed; final timed build 9.81 s, Main compile 3.4 s. New helper modules also built successfully.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC091/Audit.lean` — passed in 3.90 s.
- Audit coverage: all 79 exported theorems. Every axiom set is a subset of `propext`, `Classical.choice`, and `Quot.sound`.
- Source scan found no forbidden proof placeholders, computation escapes, or declarations.
- Audit examples check the exact target type with each explicit sufficient residual, and the exact two frozen factorization statement types.
- The requested unconditional `AKLT.W.REC091.main` is absent; the unconditional exact-type check remains unsatisfied.

## Complete declaration types and #print axioms output

```text
AKLT.W.REC091.originalLeg_outside {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (he : e ∈ AKLT.Defs.originalLegs G) : e.2 ∉ G
'AKLT.W.REC091.originalLeg_outside' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.neighbour_distance {y z : AKLT.Defs.Plane} (hz : z ∈ AKLT.Defs.neighbours y) :
  AKLT.Defs.latticeDist y z = 1
'AKLT.W.REC091.neighbour_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.no_original_leg_of_unprotected {G : Finset AKLT.Defs.Plane} {y : AKLT.Defs.Plane} (hy : y ∈ G)
  (hs : y ∉ AKLT.Defs.protectedSites G) (e : ↥(AKLT.Defs.originalLegs G)) : (↑e).1 ≠ y
'AKLT.W.REC091.no_original_leg_of_unprotected' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.trace_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) : (AKLT.Defs.traceStep D y o).active = D.active
'AKLT.W.REC091.trace_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.trace_neighbours {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) :
  (AKLT.Defs.traceStep D y o).presentNeighbours y = (D.presentNeighbours y).erase o
'AKLT.W.REC091.trace_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.remove_trace_status {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).status = (AKLT.Defs.removeSite D y).status
'AKLT.W.REC091.remove_trace_status' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.remove_trace_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).bonds = (AKLT.Defs.removeSite D y).bonds
'AKLT.W.REC091.remove_trace_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.partition_congr {G : Finset AKLT.Defs.Plane} {D E : AKLT.Defs.Network G} (hs : D.status = E.status)
  (hb : D.bonds = E.bonds) (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = E.partition τ b f
'AKLT.W.REC091.partition_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.remove_trace_partition {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).partition τ b f = (AKLT.Defs.removeSite D y).partition τ b f
'AKLT.W.REC091.remove_trace_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.departure_disintegration (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = AKLT.Defs.Status.U)
  (b : Bool) :
  ((a.D.partition a.τ b fun x => 1) =
      (AKLT.Defs.removeSite a.D a.y).partition a.τ b fun n =>
        AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v =>
          ∏ z ∈ a.D.presentNeighbours a.y, (1 + AKLT.Defs.dot v (n z))) ∧
    ((AKLT.Defs.traceStep a.D a.y a.o).partition a.τ b fun x => 1) =
      (AKLT.Defs.removeSite a.D a.y).partition a.τ b fun n =>
        AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun v =>
          ∏ z ∈ (a.D.presentNeighbours a.y).erase a.o, (1 + AKLT.Defs.dot v (n z))
'AKLT.W.REC091.departure_disintegration' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.partition_affine_one {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) (q : ℝ) :
  (D.partition τ b fun n => 1 + F n / q) = (D.partition τ b fun x => 1) * (1 + D.expectation τ b F / q)
'AKLT.W.REC091.partition_affine_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.partition_affine_three {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (F H K : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun n => 1 + (F n + H n + K n) / 3) =
    (D.partition τ b fun x => 1) * (1 + (D.expectation τ b F + D.expectation τ b H + D.expectation τ b K) / 3)
'AKLT.W.REC091.partition_affine_three' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.twoFactorization : AKLT.Blueprint.Rec.TwoFactorizationStatement
'AKLT.W.REC091.twoFactorization' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.threeFactorization : AKLT.Blueprint.Rec.ThreeFactorizationStatement
'AKLT.W.REC091.threeFactorization' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.stepRatio_two (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = AKLT.Defs.Status.U)
  (f : AKLT.Defs.Plane) (hn : a.D.presentNeighbours a.y = {a.o, f}) (hne : a.o ≠ f) (b : Bool) :
  AKLT.Defs.stepRatio a.D a.τ b a.y a.o = (AKLT.Blueprint.Rec.responseI₂ a.D a.τ b a.y a.o f)⁻¹
'AKLT.W.REC091.stepRatio_two' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.stepRatio_three (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = AKLT.Defs.Status.U)
  (f g : AKLT.Defs.Plane) (hn : a.D.presentNeighbours a.y = {a.o, f, g}) (hof : a.o ≠ f) (hog : a.o ≠ g) (hfg : f ≠ g)
  (b : Bool) :
  AKLT.Defs.stepRatio a.D a.τ b a.y a.o =
    AKLT.Defs.responseJ a.D a.τ b a.y f g / AKLT.Defs.responseI a.D a.τ b a.y a.o f g
'AKLT.W.REC091.stepRatio_three' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.adjacent_symm {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : AKLT.Defs.Adjacent z x
'AKLT.W.REC091.adjacent_symm' depends on axioms: [propext]
AKLT.W.REC091.present_symm {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x z : AKLT.Defs.Plane}
  (h : D.Present x z) : D.Present z x
'AKLT.W.REC091.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.mem_internalBonds {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane} :
  e ∈ AKLT.Defs.internalBonds G ↔ e.1 ∈ G ∧ e.2 ∈ G ∧ e.2 ∈ AKLT.Defs.positiveNeighbours e.1
'AKLT.W.REC091.mem_internalBonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.internalBonds_asymm {G : Finset AKLT.Defs.Plane} {x z : AKLT.Defs.Plane}
  (h : (x, z) ∈ AKLT.Defs.internalBonds G) : (z, x) ∉ AKLT.Defs.internalBonds G
'AKLT.W.REC091.internalBonds_asymm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.positive_neighbour_ne {x z : AKLT.Defs.Plane} (h : z ∈ AKLT.Defs.positiveNeighbours x) : z ≠ x
'AKLT.W.REC091.positive_neighbour_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.positive_mem_neighbours {x z : AKLT.Defs.Plane} (h : z ∈ AKLT.Defs.positiveNeighbours x) :
  z ∈ AKLT.Defs.neighbours x ∧ x ∈ AKLT.Defs.neighbours z
'AKLT.W.REC091.positive_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.present_edge {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x z : AKLT.Defs.Plane}
  (hz : z ∈ D.presentNeighbours x) : (x, z) ∈ D.bonds ∨ (z, x) ∈ D.bonds
'AKLT.W.REC091.present_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.otherEndpoint (y : AKLT.Defs.Plane) (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : AKLT.Defs.Plane
AKLT.W.REC091.incident_image {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  Finset.image (AKLT.W.REC091.otherEndpoint y) ({e ∈ D.bonds | e.1 = y ∨ e.2 = y}) = D.presentNeighbours y
'AKLT.W.REC091.incident_image' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.incident_injective {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  Set.InjOn (AKLT.W.REC091.otherEndpoint y) ↑({e ∈ D.bonds | e.1 = y ∨ e.2 = y})
'AKLT.W.REC091.incident_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.siteFunctional_D (f : AKLT.Defs.Vec3 → ℝ) :
  AKLT.Defs.siteFunctional AKLT.Defs.Status.D f = 3 / 5 * AKLT.Defs.siteFunctional AKLT.Defs.Status.U f + 2 / 5 * f 0
'AKLT.W.REC091.siteFunctional_D' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.integrate_U_three (a b c : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun n =>
      (1 + AKLT.Defs.dot n a) * (1 + AKLT.Defs.dot n b) * (1 + AKLT.Defs.dot n c)) =
    1 + (AKLT.Defs.dot a b + AKLT.Defs.dot a c + AKLT.Defs.dot b c) / 3
'AKLT.W.REC091.integrate_U_three' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.integrate_U_two (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun n => (1 + AKLT.Defs.dot n a) * (1 + AKLT.Defs.dot n b)) =
    1 + AKLT.Defs.dot a b / 3
'AKLT.W.REC091.integrate_U_two' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.integrate_U_one (a : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun n => 1 + AKLT.Defs.dot n a) = 1
'AKLT.W.REC091.integrate_U_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.integrate_D_two (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun n => (1 + AKLT.Defs.dot n a) * (1 + AKLT.Defs.dot n b)) =
    1 + AKLT.Defs.dot a b / 5
'AKLT.W.REC091.integrate_D_two' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.integrate_D_one (a : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun n => 1 + AKLT.Defs.dot n a) = 1
'AKLT.W.REC091.integrate_D_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.Residual_SharedCoverMixture : Prop
AKLT.W.REC091.Residual_StepFactorizations : Prop
AKLT.W.REC091.Residual_RemovedPartitionPositive : Prop
AKLT.W.REC091.stepFactorizations : AKLT.W.REC091.Residual_StepFactorizations
'AKLT.W.REC091.stepFactorizations' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.removedPartitionPositive : AKLT.W.REC091.Residual_RemovedPartitionPositive
'AKLT.W.REC091.removedPartitionPositive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.Residual_PartitionLower : Prop
AKLT.W.REC091.partitionLower_of_sharedCoverMixture (hMix : AKLT.W.REC091.Residual_SharedCoverMixture) :
  AKLT.W.REC091.Residual_PartitionLower
'AKLT.W.REC091.partitionLower_of_sharedCoverMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.main_of_residuals (hLower : AKLT.W.REC091.Residual_PartitionLower)
  (hFact : AKLT.W.REC091.Residual_StepFactorizations) (hPos : AKLT.W.REC091.Residual_RemovedPartitionPositive) :
  AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2
'AKLT.W.REC091.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.main_from_core_residuals (hMix : AKLT.W.REC091.Residual_SharedCoverMixture)
  (hFact : AKLT.W.REC091.Residual_StepFactorizations) (hPos : AKLT.W.REC091.Residual_RemovedPartitionPositive) :
  AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2
'AKLT.W.REC091.main_from_core_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.main_of_partitionLower (hLower : AKLT.W.REC091.Residual_PartitionLower) :
  AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2
'AKLT.W.REC091.main_of_partitionLower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.main_of_sharedCoverMixture (hMix : AKLT.W.REC091.Residual_SharedCoverMixture) :
  AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2
'AKLT.W.REC091.main_of_sharedCoverMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.bondWeights_insert {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  ∏ e ∈ D.bonds,
      (1 +
        AKLT.Defs.dot (D.spins (AKLT.W.REC091.insertSpin D y hy j m) e.1)
          (D.spins (AKLT.W.REC091.insertSpin D y hy j m) e.2)) =
    (∏ e ∈ (AKLT.Defs.removeSite D y).bonds,
        (1 + AKLT.Defs.dot ((AKLT.Defs.removeSite D y).spins m e.1) ((AKLT.Defs.removeSite D y).spins m e.2))) *
      ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot (AKLT.Defs.spinVector j) ((AKLT.Defs.removeSite D y).spins m z))
'AKLT.W.REC091.bondWeights_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.legWeights_insert {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∈ D.active) (hleg : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ y)
  (j : AKLT.Defs.SpinLetter) (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  (∏ e,
      if b = true ∧ (↑e).1 ∈ D.active then
        1 + AKLT.Defs.dot (↑(τ e)) (D.spins (AKLT.W.REC091.insertSpin D y hy j m) (↑e).1)
      else 1) =
    ∏ e,
      if b = true ∧ (↑e).1 ∈ (AKLT.Defs.removeSite D y).active then
        1 + AKLT.Defs.dot (↑(τ e)) ((AKLT.Defs.removeSite D y).spins m (↑e).1)
      else 1
'AKLT.W.REC091.legWeights_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.networkWeight_insert {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∈ D.active)
  (hleg : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ y) (j : AKLT.Defs.SpinLetter)
  (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  AKLT.W.REC091.networkWeight D τ b (AKLT.W.REC091.insertSpin D y hy j m) =
    AKLT.W.REC091.networkWeight (AKLT.Defs.removeSite D y) τ b m * AKLT.Defs.spinWeight (D.status y) j *
      ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot (AKLT.Defs.spinVector j) ((AKLT.Defs.removeSite D y).spins m z))
'AKLT.W.REC091.networkWeight_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.partition_integrate_site {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∈ D.active)
  (hleg : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ y) :
  (D.partition τ b fun x => 1) =
    (AKLT.Defs.removeSite D y).partition τ b fun n =>
      AKLT.Defs.siteFunctional (D.status y) fun v => ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot v (n z))
'AKLT.W.REC091.partition_integrate_site' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.hemisphere_avoid.{u_1} {ι : Type u_1} [Fintype ι] (hι : Fintype.card ι ≤ 4) (b : ι → AKLT.Defs.Vec3)
  (hb : ∀ (i : ι), AKLT.Defs.normSq (b i) ≤ 1) :
  ∃ j, ∀ (i : ι), 0 < 1 + AKLT.Defs.dot (AKLT.Defs.icoVector (AKLT.W.REC091.hemisphereLetter j)) (b i)
'AKLT.W.REC091.hemisphere_avoid' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.originalLeg_neighbour {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (he : e ∈ AKLT.Defs.originalLegs G) : e.2 ∈ AKLT.Defs.neighbours e.1
'AKLT.W.REC091.originalLeg_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.originalLegs_at_card (G : Finset AKLT.Defs.Plane) (x : AKLT.Defs.Plane) :
  {e ∈ AKLT.Defs.originalLegs G | e.1 = x}.card ≤ 4
'AKLT.W.REC091.originalLegs_at_card' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.network_spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins n x) ≤ 1
'AKLT.W.REC091.network_spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.networkWeight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) : ℝ
AKLT.W.REC091.partition_eq_sum_weight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = ∑ n, AKLT.W.REC091.networkWeight D τ b n * f (D.spins n)
'AKLT.W.REC091.partition_eq_sum_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.networkWeight_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) :
  0 ≤ AKLT.W.REC091.networkWeight D τ b n
'AKLT.W.REC091.networkWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.network_partition_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) : 0 ≤ D.partition τ b fun x => 1
'AKLT.W.REC091.network_partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.network_partition_pos {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) : 0 < D.partition τ b fun x => 1
'AKLT.W.REC091.network_partition_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.removedPairMean_bounds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (y f g : AKLT.Defs.Plane) :
  -1 ≤ AKLT.Defs.removedPairMean D τ b y f g ∧ AKLT.Defs.removedPairMean D τ b y f g ≤ 1
'AKLT.W.REC091.removedPairMean_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.responseJ_pos {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y f g : AKLT.Defs.Plane) : 0 < AKLT.Defs.responseJ D τ b y f g
'AKLT.W.REC091.responseJ_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.remove_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).active = D.active.erase y
'AKLT.W.REC091.remove_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.mem_remove_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y x : AKLT.Defs.Plane) :
  x ∈ (AKLT.Defs.removeSite D y).active ↔ x ≠ y ∧ x ∈ D.active
'AKLT.W.REC091.mem_remove_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.remove_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).bonds = {e ∈ D.bonds | e.1 ≠ y ∧ e.2 ≠ y}
'AKLT.W.REC091.remove_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.removalSiteEquiv {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) : Option ↥(AKLT.Defs.removeSite D y).active ≃ ↥D.active
AKLT.W.REC091.insertSpin {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  ↥D.active → AKLT.Defs.SpinLetter
AKLT.W.REC091.removalConfigEquiv {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) :
  (↥D.active → AKLT.Defs.SpinLetter) ≃
    AKLT.Defs.SpinLetter × (↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)
AKLT.W.REC091.removalConfigEquiv_symm {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  (AKLT.W.REC091.removalConfigEquiv D y hy).symm (j, m) = AKLT.W.REC091.insertSpin D y hy j m
'AKLT.W.REC091.removalConfigEquiv_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.insertSpin_y {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  AKLT.W.REC091.insertSpin D y hy j m ⟨y, hy⟩ = j
'AKLT.W.REC091.insertSpin_y' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.insertSpin_ne {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)
  (x : ↥D.active) (hx : ↑x ≠ y) : AKLT.W.REC091.insertSpin D y hy j m x = m ⟨↑x, ⋯⟩
'AKLT.W.REC091.insertSpin_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.spins_insert_y {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  D.spins (AKLT.W.REC091.insertSpin D y hy j m) y = AKLT.Defs.spinVector j
'AKLT.W.REC091.spins_insert_y' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.spins_insert_ne {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)
  {x : AKLT.Defs.Plane} (hx : x ≠ y) :
  D.spins (AKLT.W.REC091.insertSpin D y hy j m) x = (AKLT.Defs.removeSite D y).spins m x
'AKLT.W.REC091.spins_insert_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.siteWeights_insert {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (m : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  ∏ x, AKLT.Defs.spinWeight (D.status ↑x) (AKLT.W.REC091.insertSpin D y hy j m x) =
    AKLT.Defs.spinWeight (D.status y) j * ∏ x, AKLT.Defs.spinWeight ((AKLT.Defs.removeSite D y).status ↑x) (m x)
'AKLT.W.REC091.siteWeights_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.normSq_nonneg (v : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq v
'AKLT.W.REC091.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.dot_comm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC091.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.normSq_add (a b : AKLT.Defs.Vec3) :
  AKLT.Defs.normSq (a + b) = AKLT.Defs.normSq a + 2 * AKLT.Defs.dot a b + AKLT.Defs.normSq b
'AKLT.W.REC091.normSq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.normSq_sub (a b : AKLT.Defs.Vec3) :
  AKLT.Defs.normSq (a - b) = AKLT.Defs.normSq a - 2 * AKLT.Defs.dot a b + AKLT.Defs.normSq b
'AKLT.W.REC091.normSq_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.dot_bounds {a b : AKLT.Defs.Vec3} (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  -1 ≤ AKLT.Defs.dot a b ∧ AKLT.Defs.dot a b ≤ 1
'AKLT.W.REC091.dot_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.eq_neg_of_dot_eq_neg_one {a b : AKLT.Defs.Vec3} (ha : AKLT.Defs.normSq a ≤ 1)
  (hb : AKLT.Defs.normSq b ≤ 1) (h : AKLT.Defs.dot a b = -1) : a = -b
'AKLT.W.REC091.eq_neg_of_dot_eq_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.goldenRatio_pos : 0 < AKLT.Defs.goldenRatio
'AKLT.W.REC091.goldenRatio_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.goldenRatio_gt_one : 1 < AKLT.Defs.goldenRatio
'AKLT.W.REC091.goldenRatio_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.goldenRatio_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC091.goldenRatio_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.icoRadius_pos : 0 < AKLT.Defs.icoRadius
'AKLT.W.REC091.icoRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.icoRadius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
'AKLT.W.REC091.icoRadius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC091.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.spin_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC091.spin_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.spinWeight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
'AKLT.W.REC091.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.spinWeight_some_pos {s : AKLT.Defs.Status} (hs : s ≠ AKLT.Defs.Status.X) (j : AKLT.Defs.IcoLetter) :
  0 < AKLT.Defs.spinWeight s (some j)
'AKLT.W.REC091.spinWeight_some_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.hemisphereLetter (j : Fin 3 × Fin 2) : AKLT.Defs.IcoLetter
AKLT.W.REC091.coordinateSum (v : AKLT.Defs.Vec3) : ℝ
AKLT.W.REC091.hemisphere_positive (j : Fin 3 × Fin 2) :
  0 < AKLT.W.REC091.coordinateSum (AKLT.Defs.icoVector (AKLT.W.REC091.hemisphereLetter j))
'AKLT.W.REC091.hemisphere_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.hemisphere_injective : Function.Injective (AKLT.Defs.icoVector ∘ AKLT.W.REC091.hemisphereLetter)
'AKLT.W.REC091.hemisphere_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC091.hemisphere_bond_pos (i j : Fin 3 × Fin 2) :
  0 <
    1 +
      AKLT.Defs.dot (AKLT.Defs.icoVector (AKLT.W.REC091.hemisphereLetter i))
        (AKLT.Defs.icoVector (AKLT.W.REC091.hemisphereLetter j))
'AKLT.W.REC091.hemisphere_bond_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
WALL_SECONDS=3.90
```

## ORCH-SUMMARY

- STATUS: PARTIAL; the exact closed `AKLT.W.REC091.main` remains open.
- Main.lean and nine helper/audit files are delivered and compile.
- Proved both frozen TwoFactorizationStatement and ThreeFactorizationStatement.
- Proved stepRatio = 1/I₂ and stepRatio = J/I with canonical definitions.
- Proved positivity of every Network partition and positivity of canonical J.
- Closed earlier Residual_StepFactorizations and Residual_RemovedPartitionPositive.
- `main_of_sharedCoverMixture` now needs only Residual_SharedCoverMixture.
- Independent open construction: `AKLT.W.REC091.Residual_SharedCoverMixture`.
- Weaker sufficient open residual: `AKLT.W.REC091.Residual_PartitionLower`.
- The missing work is shared-cover finite local reconstruction with common weights.
- localThreshold, straight/turn Boolean, I, I₂, J, and frozen files are unchanged.
- All 79 exported theorems have only allowed axioms; full output is above.
- Orchestrator must supply/prove the remaining shared mixture or partition inequality.
- Once either is proved, the corresponding conditional theorem gives the exact target.
