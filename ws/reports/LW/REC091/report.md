STATUS: PROVED FROM DEPS

## Files

| File | Contents |
| --- | --- |
| [Main.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Main.lean) | Exact target theorem, H1 mixture comparison, and integration/cancellation assembly. |
| [Factorizations.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Factorizations.lean) | Two- and three-neighbour integration factorizations and step-ratio identities. |
| [Departure.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Departure.lean) | Unpinned departure disintegration and equality of the removed pre/post-step networks. |
| [OneSite.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/OneSite.lean) | Finite-sum integration at one active site, preserving original pins. |
| [Remove.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Remove.lean) | Removal/configuration equivalences and site-weight identities. |
| [Graph.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Graph.lean) | Present-bond geometry and incident-bond indexing. |
| [Integrals.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Integrals.lean) | Exact U/D site-functional evaluations. |
| [Positive.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Positive.lean) | Network partition positivity, removed-pair bounds, and positive canonical J. |
| [Spin.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Spin.lean) | Icosahedron spin bounds and the positive-hemisphere construction. |
| [Audit.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Audit.lean) | Type checks for all 91 named declarations and axiom checks for all 80 named theorems. |

The existing REC091 integration and positivity proofs were reused. This attempt adds the REC089 import and the closed target theorem in Main.lean, updates the audit, and writes this report. All proof-source changes are confined to `AKLT/W/REC091/`.

## Exported declaration and dependency

[Main.lean:128](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Main.lean:128) exports exactly:

```lean
theorem AKLT.W.REC091.main :
    AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2 :=
  AKLT.W.REC091.main_of_sharedCoverMixture AKLT.W.REC089.main
```

The sole imported blueprint leaf used directly is the indexed, proved theorem:

```lean
AKLT.W.REC089.main : AKLT.Blueprint.Rec.LocalMixtureStatementV2
```

It supplies one nonnegative covered-pattern mixture for both pinned partition functions. Applying H1 term by term gives `c * Z_after ≤ Z_before`. The local integration proofs give `Z_before = Z_removed * I₂`, `Z_after = Z_removed` in the two-neighbour case, and `Z_before = Z_removed * I`, `Z_after = Z_removed * J` in the three-neighbour case. Cancelling the proved positive `Z_removed` yields both required inequalities.

The proof uses the frozen `localThreshold (decide (outgoing = incoming))` and the canonical `responseI₂`, `responseI`, and `responseJ`. It establishes the lower bound directly in multiplication form. `responseJ_pos` is also proved in the reused helpers.

The complete elaborated statements of all 91 named declarations, including every supporting theorem and the retained transparent interface definitions, appear in the audit appendix below. All earlier residual interfaces are discharged in `main`; none is a premise of the delivered theorem.

## Axiom audit

```text
'AKLT.W.REC091.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The audit checks all 80 named theorems in this directory. Every dependency list is a subset of the three allowed axioms; no unexpected axiom occurs. A source scan found none of the prohibited proof constructs.

## Build commands and timings

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC091.Main` — passed; 9.149 s command wall time, 3.8 s reported for compiling Main.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC091/Audit.lean` — passed; 4.417 s wall time. The exact target type checks, and all 80 axiom dependency checks pass.
- The initial dependency/build driver took 501.441 s. Thirty supplied dependency modules lacked local OLeans and were built as individual module targets before the requested target. At most two Lean processes ran concurrently. Mathlib and package sources were unchanged.

Full evidence: [build.log](/home/ubuntu/aklt/reports/LW/REC091/build.log), [build-times.tsv](/home/ubuntu/aklt/reports/LW/REC091/build-times.tsv), [independent-build.log](/home/ubuntu/aklt/reports/LW/REC091/independent-build.log), [independent-build-times.tsv](/home/ubuntu/aklt/reports/LW/REC091/independent-build-times.tsv), and [audit.log](/home/ubuntu/aklt/reports/LW/REC091/audit.log).

## Open issues

None. The only mathematical input retained by the target is its specified H1 hypothesis. No statement-layer definitions were modified, and no additional premise was added.

## Complete exported declarations and axiom output

The following is the successful output of `lake env lean AKLT/W/REC091/Audit.lean`:

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
AKLT.W.REC091.main : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2
'AKLT.W.REC091.main' depends on axioms: [propext, Classical.choice, Quot.sound]
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
```

## ORCH-SUMMARY

- Delivered `AKLT.W.REC091.main : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2`.
- Status: PROVED FROM DEPS; direct indexed dependency is `AKLT.W.REC089.main`.
- Reused and verified all existing REC091 integration, factorization, and positivity proofs.
- Both required inequalities use the original threshold Boolean and canonical I₂/I/J.
- Exact requested Lake target and full declaration/axiom audit pass.
- All 80 named theorem axiom lists use only propext, Classical.choice, and Quot.sound.
- Open exact residuals: none.
- Limitations/deviations: none affecting the statement; proof uses the multiplication form of the partition comparison.
- Orchestrator action: accept/register REC091; no further proof or decision is needed.
