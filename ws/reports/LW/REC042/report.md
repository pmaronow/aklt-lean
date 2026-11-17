STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC042/AKLT/W/REC042/Main.lean): the requested closed theorem and a stronger coordinate-step lemma.
- [Site.lean](/home/ubuntu/aklt/wt/LW_REC042/AKLT/W/REC042/Site.lean): the U and D finite-neighbour coordinate moment identities, including empty neighbour sets.
- [Integration.lean](/home/ubuntu/aklt/wt/LW_REC042/AKLT/W/REC042/Integration.lean): site integration with an observable, trace partition comparisons, and partition linearity.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC042/AKLT/W/REC042/Audit.lean): exact-type check and axiom checks for every exported theorem.
- [build.log](/home/ubuntu/aklt/reports/LW/REC042/build.log) and [audit.log](/home/ubuntu/aklt/reports/LW/REC042/audit.log): successful validation output.

The earlier conditional `main` has been replaced. Its residual propositions are no longer present. The unused earlier `Moments.lean` was replaced by `Site.lean`, which reuses the indexed moment proofs.

## Proof and dependencies

The proof first isolates the moving coordinate in the unnormalized partition. The complement retains every original leg and all nonincident bonds. The U identity follows from the second and fourth coordinate moments, reducing a finite neighbour set of cardinality at most three to its four possible cardinalities. A U departure changes its law to D and deletes the selected bond. For a D departure with at most one bond, the second-moment identity removes the departure site without an extra scalar mass. Finite partition linearity then gives the required sum over outgoing neighbours.

Reused proved helpers belong to indexed leaves:

- `AKLT.W.MOM019.Main` (`AKLT.Blueprint.Mom.TripleNumeratorStatement`): coordinate moment expansions through degree four.
- `AKLT.W.REC002.Main` (`AKLT.Blueprint.Rec.ThreeFactorizationStatement`), via its `Moments`, `Integration`, and `Trace` helpers: site-law formulas, partition linearity, and trace complement facts.
- `AKLT.W.REC003.Main` (`AKLT.Blueprint.Rec.TwoFactorizationStatement`), via its `Moments`, `Integration`, and `Trace` helpers: finite site Fubini, interaction factorization, and U-trace neighbour deletion.

No unproved blueprint leaf is used. `coordinate_step` proves a stronger result using only the departure restrictions and distinct marked sites; specializing it gives the exact frozen statement. The target degree and auxiliary hypotheses remain in the required theorem's type.

## Exported declarations and their statements

Actual output from `Audit.lean`:

```text
AKLT.W.REC042.main : AKLT.Blueprint.Rec.CoordinateStepStatement
AKLT.W.REC042.siteU_coordinate_one (a : AKLT.Defs.Vec3) (k : Fin 3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun n => n k * (1 + AKLT.Defs.dot n a)) = a k / 3
AKLT.W.REC042.siteU_coordinate_two (a b : AKLT.Defs.Vec3) (k : Fin 3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun n => n k * ((1 + AKLT.Defs.dot n a) * (1 + AKLT.Defs.dot n b))) =
    (a k + b k) / 3
AKLT.W.REC042.siteU_coordinate_three (a b c : AKLT.Defs.Vec3) (k : Fin 3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun n =>
      n k * ((1 + AKLT.Defs.dot n a) * ((1 + AKLT.Defs.dot n b) * (1 + AKLT.Defs.dot n c)))) =
    (a k + b k + c k) / 3 + (a k * AKLT.Defs.dot b c + b k * AKLT.Defs.dot a c + c k * AKLT.Defs.dot a b) / 15
AKLT.W.REC042.siteU_coordinate_finset.{u_1} {α : Type u_1} [DecidableEq α] (s : Finset α) (hs : s.card ≤ 3)
  (m : α → AKLT.Defs.Vec3) (k : Fin 3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun n => n k * ∏ x ∈ s, (1 + AKLT.Defs.dot n (m x))) =
    1 / 3 *
      ∑ o ∈ s, m o k * AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun n => ∏ x ∈ s.erase o, (1 + AKLT.Defs.dot n (m x))
AKLT.W.REC042.siteD_coordinate_one (a : AKLT.Defs.Vec3) (k : Fin 3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun n => n k * (1 + AKLT.Defs.dot n a)) = a k / 5
AKLT.W.REC042.siteD_coordinate_finset.{u_1} {α : Type u_1} [DecidableEq α] (s : Finset α) (hs : s.card ≤ 1)
  (m : α → AKLT.Defs.Vec3) (k : Fin 3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun n => n k * ∏ x ∈ s, (1 + AKLT.Defs.dot n (m x))) =
    1 / 5 * ∑ o ∈ s, m o k
AKLT.W.REC042.partition_site {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∈ D.active) (hyS : y ∉ AKLT.Defs.protectedSites G) (g : AKLT.Defs.Vec3 → ℝ)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ)
  (hf : ∀ (m : AKLT.Defs.Plane → AKLT.Defs.Vec3) (n : AKLT.Defs.Vec3), f (Function.update m y n) = f m) :
  (D.partition τ b fun m => g (m y) * f m) =
    (AKLT.Defs.removeSite D y).partition τ b fun m =>
      (AKLT.Defs.siteFunctional (D.status y) fun n => g n * ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot n (m z))) *
        f m
AKLT.W.REC042.remove_trace_partition_all {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).partition τ b f = (AKLT.Defs.removeSite D y).partition τ b f
AKLT.W.REC042.trace_partition_removed {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y ≠ AKLT.Defs.Status.U) (τ : AKLT.Defs.PinAssignment G) (b : Bool)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (AKLT.Defs.traceStep D y o).partition τ b f = (AKLT.Defs.removeSite D y).partition τ b f
AKLT.W.REC042.partition_coordinate {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (u v : AKLT.Defs.Plane) (hu : u ∈ D.active)
  (huS : u ∉ AKLT.Defs.protectedSites G) (huv : u ≠ v) (k : Fin 3) :
  (D.partition τ b fun m => m u k * m v k) =
    (AKLT.Defs.removeSite D u).partition τ b fun m =>
      (AKLT.Defs.siteFunctional (D.status u) fun n => n k * ∏ z ∈ D.presentNeighbours u, (1 + AKLT.Defs.dot n (m z))) *
        m v k
AKLT.W.REC042.trace_partition_U {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (u v o : AKLT.Defs.Plane) (hu : u ∈ D.active) (huS : u ∉ AKLT.Defs.protectedSites G)
  (hU : D.status u = AKLT.Defs.Status.U) (huv : u ≠ v) (ho : o ∈ D.presentNeighbours u) (k : Fin 3) :
  ((AKLT.Defs.traceStep D u o).partition τ b fun m => m o k * m v k) =
    (AKLT.Defs.removeSite D u).partition τ b fun m =>
      (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun n =>
          ∏ z ∈ (D.presentNeighbours u).erase o, (1 + AKLT.Defs.dot n (m z))) *
        (m o k * m v k)
AKLT.W.REC042.partition_finset_sum.{u_1} {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) {α : Type u_1} (s : Finset α)
  (f : α → (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun m => ∑ x ∈ s, f x m) = ∑ x ∈ s, D.partition τ b (f x)
AKLT.W.REC042.coordinate_step {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (u v : AKLT.Defs.Plane) (hu : u ∈ D.active) (huS : u ∉ AKLT.Defs.protectedSites G)
  (hstatus :
    D.status u = AKLT.Defs.Status.U ∧ (D.presentNeighbours u).card ≤ 3 ∨
      D.status u = AKLT.Defs.Status.D ∧ (D.presentNeighbours u).card ≤ 1)
  (huv : u ≠ v) (k : Fin 3) :
  (D.partition τ b fun m => m u k * m v k) =
    (if D.status u = AKLT.Defs.Status.U then 1 / 3 else 1 / 5) *
      ∑ o ∈ D.presentNeighbours u, (AKLT.Defs.traceStep D u o).partition τ b fun m => m o k * m v k
```

## Axiom audit

Every exported theorem uses only the permitted axioms. Actual `#print axioms` output:

```text
'AKLT.W.REC042.siteU_coordinate_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.siteU_coordinate_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.siteU_coordinate_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.siteU_coordinate_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.siteD_coordinate_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.siteD_coordinate_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.partition_site' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.remove_trace_partition_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.trace_partition_removed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.partition_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.trace_partition_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.partition_finset_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.coordinate_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build commands and timings

With `$HOME/.elan/bin` on `PATH`:

- `lake build AKLT.W.REC042.Main`: succeeded without warnings; 14.31 seconds wall time (final Main compilation: 7.6 seconds).
- `lake env lean AKLT/W/REC042/Audit.lean`: succeeded; 3.57 seconds wall time. The first check explicitly ascribes `AKLT.W.REC042.main` to `AKLT.Blueprint.Rec.CoordinateStepStatement`.
- Scanned the delivered Lean files for forbidden proof escapes; none found.

Only files under `AKLT/W/REC042/` and the assigned report directory were written. No statement-layer or other existing project files were changed.

## Open issues

None. The requested theorem is closed and has no residual hypotheses.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC042.main : AKLT.Blueprint.Rec.CoordinateStepStatement`.
- Status: PROVED FROM DEPS, using indexed MOM019, REC002, and REC003 proof helpers.
- Added reusable finite-neighbour moment and site-integration lemmas.
- Replaced the earlier conditional proof and removed its unused moment helper.
- Exact type checked by `Audit.lean`.
- All 14 exported theorems have only propext, Classical.choice, and Quot.sound.
- Required module build and audit both pass.
- Open obligations: none.
- Limitations or semantic deviations: none; the stronger local lemma uses fewer hypotheses.
- Orchestrator can accept REC042 and add its main theorem to the proved index.
