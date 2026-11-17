STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC013/AKLT/W/REC013/Main.lean): Required theorem and the partition equality for a D departure.
- [SpinFacts.lean](/home/ubuntu/aklt/wt/LW_REC013/AKLT/W/REC013/SpinFacts.lean): Unit-vector algebra, six compatible atoms, and the one-bond D integral.
- [Positive.lean](/home/ubuntu/aklt/wt/LW_REC013/AKLT/W/REC013/Positive.lean): Strict positivity of every auxiliary network partition.
- [NetworkFacts.lean](/home/ubuntu/aklt/wt/LW_REC013/AKLT/W/REC013/NetworkFacts.lean): Original-leg geometry and the bond set after removal or tracing.
- [Split.lean](/home/ubuntu/aklt/wt/LW_REC013/AKLT/W/REC013/Split.lean): Explicit equivalences and finite sums/products splitting off one site.
- [Eliminate.lean](/home/ubuntu/aklt/wt/LW_REC013/AKLT/W/REC013/Eliminate.lean): Equality of the original, removed-site, and D-traced partitions.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC013/AKLT/W/REC013/Audit.lean): Exact-type example plus types and axiom audits of all 44 exported declarations.

Only files in `AKLT/W/REC013/` were written in the worktree. The prior report remains in `report.luna.md`.

## Required export

```lean
theorem AKLT.W.REC013.main : AKLT.Blueprint.Rec.DStepTrivialStatement
```

The closed statement is proved without any additional hypotheses. Its conclusion is:

```lean
∀ a : AKLT.Blueprint.Rec.Departure, a.D.status a.y = .D →
  AKLT.Defs.stepRatio a.D a.τ true a.y a.o = 1 ∧
  AKLT.Defs.stepRatio a.D a.τ false a.y a.o = 1
```

Two supporting exports close the earlier attempt's mathematical gaps:

```lean
AKLT.W.REC013.partition_positive
  {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
  (hD : D.Auxiliary) (b : Bool) :
  0 < D.partition τ b (fun _ => 1)

AKLT.W.REC013.d_step_partition
  (a : AKLT.Blueprint.Rec.Departure) (hD : a.D.status a.y = .D) (b : Bool) :
  (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
    a.D.partition a.τ b (fun _ => 1)
```

The exact types of every supporting theorem and definition, together with each axiom audit, are reproduced below and in [declarations-and-axioms.log](/home/ubuntu/aklt/reports/LW/REC013/declarations-and-axioms.log).

## Proof

The admissible-start premise and the selected outgoing neighbour make the D site's present-neighbour set a singleton. Every original leg originates in the protected layer, so none originates at the departure site. The proof explicitly splits configurations into the departure spin and the remaining active spins, and splits the site-weight and bond products. The sole departure factor has sum

```lean
∑ j : SpinLetter, spinWeight .D j * (1 + dot (spinVector j) v) = 1.
```

Deleting the D departure therefore leaves both partitions unchanged. Tracing has the same active sites and bonds as deleting the site; the extra erased half-edge at the outgoing endpoint has no further effect.

For the positive denominator, every partition summand is nonnegative by the unit-ball scalar-product bound. Six explicit icosahedron atoms have no antipodal pairs, so every interaction between chosen atoms is strictly positive. A unit pin can annihilate at most one of these six atoms. At most four original pins occur at any active site, so one can choose an atom at each site avoiding all its pins. This supplies a strictly positive summand. The quotient is then exactly one for each Boolean pin choice.

This uses a direct reindexing of active-site subtypes and a six-atom positivity witness. It does not require reindexing through `FiniteSpinNetwork` or using other blueprint leaves as lemmas. No residual propositions remain.

## Validation

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC013.Main` succeeded. During the successful proof compilation Lake reported 17 s for `Eliminate` and 9.5 s for `Main`; helper modules had been compiled during development.
- The final recorded incremental build used the same command under `/usr/bin/time -p`; [build.log](/home/ubuntu/aklt/reports/LW/REC013/build.log) and [build.time](/home/ubuntu/aklt/reports/LW/REC013/build.time) record:

```text
real 11.85
user 7.15
sys 1.79
```

- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC013/Audit.lean` succeeded. It checks the exact requested type with an `example` and prints all 44 exported declaration types and axiom sets. Timings:

```text
real 11.16
user 5.15
sys 2.42
```

- `#print axioms AKLT.W.REC013.main` reports:

```text
'AKLT.W.REC013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Every audited declaration uses only the allowed axioms. The source scan found none of the forbidden proof constructs.
- No open mathematical issues. The build emits only benign linter and deprecated tactic-name warnings.

## Exported declarations and axiom output

```text
AKLT.W.REC013.golden_pos : 0 < AKLT.Defs.goldenRatio
'AKLT.W.REC013.golden_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.golden_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC013.golden_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.radius_pos : 0 < AKLT.Defs.icoRadius
'AKLT.W.REC013.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.radius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
'AKLT.W.REC013.radius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC013.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.spin_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC013.spin_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.dot_comm (v w : AKLT.Defs.Vec3) : AKLT.Defs.dot v w = AKLT.Defs.dot w v
'AKLT.W.REC013.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.factor_nonneg (v w : AKLT.Defs.Vec3) (hv : AKLT.Defs.normSq v ≤ 1) (hw : AKLT.Defs.normSq w ≤ 1) :
  0 ≤ 1 + AKLT.Defs.dot v w
'AKLT.W.REC013.factor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.factor_zero (v w : AKLT.Defs.Vec3) (hv : AKLT.Defs.normSq v = 1) (hw : AKLT.Defs.normSq w = 1)
  (h : 1 + AKLT.Defs.dot v w = 0) : v = -w
'AKLT.W.REC013.factor_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.candidate (j : Fin 3 × Fin 2) : AKLT.Defs.IcoLetter
'AKLT.W.REC013.candidate' depends on axioms: [propext]
AKLT.W.REC013.candidate_injective : Function.Injective fun j => AKLT.Defs.icoVector (AKLT.W.REC013.candidate j)
'AKLT.W.REC013.candidate_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.candidate_not_antipodal (a b : Fin 3 × Fin 2) :
  AKLT.Defs.icoVector (AKLT.W.REC013.candidate a) ≠ -AKLT.Defs.icoVector (AKLT.W.REC013.candidate b)
'AKLT.W.REC013.candidate_not_antipodal' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.candidate_factor_pos (a b : Fin 3 × Fin 2) :
  0 <
    1 +
      AKLT.Defs.dot (AKLT.Defs.icoVector (AKLT.W.REC013.candidate a)) (AKLT.Defs.icoVector (AKLT.W.REC013.candidate b))
'AKLT.W.REC013.candidate_factor_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.d_integral_one (v : AKLT.Defs.Vec3) :
  ∑ j, AKLT.Defs.spinWeight AKLT.Defs.Status.D j * (1 + AKLT.Defs.dot (AKLT.Defs.spinVector j) v) = 1
'AKLT.W.REC013.d_integral_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.adjacent_symm {x y : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x y) : AKLT.Defs.Adjacent y x
'AKLT.W.REC013.adjacent_symm' depends on axioms: [propext]
AKLT.W.REC013.present_symm {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x y : AKLT.Defs.Plane}
  (h : D.Present x y) : D.Present y x
'AKLT.W.REC013.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.positive_neighbour_facts {x z : AKLT.Defs.Plane} (h : z ∈ AKLT.Defs.positiveNeighbours x) :
  x ≠ z ∧ z ∈ AKLT.Defs.neighbours x ∧ x ∈ AKLT.Defs.neighbours z
'AKLT.W.REC013.positive_neighbour_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.bond_facts {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {e : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (he : e ∈ D.bonds) : e.1 ≠ e.2 ∧ e.2 ∈ D.presentNeighbours e.1 ∧ e.1 ∈ D.presentNeighbours e.2
'AKLT.W.REC013.bond_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.bond_order {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {e : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (he : e ∈ D.bonds) : e.1.1 + e.1.2 < e.2.1 + e.2.2
'AKLT.W.REC013.bond_order' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.exists_selected_bond {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y o : AKLT.Defs.Plane}
  (ho : o ∈ D.presentNeighbours y) : ∃ e ∈ D.bonds, e = (y, o) ∨ e = (o, y)
'AKLT.W.REC013.exists_selected_bond' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.remove_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y x : AKLT.Defs.Plane) :
  x ∈ (AKLT.Defs.removeSite D y).active ↔ x ∈ D.active ∧ x ≠ y
'AKLT.W.REC013.remove_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.trace_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.D) : x ∈ (AKLT.Defs.traceStep D y o).active ↔ x ∈ D.active ∧ x ≠ y
'AKLT.W.REC013.trace_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.remove_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : e ∈ (AKLT.Defs.removeSite D y).bonds ↔ e ∈ D.bonds ∧ e.1 ≠ y ∧ e.2 ≠ y
'AKLT.W.REC013.remove_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.trace_remove_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.D) : (AKLT.Defs.traceStep D y o).bonds = (AKLT.Defs.removeSite D y).bonds
'AKLT.W.REC013.trace_remove_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.remove_bonds_erase {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y o : AKLT.Defs.Plane}
  (hs : D.presentNeighbours y = {o}) {e : AKLT.Defs.Plane × AKLT.Defs.Plane} (he : e ∈ D.bonds)
  (hed : e = (y, o) ∨ e = (o, y)) : (AKLT.Defs.removeSite D y).bonds = D.bonds.erase e
'AKLT.W.REC013.remove_bonds_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.leg_origin_protected {G : Finset AKLT.Defs.Plane} (e : ↥(AKLT.Defs.originalLegs G)) :
  (↑e).1 ∈ AKLT.Defs.protectedSites G
'AKLT.W.REC013.leg_origin_protected' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.candidate_avoids.{u_1} {ι : Type u_1} [Fintype ι] (hc : Fintype.card ι ≤ 4)
  (pin : ι → AKLT.Defs.UnitVector) :
  ∃ a, ∀ (i : ι), 0 < 1 + AKLT.Defs.dot (AKLT.Defs.icoVector (AKLT.W.REC013.candidate a)) ↑(pin i)
'AKLT.W.REC013.candidate_avoids' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.spinWeight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
'AKLT.W.REC013.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.spinWeight_some_pos (s : AKLT.Defs.Status) (hs : s ≠ AKLT.Defs.Status.X) (j : AKLT.Defs.IcoLetter) :
  0 < AKLT.Defs.spinWeight s (some j)
'AKLT.W.REC013.spinWeight_some_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.network_spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins n x) ≤ 1
'AKLT.W.REC013.network_spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.partition_positive {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (hD : D.Auxiliary) (b : Bool) : 0 < D.partition τ b fun x => 1
'AKLT.W.REC013.partition_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.joinSpin {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (j : AKLT.Defs.SpinLetter) (n : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  ↥D.active → AKLT.Defs.SpinLetter
'AKLT.W.REC013.joinSpin' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.splitSpin {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) :
  (↥D.active → AKLT.Defs.SpinLetter) ≃
    AKLT.Defs.SpinLetter × (↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)
'AKLT.W.REC013.splitSpin' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.siteEquiv {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) : Option ↥(AKLT.Defs.removeSite D y).active ≃ ↥D.active
'AKLT.W.REC013.siteEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.sum_split {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) (hy : y ∈ D.active)
  (F : (↥D.active → AKLT.Defs.SpinLetter) → ℝ) : ∑ m, F m = ∑ n, ∑ j, F (AKLT.W.REC013.joinSpin D y j n)
'AKLT.W.REC013.sum_split' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.join_weight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (n : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  ∏ x, AKLT.Defs.spinWeight (D.status ↑x) (AKLT.W.REC013.joinSpin D y j n x) =
    AKLT.Defs.spinWeight (D.status y) j * ∏ x, AKLT.Defs.spinWeight ((AKLT.Defs.removeSite D y).status ↑x) (n x)
'AKLT.W.REC013.join_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.join_spins_y {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (j : AKLT.Defs.SpinLetter) (n : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  D.spins (AKLT.W.REC013.joinSpin D y j n) y = AKLT.Defs.spinVector j
'AKLT.W.REC013.join_spins_y' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.join_spins_ne {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (j : AKLT.Defs.SpinLetter) (n : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) {x : AKLT.Defs.Plane}
  (hx : x ≠ y) : D.spins (AKLT.W.REC013.joinSpin D y j n) x = (AKLT.Defs.removeSite D y).spins n x
'AKLT.W.REC013.join_spins_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.trace_partition_eq_remove {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (y o : AKLT.Defs.Plane) (hy : D.status y = AKLT.Defs.Status.D) :
  ((AKLT.Defs.traceStep D y o).partition τ b fun x => 1) = (AKLT.Defs.removeSite D y).partition τ b fun x => 1
'AKLT.W.REC013.trace_partition_eq_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.join_legs {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hn : y ∉ AKLT.Defs.protectedSites G) (j : AKLT.Defs.SpinLetter)
  (n : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  (∏ e,
      if b = true ∧ (↑e).1 ∈ D.active then 1 + AKLT.Defs.dot (↑(τ e)) (D.spins (AKLT.W.REC013.joinSpin D y j n) (↑e).1)
      else 1) =
    ∏ e,
      if b = true ∧ (↑e).1 ∈ (AKLT.Defs.removeSite D y).active then
        1 + AKLT.Defs.dot (↑(τ e)) ((AKLT.Defs.removeSite D y).spins n (↑e).1)
      else 1
'AKLT.W.REC013.join_legs' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.join_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (hs : D.presentNeighbours y = {o}) (j : AKLT.Defs.SpinLetter)
  (n : ↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter) :
  ∏ t ∈ D.bonds,
      (1 +
        AKLT.Defs.dot (D.spins (AKLT.W.REC013.joinSpin D y j n) t.1) (D.spins (AKLT.W.REC013.joinSpin D y j n) t.2)) =
    (1 + AKLT.Defs.dot (AKLT.Defs.spinVector j) ((AKLT.Defs.removeSite D y).spins n o)) *
      ∏ t ∈ (AKLT.Defs.removeSite D y).bonds,
        (1 + AKLT.Defs.dot ((AKLT.Defs.removeSite D y).spins n t.1) ((AKLT.Defs.removeSite D y).spins n t.2))
'AKLT.W.REC013.join_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.d_partition_eq_remove {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (y o : AKLT.Defs.Plane) (hy : y ∈ D.active)
  (hn : y ∉ AKLT.Defs.protectedSites G) (hD : D.status y = AKLT.Defs.Status.D) (hs : D.presentNeighbours y = {o}) :
  (D.partition τ b fun x => 1) = (AKLT.Defs.removeSite D y).partition τ b fun x => 1
'AKLT.W.REC013.d_partition_eq_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.d_step_partition (a : AKLT.Blueprint.Rec.Departure) (hD : a.D.status a.y = AKLT.Defs.Status.D)
  (b : Bool) : ((AKLT.Defs.traceStep a.D a.y a.o).partition a.τ b fun x => 1) = a.D.partition a.τ b fun x => 1
'AKLT.W.REC013.d_step_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC013.main : AKLT.Blueprint.Rec.DStepTrivialStatement
'AKLT.W.REC013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- Delivered `AKLT/W/REC013/Main.lean` with the exact closed theorem `AKLT.W.REC013.main`.
- Type: `AKLT.Blueprint.Rec.DStepTrivialStatement`.
- Proved both partition equality and denominator positivity directly.
- Added six helper/audit modules, all within the assigned directory.
- Main build and independent exact-type/axiom audit pass.
- All 44 exported declaration axiom sets are subsets of `[propext, Classical.choice, Quot.sound]`.
- No residual statements, unproved dependencies, or open obligations.
- Route adaptation: direct active-site splitting and six-atom positivity replace the suggested common-network reindexing.
- Only benign linter/deprecation warnings remain; no mathematical limitations.
- No existing files outside the assigned directory were changed.
- Orchestrator action: accept the leaf; no further decision or dependency is needed.
