STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC014/AKLT/W/REC014/Main.lean): requested unconditional theorem.
- [Basic.lean](/home/ubuntu/aklt/wt/LW_REC014/AKLT/W/REC014/Basic.lean): finite spin normalization, first moment, unit atoms, and a six-atom positive support.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC014/AKLT/W/REC014/Geometry.lean): original-leg bounds and the unique orientation of a present bond.
- [Sum.lean](/home/ubuntu/aklt/wt/LW_REC014/AKLT/W/REC014/Sum.lean): explicit one-coordinate finite-sum decomposition and integration.
- [Positive.lean](/home/ubuntu/aklt/wt/LW_REC014/AKLT/W/REC014/Positive.lean): strict positivity of each concrete network partition.
- [Trace.lean](/home/ubuntu/aklt/wt/LW_REC014/AKLT/W/REC014/Trace.lean): active-set preservation and removal of the sole outgoing bond.
- [Integral.lean](/home/ubuntu/aklt/wt/LW_REC014/AKLT/W/REC014/Integral.lean): equality of the pre-step and post-step partitions.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC014/AKLT/W/REC014/Audit.lean): exact-type check and signatures/axiom audits of every exported declaration.

Only files under `AKLT/W/REC014/` were written in the worktree. The previous partial `Main.lean` was replaced. No frozen statement or existing library file was changed.

## Exported declarations

The requested theorem has exactly this name and type:

```lean
theorem AKLT.W.REC014.main : AKLT.Blueprint.Rec.OneStepTrivialStatement
```

Its expanded conclusion is

```lean
∀ a : AKLT.Blueprint.Rec.Departure,
  a.D.status a.y = .U → (a.D.presentNeighbours a.y).card = 1 →
  AKLT.Defs.stepRatio a.D a.τ true a.y a.o = 1 ∧
  AKLT.Defs.stepRatio a.D a.τ false a.y a.o = 1
```

The main supporting results are `partition_collapse`, equality of the partitions for either pin choice under the leaf hypotheses, and `partition_positive`, strict positivity for every `Network G`, pin assignment, and Boolean pin choice. The complete exact signatures of all 52 exported declarations, together with their axiom audits, appear below.

## Proof

Every original leg starts in the protected layer. Since an admissible departure lies outside that layer, no original pin factor involves its spin. Its sole present neighbour is the outgoing endpoint. Trace preserves the active set, changes the departure from U to D, and removes exactly that single bond.

`Equiv.funSplitAt` splits the finite assignment sum into the departure coordinate and the other coordinates. All remaining bond and pin factors are constant on each resulting fibre. Direct finite summation gives the U law total mass one and zero first moment, hence its single-bond integral is one. The isolated D law also has total mass one. Therefore the pre-step and post-step partitions agree for both pin choices.

For positivity, use the six explicit labels `(j.1, 0, j.2)` indexed by `Fin 3 × Fin 2`. Their vectors are distinct, unit, and contain no antipodal pair. Squared-norm identities prove nonnegativity of every interaction factor. A unit pin can forbid at most one of these six vectors, and a site has at most four original legs. Choose a permitted vector at each active site. This configuration has strictly positive site, bond, and pin factors; all other summands are nonnegative. Thus the partition is strictly positive, including for an empty active set. Cancelling the common positive partition gives both ratios equal to one.

This proof works directly on the actual finite active-site subtype. It does not assume any other blueprint leaf and has no residual propositions or extra hypotheses.

## Build and validation

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC014.Main`: passed, 75.62 s wall time for the final rebuild of the seven proof modules; no warnings. Full output: [build.log](/home/ubuntu/aklt/reports/LW/REC014/build.log).
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC014/Audit.lean`: passed, 9.66 s wall time. This checks `(AKLT.W.REC014.main : AKLT.Blueprint.Rec.OneStepTrivialStatement)` and checks/audits every exported declaration. Full output: [audit.log](/home/ubuntu/aklt/reports/LW/REC014/audit.log).
- Source scan found none of the forbidden proof shortcuts or declarations.
- All audited axioms belong to `{propext, Classical.choice, Quot.sound}`.

The requested theorem's audit is:

```text
'AKLT.W.REC014.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Complete declaration signatures and axiom output

```text
AKLT.W.REC014.main : AKLT.Blueprint.Rec.OneStepTrivialStatement
AKLT.W.REC014.dot_comm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC014.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.normSq_nonneg (a : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq a
'AKLT.W.REC014.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.normSq_add (a b : AKLT.Defs.Vec3) :
  AKLT.Defs.normSq (a + b) = AKLT.Defs.normSq a + AKLT.Defs.normSq b + 2 * AKLT.Defs.dot a b
'AKLT.W.REC014.normSq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.factor_nonneg (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  0 ≤ 1 + AKLT.Defs.dot a b
'AKLT.W.REC014.factor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.normSq_eq_zero {a : AKLT.Defs.Vec3} (h : AKLT.Defs.normSq a = 0) : a = 0
'AKLT.W.REC014.normSq_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.factor_pos (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1)
  (hne : a ≠ -b) : 0 < 1 + AKLT.Defs.dot a b
'AKLT.W.REC014.factor_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.golden_square : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC014.golden_square' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.radius_pos : 0 < AKLT.Defs.icoRadius
'AKLT.W.REC014.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.radius_square : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
'AKLT.W.REC014.radius_square' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC014.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.spin_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC014.spin_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.weight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
'AKLT.W.REC014.weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.weight_pos (s : AKLT.Defs.Status) (hs : s ≠ AKLT.Defs.Status.X) (j : AKLT.Defs.IcoLetter) :
  0 < AKLT.Defs.spinWeight s (some j)
'AKLT.W.REC014.weight_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.weight_sum (s : AKLT.Defs.Status) (hs : s ≠ AKLT.Defs.Status.X) : ∑ j, AKLT.Defs.spinWeight s j = 1
'AKLT.W.REC014.weight_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.weighted_dot_zero (v : AKLT.Defs.Vec3) :
  ∑ j, AKLT.Defs.spinWeight AKLT.Defs.Status.U j * AKLT.Defs.dot (AKLT.Defs.spinVector j) v = 0
'AKLT.W.REC014.weighted_dot_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.weighted_factor_one (v : AKLT.Defs.Vec3) :
  ∑ j, AKLT.Defs.spinWeight AKLT.Defs.Status.U j * (1 + AKLT.Defs.dot (AKLT.Defs.spinVector j) v) = 1
'AKLT.W.REC014.weighted_factor_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.label (j : Fin 3 × Fin 2) : AKLT.Defs.IcoLetter
'AKLT.W.REC014.label' depends on axioms: [propext]
AKLT.W.REC014.label_injective : Function.Injective fun j => AKLT.Defs.icoVector (AKLT.W.REC014.label j)
'AKLT.W.REC014.label_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.label_not_antipodal (j k : Fin 3 × Fin 2) :
  AKLT.Defs.icoVector (AKLT.W.REC014.label j) ≠ -AKLT.Defs.icoVector (AKLT.W.REC014.label k)
'AKLT.W.REC014.label_not_antipodal' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.label_avoids.{u_1} {ι : Type u_1} [Fintype ι] (b : ι → AKLT.Defs.UnitVector) (hc : Fintype.card ι ≤ 4) :
  ∃ j, ∀ (i : ι), 0 < 1 + AKLT.Defs.dot (AKLT.Defs.icoVector (AKLT.W.REC014.label j)) ↑(b i)
'AKLT.W.REC014.label_avoids' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.neighbour_adjacent {x z : AKLT.Defs.Plane} (h : z ∈ AKLT.Defs.neighbours x) : AKLT.Defs.Adjacent x z
'AKLT.W.REC014.neighbour_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.adjacent_symm {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : AKLT.Defs.Adjacent z x
'AKLT.W.REC014.adjacent_symm' depends on axioms: [propext, Quot.sound]
AKLT.W.REC014.adjacent_ne {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : x ≠ z
'AKLT.W.REC014.adjacent_ne' depends on axioms: [propext]
AKLT.W.REC014.adjacent_neighbour {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : z ∈ AKLT.Defs.neighbours x
'AKLT.W.REC014.adjacent_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.present_symm {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) {x z : AKLT.Defs.Plane}
  (h : D.Present x z) : D.Present z x
'AKLT.W.REC014.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.present_neighbour {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) {x z : AKLT.Defs.Plane}
  (h : D.Present x z) : z ∈ D.presentNeighbours x
'AKLT.W.REC014.present_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.leg_data {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (h : e ∈ AKLT.Defs.originalLegs G) : e.1 ∈ G ∧ e.2 ∈ AKLT.Defs.neighbours e.1 ∧ e.2 ∉ G
'AKLT.W.REC014.leg_data' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.leg_protected {G : Finset AKLT.Defs.Plane} (e : ↥(AKLT.Defs.originalLegs G)) :
  (↑e).1 ∈ AKLT.Defs.protectedSites G
'AKLT.W.REC014.leg_protected' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.leg_count {G : Finset AKLT.Defs.Plane} (x : AKLT.Defs.Plane) :
  {e ∈ AKLT.Defs.originalLegs G | e.1 = x}.card ≤ 4
'AKLT.W.REC014.leg_count' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.bonds_data {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (h : e ∈ AKLT.Defs.internalBonds G) : e.1 ∈ G ∧ e.2 ∈ AKLT.Defs.positiveNeighbours e.1 ∧ e.2 ∈ G
'AKLT.W.REC014.bonds_data' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.bond_orientation_unique {G : Finset AKLT.Defs.Plane} {e f : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (he : e ∈ AKLT.Defs.internalBonds G) (hf : f ∈ AKLT.Defs.internalBonds G)
  (h : e.1 = f.1 ∧ e.2 = f.2 ∨ e.1 = f.2 ∧ e.2 = f.1) : e = f
'AKLT.W.REC014.bond_orientation_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.present_bond {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) {y o : AKLT.Defs.Plane}
  (h : D.Present y o) : ∃ e ∈ D.bonds, e.1 = y ∧ e.2 = o ∨ e.1 = o ∧ e.2 = y
'AKLT.W.REC014.present_bond' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.sum_eq_of_fibre.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (y : ι)
  (F H : (ι → AKLT.Defs.SpinLetter) → ℝ)
  (h : ∀ (n : ι → AKLT.Defs.SpinLetter), ∑ j, F (Function.update n y j) = ∑ j, H (Function.update n y j)) :
  ∑ n, F n = ∑ n, H n
'AKLT.W.REC014.sum_eq_of_fibre' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.prod_update.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (s : ι → AKLT.Defs.Status)
  (n : ι → AKLT.Defs.SpinLetter) (y : ι) (j : AKLT.Defs.SpinLetter) :
  ∏ x, AKLT.Defs.spinWeight (s x) (Function.update n y j x) =
    AKLT.Defs.spinWeight (s y) j * ∏ x ∈ Finset.univ.erase y, AKLT.Defs.spinWeight (s x) (n x)
'AKLT.W.REC014.prod_update' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.integrate_leaf.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (s : ι → AKLT.Defs.Status) (y o : ι)
  (hyo : o ≠ y) (hy : s y = AKLT.Defs.Status.U) (H : (ι → AKLT.Defs.SpinLetter) → ℝ)
  (hH : ∀ (n : ι → AKLT.Defs.SpinLetter) (j : AKLT.Defs.SpinLetter), H (Function.update n y j) = H n) :
  ∑ n,
      (∏ x, AKLT.Defs.spinWeight (s x) (n x)) * H n *
        (1 + AKLT.Defs.dot (AKLT.Defs.spinVector (n y)) (AKLT.Defs.spinVector (n o))) =
    ∑ n, (∏ x, AKLT.Defs.spinWeight (Function.update s y AKLT.Defs.Status.D x) (n x)) * H n
'AKLT.W.REC014.integrate_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.spins_at {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (n : ↥D.active → AKLT.Defs.SpinLetter)
  (x : ↥D.active) : D.spins n ↑x = AKLT.Defs.spinVector (n x)
'AKLT.W.REC014.spins_at' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (n : ↥D.active → AKLT.Defs.SpinLetter)
  (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins n x) ≤ 1
'AKLT.W.REC014.spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.partition_positive {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (pinned : Bool) : 0 < D.partition τ pinned fun x => 1
'AKLT.W.REC014.partition_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.trace_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) : (AKLT.Defs.traceStep D y o).active = D.active
'AKLT.W.REC014.trace_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.trace_kept_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x : AKLT.Defs.Plane) :
  (AKLT.Defs.traceStep D y o).kept x ⊆ D.kept x
'AKLT.W.REC014.trace_kept_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.trace_present_old {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) {x z : AKLT.Defs.Plane} (h : (AKLT.Defs.traceStep D y o).Present x z) :
  D.Present x z
'AKLT.W.REC014.trace_present_old' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.trace_present_away {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) {x z : AKLT.Defs.Plane} (h : D.Present x z) (hx : x ≠ y) (hz : z ≠ y) :
  (AKLT.Defs.traceStep D y o).Present x z
'AKLT.W.REC014.trace_present_away' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.sole_neighbour (a : AKLT.Blueprint.Rec.Departure) (hc : (a.D.presentNeighbours a.y).card = 1)
  {z : AKLT.Defs.Plane} (hz : a.D.Present a.y z) : z = a.o
'AKLT.W.REC014.sole_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.trace_no_departure (a : AKLT.Blueprint.Rec.Departure) (hy : a.D.status a.y = AKLT.Defs.Status.U)
  (hc : (a.D.presentNeighbours a.y).card = 1) {x z : AKLT.Defs.Plane}
  (h : (AKLT.Defs.traceStep a.D a.y a.o).Present x z) : x ≠ a.y ∧ z ≠ a.y
'AKLT.W.REC014.trace_no_departure' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.leaf_bonds (a : AKLT.Blueprint.Rec.Departure) (hy : a.D.status a.y = AKLT.Defs.Status.U)
  (hc : (a.D.presentNeighbours a.y).card = 1) :
  ∃ e ∈ a.D.bonds,
    (e.1 = a.y ∧ e.2 = a.o ∨ e.1 = a.o ∧ e.2 = a.y) ∧
      (AKLT.Defs.traceStep a.D a.y a.o).bonds = a.D.bonds.erase e ∧ ∀ f ∈ a.D.bonds.erase e, f.1 ≠ a.y ∧ f.2 ≠ a.y
'AKLT.W.REC014.leaf_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.extendSpins (A : Finset AKLT.Defs.Plane) (n : ↥A → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) :
  AKLT.Defs.Vec3
'AKLT.W.REC014.extendSpins' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.extend_at (A : Finset AKLT.Defs.Plane) (n : ↥A → AKLT.Defs.SpinLetter) (x : ↥A) :
  AKLT.W.REC014.extendSpins A n ↑x = AKLT.Defs.spinVector (n x)
'AKLT.W.REC014.extend_at' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.extend_update_ne (A : Finset AKLT.Defs.Plane) (n : ↥A → AKLT.Defs.SpinLetter) (y : ↥A)
  (j : AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) (hx : x ≠ ↑y) :
  AKLT.W.REC014.extendSpins A (Function.update n y j) x = AKLT.W.REC014.extendSpins A n x
'AKLT.W.REC014.extend_update_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.partitionOn {G : Finset AKLT.Defs.Plane} (A : Finset AKLT.Defs.Plane)
  (s : AKLT.Defs.Plane → AKLT.Defs.Status) (B : Finset (AKLT.Defs.Plane × AKLT.Defs.Plane))
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) : ℝ
'AKLT.W.REC014.partitionOn' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.partition_on {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) : (D.partition τ b fun x => 1) = AKLT.W.REC014.partitionOn D.active D.status D.bonds τ b
'AKLT.W.REC014.partition_on' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.partition_collapse (a : AKLT.Blueprint.Rec.Departure) (hy : a.D.status a.y = AKLT.Defs.Status.U)
  (hc : (a.D.presentNeighbours a.y).card = 1) (b : Bool) :
  ((AKLT.Defs.traceStep a.D a.y a.o).partition a.τ b fun x => 1) = a.D.partition a.τ b fun x => 1
'AKLT.W.REC014.partition_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC014.main : AKLT.Blueprint.Rec.OneStepTrivialStatement
'AKLT.W.REC014.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues

None. The requested unconditional theorem exists, compiles, and passes the exact-type check.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC014/Main.lean` and seven helper/audit modules.
- Proved `AKLT.W.REC014.main : AKLT.Blueprint.Rec.OneStepTrivialStatement` exactly.
- Both pinned and free ratios equal one under the frozen hypotheses.
- Open declarations/residual statements: none.
- Proved the stronger helper `AKLT.W.REC014.partition_positive` for arbitrary networks.
- No other blueprint leaf is assumed; only actual definitions and proved Mathlib results are used.
- Direct finite active-site summation replaces the suggested reindexing through `FiniteSpinNetwork`.
- Final Main build and exact-type/all-declaration audit passed.
- Main axioms: `[propext, Classical.choice, Quot.sound]`; every helper uses only permitted axioms.
- No limitations, missing premises, or required follow-up decisions.
