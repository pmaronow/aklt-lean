STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Main.lean) — Requested unconditional theorem and the logarithmic divided-difference argument.
- [Factorization.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Factorization.lean) — Two integrated partition identities, their normalized factorization, and the logarithmic step-ratio formula.
- [Network.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Network.lean) — Network partitions as finite quadratures and integration at the departure site.
- [Bonds.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Bonds.lean) — Deletion and trace identities, plus reindexing incident bonds by their other endpoints.
- [Sums.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Sums.lean) — Explicit configuration equivalence separating one site from the remaining active spins.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Geometry.lean) — Nearest-neighbour facts and absence of original legs at an admissible start.
- [Bounds.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Bounds.lean) — Nonnegative weights, pair expectation bounds, zero-normalizer handling, and positivity of I₂.
- [Quadrature.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Quadrature.lean) — Unit icosahedron vectors, scalar-product bounds, and the exact U two-factor / D one-factor integrals.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Audit.lean) — Independent exact-type check, types of every public declaration, and axiom checks for every public theorem.

No files outside `AKLT/W/REC017/` and the assigned report directory were changed. The previous residual-based `Main.lean` was replaced; `report.luna.md` was preserved.

## Requested declaration

```lean
theorem AKLT.W.REC017.main :
  AKLT.Blueprint.Rec.TwoLogIdentityStatement
```

This is unconditional and has exactly the required name and frozen type. Its expanded conclusion is the pinned/free logarithmic step-ratio difference equal to `responseBetaPrime * pairResponse` for every U departure with exactly the two distinct present neighbours `o,f`.

The proof uses an explicit bijection between configurations on `insert y V` and a departure letter paired with a configuration on `V`. The incident-bond product is reindexed by the remaining endpoint. Since an admissible start has no original legs, integrating its U spin gives `1 + dot (n f) (n o) / 3`; integrating the traced D spin with its one remaining bond gives one. All pins and all other network factors remain in the remaining partition sum.

Nonnegative weights and unit-ball spins imply the unnormalized pair numerator lies between minus and plus its normalizer. Thus every normalized pair mean lies in `[-1,1]`, including the zero-normalizer case, and both I₂ arguments are positive. If a remaining normalizer vanishes, its pair numerator also vanishes, so I₂ is one and the required logarithmic formula follows from Lean's total conventions for division and `Real.log 0`. Otherwise the partition factorization gives the reciprocal I₂ ratio directly. The positive logarithmic divided difference, including its coincident-argument branch, finishes the identity.

This direct route needs only second moments and the elementary pair bound. The stronger conditioning estimates, finite-network strict-positivity theorem, fourth moments, and rational coefficient bounds suggested for neighbouring leaves are unnecessary for this identity. No other blueprint leaf was assumed or used as a proved dependency; the needed factorization is proved locally as `AKLT.W.REC017.two_factorization`.

## Build and exact-type validation

From `/home/ubuntu/aklt/wt/LW_REC017`:

```bash
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC017.Main
PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC017/Audit.lean
```

- Final incremental main build: successful, **22.71 seconds**, exit status 0. See [build.log](build.log) and [build.time](build.time). The earlier new helper modules were also compiled successfully while developing the proof.
- Audit and independent exact-type check: successful, **4.70 seconds**, exit status 0. See [audit.log](audit.log) and [audit.time](audit.time).
- The audit includes `example : AKLT.Blueprint.Rec.TwoLogIdentityStatement := AKLT.W.REC017.main`, types of all 65 public declarations, and `#print axioms` for all 57 public theorems.
- All reported theorem axioms are subsets of `{propext, Classical.choice, Quot.sound}`. In particular:

```text
'AKLT.W.REC017.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A source scan found no forbidden proof placeholders, declarations, tactics, or kernel-check bypass options.

## Exported declarations and axiom output

The following is the complete output of `Audit.lean`: each public definition/theorem type, followed by every public theorem's axiom output. All names are in `AKLT.W.REC017`.

```text
AKLT.W.REC017.radius_pos : 0 < AKLT.Defs.icoRadius
AKLT.W.REC017.golden_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
AKLT.W.REC017.radius_sq : AKLT.Defs.icoRadius ^ 2 = 1 + AKLT.Defs.goldenRatio ^ 2
AKLT.W.REC017.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
AKLT.W.REC017.spin_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
AKLT.W.REC017.dot_comm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
AKLT.W.REC017.dot_bounds {a b : AKLT.Defs.Vec3} (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  -1 ≤ AKLT.Defs.dot a b ∧ AKLT.Defs.dot a b ≤ 1
AKLT.W.REC017.weight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
AKLT.W.REC017.site_U_pair (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v => (1 + AKLT.Defs.dot v a) * (1 + AKLT.Defs.dot v b)) =
    1 + AKLT.Defs.dot a b / 3
AKLT.W.REC017.site_D_single (a : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun v => 1 + AKLT.Defs.dot v a) = 1
AKLT.W.REC017.letters {V : Finset AKLT.Defs.Plane} (n : ↥V → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) :
  AKLT.Defs.SpinLetter
AKLT.W.REC017.field {V : Finset AKLT.Defs.Plane} (n : ↥V → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) : AKLT.Defs.Vec3
AKLT.W.REC017.letters_mem {V : Finset AKLT.Defs.Plane} (n : ↥V → AKLT.Defs.SpinLetter) (x : ↥V) :
  AKLT.W.REC017.letters n ↑x = n x
AKLT.W.REC017.field_mem {V : Finset AKLT.Defs.Plane} (n : ↥V → AKLT.Defs.SpinLetter) (x : ↥V) :
  AKLT.W.REC017.field n ↑x = AKLT.Defs.spinVector (n x)
AKLT.W.REC017.quadrature (V : Finset AKLT.Defs.Plane) (s : AKLT.Defs.Plane → AKLT.Defs.Status)
  (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) : ℝ
AKLT.W.REC017.insertEquiv (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (h : y ∉ V) :
  (↥(insert y V) → AKLT.Defs.SpinLetter) ≃ AKLT.Defs.SpinLetter × (↥V → AKLT.Defs.SpinLetter)
AKLT.W.REC017.letters_insert (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (h : y ∉ V) (a : AKLT.Defs.SpinLetter)
  (n : ↥V → AKLT.Defs.SpinLetter) :
  AKLT.W.REC017.letters ((AKLT.W.REC017.insertEquiv V y h).symm (a, n)) = Function.update (AKLT.W.REC017.letters n) y a
AKLT.W.REC017.field_insert (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (h : y ∉ V) (a : AKLT.Defs.SpinLetter)
  (n : ↥V → AKLT.Defs.SpinLetter) :
  AKLT.W.REC017.field ((AKLT.W.REC017.insertEquiv V y h).symm (a, n)) =
    Function.update (AKLT.W.REC017.field n) y (AKLT.Defs.spinVector a)
AKLT.W.REC017.quadrature_insert (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (h : y ∉ V)
  (s : AKLT.Defs.Plane → AKLT.Defs.Status) (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  AKLT.W.REC017.quadrature (insert y V) s F =
    AKLT.W.REC017.quadrature V s fun n => AKLT.Defs.siteFunctional (s y) fun v => F (Function.update n y v)
AKLT.W.REC017.quadrature_status_congr (V : Finset AKLT.Defs.Plane) (s t : AKLT.Defs.Plane → AKLT.Defs.Status)
  (h : ∀ x ∈ V, s x = t x) (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  AKLT.W.REC017.quadrature V s F = AKLT.W.REC017.quadrature V t F
AKLT.W.REC017.adjacent_symm {x y : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x y) : AKLT.Defs.Adjacent y x
AKLT.W.REC017.positive_ne (x y : AKLT.Defs.Plane) (h : y ∈ AKLT.Defs.positiveNeighbours x) : x ≠ y
AKLT.W.REC017.positive_no_reverse (x y : AKLT.Defs.Plane) (h : y ∈ AKLT.Defs.positiveNeighbours x) :
  x ∉ AKLT.Defs.positiveNeighbours y
AKLT.W.REC017.positive_neighbour {x y : AKLT.Defs.Plane} (h : y ∈ AKLT.Defs.positiveNeighbours x) :
  y ∈ AKLT.Defs.neighbours x
AKLT.W.REC017.reverse_positive_neighbour {x y : AKLT.Defs.Plane} (h : y ∈ AKLT.Defs.positiveNeighbours x) :
  x ∈ AKLT.Defs.neighbours y
AKLT.W.REC017.neighbour_orientation {x y : AKLT.Defs.Plane} (h : y ∈ AKLT.Defs.neighbours x) :
  y ∈ AKLT.Defs.positiveNeighbours x ∨ x ∈ AKLT.Defs.positiveNeighbours y
AKLT.W.REC017.neighbour_adjacent {x y : AKLT.Defs.Plane} (h : y ∈ AKLT.Defs.neighbours x) : AKLT.Defs.Adjacent x y
AKLT.W.REC017.present_symm {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x y : AKLT.Defs.Plane}
  (h : D.Present x y) : D.Present y x
AKLT.W.REC017.mem_internal {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane} :
  e ∈ AKLT.Defs.internalBonds G ↔ e.1 ∈ G ∧ e.2 ∈ AKLT.Defs.positiveNeighbours e.1 ∧ e.2 ∈ G
AKLT.W.REC017.mem_bonds {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {e : AKLT.Defs.Plane × AKLT.Defs.Plane} :
  e ∈ D.bonds ↔ e.2 ∈ AKLT.Defs.positiveNeighbours e.1 ∧ D.Present e.1 e.2
AKLT.W.REC017.no_leg_at_start {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y : AKLT.Defs.Plane}
  (hy : D.AdmissibleStart y) (e : ↥(AKLT.Defs.originalLegs G)) : (↑e).1 ≠ y
AKLT.W.REC017.remove_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).active = D.active.erase y
AKLT.W.REC017.remove_present {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y x z : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).Present x z ↔ D.Present x z ∧ x ≠ y ∧ z ≠ y
AKLT.W.REC017.remove_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).bonds = {e ∈ D.bonds | e.1 ≠ y ∧ e.2 ≠ y}
AKLT.W.REC017.bondProduct {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
AKLT.W.REC017.otherEnd (y : AKLT.Defs.Plane) (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : AKLT.Defs.Plane
AKLT.W.REC017.incident_other {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y : AKLT.Defs.Plane}
  {e : AKLT.Defs.Plane × AKLT.Defs.Plane} (he : e ∈ D.bonds) (hi : e.1 = y ∨ e.2 = y) :
  AKLT.W.REC017.otherEnd y e ∈ D.presentNeighbours y
AKLT.W.REC017.incident_injective {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y : AKLT.Defs.Plane}
  {e f : AKLT.Defs.Plane × AKLT.Defs.Plane} (he : e ∈ D.bonds) (hf : f ∈ D.bonds) (hei : e.1 = y ∨ e.2 = y)
  (hfi : f.1 = y ∨ f.2 = y) (hv : AKLT.W.REC017.otherEnd y e = AKLT.W.REC017.otherEnd y f) : e = f
AKLT.W.REC017.incident_surjective {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y z : AKLT.Defs.Plane}
  (hz : z ∈ D.presentNeighbours y) : ∃ e ∈ D.bonds, (e.1 = y ∨ e.2 = y) ∧ AKLT.W.REC017.otherEnd y e = z
AKLT.W.REC017.bondProduct_split {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) (v : AKLT.Defs.Vec3) :
  AKLT.W.REC017.bondProduct D (Function.update n y v) =
    AKLT.W.REC017.bondProduct (AKLT.Defs.removeSite D y) n * ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot v (n z))
AKLT.W.REC017.trace_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) : (AKLT.Defs.traceStep D y o).active = D.active
AKLT.W.REC017.trace_present {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x z : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) :
  (AKLT.Defs.traceStep D y o).Present x z ↔ D.Present x z ∧ ¬(x = y ∧ z = o ∨ x = o ∧ z = y)
AKLT.W.REC017.trace_neighbours {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) (hne : y ≠ o) :
  (AKLT.Defs.traceStep D y o).presentNeighbours y = (D.presentNeighbours y).erase o
AKLT.W.REC017.pinProduct {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
AKLT.W.REC017.field_eq_spins {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) : AKLT.W.REC017.field n = D.spins n
AKLT.W.REC017.partition_quad {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b F =
    AKLT.W.REC017.quadrature D.active D.status fun n =>
      F n * AKLT.W.REC017.bondProduct D n * AKLT.W.REC017.pinProduct D τ b n
AKLT.W.REC017.pinProduct_split {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ y)
  (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) (v : AKLT.Defs.Vec3) :
  AKLT.W.REC017.pinProduct D τ b (Function.update n y v) = AKLT.W.REC017.pinProduct (AKLT.Defs.removeSite D y) τ b n
AKLT.W.REC017.partition_integrate {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∈ D.active) (hleg : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ y) :
  (D.partition τ b fun x => 1) =
    (AKLT.Defs.removeSite D y).partition τ b fun n =>
      AKLT.Defs.siteFunctional (D.status y) fun v => ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot v (n z))
AKLT.W.REC017.remove_trace_partition {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (y o : AKLT.Defs.Plane) (hy : D.status y = AKLT.Defs.Status.U)
  (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).partition τ b F = (AKLT.Defs.removeSite D y).partition τ b F
AKLT.W.REC017.networkWeight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) : ℝ
AKLT.W.REC017.partition_weight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b F = ∑ n, AKLT.W.REC017.networkWeight D τ b n * F (D.spins n)
AKLT.W.REC017.spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (n : ↥D.active → AKLT.Defs.SpinLetter)
  (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins n x) ≤ 1
AKLT.W.REC017.networkWeight_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) :
  0 ≤ AKLT.W.REC017.networkWeight D τ b n
AKLT.W.REC017.partition_mono {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) {F H : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ}
  (h : ∀ (n : ↥D.active → AKLT.Defs.SpinLetter), F (D.spins n) ≤ H (D.spins n)) : D.partition τ b F ≤ D.partition τ b H
AKLT.W.REC017.partition_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) : 0 ≤ D.partition τ b fun x => 1
AKLT.W.REC017.partition_affine {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun n => 1 + F n / 3) = (D.partition τ b fun x => 1) + D.partition τ b F / 3
AKLT.W.REC017.pair_partition_bounds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (x z : AKLT.Defs.Plane) :
  ((-D.partition τ b fun x => 1) ≤ D.partition τ b fun n => AKLT.Defs.dot (n x) (n z)) ∧
    (D.partition τ b fun n => AKLT.Defs.dot (n x) (n z)) ≤ D.partition τ b fun x => 1
AKLT.W.REC017.pair_partition_zero {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (x z : AKLT.Defs.Plane) (h : (D.partition τ b fun x => 1) = 0) :
  (D.partition τ b fun n => AKLT.Defs.dot (n x) (n z)) = 0
AKLT.W.REC017.pair_expectation_bounds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (x z : AKLT.Defs.Plane) :
  (-1 ≤ D.expectation τ b fun n => AKLT.Defs.dot (n x) (n z)) ∧
    (D.expectation τ b fun n => AKLT.Defs.dot (n x) (n z)) ≤ 1
AKLT.W.REC017.responseI₂_pos {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y o f : AKLT.Defs.Plane) : 0 < AKLT.Blueprint.Rec.responseI₂ D τ b y o f
AKLT.W.REC017.two_partition_raw (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = AKLT.Defs.Status.U)
  (f : AKLT.Defs.Plane) (hN : a.D.presentNeighbours a.y = {a.o, f}) (hne : a.o ≠ f) (b : Bool) :
  (a.D.partition a.τ b fun x => 1) =
    ((AKLT.Defs.removeSite a.D a.y).partition a.τ b fun x => 1) +
      ((AKLT.Defs.removeSite a.D a.y).partition a.τ b fun n => AKLT.Defs.dot (n f) (n a.o)) / 3
AKLT.W.REC017.two_partition_after (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = AKLT.Defs.Status.U)
  (f : AKLT.Defs.Plane) (hN : a.D.presentNeighbours a.y = {a.o, f}) (hne : a.o ≠ f) (b : Bool) :
  ((AKLT.Defs.traceStep a.D a.y a.o).partition a.τ b fun x => 1) =
    (AKLT.Defs.removeSite a.D a.y).partition a.τ b fun x => 1
AKLT.W.REC017.two_factorization : AKLT.Blueprint.Rec.TwoFactorizationStatement
AKLT.W.REC017.log_stepRatio (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = AKLT.Defs.Status.U)
  (f : AKLT.Defs.Plane) (hN : a.D.presentNeighbours a.y = {a.o, f}) (hne : a.o ≠ f) (b : Bool) :
  Real.log (AKLT.Defs.stepRatio a.D a.τ b a.y a.o) = -Real.log (AKLT.Blueprint.Rec.responseI₂ a.D a.τ b a.y a.o f)
AKLT.W.REC017.main : AKLT.Blueprint.Rec.TwoLogIdentityStatement
'AKLT.W.REC017.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.golden_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.radius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.spin_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.dot_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.site_U_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.site_D_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.letters_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.field_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.letters_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.field_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.quadrature_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.quadrature_status_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.adjacent_symm' depends on axioms: [propext]
'AKLT.W.REC017.positive_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.positive_no_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.positive_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.reverse_positive_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.neighbour_orientation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.neighbour_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.mem_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.mem_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.no_leg_at_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.remove_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.remove_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.remove_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.incident_other' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.incident_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.incident_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.bondProduct_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.trace_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.trace_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.trace_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.field_eq_spins' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.partition_quad' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.pinProduct_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.partition_integrate' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.remove_trace_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.partition_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.networkWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.partition_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.partition_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.pair_partition_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.pair_partition_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.pair_expectation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.responseI₂_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.two_partition_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.two_partition_after' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.two_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.log_stepRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC017.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues

None. No residual statements or additional premises remain. The earlier `ResidualTwoFactorization`, `ResidualPositivePartitions`, and `main_of_residuals` declarations were replaced by fully proved local lemmas and the requested `main`.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC017/Main.lean` and eight local helper/audit modules.
- Exact theorem: `AKLT.W.REC017.main : AKLT.Blueprint.Rec.TwoLogIdentityStatement`.
- STATUS: PROVED; no assumed blueprint dependencies and no residuals.
- Partition factorization is proved locally as `AKLT.W.REC017.two_factorization`.
- Direct active-site finite-sum reindexing replaces the suggested finite-network route.
- The elementary pair bound suffices; stronger conditioning and coefficient estimates are not needed.
- Zero normalizers are handled explicitly using the frozen definitions' total division/log conventions.
- Main build passed in 22.71 seconds; exact-type/all-theorem audit passed in 4.70 seconds.
- All 57 public theorem axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound`.
- Prior residual-based declarations were removed; `report.luna.md` is preserved.
- Open names: none. Limitations: none. No orchestrator decision is required.
