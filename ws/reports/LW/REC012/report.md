STATUS: PROVED

## Result

The required closed theorem is proved with exactly the requested name and type:

```lean
theorem AKLT.W.REC012.main : AKLT.Blueprint.Rec.PinnedRatioUpperStatement
```

No residual premises remain. The earlier conditional `main` and `ResidualPinnedPartitionUpper` have been replaced by a complete proof. The original attempt is documented separately in `report.luna.md`.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/Main.lean): the requested closed theorem.
- [Local.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/Local.lean): reused norm, dot-product, spin-support, and partition nonnegativity proofs.
- [Moments.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/Moments.lean): direct first-, second-, and third-moment computations and integrated local formulas.
- [LocalProducts.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/LocalProducts.lean): local U lower bounds and D upper bounds for finite products.
- [Ambient.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/Ambient.lean): padding removed sites by a mass-one zero atom and reindexing the actual partition.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/Geometry.lean): incident bonds, their distinct neighbours, absence of departure legs, and trace bookkeeping.
- [Fibres.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/Fibres.lean): explicit splitting and summation of the departure-spin fibres.
- [Comparison.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/Comparison.lean): common nonnegative outside factor and unconditional partition comparison.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/Audit.lean): independent exact-type example and axiom checks for every exported declaration.

## Proof

The proof computes the first three moments of the explicit twelve-point icosahedral alphabet. These give the displayed integrated U factors for one, two, and three bonds and the D factor for at most two bonds. The existing vector estimates imply that a U factor with at most three bonds is at least 1/2, and a D factor with at most two bonds is at most 6/5. With at most one bond, the D factor is exactly one.

`partition_eq_ambient` reindexes every actual active-spin partition onto the fixed original volume G. A removed site is padded by the zero spin with mass one; all other completions have zero weight. `partition_fibres` then splits off the departure spin with an explicit finite equivalence and sums that spin exactly. A start outside the protected set has no original leg at the departure. The trace preserves all other site weights, all bonds away from the departure, and all original pin factors. Their common product is nonnegative.

For a U departure, the trace deletes the chosen bond and changes the site to D, leaving at most two factors. Thus each integrated traced fibre is at most 12/5 times its original fibre. For a D departure with at most one bond, the original and traced local integrals both equal one. Summing proves `pinned_partition_upper`. The final quotient follows from partition nonnegativity; a zero denominator is handled explicitly using real division by zero.

This direct proof needs only moments through degree three. It does not use the neighbouring leaves concerning degree-four conditional means, positive normalizers, or logarithmic coefficients. It also does not require conversion to `FiniteSpinNetwork`: the fixed-volume finite-sum model is defined and connected to the frozen partition directly.

## Validation

- `PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -f 'ELAPSED_SECONDS=%e' lake build AKLT.W.REC012.Main` — passed in **40.23 s**, rebuilding all eight proof modules, with no warnings. See [build.log](/home/ubuntu/aklt/reports/LW/REC012/build.log).
- `PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -f 'ELAPSED_SECONDS=%e' lake env lean AKLT/W/REC012/Audit.lean` — passed in **4.45 s**. Its independent example checks the exact closed type. See [axioms.log](/home/ubuntu/aklt/reports/LW/REC012/axioms.log).
- Only files under `AKLT/W/REC012/` and this report directory were written. No existing statement or library file was changed. No other blueprint leaf was used as a theorem.
- The source contains no proof placeholders, unproved assumptions, computation escape hatches, or additional axioms.

## Open issues

None. There are no residual statements or missing dependencies. The alternate fixed-volume summation is a proof implementation choice, with no change to the requested statement.

## Exported declarations and statements

All declarations below are in `AKLT.W.REC012`, with `open AKLT.Defs` and `open scoped BigOperators`; types are shown exactly as in their source headers. Every theorem is proved. The `def` entries are transparent data constructions used by the finite-sum proof.

### Local.lean

```lean
theorem normSq_add (u v : Vec3) :
    normSq (fun i => u i + v i) = normSq u + 2 * dot u v + normSq v

theorem normSq_sub (u v : Vec3) :
    normSq (fun i => u i - v i) = normSq u - 2 * dot u v + normSq v

theorem normSq_nonneg' (u : Vec3) : 0 ≤ normSq u

theorem dot_add_left (u v w : Vec3) :
    dot (fun i => u i + v i) w = dot u w + dot v w

theorem dot_abs_le_one {u v : Vec3} (hu : normSq u ≤ 1) (hv : normSq v ≤ 1) :
    -1 ≤ dot u v ∧ dot u v ≤ 1

theorem threeNeighbourLocalBounds (a b c : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    1 / 2 ≤ 1 + (dot a b + dot a c + dot b c) / 3 ∧
      1 + dot b c / 5 ≤ 6 / 5

theorem threeNeighbourScalarComparison (a b c : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    1 + dot b c / 5 ≤
      (12 / 5 : ℝ) * (1 + (dot a b + dot a c + dot b c) / 3)

theorem twoNeighbourLocalBound (a b : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    2 / 3 ≤ 1 + dot a b / 3

theorem twoNeighbourScalarComparison (a b : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    1 ≤ (12 / 5 : ℝ) * (1 + dot a b / 3)

theorem goldenRatio_sq :
    AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1

theorem icoRadius_sq :
    AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2

theorem icoVector_normSq (j : IcoLetter) : normSq (icoVector j) = 1

theorem spinVector_normSq_le_one (j : SpinLetter) : normSq (spinVector j) ≤ 1

theorem networkSpin_normSq_le_one {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) :
    normSq (D.spins n x) ≤ 1

theorem network_partition_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) :
    0 ≤ D.partition τ pinned (fun _ => 1)
```

### Moments.lean

```lean
lemma moment_coord_one (i : Fin 3) : moment (fun n => n i) = 0

lemma moment_coord_two (i j : Fin 3) :
    moment (fun n => n i * n j) = if i = j then 1 / 3 else 0

lemma moment_coord_three (i j k : Fin 3) :
    moment (fun n => n i * n j * n k) = 0

lemma moment_one : moment (fun _ => 1) = 1

lemma moment_add (f g : Vec3 → ℝ) : moment (fun n => f n + g n) = moment f + moment g

lemma moment_scale (c : ℝ) (f : Vec3 → ℝ) :
    moment (fun n => c * f n) = c * moment f

lemma moment_sum {ι : Type*} [Fintype ι] (f : ι → Vec3 → ℝ) :
    moment (fun n => ∑ i, f i n) = ∑ i, moment (f i)

lemma moment_dot (a : Vec3) : moment (fun n => dot n a) = 0

lemma moment_dot_two (a b : Vec3) :
    moment (fun n => dot n a * dot n b) = dot a b / 3

lemma moment_dot_three (a b c : Vec3) :
    moment (fun n => dot n a * dot n b * dot n c) = 0

lemma site_U (f : Vec3 → ℝ) : siteFunctional .U f = moment f

lemma site_D (f : Vec3 → ℝ) :
    siteFunctional .D f = (2 / 5 : ℝ) * f 0 + (3 / 5 : ℝ) * moment f

lemma moment_local_one (a : Vec3) : moment (fun n => 1 + dot n a) = 1

lemma moment_local_two (a b : Vec3) :
    moment (fun n => (1 + dot n a) * (1 + dot n b)) = 1 + dot a b / 3

lemma moment_local_three (a b c : Vec3) :
    moment (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n c)) =
      1 + (dot a b + dot a c + dot b c) / 3
```

### LocalProducts.lean

```lean
lemma site_D_one : siteFunctional .D (fun _ => 1) = 1

lemma site_U_one : siteFunctional .U (fun _ => 1) = 1

lemma site_D_local_one (a : Vec3) : siteFunctional .D (fun n => 1 + dot n a) = 1

lemma site_U_local_one (a : Vec3) : siteFunctional .U (fun n => 1 + dot n a) = 1

lemma site_D_local_two (a b : Vec3) :
    siteFunctional .D (fun n => (1 + dot n a) * (1 + dot n b)) = 1 + dot a b / 5

lemma site_U_lower {ι : Type*} (S : Finset ι) (v : ι → Vec3)
    (hS : S.card ≤ 3) (hv : ∀ i ∈ S, normSq (v i) ≤ 1) :
    1 / 2 ≤ siteFunctional .U (fun n => ∏ i ∈ S, (1 + dot n (v i)))

lemma site_D_upper {ι : Type*} (S : Finset ι) (v : ι → Vec3)
    (hS : S.card ≤ 2) (hv : ∀ i ∈ S, normSq (v i) ≤ 1) :
    siteFunctional .D (fun n => ∏ i ∈ S, (1 + dot n (v i))) ≤ 6 / 5

lemma site_D_small {ι : Type*} (S : Finset ι) (v : ι → Vec3) (hS : S.card ≤ 1) :
    siteFunctional .D (fun n => ∏ i ∈ S, (1 + dot n (v i))) = 1
```

### Ambient.lean

```lean
def paddedWeight (s : Status) (j : SpinLetter) : ℝ

def ambientSpins (G : Finset Plane) (n : G → SpinLetter) (x : Plane) : Vec3

def pinProduct {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (v : Plane → Vec3) : ℝ

def ambientTerm {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (n : G → SpinLetter) : ℝ

def ambientPartition {G : Finset Plane} (D : Network G) (τ : PinAssignment G) : ℝ

def completeSpins {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) : G → SpinLetter

lemma completeSpins_injective {G : Finset Plane} (D : Network G) :
    Function.Injective (completeSpins D)

lemma ambient_complete {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter) :
    ambientSpins G (completeSpins D n) = D.spins n

lemma ambientTerm_complete {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (n : D.active → SpinLetter) :
    ambientTerm D τ (completeSpins D n) =
      (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
        (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) * pinProduct D τ (D.spins n)

lemma ambientTerm_zero {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (n : G → SpinLetter) (x : G) (hx : x.val ∉ D.active) (hn : n x ≠ none) :
    ambientTerm D τ n = 0

lemma partition_eq_ambient {G : Finset Plane} (D : Network G) (τ : PinAssignment G) :
    D.partition τ true (fun _ => 1) = ambientPartition D τ
```

### Geometry.lean

```lean
lemma latticeDist_symm (x y : Plane) : latticeDist x y = latticeDist y x

lemma adjacent_ne {x y : Plane} (h : Adjacent x y) : x ≠ y

lemma present_symm {G : Finset Plane} (D : Network G) {x y : Plane} :
    D.Present x y ↔ D.Present y x

lemma mem_internalBonds {G : Finset Plane} {e : Plane × Plane} (h : e ∈ internalBonds G) :
    e.1 ∈ G ∧ e.2 ∈ G ∧ e.2 ∈ positiveNeighbours e.1

lemma positive_neighbour_ne {x y : Plane} (h : y ∈ positiveNeighbours x) : x ≠ y

lemma positive_asymm {x y : Plane} (h : y ∈ positiveNeighbours x) : x ∉ positiveNeighbours y

lemma positive_neighbour_mem {x y : Plane} (h : y ∈ positiveNeighbours x) : y ∈ neighbours x

lemma positive_neighbour_mem_reverse {x y : Plane} (h : y ∈ positiveNeighbours x) : x ∈ neighbours y

def incident {G : Finset Plane} (D : Network G) (y : Plane) : Finset (Plane × Plane)

def otherEnd (y : Plane) (e : Plane × Plane) : Plane

lemma incident_other_ne {G : Finset Plane} (D : Network G) (y : Plane)
    {e : Plane × Plane} (he : e ∈ incident D y) : otherEnd y e ≠ y

lemma incident_other_mem {G : Finset Plane} (D : Network G) (y : Plane)
    {e : Plane × Plane} (he : e ∈ incident D y) : otherEnd y e ∈ D.presentNeighbours y

lemma incident_other_injective {G : Finset Plane} (D : Network G) (y : Plane) :
    Set.InjOn (otherEnd y) (incident D y)

lemma incident_card_le {G : Finset Plane} (D : Network G) (y : Plane) :
    (incident D y).card ≤ (D.presentNeighbours y).card

lemma neighbour_dist {y z : Plane} (hz : z ∈ neighbours y) : latticeDist y z = 1

lemma no_legs_at_start {G : Finset Plane} (D : Network G) (y : Plane)
    (hy : D.AdmissibleStart y) (e : originalLegs G) : e.val.1 ≠ y

lemma trace_active_off {G : Finset Plane} (D : Network G) (y o x : Plane) (hx : x ≠ y) :
    x ∈ (traceStep D y o).active ↔ x ∈ D.active

lemma trace_present_off {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (hx : x ≠ y) (hz : z ≠ y) :
    (traceStep D y o).Present x z ↔ D.Present x z

lemma trace_neighbours_U {G : Finset Plane} (D : Network G) (y o : Plane)
    (hU : D.status y = .U) (ho : o ∈ D.presentNeighbours y) :
    (traceStep D y o).presentNeighbours y = (D.presentNeighbours y).erase o

lemma trace_neighbours_D {G : Finset Plane} (D : Network G) (y o : Plane)
    (hD : D.status y = .D) : (traceStep D y o).presentNeighbours y = ∅
```

### Fibres.lean

```lean
lemma dot_comm' (u v : Vec3) : dot u v = dot v u

def fillSpin {G : Finset Plane} (y : Plane) (n : G.erase y → SpinLetter)
    (j : SpinLetter) : G → SpinLetter

def splitSpin {G : Finset Plane} (y : Plane) (hy : y ∈ G) :
    (G → SpinLetter) ≃ SpinLetter × (G.erase y → SpinLetter)

lemma ambientSpins_fill {G : Finset Plane} (y : Plane) (hy : y ∈ G)
    (n : G.erase y → SpinLetter) (j : SpinLetter) :
    ambientSpins G (fillSpin y n j) =
      Function.update (ambientSpins (G.erase y) n) y (spinVector j)

lemma weightProduct_fill {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ G)
    (n : G.erase y → SpinLetter) (j : SpinLetter) :
    (∏ x : G, paddedWeight (D.status x.val) (fillSpin y n j x)) =
      paddedWeight (D.status y) j * ∏ x : G.erase y, paddedWeight (D.status x.val) (n x)

def offBonds {G : Finset Plane} (D : Network G) (y : Plane) : Finset (Plane × Plane)

def localIntegral {G : Finset Plane} (D : Network G) (y : Plane) (v : Plane → Vec3) : ℝ

def outsideFactor {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (n : G.erase y → SpinLetter) : ℝ

lemma pinProduct_update {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (v : Plane → Vec3) (z : Vec3) (hlegs : ∀ e : originalLegs G, e.val.1 ≠ y) :
    pinProduct D τ (Function.update v y z) = pinProduct D τ v

lemma bondProduct_update {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (z : Vec3) :
    (∏ e ∈ D.bonds, (1 + dot ((Function.update v y z) e.1) ((Function.update v y z) e.2))) =
      (∏ e ∈ offBonds D y, (1 + dot (v e.1) (v e.2))) *
        ∏ e ∈ incident D y, (1 + dot z (v (otherEnd y e)))

lemma ambientTerm_fill {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (hy : y ∈ G) (n : G.erase y → SpinLetter) (j : SpinLetter)
    (hlegs : ∀ e : originalLegs G, e.val.1 ≠ y) :
    ambientTerm D τ (fillSpin y n j) = outsideFactor D τ y n *
      (paddedWeight (D.status y) j *
        ∏ e ∈ incident D y, (1 + dot (spinVector j) (ambientSpins (G.erase y) n (otherEnd y e))))

lemma partition_fibres {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (hy : y ∈ G) (hlegs : ∀ e : originalLegs G, e.val.1 ≠ y) :
    D.partition τ true (fun _ => 1) = ∑ n : G.erase y → SpinLetter,
      outsideFactor D τ y n * localIntegral D y (ambientSpins (G.erase y) n)
```

### Comparison.lean

```lean
lemma paddedWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ paddedWeight s j

lemma ambientSpins_norm {G : Finset Plane} (n : G → SpinLetter) (x : Plane) :
    normSq (ambientSpins G n x) ≤ 1

lemma outsideFactor_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (n : G.erase y → SpinLetter) : 0 ≤ outsideFactor D τ y n

lemma offBonds_trace {G : Finset Plane} (D : Network G) (y o : Plane) :
    offBonds (traceStep D y o) y = offBonds D y

lemma outsideFactor_trace {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y o : Plane) (n : G.erase y → SpinLetter)
    (hlegs : ∀ e : originalLegs G, e.val.1 ≠ y) :
    outsideFactor (traceStep D y o) τ y n = outsideFactor D τ y n

lemma localIntegral_U_lower {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (hv : ∀ x, normSq (v x) ≤ 1)
    (hU : D.status y = .U) (hcard : (D.presentNeighbours y).card ≤ 3) :
    1 / 2 ≤ localIntegral D y v

lemma localIntegral_D_upper {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (hv : ∀ x, normSq (v x) ≤ 1)
    (hD : D.status y = .D) (hcard : (D.presentNeighbours y).card ≤ 2) :
    localIntegral D y v ≤ 6 / 5

lemma localIntegral_D_small {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (hD : D.status y = .D) (hcard : (D.presentNeighbours y).card ≤ 1) :
    localIntegral D y v = 1

lemma localIntegral_X {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (hX : D.status y = .X) : localIntegral D y v = 1

lemma localIntegral_trace_le {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.AdmissibleStart y) (ho : o ∈ D.presentNeighbours y)
    (v : Plane → Vec3) (hv : ∀ x, normSq (v x) ≤ 1) :
    localIntegral (traceStep D y o) y v ≤ (12 / 5 : ℝ) * localIntegral D y v

theorem pinned_partition_upper (a : AKLT.Blueprint.Rec.Departure) :
    (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) ≤
      (12 / 5 : ℝ) * a.D.partition a.τ true (fun _ => 1)
```

### Main.lean

```lean
theorem main : AKLT.Blueprint.Rec.PinnedRatioUpperStatement
```

## Axiom audit

`Audit.lean` checks all 80 named theorems and all 13 data definitions. Every dependency is among `propext`, `Classical.choice`, and `Quot.sound`. Full output:

```text
AKLT.W.REC012.main : AKLT.Blueprint.Rec.PinnedRatioUpperStatement
'AKLT.W.REC012.normSq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.normSq_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.normSq_nonneg'' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.dot_add_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.dot_abs_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.threeNeighbourLocalBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.threeNeighbourScalarComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.twoNeighbourLocalBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.twoNeighbourScalarComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.goldenRatio_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.icoRadius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.icoVector_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.spinVector_normSq_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.networkSpin_normSq_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.network_partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_coord_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_coord_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_coord_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_dot_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_dot_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_local_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_local_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.moment_local_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_D_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_U_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_D_local_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_U_local_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_D_local_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_U_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_D_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.site_D_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.paddedWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.ambientSpins' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.pinProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.ambientTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.ambientPartition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.completeSpins' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.completeSpins_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.ambient_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.ambientTerm_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.ambientTerm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.partition_eq_ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.latticeDist_symm' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC012.adjacent_ne' depends on axioms: [propext]
'AKLT.W.REC012.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.mem_internalBonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.positive_neighbour_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.positive_asymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.positive_neighbour_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.positive_neighbour_mem_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.incident' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.otherEnd' does not depend on any axioms
'AKLT.W.REC012.incident_other_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.incident_other_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.incident_other_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.incident_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.neighbour_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.no_legs_at_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.trace_active_off' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.trace_present_off' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.trace_neighbours_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.trace_neighbours_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.dot_comm'' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.fillSpin' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.splitSpin' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.ambientSpins_fill' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.weightProduct_fill' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.offBonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.localIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.outsideFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.pinProduct_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.bondProduct_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.ambientTerm_fill' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.partition_fibres' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.paddedWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.ambientSpins_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.outsideFactor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.offBonds_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.outsideFactor_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.localIntegral_U_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.localIntegral_D_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.localIntegral_D_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.localIntegral_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.localIntegral_trace_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.pinned_partition_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.main' depends on axioms: [propext, Classical.choice, Quot.sound]
ELAPSED_SECONDS=4.45
```

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/REC012/Main.lean` with seven supporting proof modules and `Audit.lean`.
- Exact declaration: `AKLT.W.REC012.main : AKLT.Blueprint.Rec.PinnedRatioUpperStatement`.
- The theorem is closed; the earlier residual premise is eliminated.
- Main intermediate result: `AKLT.W.REC012.pinned_partition_upper`.
- Explicit active-spin reindexing, finite fibre summation, and local moments are all proved here.
- Implementation choice: fixed original-volume spin sums instead of a `FiniteSpinNetwork` bridge.
- Only degree-three moments are needed for this bound; no conditioning or coefficient leaf is assumed.
- Main build passed in 40.23 s; exact-type and complete axiom audit passed in 4.45 s.
- Axioms of `main`: `[propext, Classical.choice, Quot.sound]`.
- No frozen files were changed; no forbidden proof devices or other blueprint-leaf lemmas were used.
- Open declarations, limitations, and remaining dependencies: none.
- Orchestrator may accept this leaf; no further decision is required.
