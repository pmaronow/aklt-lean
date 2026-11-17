# REC043 exported declarations

All declarations below are in namespace `AKLT.W.REC043`.
These are the exact public source signatures, with proofs and definition bodies omitted.

## Bonds.lean

```lean
def exteriorBonds {G : Finset Plane} (D : Network G) (u : Plane) : Finset (Plane × Plane)

theorem bond_product_split {G : Finset Plane} (D : Network G) (u : Plane)
    (f : Plane → Plane → ℝ) (hf : ∀ x y, f x y = f y x) :
    (∏ e ∈ D.bonds, f e.1 e.2) =
      (∏ o ∈ D.presentNeighbours u, f u o) *
        ∏ e ∈ exteriorBonds D u, f e.1 e.2

theorem exteriorBonds_step {G : Finset Plane} {D : Network G} {u o : Plane}
    (hu : D.AdmissibleStart u) (hp : D.Present u o) :
    exteriorBonds (traceStep D u o) u = exteriorBonds D u

theorem departureNeighbours_step {G : Finset Plane} {D : Network G} {u o : Plane}
    (hu : D.AdmissibleStart u) (hp : D.Present u o) :
    (traceStep D u o).presentNeighbours u = (D.presentNeighbours u).erase o
```

## Enumeration.lean

```lean
@[simp] theorem trace_network_cons {G : Finset Plane} (D : Network G)
    {n : ℕ} (u : Plane) (d : Compass) (w : DirectionWord n) :
    traceNetwork D (wordVertices u (Fin.cons d w)) =
      traceNetwork (traceStep D u (u + d.step)) (wordVertices (u + d.step) w)

@[simp] theorem trace_coefficient_cons {G : Finset Plane} {D : Network G}
    {n : ℕ} {u : Plane} (hu : D.AdmissibleStart u) (d : Compass) (w : DirectionWord n) :
    (traceCoefficient D (wordVertices u (Fin.cons d w)) : ℝ) =
      (if D.status u = .U then (1 / 3 : ℝ) else 1 / 5) *
        (traceCoefficient (traceStep D u (u + d.step))
          (wordVertices (u + d.step) w) : ℝ)

def lengthTerm {G : Finset Plane} (D : Network G) (T : Finset Plane)
    (F : Network G → Plane → ℝ) (n : ℕ) (u : Plane) : ℝ

theorem lengthTerm_step {G : Finset Plane} {D : Network G} {u : Plane}
    (hu : D.AdmissibleStart u) {T : Finset Plane} (ht : u ∉ T)
    (F : Network G → Plane → ℝ) (n : ℕ) :
    lengthTerm D T F (n + 1) u =
      (if D.status u = .U then (1 / 3 : ℝ) else 1 / 5) *
        ∑ o ∈ D.presentNeighbours u, lengthTerm (traceStep D u o) T F n o

def boundedTrailSum {G : Finset Plane} (D : Network G) (T : Finset Plane)
    (F : Network G → Plane → ℝ) (m : ℕ) (u : Plane) : ℝ

theorem branchSum_eq_boundedTrailSum {G : Finset Plane} (D : Network G)
    (hD : D.Auxiliary) (T : Finset Plane) (hT : protectedSites G ⊆ T)
    (F : Network G → Plane → ℝ) (m : ℕ) (u : Plane) (hu : u ∈ T ∨ D.AdmissibleStart u) :
    branchSum D T F m u = boundedTrailSum D T F m u
```

## Factors.lean

```lean
theorem leg_first_protected {G : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs G) : e.1 ∈ protectedSites G

def legFactors {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (s : Plane → Vec3) : ℝ

def exteriorFactors {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (u : Plane) (s : Plane → Vec3) : ℝ

theorem exteriorFactors_step {G : Finset Plane} {D : Network G} {u o : Plane}
    (hu : D.AdmissibleStart u) (hp : D.Present u o) (τ : PinAssignment G)
    (b : Bool) (s : Plane → Vec3) :
    exteriorFactors (traceStep D u o) τ b u s = exteriorFactors D τ b u s

theorem factors_update {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) {u : Plane} (hu : u ∉ protectedSites G) (s : Plane → Vec3) (a : Vec3) :
    (∏ e ∈ D.bonds, (1 + dot (Function.update s u a e.1) (Function.update s u a e.2))) *
      legFactors D τ b (Function.update s u a) =
        (∏ o ∈ D.presentNeighbours u, (1 + dot a (s o))) * exteriorFactors D τ b u s

def paddedSiteFunctional (s : Status) (f : Vec3 → ℝ) : ℝ

theorem partition_site_fibre {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (u : G) (hu : u.val ∉ protectedSites G) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f =
      ∑ n : {x : G // x ≠ u} → SpinLetter,
        (∏ x : {x : G // x ≠ u}, paddedWeight (D.status x.val.val) (n x)) *
          exteriorFactors D τ b u.val (fibreSpins u n) *
            paddedSiteFunctional (D.status u.val) (fun a =>
              f (Function.update (fibreSpins u n) u.val a) *
                ∏ o ∈ D.presentNeighbours u.val, (1 + dot a (fibreSpins u n o)))
```

## Fibres.lean

```lean
def fibreSpins {G : Finset Plane} (u : G)
    (n : {x : G // x ≠ u} → SpinLetter) : Plane → Vec3

theorem finite_site_fibre {G : Finset Plane} (D : Network G) (u : G)
    (H : (Plane → Vec3) → ℝ) :
    (∑ n : (x : G) → SpinLetter, (∏ x : G, paddedWeight (D.status x.val) (n x)) *
        H (volumeSpins n)) =
      ∑ n : {x : G // x ≠ u} → SpinLetter,
        (∏ x : {x : G // x ≠ u}, paddedWeight (D.status x.val.val) (n x)) *
          ∑ j : SpinLetter, paddedWeight (D.status u.val) j *
            H (Function.update (fibreSpins u n) u.val (spinVector j))
```

## Iteration.lean

```lean
def branchSum {G : Finset Plane} (D : Network G) (T : Finset Plane)
    (F : Network G → Plane → ℝ) : ℕ → Plane → ℝ

def LocalPartitionResidual : Prop

theorem coordinate_eq_branchSum (hStep : LocalPartitionResidual)
    {G : Finset Plane} (τ : PinAssignment G) (b : Bool) (v : Plane) (k : Fin 3)
    (m : ℕ) (D : Network G) (hD : D.Auxiliary) (u : Plane)
    (hu : u ∈ insert v (protectedSites G) ∨ D.AdmissibleStart u)
    (hv : AdmissibleTarget D v) (hm : D.bonds.card ≤ m) :
    D.partition τ b (fun a => a u k * a v k) =
      branchSum D (insert v (protectedSites G))
        (fun E e => E.partition τ b (fun a => a e k * a v k)) m u
```

## LocalStep.lean

```lean
theorem coordinateStep : CoordinateStepStatement
```

## Main.lean

```lean
theorem coordinate_unnormalized (hStep : LocalPartitionResidual)
    {G : Finset Plane} (τ : PinAssignment G) (D : Network G) (hD : D.Auxiliary)
    (u v : Plane) (hu : D.AdmissibleStart u) (hv : AdmissibleTarget D v)
    (b : Bool) (k : Fin 3) :
    D.partition τ b (fun a => a u k * a v k) =
      stoppedSum D u (insert v (protectedSites G)) fun n w =>
        (traceCoefficient D (wordVertices u w) : ℝ) *
          (traceNetwork D (wordVertices u w)).partition τ b
            (fun a => a (wordVertex u w n) k * a v k)

theorem pair_unnormalized (hStep : LocalPartitionResidual)
    {G : Finset Plane} (τ : PinAssignment G) (D : Network G) (hD : D.Auxiliary)
    (u v : Plane) (hu : D.AdmissibleStart u) (hv : AdmissibleTarget D v) (b : Bool) :
    D.partition τ b (fun a => dot (a u) (a v)) =
      stoppedSum D u (insert v (protectedSites G)) fun n w =>
        (traceCoefficient D (wordVertices u w) : ℝ) *
          (traceNetwork D (wordVertices u w)).partition τ b
            (fun a => dot (a (wordVertex u w n)) (a v))

theorem main_of_localPartitionResidual (hStep : LocalPartitionResidual) :
    AKLT.Blueprint.Rec.PairExpansionStatement

theorem main : AKLT.Blueprint.Rec.PairExpansionStatement
```

## Moments.lean

```lean
theorem uStepMoment : AKLT.Blueprint.Rec.UStepMomentStatement

theorem dStepMoment : AKLT.Blueprint.Rec.DStepMomentStatement

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1

theorem spin_norm_le (j : SpinLetter) : normSq (spinVector j) ≤ 1
```

## Normalization.lean

```lean
def configurationWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : ℝ

theorem configurationWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : 0 ≤ configurationWeight D τ b n

theorem partition_eq_weighted_sum {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ n, configurationWeight D τ b n * f (D.spins n)

theorem partition_zero_of_normalizer_zero {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (hZ : D.partition τ b (fun _ => 1) = 0)
    (f : (Plane → Vec3) → ℝ) : D.partition τ b f = 0

theorem normalizer_mul_expectation {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun _ => 1) * D.expectation τ b f = D.partition τ b f
```

## Padding.lean

```lean
def paddedWeight (s : Status) (j : SpinLetter) : ℝ

def volumeSpins {G : Finset Plane} (n : (x : G) → SpinLetter) (x : Plane) : Vec3

def paddedPartition {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) : ℝ

theorem partition_eq_padded {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) : D.partition τ b f = paddedPartition D τ b f
```

## SetMoments.lean

```lean
@[simp] theorem paddedSite_U (f : Vec3 → ℝ) :
    paddedSiteFunctional .U f = siteFunctional .U f

@[simp] theorem paddedSite_D (f : Vec3 → ℝ) :
    paddedSiteFunctional .D f = siteFunctional .D f

@[simp] theorem paddedSite_X (f : Vec3 → ℝ) : paddedSiteFunctional .X f = f 0

theorem uMoment_finset (S : Finset Plane) (hS : S.card ≤ 3) (s : Plane → Vec3)
    (k : Fin 3) :
    paddedSiteFunctional .U (fun a => a k * ∏ o ∈ S, (1 + dot a (s o))) =
      (1 / 3 : ℝ) * ∑ o ∈ S, s o k *
        paddedSiteFunctional .D (fun a => ∏ p ∈ S.erase o, (1 + dot a (s p)))

theorem dMoment_finset (S : Finset Plane) (hS : S.card ≤ 1) (s : Plane → Vec3)
    (k : Fin 3) :
    paddedSiteFunctional .D (fun a => a k * ∏ o ∈ S, (1 + dot a (s o))) =
      (1 / 5 : ℝ) * ∑ o ∈ S, s o k

theorem paddedSite_mul_const (s : Status) (f : Vec3 → ℝ) (c : ℝ) :
    paddedSiteFunctional s (fun a => f a * c) = paddedSiteFunctional s f * c
```

## Trace.lean

```lean
theorem present_symm {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : D.Present y x

theorem traceStep_active_subset {G : Finset Plane} (D : Network G) (u o : Plane) :
    (traceStep D u o).active ⊆ D.active

theorem traceStep_kept_subset {G : Finset Plane} (D : Network G) (u o x : Plane) :
    (traceStep D u o).kept x ⊆ D.kept x

theorem traceStep_present_subset {G : Finset Plane} (D : Network G) (u o : Plane)
    {x y : Plane} (h : (traceStep D u o).Present x y) : D.Present x y

theorem traceStep_not_present {G : Finset Plane} (D : Network G) (u o : Plane) :
    ¬ (traceStep D u o).Present u o

theorem present_mem_bonds {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : (x, y) ∈ D.bonds ∨ (y, x) ∈ D.bonds

theorem traceStep_bonds_card_lt {G : Finset Plane} {D : Network G} {u o : Plane}
    (h : D.Present u o) : (traceStep D u o).bonds.card < D.bonds.card

theorem mem_presentNeighbours {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : y ∈ D.presentNeighbours x

theorem traceStep_neighbours_subset {G : Finset Plane} (D : Network G) (u o x : Plane) :
    (traceStep D u o).presentNeighbours x ⊆ D.presentNeighbours x

theorem traceStep_auxiliary {G : Finset Plane} {D : Network G}
    (hD : D.Auxiliary) {u o : Plane} (hu : D.AdmissibleStart u) (hp : D.Present u o) :
    (traceStep D u o).Auxiliary

theorem traceStep_target {G : Finset Plane} {D : Network G} {u o v : Plane}
    (hv : AdmissibleTarget D v) (hne : u ≠ v) :
    AdmissibleTarget (traceStep D u o) v

theorem traceStep_start {G : Finset Plane} {D : Network G}
    (hD : D.Auxiliary) {u o : Plane} (hp : D.Present u o)
    (ho : o ∉ protectedSites G) : (traceStep D u o).AdmissibleStart o

theorem traceStep_present_iff {G : Finset Plane} {D : Network G} {u o : Plane}
    (hu : D.AdmissibleStart u) (hp : D.Present u o) (x y : Plane) :
    (traceStep D u o).Present x y ↔
      D.Present x y ∧ ({x, y} : Finset Plane) ≠ {u, o}
```

## Trails.lean

```lean
@[simp] theorem word_vertex_zero {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertex u w 0 = u

@[simp] theorem word_vertex_cons {n : ℕ} (u : Plane) (d : Compass)
    (w : DirectionWord n) (j : ℕ) :
    wordVertex u (Fin.cons d w) (j + 1) = wordVertex (u + d.step) w j

@[simp] theorem word_bond_cons_zero {n : ℕ} (u : Plane) (d : Compass)
    (w : DirectionWord n) : wordBond u (Fin.cons d w) 0 = {u, u + d.step}

@[simp] theorem word_bond_cons_succ {n : ℕ} (u : Plane) (d : Compass)
    (w : DirectionWord n) (i : Fin n) :
    wordBond u (Fin.cons d w) i.succ = wordBond (u + d.step) w i

@[simp] theorem word_vertices_cons {n : ℕ} (u : Plane) (d : Compass)
    (w : DirectionWord n) :
    wordVertices u (Fin.cons d w) = u :: wordVertices (u + d.step) w

theorem stopped_cons_iff {G : Finset Plane} {D : Network G} {u : Plane}
    (hu : D.AdmissibleStart u) {T : Finset Plane} (ht : u ∉ T)
    {n : ℕ} (d : Compass) (w : DirectionWord n) :
    StoppedNetworkTrail D u T (Fin.cons d w) ↔
      D.Present u (u + d.step) ∧
        StoppedNetworkTrail (traceStep D u (u + d.step)) (u + d.step) T w

theorem sum_word_cons {n : ℕ} (f : DirectionWord (n + 1) → ℝ) :
    (∑ w, f w) = ∑ d : Compass, ∑ w : DirectionWord n, f (Fin.cons d w)
```
