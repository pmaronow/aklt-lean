STATUS: PROVED FROM DEPS

## Deliverable

```lean
theorem AKLT.W.REC079.main : AKLT.Blueprint.Rec.TraceKernelLengthStatement
```

The exact frozen statement is proved with no residual hypotheses. Its expanded conclusion is:

```lean
AKLT.Blueprint.Top.H1Statement → ∀ p : AKLT.Blueprint.Rec.PairData,
  ∀ d : ℕ, 1 ≤ d → (d : ℕ∞) ≤ p.depth → ∀ n : ℕ,
  |AKLT.Blueprint.Rec.firstLength p n| ≤
    ∑ Y : AKLT.Defs.PairType, ∑ s ∈ Finset.range (n + 2),
      (AKLT.Defs.kernelLengthCoefficient p.X Y s n : ℝ) *
        AKLT.Defs.responseEnvelope Y ((d : ℤ) - s)
```

## Files

- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Audit.lean)
- [Closure.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Closure.lean)
- [ExposureAlgebra.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/ExposureAlgebra.lean)
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Geometry.lean)
- [KernelAlgebra.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/KernelAlgebra.lean)
- [KernelSupport.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/KernelSupport.lean)
- [LocalComparison.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/LocalComparison.lean)
- [LocalInputs.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/LocalInputs.lean)
- [LocalLogComparison.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/LocalLogComparison.lean)
- [Main.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Main.lean)
- [OrderedExposure.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/OrderedExposure.lean)
- [Ordering.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Ordering.lean)
- [TraceGeometry.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/TraceGeometry.lean)
- [TraceStatus.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/TraceStatus.lean)
- [TrailComparison.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/TrailComparison.lean)

The six added proof modules are `LocalInputs.lean`, `Closure.lean`, `TrailComparison.lean`, `LocalLogComparison.lean`, `ExposureAlgebra.lean`, `OrderedExposure.lean`. The earlier geometry, status, ordering, kernel algebra, and finite-sum reduction are reused. `Main.lean` now exports the requested unconditional theorem, and `Audit.lean` audits the completed library. No source outside `AKLT/W/REC079/` was edited.

Report artifacts:

- [audit.log](/home/ubuntu/aklt/reports/LW/REC079/audit.log): all 130 public declaration types checked by `#check`, together with the axiom audit for every one of the 109 manually exported theorems.
- [build.log](/home/ubuntu/aklt/reports/LW/REC079/build.log): successful required build and wall-clock timing.
- [audit.time](/home/ubuntu/aklt/reports/LW/REC079/audit.time): direct Lean audit timing.
- [additional-leaves.tsv](/home/ubuntu/aklt/reports/LW/REC079/additional-leaves.tsv): optional index rows for additional closed statements proved here.

## Proof

H1 is applied to REC089's common nonnegative mixture to obtain the shared-matcher passage bound and integrated lower bounds. The proved interval, analytic and rational-enclosure leaves then give exactly `Top.ResponseTypedStatementV2`.

REC096's stronger prefix invariant and REC050's auxiliary validity restore an ordinary consistent domain after removing the live departure site. Distinct active non-arrival neighbours satisfy the response-pair definition. Arrival neighbours are excluded throughout this argument.

One fixed lattice chart is chosen per original pair. Actual U departures are lattice first visits; extra initial D departures decrease the mass-free coefficient. Present response neighbours map into the kernel-live set. The local logarithmic estimate treats one, two and three present neighbours separately; beta-prime is dominated by beta when the kernel still retains an additional live neighbour.

The actual response pair is bounded using REC078's shifted ordinary-domain supremum. Inactive endpoints have signal zero. Pair type and the actual maximum shift are preserved by the fixed chart. Ordered exposure uses REC046's product estimate and REC041's trace telescope, retaining the prescribed `kernelOrdering` in both its short and long scopes. Revisit indices appended after that ordering have zero reward. These arguments discharge both propositions in the earlier reduction, and its finite injection of words yields the frozen numerical conclusion.

## Principal exported declarations

All names below have prefix `AKLT.W.REC079`.

```lean
main : AKLT.Blueprint.Rec.TraceKernelLengthStatement
ordered_exposure : Residual_OrderedExposureV2
local_envelope : Residual_LocalEnvelopeV2
covered_ratio : AKLT.Blueprint.Rec.CoveredRatioStatementV2
covered_integrated_lower : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2
pair_closure : AKLT.Blueprint.Rec.PairClosureStatementV2
response_typed : AKLT.Blueprint.Top.ResponseTypedStatementV2
main_from_residuals (hexposure : Residual_OrderedExposureV2)
  (hlocal : Residual_LocalEnvelopeV2) : AKLT.Blueprint.Rec.TraceKernelLengthStatement
```

`Residual_OrderedExposureV2` and `Residual_LocalEnvelopeV2` are retained as transparent definitions, and are now both proved. The complete types of every helper declaration and every exported theorem are included in the audit appendix below.

The additional closed leaf proofs correspond to REC090, REC091 and REC097. These were proved locally, without assuming the currently unindexed leaves. The orchestrator may reuse the supplied index rows.

## Dependencies

Every directly imported proved-leaf module occurs in the supplied proved index:

- `AKLT.W.REC001.Main`
- `AKLT.W.REC002.Main`
- `AKLT.W.REC003.Main`
- `AKLT.W.REC004.Main`
- `AKLT.W.REC005.Main`
- `AKLT.W.REC010.Main`
- `AKLT.W.REC011.Main`
- `AKLT.W.REC013.Main`
- `AKLT.W.REC014.Main`
- `AKLT.W.REC015.Main`
- `AKLT.W.REC017.Main`
- `AKLT.W.REC018.Main`
- `AKLT.W.REC020.Main`
- `AKLT.W.REC022.Main`
- `AKLT.W.REC027.Main`
- `AKLT.W.REC028.Main`
- `AKLT.W.REC034.Main`
- `AKLT.W.REC035.Main`
- `AKLT.W.REC036.Main`
- `AKLT.W.REC039.Main`
- `AKLT.W.REC041.Main`
- `AKLT.W.REC046.Main`
- `AKLT.W.REC050.Main`
- `AKLT.W.REC078.Main`
- `AKLT.W.REC089.Main`
- `AKLT.W.REC096.Main`

The implementation uses the underlying ordered-product estimate REC046 and the actual-pair shift bound REC078. It does not identify the earlier broad residuals with REC077 or REC083; the extra local comparison and closure work is proved explicitly.

## Axioms and verification

```text
#print axioms AKLT.W.REC079.main
'AKLT.W.REC079.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every exported theorem was individually audited; the union of all reported axioms is exactly `propext`, `Classical.choice`, and `Quot.sound`. The source scan found no prohibited proof constructs.

- `PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2 /usr/bin/time -p lake build AKLT.W.REC079.Main` — passed; real 13.65 s, user 13.66 s, sys 3.70 s. This final build compiled the remaining changed modules; earlier dependency builds had populated the cache. Mathlib was not rebuilt or modified.
- `PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2 /usr/bin/time -p lake env lean AKLT/W/REC079/Audit.lean` — passed; real 4.92 s, user 4.02 s, sys 8.26 s.

Open issues: none for REC079. Existing dependency linter/deprecation warnings do not affect the successful kernel checks. The only intended input to the frozen comparison remains H1, as specified by its definition.

## Complete declaration and axiom audit

The following is the exact successful output of `lake env lean AKLT/W/REC079/Audit.lean`:

```text
AKLT.W.REC079.LatticeChart : Type
AKLT.W.REC079.LatticeChart.trans (F H : AKLT.W.REC079.LatticeChart) : AKLT.W.REC079.LatticeChart
AKLT.W.REC079.LatticeChart.translate (c : AKLT.Defs.Plane) : AKLT.W.REC079.LatticeChart
AKLT.W.REC079.LatticeChart.flip (a b : Bool) : AKLT.W.REC079.LatticeChart
AKLT.W.REC079.LatticeChart.swap (s : Bool) : AKLT.W.REC079.LatticeChart
AKLT.W.REC079.LatticeChart.orient (s a b : Bool) : AKLT.W.REC079.LatticeChart
AKLT.W.REC079.LatticeChart.orient_zero (s a b : Bool) : (AKLT.W.REC079.LatticeChart.orient s a b).point (0, 0) = (0, 0)
'AKLT.W.REC079.LatticeChart.orient_zero' depends on axioms: [propext, Quot.sound]
AKLT.W.REC079.adjacent_direction {x y : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x y) : ∃ a, x = y + a.step
'AKLT.W.REC079.adjacent_direction' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pair_chart (p : AKLT.Blueprint.Rec.PairData) :
  ∃ F,
    F.point p.c = AKLT.Defs.kernelCentre ∧
      F.point p.u = AKLT.Defs.kernelStart ∧ F.point p.v = AKLT.Defs.kernelTarget p.X
'AKLT.W.REC079.pair_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonicalChart (p : AKLT.Blueprint.Rec.PairData) : AKLT.W.REC079.LatticeChart
AKLT.W.REC079.canonicalChart_centre (p : AKLT.Blueprint.Rec.PairData) :
  (AKLT.W.REC079.canonicalChart p).point p.c = AKLT.Defs.kernelCentre
'AKLT.W.REC079.canonicalChart_centre' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonicalChart_start (p : AKLT.Blueprint.Rec.PairData) :
  (AKLT.W.REC079.canonicalChart p).point p.u = AKLT.Defs.kernelStart
'AKLT.W.REC079.canonicalChart_start' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonicalChart_target (p : AKLT.Blueprint.Rec.PairData) :
  (AKLT.W.REC079.canonicalChart p).point p.v = AKLT.Defs.kernelTarget p.X
'AKLT.W.REC079.canonicalChart_target' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonicalWord (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n) :
  AKLT.Defs.DirectionWord n
AKLT.W.REC079.canonicalWord_injective (p : AKLT.Blueprint.Rec.PairData) (n : ℕ) :
  Function.Injective (AKLT.W.REC079.canonicalWord p)
'AKLT.W.REC079.canonicalWord_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonicalWord_vertex (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n) (j : ℕ)
  (hj : j ≤ n) :
  AKLT.Defs.wordVertex AKLT.Defs.kernelStart (AKLT.W.REC079.canonicalWord p w) j =
    (AKLT.W.REC079.canonicalChart p).point (AKLT.Defs.wordVertex p.u w j)
'AKLT.W.REC079.canonicalWord_vertex' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonicalWord_baseWeight (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n) :
  AKLT.Defs.trailBaseWeight AKLT.Defs.kernelStart (AKLT.W.REC079.canonicalWord p w) = AKLT.Defs.trailBaseWeight p.u w
'AKLT.W.REC079.canonicalWord_baseWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.responsePair_endpoints_ne (p : AKLT.Blueprint.Rec.PairData) : p.u ≠ p.v
'AKLT.W.REC079.responsePair_endpoints_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.target_trail_avoids_centre (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w)
  (hend : AKLT.Defs.wordVertex p.u w n = p.v) (j : ℕ) (hj : j ≤ n) : AKLT.Defs.wordVertex p.u w j ≠ p.c
'AKLT.W.REC079.target_trail_avoids_centre' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.target_trail_closed (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w)
  (hend : AKLT.Defs.wordVertex p.u w n = p.v) : AKLT.Defs.ClosedTrail p.X (AKLT.W.REC079.canonicalWord p w)
'AKLT.W.REC079.target_trail_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.realExposure {n : ℕ} (w : AKLT.Defs.DirectionWord n) (r : Fin n → ℝ) : List (Fin n) → ℝ
AKLT.W.REC079.realExposure_cast {n : ℕ} (w : AKLT.Defs.DirectionWord n) (r : Fin n → ℚ) (l : List (Fin n)) :
  AKLT.W.REC079.realExposure w (fun i => ↑(r i)) l = ↑(AKLT.Defs.exposureSum w r l)
'AKLT.W.REC079.realExposure_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.realExposure_sum.{u_1} {n : ℕ} (w : AKLT.Defs.DirectionWord n) {ι : Type u_1} (s : Finset ι)
  (r : ι → Fin n → ℝ) (l : List (Fin n)) :
  AKLT.W.REC079.realExposure w (fun i => ∑ a ∈ s, r a i) l = ∑ a ∈ s, AKLT.W.REC079.realExposure w (r a) l
'AKLT.W.REC079.realExposure_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.realExposure_mul {n : ℕ} (w : AKLT.Defs.DirectionWord n) (r : Fin n → ℝ) (c : ℝ) (l : List (Fin n)) :
  AKLT.W.REC079.realExposure w (fun i => r i * c) l = AKLT.W.REC079.realExposure w r l * c
'AKLT.W.REC079.realExposure_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.realExposure_nonneg {n : ℕ} (w : AKLT.Defs.DirectionWord n) (r : Fin n → ℝ) (hr : ∀ (i : Fin n), 0 ≤ r i)
  (l : List (Fin n)) : 0 ≤ AKLT.W.REC079.realExposure w r l
'AKLT.W.REC079.realExposure_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.realExposure_mono {n : ℕ} (w : AKLT.Defs.DirectionWord n) (r r' : Fin n → ℝ)
  (hr : ∀ (i : Fin n), r i ≤ r' i) (l : List (Fin n)) :
  AKLT.W.REC079.realExposure w r l ≤ AKLT.W.REC079.realExposure w r' l
'AKLT.W.REC079.realExposure_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.realExposure_filter_le {n : ℕ} (w : AKLT.Defs.DirectionWord n) (r : Fin n → ℝ)
  (hr : ∀ (i : Fin n), 0 ≤ r i) (keep : Fin n → Bool) (l : List (Fin n)) :
  AKLT.W.REC079.realExposure w r (List.filter keep l) ≤ AKLT.W.REC079.realExposure w r l
'AKLT.W.REC079.realExposure_filter_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.indexedReward {n : ℕ} (X : AKLT.Defs.PairType) (d : ℕ) (w : AKLT.Defs.DirectionWord n) (i : Fin n) : ℝ
AKLT.W.REC079.canonicalBudget {n : ℕ} (X : AKLT.Defs.PairType) (d : ℕ) (w : AKLT.Defs.DirectionWord n) : ℝ
AKLT.W.REC079.kernel_bound_eq_sum (X : AKLT.Defs.PairType) (d n : ℕ) :
  ∑ Y,
      ∑ s ∈ Finset.range (n + 2),
        ↑(AKLT.Defs.kernelLengthCoefficient X Y s n) * AKLT.Defs.responseEnvelope Y (↑d - ↑s) =
    ∑ w, if AKLT.Defs.ClosedTrail X w then AKLT.W.REC079.canonicalBudget X d w else 0
'AKLT.W.REC079.kernel_bound_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.latticeDist_triangle (x y z : AKLT.Defs.Plane) :
  AKLT.Defs.latticeDist x z ≤ AKLT.Defs.latticeDist x y + AKLT.Defs.latticeDist y z
'AKLT.W.REC079.latticeDist_triangle' depends on axioms: [propext, Quot.sound]
AKLT.W.REC079.latticeDist_symm (x y : AKLT.Defs.Plane) : AKLT.Defs.latticeDist x y = AKLT.Defs.latticeDist y x
'AKLT.W.REC079.latticeDist_symm' depends on axioms: [propext, Quot.sound]
AKLT.W.REC079.latticeDist_step (x : AKLT.Defs.Plane) (a : AKLT.Defs.Compass) : AKLT.Defs.latticeDist (x + a.step) x = 1
'AKLT.W.REC079.latticeDist_step' depends on axioms: [propext, Classical.choice]
AKLT.W.REC079.vertex_distance_le {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (j : ℕ) (hj : j ≤ n) :
  AKLT.Defs.latticeDist (AKLT.Defs.wordVertex u w j) u ≤ j
'AKLT.W.REC079.vertex_distance_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.responsePair_shift_le {n : ℕ} (X : AKLT.Defs.PairType) (w : AKLT.Defs.DirectionWord n) (i : Fin n)
  (p : Finset AKLT.Defs.Plane) (hp : p ∈ AKLT.Defs.responsePairs w i) : AKLT.Defs.pairShift X p ≤ n + 1
'AKLT.W.REC079.responsePair_shift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.responseEnvelope_nonneg (X : AKLT.Defs.PairType) (d : ℤ) : 0 ≤ AKLT.Defs.responseEnvelope X d
'AKLT.W.REC079.responseEnvelope_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pairCoefficient_nonneg {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n) (p : Finset AKLT.Defs.Plane) :
  0 ≤ AKLT.Defs.pairCoefficient w i p
'AKLT.W.REC079.pairCoefficient_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.trailBaseWeight_nonneg {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) :
  0 ≤ AKLT.Defs.trailBaseWeight u w
'AKLT.W.REC079.trailBaseWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pairReward {n : ℕ} (X : AKLT.Defs.PairType) (d : ℕ) (w : AKLT.Defs.DirectionWord n) (i : Fin n) : ℝ
AKLT.W.REC079.indexedReward_eq_pairReward {n : ℕ} (X : AKLT.Defs.PairType) (d : ℕ) (w : AKLT.Defs.DirectionWord n)
  (i : Fin n) : AKLT.W.REC079.indexedReward X d w i = AKLT.W.REC079.pairReward X d w i
'AKLT.W.REC079.indexedReward_eq_pairReward' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.indexedReward_nonneg {n : ℕ} (X : AKLT.Defs.PairType) (d : ℕ) (w : AKLT.Defs.DirectionWord n)
  (i : Fin n) : 0 ≤ AKLT.W.REC079.indexedReward X d w i
'AKLT.W.REC079.indexedReward_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonicalBudget_nonneg {n : ℕ} (X : AKLT.Defs.PairType) (d : ℕ) (w : AKLT.Defs.DirectionWord n) :
  0 ≤ AKLT.W.REC079.canonicalBudget X d w
'AKLT.W.REC079.canonicalBudget_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.advanceStatus : AKLT.Defs.Status → AKLT.Defs.Status
AKLT.W.REC079.advanceStatus_ne_U (s : AKLT.Defs.Status) : AKLT.W.REC079.advanceStatus s ≠ AKLT.Defs.Status.U
'AKLT.W.REC079.advanceStatus_ne_U' does not depend on any axioms
AKLT.W.REC079.advanceStatus_twice (s : AKLT.Defs.Status) :
  AKLT.W.REC079.advanceStatus (AKLT.W.REC079.advanceStatus s) = AKLT.Defs.Status.X
'AKLT.W.REC079.advanceStatus_twice' does not depend on any axioms
AKLT.W.REC079.iterate_advance_X (k : ℕ) : AKLT.W.REC079.advanceStatus^[k] AKLT.Defs.Status.X = AKLT.Defs.Status.X
'AKLT.W.REC079.iterate_advance_X' depends on axioms: [propext, Quot.sound]
AKLT.W.REC079.iterate_advance_ne_U (s : AKLT.Defs.Status) {k : ℕ} (hk : 0 < k) :
  AKLT.W.REC079.advanceStatus^[k] s ≠ AKLT.Defs.Status.U
'AKLT.W.REC079.iterate_advance_ne_U' depends on axioms: [propext, Quot.sound]
AKLT.W.REC079.iterate_advance_removed (s : AKLT.Defs.Status) {k : ℕ} (hk : 2 ≤ k) :
  AKLT.W.REC079.advanceStatus^[k] s = AKLT.Defs.Status.X
'AKLT.W.REC079.iterate_advance_removed' depends on axioms: [propext, Quot.sound]
AKLT.W.REC079.traceNetwork_status {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (l : List AKLT.Defs.Plane)
  (x : AKLT.Defs.Plane) :
  (AKLT.Defs.traceNetwork D l).status x = AKLT.W.REC079.advanceStatus^[List.count x l.dropLast] (D.status x)
'AKLT.W.REC079.traceNetwork_status' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.wordVertices_departures {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n)
  (x : AKLT.Defs.Plane) : List.count x (AKLT.Defs.wordVertices u w).dropLast = AKLT.Defs.departureCount u w n x
'AKLT.W.REC079.wordVertices_departures' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.prefixNetwork_status {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G) (u : AKLT.Defs.Plane)
  (w : AKLT.Defs.DirectionWord n) (j : ℕ) (hj : j ≤ n) (x : AKLT.Defs.Plane) :
  (AKLT.Blueprint.Rec.prefixNetwork D u w j).status x =
    AKLT.W.REC079.advanceStatus^[AKLT.Defs.departureCount u w j x] (D.status x)
'AKLT.W.REC079.prefixNetwork_status' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.U_departure_first_visit {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (i : Fin n)
  (hU : (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i).status (AKLT.Defs.wordVertex u w ↑i) = AKLT.Defs.Status.U) :
  AKLT.Defs.wordRevisit u w i = false
'AKLT.W.REC079.U_departure_first_visit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.twice_departed_removed {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (j : ℕ) (hj : j ≤ n) (x : AKLT.Defs.Plane)
  (hx : 2 ≤ AKLT.Defs.departureCount u w j x) : (AKLT.Blueprint.Rec.prefixNetwork D u w j).status x = AKLT.Defs.Status.X
'AKLT.W.REC079.twice_departed_removed' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.target_status_unchanged {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u v : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (hfirst : ∀ j < n, AKLT.Defs.wordVertex u w j ≠ v) :
  (AKLT.Defs.traceNetwork D (AKLT.Defs.wordVertices u w)).status v = D.status v
'AKLT.W.REC079.target_status_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonicalWord_departureCount (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (j : ℕ) (hj : j ≤ n) (x : AKLT.Defs.Plane) :
  AKLT.Defs.departureCount AKLT.Defs.kernelStart (AKLT.W.REC079.canonicalWord p w) j
      ((AKLT.W.REC079.canonicalChart p).point x) =
    AKLT.Defs.departureCount p.u w j x
'AKLT.W.REC079.canonicalWord_departureCount' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.U_departure_canonical_first_visit (p : AKLT.Blueprint.Rec.PairData) {n : ℕ}
  (w : AKLT.Defs.DirectionWord n) (i : Fin n)
  (hU :
    (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).status (AKLT.Defs.wordVertex p.u w ↑i) =
      AKLT.Defs.Status.U) :
  AKLT.Defs.wordRevisit AKLT.Defs.kernelStart (AKLT.W.REC079.canonicalWord p w) i = false
'AKLT.W.REC079.U_departure_canonical_first_visit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.kernel_dead_removed (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n)
  (z : AKLT.Defs.Plane) (hz : AKLT.Defs.deadAt (AKLT.W.REC079.canonicalWord p w) i z) :
  (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).status ((AKLT.W.REC079.canonicalChart p).point.symm z) =
    AKLT.Defs.Status.X
'AKLT.W.REC079.kernel_dead_removed' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.traceCoefficient_concat {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (l : List AKLT.Defs.Plane)
  (x : AKLT.Defs.Plane) (r : List AKLT.Defs.Plane) :
  AKLT.Defs.traceCoefficient D (l ++ x :: r) =
    AKLT.Defs.traceCoefficient D (l ++ [x]) * AKLT.Defs.traceCoefficient (AKLT.Defs.traceNetwork D (l ++ [x])) (x :: r)
'AKLT.W.REC079.traceCoefficient_concat' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.traceCoefficient_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (l : List AKLT.Defs.Plane) : 0 ≤ AKLT.Defs.traceCoefficient D l
'AKLT.W.REC079.traceCoefficient_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.traceCoefficient_snoc {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G) (u : AKLT.Defs.Plane)
  (w : AKLT.Defs.DirectionWord n) (a : AKLT.Defs.Compass) :
  AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u (AKLT.Cert.H2.snoc w a)) =
    AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u w) *
      if
          (AKLT.Defs.traceNetwork D (AKLT.Defs.wordVertices u w)).status (AKLT.Defs.wordVertex u w n) =
            AKLT.Defs.Status.U then
        1 / 3
      else
        if
            (AKLT.Defs.traceNetwork D (AKLT.Defs.wordVertices u w)).status (AKLT.Defs.wordVertex u w n) =
              AKLT.Defs.Status.D then
          1 / 5
        else 0
'AKLT.W.REC079.traceCoefficient_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.trailBaseWeight_snoc {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n)
  (a : AKLT.Defs.Compass) :
  AKLT.Defs.trailBaseWeight u (AKLT.Cert.H2.snoc w a) =
    AKLT.Defs.trailBaseWeight u w *
      if 0 < AKLT.Defs.departureCount u w n (AKLT.Defs.wordVertex u w n) then 1 / 5 else 1 / 3
'AKLT.W.REC079.trailBaseWeight_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.traceCoefficient_le_baseWeight {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) :
  AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u w) ≤ AKLT.Defs.trailBaseWeight u w
'AKLT.W.REC079.traceCoefficient_le_baseWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.kernelOrdering_perm {n : ℕ} (w : AKLT.Defs.DirectionWord n) :
  (AKLT.Defs.kernelOrdering w).Perm (AKLT.Defs.firstVisitList w)
'AKLT.W.REC079.kernelOrdering_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.firstVisitList_nodup {n : ℕ} (w : AKLT.Defs.DirectionWord n) : (AKLT.Defs.firstVisitList w).Nodup
'AKLT.W.REC079.firstVisitList_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.kernelOrdering_nodup {n : ℕ} (w : AKLT.Defs.DirectionWord n) : (AKLT.Defs.kernelOrdering w).Nodup
'AKLT.W.REC079.kernelOrdering_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.kernelOrdering_mem_iff {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n) :
  i ∈ AKLT.Defs.kernelOrdering w ↔ AKLT.Defs.wordRevisit AKLT.Defs.kernelStart w i = false
'AKLT.W.REC079.kernelOrdering_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.U_departure_mem_ordering (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (i : Fin n)
  (hU :
    (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).status (AKLT.Defs.wordVertex p.u w ↑i) =
      AKLT.Defs.Status.U) :
  i ∈ AKLT.Defs.kernelOrdering (AKLT.W.REC079.canonicalWord p w)
'AKLT.W.REC079.U_departure_mem_ordering' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.long_filters_path_order {n : ℕ} (w : AKLT.Defs.DirectionWord n) :
  List.Pairwise (fun i j => ↑i < ↑j)
      (List.filter (AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming w) (AKLT.Defs.firstVisitList w)) ∧
    List.Pairwise (fun i j => ↑i < ↑j)
      (List.filter (fun i => !AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming w i) (AKLT.Defs.firstVisitList w))
'AKLT.W.REC079.long_filters_path_order' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.kernelOrdering_scopes {n : ℕ} (w : AKLT.Defs.DirectionWord n) :
  (n ≤ 12 → AKLT.Defs.kernelOrdering w = (AKLT.Defs.firstVisitList w).mergeSort (AKLT.Defs.shortOrderLE w)) ∧
    (12 < n →
      AKLT.Defs.kernelOrdering w =
        List.filter (AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming w) (AKLT.Defs.firstVisitList w) ++
          List.filter (fun i => !AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming w i) (AKLT.Defs.firstVisitList w))
'AKLT.W.REC079.kernelOrdering_scopes' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pairSignal {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (p : Finset AKLT.Defs.Plane) : ℝ
AKLT.W.REC079.pairSignal_nonneg {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (p : Finset AKLT.Defs.Plane) : 0 ≤ AKLT.W.REC079.pairSignal E τ p
'AKLT.W.REC079.pairSignal_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.localResponseReward (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (i : Fin n) : ℝ
AKLT.W.REC079.Residual_OrderedExposureV2 : Prop
AKLT.W.REC079.Residual_LocalEnvelopeV2 : Prop
AKLT.W.REC079.localResponseReward_nonneg (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (i : Fin n) : 0 ≤ AKLT.W.REC079.localResponseReward p w i
'AKLT.W.REC079.localResponseReward_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.localResponseReward_le (hlocal : AKLT.W.REC079.Residual_LocalEnvelopeV2) (p : AKLT.Blueprint.Rec.PairData)
  (d : ℕ) (hd : 1 ≤ d) (hdepth : ↑d ≤ p.depth) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w)
  (hend : AKLT.Defs.wordVertex p.u w n = p.v) (i : Fin n) :
  AKLT.W.REC079.localResponseReward p w i ≤ AKLT.W.REC079.indexedReward p.X d (AKLT.W.REC079.canonicalWord p w) i
'AKLT.W.REC079.localResponseReward_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.targetFactor_bounds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (v : AKLT.Defs.Plane) :
  0 ≤ AKLT.Blueprint.Rec.targetFactor D v ∧ AKLT.Blueprint.Rec.targetFactor D v ≤ 1
'AKLT.W.REC079.targetFactor_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.targetSummand (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n) : ℝ
AKLT.W.REC079.targetSummand_le_budget (hexposure : AKLT.W.REC079.Residual_OrderedExposureV2)
  (hlocal : AKLT.W.REC079.Residual_LocalEnvelopeV2) (hH1 : AKLT.Blueprint.Top.H1Statement)
  (p : AKLT.Blueprint.Rec.PairData) (d : ℕ) (hd : 1 ≤ d) (hdepth : ↑d ≤ p.depth) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w)
  (hend : AKLT.Defs.wordVertex p.u w n = p.v) :
  |AKLT.W.REC079.targetSummand p w| ≤ AKLT.W.REC079.canonicalBudget p.X d (AKLT.W.REC079.canonicalWord p w)
'AKLT.W.REC079.targetSummand_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.main_from_residuals (hexposure : AKLT.W.REC079.Residual_OrderedExposureV2)
  (hlocal : AKLT.W.REC079.Residual_LocalEnvelopeV2) : AKLT.Blueprint.Rec.TraceKernelLengthStatement
'AKLT.W.REC079.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.firstLength_eq_zero_of_no_closedTrail (p : AKLT.Blueprint.Rec.PairData) (n : ℕ)
  (hn : ∀ (w : AKLT.Defs.DirectionWord n), ¬AKLT.Defs.ClosedTrail p.X w) : AKLT.Blueprint.Rec.firstLength p n = 0
'AKLT.W.REC079.firstLength_eq_zero_of_no_closedTrail' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.traceKernelLength_small (p : AKLT.Blueprint.Rec.PairData) (d n : ℕ) (hn : n ≤ 1) :
  |AKLT.Blueprint.Rec.firstLength p n| ≤
    ∑ Y,
      ∑ s ∈ Finset.range (n + 2),
        ↑(AKLT.Defs.kernelLengthCoefficient p.X Y s n) * AKLT.Defs.responseEnvelope Y (↑d - ↑s)
'AKLT.W.REC079.traceKernelLength_small' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.remove_active {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite E y).active = E.active.erase y
'AKLT.W.REC079.remove_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.remove_present {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G) (y x z : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite E y).Present x z ↔ E.Present x z ∧ x ≠ y ∧ z ≠ y
'AKLT.W.REC079.remove_present' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.remove_auxiliary {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hE : E.Auxiliary) (hS : y ∉ AKLT.Defs.protectedSites G) : (AKLT.Defs.removeSite E y).Auxiliary
'AKLT.W.REC079.remove_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.invariant_remove_consistent {G : Finset AKLT.Defs.Plane} {E : AKLT.Defs.Network G}
  {y arrival : AKLT.Defs.Plane} (h : AKLT.W.REC096.PrefixInvariant E y arrival) (hE : E.Auxiliary)
  (hS : y ∉ AKLT.Defs.protectedSites G) : (AKLT.Defs.removeSite E y).Consistent
'AKLT.W.REC079.invariant_remove_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.invariant_nonarrival_present {G : Finset AKLT.Defs.Plane} {E : AKLT.Defs.Network G}
  {y arrival z : AKLT.Defs.Plane} (h : AKLT.W.REC096.PrefixInvariant E y arrival) (hy : y ∈ E.active)
  (hU : E.status y = AKLT.Defs.Status.U) (hz : z ∈ (AKLT.Defs.neighbours y).erase arrival ∩ E.active) : E.Present y z
'AKLT.W.REC079.invariant_nonarrival_present' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.neighbours_pair_distance {y a b : AKLT.Defs.Plane} (ha : a ∈ AKLT.Defs.neighbours y)
  (hb : b ∈ AKLT.Defs.neighbours y) (hab : a ≠ b) : AKLT.Defs.latticeDist a b = 2
'AKLT.W.REC079.neighbours_pair_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pair_type_pair {a b : AKLT.Defs.Plane} (hd : AKLT.Defs.latticeDist a b = 2) :
  AKLT.Defs.HasPairType (AKLT.Defs.responsePairType {a, b}) a b
'AKLT.W.REC079.pair_type_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.invariant_pair_closure {G : Finset AKLT.Defs.Plane} {E : AKLT.Defs.Network G}
  {y arrival a b : AKLT.Defs.Plane} (h : AKLT.W.REC096.PrefixInvariant E y arrival) (hE : E.Auxiliary)
  (hy : y ∈ E.active) (hS : y ∉ AKLT.Defs.protectedSites G) (hU : E.status y = AKLT.Defs.Status.U)
  (ha : a ∈ (AKLT.Defs.neighbours y).erase arrival ∩ E.active)
  (hb : b ∈ (AKLT.Defs.neighbours y).erase arrival ∩ E.active) (hab : a ≠ b) :
  (AKLT.Defs.removeSite E y).ResponsePair (AKLT.Defs.responsePairType {a, b}) a b y
'AKLT.W.REC079.invariant_pair_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.prefixDeparture (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ} (T : Finset AKLT.Defs.Plane)
  (w : AKLT.Defs.DirectionWord n) (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u T w) (i : Fin n) :
  AKLT.Blueprint.Rec.Departure
'AKLT.W.REC079.prefixDeparture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pair_closure : AKLT.Blueprint.Rec.PairClosureStatementV2
'AKLT.W.REC079.pair_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.covered_partition_bound (hH1 : AKLT.Blueprint.Top.H1Statement) (a : AKLT.Blueprint.Rec.Departure)
  (hU : a.D.status a.y = AKLT.Defs.Status.U) (incoming outgoing : AKLT.Defs.Compass) (ho : a.o = a.y + outgoing.step)
  (hcov : AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing) :
  (↑(AKLT.Defs.localThreshold (decide (outgoing = incoming))) *
      (AKLT.Defs.traceStep a.D a.y a.o).partition a.τ true fun x => 1) ≤
    a.D.partition a.τ true fun x => 1
'AKLT.W.REC079.covered_partition_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.covered_ratio : AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC079.covered_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.covered_integrated_lower : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2
'AKLT.W.REC079.covered_integrated_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.response_typed : AKLT.Blueprint.Top.ResponseTypedStatementV2
'AKLT.W.REC079.response_typed' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pairSetup (p : AKLT.Blueprint.Rec.PairData) (hu : p.u ∉ AKLT.Defs.protectedSites p.G) :
  AKLT.Blueprint.Rec.PairSetup
'AKLT.W.REC079.pairSetup' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonical_initial_direction (p : AKLT.Blueprint.Rec.PairSetup) :
  (AKLT.W.REC079.canonicalChart p.toPairData).direction p.incoming = AKLT.Defs.kernelIncoming
'AKLT.W.REC079.canonical_initial_direction' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonical_word_incoming (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (i : Fin n) :
  AKLT.Defs.wordIncoming AKLT.Defs.kernelIncoming (AKLT.W.REC079.canonicalWord p.toPairData w) i =
    (AKLT.W.REC079.canonicalChart p.toPairData).direction (AKLT.Defs.wordIncoming p.incoming w i)
'AKLT.W.REC079.canonical_word_incoming' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.canonical_word_straight (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (i : Fin n) :
  AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming (AKLT.W.REC079.canonicalWord p.toPairData w) i =
    AKLT.Defs.wordStraight p.incoming w i
'AKLT.W.REC079.canonical_word_straight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.chart_sub_step (F : AKLT.W.REC079.LatticeChart) (x : AKLT.Defs.Plane) (d : AKLT.Defs.Compass) :
  F.point (x - d.step) = F.point x - (F.direction d).step
'AKLT.W.REC079.chart_sub_step' depends on axioms: [propext, Quot.sound]
AKLT.W.REC079.canonical_arrival (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n) :
  (AKLT.W.REC079.canonicalChart p.toPairData).point (AKLT.W.REC096.arrivalSite p w ↑i) =
    AKLT.Defs.wordVertex AKLT.Defs.kernelStart (AKLT.W.REC079.canonicalWord p.toPairData w) ↑i -
      (AKLT.Defs.wordIncoming AKLT.Defs.kernelIncoming (AKLT.W.REC079.canonicalWord p.toPairData w) i).step
'AKLT.W.REC079.canonical_arrival' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.chart_neighbours (F : AKLT.W.REC079.LatticeChart) (y z : AKLT.Defs.Plane) :
  F.point z ∈ AKLT.Defs.neighbours (F.point y) ↔ z ∈ AKLT.Defs.neighbours y
'AKLT.W.REC079.chart_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.dot_comm_rec (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC079.dot_comm_rec' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pairSignal_pair {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (a b : AKLT.Defs.Plane) (hab : a ≠ b) :
  AKLT.W.REC079.pairSignal E τ {a, b} =
    |(E.expectation τ true fun n => AKLT.Defs.dot (n a) (n b)) -
        E.expectation τ false fun n => AKLT.Defs.dot (n a) (n b)|
'AKLT.W.REC079.pairSignal_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pairSignal_zero_of_inactive {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (a b : AKLT.Defs.Plane) (hab : a ≠ b) (ha : a ∉ E.active ∨ b ∉ E.active) :
  AKLT.W.REC079.pairSignal E τ {a, b} = 0
'AKLT.W.REC079.pairSignal_zero_of_inactive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.present_kernel_mem (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w) (i : Fin n)
  (hU :
    (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).status (AKLT.Defs.wordVertex p.u w ↑i) =
      AKLT.Defs.Status.U)
  {z : AKLT.Defs.Plane}
  (hz : (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).Present (AKLT.Defs.wordVertex p.u w ↑i) z) :
  (AKLT.W.REC079.canonicalChart p.toPairData).point z ∈
    insert (AKLT.Defs.wordVertex AKLT.Defs.kernelStart (AKLT.W.REC079.canonicalWord p.toPairData w) (↑i + 1))
      (AKLT.Defs.liveOtherNeighbours (AKLT.W.REC079.canonicalWord p.toPairData w) i)
'AKLT.W.REC079.present_kernel_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.kernel_member_nonarrival (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w) (i : Fin n)
  (hU :
    (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).status (AKLT.Defs.wordVertex p.u w ↑i) =
      AKLT.Defs.Status.U)
  {z : AKLT.Defs.Plane}
  (hz :
    z ∈
      insert (AKLT.Defs.wordVertex AKLT.Defs.kernelStart (AKLT.W.REC079.canonicalWord p.toPairData w) (↑i + 1))
        (AKLT.Defs.liveOtherNeighbours (AKLT.W.REC079.canonicalWord p.toPairData w) i)) :
  (AKLT.W.REC079.canonicalChart p.toPairData).point.symm z ∈
    (AKLT.Defs.neighbours (AKLT.Defs.wordVertex p.u w ↑i)).erase (AKLT.W.REC096.arrivalSite p w ↑i)
'AKLT.W.REC079.kernel_member_nonarrival' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.neighbour_pair_type_formula (y : AKLT.Defs.Plane) (a b : AKLT.Defs.Compass) (hab : a ≠ b) :
  AKLT.Defs.responsePairType {y + a.step, y + b.step} =
    if a = b.reverse then AKLT.Defs.PairType.B else AKLT.Defs.PairType.C
'AKLT.W.REC079.neighbour_pair_type_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.chart_pair_type (F : AKLT.W.REC079.LatticeChart) {y a b : AKLT.Defs.Plane}
  (ha : a ∈ AKLT.Defs.neighbours y) (hb : b ∈ AKLT.Defs.neighbours y) (hab : a ≠ b) :
  AKLT.Defs.responsePairType {F.point a, F.point b} = AKLT.Defs.responsePairType {a, b}
'AKLT.W.REC079.chart_pair_type' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.local_envelope : AKLT.W.REC079.Residual_LocalEnvelopeV2
'AKLT.W.REC079.local_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.passageFactor_one_le (straight : Bool) : 1 ≤ ↑(AKLT.Defs.passageFactor straight)
'AKLT.W.REC079.passageFactor_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.list_product_unit_bounds.{u_1} {ι : Type u_1} (c : ι → ℝ) (hc : ∀ (i : ι), 0 < c i ∧ c i ≤ 1)
  (l : List ι) : 0 < (List.map c l).prod ∧ (List.map c l).prod ≤ 1
'AKLT.W.REC079.list_product_unit_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.products_le_realExposure {n : ℕ} (w : AKLT.Defs.DirectionWord n) (b c r : Fin n → ℝ)
  (h :
    ∀ (i : Fin n),
      0 < b i ∧
        0 < c i ∧
          c i ≤ 1 ∧
            b i ≤ ↑(AKLT.Defs.passageFactor (AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming w i)) ∧
              |Real.log (c i) - Real.log (b i)| ≤ r i)
  (hr : ∀ (i : Fin n), 0 ≤ r i) (l : List (Fin n)) :
  |(List.map b l).prod - (List.map c l).prod| ≤ AKLT.W.REC079.realExposure w r l
'AKLT.W.REC079.products_le_realExposure' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.fullOrdering {n : ℕ} (w : AKLT.Defs.DirectionWord n) : List (Fin n)
'AKLT.W.REC079.fullOrdering' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.fullOrdering_perm {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (hk : (AKLT.Defs.kernelOrdering w).Perm (AKLT.Defs.firstVisitList w)) :
  (AKLT.W.REC079.fullOrdering w).Perm (List.finRange n)
'AKLT.W.REC079.fullOrdering_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.realExposure_append {n : ℕ} (w : AKLT.Defs.DirectionWord n) (r : Fin n → ℝ) (l t : List (Fin n))
  (ht : AKLT.W.REC079.realExposure w r t = 0) :
  AKLT.W.REC079.realExposure w r (l ++ t) = AKLT.W.REC079.realExposure w r l
'AKLT.W.REC079.realExposure_append' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.realExposure_zero {n : ℕ} (w : AKLT.Defs.DirectionWord n) (r : Fin n → ℝ) (l : List (Fin n))
  (hl : ∀ i ∈ l, r i = 0) : AKLT.W.REC079.realExposure w r l = 0
'AKLT.W.REC079.realExposure_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pair_kernel_mem (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w) (i : Fin n)
  (hU :
    (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).status (AKLT.Defs.wordVertex p.u w ↑i) =
      AKLT.Defs.Status.U)
  {a b : AKLT.Defs.Plane}
  (ha : (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).Present (AKLT.Defs.wordVertex p.u w ↑i) a)
  (hb : (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).Present (AKLT.Defs.wordVertex p.u w ↑i) b)
  (hab : a ≠ b) :
  {(AKLT.W.REC079.canonicalChart p.toPairData).point a, (AKLT.W.REC079.canonicalChart p.toPairData).point b} ∈
    AKLT.Defs.responsePairs (AKLT.W.REC079.canonicalWord p.toPairData w) i
'AKLT.W.REC079.pair_kernel_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.kernel_pair_signal (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n)
  (a b : AKLT.Defs.Plane) (hab : a ≠ b) :
  AKLT.W.REC079.pairSignal
      (AKLT.Defs.removeSite (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i) (AKLT.Defs.wordVertex p.u w ↑i))
      p.τ
      (Finset.image ⇑(AKLT.W.REC079.canonicalChart p).point.symm
        {(AKLT.W.REC079.canonicalChart p).point a, (AKLT.W.REC079.canonicalChart p).point b}) =
    |AKLT.Blueprint.Rec.pairResponse (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i) p.τ
        (AKLT.Defs.wordVertex p.u w ↑i) a b|
'AKLT.W.REC079.kernel_pair_signal' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.pair_sets_ne.{u_1} {α : Type u_1} [DecidableEq α] {a b c : α} (hba : b ≠ a) (hbc : b ≠ c) :
  {a, b} ≠ {a, c}
'AKLT.W.REC079.pair_sets_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.reward_single_le (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n)
  (hU :
    (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).status (AKLT.Defs.wordVertex p.u w ↑i) =
      AKLT.Defs.Status.U)
  (q : Finset AKLT.Defs.Plane) (hq : q ∈ AKLT.Defs.responsePairs (AKLT.W.REC079.canonicalWord p w) i) :
  ↑(AKLT.Defs.pairCoefficient (AKLT.W.REC079.canonicalWord p w) i q) *
      AKLT.W.REC079.pairSignal
        (AKLT.Defs.removeSite (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i) (AKLT.Defs.wordVertex p.u w ↑i))
        p.τ (Finset.image (⇑(AKLT.W.REC079.canonicalChart p).point.symm) q) ≤
    AKLT.W.REC079.localResponseReward p w i
'AKLT.W.REC079.reward_single_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.reward_three_le (p : AKLT.Blueprint.Rec.PairData) {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n)
  (hU :
    (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).status (AKLT.Defs.wordVertex p.u w ↑i) =
      AKLT.Defs.Status.U)
  (q₁ q₂ q₃ : Finset AKLT.Defs.Plane) (h₁ : q₁ ∈ AKLT.Defs.responsePairs (AKLT.W.REC079.canonicalWord p w) i)
  (h₂ : q₂ ∈ AKLT.Defs.responsePairs (AKLT.W.REC079.canonicalWord p w) i)
  (h₃ : q₃ ∈ AKLT.Defs.responsePairs (AKLT.W.REC079.canonicalWord p w) i) (h₁₂ : q₁ ≠ q₂) (h₁₃ : q₁ ≠ q₃)
  (h₂₃ : q₂ ≠ q₃) :
  have term := fun q =>
    ↑(AKLT.Defs.pairCoefficient (AKLT.W.REC079.canonicalWord p w) i q) *
      AKLT.W.REC079.pairSignal
        (AKLT.Defs.removeSite (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i) (AKLT.Defs.wordVertex p.u w ↑i))
        p.τ (Finset.image (⇑(AKLT.W.REC079.canonicalChart p).point.symm) q);
  term q₁ + term q₂ + term q₃ ≤ AKLT.W.REC079.localResponseReward p w i
'AKLT.W.REC079.reward_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.present_neighbour_cases (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = AKLT.Defs.Status.U) :
  (a.D.presentNeighbours a.y).card = 1 ∨
    (∃ f, a.D.presentNeighbours a.y = {a.o, f} ∧ a.o ≠ f) ∨
      ∃ f g, a.D.presentNeighbours a.y = {a.o, f, g} ∧ a.o ≠ f ∧ a.o ≠ g ∧ f ≠ g
'AKLT.W.REC079.present_neighbour_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.coefficient_outgoing_lower {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n)
  (q : Finset AKLT.Defs.Plane) (hq : AKLT.Defs.wordVertex AKLT.Defs.kernelStart w (↑i + 1) ∈ q) :
  AKLT.Defs.betaPrimeBound (AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming w i) ≤ AKLT.Defs.pairCoefficient w i q
'AKLT.W.REC079.coefficient_outgoing_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.prefix_coefficients (hH1 : AKLT.Blueprint.Top.H1Statement) (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ}
  (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w) (i : Fin n)
  (hU :
    (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i).status (AKLT.Defs.wordVertex p.u w ↑i) =
      AKLT.Defs.Status.U) :
  have a := AKLT.W.REC079.prefixDeparture p (insert p.v (AKLT.Defs.protectedSites p.G)) w hw i;
  have straight := AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming (AKLT.W.REC079.canonicalWord p.toPairData w) i;
  (∀ (f : AKLT.Defs.Plane),
      a.D.presentNeighbours a.y = {a.o, f} →
        a.o ≠ f →
          0 < AKLT.Defs.responseBetaPrime a.D a.τ a.y a.o f ∧
            AKLT.Defs.responseBetaPrime a.D a.τ a.y a.o f ≤ ↑(AKLT.Defs.betaPrimeBound straight)) ∧
    ∀ (f g : AKLT.Defs.Plane),
      a.D.presentNeighbours a.y = {a.o, f, g} →
        a.o ≠ f →
          a.o ≠ g →
            f ≠ g →
              0 < AKLT.Defs.responseAlpha a.D a.τ a.y a.o f g ∧
                AKLT.Defs.responseAlpha a.D a.τ a.y a.o f g ≤ ↑(AKLT.Defs.alphaBound straight) ∧
                  0 < AKLT.Defs.responseBeta a.D a.τ a.y a.o f g ∧
                    AKLT.Defs.responseBeta a.D a.τ a.y a.o f g ≤ ↑(AKLT.Defs.betaBound straight)
'AKLT.W.REC079.prefix_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.local_log_bound (hH1 : AKLT.Blueprint.Top.H1Statement) (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ}
  (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w) (i : Fin n) :
  |Real.log
          (AKLT.Defs.stepRatio (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i) p.τ false
            (AKLT.Defs.wordVertex p.u w ↑i) (AKLT.Defs.wordVertex p.u w (↑i + 1))) -
        Real.log
          (AKLT.Defs.stepRatio (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i) p.τ true
            (AKLT.Defs.wordVertex p.u w ↑i) (AKLT.Defs.wordVertex p.u w (↑i + 1)))| ≤
    AKLT.W.REC079.localResponseReward p.toPairData w i
'AKLT.W.REC079.local_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.prefix_ratio_le (hH1 : AKLT.Blueprint.Top.H1Statement) (p : AKLT.Blueprint.Rec.PairSetup) {n : ℕ}
  (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w) (i : Fin n) :
  AKLT.Defs.stepRatio (AKLT.Blueprint.Rec.prefixNetwork p.normalized p.u w ↑i) p.τ true (AKLT.Defs.wordVertex p.u w ↑i)
      (AKLT.Defs.wordVertex p.u w (↑i + 1)) ≤
    ↑(AKLT.Defs.passageFactor
        (AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming (AKLT.W.REC079.canonicalWord p.toPairData w) i))
'AKLT.W.REC079.prefix_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.ordered_exposure : AKLT.W.REC079.Residual_OrderedExposureV2
'AKLT.W.REC079.ordered_exposure' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC079.main : AKLT.Blueprint.Rec.TraceKernelLengthStatement
'AKLT.W.REC079.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- STATUS: PROVED FROM DEPS.
- Delivered `AKLT/W/REC079/Main.lean` with exact theorem `AKLT.W.REC079.main`.
- Exact type: `AKLT.Blueprint.Rec.TraceKernelLengthStatement`.
- Both earlier local residuals are discharged; no remaining leaf assumptions.
- Uses repaired `Top.ResponseTypedStatementV2` and non-arrival-only response-pair closure.
- Preserves the single chart and fixed short/long kernel ordering scopes.
- Inactive endpoints contribute zero; beta-prime/beta comparison and actual shifts are proved.
- Additional proved leaves: REC090, REC091, REC097; optional index rows in `additional-leaves.tsv`.
- Also exports a proved `Top.ResponseTypedStatementV2` interface.
- Required Main build passed (13.65 s); complete declaration audit passed (4.92 s).
- All exported theorem axioms are contained in `[propext, Classical.choice, Quot.sound]`.
- Source edits are confined to `AKLT/W/REC079/`; reports are confined to the assigned report directory.
- Open names: none. Limitations or deviations affecting the conclusion: none.
- Orchestrator decision: accept REC079 and optionally harvest the additional closed leaf proofs.
