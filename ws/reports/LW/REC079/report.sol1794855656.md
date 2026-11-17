STATUS: PARTIAL

The exact requested theorem `AKLT.W.REC079.main : AKLT.Blueprint.Rec.TraceKernelLengthStatement` is **not proved or defined**. The delivered `Main.lean` compiles and proves the frozen statement from two explicit, closed local residual propositions. Neither residual is asserted as a theorem or introduced as an axiom. No counterexample or missing mathematical premise has been established.

## Files

All Lean changes are confined to `AKLT/W/REC079/`. No existing statement, definition, library, or package file was edited. The earlier report remains in `report.luna.md`.

| File | Contents |
| --- | --- |
| [Main.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Main.lean) | Conditional assembly of the frozen statement; unconditional length-zero and length-one comparison. |
| [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Geometry.lean) | Signed coordinate permutations, translations, lattice-distance preservation, and a chart for every designated pair. |
| [TraceGeometry.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/TraceGeometry.lean) | One fixed chart per pair, injective word transport, base-weight invariance, and the actual-trail to ClosedTrail embedding. |
| [TraceStatus.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/TraceStatus.lean) | Exact departure-count status formula, true-U first visits, actual removal of kernel-dead sites, unchanged target status, and trace-coefficient domination. |
| [Ordering.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Ordering.lean) | First-visit permutation, no repetitions, true-U membership, increasing path indices within long-order filters, and the exact short/long scopes. |
| [KernelAlgebra.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/KernelAlgebra.lean) | Real exposure linearity and monotonicity, insertion of extra first visits, and the exact finite kernel regrouping identity. |
| [KernelSupport.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/KernelSupport.lean) | Actual shifts lie in range(n+2), regrouping individual pair rewards by type and shift, and all required nonnegativity results. |
| [LocalComparison.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/LocalComparison.lean) | The two open residuals, ordinary real response rewards, and their conditional pointwise comparison. |
| [Audit.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Audit.lean) | Types for all 82 public declarations and `#print axioms` for all 64 public theorems. |

Reused proved infrastructure: `AKLT.Cert.H2.Words` and `AKLT.Cert.H2.Frames`. No unproved blueprint leaf is used as a lemma.

## Principal exported declarations

All names below are in namespace `AKLT.W.REC079`. Complete kernel-printed statements for every exported declaration appear in the audit appendix below and in [build-audit.log](/home/ubuntu/aklt/reports/LW/REC079/build-audit.log). The machine-readable inventory is [exports.tsv](/home/ubuntu/aklt/reports/LW/REC079/exports.tsv).

```lean
theorem main_from_residuals
    (hexposure : Residual_OrderedExposureV2)
    (hlocal : Residual_LocalEnvelopeV2) :
    AKLT.Blueprint.Rec.TraceKernelLengthStatement

theorem traceKernelLength_small
    (p : AKLT.Blueprint.Rec.PairData) (d n : ℕ) (hn : n ≤ 1) :
    |AKLT.Blueprint.Rec.firstLength p n| ≤
      ∑ Y : AKLT.Defs.PairType, ∑ s ∈ Finset.range (n + 2),
        (AKLT.Defs.kernelLengthCoefficient p.X Y s n : ℝ) *
          AKLT.Defs.responseEnvelope Y ((d : ℤ) - s)
```

The main conditional proof uses the triangle inequality, the single injective canonical word map, nonnegative budgets for omitted words, and the exact finite kernel identity. Its open hypotheses no longer contain the full sum over true trails or the full kernel coefficient inequality.

Other substantive proved components include `pair_chart`, `target_trail_closed`, `prefixNetwork_status`, `U_departure_first_visit`, `U_departure_mem_ordering`, `kernel_dead_removed`, `target_status_unchanged`, `traceCoefficient_le_baseWeight`, `realExposure_filter_le`, `responsePair_shift_le`, `indexedReward_eq_pairReward`, and `kernel_bound_eq_sum`.

## Open residuals and blockers

The following are closed `def ... : Prop` declarations, with all instance parameters quantified. The notation uses the same opens as `LocalComparison.lean`.

```lean
def Residual_OrderedExposureV2 : Prop :=
  AKLT.Blueprint.Top.H1Statement → ∀ p : PairData, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n = p.v →
    |traceRatio p.normalized p.τ true (wordVertices p.u w) -
      traceRatio p.normalized p.τ false (wordVertices p.u w)| ≤
      realExposure (canonicalWord p w) (localResponseReward p w)
        (kernelOrdering (canonicalWord p w))

def Residual_LocalEnvelopeV2 : Prop :=
  ∀ p : PairData, ∀ d : ℕ, 1 ≤ d → (d : ℕ∞) ≤ p.depth →
    ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n = p.v → ∀ i : Fin n,
    (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U →
    ∀ q ∈ responsePairs (canonicalWord p w) i,
      pairSignal (removeSite (prefixNetwork p.normalized p.u w i.val)
        (wordVertex p.u w i.val)) p.τ (q.image (canonicalChart p).point.symm) ≤
      responseEnvelope (responsePairType q) ((d : ℤ) - pairShift p.X q)
```

`Residual_OrderedExposureV2` remains open. It is independent of depth and envelopes and concerns one trace. It requires proving the positive partition-ratio identities and the ordered logarithmic exposure inequality, deriving the repaired `Top.ResponseTypedStatementV2` bounds from H1, and comparing the actual two-/three-neighbour coefficients with the canonical alpha/beta/beta-prime branches. True-U membership in the fixed order, extra-factor monotonicity, and the base-weight comparison have been proved separately. The short rational-score ordering has not been replaced by the long straight-first order.

`Residual_LocalEnvelopeV2` remains open. It concerns one kernel pair at one actual U departure. It requires ordinary closure after deleting the live endpoint, the non-arrival-only response-pair clause, type preservation in the chosen chart, transfer of protected depth by the actual maximum shift, and boundedness of the ordinary-domain response supremum. An actually removed endpoint has zero spin response; establishing and combining that case with ordinary closure is part of this residual. The kernel-dead implies actually removed direction, the finite shift range, and envelope nonnegativity have been proved.

These residuals are explicit remaining proof work, not additional assumptions claimed to follow from a previously proved library theorem. In particular, this delivery does not satisfy the unconditional exact-type check for `AKLT.W.REC079.main`.

## Build and soundness checks

Commands were run with `PATH="$HOME/.elan/bin:$PATH"` in `/home/ubuntu/aklt/wt/LW_REC079`.

- `lake build AKLT.W.REC079.Main` — passed; final recorded build took 14.95 seconds, including recompilation of the changed Ordering, LocalComparison, and Main modules. [Log](/home/ubuntu/aklt/reports/LW/REC079/build-main.log).
- `lake build AKLT.W.REC079.Audit` — passed in 9.34 seconds. [Log](/home/ubuntu/aklt/reports/LW/REC079/build-audit.log).
- All 64 exported theorems were checked with `#print axioms`; every axiom set is a subset of `{propext, Classical.choice, Quot.sound}`. The full output is in [axioms.txt](/home/ubuntu/aklt/reports/LW/REC079/axioms.txt) and the appendix below.
- No forbidden proof placeholders, added axioms, non-kernel decision procedures, unsafe declarations, effectful Lean commands, or unlimited heartbeat settings occur in the delivered source.

Representative axiom output:

```text
'AKLT.W.REC079.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC079.traceKernelLength_small' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Complete exported statements and axiom output

The following is the successful Audit module's output, with Lake location prefixes removed. It includes every public declaration's type and every public theorem's axiom output.

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
```

## ORCH-SUMMARY

- STATUS: PARTIAL. Exact unconditional `AKLT.W.REC079.main` is absent.
- Delivered compiled `AKLT.W.REC079.main_from_residuals` with exactly two explicit local residual hypotheses.
- Open: `AKLT.W.REC079.Residual_OrderedExposureV2`.
- Open: `AKLT.W.REC079.Residual_LocalEnvelopeV2`.
- Proved fixed canonical chart and injective transport of all target-reaching true trails.
- Proved departure-count status formula, true-U first visits, actual kernel-dead removals, target-law preservation, and base-weight domination.
- Proved correct first-visit enumeration and fixed short/long ordering scopes.
- Proved finite type/shift and word regrouping, nonnegative budgets, and final conditional sum assembly.
- Proved the frozen comparison unconditionally for lengths zero and one.
- No counterexample or under-premise claim; numerical frozen conclusion unchanged.
- Main build passed (14.95 s); Audit build passed (9.34 s); all 64 theorem axiom audits use only permitted axioms.
- No other directory's source or existing blueprint was edited; no sub-agents used.
- Orchestrator must discharge both exact residuals from their own quantified hypotheses and then define the requested unconditional `main`.
