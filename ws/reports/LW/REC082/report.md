STATUS: PARTIAL

The required unconditional declaration
`AKLT.W.REC082.main : AKLT.Blueprint.Rec.PairResponseSplitStatement`
is **not delivered**. The compiled fallback is
`AKLT.W.REC082.main_of_residual : Residual_FiniteNumeratorExpansion → PairResponseSplitStatement`.
The exact-type checker for the requested unconditional `main` will therefore still fail.

Compared with the earlier attempt, normalization invariance is proved, and the terminal-factor assumption is eliminated by a proved weighted identity. Both local U/D moment identities are also proved directly. The remaining open obligation is a single unnormalized finite expansion.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/Main.lean) — The single transparent residual, its normalized one-pin consequence, and the conditional response split.
- [Normalization.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/Normalization.lean) — Removal of the harmless centre flag preserves present bonds, partitions, expectations, and auxiliary rules.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/Geometry.lean) — Four-neighbour geometry, absence of legs outside the protected layer, and admissible pair endpoints.
- [Moments.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/Moments.lean) — Explicit icosahedron unit norm, nonnegative site weights, total site mass, and the D norm-square moment.
- [LocalMoments.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/LocalMoments.lean) — Direct proofs of UStepMomentStatement and DStepMomentStatement from the finite support.
- [Partition.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/Partition.lean) — Nonnegative finite partition weights, zero-mass observables, and cancellation of trace ratios with expectations.
- [Trail.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/Trail.lean) — Trace monotonicity, consumed-bond absence, first-hit law preservation, and isolation of a degree-one target.
- [IndependentSite.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/IndependentSite.lean) — Finite coordinate disintegration and the U/D terminal numerator identities.
- [Terminal.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/Terminal.lean) — The common terminal numerator factor and the weighted factor actually required by the split.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC082/AKLT/W/REC082/Audit.lean) — Type checks and #print axioms commands for all 71 named exported theorems.

Only files in `AKLT/W/REC082/` and this report directory were written. Frozen statements and existing files outside this leaf directory were not changed. No other blueprint leaf is used as a proved lemma or an implicit assumption. The old report remains in `report.luna.md`.

## Main exported statements

All names below are in `AKLT.W.REC082`.

```lean
theorem main_of_residual
    (hExpansion : Residual_FiniteNumeratorExpansion) :
    AKLT.Blueprint.Rec.PairResponseSplitStatement
```

This theorem divides the single-pin numerator expansions, subtracts them, and partitions the same finite trail set by whether its endpoint is `p.v`.

`target_partition_factor` proves, for a stopped trail ending at `p.v`, with `E = traceNetwork p.normalized (wordVertices p.u w)`,

```lean
E.partition p.τ b (fun a => normSq (a p.v)) =
  targetFactor p.D p.v * E.partition p.τ b (fun _ => 1)
```

Its hypotheses are only `p : PairData`, `p.v ∉ protectedSites p.G`, the stopped-trail condition, and the endpoint equality. In the U case the norm-square is one at every nonzero-weight atom. In the D case, the target's initial degree is at most one and its arrival bond is absent after the trace, so its law factors with norm-square moment `3/5`.

`target_weighted_factor` consequently proves the terminal identity multiplied by `traceRatio`, which is exactly what the response split needs. This does not assume that any partition denominator is nonzero. It does **not** claim the stronger unweighted normalized terminal expectation identity from the previous attempt's residual.

`u_step_moment : AKLT.Blueprint.Rec.UStepMomentStatement` and
`d_step_moment : AKLT.Blueprint.Rec.DStepMomentStatement` are unconditional proofs of the two local finite moment identities. They are available to a continuation of the remaining expansion proof.

## Exact open obligation

```lean
def Residual_FiniteNumeratorExpansion : Prop :=
  ∀ p : PairData, p.u ∉ protectedSites p.G → p.v ∉ protectedSites p.G →
    ∀ b : Bool,
      p.normalized.partition p.τ b (fun a => dot (a p.u) (a p.v)) =
        stoppedSum p.normalized p.u (insert p.v (protectedSites p.G))
          (fun n w =>
            (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) *
              (traceNetwork p.normalized (wordVertices p.u w)).partition p.τ b
                (fun a => dot (a (wordVertex p.u w n)) (a p.v)))
```

This is a closed `def … : Prop`, not an assertion that has been proved. It contains one pin choice at a time and no expectation normalization, target-factor claim, response subtraction, or normalization invariance. Those parts are handled by proved declarations.

The missing proof must lift the proved one-site U/D identities through `Network.partition`, including the change of the active-site index type at a D departure. It must then iterate over unused present bonds and identify the resulting branches, with their evolving coefficients, with the finite `stoppedNetworkTrails` sum bounded by `p.normalized.bonds.card`. The delivered trace lemmas prove monotonicity and that traversed bonds disappear, but do not yet prove the full unused-bond preservation, admissible-prefix invariant, and branch-enumeration correspondence needed for that iteration.

No counterexample or missing mathematical premise was established; this is an unfinished proof, not a FALSE finding.

## Validation

- `$HOME/.elan/bin/lake build AKLT.W.REC082.Main` — passed, **10.14 s wall**, including the final Main rebuild (Lean module time 3.3 s). All helper modules are imported by Main.
- `$HOME/.elan/bin/lake env lean AKLT/W/REC082/Audit.lean` — passed, **3.94 s wall**. The audit also type-checks `Residual_FiniteNumeratorExpansion → PairResponseSplitStatement` via `main_of_residual`.
- All 71 named exported theorems were audited with `#print axioms`; every dependency is among `propext`, `Classical.choice`, and `Quot.sound`.
- The forbidden-construct scan was clean. The U moment proof uses a finite `maxHeartbeats 2000000` limit.
- The build has four non-failing tactic-sequencing linter warnings in `d_step_moment`.
- Full command output is in [build.log](/home/ubuntu/aklt/reports/LW/REC082/build.log) and [audit.log](/home/ubuntu/aklt/reports/LW/REC082/audit.log).

## All exported theorem statements

The following is the complete `#check` output, preserving the kernel-reported types and explicit assumptions:

```text
AKLT.W.REC082.removed_not_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) {c : AKLT.Defs.Plane}
  (hc : D.status c = AKLT.Defs.Status.X) : c ∉ D.active
AKLT.W.REC082.normalizeStart_present {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (u c x y : AKLT.Defs.Plane)
  (hc : D.status c = AKLT.Defs.Status.X) : (AKLT.Blueprint.Rec.normalizeStart D u c).Present x y ↔ D.Present x y
AKLT.W.REC082.normalizeStart_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (u c : AKLT.Defs.Plane)
  (hc : D.status c = AKLT.Defs.Status.X) : (AKLT.Blueprint.Rec.normalizeStart D u c).bonds = D.bonds
AKLT.W.REC082.normalizeStart_presentNeighbours {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (u c x : AKLT.Defs.Plane) (hc : D.status c = AKLT.Defs.Status.X) :
  (AKLT.Blueprint.Rec.normalizeStart D u c).presentNeighbours x = D.presentNeighbours x
AKLT.W.REC082.normalizeStart_partition {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (u c : AKLT.Defs.Plane)
  (hc : D.status c = AKLT.Defs.Status.X) (τ : AKLT.Defs.PinAssignment G) (b : Bool)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (AKLT.Blueprint.Rec.normalizeStart D u c).partition τ b f = D.partition τ b f
AKLT.W.REC082.normalizeStart_expectation {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (u c : AKLT.Defs.Plane)
  (hc : D.status c = AKLT.Defs.Status.X) (τ : AKLT.Defs.PinAssignment G) (b : Bool)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (AKLT.Blueprint.Rec.normalizeStart D u c).expectation τ b f = D.expectation τ b f
AKLT.W.REC082.normalizeStart_auxiliary {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (u c : AKLT.Defs.Plane)
  (hc : D.status c = AKLT.Defs.Status.X) (hD : D.Auxiliary) : (AKLT.Blueprint.Rec.normalizeStart D u c).Auxiliary
AKLT.W.REC082.pair_auxiliary (p : AKLT.Blueprint.Rec.PairData) : p.D.Auxiliary
AKLT.W.REC082.pair_c_removed (p : AKLT.Blueprint.Rec.PairData) : p.D.status p.c = AKLT.Defs.Status.X
AKLT.W.REC082.pair_u_active (p : AKLT.Blueprint.Rec.PairData) : p.u ∈ p.D.active
AKLT.W.REC082.pair_v_active (p : AKLT.Blueprint.Rec.PairData) : p.v ∈ p.D.active
AKLT.W.REC082.normalized_targetFactor (p : AKLT.Blueprint.Rec.PairData) :
  AKLT.Blueprint.Rec.targetFactor p.normalized p.v = AKLT.Blueprint.Rec.targetFactor p.D p.v
AKLT.W.REC082.normalized_auxiliary (p : AKLT.Blueprint.Rec.PairData) : p.normalized.Auxiliary
AKLT.W.REC082.normalized_expectation (p : AKLT.Blueprint.Rec.PairData) (b : Bool)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) : p.normalized.expectation p.τ b f = p.D.expectation p.τ b f
AKLT.W.REC082.adjacent_iff_mem_neighbours (x y : AKLT.Defs.Plane) : AKLT.Defs.Adjacent x y ↔ y ∈ AKLT.Defs.neighbours x
AKLT.W.REC082.neighbours_card (x : AKLT.Defs.Plane) : (AKLT.Defs.neighbours x).card = 4
AKLT.W.REC082.neighbours_degree_of_removed {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  {u c : AKLT.Defs.Plane} (hc : D.status c = AKLT.Defs.Status.X) (huc : AKLT.Defs.Adjacent u c) :
  (D.presentNeighbours u).card ≤ 3
AKLT.W.REC082.no_originalLegs {G : Finset AKLT.Defs.Plane} {x : AKLT.Defs.Plane} (hx : x ∉ AKLT.Defs.protectedSites G) :
  {e ∈ AKLT.Defs.originalLegs G | e.1 = x} = ∅
AKLT.W.REC082.pair_ne (p : AKLT.Blueprint.Rec.PairData) : p.u ≠ p.v
AKLT.W.REC082.pair_start (p : AKLT.Blueprint.Rec.PairData) (hu : p.u ∉ AKLT.Defs.protectedSites p.G) :
  p.D.AdmissibleStart p.u
AKLT.W.REC082.pair_target (p : AKLT.Blueprint.Rec.PairData) (hv : p.v ∉ AKLT.Defs.protectedSites p.G) :
  AKLT.Defs.AdmissibleTarget p.D p.v
AKLT.W.REC082.normalized_start (p : AKLT.Blueprint.Rec.PairData) (hu : p.u ∉ AKLT.Defs.protectedSites p.G) :
  p.normalized.AdmissibleStart p.u
AKLT.W.REC082.normalized_target (p : AKLT.Blueprint.Rec.PairData) (hv : p.v ∉ AKLT.Defs.protectedSites p.G) :
  AKLT.Defs.AdmissibleTarget p.normalized p.v
AKLT.W.REC082.goldenRatio_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
AKLT.W.REC082.icoRadius_pos : 0 < AKLT.Defs.icoRadius
AKLT.W.REC082.icoRadius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
AKLT.W.REC082.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
AKLT.W.REC082.spinVector_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
AKLT.W.REC082.spinWeight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
AKLT.W.REC082.d_norm_moment : AKLT.Defs.siteFunctional AKLT.Defs.Status.D AKLT.Defs.normSq = 3 / 5
AKLT.W.REC082.site_mass (s : AKLT.Defs.Status) (hs : s = AKLT.Defs.Status.U ∨ s = AKLT.Defs.Status.D) :
  (AKLT.Defs.siteFunctional s fun x => 1) = 1
AKLT.W.REC082.inv_radius_sq : AKLT.Defs.icoRadius⁻¹ ^ 2 = (3 - AKLT.Defs.goldenRatio) / 5
AKLT.W.REC082.inv_radius_fourth : AKLT.Defs.icoRadius⁻¹ ^ 4 = (2 - AKLT.Defs.goldenRatio) / 5
AKLT.W.REC082.u_step_moment : AKLT.Blueprint.Rec.UStepMomentStatement
AKLT.W.REC082.d_step_moment : AKLT.Blueprint.Rec.DStepMomentStatement
AKLT.W.REC082.normSq_nonneg (a : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq a
AKLT.W.REC082.normSq_add (a b : AKLT.Defs.Vec3) :
  AKLT.Defs.normSq (a + b) = AKLT.Defs.normSq a + 2 * AKLT.Defs.dot a b + AKLT.Defs.normSq b
AKLT.W.REC082.ball_factor_nonneg (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  0 ≤ 1 + AKLT.Defs.dot a b
AKLT.W.REC082.spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (n : ↥D.active → AKLT.Defs.SpinLetter)
  (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins n x) ≤ 1
AKLT.W.REC082.partition_eq_sum_weight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = ∑ n, AKLT.W.REC082.partitionWeight D τ b n * f (D.spins n)
AKLT.W.REC082.partitionWeight_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) :
  0 ≤ AKLT.W.REC082.partitionWeight D τ b n
AKLT.W.REC082.partition_zero_of_mass_zero {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (h : (D.partition τ b fun x => 1) = 0)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) : D.partition τ b f = 0
AKLT.W.REC082.traceRatio_mul_expectation {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (w : List AKLT.Defs.Plane) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  AKLT.Defs.traceRatio D τ b w * (AKLT.Defs.traceNetwork D w).expectation τ b f =
    (AKLT.Defs.traceNetwork D w).partition τ b f / D.partition τ b fun x => 1
AKLT.W.REC082.traceRatio_mul_terminal_of_partition {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (w : List AKLT.Defs.Plane) (v : AKLT.Defs.Plane) (η : ℝ)
  (h :
    ((AKLT.Defs.traceNetwork D w).partition τ b fun a => AKLT.Defs.normSq (a v)) =
      η * (AKLT.Defs.traceNetwork D w).partition τ b fun x => 1) :
  (AKLT.Defs.traceRatio D τ b w * (AKLT.Defs.traceNetwork D w).expectation τ b fun a => AKLT.Defs.normSq (a v)) =
    AKLT.Defs.traceRatio D τ b w * η
AKLT.W.REC082.adjacent_symm {x y : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x y) : AKLT.Defs.Adjacent y x
AKLT.W.REC082.present_symm {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x y : AKLT.Defs.Plane}
  (h : D.Present x y) : D.Present y x
AKLT.W.REC082.present_mem_neighbours {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x y : AKLT.Defs.Plane}
  (h : D.Present x y) : y ∈ D.presentNeighbours x
AKLT.W.REC082.traceStep_active_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  (AKLT.Defs.traceStep D y o).active ⊆ D.active
AKLT.W.REC082.traceStep_kept_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x : AKLT.Defs.Plane) :
  (AKLT.Defs.traceStep D y o).kept x ⊆ D.kept x
AKLT.W.REC082.traceStep_present_mono {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x z : AKLT.Defs.Plane)
  (h : (AKLT.Defs.traceStep D y o).Present x z) : D.Present x z
AKLT.W.REC082.traceStep_not_present {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  ¬(AKLT.Defs.traceStep D y o).Present y o
AKLT.W.REC082.traceNetwork_present_mono {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (l : List AKLT.Defs.Plane) (x z : AKLT.Defs.Plane) (h : (AKLT.Defs.traceNetwork D l).Present x z) : D.Present x z
AKLT.W.REC082.traceNetwork_not_present_edge {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (l : List AKLT.Defs.Plane) (i : ℕ) (hi : i + 1 < l.length) : ¬(AKLT.Defs.traceNetwork D l).Present l[i] l[i + 1]
AKLT.W.REC082.traceNetwork_status_of_not_departed {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (l : List AKLT.Defs.Plane) (v : AKLT.Defs.Plane) (hv : v ∉ l.dropLast) :
  (AKLT.Defs.traceNetwork D l).status v = D.status v
AKLT.W.REC082.wordVertex_zero {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) :
  AKLT.Defs.wordVertex u w 0 = u
AKLT.W.REC082.wordVertices_length {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) :
  (AKLT.Defs.wordVertices u w).length = n + 1
AKLT.W.REC082.wordVertices_getElem {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (i : ℕ)
  (hi : i < (AKLT.Defs.wordVertices u w).length) : (AKLT.Defs.wordVertices u w)[i] = AKLT.Defs.wordVertex u w i
AKLT.W.REC082.stopped_target_not_departed {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {u v : AKLT.Defs.Plane}
  {n : ℕ} {w : AKLT.Defs.DirectionWord n}
  (hw : AKLT.Defs.StoppedNetworkTrail D u (insert v (AKLT.Defs.protectedSites G)) w) :
  v ∉ (AKLT.Defs.wordVertices u w).dropLast
AKLT.W.REC082.stopped_target_status {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {u v : AKLT.Defs.Plane}
  {n : ℕ} {w : AKLT.Defs.DirectionWord n}
  (hw : AKLT.Defs.StoppedNetworkTrail D u (insert v (AKLT.Defs.protectedSites G)) w) :
  (AKLT.Defs.traceNetwork D (AKLT.Defs.wordVertices u w)).status v = D.status v
AKLT.W.REC082.stopped_target_isolated {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {u v : AKLT.Defs.Plane}
  {n : ℕ} {w : AKLT.Defs.DirectionWord n} (huv : u ≠ v) (hdeg : (D.presentNeighbours v).card ≤ 1)
  (hw : AKLT.Defs.StoppedNetworkTrail D u (insert v (AKLT.Defs.protectedSites G)) w)
  (he : AKLT.Defs.wordVertex u w n = v) :
  (AKLT.Defs.traceNetwork D (AKLT.Defs.wordVertices u w)).presentNeighbours v = ∅
AKLT.W.REC082.independent_site_sum.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (i : ι)
  (w : ι → AKLT.Defs.SpinLetter → ℝ) (F : (ι → AKLT.Defs.SpinLetter) → ℝ)
  (hF : ∀ (m n : ι → AKLT.Defs.SpinLetter), (∀ (x : ι), x ≠ i → m x = n x) → F m = F n) (g : AKLT.Defs.SpinLetter → ℝ) :
  ∑ n, (∏ x, w x (n x)) * F n * g (n i) =
    (∑ n, (∏ x, w (↑x) (n x)) * F ((Equiv.funSplitAt i AKLT.Defs.SpinLetter).symm (none, n))) * ∑ j, w i j * g j
AKLT.W.REC082.independent_site_moment.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (i : ι)
  (w : ι → AKLT.Defs.SpinLetter → ℝ) (F : (ι → AKLT.Defs.SpinLetter) → ℝ)
  (hF : ∀ (m n : ι → AKLT.Defs.SpinLetter), (∀ (x : ι), x ≠ i → m x = n x) → F m = F n) (g : AKLT.Defs.SpinLetter → ℝ)
  (η : ℝ) (hmass : ∑ j, w i j = 1) (hmoment : ∑ j, w i j * g j = η) :
  ∑ n, (∏ x, w x (n x)) * F n * g (n i) = η * ∑ n, (∏ x, w x (n x)) * F n
AKLT.W.REC082.partitionWeight_eq {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) :
  AKLT.W.REC082.partitionWeight D τ b n =
    (∏ x, AKLT.Defs.spinWeight (D.status ↑x) (n x)) * AKLT.W.REC082.interactionWeight D τ b n
AKLT.W.REC082.spins_eq_of_agree_away {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (v x : AKLT.Defs.Plane)
  (m n : ↥D.active → AKLT.Defs.SpinLetter) (hmn : ∀ (i : ↥D.active), ↑i ≠ v → m i = n i) (hx : x ≠ v) :
  D.spins m x = D.spins n x
AKLT.W.REC082.interactionWeight_independent {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (v : AKLT.Defs.Plane) (hiso : D.presentNeighbours v = ∅)
  (hv : v ∉ AKLT.Defs.protectedSites G) (m n : ↥D.active → AKLT.Defs.SpinLetter)
  (hmn : ∀ (i : ↥D.active), ↑i ≠ v → m i = n i) :
  AKLT.W.REC082.interactionWeight D τ b m = AKLT.W.REC082.interactionWeight D τ b n
AKLT.W.REC082.partition_norm_U {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (v : AKLT.Defs.Plane) (hv : v ∈ D.active) (hs : D.status v = AKLT.Defs.Status.U) :
  (D.partition τ b fun a => AKLT.Defs.normSq (a v)) = D.partition τ b fun x => 1
AKLT.W.REC082.partition_norm_D {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (v : AKLT.Defs.Plane) (hv : v ∈ D.active) (hs : D.status v = AKLT.Defs.Status.D)
  (hiso : D.presentNeighbours v = ∅) (hvp : v ∉ AKLT.Defs.protectedSites G) :
  (D.partition τ b fun a => AKLT.Defs.normSq (a v)) = 3 / 5 * D.partition τ b fun x => 1
AKLT.W.REC082.target_partition_factor (p : AKLT.Blueprint.Rec.PairData) (hv : p.v ∉ AKLT.Defs.protectedSites p.G)
  (n : ℕ) (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w)
  (he : AKLT.Defs.wordVertex p.u w n = p.v) (b : Bool) :
  ((AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)).partition p.τ b fun a =>
      AKLT.Defs.normSq (a p.v)) =
    AKLT.Blueprint.Rec.targetFactor p.D p.v *
      (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)).partition p.τ b fun x => 1
AKLT.W.REC082.target_weighted_factor (p : AKLT.Blueprint.Rec.PairData) (hv : p.v ∉ AKLT.Defs.protectedSites p.G) (n : ℕ)
  (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w)
  (he : AKLT.Defs.wordVertex p.u w n = p.v) (b : Bool) :
  (AKLT.Defs.traceRatio p.normalized p.τ b (AKLT.Defs.wordVertices p.u w) *
      (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)).expectation p.τ b fun a =>
        AKLT.Defs.dot (a p.v) (a p.v)) =
    AKLT.Defs.traceRatio p.normalized p.τ b (AKLT.Defs.wordVertices p.u w) * AKLT.Blueprint.Rec.targetFactor p.D p.v
AKLT.W.REC082.onePinExpansion_of_residual (hExpansion : AKLT.W.REC082.Residual_FiniteNumeratorExpansion)
  (p : AKLT.Blueprint.Rec.PairData) (hu : p.u ∉ AKLT.Defs.protectedSites p.G) (hv : p.v ∉ AKLT.Defs.protectedSites p.G)
  (b : Bool) :
  (p.D.expectation p.τ b fun a => AKLT.Defs.dot (a p.u) (a p.v)) =
    AKLT.Blueprint.Rec.stoppedSum p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) fun n w =>
      ↑(AKLT.Defs.traceCoefficient p.normalized (AKLT.Defs.wordVertices p.u w)) *
          AKLT.Defs.traceRatio p.normalized p.τ b (AKLT.Defs.wordVertices p.u w) *
        (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)).expectation p.τ b fun a =>
          AKLT.Defs.dot (a (AKLT.Defs.wordVertex p.u w n)) (a p.v)
AKLT.W.REC082.main_of_residual (hExpansion : AKLT.W.REC082.Residual_FiniteNumeratorExpansion) :
  AKLT.Blueprint.Rec.PairResponseSplitStatement
```

The only additional named definitions are `partitionWeight`, `interactionWeight`, and `Residual_FiniteNumeratorExpansion`, all transparent definitions in the listed source files.

## Axiom audit output

```text
'AKLT.W.REC082.removed_not_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalizeStart_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalizeStart_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalizeStart_presentNeighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalizeStart_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalizeStart_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalizeStart_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.pair_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.pair_c_removed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.pair_u_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.pair_v_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalized_targetFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalized_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalized_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.adjacent_iff_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.neighbours_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.neighbours_degree_of_removed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.no_originalLegs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.pair_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.pair_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.pair_target' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalized_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normalized_target' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.goldenRatio_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.icoRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.icoRadius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.spinVector_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.d_norm_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.site_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.inv_radius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.inv_radius_fourth' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.u_step_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.d_step_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.normSq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.ball_factor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.partition_eq_sum_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.partitionWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.partition_zero_of_mass_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.traceRatio_mul_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.traceRatio_mul_terminal_of_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.adjacent_symm' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC082.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.present_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.traceStep_active_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.traceStep_kept_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.traceStep_present_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.traceStep_not_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.traceNetwork_present_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.traceNetwork_not_present_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.traceNetwork_status_of_not_departed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.wordVertex_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.wordVertices_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.wordVertices_getElem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.stopped_target_not_departed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.stopped_target_status' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.stopped_target_isolated' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.independent_site_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.independent_site_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.partitionWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.spins_eq_of_agree_away' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.interactionWeight_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.partition_norm_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.partition_norm_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.target_partition_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.target_weighted_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.onePinExpansion_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC082.main_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- STATUS: PARTIAL; no unconditional `AKLT.W.REC082.main` is supplied.
- `AKLT.W.REC082.main_of_residual` proves the exact frozen statement from one closed residual.
- Open exact name: `AKLT.W.REC082.Residual_FiniteNumeratorExpansion`.
- Proved normalization invariance and admissible endpoint facts from `PairData`.
- Proved the weighted target factor for both U and D targets; removed the old terminal-factor residual.
- Proved local `u_step_moment` and `d_step_moment` without assuming another blueprint leaf.
- Proved nonnegative partition weights and trace-ratio cancellation, including zero-mass cases.
- Missing: lift local identities through changing active-site partitions, then finite bond-trail iteration/enumeration.
- The stronger raw normalized terminal factor is not separately proved; its weighted version suffices here.
- Main build and audit pass; all 71 named theorem axiom sets are permitted.
- Four non-failing tactic-sequencing warnings remain in the D moment proof.
- Only assigned leaf/report directories were changed; no sub-agents were used.
- Orchestrator must finish the named residual and instantiate `main_of_residual` to obtain the required `main`.
