STATUS: PROVED

## Files

All Lean files are under `/home/ubuntu/aklt/wt/LW_REC098/AKLT/W/REC098/`:

- `Main.lean`: the requested unconditional theorem, the far-departure covering theorem, and positive distance.
- `Trace.lean`: the prefix invariant, preservation of unused trail bonds, restart with one fixed protected defect, and the second-trace state.
- `Local.lean`: rotated template extraction and the shared present-bond cover witness.
- `Geometry.lean`: lattice adjacency, interior radius-two inclusion, and word/prefix geometry.
- `Audit.lean`: an independent import and exact target-type check, signatures of all 66 explicitly named declarations, and axiom checks for all 61 named theorems.

Report artifacts: `report.md`, `audit.log`, and `audit-timing.txt` in `/home/ubuntu/aklt/reports/LW/REC098/`. The historical `report.luna.md` is preserved.

The supplied worktree already contained a complete helper proof and `main`, beyond what the earlier partial report described. This delivery retains that proof, cleans its lint warnings, documents the argument, and adds the exact-type and comprehensive axiom audit. No file outside REC098 was edited. No other proved blueprint leaf is imported or needed.

## Requested exported declaration

```lean
theorem AKLT.W.REC098.main :
    AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2
```

This has exactly the requested name and closed type. There are no extra premises, residual statements, or unproved dependencies. `Audit.lean` verifies the exact type by importing only `AKLT.W.REC098.Main` and checking:

```lean
example : AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2 :=
  AKLT.W.REC098.main
```

## Argument

`TraceState` tracks mutual kept flags, full U kept sets away from the live site and fixed defects, two-element nonlive D kept sets, live/arrival data, and protected U statuses. `prefix_state` preserves these facts together with all future trail bonds: distinctness of trail bonds and the live D degree bound ensure that a trace step cannot destroy another required bond.

The first trace starts with no fixed defects. At its protected endpoint e, `TraceState.restart` restarts from v with `{e}` as the fixed defect set. The first trail avoids v, so its status is unchanged and its D present degree can only decrease. `second_state` applies the same prefix induction to every second-trace departure before the protected set is reached.

`state_covered` constructs a rotated `PatternData` witness whenever the defect is outside the template. It matches non-tip statuses and actual internal present bonds, sets covering tips to U, and proves the one-sided tip condition. It uses the shared `AKLT.Defs.CoveredDepartureV2`, with no external kept-set matching requirement. If the departure is farther than two from e, the entire radius-two template avoids e. Thus `far_departure_covered` applies. A second departure is outside the protected set while e is inside, giving strictly positive distance. Contraposition yields the claimed punctured radius-two location for every cover failure.

## Validation

Commands run from `/home/ubuntu/aklt/wt/LW_REC098` with `PATH="$HOME/.elan/bin:$PATH"`:

| Command | Result | Wall time |
| --- | --- | --- |
| `lake build AKLT.W.REC098.Main` | Success; freshly rebuilt Geometry, Trace, Local, Main; no warnings | 35.41 s |
| `lake env lean AKLT/W/REC098/Audit.lean` | Success; exact imported target type, all signatures, all theorem axiom checks | 5.34 s |

A separate check of the audit output confirmed that all 61 named theorem audits are present and every axiom belongs to `{propext, Classical.choice, Quot.sound}`. Two elementary rotation theorems require no axioms. The final theorem reports:

```text
'AKLT.W.REC098.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof mechanisms are used. No open issues remain.

## All explicitly named exported declarations and their statements

The following is the complete successful `#check` output from `Audit.lean`, including helper definitions and the `TraceState` predicate. Every name is in `AKLT.W.REC098`.

```text
AKLT.W.REC098.adjacent_iff (x z : AKLT.Defs.Plane) : AKLT.Defs.Adjacent x z ↔ z ∈ AKLT.Defs.neighbours x
AKLT.W.REC098.adjacent_symm {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : AKLT.Defs.Adjacent z x
AKLT.W.REC098.adjacent_ne {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : x ≠ z
AKLT.W.REC098.step_injective : Function.Injective AKLT.Defs.Compass.step
AKLT.W.REC098.neighbours_card (x : AKLT.Defs.Plane) : (AKLT.Defs.neighbours x).card = 4
AKLT.W.REC098.interior_ball {G : Finset AKLT.Defs.Plane} {y : AKLT.Defs.Plane} (hyG : y ∈ G)
  (hyS : y ∉ AKLT.Defs.protectedSites G) {z : AKLT.Defs.Plane} (hz : AKLT.Defs.latticeDist y z ≤ 2) : z ∈ G
AKLT.W.REC098.interior_neighbours {G : Finset AKLT.Defs.Plane} {y : AKLT.Defs.Plane} (hyG : y ∈ G)
  (hyS : y ∉ AKLT.Defs.protectedSites G) : AKLT.Defs.neighbours y ∩ G = AKLT.Defs.neighbours y
AKLT.W.REC098.wordVertex_zero {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) :
  AKLT.Defs.wordVertex u w 0 = u
AKLT.W.REC098.wordVertex_succ {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (j : ℕ) (hj : j < n) :
  AKLT.Defs.wordVertex u w (j + 1) = AKLT.Defs.wordVertex u w j + (w ⟨j, hj⟩).step
AKLT.W.REC098.wordVertex_adjacent {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (i : Fin n) :
  AKLT.Defs.Adjacent (AKLT.Defs.wordVertex u w ↑i) (AKLT.Defs.wordVertex u w (↑i + 1))
AKLT.W.REC098.TraceState {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (bad : Finset AKLT.Defs.Plane)
  (y a : AKLT.Defs.Plane) : Prop
AKLT.W.REC098.present_symm {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x z : AKLT.Defs.Plane}
  (h : D.Present x z) : D.Present z x
AKLT.W.REC098.present_neighbour {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x z : AKLT.Defs.Plane}
  (h : D.Present x z) : z ∈ D.presentNeighbours x
AKLT.W.REC098.traceStep_active_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  (AKLT.Defs.traceStep D y o).active ⊆ D.active
AKLT.W.REC098.traceStep_kept_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x : AKLT.Defs.Plane) :
  (AKLT.Defs.traceStep D y o).kept x ⊆ D.kept x
AKLT.W.REC098.traceStep_present_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  {x z : AKLT.Defs.Plane} (h : (AKLT.Defs.traceStep D y o).Present x z) : D.Present x z
AKLT.W.REC098.preserve_present {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y o x z : AKLT.Defs.Plane}
  (hyo : D.Present y o) (hD : D.status y = AKLT.Defs.Status.D → (D.presentNeighbours y).card ≤ 1) (hxz : D.Present x z)
  (hne : {x, z} ≠ {y, o}) : (AKLT.Defs.traceStep D y o).Present x z
AKLT.W.REC098.presentNeighbours_card_le_kept {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (x : AKLT.Defs.Plane) : (D.presentNeighbours x).card ≤ (D.kept x).card
AKLT.W.REC098.TraceState.step {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {bad : Finset AKLT.Defs.Plane}
  {y a o : AKLT.Defs.Plane} (hs : AKLT.W.REC098.TraceState D bad y a) (hyS : y ∉ AKLT.Defs.protectedSites G)
  (hyo : D.Present y o) (hoB : o ∉ bad) : AKLT.W.REC098.TraceState (AKLT.Defs.traceStep D y o) bad o y
AKLT.W.REC098.traceNetwork_append_step {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (l : List AKLT.Defs.Plane)
  (x z : AKLT.Defs.Plane) :
  AKLT.Defs.traceNetwork D (l ++ [x, z]) = AKLT.Defs.traceStep (AKLT.Defs.traceNetwork D (l ++ [x])) x z
AKLT.W.REC098.prefixNetwork_eq_range {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (j : ℕ) (hj : j ≤ n) :
  AKLT.Blueprint.Rec.prefixNetwork D u w j =
    AKLT.Defs.traceNetwork D (List.map (AKLT.Defs.wordVertex u w) (List.range (j + 1)))
AKLT.W.REC098.prefixNetwork_zero {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G) (u : AKLT.Defs.Plane)
  (w : AKLT.Defs.DirectionWord n) : AKLT.Blueprint.Rec.prefixNetwork D u w 0 = D
AKLT.W.REC098.prefixNetwork_succ {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G) (u : AKLT.Defs.Plane)
  (w : AKLT.Defs.DirectionWord n) (j : ℕ) (hj : j < n) :
  AKLT.Blueprint.Rec.prefixNetwork D u w (j + 1) =
    AKLT.Defs.traceStep (AKLT.Blueprint.Rec.prefixNetwork D u w j) (AKLT.Defs.wordVertex u w j)
      (AKLT.Defs.wordVertex u w (j + 1))
AKLT.W.REC098.prefix_state {G : Finset AKLT.Defs.Plane} {n : ℕ} {D : AKLT.Defs.Network G} {bad : Finset AKLT.Defs.Plane}
  {u a : AKLT.Defs.Plane} {w : AKLT.Defs.DirectionWord n} {T : Finset AKLT.Defs.Plane}
  (hs : AKLT.W.REC098.TraceState D bad u a) (hw : AKLT.Defs.StoppedNetworkTrail D u T w) (j : ℕ) (hj : j ≤ n)
  (hb : ∀ k ≤ j, AKLT.Defs.wordVertex u w k ∉ bad) :
  AKLT.W.REC098.TraceState (AKLT.Blueprint.Rec.prefixNetwork D u w j) bad (AKLT.Defs.wordVertex u w j)
      (if j = 0 then a else AKLT.Defs.wordVertex u w (j - 1)) ∧
    ∀ (k : Fin n),
      j ≤ ↑k →
        (AKLT.Blueprint.Rec.prefixNetwork D u w j).Present (AKLT.Defs.wordVertex u w ↑k)
          (AKLT.Defs.wordVertex u w (↑k + 1))
AKLT.W.REC098.normalizeStart_of_not_U {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (u c : AKLT.Defs.Plane)
  (h : D.status u ≠ AKLT.Defs.Status.U) : AKLT.Blueprint.Rec.normalizeStart D u c = D
AKLT.W.REC098.normalizeStart_present_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (u c : AKLT.Defs.Plane) {x z : AKLT.Defs.Plane} (h : (AKLT.Blueprint.Rec.normalizeStart D u c).Present x z) :
  D.Present x z
AKLT.W.REC098.normalizeStart_mutual {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {u c : AKLT.Defs.Plane}
  (hc : D.status c = AKLT.Defs.Status.X)
  (hm : ∀ x ∈ D.active, ∀ z ∈ D.active, AKLT.Defs.Adjacent x z → (z ∈ D.kept x ↔ x ∈ D.kept z)) (x : AKLT.Defs.Plane) :
  x ∈ (AKLT.Blueprint.Rec.normalizeStart D u c).active →
    ∀ z ∈ (AKLT.Blueprint.Rec.normalizeStart D u c).active,
      AKLT.Defs.Adjacent x z →
        (z ∈ (AKLT.Blueprint.Rec.normalizeStart D u c).kept x ↔ x ∈ (AKLT.Blueprint.Rec.normalizeStart D u c).kept z)
AKLT.W.REC098.initial_state (p : AKLT.Blueprint.Rec.PairSetup) : AKLT.W.REC098.TraceState p.normalized ∅ p.u p.c
AKLT.W.REC098.traceNetwork_present_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (l : List AKLT.Defs.Plane) {x z : AKLT.Defs.Plane} (h : (AKLT.Defs.traceNetwork D l).Present x z) : D.Present x z
AKLT.W.REC098.traceNetwork_status_X {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (l : List AKLT.Defs.Plane)
  {x : AKLT.Defs.Plane} (h : D.status x = AKLT.Defs.Status.X) :
  (AKLT.Defs.traceNetwork D l).status x = AKLT.Defs.Status.X
AKLT.W.REC098.prefix_status_unvisited {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (j : ℕ) (hj : j ≤ n) (x : AKLT.Defs.Plane)
  (hx : ∀ k < j, AKLT.Defs.wordVertex u w k ≠ x) : (AKLT.Blueprint.Rec.prefixNetwork D u w j).status x = D.status x
AKLT.W.REC098.TraceState.restart {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {e a v c : AKLT.Defs.Plane}
  (hs : AKLT.W.REC098.TraceState D ∅ e a) (he : e ∈ AKLT.Defs.protectedSites G) (hve : v ≠ e)
  (hc : D.status c = AKLT.Defs.Status.X) (hvc : AKLT.Defs.Adjacent v c)
  (hdeg : D.status v = AKLT.Defs.Status.D → (D.presentNeighbours v).card ≤ 1) :
  AKLT.W.REC098.TraceState (AKLT.Blueprint.Rec.normalizeStart D v c) {e} v c
AKLT.W.REC098.word_arrival {n : ℕ} {u c : AKLT.Defs.Plane} {incoming : AKLT.Defs.Compass} (hu : u = c + incoming.step)
  (w : AKLT.Defs.DirectionWord n) (i : Fin n) :
  (if ↑i = 0 then c else AKLT.Defs.wordVertex u w (↑i - 1)) =
    AKLT.Defs.wordVertex u w ↑i - (AKLT.Defs.wordIncoming incoming w i).step
AKLT.W.REC098.second_state (p : AKLT.Blueprint.Rec.PairSetup) (hpv : p.v ∉ AKLT.Defs.protectedSites p.G) (n : ℕ)
  (w : AKLT.Defs.DirectionWord n)
  (hfirst : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w)
  (he : AKLT.Defs.wordVertex p.u w n ∈ AKLT.Defs.protectedSites p.G) (incoming : AKLT.Defs.Compass)
  (hin : p.v = p.c + incoming.step) (m : ℕ) (w' : AKLT.Defs.DirectionWord m)
  (hsecond :
    AKLT.Defs.StoppedNetworkTrail
      (AKLT.Blueprint.Rec.normalizeStart (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)) p.v p.c)
      p.v (AKLT.Defs.protectedSites p.G) w')
  (i : Fin m) :
  AKLT.W.REC098.TraceState
      (AKLT.Blueprint.Rec.prefixNetwork
        (AKLT.Blueprint.Rec.normalizeStart (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)) p.v p.c)
        p.v w' ↑i)
      {AKLT.Defs.wordVertex p.u w n} (AKLT.Defs.wordVertex p.v w' ↑i)
      (AKLT.Defs.wordVertex p.v w' ↑i - (AKLT.Defs.wordIncoming incoming w' i).step) ∧
    (AKLT.Blueprint.Rec.prefixNetwork
          (AKLT.Blueprint.Rec.normalizeStart (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)) p.v
            p.c)
          p.v w' ↑i).Present
      (AKLT.Defs.wordVertex p.v w' ↑i) (AKLT.Defs.wordVertex p.v w' (↑i + 1))
AKLT.W.REC098.rotateDir : AKLT.Defs.Compass → AKLT.Defs.Compass → AKLT.Defs.Compass
AKLT.W.REC098.chart (y : AKLT.Defs.Plane) (a : AKLT.Defs.Compass) (z : AKLT.Defs.Plane) : AKLT.Defs.Plane
AKLT.W.REC098.chart_injective (y : AKLT.Defs.Plane) (a : AKLT.Defs.Compass) :
  Function.Injective (AKLT.W.REC098.chart y a)
AKLT.W.REC098.rotateDir_surjective (a : AKLT.Defs.Compass) : Function.Surjective (AKLT.W.REC098.rotateDir a)
AKLT.W.REC098.chart_zero (y : AKLT.Defs.Plane) (a : AKLT.Defs.Compass) : AKLT.W.REC098.chart y a (0, 0) = y
AKLT.W.REC098.chart_add_step (y z : AKLT.Defs.Plane) (a d : AKLT.Defs.Compass) :
  AKLT.W.REC098.chart y a (z + d.step) = AKLT.W.REC098.chart y a z + (AKLT.W.REC098.rotateDir a d).step
AKLT.W.REC098.chart_south (y : AKLT.Defs.Plane) (a : AKLT.Defs.Compass) : AKLT.W.REC098.chart y a (0, -1) = y - a.step
AKLT.W.REC098.chart_mem_neighbours (y z t : AKLT.Defs.Plane) (a : AKLT.Defs.Compass) :
  AKLT.W.REC098.chart y a t ∈ AKLT.Defs.neighbours (AKLT.W.REC098.chart y a z) ↔ t ∈ AKLT.Defs.neighbours z
AKLT.W.REC098.chart_adjacent (y z t : AKLT.Defs.Plane) (a : AKLT.Defs.Compass) :
  AKLT.Defs.Adjacent (AKLT.W.REC098.chart y a z) (AKLT.W.REC098.chart y a t) ↔ AKLT.Defs.Adjacent z t
AKLT.W.REC098.chart_dist (y z t : AKLT.Defs.Plane) (a : AKLT.Defs.Compass) :
  AKLT.Defs.latticeDist (AKLT.W.REC098.chart y a z) (AKLT.W.REC098.chart y a t) = AKLT.Defs.latticeDist z t
AKLT.W.REC098.templateSites_explicit :
  AKLT.Defs.templateSites =
    {(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1), (1, 1), (-1, 1), (-1, -1), (1, -1), (2, 0), (0, 2), (-2, 0), (0, -2)}
AKLT.W.REC098.chart_ball (y : AKLT.Defs.Plane) (a : AKLT.Defs.Compass) {z : AKLT.Defs.Plane}
  (hz : z ∈ AKLT.Defs.templateSites) : AKLT.Defs.latticeDist y (AKLT.W.REC098.chart y a z) ≤ 2
AKLT.W.REC098.internalBonds_mem {G : Finset AKLT.Defs.Plane} {x z : AKLT.Defs.Plane} :
  (x, z) ∈ AKLT.Defs.internalBonds G ↔ x ∈ G ∧ z ∈ G ∧ z ∈ AKLT.Defs.positiveNeighbours x
AKLT.W.REC098.positive_either (x z : AKLT.Defs.Plane) :
  z ∈ AKLT.Defs.positiveNeighbours x ∨ x ∈ AKLT.Defs.positiveNeighbours z ↔ AKLT.Defs.Adjacent x z
AKLT.W.REC098.internalPresent_iff (π : AKLT.Defs.PatternData) (z t : AKLT.Defs.Plane) :
  π.InternalPresent z t ↔
    z ∈ AKLT.Defs.templateSites ∧
      t ∈ AKLT.Defs.templateSites ∧
        AKLT.Defs.Adjacent z t ∧
          π.statusAt z ≠ AKLT.Defs.Status.X ∧
            π.statusAt t ≠ AKLT.Defs.Status.X ∧
              (z ∈ AKLT.Defs.templateTips ∨ t ∈ π.keptAt z) ∧ (t ∈ AKLT.Defs.templateTips ∨ z ∈ π.keptAt t)
AKLT.W.REC098.localFlags {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a : AKLT.Defs.Compass) (z : AKLT.Defs.Plane) : Finset AKLT.Defs.Compass
AKLT.W.REC098.localFlags_match {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a : AKLT.Defs.Compass) (z t : AKLT.Defs.Plane)
  (hsub : D.kept (AKLT.W.REC098.chart y a z) ⊆ AKLT.Defs.neighbours (AKLT.W.REC098.chart y a z)) :
  t ∈ Finset.image (fun d => z + d.step) (AKLT.W.REC098.localFlags D y a z) ↔
    AKLT.W.REC098.chart y a t ∈ D.kept (AKLT.W.REC098.chart y a z)
AKLT.W.REC098.localFlags_image {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a : AKLT.Defs.Compass) (z : AKLT.Defs.Plane)
  (hsub : D.kept (AKLT.W.REC098.chart y a z) ⊆ AKLT.Defs.neighbours (AKLT.W.REC098.chart y a z)) :
  Finset.image (fun d => AKLT.W.REC098.chart y a (z + d.step)) (AKLT.W.REC098.localFlags D y a z) =
    D.kept (AKLT.W.REC098.chart y a z)
AKLT.W.REC098.localFlags_card {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a : AKLT.Defs.Compass) (z : AKLT.Defs.Plane)
  (hsub : D.kept (AKLT.W.REC098.chart y a z) ⊆ AKLT.Defs.neighbours (AKLT.W.REC098.chart y a z)) :
  (Finset.image (fun d => z + d.step) (AKLT.W.REC098.localFlags D y a z)).card =
    (D.kept (AKLT.W.REC098.chart y a z)).card
AKLT.W.REC098.localPattern {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a out : AKLT.Defs.Compass) : AKLT.Defs.PatternData
AKLT.W.REC098.localPattern_status {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a out : AKLT.Defs.Compass) {z : AKLT.Defs.Plane} (hz : z ∈ AKLT.Defs.templateSites \ AKLT.Defs.templateTips) :
  (AKLT.W.REC098.localPattern D y a out).statusAt z = D.status (AKLT.W.REC098.chart y a z)
AKLT.W.REC098.localPattern_tip {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a out : AKLT.Defs.Compass) {z : AKLT.Defs.Plane} (hz : z ∈ AKLT.Defs.templateTips) :
  (AKLT.W.REC098.localPattern D y a out).statusAt z = AKLT.Defs.Status.U
AKLT.W.REC098.localPattern_center_kept {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a out : AKLT.Defs.Compass) : (AKLT.W.REC098.localPattern D y a out).keptAt (0, 0) = {(1, 0), (0, 1), (-1, 0)}
AKLT.W.REC098.localPattern_kept_U {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a out : AKLT.Defs.Compass) {z : AKLT.Defs.Plane} (hz : z ∈ AKLT.Defs.templateSites) (hne : z ≠ (0, 0))
  (hU : D.status (AKLT.W.REC098.chart y a z) = AKLT.Defs.Status.U) :
  (AKLT.W.REC098.localPattern D y a out).keptAt z = AKLT.Defs.neighbours z
AKLT.W.REC098.localPattern_kept_notU {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a out : AKLT.Defs.Compass) {z : AKLT.Defs.Plane} (hz : z ∈ AKLT.Defs.templateSites) (hne : z ≠ (0, 0))
  (hU : D.status (AKLT.W.REC098.chart y a z) ≠ AKLT.Defs.Status.U) :
  (AKLT.W.REC098.localPattern D y a out).keptAt z =
    Finset.image (fun d => z + d.step) (AKLT.W.REC098.localFlags D y a z)
AKLT.W.REC098.localPattern_kept_match {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y : AKLT.Defs.Plane}
  {a out : AKLT.Defs.Compass} {bad : Finset AKLT.Defs.Plane} (hs : AKLT.W.REC098.TraceState D bad y (y - a.step))
  (hU : D.status y = AKLT.Defs.Status.U) (hG : ∀ t ∈ AKLT.Defs.templateSites, AKLT.W.REC098.chart y a t ∈ G)
  (hb : ∀ z ∈ AKLT.Defs.templateSites, AKLT.W.REC098.chart y a z ∉ bad) {z t : AKLT.Defs.Plane}
  (hz : z ∈ AKLT.Defs.templateSites \ AKLT.Defs.templateTips) (ht : t ∈ AKLT.Defs.templateSites) :
  t ∈ (AKLT.W.REC098.localPattern D y a out).keptAt z ↔ AKLT.W.REC098.chart y a t ∈ D.kept (AKLT.W.REC098.chart y a z)
AKLT.W.REC098.localPattern_D_card {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y : AKLT.Defs.Plane}
  {a out : AKLT.Defs.Compass} {bad : Finset AKLT.Defs.Plane} (hs : AKLT.W.REC098.TraceState D bad y (y - a.step))
  {z : AKLT.Defs.Plane} (hz : z ∈ AKLT.Defs.templateSites) (hz0 : z ≠ (0, 0))
  (hD : D.status (AKLT.W.REC098.chart y a z) = AKLT.Defs.Status.D) :
  ((AKLT.W.REC098.localPattern D y a out).keptAt z).card = 2
AKLT.W.REC098.normalizeRotation_step (a d : AKLT.Defs.Compass) :
  AKLT.Defs.normalizeRotation a d.step = (AKLT.W.REC098.rotateDir a d).step
AKLT.W.REC098.state_covered {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y : AKLT.Defs.Plane}
  {a outgoing : AKLT.Defs.Compass} {bad : Finset AKLT.Defs.Plane} (hs : AKLT.W.REC098.TraceState D bad y (y - a.step))
  (hyS : y ∉ AKLT.Defs.protectedSites G) (hU : D.status y = AKLT.Defs.Status.U)
  (hpres : D.Present y (y + outgoing.step)) (hb : ∀ z ∈ AKLT.Defs.templateSites, AKLT.W.REC098.chart y a z ∉ bad) :
  AKLT.Defs.CoveredDepartureV2 D y a outgoing
AKLT.W.REC098.far_departure_covered (p : AKLT.Blueprint.Rec.PairSetup) (hpv : p.v ∉ AKLT.Defs.protectedSites p.G)
  (n : ℕ) (w : AKLT.Defs.DirectionWord n)
  (hfirst : AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w)
  (he : AKLT.Defs.wordVertex p.u w n ∈ AKLT.Defs.protectedSites p.G) (incoming : AKLT.Defs.Compass)
  (hin : p.v = p.c + incoming.step) (m : ℕ) (w' : AKLT.Defs.DirectionWord m)
  (hsecond :
    AKLT.Defs.StoppedNetworkTrail
      (AKLT.Blueprint.Rec.normalizeStart (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)) p.v p.c)
      p.v (AKLT.Defs.protectedSites p.G) w')
  (i : Fin m)
  (hU :
    (AKLT.Blueprint.Rec.prefixNetwork
            (AKLT.Blueprint.Rec.normalizeStart (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)) p.v
              p.c)
            p.v w' ↑i).status
        (AKLT.Defs.wordVertex p.v w' ↑i) =
      AKLT.Defs.Status.U)
  (hfar : 2 < AKLT.Defs.latticeDist (AKLT.Defs.wordVertex p.v w' ↑i) (AKLT.Defs.wordVertex p.u w n)) :
  AKLT.Defs.CoveredDepartureV2
    (AKLT.Blueprint.Rec.prefixNetwork
      (AKLT.Blueprint.Rec.normalizeStart (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)) p.v p.c)
      p.v w' ↑i)
    (AKLT.Defs.wordVertex p.v w' ↑i) (AKLT.Defs.wordIncoming incoming w' i) (w' i)
AKLT.W.REC098.secondDeparture_distance_pos (p : AKLT.Blueprint.Rec.PairSetup) (n : ℕ) (w : AKLT.Defs.DirectionWord n)
  (he : AKLT.Defs.wordVertex p.u w n ∈ AKLT.Defs.protectedSites p.G) (m : ℕ) (w' : AKLT.Defs.DirectionWord m)
  (hsecond :
    AKLT.Defs.StoppedNetworkTrail
      (AKLT.Blueprint.Rec.normalizeStart (AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)) p.v p.c)
      p.v (AKLT.Defs.protectedSites p.G) w')
  (i : Fin m) : 0 < AKLT.Defs.latticeDist (AKLT.Defs.wordVertex p.v w' ↑i) (AKLT.Defs.wordVertex p.u w n)
AKLT.W.REC098.main : AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2
```

## Complete `#print axioms` output

```text
'AKLT.W.REC098.adjacent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.adjacent_symm' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC098.adjacent_ne' depends on axioms: [propext]
'AKLT.W.REC098.step_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.neighbours_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.interior_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.interior_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.wordVertex_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.wordVertex_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.wordVertex_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.present_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.traceStep_active_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.traceStep_kept_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.traceStep_present_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.preserve_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.presentNeighbours_card_le_kept' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.TraceState.step' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.traceNetwork_append_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.prefixNetwork_eq_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.prefixNetwork_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.prefixNetwork_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.prefix_state' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.normalizeStart_of_not_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.normalizeStart_present_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.normalizeStart_mutual' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.initial_state' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.traceNetwork_present_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.traceNetwork_status_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.prefix_status_unvisited' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.TraceState.restart' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.word_arrival' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.second_state' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.chart_injective' depends on axioms: [propext]
'AKLT.W.REC098.rotateDir_surjective' does not depend on any axioms
'AKLT.W.REC098.chart_zero' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC098.chart_add_step' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC098.chart_south' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC098.chart_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.chart_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.chart_dist' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC098.templateSites_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.chart_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.internalBonds_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.positive_either' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.internalPresent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localFlags_match' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localFlags_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localFlags_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localPattern_status' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localPattern_tip' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localPattern_center_kept' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localPattern_kept_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localPattern_kept_notU' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localPattern_kept_match' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.localPattern_D_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.normalizeRotation_step' does not depend on any axioms
'AKLT.W.REC098.state_covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.far_departure_covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.secondDeparture_distance_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/REC098/Main.lean` and four helper/audit modules in the same directory.
- Exact theorem: `AKLT.W.REC098.main : AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2`.
- Complete proof retained from the supplied worktree; lint cleanup, documentation, and full audit added.
- Second-trace prefix invariant has precisely the first protected endpoint as the fixed defect.
- Shared present-bond template matching proves coverage beyond distance two.
- Positive distance follows from departure avoidance of the original protected set.
- No extra blueprint leaf dependency, residual statement, or additional premise.
- All 61 named theorem axiom checks passed; only the three permitted axioms occur.
- Fresh requested module build passed in 35.41 s; exact-type/full audit passed in 5.34 s.
- No remaining open names, limitations, deviations, or orchestrator decisions.
