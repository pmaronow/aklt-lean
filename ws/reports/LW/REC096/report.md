STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC096/AKLT/W/REC096/Main.lean): the required unconditional theorem.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC096/AKLT/W/REC096/Geometry.lean): lattice, rotation, and interior-radius-two facts.
- [Trace.lean](/home/ubuntu/aklt/wt/LW_REC096/AKLT/W/REC096/Trace.lean): the kept/status invariant and preservation of unused bonds under one step.
- [Prefix.lean](/home/ubuntu/aklt/wt/LW_REC096/AKLT/W/REC096/Prefix.lean): initial normalization, word/prefix identities, and the prefix induction.
- [Template.lean](/home/ubuntu/aklt/wt/LW_REC096/AKLT/W/REC096/Template.lean): covered-pattern extraction and the shared internal-present-bond matcher.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC096/AKLT/W/REC096/Audit.lean): the exact-type example, declaration checks, and all theorem dependency checks.

Only files in `AKLT/W/REC096/` were written in the worktree. The frozen statement and existing libraries were not modified. The earlier conditional residual reduction in `Main.lean` has been replaced by the unconditional proof; `report.luna.md` remains the record of that earlier attempt.

## Required export

```lean
theorem AKLT.W.REC096.main : AKLT.Blueprint.Rec.CoveredClosureStatementV2
```

The theorem has no additional hypotheses or residual assumptions. `Audit.lean` independently imports `Main` and checks:

```lean
example : AKLT.Blueprint.Rec.CoveredClosureStatementV2 := AKLT.W.REC096.main
```

## Proof

`PrefixInvariant` records the outside-X rule, kept-set containment, full kept sets at nonlive U sites, two kept flags at nonlive D sites, active-endpoint consistency, the non-U arrival site, the live U kept set with exactly its arrival erased, and uniqueness of a live D site's present neighbour. The induction also proves that every remaining original trail bond is still present. A U departure leaves two kept flags at its new D site. A D departure can destroy no unused present bond, because it has at most one present neighbour. Distinct unoriented word bonds therefore give the next live bond at every prefix.

At a live U departure, the radius-two diamond lies inside the original volume. The affine chart pulls back the actual D kept sets and completes noncentral U kept sets to all four directions. It sets the four covering-tip statuses to U. Active consistency proves the non-tip pattern rules and exact non-tip internal bond matching. Every actual internal bond to a tip survives in the covering pattern. The proof uses precisely `AKLT.Defs.CoveredDepartureV2`, so external flags and flags to removed sites impose no extra matching condition.

## Build and verification

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC096.Main` — **passed**, no warnings in the final build.
- Lake-reported module times: `Geometry` 3.7 s, `Trace` 4.7 s, `Prefix` 3.8 s, `Template` 14 s, `Main` 3.2 s.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC096/Audit.lean` — **passed**, 4.19 s wall time measured with `/usr/bin/time`.
- All 52 explicitly declared theorems were checked with `#print axioms`; every dependency is among `propext`, `Classical.choice`, and `Quot.sound`.
- Source scan found no forbidden proof shortcuts or forbidden declarations.
- Complete verification output: [audit.log](/home/ubuntu/aklt/reports/LW/REC096/audit.log).

For the required theorem:

```text
'AKLT.W.REC096.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exported declarations and statements

The following is the complete `#check` output for explicit declarations in the five proof modules. Unqualified names in types use `AKLT.Defs`, `AKLT.Blueprint.Rec`, and `AKLT.W.REC096`, as opened in `Audit.lean`.

```text
AKLT.W.REC096.natAbs_sub_comm (a b : ℤ) : (a - b).natAbs = (b - a).natAbs
AKLT.W.REC096.natAbs_neg_add (a b : ℤ) : (-a + b).natAbs = (a - b).natAbs
AKLT.W.REC096.step_injective : Function.Injective Compass.step
AKLT.W.REC096.neighbours_card (x : Plane) : (neighbours x).card = 4
AKLT.W.REC096.adjacent_iff (x z : Plane) : Adjacent x z ↔ z ∈ neighbours x
AKLT.W.REC096.adjacent_symm {x z : Plane} (h : Adjacent x z) : Adjacent z x
AKLT.W.REC096.adjacent_ne {x z : Plane} (h : Adjacent x z) : x ≠ z
AKLT.W.REC096.step_adjacent (x : Plane) (d : Compass) : Adjacent x (x + d.step)
AKLT.W.REC096.chart (y : Plane) (d : Compass) : Plane ≃ Plane
AKLT.W.REC096.chart_apply (y : Plane) (d : Compass) (z : Plane) : (chart y d) z = y + normalizeRotation d z
AKLT.W.REC096.chart_zero (y : Plane) (d : Compass) : (chart y d) (0, 0) = y
AKLT.W.REC096.chart_south (y : Plane) (d : Compass) : (chart y d) (0, -1) = y - d.step
AKLT.W.REC096.chart_dist (y x z : Plane) (d : Compass) : latticeDist ((chart y d) x) ((chart y d) z) = latticeDist x z
AKLT.W.REC096.chart_adjacent (y x z : Plane) (d : Compass) : Adjacent ((chart y d) x) ((chart y d) z) ↔ Adjacent x z
AKLT.W.REC096.chart_neighbours (y x : Plane) (d : Compass) :
  Finset.image (⇑(chart y d)) (neighbours x) = neighbours ((chart y d) x)
AKLT.W.REC096.interior_ball {G : Finset Plane} {y : Plane} (hy : y ∈ G) (hS : y ∉ protectedSites G) {z : Plane}
  (hz : latticeDist y z ≤ 2) : z ∈ G
AKLT.W.REC096.template_dist {z : Plane} (hz : z ∈ templateSites) : latticeDist (0, 0) z ≤ 2
AKLT.W.REC096.template_interior {G : Finset Plane} {y : Plane} (hy : y ∈ G) (hS : y ∉ protectedSites G) (d : Compass)
  {z : Plane} (hz : z ∈ templateSites) : (chart y d) z ∈ G
AKLT.W.REC096.present_symm {G : Finset Plane} {E : Network G} {x z : Plane} (h : E.Present x z) : E.Present z x
AKLT.W.REC096.present_mem_neighbours {G : Finset Plane} {E : Network G} {x z : Plane} (h : E.Present x z) :
  z ∈ E.presentNeighbours x
AKLT.W.REC096.step_status_ne {G : Finset Plane} (E : Network G) (y o x : Plane) (hx : x ≠ y) :
  (traceStep E y o).status x = E.status x
AKLT.W.REC096.step_active_subset {G : Finset Plane} (E : Network G) (y o : Plane) : (traceStep E y o).active ⊆ E.active
AKLT.W.REC096.step_kept_iff {G : Finset Plane} (E : Network G) (y o x z : Plane) :
  z ∈ (traceStep E y o).kept x ↔ z ∈ E.kept x ∧ ¬(x = y ∧ z = o) ∧ ¬(x = o ∧ z = y)
AKLT.W.REC096.PrefixInvariant {G : Finset Plane} (E : Network G) (y a : Plane) : Prop
AKLT.W.REC096.invariant_step {G : Finset Plane} {E : Network G} {y a o : Plane} (h : PrefixInvariant E y a)
  (hS : y ∉ protectedSites G) (hp : E.Present y o) : PrefixInvariant (traceStep E y o) o y
AKLT.W.REC096.step_preserves_unused {G : Finset Plane} {E : Network G} {y a o x z : Plane} (h : PrefixInvariant E y a)
  (hp : E.Present y o) (hxz : E.Present x z) (hne : {x, z} ≠ {y, o}) : (traceStep E y o).Present x z
AKLT.W.REC096.initial_invariant (p : PairSetup) : PrefixInvariant p.normalized p.u p.c
AKLT.W.REC096.word_vertex_zero {n : ℕ} (u : Plane) (w : DirectionWord n) : wordVertex u w 0 = u
AKLT.W.REC096.word_vertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j < n) :
  wordVertex u w (j + 1) = wordVertex u w j + (w ⟨j, hj⟩).step
AKLT.W.REC096.trace_concat {G : Finset Plane} (E : Network G) (l : List Plane) (y o : Plane) :
  traceNetwork E (l ++ [y, o]) = traceStep (traceNetwork E (l ++ [y])) y o
AKLT.W.REC096.prefix_zero {G : Finset Plane} {n : ℕ} (E : Network G) (u : Plane) (w : DirectionWord n) :
  prefixNetwork E u w 0 = E
AKLT.W.REC096.prefix_step {G : Finset Plane} {n : ℕ} (E : Network G) (u : Plane) (w : DirectionWord n) (j : ℕ)
  (hj : j < n) :
  prefixNetwork E u w (j + 1) = traceStep (prefixNetwork E u w j) (wordVertex u w j) (wordVertex u w (j + 1))
AKLT.W.REC096.arrivalSite {n : ℕ} (p : PairSetup) (w : DirectionWord n) (j : ℕ) : Plane
AKLT.W.REC096.prefix_invariant {n : ℕ} (p : PairSetup) (T : Finset Plane) (w : DirectionWord n)
  (ht : StoppedNetworkTrail p.normalized p.u T w) (j : ℕ) (hj : j ≤ n) :
  PrefixInvariant (prefixNetwork p.normalized p.u w j) (wordVertex p.u w j) (arrivalSite p w j) ∧
    ∀ (k : Fin n),
      j ≤ ↑k → (prefixNetwork p.normalized p.u w j).Present (wordVertex p.u w ↑k) (wordVertex p.u w (↑k + 1))
AKLT.W.REC096.arrival_eq {n : ℕ} (p : PairSetup) (w : DirectionWord n) (i : Fin n) :
  arrivalSite p w ↑i = wordVertex p.u w ↑i - (wordIncoming p.incoming w i).step
AKLT.W.REC096.template_sites_eq :
  templateSites =
    {(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1), (1, 1), (-1, 1), (-1, -1), (1, -1), (2, 0), (0, 2), (-2, 0), (0, -2)}
AKLT.W.REC096.neighbours_zero : neighbours (0, 0) = {(1, 0), (0, 1), (-1, 0), (0, -1)}
AKLT.W.REC096.canonicalOutgoing : Compass → Compass → Compass
AKLT.W.REC096.canonical_outgoing_step (a b : Compass) : normalizeRotation a (canonicalOutgoing a b).step = b.step
AKLT.W.REC096.canonical_south (a b : Compass) : canonicalOutgoing a b = Compass.south ↔ b = a.reverse
AKLT.W.REC096.pullKept {G : Finset Plane} (E : Network G) (y : Plane) (a : Compass) (z : Plane) : Finset Plane
AKLT.W.REC096.mem_pullKept {G : Finset Plane} (E : Network G) (y : Plane) (a : Compass) (z t : Plane) :
  t ∈ pullKept E y a z ↔ (chart y a) t ∈ E.kept ((chart y a) z)
AKLT.W.REC096.pullKept_sub {G : Finset Plane} {E : Network G} {y arrival : Plane} {a : Compass}
  (h : PrefixInvariant E y arrival) (z : Plane) : pullKept E y a z ⊆ neighbours z
AKLT.W.REC096.completedKept {G : Finset Plane} (E : Network G) (y : Plane) (a : Compass) (z : Plane) : Finset Plane
AKLT.W.REC096.completedKept_sub {G : Finset Plane} {E : Network G} {y arrival : Plane} {a : Compass}
  (h : PrefixInvariant E y arrival) (z : Plane) : completedKept E y a z ⊆ neighbours z
AKLT.W.REC096.extractedPattern {G : Finset Plane} (E : Network G) (y : Plane) (a out : Compass) : PatternData
AKLT.W.REC096.extracted_status {G : Finset Plane} (E : Network G) (y : Plane) (a out : Compass) {z : Plane}
  (hz : z ∈ templateSites) :
  (extractedPattern E y a out).statusAt z = if z ∈ templateTips then Status.U else E.status ((chart y a) z)
AKLT.W.REC096.extracted_kept {G : Finset Plane} {E : Network G} {y arrival : Plane} {a out : Compass}
  (h : PrefixInvariant E y arrival) {z : Plane} (hz : z ∈ templateSites) :
  (extractedPattern E y a out).keptAt z = completedKept E y a z
AKLT.W.REC096.completed_mem_internal {G : Finset Plane} {E : Network G} {y arrival : Plane} {a : Compass}
  (h : PrefixInvariant E y arrival) (hG : ∀ z ∈ templateSites, (chart y a) z ∈ G) {z t : Plane} (hz : z ∈ templateSites)
  (ht : t ∈ templateSites) : t ∈ completedKept E y a z ↔ (chart y a) t ∈ E.kept ((chart y a) z)
AKLT.W.REC096.completed_D_card {G : Finset Plane} {E : Network G} {y arrival : Plane} {a : Compass}
  (h : PrefixInvariant E y arrival) {z : Plane} (hzG : (chart y a) z ∈ G) (hz : z ≠ (0, 0))
  (hd : E.status ((chart y a) z) = Status.D) : (completedKept E y a z).card = 2
AKLT.W.REC096.completed_center {G : Finset Plane} {E : Network G} {y : Plane} {a : Compass}
  (h : PrefixInvariant E y (y - a.step)) (hy : y ∈ G) (hS : y ∉ protectedSites G) (hu : E.status y = Status.U) :
  completedKept E y a (0, 0) = {(1, 0), (0, 1), (-1, 0)}
AKLT.W.REC096.internalBonds_iff (S : Finset Plane) (x z : Plane) :
  (x, z) ∈ internalBonds S ↔ x ∈ S ∧ z ∈ S ∧ z ∈ positiveNeighbours x
AKLT.W.REC096.unoriented_internalBonds (S : Finset Plane) (x z : Plane) :
  (x, z) ∈ internalBonds S ∨ (z, x) ∈ internalBonds S ↔ x ∈ S ∧ z ∈ S ∧ Adjacent x z
AKLT.W.REC096.internal_present_iff (π : PatternData) {z t : Plane} (hz : z ∈ templateSites) (ht : t ∈ templateSites) :
  π.InternalPresent z t ↔
    Adjacent z t ∧
      π.statusAt z ≠ Status.X ∧
        π.statusAt t ≠ Status.X ∧ (z ∈ templateTips ∨ t ∈ π.keptAt z) ∧ (t ∈ templateTips ∨ z ∈ π.keptAt t)
AKLT.W.REC096.template_step (d : Compass) : d.step ∈ templateSites ∧ d.step ∉ templateTips
AKLT.W.REC096.template_tips_sub : templateTips ⊆ templateSites
AKLT.W.REC096.template_corner_facts {z : Plane} (hz : z ∈ templateCorners) :
  z ∈ templateSites ∧ z ∉ templateTips ∧ z ≠ (0, 0)
AKLT.W.REC096.invariant_covered {G : Finset Plane} {E : Network G} {y : Plane} {a out : Compass}
  (h : PrefixInvariant E y (y - a.step)) (hy : y ∈ G) (hS : y ∉ protectedSites G) (hu : E.status y = Status.U)
  (hp : E.Present y (y + out.step)) : AKLT.Defs.CoveredDepartureV2 E y a out
AKLT.W.REC096.main : CoveredClosureStatementV2
```

## Complete theorem dependency output

```text
'AKLT.W.REC096.natAbs_sub_comm' depends on axioms: [propext]
'AKLT.W.REC096.natAbs_neg_add' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC096.step_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.neighbours_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.adjacent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.adjacent_symm' depends on axioms: [propext]
'AKLT.W.REC096.adjacent_ne' depends on axioms: [propext]
'AKLT.W.REC096.step_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.chart_apply' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC096.chart_zero' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC096.chart_south' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC096.chart_dist' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC096.chart_adjacent' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC096.chart_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.interior_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.template_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.template_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.present_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.step_status_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.step_active_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.step_kept_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.invariant_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.step_preserves_unused' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.initial_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.word_vertex_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.word_vertex_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.trace_concat' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.prefix_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.prefix_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.prefix_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.arrival_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.template_sites_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.neighbours_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.canonical_outgoing_step' does not depend on any axioms
'AKLT.W.REC096.canonical_south' does not depend on any axioms
'AKLT.W.REC096.mem_pullKept' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.pullKept_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.completedKept_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.extracted_status' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.extracted_kept' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.completed_mem_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.completed_D_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.completed_center' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.internalBonds_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.unoriented_internalBonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.internal_present_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.template_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.template_tips_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.template_corner_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.invariant_covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC096.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues

None. No other blueprint leaf is assumed, and no residual proposition remains.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/REC096/Main.lean` with the exact export `AKLT.W.REC096.main : AKLT.Blueprint.Rec.CoveredClosureStatementV2`.
- Helpers: `Geometry.lean`, `Trace.lean`, `Prefix.lean`, and `Template.lean`.
- `Audit.lean` checks the exact type and the dependencies of all 52 explicitly declared theorems.
- The main build and the independent import/type audit pass.
- Main dependencies: `propext`, `Classical.choice`, `Quot.sound`.
- Open names: none. Residual assumptions: none. Limitations or deviations: none.
- Orchestrator can accept REC096; no premise repair or downstream decision is needed.
