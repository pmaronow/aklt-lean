STATUS: PROVED

Delivered `AKLT.W.H1M006.main : AKLT.Blueprint.H1.PassageFubiniStatement`. Both passage identities are proved from the frozen statement’s own one-site premise and coveredness. No other blueprint leaf is used as a lemma, and no residual assumptions remain.

Files:

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M006/AKLT/W/H1M006/Main.lean): the required theorem and the outer finite-sum reindexing.
- [Basic.lean](/home/ubuntu/aklt/wt/LW_H1M006/AKLT/W/H1M006/Basic.lean): summands and the passage/complement assignment equivalence, reused and cleaned from the earlier attempt.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1M006/AKLT/W/H1M006/Geometry.lean): covered passage-bond characterization and absence of external slots at the origin.
- [Split.lean](/home/ubuntu/aklt/wt/LW_H1M006/AKLT/W/H1M006/Split.lean): coordinate and site-weight factorization.
- [Bonds.lean](/home/ubuntu/aklt/wt/LW_H1M006/AKLT/W/H1M006/Bonds.lean): bond-product factorization, including zero spins at removed neighbours.
- [Local.lean](/home/ubuntu/aklt/wt/LW_H1M006/AKLT/W/H1M006/Local.lean): local summand factorization and integration using exactly the supplied one-site equations.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_H1M006/AKLT/W/H1M006/Audit.lean): the exact-type example, declaration checks, and axiom audit for all public theorems.
- [audit.log](/home/ubuntu/aklt/reports/LW/H1M006/audit.log): complete successful audit build output.
- [audit-time.txt](/home/ubuntu/aklt/reports/LW/H1M006/audit-time.txt): audit wall/CPU timings.

Only task-directory Lean files and this task’s report artifacts were written. Frozen statements and other project files were not edited.

The proof first identifies the three possible incident edges. Coveredness supplies reciprocity at each nonremoved neighbour and excludes the south edge. Removed neighbours have zero spin, so their added linear factors equal one. Splitting assignments at the origin separates its U or D weight from the complementary weights. The remaining bond factors and all twenty slot factors are independent of that coordinate. The supplied U equation integrates three factors; the supplied D equation integrates the two factors left after deleting the outgoing bond. Finally, the assignment equivalence reindexes the finite sum.

Exported declarations with their checked types (verbatim `#check` output, with diagnostic location prefixes removed):

```text
AKLT.W.H1M006.passageComplement (π : AKLT.Defs.PatternData) : Finset AKLT.Defs.Plane
AKLT.W.H1M006.originalSummand (π : AKLT.Defs.PatternData) (next : Bool) (m : Fin 20 → AKLT.Defs.UnitVector)
  (n : ↥π.active → AKLT.Defs.SpinLetter) : ℝ
AKLT.W.H1M006.erasedSummand (π : AKLT.Defs.PatternData) (m : Fin 20 → AKLT.Defs.UnitVector)
  (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) (n : ↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) : ℝ
AKLT.W.H1M006.splitAssignments (π : AKLT.Defs.PatternData) (h0 : (0, 0) ∈ π.active) :
  (↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) × AKLT.Defs.SpinLetter ≃
    (↥π.active → AKLT.Defs.SpinLetter)
AKLT.W.H1M006.origin_mem_template : (0, 0) ∈ AKLT.Defs.templateSites
AKLT.W.H1M006.origin_active (π : AKLT.Defs.PatternData) (hπ : π.Covered) : (0, 0) ∈ π.active
AKLT.W.H1M006.passageSites : Finset AKLT.Defs.Plane
AKLT.W.H1M006.passageEdges : Finset (AKLT.Defs.Plane × AKLT.Defs.Plane)
AKLT.W.H1M006.mem_active_iff (π : AKLT.Defs.PatternData) (x : AKLT.Defs.Plane) :
  x ∈ π.active ↔ π.statusAt x ≠ AKLT.Defs.Status.X
AKLT.W.H1M006.passage_sites_geometry (x : AKLT.Defs.Plane) (hx : x ∈ AKLT.W.H1M006.passageSites) :
  x ∈ AKLT.Defs.templateSites \ AKLT.Defs.templateTips ∧ AKLT.Defs.Adjacent (0, 0) x ∧ x ≠ (0, 0)
AKLT.W.H1M006.origin_not_tip : (0, 0) ∉ AKLT.Defs.templateTips
AKLT.W.H1M006.passage_kept (π : AKLT.Defs.PatternData) (hπ : π.Covered) (x : AKLT.Defs.Plane)
  (hx : x ∈ AKLT.W.H1M006.passageSites) (hs : π.statusAt x ≠ AKLT.Defs.Status.X) : (0, 0) ∈ π.keptAt x
AKLT.W.H1M006.template_incident_edges :
  {e ∈ AKLT.Defs.internalBonds AKLT.Defs.templateSites | e.1 = (0, 0) ∨ e.2 = (0, 0)} =
    insert ((0, -1), 0, 0) AKLT.W.H1M006.passageEdges
AKLT.W.H1M006.passage_edge_internal (e : AKLT.Defs.Plane × AKLT.Defs.Plane) (he : e ∈ AKLT.W.H1M006.passageEdges) :
  e ∈ AKLT.Defs.internalBonds AKLT.Defs.templateSites
AKLT.W.H1M006.covered_incident_subset (π : AKLT.Defs.PatternData) (hπ : π.Covered)
  (e : AKLT.Defs.Plane × AKLT.Defs.Plane) (he : e ∈ π.bonds) (h : e.1 = (0, 0) ∨ e.2 = (0, 0)) :
  e ∈ AKLT.W.H1M006.passageEdges
AKLT.W.H1M006.passage_edge_mem_iff (π : AKLT.Defs.PatternData) (hπ : π.Covered) (e : AKLT.Defs.Plane × AKLT.Defs.Plane)
  (he : e ∈ AKLT.W.H1M006.passageEdges) :
  e ∈ π.bonds ↔ π.statusAt e.1 ≠ AKLT.Defs.Status.X ∧ π.statusAt e.2 ≠ AKLT.Defs.Status.X
AKLT.W.H1M006.covered_incident_edges (π : AKLT.Defs.PatternData) (hπ : π.Covered) :
  {e ∈ π.bonds | e.1 = (0, 0) ∨ e.2 = (0, 0)} =
    {e ∈ AKLT.W.H1M006.passageEdges | π.statusAt e.1 ≠ AKLT.Defs.Status.X ∧ π.statusAt e.2 ≠ AKLT.Defs.Status.X}
AKLT.W.H1M006.external_not_origin (j : Fin 20) : (AKLT.Defs.externalSlot j).1 ≠ (0, 0)
AKLT.W.H1M006.split_spins (π : AKLT.Defs.PatternData) (h0 : (0, 0) ∈ π.active)
  (n : ↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) (p : AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) :
  π.spins ((AKLT.W.H1M006.splitAssignments π h0) (n, p)) x =
    if x = (0, 0) then AKLT.Defs.spinVector p else AKLT.Defs.supportSpins (AKLT.W.H1M006.passageComplement π) n x
AKLT.W.H1M006.prod_subtype_erase (V : Finset AKLT.Defs.Plane) (a : AKLT.Defs.Plane) (ha : a ∈ V) (f : ↥V → ℝ) :
  ∏ x, f x = f ⟨a, ha⟩ * ∏ x, f ⟨↑x, ⋯⟩
AKLT.W.H1M006.split_weights (π : AKLT.Defs.PatternData) (hπ : π.Covered) (next : Bool)
  (n : ↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) (p : AKLT.Defs.SpinLetter) :
  ∏ x,
      AKLT.Defs.spinWeight (if next = true ∧ ↑x = (0, 0) then AKLT.Defs.Status.D else π.statusAt ↑x)
        ((AKLT.W.H1M006.splitAssignments π ⋯) (n, p) x) =
    AKLT.Defs.spinWeight (if next = true then AKLT.Defs.Status.D else AKLT.Defs.Status.U) p *
      ∏ x, AKLT.Defs.spinWeight (π.statusAt ↑x) (n x)
AKLT.W.H1M006.dot_symm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
AKLT.W.H1M006.dot_zero_right (a : AKLT.Defs.Vec3) : AKLT.Defs.dot a 0 = 0
AKLT.W.H1M006.dot_zero_left (a : AKLT.Defs.Vec3) : AKLT.Defs.dot 0 a = 0
AKLT.W.H1M006.bondFactor (π : AKLT.Defs.PatternData) (next : Bool) (N : AKLT.Defs.Plane → AKLT.Defs.Vec3)
  (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : ℝ
AKLT.W.H1M006.bondProduct (π : AKLT.Defs.PatternData) (next : Bool) (N : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
AKLT.W.H1M006.remainingBondProduct (π : AKLT.Defs.PatternData) (N : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
AKLT.W.H1M006.slotProduct (π : AKLT.Defs.PatternData) (m : Fin 20 → AKLT.Defs.UnitVector)
  (N : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
AKLT.W.H1M006.localPassageFactor (next : Bool) (z a b o : AKLT.Defs.Vec3) : ℝ
AKLT.W.H1M006.out_edge_incident (π : AKLT.Defs.PatternData) (e : AKLT.Defs.Plane × AKLT.Defs.Plane)
  (h : {e.1, e.2} = {(0, 0), π.outgoing.step}) : e.1 = (0, 0) ∨ e.2 = (0, 0)
AKLT.W.H1M006.split_bond_product (π : AKLT.Defs.PatternData) (hπ : π.Covered) (next : Bool)
  (N : AKLT.Defs.Plane → AKLT.Defs.Vec3)
  (hzero : ∀ (x : AKLT.Defs.Plane), π.statusAt x = AKLT.Defs.Status.X → N x = 0) :
  AKLT.W.H1M006.bondProduct π next N =
    AKLT.W.H1M006.remainingBondProduct π N * ∏ e ∈ AKLT.W.H1M006.passageEdges, AKLT.W.H1M006.bondFactor π next N e
AKLT.W.H1M006.origin_pair_eq (x o : AKLT.Defs.Plane) (hx : x ≠ (0, 0)) : {(0, 0), x} = {(0, 0), o} ↔ x = o
AKLT.W.H1M006.passage_edges_product (π : AKLT.Defs.PatternData) (next : Bool) (N : AKLT.Defs.Plane → AKLT.Defs.Vec3)
  (f g : AKLT.Defs.Plane) (hn : AKLT.Blueprint.H1.PassageNeighbours π f g) :
  ∏ e ∈ AKLT.W.H1M006.passageEdges, AKLT.W.H1M006.bondFactor π next N e =
    AKLT.W.H1M006.localPassageFactor next (N (0, 0)) (N f) (N g) (N π.outgoing.step)
AKLT.W.H1M006.factor_bonds (π : AKLT.Defs.PatternData) (hπ : π.Covered) (next : Bool)
  (N : AKLT.Defs.Plane → AKLT.Defs.Vec3) (hzero : ∀ (x : AKLT.Defs.Plane), π.statusAt x = AKLT.Defs.Status.X → N x = 0)
  (f g : AKLT.Defs.Plane) (hn : AKLT.Blueprint.H1.PassageNeighbours π f g) :
  AKLT.W.H1M006.bondProduct π next N =
    AKLT.W.H1M006.remainingBondProduct π N *
      AKLT.W.H1M006.localPassageFactor next (N (0, 0)) (N f) (N g) (N π.outgoing.step)
AKLT.W.H1M006.complementWeight (π : AKLT.Defs.PatternData) (m : Fin 20 → AKLT.Defs.UnitVector)
  (n : ↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) : ℝ
AKLT.W.H1M006.erasedSummand_eq (π : AKLT.Defs.PatternData) (m : Fin 20 → AKLT.Defs.UnitVector)
  (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) (n : ↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) :
  AKLT.W.H1M006.erasedSummand π m F n =
    AKLT.W.H1M006.complementWeight π m n * F (AKLT.Defs.supportSpins (AKLT.W.H1M006.passageComplement π) n)
AKLT.W.H1M006.spins_removed (π : AKLT.Defs.PatternData) (n : ↥π.active → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane)
  (hx : π.statusAt x = AKLT.Defs.Status.X) : π.spins n x = 0
AKLT.W.H1M006.split_remaining_bonds (π : AKLT.Defs.PatternData) (h0 : (0, 0) ∈ π.active)
  (n : ↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) (p : AKLT.Defs.SpinLetter) :
  AKLT.W.H1M006.remainingBondProduct π (π.spins ((AKLT.W.H1M006.splitAssignments π h0) (n, p))) =
    AKLT.W.H1M006.remainingBondProduct π (AKLT.Defs.supportSpins (AKLT.W.H1M006.passageComplement π) n)
AKLT.W.H1M006.split_slots (π : AKLT.Defs.PatternData) (h0 : (0, 0) ∈ π.active) (m : Fin 20 → AKLT.Defs.UnitVector)
  (n : ↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) (p : AKLT.Defs.SpinLetter) :
  AKLT.W.H1M006.slotProduct π m (π.spins ((AKLT.W.H1M006.splitAssignments π h0) (n, p))) =
    AKLT.W.H1M006.slotProduct π m (AKLT.Defs.supportSpins (AKLT.W.H1M006.passageComplement π) n)
AKLT.W.H1M006.neighbours_not_origin (π : AKLT.Defs.PatternData) (f g : AKLT.Defs.Plane)
  (hn : AKLT.Blueprint.H1.PassageNeighbours π f g) : f ≠ (0, 0) ∧ g ≠ (0, 0) ∧ π.outgoing.step ≠ (0, 0)
AKLT.W.H1M006.originalSummand_factorized (π : AKLT.Defs.PatternData) (hπ : π.Covered) (next : Bool)
  (m : Fin 20 → AKLT.Defs.UnitVector) (f g : AKLT.Defs.Plane) (hn : AKLT.Blueprint.H1.PassageNeighbours π f g)
  (n : ↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) (p : AKLT.Defs.SpinLetter) :
  AKLT.W.H1M006.originalSummand π next m ((AKLT.W.H1M006.splitAssignments π ⋯) (n, p)) =
    AKLT.W.H1M006.complementWeight π m n *
      (AKLT.Defs.spinWeight (if next = true then AKLT.Defs.Status.D else AKLT.Defs.Status.U) p *
        AKLT.W.H1M006.localPassageFactor next (AKLT.Defs.spinVector p)
          (AKLT.Defs.supportSpins (AKLT.W.H1M006.passageComplement π) n f)
          (AKLT.Defs.supportSpins (AKLT.W.H1M006.passageComplement π) n g)
          (AKLT.Defs.supportSpins (AKLT.W.H1M006.passageComplement π) n π.outgoing.step))
AKLT.W.H1M006.local_fubini
  (hSite :
    ∀ (a b o : AKLT.Defs.Vec3),
      (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun z =>
            (1 + AKLT.Defs.dot z a) * (1 + AKLT.Defs.dot z b) * (1 + AKLT.Defs.dot z o)) =
          1 + (AKLT.Defs.dot a b + AKLT.Defs.dot a o + AKLT.Defs.dot b o) / 3 ∧
        (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun z => (1 + AKLT.Defs.dot z a) * (1 + AKLT.Defs.dot z b)) =
          1 + AKLT.Defs.dot a b / 5)
  (π : AKLT.Defs.PatternData) (hπ : π.Covered) (m : Fin 20 → AKLT.Defs.UnitVector) (f g : AKLT.Defs.Plane)
  (hn : AKLT.Blueprint.H1.PassageNeighbours π f g) (n : ↥(AKLT.W.H1M006.passageComplement π) → AKLT.Defs.SpinLetter) :
  ∑ p, AKLT.W.H1M006.originalSummand π false m ((AKLT.W.H1M006.splitAssignments π ⋯) (n, p)) =
      AKLT.W.H1M006.erasedSummand π m (AKLT.Blueprint.H1.passageI π.outgoing.step f g) n ∧
    ∑ p, AKLT.W.H1M006.originalSummand π true m ((AKLT.W.H1M006.splitAssignments π ⋯) (n, p)) =
      AKLT.W.H1M006.erasedSummand π m (AKLT.Blueprint.H1.passageJ f g) n
AKLT.W.H1M006.main : AKLT.Blueprint.H1.PassageFubiniStatement
```

Axiom audit: every public theorem and `splitAssignments` was checked. All use only the allowed axioms `propext`, `Classical.choice`, and `Quot.sound`. Verbatim `#print axioms` output, with diagnostic location prefixes removed:

```text
'AKLT.W.H1M006.splitAssignments' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.origin_mem_template' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.origin_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.mem_active_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.passage_sites_geometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.origin_not_tip' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.passage_kept' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.template_incident_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.passage_edge_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.covered_incident_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.passage_edge_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.covered_incident_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.external_not_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.split_spins' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.prod_subtype_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.split_weights' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.dot_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.dot_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.dot_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.out_edge_incident' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.split_bond_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.origin_pair_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.passage_edges_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.factor_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.erasedSummand_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.spins_removed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.split_remaining_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.split_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.neighbours_not_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.originalSummand_factorized' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.local_fubini' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M006.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build and verification commands were run with `PATH="$HOME/.elan/bin:$PATH"`:

| Command | Result | Timing |
| --- | --- | --- |
| `lake build AKLT.W.H1M006.Main` | Success, all six proof modules rebuilt without warnings | 36.99 s wall; Main module 9.9 s |
| `lake build AKLT.W.H1M006.Audit` | Success; exact-type example and all declaration/axiom checks passed | 9.82 s wall; Audit module 4.7 s |

The source scan found no prohibited proof escape, effectful command, or heartbeat override. Closed finite geometry checks use `decide +kernel`.

Open issues: none. The earlier `Residual_currentLocal`, `Residual_nextLocal`, and `main_of_residuals` reduction has been replaced by the proved `local_fubini` and the exact required `main`.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M006/Main.lean` with `AKLT.W.H1M006.main : AKLT.Blueprint.H1.PassageFubiniStatement`.
- Supporting proof modules: Basic, Geometry, Split, Bonds, Local.
- Audit module verifies the exact type and checks every public theorem’s axioms.
- Both Main and Audit build successfully; only allowed axioms occur.
- Open declarations: none. No residual hypotheses or other blueprint-leaf dependencies.
- Reused the earlier assignment split and completed the missing local factorization.
- Limitations/deviations: none. No frozen or unrelated files were changed.
- Orchestrator: accept the proved leaf and pass `AKLT.W.H1M006.main` to assembly.
