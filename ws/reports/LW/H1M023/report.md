STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M023/AKLT/W/H1M023/Main.lean): the requested theorem with exactly the requested name and type.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1M023/AKLT/W/H1M023/Geometry.lean): kernel-checked finite template geometry, unique leaf bonds, and retention of replacement endpoints.
- [Count.lean](/home/ubuntu/aklt/wt/LW_H1M023/AKLT/W/H1M023/Count.lean): charge each replacement to its deleted bond; bound the total degree budget and prove it vanishes outside the retained sites.
- [Degree.lean](/home/ubuntu/aklt/wt/LW_H1M023/AKLT/W/H1M023/Degree.lean): polynomial support bounds under sums, products, scalar factors, and finite products; internal admissibility.
- [Check.lean](/home/ubuntu/aklt/wt/LW_H1M023/AKLT/W/H1M023/Check.lean): an exact-type assignment and declaration/axiom checks for every exported theorem.
- [check.log](/home/ubuntu/aklt/reports/LW/H1M023/check.log): full checker output and measured elapsed time.

No tracked project files outside the assigned directory were changed. The original frozen statement and its definitions are unchanged. The earlier report remains in `report.luna.md`.

## Result and proof

```lean
theorem AKLT.W.H1M023.main : AKLT.Blueprint.H1.ReducedDegreeStatement
```

The proof establishes the stronger `reducedIntegrand_admissible` for arbitrary raw `PatternData`, without needing coveredness. Every replacement has one original incident bond, and its other endpoint belongs to the retained set. Each original bond pays for at most one retained bond factor or replacement factor at a given site. The retained corner fields contribute at most two more units, while a corner has at most two original bonds. Other sites have at most four original bonds. The resulting degree budget is at most four everywhere and zero outside `reducedSpinSites`, proving both clauses of `InternalAdmissible`.

The polynomial support lemmas reuse useful work from the earlier attempt. All residual statements from that attempt have been replaced with proofs. No other blueprint leaf is used as an assumption or lemma.

## Exported declarations and statements

The following is the complete `#check` output, including the helper definitions and all exported theorem statements:

```text
AKLT.W.H1M023.bond_info (π : AKLT.Defs.PatternData) {e : AKLT.Defs.Plane × AKLT.Defs.Plane} (he : e ∈ π.bonds) :
  e.1 ∈ π.active ∧
    e.2 ∈ π.active ∧
      e.1 ≠ e.2 ∧
        ¬(e.1 ∈ AKLT.Defs.templateCorners ∪ AKLT.Defs.templateTips ∧
            e.2 ∈ AKLT.Defs.templateCorners ∪ AKLT.Defs.templateTips)
AKLT.W.H1M023.pattern_degree_bound (π : AKLT.Defs.PatternData) (x : AKLT.Defs.Plane) :
  AKLT.Defs.patternDegree π x ≤ if x ∈ AKLT.Defs.templateCorners then 2 else 4
AKLT.W.H1M023.pattern_tip_degree_bound (π : AKLT.Defs.PatternData) {x : AKLT.Defs.Plane}
  (hx : x ∈ AKLT.Defs.templateTips) : AKLT.Defs.patternDegree π x ≤ 1
AKLT.W.H1M023.positive_degree_active (π : AKLT.Defs.PatternData) {x : AKLT.Defs.Plane}
  (hx : 0 < AKLT.Defs.patternDegree π x) : x ∈ π.active
AKLT.W.H1M023.group_pair_retained (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) {x : AKLT.Defs.Plane}
  (hx : x ∈ AKLT.Defs.reductionGroups π) (hp : AKLT.Defs.groupIsPair π r x = true) : x ∈ AKLT.Defs.reducedSpinSites π r
AKLT.W.H1M023.group_single (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) {x : AKLT.Defs.Plane}
  (hx : x ∈ AKLT.Defs.reductionGroups π) (hp : AKLT.Defs.groupIsPair π r x = false) :
  AKLT.Defs.SingleReplacement π r x ∧ x ∉ AKLT.Defs.reducedSpinSites π r
AKLT.W.H1M023.otherEnd (x : AKLT.Defs.Plane) (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : AKLT.Defs.Plane
AKLT.W.H1M023.leaf_bond (π : AKLT.Defs.PatternData) {x : AKLT.Defs.Plane} (hx : AKLT.Defs.patternDegree π x = 1) :
  ∃ e ∈ π.bonds,
    (e.1 = x ∨ e.2 = x) ∧
      AKLT.Defs.leafNeighbour π x = AKLT.W.H1M023.otherEnd x e ∧ ∀ f ∈ π.bonds, f.1 = x ∨ f.2 = x → f = e
AKLT.W.H1M023.group_single_neighbour_retained (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  {x : AKLT.Defs.Plane} (hx : x ∈ AKLT.Defs.reductionGroups π) (hp : AKLT.Defs.groupIsPair π r x = false) :
  AKLT.Defs.leafNeighbour π x ∈ AKLT.Defs.reducedSpinSites π r
AKLT.W.H1M023.bondCost (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x : AKLT.Defs.Plane)
  (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : ℕ
AKLT.W.H1M023.pairCost (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x y : AKLT.Defs.Plane) : ℕ
AKLT.W.H1M023.singleCost (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x y : AKLT.Defs.Plane) : ℕ
AKLT.W.H1M023.replacementCost (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x y : AKLT.Defs.Plane)
  (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : ℕ
AKLT.W.H1M023.degreeBudget (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x : AKLT.Defs.Plane) : ℕ
AKLT.W.H1M023.singleCost_eq_sum (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x : AKLT.Defs.Plane)
  {y : AKLT.Defs.Plane} (hy : y ∈ AKLT.Defs.reductionGroups π) :
  AKLT.W.H1M023.singleCost π r x y = ∑ e ∈ π.bonds, AKLT.W.H1M023.replacementCost π r x y e
AKLT.W.H1M023.bonds_and_singles_le (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x : AKLT.Defs.Plane) :
  ∑ e ∈ π.bonds, AKLT.W.H1M023.bondCost π r x e + ∑ y ∈ AKLT.Defs.reductionGroups π, AKLT.W.H1M023.singleCost π r x y ≤
    AKLT.Defs.patternDegree π x
AKLT.W.H1M023.pairs_le (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x : AKLT.Defs.Plane) :
  ∑ y ∈ AKLT.Defs.reductionGroups π, AKLT.W.H1M023.pairCost π r x y ≤ if x ∈ AKLT.Defs.templateCorners then 2 else 0
AKLT.W.H1M023.degreeBudget_le_four (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x : AKLT.Defs.Plane) :
  AKLT.W.H1M023.degreeBudget π r x ≤ 4
AKLT.W.H1M023.degreeBudget_zero (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (x : AKLT.Defs.Plane)
  (hx : x ∉ AKLT.Defs.reducedSpinSites π r) : AKLT.W.H1M023.degreeBudget π r x = 0
AKLT.W.H1M023.reducedIntegrand_degreeBudget (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (next : Bool)
  (x : AKLT.Defs.Plane) (m : AKLT.Defs.LocalVariable →₀ ℕ) :
  m ∈ (AKLT.Defs.reducedIntegrand π r next).support → ∑ k, m (Sum.inl (x, k)) ≤ AKLT.W.H1M023.degreeBudget π r x
AKLT.W.H1M023.reducedIntegrand_admissible (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (next : Bool) :
  AKLT.Blueprint.H1.InternalAdmissible (AKLT.Defs.reducedSpinSites π r) (AKLT.Defs.reducedIntegrand π r next)
AKLT.W.H1M023.main : AKLT.Blueprint.H1.ReducedDegreeStatement
```

## Axioms

Every exported theorem was checked with `#print axioms`. The complete output is:

```text
'AKLT.W.H1M023.bond_info' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.pattern_degree_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.pattern_tip_degree_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.positive_degree_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.group_pair_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.group_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.leaf_bond' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.group_single_neighbour_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.singleCost_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.bonds_and_singles_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.pairs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.degreeBudget_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.degreeBudget_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.reducedIntegrand_degreeBudget' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.reducedIntegrand_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M023.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only `propext`, `Classical.choice`, and `Quot.sound` occur. The three finite template checks use `decide +kernel`. A source scan found none of the forbidden proof shortcuts.

## Builds and timings

Commands used `PATH="$HOME/.elan/bin:$PATH"`.

- `lake build AKLT.W.H1M023.Geometry`: successful; Lake reported 6.1 s for the geometry module.
- `/usr/bin/time -f 'ELAPSED_SECONDS=%e' lake build AKLT.W.H1M023.Main`: successful, 28.67 s elapsed. Rebuilt Count (5.2 s), Degree (12 s), and Main (5.3 s), with no warnings or errors.
- `/usr/bin/time -f 'ELAPSED_SECONDS=%e' lake env lean AKLT/W/H1M023/Check.lean`: successful, 6.00 s elapsed. The exact-type example compiled, and `#check` found `AKLT.W.H1M023.main : AKLT.Blueprint.H1.ReducedDegreeStatement`.

## Open issues

None. There are no residual obligations or additional premises.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/H1M023/Main.lean` and four helper/check modules in the same directory.
- Exact export: `AKLT.W.H1M023.main : AKLT.Blueprint.H1.ReducedDegreeStatement`.
- Both support and separate-degree clauses are proved.
- Stronger helper: `reducedIntegrand_admissible` holds without coveredness.
- No open declarations, residual premises, or dependencies on other blueprint leaves.
- All exported theorem axioms: `[propext, Classical.choice, Quot.sound]`.
- Main build and separate exact-type check pass.
- No frozen files were changed; no forbidden shortcuts were used.
- Limitations/deviations: none; the unused coveredness premise reflects the stronger helper.
- Orchestrator action: accept the exact export; no further mathematical decision is required.
