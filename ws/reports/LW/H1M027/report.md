STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M027/AKLT/W/H1M027/Main.lean): local leaf choices and the requested theorem.
- [Factors.lean](/home/ubuntu/aklt/wt/LW_H1M027/AKLT/W/H1M027/Factors.lean): atom norm bounds, peripheral classification, vector assignment, and evaluated factor identities.
- [Factorization.lean](/home/ubuntu/aklt/wt/LW_H1M027/AKLT/W/H1M027/Factorization.lean): extraction of the common product of normalizers and the separated-sum identity.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_H1M027/AKLT/W/H1M027/Audit.lean): exact-type check and axiom checks for all 21 exported theorems.
- [audit.log](/home/ubuntu/aklt/reports/LW/H1M027/audit.log): recorded exact-type and axiom output.

## Result and proof

```lean
theorem AKLT.W.H1M027.main :
    AKLT.Blueprint.H1.PeripheralAssignmentStatement
```

For each deleted site, select its positive isolated-site normalizer or its one-bond normalizer and ball vector from `LeafRule`. Set `K` to the product of these normalizers. The twenty-vector assignment retains the original corner slots, places each replacement in its leader slot, and sets unused tokens to zero. Classify each peripheral site as an isolated site, a retained pair, or a deleted single. The product of the retained fields and the normalized deleted factors equals the evaluated group product of `reducedIntegrand`. The icosahedral atom norm premise bounds every `supportSpins` argument, including the zero atom. Factor `K` out of the finite sum. Both `K` and the vector assignment are selected independently of `next`.

The earlier local-choice proof was reused. Its unproved residual and conditional `main_of_residual` have been replaced by proved factorization lemmas and unconditional `main`.

## Exported declarations and statements

All declarations below are in namespace `AKLT.W.H1M027`, with `AKLT.Defs` and `AKLT.Blueprint.H1` open and `BigOperators` scoped. Signatures are reproduced without proof terms; the three helper definitions have their defining equations in `Factors.lean`.

### Factors.lean

```lean
theorem dot_symm (a b : Vec3) : dot a b = dot b a

theorem normSq_zero : normSq (0 : Vec3) = 0

theorem supportSpins_ball (hIco : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (V : Finset Plane) (n : V → SpinLetter) (x : Plane) :
    normSq (supportSpins V n x) ≤ 1

theorem corner_not_tip {x : Plane} (hx : x ∈ templateCorners) : x ∉ templateTips

theorem slot_peripheral (j : Fin 20) :
    (externalSlot j).1 ∈ templateCorners ∪ templateTips

theorem leader_site {x : Plane} (hx : x ∈ templateCorners ∪ templateTips) :
    (externalSlot (groupLeader x)).1 = x

theorem second_site {x : Plane} (hx : x ∈ templateCorners) :
    (externalSlot (groupSecond x)).1 = x

theorem corner_field (m : Fin 20 → UnitVector) {x : Plane}
    (hx : x ∈ templateCorners) (z : Vec3) :
    coveredSiteField m x z =
      (1 + dot (m (groupLeader x)).val z) *
      (1 + dot (m (groupSecond x)).val z)

theorem degree_pos_active (π : PatternData) {x : Plane}
    (hx : 0 < patternDegree π x) : x ∈ π.active

theorem retained_peripheral_iff (π : PatternData) (r : Representation) {x : Plane}
    (hx : x ∈ templateCorners ∪ templateTips) :
    x ∈ reducedSpinSites π r ↔
      0 < patternDegree π x ∧ groupIsPair π r x = true

def assignedVectors (π : PatternData) (r : Representation) (m : Fin 20 → UnitVector)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3) (j : Fin 20) : Vec3

theorem assignedVectors_ball (π : PatternData) (r : Representation)
    (m : Fin 20 → UnitVector) (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (hv : ∀ x, normSq (v x) ≤ 1) (j : Fin 20) :
    normSq (assignedVectors π r m v j) ≤ 1

theorem retained_field_product (π : PatternData) (r : Representation)
    (m : Fin 20 → UnitVector) (n : Plane → Vec3) :
    (∏ j : Fin 20, if (externalSlot j).1 ∈ reducedSpinSites π r then
      1 + dot (m j).val (n (externalSlot j).1) else 1) =
    ∏ x ∈ templateCorners ∪ templateTips,
      if x ∈ reducedSpinSites π r then coveredSiteField m x (n x) else 1

def leafRemainder (π : PatternData) (r : Representation)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3) (n : Plane → Vec3) (x : Plane) : ℝ

def groupFactor (π : PatternData) (r : Representation) (u : Fin 20 → Vec3)
    (n : Plane → Vec3) (x : Plane) : ℝ

theorem assigned_leader (π : PatternData) (r : Representation) (m : Fin 20 → UnitVector)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3) {x : Plane}
    (hx : x ∈ reductionGroups π) :
    assignedVectors π r m v (groupLeader x) =
      if h : x ∈ deletedLeafSites π r then v ⟨x, h⟩ else (m (groupLeader x)).val

theorem assigned_second (π : PatternData) (r : Representation) (m : Fin 20 → UnitVector)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3) {x : Plane}
    (hx : x ∈ reductionGroups π) (hp : groupIsPair π r x = true) :
    assignedVectors π r m v (groupSecond x) = (m (groupSecond x)).val

theorem peripheral_factor (π : PatternData) (r : Representation)
    (m : Fin 20 → UnitVector) (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (n : Plane → Vec3) {x : Plane} (hx : x ∈ templateCorners ∪ templateTips) :
    (if x ∈ reducedSpinSites π r then coveredSiteField m x (n x) else 1) *
        leafRemainder π r v n x =
      if 0 < patternDegree π x then groupFactor π r (assignedVectors π r m v) n x else 1

theorem evaluate_reducedIntegrand (π : PatternData) (r : Representation)
    (next : Bool) (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (reducedIntegrand π r next) n u =
      (∏ e ∈ π.bonds, if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
        ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
          1 + dot (n e.1) (n e.2) else 1) *
      ∏ x ∈ reductionGroups π, groupFactor π r u n x

```

### Factorization.lean

```lean
theorem leaf_product (π : PatternData) (r : Representation)
    (hGeometry : PeripheralGeometry π r) (m : Fin 20 → UnitVector)
    (A : {x // x ∈ deletedLeafSites π r} → ℝ)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (hfactor : ∀ x n, normSq (n (leafNeighbour π x.1)) ≤ 1 →
      integratedLeafFactor π m x.1 n = A x *
        (if patternDegree π x.1 = 0 then 1 else
          1 + (replacementRadius π x.1 : ℝ) * dot (v x) (n (leafNeighbour π x.1))))
    (n : Plane → Vec3) (hn : ∀ x, normSq (n x) ≤ 1) :
    (∏ x ∈ deletedLeafSites π r, integratedLeafFactor π m x n) =
      (∏ x : {x // x ∈ deletedLeafSites π r}, A x) *
        ∏ x ∈ templateCorners ∪ templateTips, leafRemainder π r v n x

theorem retained_leaf_product (π : PatternData) (r : Representation)
    (hGeometry : PeripheralGeometry π r) (m : Fin 20 → UnitVector)
    (A : {x // x ∈ deletedLeafSites π r} → ℝ)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (hfactor : ∀ x n, normSq (n (leafNeighbour π x.1)) ≤ 1 →
      integratedLeafFactor π m x.1 n = A x *
        (if patternDegree π x.1 = 0 then 1 else
          1 + (replacementRadius π x.1 : ℝ) * dot (v x) (n (leafNeighbour π x.1))))
    (next : Bool) (n : Plane → Vec3) (hn : ∀ x, normSq (n x) ≤ 1) :
    retainedOriginalFactors π r next m n *
        (∏ x ∈ deletedLeafSites π r, integratedLeafFactor π m x n) =
      (∏ x : {x // x ∈ deletedLeafSites π r}, A x) *
        localEvaluation (reducedIntegrand π r next) n (assignedVectors π r m v)

theorem separated_factorization
    (hIco : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (π : PatternData) (r : Representation) (hGeometry : PeripheralGeometry π r)
    (m : Fin 20 → UnitVector)
    (A : {x // x ∈ deletedLeafSites π r} → ℝ)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (hfactor : ∀ x n, normSq (n (leafNeighbour π x.1)) ≤ 1 →
      integratedLeafFactor π m x.1 n = A x *
        (if patternDegree π x.1 = 0 then 1 else
          1 + (replacementRadius π x.1 : ℝ) * dot (v x) (n (leafNeighbour π x.1))))
    (next : Bool) :
    separatedLeafFunctional π r next m =
      (∏ x : {x // x ∈ deletedLeafSites π r}, A x) *
        rawFunctional (reducedSpinSites π r) (nextStatus π next)
          (reducedIntegrand π r next) (assignedVectors π r m v)

```

### Main.lean

```lean
theorem deletedLeafChoices
    (π : PatternData) (r : Representation) (m : Fin 20 → UnitVector)
    (hGeometry : PeripheralGeometry π r) (hRule : LeafRule π m) :
    ∃ A : {x // x ∈ deletedLeafSites π r} → ℝ,
    ∃ v : {x // x ∈ deletedLeafSites π r} → Vec3,
      (∀ x, 0 < A x) ∧
      (∀ x, normSq (v x) ≤ 1) ∧
      (∀ x n, normSq (n (leafNeighbour π x.1)) ≤ 1 →
        integratedLeafFactor π m x.1 n = A x *
        (if patternDegree π x.1 = 0 then 1 else
          1 + (replacementRadius π x.1 : ℝ) * dot (v x) (n (leafNeighbour π x.1))))

theorem main : AKLT.Blueprint.H1.PeripheralAssignmentStatement

```

## Axiom audit

`lake env lean AKLT/W/H1M027/Audit.lean` produced:

```text
AKLT.W.H1M027.main : AKLT.Blueprint.H1.PeripheralAssignmentStatement
'AKLT.W.H1M027.dot_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.normSq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.supportSpins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.corner_not_tip' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.slot_peripheral' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.leader_site' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.second_site' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.corner_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.degree_pos_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.retained_peripheral_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.assignedVectors_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.retained_field_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.assigned_leader' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.assigned_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.peripheral_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.evaluate_reducedIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.leaf_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.retained_leaf_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.separated_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.deletedLeafChoices' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M027.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound` occur. Every exported theorem was audited. The exact-type `example` and explicit `#check` both pass. The source scan found no forbidden proof constructs.

## Build commands and timings

All commands use `PATH="$HOME/.elan/bin:$PATH"` and exited successfully.

| Command | Wall time | Notes |
| --- | ---: | --- |
| `lake build AKLT.W.H1M027.Main` | 28.20 s | Full build of the three proof modules. |
| `lake build AKLT.W.H1M027.Audit` | 22.48 s | Rebuilt final proof modules after warning cleanup and checked all theorem axioms. |
| `lake build AKLT.W.H1M027.Main` | 5.10 s | Final required command, up to date; output in `main-build.log`. |
| `lake env lean AKLT/W/H1M027/Audit.lean` | 5.49 s | Final exact-type and axiom verification; output in `audit.log`. |

The final two commands ran concurrently, with two Lean/Lake processes at most. No Mathlib build or dependency update was performed.

## Open issues

None. There are no residual statements, extra assumptions on `main`, or dependencies on proofs of other blueprint leaves. All source changes are within `AKLT/W/H1M027/`.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT.W.H1M027.main : AKLT.Blueprint.H1.PeripheralAssignmentStatement`.
- Required entry point: `AKLT/W/H1M027/Main.lean`.
- Helpers: `Factors.lean`, `Factorization.lean`; verification: `Audit.lean`.
- The earlier local leaf-choice proof was reused and its factorization gap is closed.
- Common `K` is the product of positive deleted-site normalizers; empty products give 1.
- Common vector assignment is ball-valued at all twenty tokens; unused tokens are zero.
- Both next values follow from the same pointwise product identity.
- Required build and exact-type check pass.
- All 21 exported theorems use only `[propext, Classical.choice, Quot.sound]`.
- Open declarations: none. Residuals: none. Limitations or deviations: none.
- No files outside the assigned source directory were changed.
- Orchestrator can import `AKLT.W.H1M027.Main` and use the theorem directly.
