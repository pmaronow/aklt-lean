STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/Main.lean)
- [LocalBounds.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/LocalBounds.lean)
- [Dynamics.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/Dynamics.lean)
- [TraceAlgebra.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/TraceAlgebra.lean)
- [Positivity.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/Positivity.lean)
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/Audit.lean)

Verification artifacts: [audit.log](/home/ubuntu/aklt/reports/LW/REC094/audit.log), [audit-time.txt](/home/ubuntu/aklt/reports/LW/REC094/audit-time.txt).
The previous report is preserved as `report.luna.md`.

## Delivered theorem

```lean
theorem AKLT.W.REC094.main :
    AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
```

This is the exact requested closed theorem type. There are no residual obligations or additional theorem parameters. The H1 implication and all network/trail hypotheses are those of the frozen statement.

The earlier files already proved the trace identities and reduced the result to the covered-ratio leaf. This delivery replaces that residual with the indexed, proved `AKLT.W.REC090.main`, removes `Residual_CoveredRatioV2`, and retains the reduction as `main_of_coveredRatio`.

## Proof and dependencies

For each evolving departure, the proof bounds the departure coefficient times the step ratio for both pin choices. A covered U departure uses REC090 for the pinned choice and REC011 for the free choice. An uncovered U departure uses REC012 and pays one factor of 12/5. Every U departure is a first departure. A D departure uses REC013: its ratio is exactly one, so its coefficient 1/5 equals the revisit weight or is bounded by the first-departure weight.

The helper files prove closure and admissibility of every prefix, positivity of partition sums, and exact products for trace coefficients and ratios. Multiplication and telescoping give the same bound for both pin choices. Taking their maximum and using `uncoveredCountV2 ≤ 12` yields `(12/5)^12 * trailWeight`.

Direct indexed leaf dependencies:

| Module | Theorem | Statement |
| --- | --- | --- |
| `AKLT.W.REC011.Main` | `AKLT.W.REC011.main` | `AKLT.Blueprint.Rec.FreeRatioUpperStatement` |
| `AKLT.W.REC012.Main` | `AKLT.W.REC012.main` | `AKLT.Blueprint.Rec.PinnedRatioUpperStatement` |
| `AKLT.W.REC013.Main` | `AKLT.W.REC013.main` | `AKLT.Blueprint.Rec.DStepTrivialStatement` |
| `AKLT.W.REC090.Main` | `AKLT.W.REC090.main` | `AKLT.Blueprint.Rec.CoveredRatioStatementV2` |

REC090 supplies the shared-mixture comparison through its proved REC089 dependency. No unindexed blueprint leaf is assumed.

## Exported declarations and axioms

All names below use namespace `AKLT.W.REC094`. The appendix reproduces the exact Lean type checks and `#print axioms` output for all 61 exported theorems, plus the four direct dependency theorems. Every audited axiom set is a subset of `{propext, Classical.choice, Quot.sound}`.

The seven exported helper definitions are:

```lean
positiveLetters : Finset IcoLetter
departureCoefficient {G : Finset Plane} : Network G → Plane → ℚ
vertexList : (ℕ → Plane) → ℕ → List Plane
stepCoeff {G : Finset Plane} {n : ℕ} :
  Network G → Plane → DirectionWord n → Fin n → ℝ
stepWeight {n : ℕ} :
  Plane → Compass → DirectionWord n → Fin n → ℝ
stepException {G : Finset Plane} {n : ℕ} :
  Network G → Plane → Compass → DirectionWord n → Fin n → Prop
stepCost {G : Finset Plane} {n : ℕ} :
  Network G → Plane → Compass → DirectionWord n → Fin n → ℝ
```

The required theorem's axiom output is:

```text
'AKLT.W.REC094.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Verification

Commands were run from `/home/ubuntu/aklt/wt/LW_REC094` with `$HOME/.elan/bin` on PATH.

```text
/usr/bin/time -p lake build AKLT.W.REC094.Main
Build completed successfully (9022 jobs).
real 119.41
user 274.45
sys 55.46
```

The Main module took 5.1 seconds; the total invocation also built the imported REC090/REC089 dependency chain.

```text
/usr/bin/time -p lake env lean AKLT/W/REC094/Audit.lean
exit code 0
real 4.34
user 3.35
sys 5.45
```

`Audit.lean` also checks the exact target by `example : AKLT.Blueprint.Rec.OnePointPointwiseStatementV2 := AKLT.W.REC094.main`. A source scan found no forbidden proof escape or placeholder. Only files within the assigned REC094 source and report directories were edited.

## Open issues

None. The target definition and existing files outside REC094 were unchanged.

## Complete theorem type and axiom audit

```text
'AKLT.W.REC011.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC090.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.goldenRatio_pos : 0 < AKLT.Defs.goldenRatio
'AKLT.W.REC094.goldenRatio_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.goldenRatio_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC094.goldenRatio_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.icoRadius_pos : 0 < AKLT.Defs.icoRadius
'AKLT.W.REC094.icoRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.icoVector_unit : ∀ (j : AKLT.Defs.IcoLetter), AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC094.icoVector_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.normSq_nonneg : ∀ (v : AKLT.Defs.Vec3), 0 ≤ AKLT.Defs.normSq v
'AKLT.W.REC094.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.normSq_eq_zero_iff : ∀ (v : AKLT.Defs.Vec3), AKLT.Defs.normSq v = 0 ↔ v = 0
'AKLT.W.REC094.normSq_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.dot_comm : ∀ (a b : AKLT.Defs.Vec3), AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC094.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.normSq_add : ∀ (a b : AKLT.Defs.Vec3),
  AKLT.Defs.normSq (a + b) = AKLT.Defs.normSq a + AKLT.Defs.normSq b + 2 * AKLT.Defs.dot a b
'AKLT.W.REC094.normSq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.one_add_dot_nonneg : ∀ (a b : AKLT.Defs.Vec3),
  AKLT.Defs.normSq a ≤ 1 → AKLT.Defs.normSq b ≤ 1 → 0 ≤ 1 + AKLT.Defs.dot a b
'AKLT.W.REC094.one_add_dot_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.one_add_dot_pos : ∀ (a b : AKLT.Defs.Vec3),
  AKLT.Defs.normSq a = 1 → AKLT.Defs.normSq b = 1 → a ≠ -b → 0 < 1 + AKLT.Defs.dot a b
'AKLT.W.REC094.one_add_dot_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.positiveLetters_card : AKLT.W.REC094.positiveLetters.card = 6
'AKLT.W.REC094.positiveLetters_card' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.positiveLetters_injective : Set.InjOn AKLT.Defs.icoVector ↑AKLT.W.REC094.positiveLetters
'AKLT.W.REC094.positiveLetters_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.positiveLetters_not_antipodal : ∀ j ∈ AKLT.W.REC094.positiveLetters,
  ∀ k ∈ AKLT.W.REC094.positiveLetters, AKLT.Defs.icoVector j ≠ -AKLT.Defs.icoVector k
'AKLT.W.REC094.positiveLetters_not_antipodal' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.originalLeg_mem : ∀ {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane},
  e ∈ AKLT.Defs.originalLegs G → e.1 ∈ G ∧ e.2 ∈ AKLT.Defs.neighbours e.1 ∧ e.2 ∉ G
'AKLT.W.REC094.originalLeg_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.originalLegs_at_card_le : ∀ (G : Finset AKLT.Defs.Plane) (x : AKLT.Defs.Plane), {e | (↑e).1 = x}.card ≤ 4
'AKLT.W.REC094.originalLegs_at_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.exists_positive_letter : ∀ (G : Finset AKLT.Defs.Plane) (τ : AKLT.Defs.PinAssignment G)
  (x : AKLT.Defs.Plane),
  ∃ j ∈ AKLT.W.REC094.positiveLetters, ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 = x → AKLT.Defs.icoVector j ≠ -↑(τ e)
'AKLT.W.REC094.exists_positive_letter' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.spinVector_normSq_le : ∀ (j : AKLT.Defs.SpinLetter), AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC094.spinVector_normSq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.spinWeight_nonneg : ∀ (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter), 0 ≤ AKLT.Defs.spinWeight s j
'AKLT.W.REC094.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.Network.spins_normSq_le : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane), AKLT.Defs.normSq (D.spins n x) ≤ 1
'AKLT.W.REC094.Network.spins_normSq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.partition_nonneg : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool), 0 ≤ D.partition τ b fun x => 1
'AKLT.W.REC094.partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.partition_pos : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool), 0 < D.partition τ b fun x => 1
'AKLT.W.REC094.partition_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceNetwork_append : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (l : List AKLT.Defs.Plane)
  (y : AKLT.Defs.Plane) (r : List AKLT.Defs.Plane),
  AKLT.Defs.traceNetwork D (l ++ y :: r) = AKLT.Defs.traceNetwork (AKLT.Defs.traceNetwork D (l ++ [y])) (y :: r)
'AKLT.W.REC094.traceNetwork_append' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceCoefficient_append : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (l : List AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (r : List AKLT.Defs.Plane),
  AKLT.Defs.traceCoefficient D (l ++ y :: r) =
    AKLT.Defs.traceCoefficient D (l ++ [y]) * AKLT.Defs.traceCoefficient (AKLT.Defs.traceNetwork D (l ++ [y])) (y :: r)
'AKLT.W.REC094.traceCoefficient_append' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.vertexList_succ : ∀ (v : ℕ → AKLT.Defs.Plane) (n : ℕ),
  AKLT.W.REC094.vertexList v (n + 1) = List.map v (List.range n) ++ [v n, v (n + 1)]
'AKLT.W.REC094.vertexList_succ' depends on axioms: [propext]
@AKLT.W.REC094.traceNetwork_vertexList_succ : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (v : ℕ → AKLT.Defs.Plane) (n : ℕ),
  AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList v (n + 1)) =
    AKLT.Defs.traceStep (AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList v n)) (v n) (v (n + 1))
'AKLT.W.REC094.traceNetwork_vertexList_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceCoefficient_vertexList_succ : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (v : ℕ → AKLT.Defs.Plane) (n : ℕ),
  AKLT.Defs.traceCoefficient D (AKLT.W.REC094.vertexList v (n + 1)) =
    AKLT.Defs.traceCoefficient D (AKLT.W.REC094.vertexList v n) *
      AKLT.W.REC094.departureCoefficient (AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList v n)) (v n)
'AKLT.W.REC094.traceCoefficient_vertexList_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceCoefficient_vertexList : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (v : ℕ → AKLT.Defs.Plane) (n : ℕ),
  AKLT.Defs.traceCoefficient D (AKLT.W.REC094.vertexList v n) =
    ∏ i ∈ Finset.range n,
      AKLT.W.REC094.departureCoefficient (AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList v i)) (v i)
'AKLT.W.REC094.traceCoefficient_vertexList' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceRatio_vertexList : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (v : ℕ → AKLT.Defs.Plane) (n : ℕ),
  AKLT.Defs.traceRatio D τ b (AKLT.W.REC094.vertexList v n) =
    ∏ i ∈ Finset.range n,
      AKLT.Defs.stepRatio (AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList v i)) τ b (v i) (v (i + 1))
'AKLT.W.REC094.traceRatio_vertexList' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.prefixNetwork_eq_vertexList : ∀ {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n),
  ∀ j ≤ n,
    AKLT.Blueprint.Rec.prefixNetwork D u w j =
      AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList (AKLT.Defs.wordVertex u w) j)
'AKLT.W.REC094.prefixNetwork_eq_vertexList' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceCoefficient_product : ∀ {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n),
  AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u w) =
    ∏ i, AKLT.W.REC094.departureCoefficient (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i) (AKLT.Defs.wordVertex u w ↑i)
'AKLT.W.REC094.traceCoefficient_product' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceRatio_product : ∀ {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n),
  AKLT.Defs.traceRatio D τ b (AKLT.Defs.wordVertices u w) =
    ∏ i,
      AKLT.Defs.stepRatio (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i) τ b (AKLT.Defs.wordVertex u w ↑i)
        (AKLT.Defs.wordVertex u w (↑i + 1))
'AKLT.W.REC094.traceRatio_product' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_status_U_iff : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (y o x : AKLT.Defs.Plane),
  (AKLT.Defs.traceStep D y o).status x = AKLT.Defs.Status.U ↔ D.status x = AKLT.Defs.Status.U ∧ x ≠ y
'AKLT.W.REC094.traceStep_status_U_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceNetwork_vertexList_status_U_iff : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (v : ℕ → AKLT.Defs.Plane) (n : ℕ) (x : AKLT.Defs.Plane),
  (AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList v n)).status x = AKLT.Defs.Status.U ↔
    D.status x = AKLT.Defs.Status.U ∧ ∀ j < n, v j ≠ x
'AKLT.W.REC094.traceNetwork_vertexList_status_U_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.U_departure_first : ∀ {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (i : Fin n),
  (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i).status (AKLT.Defs.wordVertex u w ↑i) = AKLT.Defs.Status.U →
    AKLT.Defs.wordRevisit u w i = false
'AKLT.W.REC094.U_departure_first' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.wordVertex_succ : ∀ {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (i : Fin n),
  AKLT.Defs.wordVertex u w (↑i + 1) = AKLT.Defs.wordVertex u w ↑i + (w i).step
'AKLT.W.REC094.wordVertex_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.adjacent_symm : ∀ {x y : AKLT.Defs.Plane}, AKLT.Defs.Adjacent x y → AKLT.Defs.Adjacent y x
'AKLT.W.REC094.adjacent_symm' depends on axioms: [propext]
@AKLT.W.REC094.adjacent_ne : ∀ {x y : AKLT.Defs.Plane}, AKLT.Defs.Adjacent x y → x ≠ y
'AKLT.W.REC094.adjacent_ne' depends on axioms: [propext]
@AKLT.W.REC094.adjacent_mem_neighbours : ∀ {x y : AKLT.Defs.Plane}, AKLT.Defs.Adjacent x y → y ∈ AKLT.Defs.neighbours x
'AKLT.W.REC094.adjacent_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.present_symm : ∀ {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x y : AKLT.Defs.Plane},
  D.Present x y → D.Present y x
'AKLT.W.REC094.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.present_mem_neighbours : ∀ {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G}
  {x y : AKLT.Defs.Plane}, D.Present x y → y ∈ D.presentNeighbours x
'AKLT.W.REC094.present_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_active_subset : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (y o : AKLT.Defs.Plane), (AKLT.Defs.traceStep D y o).active ⊆ D.active
'AKLT.W.REC094.traceStep_active_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_present_subset : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (y o : AKLT.Defs.Plane) {x z : AKLT.Defs.Plane}, (AKLT.Defs.traceStep D y o).Present x z → D.Present x z
'AKLT.W.REC094.traceStep_present_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_neighbours_subset : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (y o x : AKLT.Defs.Plane), (AKLT.Defs.traceStep D y o).presentNeighbours x ⊆ D.presentNeighbours x
'AKLT.W.REC094.traceStep_neighbours_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_not_present : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane),
  ¬(AKLT.Defs.traceStep D y o).Present y o
'AKLT.W.REC094.traceStep_not_present' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_neighbours_subset_erase : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (y o : AKLT.Defs.Plane), (AKLT.Defs.traceStep D y o).presentNeighbours y ⊆ (D.presentNeighbours y).erase o
'AKLT.W.REC094.traceStep_neighbours_subset_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_arrival_neighbours_subset_erase : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (y o : AKLT.Defs.Plane), (AKLT.Defs.traceStep D y o).presentNeighbours o ⊆ (D.presentNeighbours o).erase y
'AKLT.W.REC094.traceStep_arrival_neighbours_subset_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_auxiliary : ∀ {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y o : AKLT.Defs.Plane},
  D.Auxiliary → D.AdmissibleStart y → D.Present y o → (AKLT.Defs.traceStep D y o).Auxiliary
'AKLT.W.REC094.traceStep_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_arrival_admissible : ∀ {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G}
  {y o : AKLT.Defs.Plane},
  D.Auxiliary → D.Present y o → o ∉ AKLT.Defs.protectedSites G → (AKLT.Defs.traceStep D y o).AdmissibleStart o
'AKLT.W.REC094.traceStep_arrival_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.traceStep_present_of_distinct : ∀ {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G}
  {y o x z : AKLT.Defs.Plane},
  D.AdmissibleStart y → D.Present y o → D.Present x z → {x, z} ≠ {y, o} → (AKLT.Defs.traceStep D y o).Present x z
'AKLT.W.REC094.traceStep_present_of_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.vertexList_dynamics : ∀ {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G},
  D.Auxiliary →
    ∀ (v : ℕ → AKLT.Defs.Plane) (n : ℕ),
      D.AdmissibleStart (v 0) →
        (∀ i < n, D.Present (v i) (v (i + 1))) →
          (∀ i < n, v i ∉ AKLT.Defs.protectedSites G) →
            (∀ i < n, ∀ j < n, {v i, v (i + 1)} = {v j, v (j + 1)} → i = j) →
              ∀ j ≤ n,
                (AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList v j)).Auxiliary ∧
                  (j < n → (AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList v j)).AdmissibleStart (v j)) ∧
                    ∀ (i : ℕ),
                      j ≤ i →
                        i < n → (AKLT.Defs.traceNetwork D (AKLT.W.REC094.vertexList v j)).Present (v i) (v (i + 1))
'AKLT.W.REC094.vertexList_dynamics' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.trail_dynamics : ∀ {G : Finset AKLT.Defs.Plane} {n : ℕ} {D : AKLT.Defs.Network G},
  D.Auxiliary →
    ∀ {u : AKLT.Defs.Plane},
      D.AdmissibleStart u →
        ∀ {T : Finset AKLT.Defs.Plane} {w : AKLT.Defs.DirectionWord n},
          AKLT.Defs.StoppedNetworkTrail D u T w →
            (∀ j ≤ n, (AKLT.Blueprint.Rec.prefixNetwork D u w j).Auxiliary) ∧
              ∀ (i : Fin n),
                (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i).AdmissibleStart (AKLT.Defs.wordVertex u w ↑i) ∧
                  (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i).Present (AKLT.Defs.wordVertex u w ↑i)
                    (AKLT.Defs.wordVertex u w (↑i + 1))
'AKLT.W.REC094.trail_dynamics' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.passageFactor_one_le : ∀ (s : Bool), 1 ≤ ↑(AKLT.Defs.passageFactor s)
'AKLT.W.REC094.passageFactor_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.stepRatio_pos : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y o : AKLT.Defs.Plane), 0 < AKLT.Defs.stepRatio D τ b y o
'AKLT.W.REC094.stepRatio_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.stepRatio_le_twelve_fifths : ∀ (a : AKLT.Blueprint.Rec.Departure) (b : Bool),
  AKLT.Defs.stepRatio a.D a.τ b a.y a.o ≤ 12 / 5
'AKLT.W.REC094.stepRatio_le_twelve_fifths' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.dRatio_eq_one : ∀ (a : AKLT.Blueprint.Rec.Departure),
  a.D.status a.y = AKLT.Defs.Status.D → ∀ (b : Bool), AKLT.Defs.stepRatio a.D a.τ b a.y a.o = 1
'AKLT.W.REC094.dRatio_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.coveredRatio_of_mixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
  AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC094.coveredRatio_of_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.local_step_comparison : AKLT.Blueprint.Rec.CoveredRatioStatementV2 →
  AKLT.Blueprint.Top.H1Statement →
    ∀ {G : Finset AKLT.Defs.Plane} {n : ℕ} {D : AKLT.Defs.Network G} (τ : AKLT.Defs.PinAssignment G),
      D.Auxiliary →
        ∀ {u : AKLT.Defs.Plane},
          D.AdmissibleStart u →
            ∀ (incoming : AKLT.Defs.Compass) {w : AKLT.Defs.DirectionWord n},
              AKLT.Defs.StoppedNetworkTrail D u (AKLT.Defs.protectedSites G) w →
                ∀ (i : Fin n) (b : Bool),
                  have P := AKLT.Blueprint.Rec.prefixNetwork D u w ↑i;
                  0 ≤ AKLT.Defs.stepRatio P τ b (AKLT.Defs.wordVertex u w ↑i) (AKLT.Defs.wordVertex u w (↑i + 1)) ∧
                    AKLT.W.REC094.stepCoeff D u w i *
                        AKLT.Defs.stepRatio P τ b (AKLT.Defs.wordVertex u w ↑i) (AKLT.Defs.wordVertex u w (↑i + 1)) ≤
                      AKLT.W.REC094.stepCost D u incoming w i * AKLT.W.REC094.stepWeight u incoming w i
'AKLT.W.REC094.local_step_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC094.trace_product_identities : ∀ {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n),
  ↑(AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u w)) = ∏ i, AKLT.W.REC094.stepCoeff D u w i ∧
    AKLT.Defs.traceRatio D τ true (AKLT.Defs.wordVertices u w) =
        ∏ i,
          AKLT.Defs.stepRatio (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i) τ true (AKLT.Defs.wordVertex u w ↑i)
            (AKLT.Defs.wordVertex u w (↑i + 1)) ∧
      AKLT.Defs.traceRatio D τ false (AKLT.Defs.wordVertices u w) =
        ∏ i,
          AKLT.Defs.stepRatio (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i) τ false (AKLT.Defs.wordVertex u w ↑i)
            (AKLT.Defs.wordVertex u w (↑i + 1))
'AKLT.W.REC094.trace_product_identities' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.main : AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
'AKLT.W.REC094.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.main_of_coveredRatio : AKLT.Blueprint.Rec.CoveredRatioStatementV2 →
  AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
'AKLT.W.REC094.main_of_coveredRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.main_of_mixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
  AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
'AKLT.W.REC094.main_of_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- Delivered `AKLT/W/REC094/Main.lean` and five helper/audit modules.
- Exact theorem: `AKLT.W.REC094.main : AKLT.Blueprint.Rec.OnePointPointwiseStatementV2`.
- Status: PROVED FROM DEPS; no residual or extra premise remains.
- Direct proved leaves used: REC011, REC012, REC013, REC090.
- REC090 transitively uses the proved shared-mixture leaf REC089.
- The trace identities, prefix dynamics, and remaining local/product estimates are proved here.
- All 61 exported theorem axiom audits passed; only the three permitted axioms occur.
- Requested build passed in 119.41 seconds; Main module took 5.1 seconds.
- Full audit passed in 4.34 seconds.
- Open names: none. Limitations or deviations: none.
- Orchestrator action: accept/register the exact theorem above; no mathematical decision remains.
