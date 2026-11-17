STATUS: PARTIAL

The requested unconditional theorem is not proved. The earlier two broad residuals have been replaced by one exact, smaller blueprint dependency: REC090, `AKLT.Blueprint.Rec.CoveredRatioStatementV2`. This leaf is absent from `/home/ubuntu/aklt/state/lw/proved-index.tsv`. No unindexed leaf proof is imported.

## Files

All Lean files are under `/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/`.

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/Main.lean): local coefficient comparison, unconditional trace product identities, the conditional pointwise theorem, and an alternative reduction from the local-mixture leaf.
- [LocalBounds.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/LocalBounds.lean): the single transparent residual, proved uniform and D-step estimates, and the mixture-to-covered-ratio implication.
- [TraceAlgebra.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/TraceAlgebra.lean): reused list/prefix algebra, coefficient and ratio products, and the fact that a U departure cannot be a revisit.
- [Dynamics.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/Dynamics.lean): reused auxiliary closure, admissibility, and survival of untraversed bonds along stopped trails.
- [Positivity.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/Positivity.lean): reused positivity of both finite network partitions, with no network-validity assumptions.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/Audit.lean): checks the types and prints axioms of all 60 public REC094 theorems, plus the three imported leaf theorems. It also verifies both exact conditional reduction types.

The earlier `report.luna.md` is preserved. Only files in REC094's assigned source and report directories were written.

## Exported declarations and statements

The principal declarations, all in namespace `AKLT.W.REC094`, are:

```lean
def Residual_CoveredRatioV2 : Prop :=
  AKLT.Blueprint.Rec.CoveredRatioStatementV2

theorem main :
  Residual_CoveredRatioV2 →
    AKLT.Blueprint.Rec.OnePointPointwiseStatementV2

theorem main_of_mixture :
  AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
    AKLT.Blueprint.Rec.OnePointPointwiseStatementV2

theorem coveredRatio_of_mixture :
  AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
    AKLT.Blueprint.Rec.CoveredRatioStatementV2

theorem stepRatio_le_twelve_fifths (a : AKLT.Blueprint.Rec.Departure) (b : Bool) :
  AKLT.Defs.stepRatio a.D a.τ b a.y a.o ≤ 12 / 5

theorem dRatio_eq_one (a : AKLT.Blueprint.Rec.Departure)
    (hD : a.D.status a.y = .D) (b : Bool) :
  AKLT.Defs.stepRatio a.D a.τ b a.y a.o = 1
```

`local_step_comparison` derives the old local residual from REC090 and H1: at every departure of a stopped trail, the step ratio is nonnegative and the evolving departure coefficient times that ratio is at most `stepCost * stepWeight`, for each pin choice.

`trace_product_identities` proves all three old product obligations without trail, auxiliary, admissibility, or residual assumptions: the real trace coefficient is the product of `stepCoeff`, and each trace ratio is the product of its evolving step ratios. The full kernel-printed types of these and every other exported theorem appear in the complete listing below and in [declarations-and-axioms.txt](/home/ubuntu/aklt/reports/LW/REC094/declarations-and-axioms.txt).

## Proof and dependencies

The indexed leaves used are exactly:

| Statement | Proved theorem | Import |
| --- | --- | --- |
| `AKLT.Blueprint.Rec.FreeRatioUpperStatement` | `AKLT.W.REC011.main` | `AKLT.W.REC011.Main` |
| `AKLT.Blueprint.Rec.PinnedRatioUpperStatement` | `AKLT.W.REC012.main` | `AKLT.W.REC012.Main` |
| `AKLT.Blueprint.Rec.DStepTrivialStatement` | `AKLT.W.REC013.main` | `AKLT.W.REC013.Main` |

A U departure is a first departure. At a covered U departure, REC090 bounds the pinned ratio by the appropriate passage factor, while REC011 bounds the free ratio by one. At an uncovered U departure, REC011/REC012 bound either ratio by 12/5. At a D departure, REC013 makes either ratio exactly one; its coefficient is 1/5, which also fits the larger lattice weight when this is a first departure.

The proved trace dynamics provide an actual admissible `Departure` at each prefix, so all indexed leaf hypotheses are established. The trace ratios telescope using strictly positive partition sums. Multiplication produces one common bound for both pin choices, with exactly `(12/5)^uncoveredCountV2`; nonnegativity allows taking the maximum, and the count bound gives `exceptionFactor = (12/5)^12`.

The absent-incoming-bond hypothesis is retained in the target. This pointwise argument does not need it; its role in the paper is the later enlargement to plane trails.

## Remaining obligation

The only residual on `main` is:

```lean
AKLT.Blueprint.Rec.CoveredRatioStatementV2
-- REC090, module AKLT.Blueprint.Rec.NodesV2Local
```

It requires deriving the pinned one-step passage-factor bound from H1 for the shared internal-present-bond matcher. The pointwise product argument does not itself supply the network-to-template comparison.

As a separate sufficient route, the proved `main_of_mixture` reduces the result to REC089, `AKLT.Blueprint.Rec.LocalMixtureStatementV2`, in the same blueprint module. REC089 asks for common finite nonnegative mixtures representing the current and next network partitions by covered template partitions. It is also absent from the proved index. REC089 is an alternative sufficient dependency, not a second premise on `main`.

The old `Residual_LocalStepComparisonV2`, `Residual_TraceProductIdentitiesV2`, and `Residual_UniformRatiosV2` are no longer unproved assumptions in the delivered sources. No counterexample or missing mathematical premise was found; the remaining issue is an unproved local blueprint leaf.

## Axioms and validation

```text
'AKLT.W.REC094.local_step_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC094.trace_product_identities' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC094.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC094.main_of_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The audit checks all 60 exported REC094 theorems. Each axiom set is a subset of `{propext, Classical.choice, Quot.sound}`; `vertexList_succ`, `adjacent_symm`, and `adjacent_ne` use only `propext`. The three imported leaf theorems also use only the allowed axioms. No forbidden proof constructs occur in the delivered files.

Commands used `PATH="$HOME/.elan/bin:$PATH"`:

| Command | Result | Measured wall time |
| --- | --- | --- |
| `lake build AKLT.W.REC094.Main` (initial implementation) | passed; Main compiled in 6.1 s, including needed indexed-dependency builds | 58.20 s |
| `lake build AKLT.W.REC094.Audit` (final source) | passed; checks all public declarations and conditional types | 13.95 s |
| `lake build AKLT.W.REC094.Main` (final source) | passed | 5.53 s |
| `lake env lean /tmp/rec094_exact_check.lean` | exact unconditional type check failed, confirming the remaining explicit argument | 3.59 s |

Logs: [build-main.log](/home/ubuntu/aklt/reports/LW/REC094/build-main.log), [build-audit.log](/home/ubuntu/aklt/reports/LW/REC094/build-audit.log), and [exact-type-check.log](/home/ubuntu/aklt/reports/LW/REC094/exact-type-check.log).

The exact-type diagnostic reports:

```text
AKLT.W.REC094.main
has type
  AKLT.W.REC094.Residual_CoveredRatioV2 → AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
but is expected to have type
  AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
```

Thus this delivery must not be indexed as a proof of the requested closed statement.

## Complete exported theorem types and axiom output

The following is the Audit module's output, including the transparent residual's type and the three imported leaf axiom checks:

```text
AKLT.W.REC094.Residual_CoveredRatioV2 : Prop
'AKLT.W.REC011.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
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
AKLT.W.REC094.local_step_comparison : AKLT.W.REC094.Residual_CoveredRatioV2 →
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
AKLT.W.REC094.main : AKLT.W.REC094.Residual_CoveredRatioV2 → AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
'AKLT.W.REC094.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC094.main_of_mixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
  AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
'AKLT.W.REC094.main_of_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- STATUS: PARTIAL; the exact unconditional REC094 theorem is not delivered.
- `AKLT.W.REC094.main` proves `Residual_CoveredRatioV2 → OnePointPointwiseStatementV2`.
- `Residual_CoveredRatioV2` is definitionally `AKLT.Blueprint.Rec.CoveredRatioStatementV2` (REC090).
- REC090 is the sole open dependency on `main`; it is absent from the proved index.
- Alternative: `main_of_mixture` proves the target from `AKLT.Blueprint.Rec.LocalMixtureStatementV2` (REC089).
- `coveredRatio_of_mixture` proves REC089 → REC090; REC089 is not an additional required premise.
- Imported proved leaves: REC011, REC012, REC013 only.
- Former whole-trail local-comparison and trace-product residuals are discharged.
- Both pin choices, D first departures, D revisits, and arbitrary exception positions are handled.
- Main and Audit builds pass; all 60 exported theorem axiom checks pass the allowed-axiom restriction.
- The unconditional exact-type diagnostic still fails because REC090 is explicit.
- Orchestrator should supply/prove REC090, or REC089 via the included reduction, before indexing REC094.
