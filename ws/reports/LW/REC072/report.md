STATUS: PROVED

The exact requested theorem is present and compiled:

```lean
theorem AKLT.W.REC072.main :
    AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement
```

## Files

- `AKLT/W/REC072/Main.lean`: proves summability, finite ENNReal rows, the former residual, and the requested closed theorem.
- `AKLT/W/REC072/Estimates.lean`: preserves the earlier attempt's proofs, relocated from its `Main.lean`. These include coefficient nonnegativity, first-visit ordering, shift support, the H2 coefficient bound, and the finite-cutoff comparison.
- `AKLT/W/REC072/Audit.lean`: checks the exact requested type and prints the axioms of every exported theorem.
- `/home/ubuntu/aklt/reports/LW/REC072/audit.log`: complete build, exact-type, and axiom-audit output.

## Proof

The first-visit exposure product is bounded by the full first-visit product, since all passage factors are at least one. The aggregate response coefficient at one departure is at most six. Thus H2 bounds each real length coefficient by `6 * n * CV * q^n`. The coefficient vanishes whenever `n + 1 < s`, so summing the possible shifts costs at most `n + 2`. The resulting bound `6 * CV * (n^2 + 2*n) * q^n` is summable because `0 < q < 1`.

The proof exchanges the length and shift sums in ENNReal, proves that every complete row is finite, and only then converts to real summable rows and real coefficient series. Multiplication by a nonnegative function bounded by two preserves summability. Regrouping the finite cutoff and comparing nonnegative partial sums with these convergent series proves the required inequality.

This uses H2 alone. It requires no additional blueprint leaf, H3 witness, shifted contraction bound, or epsilon budget. The coarse coefficient bound is sufficient for this particular unshifted finiteness statement.

## Exported declarations and statements

All signatures below are in namespace `AKLT.W.REC072`, with `AKLT.Defs` and `AKLT.Blueprint.Rec` open and the `BigOperators` and `ENNReal` scopes open.

### Main.lean

```lean
lemma lengthRowMajorant_summable {CV q : ℝ} (hbound : OpenTrailBound CV q) :
    Summable (fun n : ℕ => (n + 2 : ℝ) * (6 * n) * CV * q ^ n)

lemma coefficient_length_sum_le {CV q : ℝ} (hbound : OpenTrailBound CV q)
    (X Y : PairType) (n : ℕ) :
    (∑' s : ℕ, ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ)) ≤
      ENNReal.ofReal ((n + 2 : ℝ) * (6 * n) * CV * q ^ n)

lemma shiftKernel_row_ne_top {CV q : ℝ} (hbound : OpenTrailBound CV q)
    (X Y : PairType) : (∑' s : ℕ, shiftKernel X Y s) ≠ ⊤

theorem kernelSeriesBridge : ResidualKernelSeriesBridge

theorem main : AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement
```

### Estimates.lean

```lean
lemma vertexDist_le (n : ℕ) (w : DirectionWord n) (j : ℕ) :
    latticeDist (wordVertex kernelStart w j) kernelStart ≤ n

lemma latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z

lemma partition_perm {n : ℕ} (l : List (Fin n)) (p : Fin n → Bool) :
    (l.filter p ++ l.filter (fun i => !p i)).Perm l

lemma firstVisit_nodup {n : ℕ} (w : DirectionWord n) :
    (firstVisitList w).Nodup

lemma kernelOrdering_perm {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).Perm (firstVisitList w)

lemma kernelOrdering_nodup {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).Nodup

lemma kernelOrdering_length_le {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).length ≤ n

lemma passageFactor_ge_one (b : Bool) : 1 ≤ passageFactor b

lemma passageFactor_pos (b : Bool) : 0 < passageFactor b

lemma exposure_bound {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (l : List (Fin n)) (hl : l.Nodup)
    (hr : ∀ i, 0 ≤ r i) :
    exposureSum w r l ≤
      (∏ i ∈ l.toFinset, passageFactor (wordStraight kernelIncoming w i)) *
        (∑ i ∈ l.toFinset, r i)

lemma pairCoefficient_nonneg {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane) :
    0 ≤ pairCoefficient w i p

lemma pairCoefficient_le_one {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane) :
    pairCoefficient w i p ≤ 1

lemma responseKappa_nonneg {n : ℕ} (X Y : PairType) (s : ℕ)
    (w : DirectionWord n) (i : Fin n) : 0 ≤ responseKappa X Y s w i

lemma step_mem_neighbours (x : Plane) (d : Compass) : x + d.step ∈ neighbours x

lemma step_latticeDist (x : Plane) (d : Compass) : latticeDist (x + d.step) x = 1

lemma neighbours_card_le_four (x : Plane) : (neighbours x).card ≤ 4

lemma responseCarrier_subset_neighbours {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbours w i) ⊆
      neighbours (wordVertex kernelStart w i.val)

lemma responseKappa_le_six {n : ℕ} (X Y : PairType) (s : ℕ)
    (w : DirectionWord n) (i : Fin n) : responseKappa X Y s w i ≤ 6

lemma responsePairShift_le {n : ℕ} (X : PairType) (w : DirectionWord n)
    (i : Fin n) (p : Finset Plane) (hp : p ∈ responsePairs w i) :
    pairShift X p ≤ n + 1

lemma responseKappa_zero_of_shift_large {n : ℕ} (X Y : PairType) (s : ℕ)
    (w : DirectionWord n) (i : Fin n) (hs : n + 1 < s) :
    responseKappa X Y s w i = 0

lemma exposureSum_eq_zero_of_reward_zero {n : ℕ} (w : DirectionWord n)
    (r : Fin n → ℚ) (hr : ∀ i, r i = 0) (l : List (Fin n)) : exposureSum w r l = 0

lemma kernelLengthCoefficient_zero_of_shift_large (X Y : PairType) (n s : ℕ)
    (hs : n + 1 < s) : kernelLengthCoefficient X Y s n = 0

lemma firstVisit_toFinset {n : ℕ} (w : DirectionWord n) :
    (firstVisitList w).toFinset = Finset.univ.filter (fun i => !wordRevisit kernelStart w i)

lemma trailWeight_eq_base_mul_firstVisits {n : ℕ} (w : DirectionWord n) :
    (trailWeight kernelStart kernelIncoming w : ℚ) = trailBaseWeight kernelStart w *
      ∏ i ∈ (firstVisitList w).toFinset, passageFactor (wordStraight kernelIncoming w i)

lemma kernelOrdering_product_eq_firstVisits {n : ℕ} (w : DirectionWord n) :
    ∏ i ∈ (kernelOrdering w).toFinset, passageFactor (wordStraight kernelIncoming w i) =
      ∏ i ∈ (firstVisitList w).toFinset, passageFactor (wordStraight kernelIncoming w i)

lemma kernelOrdering_reward_sum_le {n : ℕ} (w : DirectionWord n) (X Y : PairType) (s : ℕ) :
    (∑ i ∈ (kernelOrdering w).toFinset, responseKappa X Y s w i) ≤ (6 * n : ℚ)

lemma exposedTrail_le {n : ℕ} (w : DirectionWord n) (X Y : PairType) (s : ℕ) :
    (trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w) : ℚ) ≤
      (6 * n : ℚ) * (trailWeight kernelStart kernelIncoming w : ℚ)

lemma exposureSum_nonneg {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (hr : ∀ i, 0 ≤ r i) : ∀ l : List (Fin n), 0 ≤ exposureSum w r l

lemma trailWeight_nonneg {n : ℕ} (w : DirectionWord n) :
    0 ≤ (trailWeight kernelStart kernelIncoming w : ℚ)

lemma kernelLengthCoefficient_nonneg (X Y : PairType) (s n : ℕ) :
    0 ≤ kernelLengthCoefficient X Y s n

lemma kernelLengthCoefficient_bound {CV q : ℝ} (hbound : OpenTrailBound CV q)
    (X Y : PairType) (s n : ℕ) :
    (kernelLengthCoefficient X Y s n : ℝ) ≤ (6 * n : ℝ) * CV * q ^ n

lemma finite_cutoff_reorder (N : ℕ) (f : ℕ → PairType → ℕ → ℝ) :
    (∑ n ∈ Finset.range N, ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), f n Y s) =
      ∑ Y : PairType, ∑ s ∈ Finset.range (N + 1), ∑ n ∈ Finset.range N,
        if s < n + 2 then f n Y s else 0

theorem main_of_residual (hres : ResidualKernelSeriesBridge) :
    AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement
```

The earlier residual proposition is retained for compatibility and is now proved by `kernelSeriesBridge`; it is not an outstanding assumption:

```lean
def ResidualKernelSeriesBridge : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → ∀ X : PairType,
    (∀ Y s, Summable (fun n : ℕ => (kernelLengthCoefficient X Y s n : ℝ))) ∧
    (∀ Y s, realKernel X Y s = ∑' n : ℕ, (kernelLengthCoefficient X Y s n : ℝ)) ∧
    (∀ Y s, 0 ≤ realKernel X Y s) ∧
    Summable (fun j : PairType × ℕ => realKernel X j.1 j.2 * 2)
```

## Axiom audit

`Audit.lean` runs `#print axioms` on all 38 exported theorems. Its exact-type check reports:

```text
AKLT.W.REC072.main : AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement
```

The complete `#print axioms` output, with Lake location prefixes removed, is:

```text
'AKLT.W.REC072.vertexDist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.latticeDist_triangle' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC072.partition_perm' depends on axioms: [propext]
'AKLT.W.REC072.firstVisit_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.kernelOrdering_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.kernelOrdering_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.kernelOrdering_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.passageFactor_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.passageFactor_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.exposure_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.pairCoefficient_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.pairCoefficient_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.responseKappa_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.step_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.step_latticeDist' depends on axioms: [propext, Classical.choice]
'AKLT.W.REC072.neighbours_card_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.responseCarrier_subset_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.responseKappa_le_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.responsePairShift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.responseKappa_zero_of_shift_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.exposureSum_eq_zero_of_reward_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.kernelLengthCoefficient_zero_of_shift_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.firstVisit_toFinset' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.trailWeight_eq_base_mul_firstVisits' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.kernelOrdering_product_eq_firstVisits' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.kernelOrdering_reward_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.exposedTrail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.exposureSum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.trailWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.kernelLengthCoefficient_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.kernelLengthCoefficient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.finite_cutoff_reorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.main_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.lengthRowMajorant_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.coefficient_length_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.shiftKernel_row_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.kernelSeriesBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC072.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every dependency is among `propext`, `Classical.choice`, and `Quot.sound`. A source scan found no forbidden proof placeholders or declarations.

## Build commands and timings

With `PATH="$HOME/.elan/bin:$PATH"`:

- `lake build AKLT.W.REC072.Main`: succeeded. Lake reported 19 seconds for `Estimates.lean` and 4.2 seconds for `Main.lean`.
- `/usr/bin/time -f 'Elapsed: %e s' lake build AKLT.W.REC072.Audit`: succeeded. Audit module compilation took 4.0 seconds; total wall time was 8.35 seconds.

The inherited estimate proof produces one harmless `linter.unnecessarySeqFocus` warning at `Estimates.lean:278`. No errors or unfinished proof obligations remain. No source files outside `AKLT/W/REC072/` were changed.

## Open issues

None. `ResidualKernelSeriesBridge` is discharged by a closed theorem, and `main` has exactly the requested name and type.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC072.main : AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement`.
- Status: PROVED; no residual assumptions and no additional blueprint dependencies.
- Earlier estimates are preserved in `AKLT/W/REC072/Estimates.lean`.
- `AKLT/W/REC072/Main.lean` closes the analytic bridge using H2 and a polynomial geometric majorant.
- `AKLT/W/REC072/Audit.lean` confirms the exact type and audits all 38 exported theorem declarations.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Both requested-module and audit builds succeed.
- Open exact names: none.
- Limitation: one inherited cosmetic tactic-linter warning.
- Route deviation: coarse unshifted finiteness bound suffices; no H3 or transport budget is used.
- Orchestrator can accept the leaf; no further mathematical decision is needed.
