STATUS: PARTIAL

# REC072 report

## Files

- `AKLT/W/REC072/Main.lean` — proved finite-path estimates and a theorem deriving the requested leaf from `ResidualKernelSeriesBridge`.

The requested closed declaration `AKLT.W.REC072.main : AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement` is not present. No hypotheses or unfinished facts are hidden in a theorem claimed as that leaf.

## Residual and proved declarations

The explicit remaining proposition is:

```lean
def ResidualKernelSeriesBridge : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → ∀ X : PairType,
    (∀ Y s, Summable (fun n : ℕ => (kernelLengthCoefficient X Y s n : ℝ))) ∧
    (∀ Y s, realKernel X Y s = ∑' n : ℕ, (kernelLengthCoefficient X Y s n : ℝ)) ∧
    (∀ Y s, 0 ≤ realKernel X Y s) ∧
    Summable (fun j : PairType × ℕ => realKernel X j.1 j.2 * 2)
```

`main_of_residual (hres : ResidualKernelSeriesBridge) : FiniteKernelTailDominationStatement` is proved. It rearranges the finite cutoff sums, bounds each fixed `(Y,s)` partial length sum by `realKernel X Y s * F Y (d-s)`, and uses the residual row summability to compare the finite row to `renewalOp`.

Other exported lemmas in `Main.lean` and their statements are:

- `vertexDist_le`: every length-`n` word vertex is at lattice distance at most `n` from `kernelStart`; `latticeDist_triangle`: lattice distance satisfies the triangle inequality.
- `partition_perm`: the two complementary filters of a list, concatenated, permute the list. `firstVisit_nodup`, `kernelOrdering_perm`, `kernelOrdering_nodup`, and `kernelOrdering_length_le` prove the first-visit ordering is a permutation without repeats and has length at most `n`.
- `passageFactor_ge_one`, `passageFactor_pos`, `exposure_bound`: passage factors are at least one and the exposure sum is bounded by the product of factors in the ordering times the sum of rewards.
- `pairCoefficient_nonneg`, `pairCoefficient_le_one`, `responseKappa_nonneg`, `responseKappa_le_six`: local coefficients are nonnegative and bounded; the per-departure aggregate response reward is at most six.
- `step_mem_neighbours`, `step_latticeDist`, `neighbours_card_le_four`, `responseCarrier_subset_neighbours`: elementary lattice-neighbour facts used in the response-pair count.
- `responsePairShift_le`: each live response pair has shift at most `n+1`; `responseKappa_zero_of_shift_large` and `kernelLengthCoefficient_zero_of_shift_large` prove coefficients vanish for `n+1 < s`.
- `exposureSum_eq_zero_of_reward_zero`: zero rewards give zero exposure. `firstVisit_toFinset`, `trailWeight_eq_base_mul_firstVisits`, and `kernelOrdering_product_eq_firstVisits` identify the first-visit product with the trail-weight factor.
- `kernelOrdering_reward_sum_le` and `exposedTrail_le`: aggregate rewards are bounded by `6n`, and the path contribution is bounded by `6n` times its H2 trail weight.
- `exposureSum_nonneg`, `trailWeight_nonneg`, `kernelLengthCoefficient_nonneg`, `kernelLengthCoefficient_bound`: positivity and the H2 consequence `(kernelLengthCoefficient X Y s n : ℝ) ≤ (6*n) * CV * q^n`.
- `finite_cutoff_reorder`: the finite cutoff over length-dependent shift ranges equals a fixed finite row cutoff with a length guard.

## Axiom audit

`#print axioms` was run on every theorem declaration in the file. The complete output is:

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
```

All dependencies are among the allowed axioms. No `sorry`, `admit`, or additional axiom is used.

## Build

- `lake build AKLT.W.REC072.Main` — successful; module build reported 27 seconds.
- Axiom audit: `lake env lean /tmp/REC072_Audit.lean` — successful; about 6 seconds.

## Open issue

Prove `ResidualKernelSeriesBridge` from `OpenTrailBound` and the frozen kernel definitions. This is the H2-to-real-series finiteness and `toReal` regrouping step; the finite coefficient estimate, shift support, and reduction of the requested inequality to that bridge are already proved.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC072/Main.lean`, which compiles and proves direct coefficient, support, ordering, and cutoff rearrangement lemmas.
- Proved `main_of_residual`, reducing the requested statement to `ResidualKernelSeriesBridge`.
- The exact closed declaration `AKLT.W.REC072.main` remains open.
- Remaining exact declaration: `AKLT.W.REC072.ResidualKernelSeriesBridge`.
- All audited theorem axioms are restricted to `propext`, `Classical.choice`, and `Quot.sound`.
- No forbidden proof placeholders or unsound declarations are used.
- Orchestrator should continue by proving the residual from H2 at `theta = 1`, then invoke `main_of_residual`.
