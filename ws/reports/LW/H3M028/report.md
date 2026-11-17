STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3M028/AKLT/W/H3M028/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3M028/report.md`

## Exported declaration

`AKLT.W.H3M028.main : AKLT.Blueprint.H3.LengthRewardPartitionStatement`

The exact target is the closed proposition

```lean
∀ X : PairType, ∀ n : ℕ,
  kernelLengthRow X n = ∑ Y : PairType, ∑ s ∈ lengthShifts X n,
    kernelLengthCoefficient X Y s n * kernelWitness Y
```

## Proof

For each departure, the proof expands `responseKappa` and reorders its finite response-pair, type, and shift sums. Every response pair contributes at its unique `responsePairType` and `pairShift`. Membership of that shift in `lengthShifts` follows directly from the definition of that finite set, so the regrouping recovers `witnessKappa`.

A list induction proves `exposureSum` linear in its reward for any fixed list. Applying it to `kernelOrdering w` gives the weighted exposure identity while keeping the ordering for each word fixed. Finally, finite-sum commutation moves the word sum outside the type and shift sums; the exposure identity turns each word's summand into `closedContribution` when it is a closed trail and zero otherwise.

## Axioms

Output of `#print axioms AKLT.W.H3M028.main`:

```text
'AKLT.W.H3M028.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.H3M028.Main`

Result: success. Wall time was 10.4 seconds; Lake reported 4.9 seconds for the target build. The build emitted two Lean deprecation warnings for `if_pos`; there were no proof errors.

## Open issues

None. The theorem is fully proved and compiled. The only build output beyond success is the pair of `if_pos` deprecation warnings.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3M028/Main.lean` with the requested theorem and exact type.
- `AKLT.W.H3M028.main` compiles and depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Build: `lake build AKLT.W.H3M028.Main` succeeded (10.4 seconds total; 4.9 seconds target).
- The proof partitions finite response-pair sums by actual pair type and shift, then uses linearity of `exposureSum` at fixed `kernelOrdering w`.
- No residual statements, deviations, or mathematical issues remain.
- Build emitted two deprecation warnings for `if_pos`.
- Orchestrator action: none required.
