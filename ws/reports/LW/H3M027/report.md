STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3M027/AKLT/W/H3M027/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M027/report.md`

## Exported declaration

`AKLT.W.H3M027.main : AKLT.Blueprint.H3.LengthShiftSupportStatement`

## Proof outline

For each response pair `p` at word `w` and index `i`, the definition of `lengthShifts` includes `pairShift X p`. Therefore, if `s` is outside that set, the indicator for shift `s` in `responseKappa` is zero for every pair. Its finite sum is zero. Induction over `kernelOrdering w` then gives zero `exposureSum`, and summing over all words gives the required zero `kernelLengthCoefficient`.

## Axioms

`#print axioms AKLT.W.H3M027.main`:

```text
'AKLT.W.H3M027.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M027.Main`
- Result: successful.
- Timing: 11.8 seconds wall time for the successful command; Lean reported 5.3 seconds for the target module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M027.main` with the exact requested type.
- The new module builds successfully with the required Lake target.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, limitations, or deviations remain.
