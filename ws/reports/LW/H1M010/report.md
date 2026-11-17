STATUS: PROVED

## Files

- `AKLT/W/H1M010/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M010/report.md`

## Exported declaration

`AKLT.W.H1M010.main : AKLT.Blueprint.H1.OriginalFactorStructureStatement`

The proof establishes the slot degree bound by tracking supports of formal-dot monomials through sums and products. Each external factor contributes degree only to its own slot. It establishes invariance by evaluating each internal and external dot factor and applying preservation of the dot product under `R.transpose * R = 1`.

## Axioms

Output of `#print axioms AKLT.W.H1M010.main`:

```text
'AKLT.W.H1M010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M010.Main`
- Result: successful (`Build completed successfully (8954 jobs).`)
- Timing: 15.4 s wall time for the final command; Lean reported 7.5 s for the module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M010.main` with the exact requested type.
- The target module builds successfully.
- Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
- No deviations or open issues.
