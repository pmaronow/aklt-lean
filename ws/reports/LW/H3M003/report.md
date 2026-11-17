STATUS: PROVED

## Files

- `AKLT/W/H3M003/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M003/report.md`

## Exported declaration

- `AKLT.W.H3M003.main : AKLT.Blueprint.H3.PhaseFoldExpansionStatement`

The proof establishes four coordinate invariants for `phaseRun` on `List.finRange n`: A and B are their diagonal products, and C and D are the sums of their respective single-change terms. Induction on `n` uses the cast-successor/last decomposition of `finRange`, with explicit recurrences for the single-change products. The terminal phase sum then selects the C and D coordinates.

## Axioms

`#print axioms AKLT.W.H3M003.main` output:

```text
'AKLT.W.H3M003.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M003.Main`
- Result: successful (`Built AKLT.W.H3M003.Main`)
- Module build time reported by Lake: 7.2 seconds; command wall time: 16.5 seconds.

## Open issues

None.

## ORCH-SUMMARY

Delivered `AKLT/W/H3M003/Main.lean` with `AKLT.W.H3M003.main` at the requested type.
The closed statement is proved from its own definitions using four coordinate invariants.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.
`lake build AKLT.W.H3M003.Main` succeeds.
No deviations or open issues.
