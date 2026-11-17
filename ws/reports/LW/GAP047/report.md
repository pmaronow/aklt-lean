STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP047/AKLT/W/GAP047/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP047/report.md`

## Exported declaration

`AKLT.W.GAP047.main : AKLT.Blueprint.Gap.TrialCountStatement`

The proof counts the `h - 1` candidate times corresponding to indices 2 through `h`. For each of the two possible deleted positions (the index itself and its successor), an injective map sends deleted candidates into `exceptionalIndices`; thus at most two candidates are removed when that set has cardinality at most one. The hypothesis `4 ≤ h` handles the natural subtraction in the conclusion.

## Axioms

`#print axioms AKLT.W.GAP047.main`:

```text
'AKLT.W.GAP047.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP047.Main` — success; Lake reported 4.4s for the module.
- `lake env lean /tmp/GAP047Check.lean` — success; checked the declaration and printed its axioms.

## Open issues

None.

## ORCH-SUMMARY

Delivered `AKLT/W/GAP047/Main.lean` with `AKLT.W.GAP047.main` proving `AKLT.Blueprint.Gap.TrialCountStatement`.
The module builds successfully.
Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
No residual statements, deviations, or open issues.
