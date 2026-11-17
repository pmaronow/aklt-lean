STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN001/AKLT/W/WIN001/Main.lean)
- Report: `/home/ubuntu/aklt/reports/LW/WIN001/report.md`

## Exported declaration

`AKLT.W.WIN001.main : AKLT.Blueprint.Win.ShellScaleStatement`

The proof obtains the two fourth-root identities by squaring `Real.sqrt` twice. The threshold gives both lower bounds on the spacing. Those bounds imply the two low-degree estimates, and `Int.lt_floor_add_one` gives the final floor inequality.

## Axioms

`#print axioms AKLT.W.WIN001.main`:

```text
'AKLT.W.WIN001.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All listed axioms are permitted by the task rules.

## Build

- Command: `lake build AKLT.W.WIN001.Main`
- Result: successful
- Reported module build time: 8.5 s (8,955 Lake jobs)
- A separate `lake env lean /tmp/WIN001_axioms.lean` axiom audit completed successfully.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN001/Main.lean` with the exact theorem name and requested type.
- The module builds successfully.
- Axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, helper files, or deviations.
- No open issues.
