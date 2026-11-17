STATUS: PROVED

## Files

- `AKLT/W/H3M009/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M009/report.md`

## Exported declaration

`AKLT.W.H3M009.main : AKLT.Blueprint.H3.SuffixWindowValidityStatement`

The proof translates the ten local window bonds by the vertex at the window origin. They become whole-trail bonds at indices `i - 10` through `i - 1`, so the whole-trail injectivity proves `RawWindow`. The next local bond translates to the whole-trail bond at `i`, distinct from every remembered bond. If the next direction reversed the window arrival, the bond at `i` would equal the bond at `i - 1`, contradicting the same injectivity.

## Axioms

`#print axioms AKLT.W.H3M009.main`:

```text
'AKLT.W.H3M009.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M009.Main`
- Result: success; Lean reported the module build in 8.8 seconds (the final Lake invocation took 18.5 seconds wall time).
- Axiom check: `lake env lean /tmp/H3M009Axioms.lean`

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem with its exact name and type in `AKLT/W/H3M009/Main.lean`.
- The theorem compiles with `lake build AKLT.W.H3M009.Main`.
- The only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No statement or existing project file was edited.
- No open proof obligations or deviations remain.
