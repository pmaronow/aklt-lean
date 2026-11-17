STATUS: PROVED

## Files

- `AKLT/W/WIN013/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN013/report.md`

## Exported declaration

- `AKLT.W.WIN013.main : AKLT.Blueprint.Win.ChainBoxStatement`

The proof forms a finite vertex set by taking the union of `e.toFinset` over `c.support`. It bounds both natural absolute coordinate values on that set using its `Finset.sup`, then chooses the integer cast of `max 1 M`. Thus the argument also supplies `R = 1` when the chain has empty support.

## Axioms

`#print axioms main` output:

```text
'AKLT.W.WIN013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN013.Main`
- Result: successful; module build reported 5.5 seconds (13.2 seconds wall time for the build command).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN013.Main` with the requested theorem and exact type.
- The finite support endpoints are bounded by a finite supremum; the bound is enlarged to one for the zero chain.
- Build: `lake build AKLT.W.WIN013.Main` succeeded.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No open issues or deviations.
