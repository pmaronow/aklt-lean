STATUS: PROVED

## Files

- `AKLT/W/WIN015/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN015/report.md`

## Exported declaration

- `AKLT.W.WIN015.main : AKLT.Blueprint.Win.ColumnFluxStatement`

The proof sums the even-degree identity over the finite portion of the box with first coordinate at most `i`. After exchanging finite sums, each supported nearest-neighbour edge contributes zero unless it crosses the vertical cut; those crossing edges are exactly the horizontal edges in the requested sum. Internal edges contribute twice, which is zero in `ZMod 2`.

## Axiom audit

`#print axioms AKLT.W.WIN015.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the permitted axioms. No residual propositions remain.

## Build

- Command: `lake build AKLT.W.WIN015.Main`
- Result: successful
- Timing: 9.6 seconds wall time; module compilation reported 4.8 seconds

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem and type in `AKLT/W/WIN015/Main.lean`.
- Proof uses only the statement’s hypotheses and finite parity counting.
- Build passed with `lake build AKLT.W.WIN015.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residuals, deviations, or open issues.
