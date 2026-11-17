STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q014/AKLT/W/Q014/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/Q014/report.md`

## Exported declaration

`AKLT.W.Q014.main : AKLT.Blueprint.Q.ResolutionExpansionStatement`

The proof expands the complex norm square into its finite double sum, exchanges
the finite sums, applies the `resolution` Gram identity, and collapses the
Kronecker diagonal to the inverse-binomial coefficient norm. It retains the
factor `5 * w a` and does not require positivity of the weights.

## Axioms

`#print axioms AKLT.W.Q014.main`:

```text
'AKLT.W.Q014.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q014.Main` — passed; Lake reported 6.9s for the target
  build (17.2s wall time for the command).
- `lake env lean /tmp/Q014axioms.lean` — passed; printed the axioms above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q014.main` with the exact requested statement.
- New Lean file: `AKLT/W/Q014/Main.lean`.
- The requested Lake module build passes.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
