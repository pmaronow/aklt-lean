STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q003/AKLT/W/Q003/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/Q003/report.md)

## Exported declaration

- `AKLT.W.Q003.main : AKLT.Blueprint.Q.IcoDistanceStatement`

The proof expands the explicit coordinate/sign definitions, exhausts the twelve labels for each endpoint, and discharges the resulting real inequalities using `sqrt 5 ^ 2 = 5`, `goldenRatio ^ 2 = goldenRatio + 1`, and `icoRadius ^ 2 = goldenRatio + 2`. The premise `a ≠ b` is used to rule out equal-label cases.

The exhaustive split uses `set_option maxHeartbeats 1000000` for this theorem; the limit is finite and nonzero.

## Axioms

`#print axioms AKLT.W.Q003.main`:

```text
'AKLT.W.Q003.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q003.Main` — successful, 73 seconds.
- A separate `lake env lean --stdin` check imported the module and printed the axioms above — successful, 6 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q003.main` with the exact requested type.
- The only new Lean file is `AKLT/W/Q003/Main.lean`.
- Build succeeded; exported theorem uses only the permitted Lean axioms.
- The exhaustive proof uses the stated finite heartbeat limit; no residual statements or open issues.
