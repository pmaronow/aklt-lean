STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_REC040/AKLT/W/REC040/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC040/report.md`

## Exported theorem

`AKLT.W.REC040.main : AKLT.Blueprint.Rec.TraceCoefficientStatement`

The proof develops a recursive `TraceGood` invariant for the evolving prefix network, using distinct bonds to show each future trail edge remains present after a trace step. It identifies the recursive count of D departures with the statement's `Fin n` filter over prefix networks, then applies the exact coefficient recurrence. Positivity follows from the two positive rational bases.

Supporting declarations are in `AKLT.W.REC040`, including `stoppedNetworkTrail_tail`, `traceGood_of_stopped`, and `traceDCount_wordVertices`.

## Axioms

`#print axioms AKLT.W.REC040.main`:

```text
'AKLT.W.REC040.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC040.Main` — succeeded in about 4.5 seconds.
- `lake env lean /tmp/rec040_axioms.lean` — succeeded and printed the theorem type and axioms.

The build reports pre-existing style and deprecation warnings in the helper proof file; no errors remain.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC040.main` with the exact requested statement.
- Proved evolving departure statuses and retained future trail bonds by induction on trail length.
- Matched the evolving D-departure count to the prefix-network count in the statement.
- Build succeeds; theorem axioms are exactly propext, Classical.choice, and Quot.sound.
- Only compiler warnings are style/deprecation warnings in the proof file.
- No open residual statements or required orchestrator decisions.
