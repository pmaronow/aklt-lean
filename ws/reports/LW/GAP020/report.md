STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP020/AKLT/W/GAP020/Main.lean)
- Report: `/home/ubuntu/aklt/reports/LW/GAP020/report.md`

## Exported declaration

`AKLT.W.GAP020.main : AKLT.Blueprint.Gap.HammingPathStatement`

The proof uses a finite set of edge oscillations, with zero included to handle products that have no Hamming-one pairs. It changes differing coordinates one at a time and telescopes the absolute differences. This proves the path bound, including the zero-site case. The reverse direction of the zero-Lipschitz characterization follows because every edge oscillation in the defining set is zero.

## Axioms

`#print axioms AKLT.W.GAP020.main`:

```text
'AKLT.W.GAP020.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP020.Main` — succeeded; Lake reported 4.6 s for the module (9.5 s total command wall time).
- A separate `lake env lean` check of `#print axioms` succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP020/Main.lean` with `AKLT.W.GAP020.main` proving the requested closed statement.
- The build `lake build AKLT.W.GAP020.Main` succeeded.
- Axioms are `[propext, Classical.choice, Quot.sound]`, all permitted.
- The proof explicitly covers empty site sets and singleton alphabets.
- No residual statements, limitations, or deviations remain.
- Orchestrator action: none.
