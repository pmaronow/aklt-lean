STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3M026/AKLT/W/H3M026/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M026/report.md`

## Exported declaration

`AKLT.W.H3M026.main : AKLT.Blueprint.H3.FirstDirectionPartitionStatement`

The proof partitions the finite word sum at each positive length by its first compass direction. The first index exists since each summed length is in `Icc 1 R`. A closed trail cannot start east: its first vertex would be `kernelCentre`, contradicting the centre-avoidance clause of `ClosedTrail`. The north, west, and south contributions therefore reassemble the full row; distributing the finite sums over lengths gives the statement.

## Axioms

Output of `#print axioms AKLT.W.H3M026.main`:

```text
'AKLT.W.H3M026.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.H3M026.Main` — succeeded; module build reported 6.8 s.
- `export PATH="$HOME/.elan/bin:$PATH"; lake env lean AKLT/W/H3M026/Main.lean` — succeeded and printed the axiom list above (about 5 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem as `AKLT.W.H3M026.main` in `AKLT/W/H3M026/Main.lean`.
- The requested module builds successfully.
- Axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- No deviations or open issues.
