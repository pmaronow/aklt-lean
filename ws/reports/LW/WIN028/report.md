STATUS: PROVED

## Files

- `AKLT/W/WIN028/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN028/report.md`

## Exported declaration

`AKLT.W.WIN028.main : AKLT.Blueprint.Win.NeighbourDecayStatement`

The proof shows that the distance to the complement of a finite set is attained and changes by at most one across a step of lattice distance at most one. The resulting depth inequality gives the claimed decay comparison for `0 < θ < 1`, including depth zero.

## Axioms

`#print axioms AKLT.W.WIN028.main`:

```text
'AKLT.W.WIN028.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN028.Main`
- Result: successful; module build reported 5.5 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN028/Main.lean` with the requested theorem and exact statement.
- Proof uses a nearest complementary site, a lattice-distance triangle bound, and monotonicity of powers for `0 < θ < 1`.
- Build passed: `lake build AKLT.W.WIN028.Main` (5.5 seconds for the module).
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No open issues or deviations.
