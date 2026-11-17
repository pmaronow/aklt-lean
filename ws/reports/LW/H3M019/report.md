STATUS: PROVED

## Files

- `AKLT/W/H3M019/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M019/report.md`

## Exported declaration

- `AKLT.W.H3M019.main : AKLT.Blueprint.H3.StationaryWordExpansionStatement`

The proof inducts on the iterate length. At each successor it expands `stationaryApply`, applies the induction hypothesis at each successor state and phase, distributes the coefficient over the word sum, commutes the finite phase and tail-word sums, and reindexes the result by the head/tail equivalence for `DirectionWord (r + 1)`. The head/tail helper and induction lemma are private.

## Axioms

`#print axioms AKLT.W.H3M019.main`:

```text
'AKLT.W.H3M019.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/H3M019/Main.lean` — compiled successfully (9.5 s, direct Lean check).
- `time lake build AKLT.W.H3M019.Main` — succeeded; wall time 16.07 s (module reported 7.9 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M019.main` proving `AKLT.Blueprint.H3.StationaryWordExpansionStatement`.
- Proof uses finite sums over compass labels, phases, and direction words; parallel compass labels remain distinct.
- Build succeeded with `lake build AKLT.W.H3M019.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- No residual statements, deviations, or open issues.
