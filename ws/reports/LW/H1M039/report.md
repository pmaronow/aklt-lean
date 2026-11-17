STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M039/AKLT/W/H1M039/Main.lean)

## Exported declaration

- `AKLT.W.H1M039.main : AKLT.Blueprint.H1.LadderWalkStatement`

The proof iterates lowering for nonnegative integer offsets and raising for negative offsets. Private induction lemmas track subspace membership, nonvanishing, the preserved `O` eigenvalue, and the current spin weight. The sign bounds follow from `κ = 0 ∨ κ = 1/2` and integer step counts.

## Axioms

`#print axioms AKLT.W.H1M039.main`:

```text
'AKLT.W.H1M039.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M039.Main` — succeeded; final timed run took 12.46 seconds wall time (module compilation reported 6.2 seconds).
- Axiom check used `lake env lean /tmp/H1M039Axioms.lean`, importing the built module and printing the theorem and its axioms.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M039.main` with the exact requested statement.
- Build succeeded with `lake build AKLT.W.H1M039.Main`.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No residual statements or open proof obligations remain.
- No deviations from the requested file and theorem names.
