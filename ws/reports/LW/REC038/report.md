STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC038/AKLT/W/REC038/Main.lean) proves the requested leaf.

## Exported declaration

`AKLT.W.REC038.main : AKLT.Blueprint.Rec.DStepMomentStatement`

The proof expands the two cases `k = 0` and `k = 1`. It derives the first and second coordinate moments directly from the explicit icosahedral labels, transfers them to the D site law including its zero atom, and uses finite-sum linearity to obtain the dot-product identity. It does not use another blueprint leaf as a lemma.

## Axioms

Output of `#print axioms AKLT.W.REC038.main`:

```text
'AKLT.W.REC038.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC038.Main` — completed successfully in 21.5 seconds wall time (16 seconds reported for the module).
- `lake env lean AKLT/W/REC038/PrintAxioms.lean` — completed successfully and produced the axiom output above; the temporary audit file was removed.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC038/Main.lean` with the exact requested theorem name and type.
- Proved the k=0 and k=1 cases from explicit D-law first and second moments.
- No residual statements, deviations, or open issues.
- Lake build succeeded; exported axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
