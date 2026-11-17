STATUS: PROVED

## Files

- Added `AKLT/W/WIN047/Main.lean`.
- No existing files were modified.

## Exported declaration

- `AKLT.W.WIN047.main : AKLT.Blueprint.Win.CutSeparationStatement`

The proof shows `B ⊆ F` and the exterior pin restriction from `B ⊆ U ⊆ F` and the buffer hypothesis. It proves the specified pieces are disjoint and have union `(F \ B) \ X`. For a crossing adjacency from `U` to its complement, the outside endpoint lies in `rawBoundary U`, hence in `X`; this rules out bonds between the pieces. The other two no-bond properties follow directly from the hypotheses and the buffer.

## Axioms

`#print axioms AKLT.W.WIN047.main`:

```text
'AKLT.W.WIN047.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN047.Main`
- Result: successful; Lake reported the module built in 5.6 seconds (10.8 seconds wall time for the command).
- A separate `lake env lean /tmp/WIN047Axioms.lean` check confirmed the exported name and axiom output.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN047.main` with the exact requested type in `AKLT/W/WIN047/Main.lean`.
- Proof uses only the statement hypotheses and elementary finite-set/lattice facts.
- Build succeeded; axioms are `[propext, Classical.choice, Quot.sound]`.
- Report: `/home/ubuntu/aklt/reports/LW/WIN047/report.md`.
- No open issues or deviations.
