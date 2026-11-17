STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP030/AKLT/W/GAP030/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/GAP030/report.md`

## Exported declaration

`AKLT.W.GAP030.main : AKLT.Blueprint.Gap.BlockVolumeBoundStatement`

The proof maps `Fin (2*M+1) × Fin (2*M+1)` into `Site L N` by reducing each offset coordinate modulo its period. The hypotheses imply `2*M+1 ≤ L.val` and `2*M+1 ≤ N.val`, so both coordinates remain below their moduli and the map is injective. `Fintype.card_le_of_injective` then gives the volume bound. This follows the offset injection in `t:periodic`, sec4:382–384; it does not use a measure or normalize an update rate.

## Axioms

Output of `#print axioms AKLT.W.GAP030.main`:

```text
'AKLT.W.GAP030.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.GAP030.Main`
- Result: successful; the new module built in 3.4 seconds (the build command completed in about 5 seconds).
- Axiom check: `lake env lean /tmp/GAP030_axioms.lean`, successful.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP030.main` with the exact requested type.
- Proved the bound using an actual injection from the offset square into `Site L N`.
- Requested Lake build succeeded.
- Axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, limitations, or deviations remain.
