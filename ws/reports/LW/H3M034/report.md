STATUS: PROVED

## Delivered

- File: `/home/ubuntu/aklt/wt/LW_H3M034/AKLT/W/H3M034/Main.lean`
- Exported declaration: `AKLT.W.H3M034.main : AKLT.Blueprint.H3.StationaryCertificateBridgeStatementV2`
- The proof reuses the five unchanged conjunctions from `PassesV2`. For each local row, it equates summands: at a centre destination both rounded products vanish using the checked centre value, and away from the centre the two stationary coefficients agree. It carries the existing coefficient and value scales through unchanged.
- No array or `Correct` witness is constructed.

## Axioms

`#print axioms AKLT.W.H3M034.main`:

```text
'AKLT.W.H3M034.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.H3M034.Main`
- Result: successful; Lake reported `Built AKLT.W.H3M034.Main (5.0s)` and `Build completed successfully (8972 jobs)`.
- Axiom check: `lake env lean /tmp/H3M034-Axioms.lean` completed successfully.

## Open issues

None.

## ORCH-SUMMARY

- Delivered and compiled `AKLT.W.H3M034.main` with the exact requested statement type.
- Proved the legacy/corrected local integer row comparison by destination case split.
- Axiom footprint: `propext`, `Classical.choice`, `Quot.sound`.
- No open proof obligations or deviations.
- No orchestrator decision needed.
