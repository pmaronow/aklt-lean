STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C018/AKLT/W/H1C018/Main.lean) — contains the delivered theorem and private helper lemmas.

## Exported declaration

`AKLT.W.H1C018.main : AKLT.Cert.H1.Production.Leaves.packingDecode`

The proof composes the supplied expansion, coefficient bound, and signed-packing hypotheses row by row. It uses the actual sector lane count `(b.sector.map (fun s => s.coordinates.length)).prod`. From `LayoutAccepted`, it proves each remapped column is in that mixed-radix range by following the parity bit through `sectorLabel` and the selected coordinate lists.

## Axioms

`#print axioms AKLT.W.H1C018.main`:

```text
'AKLT.W.H1C018.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed Lean axioms.

## Build

- `lake build AKLT.W.H1C018.Main` — succeeded; 13.52 seconds wall time, with the target module reported at 8.1 seconds.
- `lake env lean /tmp/H1C018_Axioms.lean` — succeeded; 6.45 seconds wall time.

Lake emitted only linter warnings for redundant/unused simp arguments in `Main.lean` and pre-existing warnings in imported modules.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C018.main` with the exact requested type in `AKLT/W/H1C018/Main.lean`.
- The row decoder uses the three explicit hypotheses of `packingDecode`.
- The decoder lane count is the sector coordinate-length product.
- The remapped-index range proof follows sector parity and selected coordinates.
- Build succeeded: `lake build AKLT.W.H1C018.Main`.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No residual statements, extra helper files, or open issues.
