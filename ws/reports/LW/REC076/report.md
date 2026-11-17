STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC076/AKLT/W/REC076/Main.lean) — defines the signed coordinate symmetries, proves their distance preservation and direction classification, and proves the requested theorem.
- `/home/ubuntu/aklt/reports/LW/REC076/report.md` — this report.

## Exported declaration

`AKLT.W.REC076.main : AKLT.Blueprint.Rec.PairCanonicalGeometryStatement`

The proof extracts compass directions from the two center adjacencies, classifies their ordered pair using `HasPairType`, chooses the corresponding signed coordinate permutation, and composes it with translation by the designated center. It proves the three image equalities and preserves `latticeDist` for every pair of plane points.

## Axioms

`#print axioms AKLT.W.REC076.main`:

```text
'AKLT.W.REC076.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC076.Main` — succeeded; 14.8 s wall time (Lake reported module build time 7.4 s).
- `lake env lean /tmp/REC076Axioms.lean` — succeeded; 6.6 s wall time and printed the axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC076.main` with the requested exact type in `AKLT/W/REC076/Main.lean`.
- The proof is complete and the requested Lake build succeeded.
- Axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations remain.
- Orchestrator action: none required.
