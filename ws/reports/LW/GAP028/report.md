STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP028/AKLT/W/GAP028/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/GAP028/report.md`

## Exported declaration

`AKLT.W.GAP028.main : AKLT.Blueprint.Gap.ContainingBlockCountStatement`

The proof identifies the filtered centre-label set with the image of the integer offset square under `z ↦ x - reduction L N z`. The reduction is injective on that square because each coordinate difference is at most `2*M`, strictly below the corresponding period. The square's cardinality is the product of its two interval cardinalities, namely `(2*M+1)^2`.

## Axioms

Output of `#print axioms AKLT.W.GAP028.main`:

```text
'AKLT.W.GAP028.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.GAP028.Main`
- Result: successful; Lean reported `Built AKLT.W.GAP028.Main (3.7s)` (about 9 seconds wall time for the build invocation).
- A separate `lake env lean --stdin` check confirmed the theorem's name and type and printed the axioms above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP028/Main.lean` with `AKLT.W.GAP028.main` proving the exact frozen statement.
- Build succeeded with `lake build AKLT.W.GAP028.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
