STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC075/AKLT/W/REC075/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/REC075/report.md)

## Exported declaration

`AKLT.W.REC075.main : AKLT.Blueprint.Rec.ProtectedDistanceFiniteStatement`

The proof chooses a site of `G` with maximal first coordinate. Its east neighbor cannot lie in `G`, so its distance to the exterior is one and the site belongs to `protectedSites G`. This gives a witness in the protected set. For any `x`, the infimum defining distance to that set is bounded above by the distance from `x` to this witness, which is finite; hence it is not `⊤`.

## Axioms

Output of `#print axioms AKLT.W.REC075.main`:

```text
'AKLT.W.REC075.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC075.Main`
- Result: successful; the final module build reported 5.0 seconds.
- Axiom check: `lake env lean /tmp/REC075Axioms.lean` succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC075.main` with the requested exact type.
- The proof is direct from finite-lattice definitions; no residual propositions or helper files were needed.
- `lake build AKLT.W.REC075.Main` succeeds.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No deviations or open issues.
