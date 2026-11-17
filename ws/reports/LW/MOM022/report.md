STATUS: PROVED

## Files

- `AKLT/W/MOM022/Main.lean`
- `/home/ubuntu/aklt/reports/LW/MOM022/report.md`

## Exported declaration

`AKLT.W.MOM022.main : AKLT.Blueprint.Mom.BallFieldSplitStatement`

The proof uses `r = sqrt (normSq a)` and `e = a / r` when `r > 0`, establishing unit norm and the affine coordinate identity. When the radius is zero, it proves each coordinate of `a` is zero and chooses a fixed coordinate unit vector with `t = 1/2`.

## Axioms

`#print axioms AKLT.W.MOM022.main`:

```text
'AKLT.W.MOM022.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.MOM022.Main`
- Result: success; final build invocation took 17.1 seconds wall time, with Lean reporting 8.5 seconds for this module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.MOM022.main` with the requested statement in `AKLT/W/MOM022/Main.lean`.
- The requested Lake module build succeeds.
- Axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
