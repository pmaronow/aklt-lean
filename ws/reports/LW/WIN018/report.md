STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN018/AKLT/W/WIN018/Main.lean`

## Exported declaration

`AKLT.W.WIN018.main : AKLT.Blueprint.Win.PlaquetteTrianglesStatement`

The proof puts each of the two square triangles in `triangleSpan`, adds them using submodule closure, and proves coefficientwise that their sum is `plaquette p`. The duplicated diagonal coefficient vanishes in `ZMod 2`.

## Axioms

Output of `#print axioms AKLT.W.WIN018.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN018.Main`
- Result: success
- Wall time: 10.286 s; Lean reported the module build at 5.5 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN018/Main.lean` with `AKLT.W.WIN018.main` proving the requested statement.
- Build succeeded with `lake build AKLT.W.WIN018.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No helper files, residual claims, or deviations.
- No open issues or orchestrator decisions.
