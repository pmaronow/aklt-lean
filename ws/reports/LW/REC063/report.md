STATUS: PROVED

## Files

- `AKLT/W/REC063/Main.lean` — proof of the requested support statement.
- `/home/ubuntu/aklt/reports/LW/REC063/report.md` — this report.

## Exported declaration

`AKLT.W.REC063.main : AKLT.Blueprint.Rec.KernelSupportStatement`

The proof bounds the Manhattan distance of each path vertex by its index. Every response-pair site is a neighbor of the current vertex, so its distance from `kernelStart` is at most `i + 1`; consequently its `pairShift` is at most `i + 1`. For `s > n + 1`, every `responseKappa` term is zero, hence the exposure sum and length-n coefficient are zero. At length zero, the start vertex cannot equal either target.

## Axioms

`#print axioms AKLT.W.REC063.main`:

```text
'AKLT.W.REC063.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build and verification

- `lake build AKLT.W.REC063.Main` — succeeded; Lean reported the target module built in 5.1 seconds (10.6 seconds command wall time).
- `printf 'import AKLT.W.REC063.Main\n#print axioms AKLT.W.REC063.main\n' | lake env lean --stdin` — succeeded; 5.8 seconds.
- No tests were added or run.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC063.main` with the exact requested type in `AKLT/W/REC063/Main.lean`.
- The support bound follows from a path-length Manhattan-distance estimate and the response-pair neighbor definition.
- The length-zero coefficient vanishes because the fixed start is distinct from both targets.
- Build succeeded; axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual declarations or open issues.
