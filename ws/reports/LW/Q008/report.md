STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q008/AKLT/W/Q008/Main.lean) — complete proof and private algebra helpers.
- [report.md](/home/ubuntu/aklt/reports/LW/Q008/report.md) — this report.

## Exported declaration

`AKLT.W.Q008.main : AKLT.Blueprint.Q.SpinorChoiceStatement`

The proof handles `v 2 = -1` first, deriving `v 0 = v 1 = 0` from unit length. In the other branch, unit length and exclusion of the south pole give `0 < 1 + v 2`; positive square roots then provide the denominator relation. It verifies the spinor norm and the four entries of the outer product against `spinDensity`.

## Axioms

Output of `#print axioms AKLT.W.Q008.main`:

```text
'AKLT.W.Q008.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/Q008/Main.lean` — passed, about 15 seconds.
- `lake build AKLT.W.Q008.Main` — passed, 7.4 seconds wall time on the final cached build (8953 jobs).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q008.main` with the requested exact type.
- Proof covers the south pole separately and the positive-root chart elsewhere.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build AKLT.W.Q008.Main` passed.
- No residual statements, limitations, or orchestrator decisions remain.
