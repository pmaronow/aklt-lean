STATUS: PROVED

## Files

- `AKLT/W/MOM006/Main.lean`

## Exported declaration

- `AKLT.W.MOM006.main : AKLT.Blueprint.Mom.MixedScalarMomentStatement`

## Proof summary

The proof expands the finite moment and enumerates the coordinate pairs. For each distinct pair, four labels contribute the same squared-coordinate product and all other labels contribute zero. The algebraic steps prove `goldenRatio ^ 2 = goldenRatio + 1`, `icoRadius ^ 2 = goldenRatio + 2`, and hence `icoRadius ^ 4 = 5 * goldenRatio ^ 2`; clearing the positive radius denominators gives `1 / 15`.

## Axioms

`#print axioms AKLT.W.MOM006.main`:

```text
'AKLT.W.MOM006.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms.

## Build

- `lake env lean AKLT/W/MOM006/Main.lean` — succeeded (16.5 s wall time).
- `lake build AKLT.W.MOM006.Main` — succeeded; Lake reported the target built in 14 s (23.7 s wall time for the command).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/MOM006/Main.lean` with the requested theorem and exact type.
- Proved the mixed scalar moment by finite coordinate and label enumeration, followed by golden-ratio and radius algebra.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- `lake build AKLT.W.MOM006.Main` succeeded.
- No deviations or open issues.
