STATUS: PROVED

## Files

- `AKLT/W/MOM003/Main.lean`
- `/home/ubuntu/aklt/reports/LW/MOM003/report.md`

## Exported declaration

`AKLT.W.MOM003.main : AKLT.Blueprint.Mom.OddMonomialStatement`

The proof selects an odd exponent coordinate, pairs each label with an involutive flip of that coordinate (fixing the group where the coordinate is zero), and reindexes the finite sum. Each paired monomial is its negative, so the sum and hence the moment vanish.

## Axioms

`#print axioms AKLT.W.MOM003.main`:

```text
'AKLT.W.MOM003.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

`PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.MOM003.Main` — succeeded; command wall time about 19 seconds (module build reported about 11 seconds).

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/MOM003/Main.lean`.
- The statement is proved from its definition and the existing moment and monomial definitions.
- Build succeeded; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
