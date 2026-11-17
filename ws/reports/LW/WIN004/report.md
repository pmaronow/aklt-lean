STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN004/AKLT/W/WIN004/Main.lean`

## Exported declaration

`AKLT.W.WIN004.main : AKLT.Blueprint.Win.RadiusGapStatement`

The proof sets `s = shellSpacing u`. Since `s ≥ 16`, `Int.sub_one_lt_floor` gives
`2s/3 < ⌊s⌋`. For `i < j`, we have `(i + 1)s ≤ js`; monotonicity of floor and
`Int.le_floor_add` then give `⌊is⌋ + ⌊s⌋ ≤ ⌊js⌋`, yielding the stated radius gap.

## Axioms

`#print axioms AKLT.W.WIN004.main`:

```text
'AKLT.W.WIN004.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN004.Main` — succeeded; module compilation reported 5.8 s.
- Axiom inspection with `lake env lean /tmp/WIN004Axioms.lean` succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN004/Main.lean` with `AKLT.W.WIN004.main` at the requested type.
- The requested Lake build succeeded.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
