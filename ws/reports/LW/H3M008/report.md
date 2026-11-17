STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3M008/AKLT/W/H3M008/Main.lean)
- Report: `/home/ubuntu/aklt/reports/LW/H3M008/report.md`

## Exported declaration

- `AKLT.W.H3M008.main : AKLT.Blueprint.H3.PhaseSplitAlgebraStatement`

The proof aligns the first `L` entries of `finRange n` with `finRange L`, applies the assumed coefficient equalities to identify the prefix rows, then uses `take ++ drop` to split the fold. Linearity of the suffix fold in its initial row is proved by expanding that row in the four delta-phase basis vectors.

## Axioms

`#print axioms AKLT.W.H3M008.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3M008.Main` — successful; Lean module build reported 8.3s (20.0s total command wall time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3M008/Main.lean` with the requested theorem name and type.
- `AKLT.W.H3M008.main` is proved from its statement's coefficient-equality premise.
- Build succeeds; axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
