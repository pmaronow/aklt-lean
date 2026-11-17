STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP055/AKLT/W/GAP055/Main.lean)
- `/home/ubuntu/aklt/reports/LW/GAP055/report.md`

## Exported declaration

`AKLT.W.GAP055.main : AKLT.Blueprint.Gap.HammingCardinalityStatement`

The proof counts the integer sup-ball inside the translated coordinate rectangle of radius `n^3`, then counts the square subtype as a product of two centered integer intervals. The hypothesis `1 ≤ n` supplies the lower bounds needed for `2x + 1 ≤ 3x`; the remaining numerical estimates follow from squaring and the slack factor 25.

## Axiom audit

`#print axioms AKLT.W.GAP055.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.GAP055.Main`
- Result: successful; target module built in 4.5s (full Lake invocation completed in 9.1s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP055/Main.lean` with the requested theorem name and type.
- Proved the near-region complement bound by an injection into a translated integer rectangle.
- Proved the square bound from exact interval cardinalities and the `n ≥ 1` polynomial estimate.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Build: `lake build AKLT.W.GAP055.Main` succeeded.
- No residual statements, deviations, or open issues.
