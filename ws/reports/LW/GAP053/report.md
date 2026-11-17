STATUS: PROVED

## Delivered files

- `AKLT/W/GAP053/Main.lean`
- This report: `/home/ubuntu/aklt/reports/LW/GAP053/report.md`

## Exported declaration

`AKLT.W.GAP053.main : AKLT.Blueprint.Gap.BinomialTailStatement`

The proof expands `(1 + d)^(n - 3)` and keeps its degree-20 term. `Nat.pow_le_choose` bounds the associated binomial coefficient using the twenty falling factors, with the natural subtractions shown explicitly as `n - 3` and `n - 22`. Pairing with `(1 - d)^(n - 3)` yields the stated reciprocal bound.

## Axioms

Output of `#print axioms AKLT.W.GAP053.main`:

```text
'AKLT.W.GAP053.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.GAP053.Main`

Result: successful; Lake reported the module built in 4.5s (command wall time 9.57s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered and compiled `AKLT.W.GAP053.Main` with the exact requested theorem name and type.
- `AKLT.W.GAP053.main` has only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
