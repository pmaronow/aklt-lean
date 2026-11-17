STATUS: PROVED

## Files

- `AKLT/W/GAP056/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP056/report.md`

## Exported declaration

`AKLT.W.GAP056.main : AKLT.Blueprint.Gap.HammingBudgetStatement`

The proof splits the budget into two `n^8 / 2000` estimates. The first follows from `50000 ≤ n^2`; the second follows by combining the explicit tail bound with `50000 * 2^20 * 20! ≤ n^12 * d^20`, after establishing denominator positivity.

## Axioms

Output of `#print axioms AKLT.W.GAP056.main`:

```text
'AKLT.W.GAP056.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.GAP056.Main`

Result: successful; module build reported 4.8s, command completed in 10.2s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP056.main` with the exact requested type in `AKLT/W/GAP056/Main.lean`.
- Proved the budget by splitting it into two `n^8 / 2000` bounds.
- `lake build AKLT.W.GAP056.Main` succeeds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No known limitations or open issues.
