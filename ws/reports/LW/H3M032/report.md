STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3M032/AKLT/W/H3M032/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3M032/report.md`

## Exported declaration

`AKLT.W.H3M032.main : AKLT.Blueprint.H3.StationaryCentreZeroOperatorStatementV2`

For each direction and next phase, the proof splits on whether the destination is the centre. At the centre, the continuation value is zero by the supplied hypothesis, so both products vanish. At every other destination, simplification of the literal coefficient definitions proves their equality. Finite-sum congruence then proves equality of the operators.

## Axioms

`#print axioms AKLT.W.H3M032.main`:

```text
'AKLT.W.H3M032.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M032.Main`
- Result: successful; `Built AKLT.W.H3M032.Main` in 5.4s (Lake reported 8972/8972 jobs).
- Axiom inspection: `lake env lean /tmp/H3M032Axioms.lean` completed successfully.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem at the exact name and type in `AKLT/W/H3M032/Main.lean`.
- Proof compares each direction/phase summand and handles centre destinations using the zero-value premise.
- Module build succeeded; only the allowed standard axioms are reported.
- No deviations or open issues.
