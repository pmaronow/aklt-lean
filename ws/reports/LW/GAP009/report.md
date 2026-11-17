STATUS: PROVED

## Files

- `AKLT/W/GAP009/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP009/report.md`

## Exported declaration

`AKLT.W.GAP009.main : AKLT.Blueprint.Gap.SurgeryPreservationStatement`

The proof defines the output coupling as the mixture of the supplied row couplings, weighted by the input coupling. Its nonnegativity follows termwise. For each marginal, summing the row marginal and then the input coupling marginal reduces the result to the stationarity identity for `fibre`; that identity is proved from the finite conditional-law definition using positivity of the denominator.

## Axioms

Output of `#print axioms AKLT.W.GAP009.main`:

```text
'AKLT.W.GAP009.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.GAP009.Main`

Result: success, module build reported `4.3s` (Lake completed 8955 jobs).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP009/Main.lean` with `AKLT.W.GAP009.main` proving the exact frozen statement.
- Report: `/home/ubuntu/aklt/reports/LW/GAP009/report.md`.
- Build succeeded with `lake build AKLT.W.GAP009.Main` (4.3s module time).
- Exported theorem uses only `[propext, Classical.choice, Quot.sound]`.
- No residual statements, deviations, or open issues.
