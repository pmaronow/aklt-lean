STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC096/AKLT/W/REC096/Main.lean)

## Exported declarations

- `AKLT.W.REC096.ResidualKeptPrefixInvariant : Prop` — every trace prefix is auxiliary; away from the live endpoint, U sites retain all original in-volume flags, D sites have two kept flags, active adjacent endpoints agree on flags, and departed sites are no longer U.
- `AKLT.W.REC096.ResidualLiveArrivalInvariant : Prop` — at a live U departure, the kept set is exactly the in-volume neighbour set with the arrival site erased.
- `AKLT.W.REC096.ResidualPrefixGeometry : Prop` — the radius-two template lies in the original volume, the outgoing bond is present, and the departure does not immediately reverse its arrival.
- `AKLT.W.REC096.ResidualTemplateExtraction : Prop` — the local finite template-classification implication from these frozen prefix facts to `CoveredDepartureV2`.
- `AKLT.W.REC096.main_of_residuals` proves `AKLT.Blueprint.Rec.CoveredClosureStatementV2` assuming the four explicit residual propositions above.

The requested declaration `AKLT.W.REC096.main : AKLT.Blueprint.Rec.CoveredClosureStatementV2` is not yet proved or exported.

## Axioms

`#print axioms main_of_residuals`:

```text
'AKLT.W.REC096.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC096.Main`
- Result: successful; Lean reported `Built AKLT.W.REC096.Main (5.6s)`.

## Open issues

The residuals have not been proved. The main missing work is the induction establishing the frozen prefix and arrival invariants, the geometric facts from trail hypotheses, and the local `PatternData` extraction proving `ResidualTemplateExtraction`. Until those are discharged, the exact requested `main` declaration is absent.

## ORCH-SUMMARY

- Delivered a compiled residual reduction in `AKLT/W/REC096/Main.lean`.
- `main_of_residuals` has the exact target conclusion, conditional on four named residual propositions.
- Open: `ResidualKeptPrefixInvariant`, `ResidualLiveArrivalInvariant`, `ResidualPrefixGeometry`, and `ResidualTemplateExtraction`.
- The requested unconditional `AKLT.W.REC096.main` is not delivered; status is PARTIAL.
- The module build succeeded in 5.6 seconds; reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- Orchestrator should treat this leaf as open until all four residuals are proved and the exact `main` theorem is exported.
