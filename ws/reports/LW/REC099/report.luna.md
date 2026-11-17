STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC099/AKLT/W/REC099/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/REC099/report.md)

## Exported declarations

- `AKLT.W.REC099.in_diamondOffsets`: every site at lattice distance 1 or 2 from `e` is `e + d` for some `d ∈ diamondOffsets`.
- `AKLT.W.REC099.uDepartureInjective`: along a stopped network trail, two indices whose departure status is U cannot have the same vertex.
- `AKLT.W.REC099.Residual_terminalLocalCover : Prop`: every second-trail U departure farther than two from the first terminal site has a `CoveredDepartureV2` template.
- `AKLT.W.REC099.main (hLocalCover : Residual_terminalLocalCover) : TerminalExceptionCountStatementV2`: proves the requested count from the explicit local-cover residual. The requested closed type `AKLT.W.REC099.main : TerminalExceptionCountStatementV2` is not yet proved.

The counting and geometry steps are complete: exceptions map injectively to the twelve sites in the punctured radius-two diamond. The remaining obligation is the local pattern construction for departures away from the first terminal site's defect. It requires establishing the kept-set and present-bond invariants through both traces and constructing a `PatternData.Covered` witness; this file does not assume that obligation as a theorem or axiom.

## Axioms

`#print axioms` output:

```text
AKLT.W.REC099.in_diamondOffsets: [propext, Classical.choice, Quot.sound]
AKLT.W.REC099.uDepartureInjective: [propext, Classical.choice, Quot.sound]
AKLT.W.REC099.main: [propext, Classical.choice, Quot.sound]
```

The residual is an explicit closed `def ... : Prop`; it is an argument of the conditional theorem, not an axiom or hidden theorem premise.

## Build

- `lake build AKLT.W.REC099.Main` — passed; target module built in 13 seconds (8965/8965 jobs).

## Open issue

- Prove `AKLT.W.REC099.Residual_terminalLocalCover`; until then, the exact requested closed theorem remains open.

## ORCH-SUMMARY

- Delivered the finite diamond enumeration, injectivity of U departures, and the count proof conditional on `Residual_terminalLocalCover`.
- Open: `AKLT.W.REC099.Residual_terminalLocalCover` and therefore the closed requested theorem type.
- The exported `main` currently has an explicit residual premise; it does not have the exact requested type.
- No forbidden axioms or tactics are used; printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- Build command: `lake build AKLT.W.REC099.Main` (passed, 13 seconds).
- Orchestrator decision: continue the local trace-invariant and covered-pattern construction to discharge the residual.
