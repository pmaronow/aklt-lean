STATUS: PROVED

# H3C055 — prove one blueprint leaf

## Delivered files

- `/home/ubuntu/aklt/wt/LW_H3C055/AKLT/W/H3C055/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C055/report.md`

## Exported declaration

`AKLT.W.H3C055.main : CertData.H3.Bridge.PassesEquivalenceLeaf`

The proof isolates the stationary row comparison. For each edge whose destination is the centre, the V2 coefficient vanishes and the legacy summand vanishes by the checked zero-centre value. For other destinations, simplifying `stationaryCoefficientV2` and `stationaryCoefficient` gives the same coefficient. The shared certificate clauses are carried through directly; the certificate is not normalized wholesale.

## Axioms

`#print axioms AKLT.W.H3C055.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.H3C055.Main`

Result: success. The final Lean module compiled in 8.2 seconds; total command wall time was about 14 seconds.

## Open issues and deviations

- No proof issues remain.
- The requested alternate cheaper-model first attempt could not be performed: this turn provides no alternate-model invocation, and the campaign explicitly prohibits sub-agents. The proof was completed in the active model without delegation.
- The row identity was proved directly from the retained coefficient definitions and the centre-zero clause; the Packed/Bellman API is not needed for this definitional bridge.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C055.main` with the exact requested closed statement.
- Proof establishes equality of legacy and V2 local row sums using `stationaryCoefficientV2` and the checked zero-centre condition.
- Build: `lake build AKLT.W.H3C055.Main` succeeded; module compile 8.2 seconds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No open proof obligations.
- Deviation: alternate cheaper-model attempt unavailable without violating the no-sub-agents instruction.
- Orchestrator decision: none required.
