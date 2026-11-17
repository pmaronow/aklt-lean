STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC094/AKLT/W/REC094/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/REC094/report.md)

## Exported declaration

`AKLT.W.REC094.main` proves

```lean
Residual_LocalStepComparisonV2 →
  Residual_TraceProductIdentitiesV2 →
    AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
```

It is conditional and does not yet have the requested unconditional type.

The residuals are closed propositions:

- `Residual_LocalStepComparisonV2` states the nonnegativity and local coefficient-times-step-ratio comparison for each evolving departure on a stopped trail. This is the missing network-to-pattern comparison needed to turn `Top.H1Statement` into the covered-step bound, along with the uncovered and D-step bounds.
- `Residual_TraceProductIdentitiesV2` states the exact factorizations of the trace coefficient and both trace ratios into evolving departure factors. The ratio identities require a positive-normalizer/telescoping argument.

The proved portion compares the two pin choices to one common product, converts the uncovered exceptions into a penalty of `(12/5)^count`, and uses the count bound to obtain `exceptionFactor * trailWeight`.

## Axioms

`#print axioms AKLT.W.REC094.main`:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axioms occur in the delivered Lean file. The residuals are explicit theorem parameters, not axioms.

## Build

Command: `lake build AKLT.W.REC094.Main`

Result: successful; Lake invocation took about 12.8 seconds, with the module reported built in 6.9 seconds.

## Open issues

- Prove `AKLT.W.REC094.Residual_LocalStepComparisonV2` from `AKLT.Blueprint.Top.H1Statement` and the stated trail hypotheses.
- Prove `AKLT.W.REC094.Residual_TraceProductIdentitiesV2` from the trace definitions, including the positivity needed to telescope partition ratios.
- Then expose `AKLT.W.REC094.main` at the exact requested unconditional type.

## ORCH-SUMMARY

- Delivered a compiled conditional proof in `AKLT/W/REC094/Main.lean`.
- `AKLT.W.REC094.main` derives the target statement from `Residual_LocalStepComparisonV2` and `Residual_TraceProductIdentitiesV2`.
- The local step comparison and trace product identities remain open under those exact names.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Build command: `lake build AKLT.W.REC094.Main` (successful).
- Limitation: the requested unconditional theorem is not yet proved; orchestrator should pass on the two residual obligations.
