STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC079/AKLT/W/REC079/Main.lean)

## Declarations

- `AKLT.W.REC079.Residual_PositiveTraceKernelLengths`: the frozen comparison restricted to positive lengths.
- `AKLT.W.REC079.main_from_residual (hpositive : Residual_PositiveTraceKernelLengths) : AKLT.Blueprint.Rec.TraceKernelLengthStatement`.
- Private helper `traceKernelLength_zero`: proves the length-zero case directly from the distance-two endpoint condition and the impossibility of a length-zero canonical kernel trail.

The requested exact theorem `AKLT.W.REC079.main : AKLT.Blueprint.Rec.TraceKernelLengthStatement` is not delivered. The remaining residual is the positive-length trace-to-kernel comparison. Its proof needs the long §7 argument: response exposure along actual U departures, V2 covered-departure response bounds, response-pair closure after removal, comparison of live pairs and shifts, and the fixed-isometry trail embedding. No unsupported residual was used as a theorem or axiom.

## Axioms

`#print axioms AKLT.W.REC079.main_from_residual`:

```text
[propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.REC079.traceKernelLength_zero`:

```text
[propext, Classical.choice, Quot.sound]
```

These are permitted axioms. There are no `sorry`, `admit`, or added axioms in the delivered Lean file.

## Build

- `lake build AKLT.W.REC079.Main` — passed, 4.8 s (single module; existing dependencies were already built).

## Open issue

Prove `AKLT.W.REC079.Residual_PositiveTraceKernelLengths` from `Top.H1Statement`, then expose the exact requested declaration `AKLT.W.REC079.main`.

## ORCH-SUMMARY

- Delivered a compiled reduction theorem and a direct proof of the zero-length case.
- Remaining exact residual: `AKLT.W.REC079.Residual_PositiveTraceKernelLengths`.
- The requested exact theorem `AKLT.W.REC079.main` remains open; report status is PARTIAL.
- No existing blueprint or definition files were edited; no unsupported residual was treated as proved.
- Build: `lake build AKLT.W.REC079.Main` passed; axioms are permitted (`propext`, `Classical.choice`, `Quot.sound`).
