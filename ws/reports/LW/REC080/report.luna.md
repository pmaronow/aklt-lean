STATUS: PARTIAL

## Files

- `AKLT/W/REC080/Main.lean`

## Delivered declarations

- `AKLT.W.REC080.ResidualTerminalExpansion : Prop` — the terminal two-point expectation is bounded by the normalized terminal network's `onePointSum`.
- `AKLT.W.REC080.ResidualTerminalTail : Prop` — that `onePointSum` has the required geometric tail.
- `AKLT.W.REC080.main (hExpansion : ResidualTerminalExpansion) (hTail : ResidualTerminalTail) : AKLT.Blueprint.Rec.ResidualTargetBoundStatement` — combines the two residual bounds by transitivity.

`main` is conditional and therefore does not yet have the requested direct type. Both residual obligations are explicit closed propositions; neither is asserted as proved. The expansion residual omits the tail estimate, and the tail residual concerns a one-point sum rather than the target two-point expectation.

## Axioms

`#print axioms AKLT.W.REC080.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC080.Main` — succeeded; Lean reported the module built in 5.6 s.

## Open issues

- Prove `AKLT.W.REC080.ResidualTerminalExpansion` from the second pair expansion and the removal realization.
- Prove `AKLT.W.REC080.ResidualTerminalTail` using the shared-matcher covering, twelve-exception bound, and one-point uniform majorant.
- Then discharge both arguments to obtain the direct theorem `AKLT.W.REC080.main : AKLT.Blueprint.Rec.ResidualTargetBoundStatement`.

## ORCH-SUMMARY

- Delivered a compiled conditional assembly in `AKLT/W/REC080/Main.lean`.
- Exact direct theorem remains open; `main` explicitly takes `ResidualTerminalExpansion` and `ResidualTerminalTail`.
- Both residuals are closed `Prop` definitions with simpler conclusions than the frozen target.
- Build: `lake build AKLT.W.REC080.Main` succeeded.
- Remaining work: prove both residuals and replace the conditional assembly with the requested direct theorem.
