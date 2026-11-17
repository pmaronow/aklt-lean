STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3M007/AKLT/W/H3M007/Main.lean)

## Exported declaration

- `AKLT.W.H3M007.main : AKLT.Blueprint.H3.PrefixCoefficientCausalityStatement`

The proof establishes equality of prefix vertices through the current departure, then incoming direction, departure count, revisit and straight flags, dead/live neighbour sets, response pairs, pair coefficients, and `witnessKappa`. These imply equality of the true phase coefficients.

## Axioms

`#print axioms AKLT.W.H3M007.main`:

```text
'AKLT.W.H3M007.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3M007.Main` — succeeded; Lean target reported 7.1 s (command wall time 17.7 s).
- A separate `lake env lean /tmp/H3M007Axioms.lean` audit — succeeded; command wall time 7.8 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M007.main` with the requested statement.
- Source: `AKLT/W/H3M007/Main.lean`.
- Build command succeeded: `lake build AKLT.W.H3M007.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements or deviations.
- No open issues; no orchestrator decision is needed.
