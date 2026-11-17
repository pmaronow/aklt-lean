STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M051/AKLT/W/H1M051/Main.lean)

## Exported declaration

- `AKLT.W.H1M051.main : AKLT.Blueprint.H1.MomentPauliInterchangeStatement`

The proof expands the local polynomial over its finite monomial support. For each monomial it factors the finite spin sum into exact site moments using the supplied `MonomialMoments` hypothesis, then carries the resulting polynomial identity through inversion and Pauli coefficient extraction.

## Axioms

`#print axioms AKLT.W.H1M051.main`:

```text
'AKLT.W.H1M051.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M051.Main` — succeeded; Lake reported the target built in 16 seconds (`8958/8958`).
- `lake env lean /tmp/print051.lean` — printed the declaration and axioms successfully.

## Open issues

None for the requested theorem.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M051.main` at the exact requested type in `AKLT/W/H1M051/Main.lean`.
- Status: proved; `lake build AKLT.W.H1M051.Main` succeeds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Proof uses the statement's `MonomialMoments` hypothesis and finite monomial expansion.
- No residual statements, deviations, or open proof obligations.
