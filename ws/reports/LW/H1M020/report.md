STATUS: PROVED

## Files

- `AKLT/W/H1M020/Main.lean`

## Exported declaration

`AKLT.W.H1M020.main : AKLT.Blueprint.H1.InversionPolynomialStatement`

The proof shows that each substituted monomial retains its exponent, so the transformed support is a subset of the original support. This transfers vector affineness and support. For evaluation, it composes the sign substitution with evaluation at the inverted vectors; the two signs cancel for every coordinate, regardless of whether the token lies in `J`.

## Axioms

Output of `#print axioms AKLT.W.H1M020.main`:

```text
'AKLT.W.H1M020.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1M020.Main` — successful; Lean module build reported 5.6 s (11.9 s command wall time).
- Axiom audit with `lake env lean /tmp/H1M020Axioms.lean` — successful; 5.3 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M020.main` with the exact requested type in `AKLT/W/H1M020/Main.lean`.
- `lake build AKLT.W.H1M020.Main` succeeds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements or deviations.
- No open issues; orchestrator action: none.
