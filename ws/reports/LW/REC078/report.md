STATUS: PROVED

## Files

- `AKLT/W/REC078/Main.lean`

## Exported declaration

- `AKLT.W.REC078.main : AKLT.Blueprint.Rec.PairEnvelopeShiftStatement`

The proof obtains both shifted endpoint-depth bounds from the lattice triangle inequality. It then places the original ordinary response pair directly in the defining set of `responseEnvelope`. To justify taking that supremum, it proves a uniform bound of 2 on response values from nonnegative finite partition weights and the unit-ball bound for spin vectors and pins.

## Axioms

`#print axioms AKLT.W.REC078.main`:

```text
'AKLT.W.REC078.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC078.Main` — succeeded; Lake reported 17 seconds for the module build (22.7 seconds command wall time).
- The build emitted only deprecation warnings for `if_pos`/`if_neg` simplification lemmas.
- Forbidden proof constructs scan: no matches in `AKLT/W/REC078`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC078/Main.lean` with the exact requested theorem name and type.
- The theorem compiles and depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, open issues, or proof limitations remain.
- The proof uses direct envelope membership for the given `ResponsePair`; the suggested trail realization and isometry steps are unnecessary for this frozen statement.
- No orchestrator decision or follow-up is needed.
