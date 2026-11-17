STATUS: PROVED

## Files

- `AKLT/W/H3C040/Main.lean`

## Exported declaration

- `AKLT.W.H3C040.main : CertData.H3.Bridge.RowCoverageLeaf`

The proof establishes generic interval coverage from `intervalCheck` by showing that a successful `intervalEnd` describes adjacent, nonempty intervals, then proves each position in the covered range belongs to exactly one interval. It establishes batch soundness directly from `List.all`. For each phase/window key, arithmetic places it below 14964; interval coverage selects its batch, whose soundness yields the requested `planeCheck`.

## Axioms

`#print axioms AKLT.W.H3C040.main`:

```text
'AKLT.W.H3C040.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All are on the allowed list. No `sorry`, `admit`, `native_decide`, or other forbidden proof escape appears in the delivered file.

## Build

- `lake build AKLT.W.H3C040.Main` — succeeded; 15.3 s total, with the target module reported at 6.0 s.
- `lake env lean /tmp/h3c040_axioms.lean` — succeeded; 7.5 s, printing the axiom list above.

The build replayed imported modules and showed pre-existing lint warnings in `AKLT/Gen/Packed/Routing.lean`; the new module built without warnings.

## Open issues and deviations

No proof issues remain. The requested cheaper-model first attempt was unavailable in this session: there is no direct model-switch tool, and the brief explicitly prohibits sub-agents. The proof was completed in the active model.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C040/Main.lean` and the exact requested theorem.
- `AKLT.W.H3C040.main` proves `CertData.H3.Bridge.RowCoverageLeaf`.
- Proved interval and batch soundness privately from their executable definitions; no certificate-wide normalization was used.
- Build succeeded and the theorem depends only on allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Paper label: `p:stationary-check`.
- Open proof issues: none. The cheaper-model first-attempt instruction could not be followed because no direct model switch is available and the brief prohibits sub-agents.
