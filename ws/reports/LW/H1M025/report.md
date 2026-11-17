STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M025/AKLT/W/H1M025/Main.lean)

## Exported declaration

`AKLT.W.H1M025.main : AKLT.Blueprint.H1.PeripheralGeometryStatement`

The proof identifies deleted sites as corners or tips, bounds deleted corner degree from the definition of `reducedSpinSites`, and enumerates the possible bonds at each tip. For degree one, the unique incident bond identifies `leafNeighbour`; its other endpoint is active and cannot be peripheral because distinct peripheral sites are never adjacent. The `π.Covered` premise is unused, so the proof establishes the geometry for arbitrary `PatternData` and either representation.

## Axioms

Output of `#print axioms AKLT.W.H1M025.main`:

```text
'AKLT.W.H1M025.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M025.Main` — succeeded; module compile reported 7.2 s (14.8 s wall time for the command).
- The build emits four non-fatal `unnecessarySeqFocus` tactic-style warnings.
- `lake env lean /tmp/H1M025Axioms.lean` — succeeded; reported the declaration and axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M025/Main.lean` with `AKLT.W.H1M025.main` at the requested type.
- Build command `lake build AKLT.W.H1M025.Main` succeeds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- `π.Covered` is unused; the proof establishes the stated geometry for all patterns.
- Only limitation: four non-fatal tactic-style warnings in the build.
- No orchestrator decision or follow-up is required.
