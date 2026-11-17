STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C022/AKLT/W/H3C022/Main.lean)
- `/home/ubuntu/aklt/reports/LW/H3C022/report.md`

## Exported declaration

`AKLT.W.H3C022.main : CertData.H3.Bridge.KnownMaskLeaf`

The proof reduces `knownMask` to one or two packed single-site masks. It proves their lane values and uses `AKLT.Gen.Packed.lane_add` for the no-carry sum. The grid coordinates identify the two sites as indices 9799 and 9800, 9658, or 9798 when `d₀` is north, west, or south.

## Axioms

`#print axioms main`:

```text
'AKLT.W.H3C022.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are within the allowed axiom set. The proof does not use `native_decide`.

## Build

- Command: `lake build AKLT.W.H3C022.Main`
- Result: exit 0; 9.83 seconds wall time, with the target Lean module compiled in 4.0 seconds.

## Open issues and deviations

- No proof issues remain.
- The brief requested a first attempt with a different, cheaper model and also prohibited subagents. This runtime exposed no model-switch mechanism, so a separate cheaper-model attempt was unavailable; no subagents were used.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C022.main : CertData.H3.Bridge.KnownMaskLeaf` in `AKLT/W/H3C022/Main.lean`.
- Build command `lake build AKLT.W.H3C022.Main` succeeded.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Open issues: none.
- Deviation: no separate cheaper-model attempt was possible in this runtime; no subagents were used, per brief.
- Orchestrator action: none required.
