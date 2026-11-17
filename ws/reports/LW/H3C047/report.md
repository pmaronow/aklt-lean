STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C047/AKLT/W/H3C047/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3C047/report.md`

## Exported declaration

`AKLT.W.H3C047.main : CertData.H3.Bridge.SpanDataLeaf`

Expanded target: for every `PackedGraph`, `SpanRepresents P.toGraph` holds. The proof uses `lane_truncate` and `lane_shiftRight` from `AKLT.Gen.Packed`, and arithmetic to show each queried index remains inside its 4096-entry block. It does not use receipts or import generated data directly.

## Axioms

`#print axioms AKLT.W.H3C047.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are permitted axioms. No residual propositions or unproved assumptions remain.

## Build

- `lake build AKLT.W.H3C047.Main` — succeeded; command wall time 16.5 s (the module itself built in 6.5 s).

## Open issues and limitations

The requested first attempt with a different cheaper model could not be performed: this session has no model-switch facility, and the task workflow prohibits sub-agents. The proof was completed with the available model. There are no mathematical open issues.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C047/Main.lean` with the exact theorem `AKLT.W.H3C047.main : CertData.H3.Bridge.SpanDataLeaf`.
- The universal packed-graph span obligation is proved structurally from the generic packed lane lemmas.
- `lake build AKLT.W.H3C047.Main` succeeded.
- The theorem's axioms are `[propext, Classical.choice, Quot.sound]`.
- Limitation: the cheaper-model first-attempt constraint could not be met in this session; no model-switch tool was available, and sub-agents are prohibited.
- No mathematical open items; orchestrator can accept the proof and note that process deviation.
