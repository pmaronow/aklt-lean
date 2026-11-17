STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C023/AKLT/W/H3C023/Main.lean)

## Exported declaration

`AKLT.W.H3C023.main : CertData.H3.Bridge.DeadMaskLeaf`

The proof establishes the four single-neighbor masks with the packed lane shift lemma. For the fifth mask it represents the four neighbor lanes and their complement with `packFn`, then uses `repeatLane_eq`, `packFn_add`, and `lane_packFn`.

## Axioms

`#print axioms AKLT.W.H3C023.main`:

```text
[propext, Classical.choice, Quot.sound]
```

All are allowed by the brief.

## Build

- `lake build AKLT.W.H3C023.Main` — succeeded, 9.0 seconds wall time (final build).

## Open issues and deviations

The requested first attempt on a different cheaper model was unavailable in this runtime: there is no direct model-switch tool, and the brief forbids sub-agents. After checking tool availability, I completed the proof in the active model. No proof obligation remains open.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C023/Main.lean` with `AKLT.W.H3C023.main : CertData.H3.Bridge.DeadMaskLeaf`.
- The exact requested leaf is proved and the requested Lake build succeeds.
- Axiom output is `[propext, Classical.choice, Quot.sound]`, all allowed.
- No additional helper files or residual statements remain.
- Limitation: the cheaper-model-first instruction could not be followed because direct model switching was unavailable and sub-agents were forbidden.
- No further orchestrator decision is required unless the model-selection deviation needs separate handling.
