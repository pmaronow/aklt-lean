STATUS: PROVED

## Files

- `AKLT/W/H3C041/Main.lean`

## Exported declaration

- `AKLT.W.H3C041.main : CertData.H3.Bridge.EndpointTableSoundLeaf`

The proof reads the final rectangle equality out of `planeCheck`, proves the endpoint rectangle lane calculation using the generic packed-lane lemmas, and transfers equality of table endpoint entries to `EndpointBinding`. It uses the existing `extended_view` theorem to identify the in-box extension with the plane lane. It does not assume the frozen `RectangleLeaf` or `TableBoundsLeaf` propositions as lemmas.

## Axioms

`#print axioms AKLT.W.H3C041.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the allowed axioms.

## Build

- `lake env lean AKLT/W/H3C041/Main.lean -o /tmp/H3C041.olean` — passed, 4.1 s.
- `lake build AKLT.W.H3C041.Main` — passed, 11.5 s overall; the target module compiled in 4.4 s after dependency replay.

The build emitted warnings about the exponentiation threshold and deprecated `if_pos`/`if_neg` simp names; no proof errors remain.

## Open issues and deviations

- The runtime exposed no in-turn model-switch control, so I could not select a different cheaper model for the first attempt. I did not use subagents, as the brief forbids them. The orchestrator should decide whether a cheaper-model rerun is still required.
- No mathematical or Lean proof obligations remain open.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C041/Main.lean` with the exact theorem `AKLT.W.H3C041.main`.
- The target proves `CertData.H3.Bridge.EndpointTableSoundLeaf` from its stated hypotheses.
- Axioms: `[propext, Classical.choice, Quot.sound]` only.
- `lake build AKLT.W.H3C041.Main` passed; target compile time 4.4 s.
- No mathematical or proof issue remains.
- Limitation: no model-switch control was exposed; no subagents were used per brief.
- Orchestrator decision: determine whether to rerun on a different cheaper model.
