STATUS: PROVED

## Files

- `AKLT/W/H3C005/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C005/report.md`

## Exported declaration

`AKLT.W.H3C005.main : CertData.H3.Bridge.RawReplaySoundLeaf`

The proof inducts over `replayRaw`, establishes a trace invariant for depth, position, incoming direction, and the reversed departure and bond histories, and carries `List.Nodup` of the used bonds from each successful legality check. It derives `RawWindow` from that nodup history. A base‑4 identity proves the decode/encode direction used by `WalkRepresents`; the local `codeDecodeLeaf` supplies that closed leaf. `CodeEncodeLeaf` is not needed by this target.

## Axioms

`#print axioms AKLT.W.H3C005.main`:

```text
'AKLT.W.H3C005.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms.

## Build

Command: `lake build AKLT.W.H3C005.Main`

Result: succeeded. Final measured command time was 8.9 seconds wall time; Lake reported the target module built in 4.2 seconds. The theorem was also checked with `lake env lean AKLT/W/H3C005/Main.lean`.

## Open issues and deviations

The requested first attempt with a different cheaper model could not be made: this environment provides no model-switch tool, and the campaign instructions prohibit spawning sub-agents. The proof itself is complete. The opposite code round-trip leaf `CodeEncodeLeaf` is not used because the exact statement only needs `encodeWord (decodeWord n c)`.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C005/Main.lean`; exported `AKLT.W.H3C005.main` proves the exact frozen leaf.
- Local decode/encode identity and replay trace lemmas prove the result structurally; no certificate-wide normalization or forbidden proof escape was used.
- Build succeeded with `lake build AKLT.W.H3C005.Main` (8.9 s wall, 4.2 s target).
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`, all permitted.
- `CodeEncodeLeaf` was unnecessary for this target.
- Deviation: no cheaper-model first attempt was available through the exposed tools; sub-agent use is prohibited.
- No residual statements or open proof obligations remain.
