STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C030/AKLT/W/H3C030/Main.lean)

## Exported declarations

- `AKLT.W.H3C030.suffixWord`: the remaining compass word at a processed offset.
- `AKLT.W.H3C030.usedBonds`: the bonds used by the processed prefix, in replay order.
- `AKLT.W.H3C030.WalkPrefix`: relates replay depth, position, and used bonds to the corresponding word prefix.
- `AKLT.W.H3C030.wordVertex_succ`: one-step recurrence for `wordVertex`.
- `AKLT.W.H3C030.usedBonds_succ`: one-step recurrence for the used-bond list.
- `AKLT.W.H3C030.transition_walk`: the walk component of `transition` is `Walk.step`.
- `AKLT.W.H3C030.walkPrefix_transition`: extending the walk preserves the prefix invariant.
- `AKLT.W.H3C030.walkPrefix_initial`: the initial walk represents the empty prefix.
- `AKLT.W.H3C030.bond_finset_eq`: equal canonical production bonds give equal unordered endpoint sets.
- `AKLT.W.H3C030.freshBond`: trail injectivity makes the next bond absent from the used prefix.
- `AKLT.W.H3C030.walkLegal`: each next direction passes the walk's used-bond legality check.
- `AKLT.W.H3C030.directionCode_direction`: decoding a code below four and re-encoding it recovers that code.
- `AKLT.W.H3C030.ReplayTrace`: recursive local conditions for successful prefix replay.
- `AKLT.W.H3C030.replayTrace_from_prefix`: a valid trail prefix satisfies `ReplayTrace` from any matching prefix walk.
- `AKLT.W.H3C030.replayPrefix_of_trace`: `ReplayTrace E X d₀ n c s → (replayPrefix E X d₀ n c s).isSome = true`.
- `AKLT.W.H3C030.main : CertData.H3.Bridge.PrefixReplayCompleteLeaf`.

The proof establishes the replay walk invariant directly from `SurvivingPrefix`: distinct bonds imply every next bond is fresh, while the vertex exclusions prevent center and target hits. The decoder's head/tail equations align the recursive parser with the word. The suggested `CodeEncodeLeaf` and `PrefixReplaySoundLeaf` were not needed, and no certificate-wide normalization or `native_decide` was used.

## Axioms

`#print axioms AKLT.W.H3C030.replayPrefix_of_trace` and `#print axioms AKLT.W.H3C030.main` both report:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/H3C030/Main.lean` — passed (about 6 seconds).
- `lake build AKLT.W.H3C030.Main` — passed (Lake reported 4.5 seconds for the module; full command about 11 seconds).

## Open issues

None for the statement. The requested first attempt with a different cheaper model could not be made because this session does not expose model switching; the leaf brief also prohibited delegation.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C030.main` with the exact requested type.
- Build passed for `AKLT.W.H3C030.Main`; exported theorem axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- Proof uses a prefix walk invariant and derives fresh-bond legality from `IsTrail` injectivity.
- `CodeEncodeLeaf` and `PrefixReplaySoundLeaf` were unnecessary for this proof route.
- Deviation: the requested cheaper-model first attempt was unavailable in-session; no delegation was used.
- No open theorem or decision remains for the orchestrator.
