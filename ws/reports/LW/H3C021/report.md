STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C021/AKLT/W/H3C021/Main.lean)

## Exported declaration

`AKLT.W.H3C021.main : CertData.H3.Bridge.OrdinaryMaskLeaf`

The proof factors the packed mask into four successive lane removals. A generic subtraction lemma establishes that removing a full lane clears only that lane; the all-ones mask is handled by power/division identities. The five admitted cases supply distinct in-range site indices, and the grid/site-index correspondence identifies the four zeroed lanes.

## Axioms

Output of `#print axioms AKLT.W.H3C021.main`:

```text
'AKLT.W.H3C021.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms.

## Build

Command: `lake build AKLT.W.H3C021.Main`

Result: success. Lake reported the target module built in 29 seconds; the full command, including project replay, took 43.7 seconds wall time (`time` output).

## Open issues and deviations

- The brief required the first attempt to use a different cheaper model and also prohibited sub-agents. This runtime exposes no way to switch the current model; I therefore did not delegate and completed the proof in the active model. An initial finite checker attempt was discarded in favor of the structural proof above.
- `maxRecDepth` is raised to 100000 locally to elaborate the power/mask arithmetic proof.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C021/Main.lean` with `AKLT.W.H3C021.main` proving the exact `OrdinaryMaskLeaf` statement.
- Build succeeded: `lake build AKLT.W.H3C021.Main` (29s target; 43.7s full command).
- Axioms are `[propext, Classical.choice, Quot.sound]` only.
- The mask identity is proved structurally through four distinct full-lane subtractions and grid/site-index correspondence.
- Deviation: no self-model switch was available for the requested cheaper-model first attempt; no sub-agents were used because the brief forbids them.
- Local `maxRecDepth` is 100000; no other limitation or open proof obligation remains.
