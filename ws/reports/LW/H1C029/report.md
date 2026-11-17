STATUS: PROVED

## Files

- `AKLT/W/H1C029/Main.lean`

## Exported declaration

`AKLT.W.H1C029.main : AKLT.Cert.H1.Production.Leaves.representativeWitnessLookup`

The proof unfolds `representativeWitnessLookup` and inducts on the representative list. For the head, it extracts all three facts from `RepresentativesAccepted`; for a tail member, it applies the induction hypothesis to the accepted tail.

## Axioms

Output of `#print axioms AKLT.W.H1C029.main`:

```text
'AKLT.W.H1C029.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms.

## Build

Command: `lake build AKLT.W.H1C029.Main`

Result: successful; target module built in 5.7 s, command elapsed time 12.06 s (including Lake replay/startup).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C029/Main.lean` with the requested theorem name and type.
- `representativeWitnessLookup` is proved by structural induction over `RepresentativesAccepted`.
- Build: `lake build AKLT.W.H1C029.Main` succeeded.
- Axioms: `[propext, Classical.choice, Quot.sound]` only.
- No open issues or deviations.
