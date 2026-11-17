STATUS: PROVED

## Files

- `AKLT/W/H3M021/Main.lean`

## Exported declaration

- `AKLT.W.H3M021.main : AKLT.Blueprint.H3.LongTrailPrefixStatement`

The proof restricts the full trail's bond injectivity to the first 12 departures. A helper proves that vertices of `takeWord w 12` agree with the corresponding full-word vertices at all times through 12, by reducing the finite sums to the indices below the queried time. The first direction transfers to the prefix, centre avoidance restricts directly, and the full trail's first-hit condition excludes the target at each prefix time since `12 < n`.

## Axioms

Output of `#print axioms AKLT.W.H3M021.main`:

```text
'AKLT.W.H3M021.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M021.Main`
- Result: successful; Lake reported the target built in 6.7 seconds.
- A separate `lake env lean /tmp/CheckMain.lean` check printed the declaration and its axioms successfully.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3M021/Main.lean` with `AKLT.W.H3M021.main` proving the exact frozen statement.
- The required Lake target compiled successfully.
- Exported theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- No helper residual statements, limitations, or deviations remain.
