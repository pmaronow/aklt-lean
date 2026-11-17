STATUS: PROVED

## Files

- `AKLT/W/GAP041/Main.lean`

## Exported declaration

- `AKLT.W.GAP041.main : AKLT.Blueprint.Gap.FrameSpecEnergyStatement`

## Proof summary

For each finite volume `W`, reindex the prescribed and conditioning subsets of the subtype `W` as image finsets in `Plane`. Subtype-value injectivity preserves the prescribed cardinal, and disjointness is preserved by injectivity. Extend each subtype assignment to a total plane assignment by using the default letter outside `W`. The resulting plane-site events agree exactly with the original subtype-coordinate events, so the supplied assignment bound gives `SpecEnergy`.

## Axioms

Output of `#print axioms AKLT.W.GAP041.main`:

```text
'AKLT.W.GAP041.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.GAP041.Main`

Result: successful; module build reported 3.5 seconds.

Axiom check command: `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/GAP041Axioms.lean`

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP041/Main.lean` with the requested theorem and exact type.
- The proof reindexes finite subtype sites into `Plane` and matches the assignment events.
- Build succeeded; axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or deviations.
