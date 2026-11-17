STATUS: PROVED

## Files

- `AKLT/W/WIN071/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN071/report.md`

## Exported declaration

`AKLT.W.WIN071.main : AKLT.Blueprint.Win.OverlapMinorizationStatement`

The proof bounds each `|p s - q s|` by `p s + q s - 2 * (p₀ * ν s)`, using the common lower bounds. Summing and applying the three probability normalization equations gives the total variation bound.

## Axioms

`#print axioms AKLT.W.WIN071.main`:

```text
'AKLT.W.WIN071.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed Lean axioms.

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.WIN071.Main`
- Result: success; final replay build completed in 4.72 seconds wall time (`/usr/bin/time -p`; Lake reports the cached target replayed).
- Also checked with `lake env lean AKLT/W/WIN071/Main.lean`; elaboration succeeded and printed the axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem at the exact name and type in `AKLT/W/WIN071/Main.lean`.
- The overlap estimate follows from pointwise minorization, finite summation, and probability normalization.
- The requested Lake build succeeds.
- Exported theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No open proof obligations or deviations.
