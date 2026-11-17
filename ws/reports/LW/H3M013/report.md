STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3M013/AKLT/W/H3M013/Main.lean)

## Exported declaration

`AKLT.W.H3M013.main : AKLT.Blueprint.H3.KnownSiteMemoryStatement`

The proof recovers the first two departures from `SurvivingPrefix`. For a suffix window at index `i`, it rewrites the remembered directions as the original slice `i−10,...,i−1`. A remembered departure from either known site then supplies an index at least 2 and below `i`; together with the initial departure and the current departure, this gives three distinct departures at that site, contradicting the assumed budget of two. Bond injectivity separately rules out the time-zero bond at index `i`.

## Axioms

Output of `#print axioms AKLT.W.H3M013.main`:

```text
'AKLT.W.H3M013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M013.Main`
- Result: successful; module build reported 5.6 seconds.
- A separate `lake env lean --stdin` declaration and axiom check succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/H3M013/Main.lean`.
- Status: proved; `lake build AKLT.W.H3M013.Main` succeeds.
- Exported type: `AKLT.Blueprint.H3.KnownSiteMemoryStatement`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements or deviations.
- No open issues for the orchestrator.
