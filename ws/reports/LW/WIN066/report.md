STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN066/AKLT/W/WIN066/Main.lean)

## Exported declaration

- `AKLT.W.WIN066.main : AKLT.Blueprint.Win.OriginalFactorizationStatement`

The proof splits configurations over the disjoint partition, factors the site and internal bond weights, and splits the original-leg pin product by piece while retaining the original volume's leg indexing. The free sum uses the same configuration and bond factorization without pin factors.

## Axioms

`#print axioms AKLT.W.WIN066.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN066.Main` — passed, 3.9 s for the module (Lake reported 8955/8955 jobs).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN066/Main.lean` with the requested theorem and exact type.
- Proved `AKLT.Blueprint.Win.OriginalFactorizationStatement` from the hypotheses of `SeparatingCut`.
- Pin products preserve `originalLegs (F \ B)` and are split by the retained tail's component.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- Build passed with `lake build AKLT.W.WIN066.Main`.
- No residual statements, open issues, or deviations.
