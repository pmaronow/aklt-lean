STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN069/AKLT/W/WIN069/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/WIN069/report.md`

## Exported declaration

`AKLT.W.WIN069.main : AKLT.Blueprint.Win.WindowRewriteStatement`

The proof fixes assignments `η₀` and `s₀`, factors the pinned partition sum on `G₁` and `G₂`, and uses the invariance hypothesis to isolate the two component sums. The free partition sums and the exterior component contribute a positive scalar depending only on `η`; normalization removes it. The helper `reconstruct_removed_sum` expands `cutError` using logarithms of positive partition ratios.

## Axioms

`#print axioms AKLT.W.WIN069.main`:

```text
[propext, Classical.choice, Quot.sound]
```

No residual propositions or unproved assumptions are used.

## Build

Command: `lake build AKLT.W.WIN069.Main`

Result: successful; Lake reported the target built in 4.7 seconds (10.0 seconds total command time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN069.main` at the requested exact type in `AKLT/W/WIN069/Main.lean`.
- Build passed with `lake build AKLT.W.WIN069.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, limitations, or deviations.
