STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q052/AKLT/W/Q052/Main.lean)

## Exported declaration

- `AKLT.W.Q052.main : AKLT.Blueprint.Q.PlaneOneSiteEnergyStatement`

The proof expands the one-site conditioning fibre to updates of the selected configuration, cancels the fixed factors in `planeWeight`, and bounds the remaining products by `frameBound^k` and `(2-frameBound)^k`. A tagged incidence set injects internal bonds and boundary legs touching the site into its four-neighbour set, proving `k ≤ 4`. The numerical interaction bounds and proper colouring hypotheses supply the factor bounds and full support.

## Axioms

`#print axioms AKLT.W.Q052.main` reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q052.Main` — succeeded; total build command 11.2 s, module build 4.0 s.

## Open issues

None. The build emits only linter warnings for redundant simp arguments and the local `letI` used to align the conditional-event decidability instance.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q052/Main.lean` with `AKLT.W.Q052.main` at the requested type.
- Proved the full-fibre probability formula by a finite update reindexing.
- Cancelled all factors away from the selected site and bounded its incident plus factors using `interactionBounds`.
- Proved the total incident factor count, including boundary legs, is at most four.
- Build succeeded with axioms `[propext, Classical.choice, Quot.sound]`.
- No residual statements or open issues.
