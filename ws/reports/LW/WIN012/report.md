STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN012/AKLT/W/WIN012/Main.lean)

## Exported declaration

- `AKLT.W.WIN012.main : AKLT.Blueprint.Win.BoundaryMembershipStatement`
- Unfolded statement: for every finite `U` and `z`, `z ∈ rawBoundary U` iff `z ∉ U` and `setDistance supDist z (↑U : Set Plane) = 1`.

## Axioms

`#print axioms AKLT.W.WIN012.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the allowed axioms. The proof handles `U = ∅` through the infimum definition, whose empty infimum is `⊤`.

## Build

- Command: `lake build AKLT.W.WIN012.Main`
- Result: success
- Target compilation: 5.4 s; full build command: 12.35 s

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN012.main` with the exact requested type.
- Added only `AKLT/W/WIN012/Main.lean` in the worktree and this report.
- Build succeeded; exported theorem axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- Empty `U` is included in the proof.
- No deviations or open issues.
