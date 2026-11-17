STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN062/AKLT/W/WIN062/Main.lean)

## Exported declaration

- `AKLT.W.WIN062.main : AKLT.Blueprint.Win.RemovalCostSumStatement`

The proof bounds the seed power by one. For every later enumerated site, it proves the boundary depth finite using that the complement of a finite volume is nonempty. The depth hypothesis then gives `3 ≤ depth.toNat`, so `θ^(depth.toNat - 3) = θ^(-3) * decay θ depth`. Injectivity and image equality for the enumeration bound the later-site sum by the sum over `X`.

## Axioms

`#print axioms AKLT.W.WIN062.main`:

```text
'AKLT.W.WIN062.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN062.Main` — succeeded; Lake reported the module built in 4.4 s (wall time 9.441 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN062.main` with the required closed statement type.
- The proof uses the stated seed bound and converts each nonseed shifted power using depth at least three.
- The enumeration image and injectivity justify enlargement of the nonseed sum to `X`.
- Build succeeded with `lake build AKLT.W.WIN062.Main`.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No helper files, deviations, or open issues.
