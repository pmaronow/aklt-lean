STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN067/AKLT/W/WIN067/Main.lean)

## Exported declaration

- `AKLT.W.WIN067.main : AKLT.Blueprint.Win.ComponentPinsStatement`

The proof unfolds `componentSum` and `pinnedSum`, then compares their original-leg products. For a retained tail in `G₁`, the original leg cannot end outside `F` by `NoBond`, and cannot end in `F \ B` by its original-leg membership, so its endpoint lies in `B`; both cut pin assignments therefore use the same window configuration `s`. For a retained tail in `G₂`, `NoBond` rules out an endpoint in `B`, so both assignments use the same boundary `η`. A general helper proves pinned sums equal when pins agree on all retained tails.

## Axioms

`#print axioms AKLT.W.WIN067.main`:

```text
'AKLT.W.WIN067.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN067.Main` — succeeded; module compilation took 5.1 s (Lake command completed in 11.9 s).
- A separate `lake env lean /tmp/WIN067Check.lean` axiom check succeeded in 4.5 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN067.main` with the requested exact type in `AKLT/W/WIN067/Main.lean`.
- The proof uses termwise equality of surviving original-leg pin factors.
- The requested Lake build succeeds.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, limitations, or deviations remain.
