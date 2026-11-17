STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_Q028/AKLT/W/Q028/Main.lean`

## Exported declaration

- `AKLT.W.Q028.main : AKLT.Blueprint.Q.PairDiagonalRankStatement`
- Unfolded statement: `Module.finrank ℂ (LinearMap.ker pairDiagonal) = 16`.

The proof identifies the range with the span of the nine explicit degree-eight diagonal monomials. It proves the monomials are linearly independent, gives a preimage for each using a selected pair of source coordinates, and applies rank–nullity to the 25-dimensional source. It does not assign a finite dimension to the full polynomial-ring codomain.

## Axioms

`#print axioms AKLT.W.Q028.main`:

```text
'AKLT.W.Q028.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH=$HOME/.elan/bin:$PATH lake build AKLT.W.Q028.Main`
- Result: success (`Built AKLT.W.Q028.Main`)
- Wall time: 10.88 s total; Lean reported 5.8 s for the module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q028.main` with the exact requested statement in `AKLT/W/Q028/Main.lean`.
- Proved the range is the span of nine independent degree-eight monomials; rank–nullity gives kernel dimension 16.
- `lake build AKLT.W.Q028.Main` succeeded in 10.88 s total.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or deviations.
