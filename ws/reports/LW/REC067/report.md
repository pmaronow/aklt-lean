STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC067/AKLT/W/REC067/Main.lean)

## Exported declaration

- `AKLT.W.REC067.main : AKLT.Blueprint.Rec.UnshiftedWitnessStatement`

The proof regroups the weighted coefficients at each length into the H3 row, then exhausts the nonnegative finite cutoff sums in `ENNReal`.

## Axioms

`#print axioms AKLT.W.REC067.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC067.Main` — successful; Lean module build 5.0 s (command wall time 10.7 s).
- Also checked with `lake env lean AKLT/W/REC067/Main.lean` during development.

## Open issues

None. For the fixed unshifted row, the proof uses the finite union of actual response-pair shifts at each length. This suffices for regrouping and avoids needing the stronger uniform geometric estimate `s ≤ n + 1`.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC067.main` with the requested exact type.
- H3 finite rational rows are regrouped into lengthwise ENNReal sums and exhausted by cutoff monotonicity.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Build: `lake build AKLT.W.REC067.Main` succeeded.
- Deviation: finite actual-shift support replaces a uniform geometric shift bound, which is unnecessary at `theta = 1`.
- No open proof obligations remain.
