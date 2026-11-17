STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M008/AKLT/W/H1M008/Main.lean)

## Exported declaration

- `AKLT.W.H1M008.main : AKLT.Blueprint.H1.PassageNextLowerBoundStatement`

The proof bounds every spin vector by squared norm `≤ 1`, using the supplied
icosahedron atom norms and the zero atom. A coordinatewise square inequality
gives `-1 ≤ dot a b` for any two such vectors. This makes every bond and pin
factor nonnegative, while all spin weights are nonnegative. The passage factor
is at least `4/5`; multiplying this pointwise inequality by the common
nonnegative factors and summing proves the claim.

## Axioms

`#print axioms AKLT.W.H1M008.main`:

```text
'AKLT.W.H1M008.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/H1M008/Main.lean` — passed in 4.3 s.
- `lake build AKLT.W.H1M008.Main` — passed; Lake reported 3.0 s for the module (8.9 s command wall time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered the proof at `AKLT/W/H1M008/Main.lean` with the exact required name and type.
- Proved the lower bound from unit atom norms, nonnegative spin weights, bond factors, and pin factors.
- Build passed; exported theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
