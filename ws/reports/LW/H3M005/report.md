STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3M005/AKLT/W/H3M005/Main.lean`

## Exported declaration

```lean
AKLT.W.H3M005.main : AKLT.Blueprint.H3.ExposureListExpansionStatement
```

The proof establishes the generic list expansion by induction. Nodup separates the head from the tail, which lets `idxOf` place every tail member after the head; the resulting head passage factor is then distributed across the tail sum.

## Axioms

Output of `#print axioms AKLT.W.H3M005.main`:

```text
'AKLT.W.H3M005.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3M005.Main` — succeeded; final build reported 5.8 seconds.
- The axiom check used `lake env lean` on a temporary import harness and succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3M005/Main.lean` with the requested theorem and exact type.
- The generic list induction proves the closed blueprint statement without additional hypotheses.
- `lake build AKLT.W.H3M005.Main` succeeded (5.8 seconds on final run).
- `main` depends on `[propext, Classical.choice, Quot.sound]`.
- No residual statements, deviations, or open issues.
