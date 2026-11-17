STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_MOM013/AKLT/W/MOM013/Main.lean`

## Exported declaration

- `AKLT.W.MOM013.main : AKLT.Blueprint.Mom.GreedyAssignmentStatement`

The proof inducts over the first `k` vertices of `Fin n`. At a step it indexes the constraints on the new vertex by its pins and its already assigned neighbours. The number of these factors is at most the total incident degree plus pins, hence at most four by `D.Valid`. The stated local-feasibility hypothesis selects a new label satisfying all those factors. The prefix invariant carries pin positivity and completed-bond positivity forward; `dot_comm` handles bonds and pins in the opposite order.

## Axioms

`#print axioms AKLT.W.MOM013.main`:

```text
'AKLT.W.MOM013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed axioms.

## Build

- `$HOME/.elan/bin/lake build AKLT.W.MOM013.Main` — succeeded; 16.118 seconds wall time (Lake reported the module build itself as 7.1 seconds).
- `$HOME/.elan/bin/lake env lean /tmp/MOM013Axioms.lean` — succeeded; printed the theorem and the axiom list above.

## Open issues

- None. The build emits non-fatal style warnings for local finite-type instances.

## ORCH-SUMMARY

- Delivered the exact theorem `AKLT.W.MOM013.main` in `AKLT/W/MOM013/Main.lean`.
- Proved the closed greedy-assignment statement from its own hypotheses using a prefix induction and the local-feasibility property.
- `lake build AKLT.W.MOM013.Main` succeeded.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- No residual statements, deviations, or open issues.
