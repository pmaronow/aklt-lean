STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_MOM016/AKLT/W/MOM016/Main.lean)

## Exported declaration

- `AKLT.W.MOM016.main : AKLT.Blueprint.Mom.TwoSiteFactorizationStatement`

The proof partitions site and pin products into the two selected sites and their exterior, and partitions bonds into those incident to each selected site and those wholly exterior. The two no-bond hypotheses and `D.Valid` ensure the incident groups are disjoint and every exterior spin is fixed on the fibre. The factors are defined as direct products, so the proof also covers zero site masses without division. Nonnegativity follows from the explicit site weights, the unit norm of the icosahedral vectors, and the squared-norm proof of the unit-ball dot-product bound.

## Axioms

`#print axioms AKLT.W.MOM016.main`:

```text
'AKLT.W.MOM016.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.MOM016.Main` — succeeded; 13.6 seconds wall time, target module built in 8.5 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/MOM016/Main.lean` with the required theorem and type.
- Status: proved and Lake build succeeded.
- Exported theorem uses only the allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements or known limitations.
