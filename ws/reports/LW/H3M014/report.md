STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3M014/AKLT/W/H3M014/Main.lean`

## Exported declaration

- `AKLT.W.H3M014.main : AKLT.Blueprint.H3.TrueRewardIdentityStatement`

The proof derives the successor-vertex formula, identifies the two live-other-neighbour sets elementwise after removing `trueDeadSet`, matches the powersetCard and coefficient branches, and proves nonreversal from the initial trail condition or injectivity of adjacent bonds.

## Axioms

`#print axioms AKLT.W.H3M014.main`:

```text
'AKLT.W.H3M014.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M014.Main`
- Result: success
- Reported target time: 6.7s
- Axiom check command: `lake env lean /tmp/H3M014_axioms.lean` (7.5s; temporary check file imports the delivered module)

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3M014/Main.lean` with the exact requested theorem and type.
- Status: proved; target build succeeded.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, limitations, or deviations.
