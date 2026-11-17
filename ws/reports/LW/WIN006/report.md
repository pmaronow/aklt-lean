STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN006/AKLT/W/WIN006/Main.lean)

## Exported declaration

- `AKLT.W.WIN006.main : AKLT.Blueprint.Win.SideCornerWitnessStatement`

## Axioms

`#print axioms AKLT.W.WIN006.main`:

```text
'AKLT.W.WIN006.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN006.Main`
- Result: successful; Lake reported the module built in 10s.
- Command wall time: 15.72s (`real`), 18.23s (`user`), 2.29s (`sys`).

## Open issues

None. The proof uses the paper's side normalization argument, with the four exterior sides handled explicitly. No existing files were modified.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN006.main` at the required statement and path.
- The requested Lake build succeeds.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- No residual statements, deviations, or open issues.
