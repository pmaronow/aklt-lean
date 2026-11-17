STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M037/AKLT/W/H1M037/Main.lean)

## Exported declaration

- `AKLT.W.H1M037.main : AKLT.Blueprint.H1.WeightLadderTransferStatement`

The proof derives both shifted-weight equations from the commutators. It obtains the norm-square difference from the plus/minus adjoint identity and the raising/lowering commutator, then uses positivity of the squared norm of a nonzero vector to prove the two nonvanishing clauses.

## Axioms

`#print axioms AKLT.W.H1M037.main`:

```text
'AKLT.W.H1M037.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M037.Main`
- Result: successful; module built in 11s, total command time 19.765s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M037/Main.lean` with `AKLT.W.H1M037.main` proving the requested statement.
- The requested Lake build succeeds.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
