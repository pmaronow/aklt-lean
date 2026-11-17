STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC074/AKLT/W/REC074/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/REC074/report.md`

## Exported declaration

`AKLT.W.REC074.main : AKLT.Blueprint.Rec.EnvelopeOrderStatement`

The proof unfolds the envelope definition. For negative integers it reduces `d.toNat` to zero. For monotonicity, it proves each defining class bounded above by 2: spin support vectors are in the unit ball, every bond and pin factor is nonnegative, and finite normalized expectations of a scalar product have absolute value at most 1. The class for the larger threshold is then a subset of the class for the smaller threshold, so the conditional supremum is antitone.

## Axioms

`#print axioms AKLT.W.REC074.main`:

```text
'AKLT.W.REC074.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof placeholders or unsafe declarations occur in the delivered file.

## Build and audit

- `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.REC074.Main` — passed; command completed in about 17 seconds (Lean module compilation: 11 seconds).
- `lake env lean /tmp/REC074Audit.lean` with `#print axioms AKLT.W.REC074.main` — passed; 5 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/REC074/Main.lean`.
- `AKLT.W.REC074.main` proves `AKLT.Blueprint.Rec.EnvelopeOrderStatement`.
- Build passed; axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations; no open issues.
