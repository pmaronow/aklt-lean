STATUS: PROVED

## Delivered files

- `AKLT/W/REC087/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC087/report.md`

## Exported declaration

`AKLT.W.REC087.main : AKLT.Blueprint.Rec.RenewalSourceStatement`

The proof bounds the source on every integer depth, then inducts over the renewal iterate. At the induction step, each summand is dominated by a nonnegative scalar multiple of the weighted row from `RenewalRows`. The explicit row summability premise supplies summability for the iterate summands and justifies the `tsum` comparison; the row contraction gives the next factor of `ρ`.

## Axioms

`#print axioms AKLT.W.REC087.main`:

```text
'AKLT.W.REC087.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.REC087.Main`

Result: success; 8960 jobs, module build reported 5.8s (12.2s wall time for the command).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC087/Main.lean` with the exact requested theorem name and type.
- `AKLT.W.REC087.main` is proved from the statement's `RenewalRows` and scalar hypotheses.
- Build: `lake build AKLT.W.REC087.Main` succeeded.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No helper files or statement modifications.
- No known open issues or deviations.
