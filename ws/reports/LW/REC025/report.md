STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC025/AKLT/W/REC025/Main.lean) — new proof module with private integral and pointwise comparison helpers.

## Exported declaration

`AKLT.W.REC025.main : AKLT.Blueprint.Rec.LogCoefficientMonoYStatement`

The proof derives the reciprocal logarithmic mean integral formula directly from the frozen definition, including the diagonal case. It then compares the two integrands pointwise on `[0,1]`: the affine denominators are positive, the first denominator is at most the second since `c ≤ 1`, and the resulting product inequality gives the required sign. Integrating yields the statement.

## Axioms

Output of `#print axioms AKLT.W.REC025.main`:

```text
'AKLT.W.REC025.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC025.Main`
- Result: success; Lake reported the module built in 12 seconds (23.2 seconds wall time for the command).

## Open issues

None. The exact requested theorem name and type are proved. No existing source files were changed.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC025.main` proving `AKLT.Blueprint.Rec.LogCoefficientMonoYStatement`.
- New file: `AKLT/W/REC025/Main.lean`.
- Build: `lake build AKLT.W.REC025.Main` succeeded.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- No open issues or deviations.
