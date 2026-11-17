STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC035/AKLT/W/REC035/Main.lean)
- `/home/ubuntu/aklt/reports/LW/REC035/report.md`

## Exported declaration

`AKLT.W.REC035.main : AKLT.Blueprint.Rec.BetaAnalyticStatement`

The proof sets `s = (116 / 125) * c`, obtains `s ≤ It` and `1 ≤ I₀` from the hypotheses, and proves `logarithmicMean s 1 ≤ logarithmicMean It I₀`. The comparison follows by expressing the logarithmic mean as a secant slope of `exp` and applying convexity, with the diagonal case handled separately. Positivity then permits inversion and division by three.

## Axioms

`#print axioms AKLT.W.REC035.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/REC035/Main.lean` — passed (about 7.6 s).
- `lake build AKLT.W.REC035.Main` — passed (10.4 s, 8955 jobs).

## Open issues

None. The build reports only deprecated `if_neg` simp-lemma warnings; they do not affect compilation or the proof.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC035/Main.lean` with the requested theorem name and type.
- The target is proved from its own hypotheses; no residual statements or additional assumptions were introduced.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build AKLT.W.REC035.Main` passes.
- Open issues: none.
- No deviations from the requested namespace, file location, or report format.
