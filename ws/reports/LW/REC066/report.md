STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_REC066/AKLT/W/REC066/Main.lean`

## Exported declaration

- `AKLT.W.REC066.main : AKLT.Blueprint.Rec.MajorantFiniteStatement`

The proof factors the majorant as a constant multiple of `n * r^n`, where
`r = q / Real.sqrt θ`. From `0 < q` and `q^2 < θ`, it obtains `0 ≤ r < 1`,
uses Mathlib's summability theorem for `n * r^n`, and transfers the resulting
real summability to the ENNReal tsum with `ENNReal.ofReal_tsum_of_nonneg`.
The `OpenTrailBound` data and `θ ≤ 1` are accepted as stated; the argument only
needs `CV ≥ 1`, `0 < q`, and `q^2 < θ`.

## Axioms

`#print axioms AKLT.W.REC066.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC066.Main`
- Result: successful, module build reported 5.8 s; command wall time 12.076 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC066.main` with the requested exact type.
- The theorem compiles in `AKLT/W/REC066/Main.lean`.
- The proof establishes geometric summability with `r = q / sqrt(θ) < 1` and lifts it to ENNReal.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- Build command: `lake build AKLT.W.REC066.Main` (successful).
- No residual statements, deviations, or open issues.
