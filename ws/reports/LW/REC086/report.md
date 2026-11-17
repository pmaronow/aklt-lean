STATUS: PROVED

# REC086 report

## Files

- `AKLT/W/REC086/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC086/report.md`

## Exported declaration

`AKLT.W.REC086.main : AKLT.Blueprint.Rec.RenewalRemainderStatement`

The proof derives an unweighted summable row from each theta weighted row, using `0 < θ < 1` to show `1 ≤ θ ^ (-(s : ℤ))`. It then proves that the renewal operator sends any nonnegative function bounded by `C * h` to a summable function bounded by `C * ρ * h`. Induction applies this contraction to `renewalIterate`; the initial bound follows from `F ≤ 2` and `hmin h ≤ h X`. The argument is uniform over all integer shifts.

The cited passage, §7 lines 974–981, states exactly this unweighted row estimate and its consequence for arbitrary backward shifts.

## Axioms

Output of `#print axioms AKLT.W.REC086.main`:

```text
'AKLT.W.REC086.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.REC086.Main`

Result: successful, including the target module build in 5.5 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC086.main` with the requested exact statement.
- The proof uses only the frozen `RenewalRows` and boundedness hypotheses.
- The target module builds successfully.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements or deviations remain.
