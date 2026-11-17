STATUS: PROVED

# H3M020 report

## Delivered files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3M020/AKLT/W/H3M020/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3M020/report.md`

## Exported declaration

`AKLT.W.H3M020.main : AKLT.Blueprint.H3.StationaryFreeEdgeStatement`

The proof handles killed edges by free-coefficient nonnegativity, known-site rows by the `1/5` diagonal lower bound, and ordinary rows by translating the local reward and applying a finite-pair subset comparison after deleting dead neighbours. The local subset argument accounts for lost pairs and for the surviving `beta` to `betaPrime` change.

The proof does not use `Q.Correct` or `d₀ ≠ .east`: the stationary and free coefficients in this frozen statement share the same quotient edge data, and the comparison holds for every arrival direction. These unused hypotheses are not a change to the delivered theorem type.

## Axioms

Output of `#print axioms AKLT.W.H3M020.main`:

```text
'AKLT.W.H3M020.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof escape hatches or residual statements are present.

## Build

- `lake build AKLT.W.H3M020.Main` — success; final invocation 5.2 s wall time.
- Axioms/type inspection with `lake env lean /tmp/H3M020Axioms.lean` — success; 5.08 s.

## Open issues

None.

## ORCH-SUMMARY

- Proved `AKLT.W.H3M020.main` at the exact requested type in `AKLT/W/H3M020/Main.lean`.
- Main comparison follows from translation invariance, dead-neighbor monotonicity, and the known-site diagonal bound.
- Lake target `AKLT.W.H3M020.Main` builds successfully.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No residual statements or limitations remain; `Q.Correct` and `d₀ ≠ .east` are unused by the stronger local proof.
