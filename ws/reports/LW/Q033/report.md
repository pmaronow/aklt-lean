STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q033/AKLT/W/Q033/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/Q033/report.md)

## Exported declaration

`AKLT.W.Q033.main : AKLT.Blueprint.Q.CentreDegreeCancellationStatement`

The proof converts each support-degree hypothesis to weighted homogeneity using `siteWeight_degree`. It then applies the proved library theorem `AKLT.Uniq.homogeneous_quotient` with the explicit premise `p ≠ 0` to conclude that `χ` is weighted homogeneous of degree zero at `x`. Since the site weight is the sum of the exponents of the two variables at `x`, both exponents vanish for every supported monomial. This establishes `independentAt x χ`, including when `χ = 0`.

## Axioms

`#print axioms AKLT.W.Q033.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.Q033.Main`

Result: successful, 11.46 seconds wall time (module compile reported 5.0 seconds); Lake reported 8958 targets built or checked.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q033/Main.lean` with the exact requested theorem name and type.
- Proved using the existing `AKLT.Uniq.homogeneous_quotient` result, so status is PROVED FROM DEPS.
- Build succeeded; exported theorem axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No deviations or open issues.
