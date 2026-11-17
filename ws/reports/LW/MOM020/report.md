STATUS: PROVED

## Files

- `AKLT/W/MOM020/Main.lean`
- `/home/ubuntu/aklt/reports/LW/MOM020/report.md`

## Exported declaration

`AKLT.W.MOM020.main : AKLT.Blueprint.Mom.TripleGeometryStatement`

The proof expands the squared norm of the sum of the three vectors to obtain
the lower bound on `1 + tripleP a / 3`. For each pair, nonnegativity of the
squared norms of the sum and difference gives both scalar product bounds,
which imply the three nonnegative deficits.

## Axioms

Output of `#print axioms AKLT.W.MOM020.main`:

```text
'AKLT.W.MOM020.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.MOM020.Main`

Result: successful. The latest invocation took 17.6 seconds wall time; Lake
reported 7.0 seconds for the module build.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact theorem `AKLT.W.MOM020.main` with the requested type.
- Proof uses the unit hypotheses and direct sums-of-squares arguments.
- Build succeeded with `lake build AKLT.W.MOM020.Main`.
- Axiom output is `[propext, Classical.choice, Quot.sound]`.
- No open issues or deviations.
