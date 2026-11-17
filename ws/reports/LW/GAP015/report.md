STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP015/AKLT/W/GAP015/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/GAP015/report.md)

## Exported declaration

`AKLT.W.GAP015.main : AKLT.Blueprint.Gap.VariationalCenteringStatement`

The proof expands the weighted complex square. For constant centers, the weighted residual about `complexMean` sums to zero. For block centers, it groups states by their complement restriction; both the conditional mean and each admissible `h` are constant on these fibres, and the weighted conditional residual sums to zero on each fibre. Positivity supplies nonzero fibre denominators.

## Axioms

`#print axioms AKLT.W.GAP015.main`:

```text
'AKLT.W.GAP015.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP015.Main` — succeeded, 8.8 seconds.
- `lake env lean /tmp/GAP015Axioms.lean` — confirmed the theorem type and axiom list.
- `git diff --check` — clean.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP015/Main.lean` with `AKLT.W.GAP015.main` at the exact requested type.
- Both quantified conclusions are proved independently from the statement hypotheses.
- The requested Lake build succeeds; no tests were added or run.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- No residual statements, deviations, or open issues remain.
