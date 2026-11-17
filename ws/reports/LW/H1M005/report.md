STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M005/AKLT/W/H1M005/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H1M005/report.md`

## Exported declaration

`AKLT.W.H1M005.main : AKLT.Blueprint.H1.PassageSiteMomentsStatement`

The proof derives first, second, and third coordinate moments from the statement's `MonomialMoments` premise, expands the products, and collects their dot products. It reuses the proved finite-linearity lemma `AKLT.Blueprint.Mom.siteFunctional_sum` from `AKLT.Blueprint.Mom.Assembly`.

## Axioms

`#print axioms AKLT.W.H1M005.main`:

```text
'AKLT.W.H1M005.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M005.Main`
- Result: successful; 8961 jobs, module build reported 8.5 seconds (17.2 seconds wall time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M005.main` with the exact requested type in `AKLT/W/H1M005/Main.lean`.
- Build succeeds with `lake build AKLT.W.H1M005.Main`.
- The proof uses the closed `MonomialMoments` premise and the proved dependency `AKLT.Blueprint.Mom.siteFunctional_sum`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No deviations or open issues.
