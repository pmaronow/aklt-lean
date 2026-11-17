STATUS: PROVED

## Files

- `AKLT/W/H1M026/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M026/report.md`

## Exported declarations

- `AKLT.W.H1M026.main : AKLT.Blueprint.H1.PeripheralFubiniStatement`
- `AKLT.W.H1M026.patternFunctional_eq_separated` proves the intermediate equality between the original pattern functional and the separated leaf functional.

The proof partitions active spins into retained and deleted sites, reindexes the finite sum over spin assignments through the corresponding product equivalence, factors the slot and bond terms, and sums each deleted spin locally to obtain `integratedLeafFactor`.

## Axiom audit

`#print axioms AKLT.W.H1M026.main`:

```text
'AKLT.W.H1M026.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M026.Main` — succeeded (`Build completed successfully (8956 jobs).`); final replay took 4.8 seconds.
- A separate `lake env lean --stdin` import and `#print axioms` audit succeeded.

## Open issues

No proof gaps or residual statements. Lean reports non-fatal linter warnings for unused simp arguments/binders and deprecated `if_pos`/`if_neg` names.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M026.main` with the required type in `AKLT/W/H1M026/Main.lean`.
- Proved the finite reindexing and deleted-site factorization from the statement's hypotheses.
- The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Build succeeded; only non-fatal linter warnings remain.
- No residual declarations or orchestrator decisions are needed.
