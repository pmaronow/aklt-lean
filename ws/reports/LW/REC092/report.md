STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC092/AKLT/W/REC092/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/REC092/report.md)

## Exported declaration

`AKLT.W.REC092.main : AKLT.Blueprint.Rec.LegacyCoverComparisonStatementV2`.

The proof reuses the legacy pattern. At non-tip sites it transfers both kept
flags through the legacy equality intersected with `G`, and uses the auxiliary
rule that sites outside `G` are removed. It identifies template bonds in
either orientation because `PatternData.InternalPresent` is symmetric. At a
tip, it transfers the kept flag at the non-tip endpoint and uses the cover's
tip status, proving the required actual-to-cover implication.

## Axioms

Output of `#print axioms AKLT.W.REC092.main`:

```text
'AKLT.W.REC092.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH=/home/ubuntu/.elan/bin:$PATH lake build AKLT.W.REC092.Main` — successful; Lake reported the module build in 5.9 s (12.2 s command wall time).
- `PATH=/home/ubuntu/.elan/bin:$PATH lake env lean /tmp/rec092_axioms.lean` — successful; 4.9 s.

No existing project files were changed. The new Lean file contains no
`sorry`, `admit`, or added axioms. Open issues: none.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC092.main` with the exact requested type in `AKLT/W/REC092/Main.lean`.
- Proved from the frozen legacy matcher and `D.Auxiliary` hypotheses.
- Build: `lake build AKLT.W.REC092.Main` succeeded.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- No residual declarations, limitations, or deviations; no orchestrator decision needed.
