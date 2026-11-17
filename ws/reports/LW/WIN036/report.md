STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN036/AKLT/W/WIN036/Main.lean)

## Exported declaration

```lean
theorem AKLT.W.WIN036.main : AKLT.Blueprint.Win.WindowBufferStatement
```

The proof establishes the window depth from an explicit site outside the square, then uses the radial shell gap and sup-distance bounds for tapered sites, neighbours, and raw-boundary sites.

## Axioms

`#print axioms AKLT.W.WIN036.main`:

```text
'AKLT.W.WIN036.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN036.Main` — succeeded, 11.80 seconds wall time (module compilation reported 4.8 seconds).
- The module emits non-fatal linter warnings for some unused simp arguments, two deprecated `if_pos`/`if_neg` rewrites, and unreachable omega tactics.

## Open issues

None. No existing files were changed and no residual statements were introduced.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN036.main` with the exact requested type.
- Build succeeded with allowed axioms `[propext, Classical.choice, Quot.sound]`.
- New Lean file: `AKLT/W/WIN036/Main.lean`; report: `reports/LW/WIN036/report.md`.
- Remaining limitation: non-fatal linter warnings only.
- No orchestrator decision is needed.
