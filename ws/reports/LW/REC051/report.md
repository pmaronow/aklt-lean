STATUS: PROVED

## Delivered

- Source: `AKLT/W/REC051/Main.lean`
- Exported declaration: `AKLT.W.REC051.main`
- Statement: `AKLT.Blueprint.Rec.RemovedClosureStatement`

The proof establishes a prefix invariant for the auxiliary trace: all nonlive U sites retain their full kept sets, all nonlive D sites retain two kept flags, and mutual kept consistency is preserved. It handles the normalized initial endpoint and each trace transition, then shows removing an unprotected live endpoint gives an ordinary consistent network.

## Axiom audit

`#print axioms AKLT.W.REC051.main`:

```text
'AKLT.W.REC051.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms. The delivered source contains no forbidden proof escapes or effectful commands.

## Build

- `lake env lean AKLT/W/REC051/Main.lean` — succeeded.
- `lake build AKLT.W.REC051.Main` — succeeded, 21.3 s wall time; Lake reported 10 s for the module build.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC051/Main.lean` with `AKLT.W.REC051.main : AKLT.Blueprint.Rec.RemovedClosureStatement`.
- Status: PROVED; the requested Lake build succeeds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No helper source files, deviations, or open proof obligations.
- Report: `/home/ubuntu/aklt/reports/LW/REC051/report.md`.
