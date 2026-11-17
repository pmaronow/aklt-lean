STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP024/AKLT/W/GAP024/Main.lean)

## Exported declaration

- `AKLT.W.GAP024.main : AKLT.Blueprint.Gap.BlockAverageFormStatement`

The proof derives the conditional-kernel identities from finite equivalence classes, then averages their row normalization and detailed balance over labels. The quadratic form is the sum of the labelled block forms, with repeated labels counted and the rate-one normalization preserved.

## Axioms

`#print axioms AKLT.W.GAP024.main`:

```text
'AKLT.W.GAP024.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/GAP024/Main.lean` — passed.
- `lake build AKLT.W.GAP024.Main` — passed; 11.6 seconds wall time, with the module reported built in 6.7 seconds.
- `git diff --check -- AKLT/W/GAP024/Main.lean` — passed.

Lean emitted linter and deprecation warnings; there were no build errors.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP024.main` with the exact requested type in `AKLT/W/GAP024/Main.lean`.
- Proved block reversibility and the labelled block-form identity from finite conditional kernels.
- Build passed; `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`.
- No helper files or other source files were retained.
- No open theorem names, deviations, or decisions remain for the orchestrator.
