STATUS: PROVED

## Delivered files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C023/AKLT/W/H1C023/Main.lean)

## Exported declaration

- `AKLT.W.H1C023.main : AKLT.Cert.H1.Production.Leaves.directRowsEntry`

The proof unfolds `matrix` and `directSectorRows`, obtains explicit list bounds for both `Fin n` indices from `indices.length = n`, and applies `List.getD_map` to the row and column maps. The bounds justify replacing the out-of-range defaults with the actual in-range elements. This proves the data-decoding statement directly; it does not require the paper's positivity argument at `l:integercheck`.

## Axioms

`#print axioms AKLT.W.H1C023.main` reports:

```text
'AKLT.W.H1C023.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed axioms listed in the task.

## Build

Command:

```text
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C023.Main
```

Result: successful, `Built AKLT.W.H1C023.Main (5.8s)`; the build completed successfully.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C023/Main.lean` with the requested theorem and exact type.
- The nested row and column list maps are decoded with `List.getD_map`.
- Explicit bounds for both `Fin n` values come from the supplied length equality.
- Build succeeded with `lake build AKLT.W.H1C023.Main`.
- `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues remain.
