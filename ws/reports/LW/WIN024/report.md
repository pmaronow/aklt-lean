STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN024/AKLT/W/WIN024/Main.lean)

## Exported declaration

`AKLT.W.WIN024.main : AKLT.Blueprint.Win.OuterEndpointTransferStatement`

The proof selects the unique exterior endpoint of each crossing edge, proves that every raw-boundary vertex is represented, and maps the assumed linked-edge paths to star-adjacency paths. Consecutive equal endpoints are handled by retaining the existing path; distinct endpoints in a linked triangle are star-adjacent.

## Axioms

`#print axioms AKLT.W.WIN024.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the permitted foundational axioms.

## Build

- Command: `lake build AKLT.W.WIN024.Main`
- Result: success; final incremental build reported 3.9 seconds for the Lean module (8.8 seconds wall time for the command).

## Open issues

None.

## ORCH-SUMMARY

- Delivered a compiled proof of `AKLT.W.WIN024.main` at the requested type.
- Only new file: `AKLT/W/WIN024/Main.lean`.
- Build succeeded with `lake build AKLT.W.WIN024.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, known limitations, or deviations.
