STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q051/AKLT/W/Q051/Main.lean)

## Exported declaration

```lean
theorem AKLT.W.Q051.main : AKLT.Blueprint.Q.TorusMarkovStatement
```

The proof reindexes each conditioned fibre with an exterior sitewise swap. Numerical `interactionBounds` and proper colouring make every bond factor positive. Bonds touching `U` have identical factors under the map: internal bonds keep both labels, and crossing bonds use an exterior neighbour where the labels agree. All other bond factors change by a fixed positive product, which cancels from the conditional ratio. The argument includes empty and full `U`.

## Axioms

`#print axioms AKLT.W.Q051.main`:

```text
'AKLT.W.Q051.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All helper declarations are private.

## Build

- `lake build AKLT.W.Q051.Main` — passed; Lean reported 5.5 s for the module build (13.0 s wall time for the command).
- `lake env lean /tmp/Q051Audit.lean` — axiom audit passed.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q051.main` with the requested closed statement.
- Build passed and the exported theorem uses only allowed axioms.
- The proof uses explicit numerical interaction bounds and boundary-neighbour agreement; no global gauge or evenness premise is added.
- Empty and full blocks are included.
- No open issues or deviations.
