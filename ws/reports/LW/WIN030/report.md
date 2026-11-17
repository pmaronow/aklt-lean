STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN030/AKLT/W/WIN030/Main.lean)

## Exported declarations

- `AKLT.W.WIN030.main : AKLT.Blueprint.Win.ConnectedEnumerationStatement`
- `AKLT.W.WIN030.reflTransGen_exists_finitePath`: a reflexive transitive relation path yields a finite indexed path.
- `AKLT.W.WIN030.finitePath_zero_eq`: a length-zero finite path has equal endpoints.
- `AKLT.W.WIN030.finitePath_last`: a positive-length finite path has a final edge and a shorter prefix.

The proof chooses a root, assigns each vertex its minimum finite path length from that root, and orders vertices lexicographically by distance and coordinates. The final-edge decomposition of a shortest path supplies an adjacent vertex with smaller distance, hence an earlier index.

## `#print axioms`

- `reflTransGen_exists_finitePath`: does not depend on any axioms.
- `finitePath_zero_eq`: does not depend on any axioms.
- `finitePath_last`: `[propext]`.
- `main`: `[propext, Classical.choice, Quot.sound]`.

## Build

- `lake build AKLT.W.WIN030.Main` — passed; 9.13 seconds wall time, with the target module built in 4.4 seconds.

The compiler emitted one style suggestion for the local `LinearOrder` instance (`letI` versus `let`); it does not affect the build or proof.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN030.Main.main` with the exact requested statement.
- The target module builds successfully.
- Axioms used by `main`: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements or unresolved proof obligations.
- Only limitation: one non-failing Lean style suggestion for the local instance declaration.
- Orchestrator action: none required.
