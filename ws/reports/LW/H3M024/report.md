STATUS: PROVED

## Files

- `AKLT/W/H3M024/Main.lean`

## Exported declaration

`AKLT.W.H3M024.main : AKLT.Blueprint.H3.ReflectionLivePairsStatement`

The proof transports the departure vertices and counts through reflection, then transports the erased and filtered neighbour sets. An involution lemma transports `powersetCard`, preserving both subset containment and cardinality two.

## Axioms

Command: `lake env lean --stdin` with `import AKLT.W.H3M024.Main` and `#print axioms AKLT.W.H3M024.main`.

Output:

```text
'AKLT.W.H3M024.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3M024.Main` — succeeded; Lean reported 7.1s for the module (14s wall time).
- The final build completed without warnings.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M024.main` with the required closed statement type.
- Proof compiled with `lake build AKLT.W.H3M024.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No proof limitations or open declarations.
- No orchestrator decision or additional input is needed.
