STATUS: PROVED

## Files

- `AKLT/W/Q007/Main.lean`

## Exported declaration

- `AKLT.W.Q007.main : AKLT.Blueprint.Q.RelativeRotationStatement`

The proof establishes orthogonality of the frozen rotation directly, derives cancellation for each common power, and splits `i,j : Fin 3`. For forward exponent differences it uses `k = 1` or `2`; for reversed differences it swaps the two icosahedron labels. Thus all witnesses obey `1 ≤ k ≤ 2` without converting a negative exponent to `Nat`.

## Axioms

Output of `#print axioms AKLT.W.Q007.main`:

```text
'AKLT.W.Q007.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q007.Main` — succeeded; final incremental build took 5.4 seconds.
- Axioms inspected with `lake env lean /tmp/Q007Axioms.lean` — succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q007/Main.lean` with the requested theorem and exact type.
- `lake build AKLT.W.Q007.Main` succeeded.
- Exported theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, deviations, or open issues.
- Orchestrator action: include the delivered file and report.
