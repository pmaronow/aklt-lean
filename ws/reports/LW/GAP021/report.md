STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP021/AKLT/W/GAP021/Main.lean)

## Exported declaration

`AKLT.W.GAP021.main : AKLT.Blueprint.Gap.LipschitzCouplingStatement`

The proof establishes the finite Hamming path bound from the definition of `lipschitz`, then bounds the difference of kernel means by summing against each supplied coupling and using its marginals and expected Hamming cost.

## Axioms

`#print axioms main`:

```text
'AKLT.W.GAP021.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP021.Main` — succeeded; Lean target reported 3.6 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/GAP021/Main.lean`.
- The theorem compiles and depends only on permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, deviations, or open issues.
