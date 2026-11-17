STATUS: PROVED

## Files

- [`Main.lean`](/home/ubuntu/aklt/wt/LW_H3M025/AKLT/W/H3M025/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3M025/report.md`

## Exported declaration

`AKLT.W.H3M025.main : AKLT.Blueprint.H3.ReflectionPairLabelsStatement`

## Proof summary

Reflection commutes with word vertices and preserves straightness. It maps the response-neighbour set through both erasures and the dead-site filter, so the live-other cardinality and outgoing membership are preserved. Those facts keep the coefficient row unchanged. Reflection preserves coordinate equality, hence pair type. Finally, the natAbs distances to `kernelStart` and `kernelTarget .B` are unchanged, and the finite supremum transports through the pair image, proving shift equality.

## Axioms

`#print axioms AKLT.W.H3M025.main` output:

```text
'AKLT.W.H3M025.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M025.Main`
- Result: success; Lake reported the module built in 7.4 seconds. Lean emitted two nonfatal deprecation warnings for `if_pos`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/H3M025/Main.lean`.
- The target statement is proved with no residual claims.
- Axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- Build command succeeded: `lake build AKLT.W.H3M025.Main`.
- No deviations or open issues.
