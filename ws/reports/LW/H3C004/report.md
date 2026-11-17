STATUS: PROVED

## Delivered files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C004/AKLT/W/H3C004/Main.lean)

## Exported declaration

`AKLT.W.H3C004.main : CertData.H3.Bridge.SuccessorCodeLeaf`

The proof expands the length-10 word coding, rewrites `directionCode (direction (n % 4))` to `n % 4`, and records the nine base-4 quotient/remainder steps. `omega` then closes the arithmetic identity. The proof does not normalize the larger certificate and does not use `native_decide`.

## Axioms

`#print axioms AKLT.W.H3C004.main`:

```text
'AKLT.W.H3C004.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms.

## Build

- Command: `lake build AKLT.W.H3C004.Main`
- Result: succeeded; Lake reported the module build at 16 seconds (25.2 seconds elapsed for the full command in this environment).

## Open issues and limitations

- No proof issues remain.
- The requested first attempt using a different cheaper model could not be routed with the available tools. No sub-agents were used, in accordance with the leaf-writer brief.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C004/Main.lean` with `AKLT.W.H3C004.main` proving the exact requested leaf.
- `lake build AKLT.W.H3C004.Main` succeeds.
- Exported theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, `axiom`, or `native_decide` occurs in the delivered file.
- Limitation: model-routing tools were unavailable for the requested cheaper-model first attempt; no sub-agents were used.
- No proof issue remains for the orchestrator.
