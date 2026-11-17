STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C020/AKLT/W/H3C020/Main.lean)

## Exported declaration

`theorem AKLT.W.H3C020.main : CertData.H3.Bridge.PullLeaf`

## Axioms

`#print axioms main`:

```text
'AKLT.W.H3C020.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H3C020.Main`
- Result: success; command wall time 9.9 s, module build reported 5.3 s. Lean emitted benign exponentiation-threshold and proof-script lint warnings.

The proof uses the existing packed-lane shift and mask lemmas, proves the boundary-mask lane formulas, then combines the interior source lane and exterior cap lane. The closed boundary-mask bounds use kernel reduction with `decide +kernel`; `native_decide` is not used. The certificate itself is never normalized.

## Open issues and deviations

- The requested first attempt with a different cheaper model was unavailable: this session has no model-switch tool, and the brief prohibits subagents. The proof was completed in the available model.
- No mathematical proof issues remain.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C020.main : CertData.H3.Bridge.PullLeaf` in the new `Main.lean` file.
- The requested Lake build succeeds.
- Axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- The proof uses packed-lane and boundary-mask lemmas; no whole-certificate normalization or `native_decide`.
- Limitation: no alternate cheaper-model attempt was possible; model switching was unavailable and subagents were prohibited.
- No remaining proof obligations; orchestrator may register this leaf as proved.
