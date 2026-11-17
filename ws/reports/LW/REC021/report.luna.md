STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC021/AKLT/W/REC021/Main.lean)

## Exported declarations

- `AKLT.W.REC021.Residual_ResponseILowerBounds : Prop` — for every admissible three-neighbour U departure, `responseI` is at least `41/50` in the pinned model and at least `1` in the free model.
- `AKLT.W.REC021.Residual_LogMeanMonotone : Prop` — coordinatewise monotonicity of the defined logarithmic mean on positive inputs.
- `AKLT.W.REC021.Residual_CrudeLogAt41 : Prop` — the crude logarithmic enclosure at `41/50`.
- `AKLT.W.REC021.logarithmicMean_pos_local` — proves positivity of the divided-difference logarithmic mean for positive arguments.
- `AKLT.W.REC021.main (hI) (hM) (hC) : AKLT.Blueprint.Rec.BetaUniformStatement` — proves the requested conclusion from the three residuals above. The requested unconditional `main : BetaUniformStatement` remains open.

The reduction uses `responseBeta = 1 / (3 * logarithmicMean I_true I_false)`, compares the two I arguments with `(41/50, 1)`, applies the endpoint enclosure, and closes the rational comparison by exact arithmetic.

## Axioms

`#print axioms AKLT.W.REC021.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC021.Main` — succeeded; module build reported 5.3s (command elapsed 10.6s).
- No tests were run.

## Open issues

- `Residual_ResponseILowerBounds` is the finite-network conditioning step. It still needs reindexing to a common finite network, explicit summation over positive-mass fibres, and the degree-four/three-factor mean estimates from the paper.
- `Residual_LogMeanMonotone` is the analytic monotonicity argument cited in §6 lines 387–391.
- `Residual_CrudeLogAt41` is the rational/logarithmic endpoint enclosure at `41/50`.
- Because these remain assumptions of `main`, the file does not yet export the requested unconditional declaration with exactly the requested type.

## ORCH-SUMMARY

- Delivered a compiling conditional reduction in `AKLT/W/REC021/Main.lean`.
- `AKLT.W.REC021.main` proves `BetaUniformStatement` from `Residual_ResponseILowerBounds`, `Residual_LogMeanMonotone`, and `Residual_CrudeLogAt41`.
- `logarithmicMean_pos_local` is proved directly; the main reduction uses exact arithmetic for the final rational comparison.
- Open declarations: `Residual_ResponseILowerBounds`, `Residual_LogMeanMonotone`, `Residual_CrudeLogAt41`.
- The unconditional requested `AKLT.W.REC021.main : AKLT.Blueprint.Rec.BetaUniformStatement` is not yet proved.
- Axioms reported for the conditional theorem: propext, Classical.choice, Quot.sound.
- Build succeeded with `lake build AKLT.W.REC021.Main`.
- Orchestrator should continue with the three residuals or assign their proofs independently.
