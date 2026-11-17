STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC019/AKLT/W/REC019/Main.lean)

## Exported declarations

- `AKLT.W.REC019.Residual_BetaReciprocalBound : Prop` — for every eligible three-neighbour departure, the I logarithmic mean is positive and its reciprocal coefficient is at most `367502 / 1000000`.
- `AKLT.W.REC019.Residual_JMeanUpper : Prop` — for every eligible three-neighbour departure, the J logarithmic mean is positive and at most `134 / 125`.
- `AKLT.W.REC019.main_of_residuals (hβ : Residual_BetaReciprocalBound) (hJ : Residual_JMeanUpper) : AKLT.Blueprint.Rec.AlphaUniformStatement` — combines the residual bounds and proves the requested alpha constant using exact rational arithmetic.

The requested closed theorem `AKLT.W.REC019.main` is not delivered. The unresolved work is proving the two residual propositions from the network hypotheses. In particular, the I-side residual requires the paper's finite-network reindexing, explicit conditioning over spin fibres, conditional moment bounds, and the crude logarithmic-mean estimate. The J-side residual requires the corresponding conditional estimates and logarithmic-mean upper bound. The blueprint descriptions of those results are not used as lemmas.

## Axioms

`#print axioms AKLT.W.REC019.main_of_residuals`:

```text
'AKLT.W.REC019.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC019.Main`
- Result: successful; module build reported 5.1 s (11.0 s wall time for the successful command invocation).

## Open issues

- Prove `AKLT.W.REC019.Residual_BetaReciprocalBound` from the finite-network definitions.
- Prove `AKLT.W.REC019.Residual_JMeanUpper` from the finite-network definitions.
- Then export the closed theorem as `AKLT.W.REC019.main` with type `AKLT.Blueprint.Rec.AlphaUniformStatement`.

## ORCH-SUMMARY

- Delivered a compiled conditional proof of the target coefficient bound in `AKLT/W/REC019/Main.lean`.
- The coefficient subtraction and final rational comparison are proved in `main_of_residuals`.
- Open residuals: `Residual_BetaReciprocalBound` and `Residual_JMeanUpper`.
- The exact closed declaration `AKLT.W.REC019.main` remains open.
- No existing files or frozen statements were edited.
- Orchestrator must supply/prove the two finite-network residuals or assign their derivation.
