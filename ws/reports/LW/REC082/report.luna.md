STATUS: PARTIAL

## Files

- `AKLT/W/REC082/Main.lean`

## Exported declarations

- `AKLT.W.REC082.Residual_OnePinExpansion : Prop` — the single-pin finite stopped-trail expansion, including normalization from the original network to `p.normalized`.
- `AKLT.W.REC082.Residual_TargetTerminalFactor : Prop` — the terminal expectation equals the common target factor on trails ending at `p.v`.
- `AKLT.W.REC082.main_of_residuals (hExpansion : Residual_OnePinExpansion) (hTerminal : Residual_TargetTerminalFactor) : AKLT.Blueprint.Rec.PairResponseSplitStatement` — proves the finite target/boundary split from those two residual facts.

The exact unconditional declaration `AKLT.W.REC082.main : AKLT.Blueprint.Rec.PairResponseSplitStatement` is not delivered. No `sorry`, axiom, or other placeholder was used.

## Axioms

`#print axioms AKLT.W.REC082.main_of_residuals`:

```text
'AKLT.W.REC082.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `$HOME/.elan/bin/lake build AKLT.W.REC082.Main` — passed; Final build after cleanup: Lake reported module time 4.6 s (the initial uncached build took 13.343 s wall time).
- `$HOME/.elan/bin/lake env lean AKLT/W/REC082/Audit.lean` with an audit file importing `Main` and printing axioms — passed; audit output is above.

## Open issues

The missing proofs are precisely `Residual_OnePinExpansion` and `Residual_TargetTerminalFactor`. The first requires the finite pair-walk expansion and normalization invariance. The second requires the local norm-square terminal factor for both target types. The finite-sum subtraction and target/boundary partition are proved in `main_of_residuals`.

## ORCH-SUMMARY

- Delivered a compiled conditional proof of `PairResponseSplitStatement` in `AKLT/W/REC082/Main.lean`.
- The algebraic split is proved by `AKLT.W.REC082.main_of_residuals` from `Residual_OnePinExpansion` and `Residual_TargetTerminalFactor`.
- Open exact propositions: `AKLT.W.REC082.Residual_OnePinExpansion`, `AKLT.W.REC082.Residual_TargetTerminalFactor`.
- The required unconditional name and type, `AKLT.W.REC082.main : AKLT.Blueprint.Rec.PairResponseSplitStatement`, remains unproved.
- No other files were changed. Build passed; theorem axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- Orchestrator should supply/prove the two residuals or keep this leaf marked partial.
