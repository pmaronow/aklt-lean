STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H1M062/AKLT/W/H1M062/Main.lean`

## Exported declaration

- `AKLT.W.H1M062.main : AKLT.Blueprint.H1.RationalEmbeddingEvaluationStatementV2`
- The target states that for every rational vector polynomial `p` and real vector assignment `u`, evaluating the coefficient-mapped real polynomial equals `evaluateReduced p u`.

The proof unfolds the evaluation wrappers and applies `MvPolynomial.eval_map`.

## Axioms

`#print axioms AKLT.W.H1M062.main`:

```text
'AKLT.W.H1M062.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1M062.Main` — succeeded; module build reported 3.7s.
- A separate `lake env lean /tmp/H1M062Axioms.lean` invocation printed the axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem in `AKLT/W/H1M062/Main.lean`.
- The proof uses the polynomial evaluation/map identity.
- Build succeeded; exported theorem axioms are propext, Classical.choice, and Quot.sound.
- No residual statements, limitations, or deviations.
- No orchestrator decision is needed.
