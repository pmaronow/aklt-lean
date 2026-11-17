STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M009/AKLT/W/H1M009/Main.lean)

## Delivered declarations

- `AKLT.W.H1M009.Residual_FormalDotSupport`: the two formal-dot support degree bounds (internal bond endpoints and internal-to-slot).
- `AKLT.W.H1M009.Residual_LocalCounts`: the local incident-bond plus retained-slot count bound, at active and omitted sites.
- `AKLT.W.H1M009.main_from_residuals`:

  ```lean
  Residual_FormalDotSupport → Residual_LocalCounts →
    AKLT.Blueprint.H1.OriginalDegreeStatement
  ```

The conditional theorem separately counts internal bond contributions and active external-slot contributions, then uses support inclusions under polynomial addition and multiplication. It establishes the requested conclusion from the two residuals. The exact theorem `AKLT.W.H1M009.main : AKLT.Blueprint.H1.OriginalDegreeStatement` is not yet delivered.

## Axioms

`#print axioms AKLT.W.H1M009.main_from_residuals`:

```text
'AKLT.W.H1M009.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M009.Main` — succeeded; Lake reported the module build in 6.1 seconds (12.0 seconds wall time for the command).
- `lake env lean AKLT/W/H1M009/Main.lean` — succeeded in about 7.0 seconds.

## Open issues

- Prove `AKLT.W.H1M009.Residual_FormalDotSupport`. Direct support expansion for `formalDot` exceeded Lean's heartbeat limit in attempts up to 1,500,000.
- Prove `AKLT.W.H1M009.Residual_LocalCounts` from the template geometry, covered bond rules, and slot enumeration.
- Then instantiate `main_from_residuals` to produce the exact requested `main` theorem.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M009/Main.lean` and this report.
- Compiled `main_from_residuals`, proving the target from two explicit closed residual propositions.
- Open exact declarations: `Residual_FormalDotSupport`, `Residual_LocalCounts`.
- Exact requested declaration `AKLT.W.H1M009.main` remains open; status is PARTIAL.
- Formal-dot support expansion exceeded tested Lean heartbeat limits; finite geometric counting also remains to be proved.
- Orchestrator should pass on the two residual proofs or resume this leaf with a more efficient formal-dot support lemma.
