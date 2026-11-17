STATUS: PARTIAL

## Files

- `AKLT/W/REC003/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC003/report.md`

## Exported declaration

- `AKLT.W.REC003.main_from_residuals` :
  `Residual_PreFactorization → Residual_PostFactorization → AKLT.Blueprint.Rec.TwoFactorizationStatement`

`AKLT.W.REC003.main` with the required unconditional type was not completed. No axioms, `sorry`, or other forbidden constructs were used.

## Residual statements

- `AKLT.W.REC003.Residual_PreFactorization` is the pre-step partition identity obtained by integrating the U spin with its two present bonds.
- `AKLT.W.REC003.Residual_PostFactorization` is the post-step partition identity obtained by integrating the D spin after the selected bond is deleted.

Each residual is one conjunct of the target, stated universally over exactly the target's premises. `main_from_residuals` only assembles them; it does not prove either residual.

The remaining work in both residuals is to reindex the finite function space on `D.active` at the departure site, identify and isolate the incident bond factors in `D.bonds`, and evaluate the resulting one-site finite sums. The pre-step identity additionally needs the exact U second-moment calculation. The post-step identity needs the D first-moment calculation and the fact that no original leg is incident at an admissible start outside `protectedSites`.

## Axioms

Output of `#print axioms AKLT.W.REC003.main_from_residuals`:

```text
'AKLT.W.REC003.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC003.Main`
- Result: successful, `Built AKLT.W.REC003.Main`
- Reported module build time: 5.6 seconds

## Open issues

- Prove `AKLT.W.REC003.Residual_PreFactorization`.
- Prove `AKLT.W.REC003.Residual_PostFactorization`.
- Then expose the required unconditional `AKLT.W.REC003.main` declaration.

## ORCH-SUMMARY

- Delivered a compiling composition theorem and two explicit, closed residuals.
- The required unconditional theorem `AKLT.W.REC003.main` remains open.
- No existing project files were changed; no forbidden proof escape was used.
- Both residuals require the finite partition reindexing and site-integration proof described above.
- Orchestrator should pass on the two residual proofs before considering this leaf complete.
