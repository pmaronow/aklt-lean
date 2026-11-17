STATUS: PARTIAL

## Files

- `AKLT/W/H1C008/Main.lean`

## Delivered declarations

- `AKLT.W.H1C008.Residual_activeTokens : Prop`
  ```lean
  ∀ a : Input, inputCheck a = true →
    inputInversion a ⊆ reductionVectors (inputPattern a) (inputRepresentation a)
  ```
- `AKLT.W.H1C008.Residual_wholePairMembership : Prop`
  ```lean
  ∀ a : Input, inputCheck a = true →
    ∀ x ∈ reductionGroups (inputPattern a),
      groupIsPair (inputPattern a) (inputRepresentation a) x = true →
        (groupLeader x ∈ inputInversion a ↔ groupSecond x ∈ inputInversion a)
  ```
- `AKLT.W.H1C008.main_from_residuals`
  ```lean
  (hActive : Residual_activeTokens) →
  (hPairs : Residual_wholePairMembership) →
  AKLT.Cert.H1.Production.Leaves.compilerInversion
  ```

The file also contains proved private lemmas extracting the relevant `inputCheck` fields, converting `inputInversion` and `inputTokens` membership, and expressing a site's degree using its four possible incident bonds. A local east-tip bond calculation confirms the original-slot indexing for that case.

The requested declaration `AKLT.W.H1C008.main` is **not proved**. The two residual propositions remain open; in particular, I did not establish that the checker's slot counts coincide with `reductionVectors` for every corner and tip.

## Axioms

`#print axioms AKLT.W.H1C008.main_from_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

No forbidden proof escape is used.

## Build

- Command: `lake build AKLT.W.H1C008.Main`
- Result: successful.
- Timing: Lake reported 13 seconds for the target; shell wall time was 18.3 seconds.

## Open issues

- Prove `AKLT.W.H1C008.Residual_activeTokens` by matching `inputTokens` to the retained original `Fin 20` slots.
- Prove `AKLT.W.H1C008.Residual_wholePairMembership` using the checker's equal-membership condition for two-slot corners.
- Then export the exact requested theorem `AKLT.W.H1C008.main`.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C008/Main.lean` and this report.
- `main_from_residuals` compiles, with only allowed axioms.
- The exact theorem `AKLT.W.H1C008.main` is not delivered.
- Open residuals: `Residual_activeTokens`, `Residual_wholePairMembership`.
- No existing files were changed; only the assigned worktree directory and report were written.
- Build command succeeded: `lake build AKLT.W.H1C008.Main` (13 seconds target, 18.3 seconds wall time).
- Orchestrator should pass the two residuals to a follow-up proof attempt or mark the task partial.
