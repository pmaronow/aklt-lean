STATUS: PARTIAL

## Files

- `/home/ubuntu/aklt/wt/LW_H1C003/AKLT/W/H1C003/Main.lean`

## Exported declarations

- `AKLT.W.H1C003.Residual_thresholdScale : Prop` is the entrywise threshold scaling identity required to relate `thresholdSectorMatrix` to the complex sector matrix. This is the remaining unproved residual; it is simpler than the requested positive-definiteness equivalence because it contains only entry equalities.
- `AKLT.W.H1C003.positiveScale_of_thresholdScale` proves `AKLT.Cert.H1.Production.TopLeaves.positiveScale` assuming the named threshold scaling identity.
- `AKLT.W.H1C003.main_of_residual` proves the same target assuming `Residual_thresholdScale`.

The requested closed declaration `AKLT.W.H1C003.main : AKLT.Cert.H1.Production.TopLeaves.positiveScale` is not delivered. The target does not include `thresholdScale` as a hypothesis, so proving the requested theorem still requires deriving that identity from `ClearsDenominator` and the definitions of the rational and complex sector matrices.

## Axioms

Lean printed:

```text
'AKLT.W.H1C003.positiveScale_of_thresholdScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C003.main_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms. The positive scalar used in the transfer is obtained from `0 < D₀` (the first conjunct of `ClearsDenominator`) and the explicit `0 < q`; the complex order is handled by casting their positive natural product. The reverse implication uses positivity of the inverse scalar.

## Build

- Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.H1C003.Main`
- Result: successful.
- Wall time: 12.4 seconds for the build command; Lake reported the target module built in 5.9 seconds. Existing unrelated linter warnings appeared in `AKLT.Gen.Gram` and `AKLT.Gen.Gram.Checker`.

## Open issue

- `AKLT.W.H1C003.Residual_thresholdScale` is unproved. It requires showing the scaled integer matrix entries reconstruct the exact complex sector entries, including the floor/integrality step from `ClearsDenominator` and the rational-to-complex operator-entry identity. Consequently, the exact requested declaration `AKLT.W.H1C003.main` remains open.

## ORCH-SUMMARY

- Delivered a compiled conditional proof of `positiveScale` in `AKLT/W/H1C003/Main.lean`.
- The scalar transfer is complete and extracts positivity of `D₀` and `q`.
- Remaining exact name: `AKLT.W.H1C003.main`.
- Open residual: `AKLT.W.H1C003.Residual_thresholdScale`.
- No changes were made to existing project files.
- Build command succeeded; only unrelated existing linter warnings were emitted.
