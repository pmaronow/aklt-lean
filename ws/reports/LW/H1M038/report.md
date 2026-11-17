STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M038/AKLT/W/H1M038/Main.lean)

## Exported declaration

- `AKLT.W.H1M038.main : AKLT.Blueprint.H1.CommonWeightEigenvectorStatement`

## Proof outline

For each `μ ∈ eigenvaluesOn S O`, unfold `eigenvaluesOn` to obtain a nonzero `O` eigenvector in `S`. Form `E = S ⊓ eigenspace O μ`. The supplied commutation and invariance hypotheses show that `totalSpinZ` preserves `E`; its supplied symmetry on `S` gives symmetry of the restriction to `E` by the inherited inner product. Since `E` contains the given nonzero vector, it has positive finite dimension. The finite-dimensional spectral theorem applied to restricted `totalSpinZ` yields a nonzero eigenvector in `E` with a real eigenvalue. Membership in `E` supplies both the original `O` eigenvector equation and membership in `S`.

## Axioms

Output of `#print axioms AKLT.W.H1M038.main`:

```text
'AKLT.W.H1M038.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M038.Main`
- Result: successful; `AKLT.W.H1M038.Main` compiled in 4.5 seconds.
- Axiom check: `lake env lean /tmp/H1M038Axioms.lean` succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem `AKLT.W.H1M038.main` in `AKLT/W/H1M038/Main.lean`.
- The theorem proves the exact closed statement, with no residual propositions.
- `lake build AKLT.W.H1M038.Main` succeeded; exported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No changes were made to existing project files; no open issues remain.
