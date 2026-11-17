STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3M004/AKLT/W/H3M004/Main.lean)

## Exported declaration

- `AKLT.W.H3M004.main : AKLT.Blueprint.H3.SingleChangeFactorStatement`

The proof factors the A→C term for a first-visit turn and the B→D term for a first-visit straight departure. It proves the corresponding finite-product identities directly, retaining the reward as a multiplicative factor throughout. Revisit and nonmatching channels vanish at the change index.

## Axioms

`#print axioms AKLT.W.H3M004.main`:

```text
'AKLT.W.H3M004.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3M004.Main` — passed; Lean reported a 6.9s module build (15.8s command wall time).
- The source contains no forbidden proof placeholders or unsafe declarations.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M004.main` with the required type in `AKLT/W/H3M004/Main.lean`.
- The target builds successfully with `lake build AKLT.W.H3M004.Main`.
- The theorem uses only the permitted axioms: `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues remain.
