STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C013/AKLT/W/H1C013/Main.lean)

## Exported declarations

- `AKLT.W.H1C013.basisCheck_coordinates` proves that a successful `basisCheck` fixes the central weight, selects an allowed parity, and makes `indices` exactly the corresponding `sectorIndices` list (which is nonempty).
- `AKLT.W.H1C013.layout_coordinates` extracts the selected list and its length equality from `Bundle.LayoutAccepted`.
- `AKLT.W.H1C013.Residual_mixedRadixCodec : Prop` is the remaining closed finite-sector codec statement. For any metadata-accepted case, sign assignment, parity matching `exchangeParity`, and basis list passing `basisCheck`, it asks for an equivalence from positions in the checked list to `CentralBasis`, preserving `exchangeBasisCode` in list order.
- `AKLT.W.H1C013.main_from_Residual_mixedRadixCodec` proves
  `Residual_mixedRadixCodec → AKLT.Cert.H1.Production.Leaves.basisIndexing`.

The exact requested closed theorem `AKLT.W.H1C013.main` is not delivered because the residual codec proposition remains unproved. It isolates the mixed-radix enumeration from bundle remapping and matrix data. Its proof must relate site dimensions and `sectorLabel` to group basis dimensions, exchange weight, and exchange parity. In particular, for an exterior D coordinate the full site digit must be `3`, although the local group basis has one coordinate.

## Axioms

The module prints the axiom dependencies for its proved declarations. Each reports:

```text
[propext, Classical.choice, Quot.sound]
```

No forbidden proof escape is used.

## Build

Command: `lake build AKLT.W.H1C013.Main`

Result: succeeded; elapsed `10.57 s` (Lean reported the target module build itself as `4.7s`). The build also emitted pre-existing linter warnings in `AKLT.Gen.Gram`.

## Open issues

- Prove `AKLT.W.H1C013.Residual_mixedRadixCodec` by constructing the ordered finite-sector equivalence from the mixed-radix encoding and the checked weight/parity filter.
- Then export the exact closed theorem `AKLT.W.H1C013.main` at the requested type.

## ORCH-SUMMARY

- Delivered a compiled `Main.lean` with checker extraction lemmas and a theorem reducing `basisIndexing` to `Residual_mixedRadixCodec`.
- Exact requested declaration `AKLT.W.H1C013.main` remains open.
- `Residual_mixedRadixCodec` is the sole unproved proposition; it states the finite-sector list/code equivalence for accepted inputs.
- The residual explicitly requires the exterior D coordinate to encode as full local digit `3`.
- `lake build AKLT.W.H1C013.Main` succeeded in 10.57 s.
- Exported proof axiom output is `[propext, Classical.choice, Quot.sound]`.
- No other files were added.
