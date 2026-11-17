STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C014/AKLT/W/H1C014/Main.lean)

## Delivered declarations

- `AKLT.W.H1C014.Residual_layoutIndexing : Prop` — explicit residual for positive width and the mapped-index distinctness/range facts needed by the leaf.
- `AKLT.W.H1C014.Residual_signedSparseDecode : Prop` — explicit signed sparse-digit extraction statement for the exact `sparsePack` and `signedBias` definitions.
- `AKLT.W.H1C014.rows_decode_from_residuals` — from the signed sparse decoder, a positive width, and distinct in-range columns, proves that every accepted sector row reconstructs its expected integer row.

The requested theorem `AKLT.W.H1C014.main : AKLT.Cert.H1.Production.Leaves.acceptedDecode` is **not delivered**. The complete leaf still needs proofs of the two residuals and a successful assembly of the row result with the metadata/layout hypotheses. I did not replace the requested theorem with an unproved assumption.

## Axioms

`#print axioms AKLT.W.H1C014.rows_decode_from_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

No forbidden proof escape is used.

## Build

- `lake build AKLT.W.H1C014.Main` — passed; 10.8 seconds wall time (the module itself reported 5.5 seconds).
- I attempted the outer conditional assembly, but Lean timed out during elaboration at `whnf`, including with a finite 2,500,000 heartbeat limit. That attempt is not present in the delivered file.

## Open issues

- Prove `AKLT.W.H1C014.Residual_signedSparseDecode` from signed base-2 positional arithmetic and the bias formula.
- Prove `AKLT.W.H1C014.Residual_layoutIndexing` from `basisCheck`, `sectorNetworkCheck`, and `remapCheck`, including distinctness and the mixed-radix range bound.
- Assemble those facts into the exact `AKLT.Cert.H1.Production.Leaves.acceptedDecode` theorem under the metadata and layout hypotheses.

## ORCH-SUMMARY

- Delivered a compiling row-check decoding bridge in `AKLT/W/H1C014/Main.lean`.
- The bridge assumes `Residual_signedSparseDecode`, distinct mapped columns, and an in-range bound.
- Explicit closed residuals: `Residual_signedSparseDecode` and `Residual_layoutIndexing`.
- Exact requested declaration `AKLT.W.H1C014.main` remains open; status is PARTIAL.
- No existing project files were changed; only the task directory and report were written.
- The outer assembly attempt timed out at Lean elaboration under a finite 2.5M heartbeat limit; it was removed from the final file.
- Orchestrator should pass the two residuals and exact theorem assembly to a follow-up writer.
