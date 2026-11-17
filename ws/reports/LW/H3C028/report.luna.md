STATUS: PARTIAL

## Files

- `/home/ubuntu/aklt/wt/LW_H3C028/AKLT/W/H3C028/Main.lean`

## Exported declarations

- `AKLT.W.H3C028.tableBoundsLeaf : CertData.H3.Bridge.TableBoundsLeaf`
- `AKLT.W.H3C028.Residual_FreeRow : Prop := CertData.H3.Bridge.FreeRowLeaf`
- `AKLT.W.H3C028.Residual_RowTermsV2 : Prop := CertData.H3.Bridge.RowTermsV2Leaf`
- `AKLT.W.H3C028.planeSoundLeaf_from_residuals
  (hFree : Residual_FreeRow) (hRows : Residual_RowTermsV2) :
  CertData.H3.Bridge.PlaneSoundLeaf`

The last theorem extracts the packed checker facts, proves the bounded-grid indexing needed for the plane values, and composes the exact PlaneSpec clauses from the two residuals. The local-row clause uses `localRowCheck_sound` and the corrected `stationaryCoefficientV2` row identity. The checked zero-centre value is retained in the terminal clause.

## Axioms

`#print axioms tableBoundsLeaf` and `#print axioms planeSoundLeaf_from_residuals` both report:

```text
[propext, Classical.choice, Quot.sound]
```

These are the permitted axioms. No `sorry`, `admit`, `axiom`, `native_decide`, or unsafe declarations are used.

## Build

- `lake build AKLT.W.H3C028.Main` — succeeded; 10.65 s wall time (Lake reported 5.8 s for the target module).

## Open issues

The requested exact declaration `AKLT.W.H3C028.main : CertData.H3.Bridge.PlaneSoundLeaf` is not yet proved. The two remaining closed obligations are `Residual_FreeRow` (identify the integer free-row table with the coefficient-ceiling sum) and `Residual_RowTermsV2` (identify the routed and masked integer row with the corrected V2 coefficient expression). The frozen project contains these obligations only as Prop definitions, without proofs. I left the composition theorem explicit in both obligations rather than claiming the exact leaf.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C028/Main.lean` and this report.
- Proved `AKLT.W.H3C028.tableBoundsLeaf`.
- Proved `planeSoundLeaf_from_residuals` from the two transparent residual Props.
- Open exact declaration: `AKLT.W.H3C028.main : CertData.H3.Bridge.PlaneSoundLeaf`.
- Open residuals: `AKLT.W.H3C028.Residual_FreeRow`, `AKLT.W.H3C028.Residual_RowTermsV2`.
- Build succeeded; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No changes were made to frozen files.
