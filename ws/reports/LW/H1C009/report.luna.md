STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C009/AKLT/W/H1C009/Main.lean)
- This file contains the proof scaffolding and the explicit residual propositions. No existing project files were edited.

## Delivered declarations

`Residual_left`, `Residual_right`, `Residual_center`, `Residual_slots`, `Residual_dim`, `Residual_diluted`, `Residual_leaf`, `Residual_tip`, and `Residual_inverted` are closed `Prop` definitions. Each states one field of `NetworkGeometry` for inputs satisfying `inputCheck` and networks satisfying `geometryCheck`.

`main_of_residuals` proves:

```lean
Residual_left → Residual_right → Residual_center → Residual_slots →
Residual_dim → Residual_diluted → Residual_leaf → Residual_tip →
Residual_inverted →
AKLT.Cert.H1.Production.Leaves.compilerGeometry
```

The proof discharges the eight-site indexing, the full dimension list and suffix strides, and the table field from `TablesAccepted`. It also includes a proved finite description of the template's internal edges and a concrete east-center raw-edge bridge. The universal raw-edge and reduction-group field bridges remain residual.

The requested declaration `AKLT.W.H1C009.main : AKLT.Cert.H1.Production.Leaves.compilerGeometry` is not proved. The delivered theorem is conditional on the nine named residuals, so this is a partial result rather than a proof from the original hypotheses alone.

## Axioms

`#print axioms main_of_residuals`:

```text
'AKLT.W.H1C009.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed Lean axioms.

## Build

Command: `time lake build AKLT.W.H1C009.Main`

Result: success. Wall time: 13.27 seconds; Lean module build: 7.3 seconds. The build replayed the existing project dependencies and reported their existing linter warnings.

## Open issues

- `Residual_left`, `Residual_right`, and `Residual_center`: prove that raw edge bits agree with `presentBond` at every ring site.
- `Residual_slots` and `Residual_dim`: prove that raw incident-edge counts select the actual reduction group size and dimension, including reduced single-replacement corners.
- `Residual_diluted`: identify the ring status used by the local spec with the adjacent axial/tip group's status.
- `Residual_leaf`, `Residual_tip`, and `Residual_inverted`: identify the compiled flags with `SingleReplacement`, tip-group membership, and inversion membership. Tip groups are at the tip endpoint while ring moments are at the adjacent axial site.
- Once all nine residuals are proved, `main_of_residuals` supplies the exact target conclusion.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C009/Main.lean` and this report; the module builds.
- `main_of_residuals` proves compilerGeometry from nine explicit, smaller closed residuals.
- The requested assumption-free `AKLT.W.H1C009.main` remains open.
- Indexing, stride, table acceptance, the finite internal-edge list, and one center-edge bridge are proved.
- The universal raw-edge and reduction-group bridges remain the work needed to close the leaf.
