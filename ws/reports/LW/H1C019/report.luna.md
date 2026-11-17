STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C019/AKLT/W/H1C019/Main.lean)

Only the new task-directory file was added. No existing statement or library file was changed.

## Declarations

- `AKLT.W.H1C019.Residual_coordinateDigits : Prop` states the outstanding local coordinate identity: for every accepted bundle, basis row and column, and sector site, the sector coordinate selected from `mapped` equals the original local digit selected from `block.indices`.
- `AKLT.W.H1C019.main_of_coordinateDigits (h : AKLT.W.H1C019.Residual_coordinateDigits) : AKLT.Cert.H1.Production.Leaves.paritySlice` proves the requested leaf from that residual.

The exact unconditional declaration `AKLT.W.H1C019.main : AKLT.Cert.H1.Production.Leaves.paritySlice` is not delivered because `Residual_coordinateDigits` remains unproved.

The compiled proof also establishes that `sectorNetworkCheck = true` makes the sector sites' base projection equal the original network. It then proves generically that pointwise local matrix equality preserves the ring product, center-code sums, and current contraction. The local matrix equality follows directly from `Residual_coordinateDigits`, without changing or normalizing any antisymmetric coordinate.

## Axioms

`#print axioms AKLT.W.H1C019.main_of_coordinateDigits`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the permitted axioms.

## Build

- `lake build AKLT.W.H1C019.Main` — succeeded; target module built in 5.0 s, command wall time 11.622 s (including replay of dependencies).
- `lake env lean AKLT/W/H1C019/Main.lean` — succeeded.

## Open issue

Prove `AKLT.W.H1C019.Residual_coordinateDigits` from `Bundle.LayoutAccepted`. The remaining work is the mixed-radix argument from `remapCheck` and the sector stride checks, together with proving that each original local digit belongs to its parity-selected `sectorCoordinates` list. The latter must preserve the D exterior coordinate `3` exactly; no sign normalization or coordinate permutation is justified by the current proof.

## ORCH-SUMMARY

- Delivered a compiled conditional proof of `Leaves.paritySlice` from `Residual_coordinateDigits`.
- Proved base projection equality from `sectorNetworkCheck` and generic preservation through ring contraction.
- Open declaration: `AKLT.W.H1C019.Residual_coordinateDigits`.
- The exact unconditional theorem `AKLT.W.H1C019.main` is not available until that residual is proved.
- Main limitation: coordinate membership/parity and mixed-radix `remapIndex` extraction remain open.
- No existing files changed; the only added Lean file is `AKLT/W/H1C019/Main.lean`.
