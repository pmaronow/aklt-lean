STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP042/AKLT/W/GAP042/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/GAP042/report.md`

## Exported declaration

`AKLT.W.GAP042.main : AKLT.Blueprint.Gap.FrameWindowTransferStatement`

The proof extracts the constants and window estimate from `WindowProperty`. For each allowed `u`, it proves the window lies in `farVolume`: `u ≥ 1` gives `shellSpacing u ≥ 1`, and the integer floor estimate puts every shell radius strictly beyond the far-volume cutoff. The generic marginal then agrees with the finite-boundary frame marginal on the window, so the given estimate applies to restrictions of arbitrary total assignments.

## Axioms

`#print axioms AKLT.W.GAP042.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.GAP042.Main`
- Result: successful; module reported 6.9 seconds (16.0 seconds total command wall time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP042/Main.lean` with the requested theorem and type.
- The theorem is proved from `WindowProperty` by the finite-boundary to total-assignment marginal transfer.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build AKLT.W.GAP042.Main` succeeds.
- No residual statements, deviations, or open issues.
