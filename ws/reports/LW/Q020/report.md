STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q020/AKLT/W/Q020/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/Q020/report.md`

## Exported declaration

`AKLT.W.Q020.main : AKLT.Blueprint.Q.StarAmplificationStatement`

The proof defines the candidate projection in the amplified coordinates by applying the fixed-star kernel projection independently in every `Fin n` fibre. It proves that this vector belongs to `ker T` and that its difference from the original vector is orthogonal to `ker T`, so it is the ambient kernel projection. The squared distance and quadratic form both decompose as sums over the spectator coordinate; summing the fixed-star coercivity inequalities proves the result. The constant `g` is unchanged.

The argument also covers `n = 0`: the coordinate sums are empty and the fibrewise construction and identities remain valid.

## Axioms

Output of `#print axioms AKLT.W.Q020.main` (printed in the module as `#print axioms main`):

```text
[propext, Classical.choice, Quot.sound]
```

No forbidden proof escape or residual proposition is used.

## Build

Command: `lake build AKLT.W.Q020.Main`

Result: success; final module compile reported 9.3 seconds. The build compiled the target module with Lean 4.35.0-rc2 and the prebuilt project dependencies.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q020/Main.lean` with `AKLT.W.Q020.main` at the requested exact type.
- Proved the direct sum kernel projection identity and summed the fibre inequalities.
- Build: `lake build AKLT.W.Q020.Main` succeeded.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- `n = 0` is covered by the same empty-sum argument.
- No residual declarations, limitations, or deviations; no orchestrator decision is needed.
