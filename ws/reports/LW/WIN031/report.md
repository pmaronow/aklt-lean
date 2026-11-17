STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN031/AKLT/W/WIN031/Main.lean`

## Exported declaration

`AKLT.W.WIN031.main : AKLT.Blueprint.Win.CutScalesStatement`

Its statement is: for all `a y : Plane`, `u : ℕ`, and `i : ℤ`, if `CutSetup a y u i`, then

```lean
390 ≤ shellSpacing u ∧
2 * shellSpacing u - 1 ≤ (shellRadius u i : ℝ) ∧
(shellRadius u i : ℝ) ≤ shellSpacing u ^ 2 ∧
(shellRadius u i : ℝ) ≤ (u : ℝ) - 31 ∧
(i - 1 : ℝ) * shellSpacing u <
  (shellRadius u i : ℝ) - shellSpacing u / 12 - 1
```

## Proof route

The setup gives `geometryThreshold 64 ≤ u`, which reduces to `390^4 ≤ u`. Taking square roots establishes `390 ≤ shellSpacing u`; the fourth-power identity `shellSpacing u ^ 4 = u` supplies the `u - 31` radius bound. The floor bounds for `shellRadius` give the lower and upper radius estimates from `2 ≤ i ≤ shellSpacing u`. For the final strict inequality, the strict lower floor estimate leaves a gap of `11 * shellSpacing u / 12 - 2`, which is positive by the scale bound.

## Axioms

`#print axioms AKLT.W.WIN031.main`:

```text
'AKLT.W.WIN031.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN031.Main` — succeeded; final invocation took 14.9 seconds wall time.
- Axiom check: `printf 'import AKLT.W.WIN031.Main\n#print axioms AKLT.W.WIN031.main\n' | lake env lean --stdin`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/WIN031/Main.lean`.
- The module builds successfully with `lake build AKLT.W.WIN031.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No helper file, residual statement, limitation, or deviation.
- No open issues; orchestrator action: none.
