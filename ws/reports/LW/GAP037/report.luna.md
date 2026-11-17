STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP037/AKLT/W/GAP037/Main.lean)

## Delivered declarations

- `AKLT.W.GAP037.Residual_blockConditionalFormula : Prop` states, under the leaf's positive signed-interaction and proper-colouring hypotheses, the explicit normalized-weight formula for conditioning the torus law on a block fibre.
- `AKLT.W.GAP037.Residual_liftedWeightFactorization : Prop` states the raw torus-to-plane weight comparison, with a positive scalar independent of the block configuration.
- `AKLT.W.GAP037.paritySign_adjacent` proves that adjacent lifted plane sites have opposite parity signs.
- `AKLT.W.GAP037.normalize_rescale_equiv` proves that a positive constant rescaling and an equivalence of finite state spaces preserve normalized weights.
- `AKLT.W.GAP037.main_from_residuals` proves `AKLT.Blueprint.Gap.BoxGaugeLawStatement` assuming the two named residual statements.

The exact requested declaration `AKLT.W.GAP037.main : AKLT.Blueprint.Gap.BoxGaugeLawStatement` is not yet proved. The residuals are explicit `def ... : Prop` declarations; no unproved result is hidden behind an axiom or `sorry`.

## Axioms

`#print axioms normalize_rescale_equiv`:

```text
[propext, Classical.choice, Quot.sound]
```

`#print axioms paritySign_adjacent`:

```text
[propext, Classical.choice, Quot.sound]
```

`#print axioms main_from_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP037.Main` — successful; final module compilation reported 5.8 s (the project targets were already built).

## Open work

- Prove `AKLT.W.GAP037.Residual_blockConditionalFormula` by reducing the finite conditional marginal to the block-fibre weights.
- Prove `AKLT.W.GAP037.Residual_liftedWeightFactorization`: apply the proved parity flip to each lifted bond, reindex internal and crossing products using `LiftBonds`, and show the exterior-only product is positive before cancelling it.
- Then export the requested exact theorem `AKLT.W.GAP037.main` without residual assumptions.

## ORCH-SUMMARY

- Delivered a compiled reduction in `AKLT/W/GAP037/Main.lean`.
- Proved normalization invariance under a constant rescaling and finite equivalence.
- Proved the adjacent lifted parity signs are opposite.
- `main_from_residuals` derives the target leaf from two transparent residual propositions.
- Open: prove `Residual_blockConditionalFormula` and `Residual_liftedWeightFactorization`.
- Open: export exact `AKLT.W.GAP037.main`; the requested theorem is not yet available.
- No changes were made to existing project files; no forbidden proof placeholders or axioms were added.
