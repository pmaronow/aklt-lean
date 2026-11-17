STATUS: PROVED

## Files

- `AKLT/W/MOM007/Main.lean`

## Exported declaration

- `AKLT.W.MOM007.main : AKLT.Blueprint.Mom.ScalarTensorReconstructionStatement`

## Proof outline

The proof unfolds `TensorLaw`. It rewrites coordinate products as `mono` of sums of coordinate exponent vectors. The first and third indexed tensors, and all fourth-index patterns with an odd multiplicity, follow from the parity premise. The second tensor splits into equal indices (the second scalar moment) and unequal indices (parity). For order four, the three possible pairings are handled explicitly: all four equal uses the fourth scalar moment, two distinct equal pairs use the mixed scalar moment, and all other patterns have an odd exponent. A finite classification lemma checks that these cases exhaust `Fin 3` indices.

## Axiom audit

`#print axioms AKLT.W.MOM007.main`:

```text
'AKLT.W.MOM007.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.MOM007.Main` — succeeded; Lake reported 5.8 s for the module and 10.46 s total command time.
- `lake env lean /tmp/MOM007_axioms.lean` — succeeded; confirmed theorem type and printed axioms.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/MOM007/Main.lean` with the exact requested theorem name and type.
- `AKLT.W.MOM007.main` is proved from the statement's own hypotheses.
- Axiom dependencies: `propext`, `Classical.choice`, `Quot.sound`.
- `lake build AKLT.W.MOM007.Main` succeeded.
- No residual statements, deviations, or open issues.
