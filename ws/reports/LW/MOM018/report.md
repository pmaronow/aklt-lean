STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_MOM018/AKLT/W/MOM018/Main.lean)

## Exported declaration

`AKLT.W.MOM018.main : AKLT.Blueprint.Mom.TripleNormalizerStatement`

The proof identifies the U functional with `moment` directly from the finite
weight definitions. It calculates the diagonal second moments from the
explicit twelve labels and derives the full second tensor for two arbitrary
vectors. A sign-flipping equivalence pairs antipodal labels, so the linear and
cubic terms vanish. Expanding the three affine factors then gives the required
normalizer. The constant moment is also calculated directly from the twelve
labels.

## Axioms

Output of `#print axioms AKLT.W.MOM018.main`:

```text
'AKLT.W.MOM018.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms.

## Build

- Command: `export PATH="$HOME/.elan/bin:$PATH"; time lake build AKLT.W.MOM018.Main`
- Result: successful build, 21.0 seconds wall time (15 seconds for the module).

## Open issues

None. The build reports minor tactic linter/info suggestions; they do not affect
the successful kernel-checked proof.

## ORCH-SUMMARY

- Delivered `AKLT.W.MOM018.main` with the exact requested type.
- The theorem compiles in `AKLT/W/MOM018/Main.lean`.
- Derives the finite U law and constant moment directly from definitions.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- Build command succeeded in about 21.0 seconds wall time.
- No open issues or deviations.
