STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q013/AKLT/W/Q013/Main.lean)

## Exported declaration

- `AKLT.W.Q013.main : AKLT.Blueprint.Q.QuarticDiagonalStatement`

The proof enumerates `j : Fin 5`. It computes the third-coordinate icosahedron averages in degrees one through four as `0`, `1/3`, `0`, and `1/5`, expands the five diagonal polynomials, and simplifies the resulting values against the inverse binomial coefficients.

## Axioms

`#print axioms AKLT.W.Q013.main`:

```text
'AKLT.W.Q013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q013.Main` — passed; Lake reported the module built in 6.1 seconds.
- `lake env lean` with `import AKLT.W.Q013.Main` and `#print axioms AKLT.W.Q013.main` — passed.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q013/Main.lean` and `AKLT.W.Q013.main` with the requested exact statement.
- The module builds successfully.
- The theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, limitations, or deviations remain.
