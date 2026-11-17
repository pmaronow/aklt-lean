STATUS: PROVED FROM DEPS

## Files

- `/home/ubuntu/aklt/wt/LW_Q032/AKLT/W/Q032/Main.lean`

## Exported declarations

- `AKLT.W.Q032.main : AKLT.Blueprint.Q.DeterminantPrimeEmbeddingStatement`

The proof applies `AKLT.Uniq.singletPrime`, which establishes primality of each
actual bond determinant in the full spinor polynomial ring. This stronger
result makes the statement's generic four-variable primality premise unused.
The dependency proves irreducibility by writing the determinant as a variable
plus a polynomial in the other variables; its coprimality and variable-support
conditions use `nextSite_ne`. That endpoint inequality follows from the lower
bound `3 ≤ L.val, N.val` in `Size`.

## Axioms

`#print axioms AKLT.W.Q032.main`:

```text
'AKLT.W.Q032.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.Q032.Main`
- Result: successful; Lake reported `Built AKLT.W.Q032.Main (5.1s)` and
  `Build completed successfully (8957 jobs)`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q032.main` with the exact requested statement.
- Proof reuses the existing stronger theorem `AKLT.Uniq.singletPrime`.
- The generic four-variable premise is not needed by this proof.
- Build succeeded; exported axioms are `propext`, `Classical.choice`, and
  `Quot.sound`.
- No open issues or deviations from the requested type and file location.
