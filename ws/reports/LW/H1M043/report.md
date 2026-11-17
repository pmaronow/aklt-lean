STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M043/AKLT/W/H1M043/Main.lean)

## Exported declaration

`AKLT.W.H1M043.main : AKLT.Blueprint.H1.PauliRealityStatement`

The proof shows that conjugation fixes each Pauli entry except entries of the second Pauli matrix, which it negates. The conjugate of a tensor product therefore gains a sign of `(-1)^(pauliYCount J a)`. Even-count terms are fixed; odd-count terms vanish by the coefficient premise. Conjugation fixes the resulting finite sum, so its imaginary part is zero.

## Axioms

Output of `#print axioms AKLT.W.H1M043.main`:

```text
'AKLT.W.H1M043.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms.

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1M043.Main`
- Result: successful, with no warnings. Lake reported 6.8 seconds for the module build; command wall time was 17.1 seconds.
- Axiom check: `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/H1M043Axioms.lean`

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M043.main` with the exact requested type in `AKLT/W/H1M043/Main.lean`.
- The requested module build succeeds.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
