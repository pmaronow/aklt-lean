STATUS: PROVED FROM DEPS

## Files

- `AKLT/W/Q023/Main.lean`

## Exported declarations

- `AKLT.W.Q023.siteHomogeneous_isPhysical {L N} {p} (hp : AKLT.Blueprint.Q.siteHomogeneous p (fun _ => 4)) : AKLT.Uniq.IsPhysical p`
- `AKLT.W.Q023.encoded_polynomial_eq (p : SpinorPolynomial L N) : statePolynomial (polynomialState p) = AKLT.Uniq.encode (AKLT.Uniq.decode p)`
- `AKLT.W.Q023.main : AKLT.Blueprint.Q.CoefficientReconstructionStatement`

The proof converts the support-based degree premise to the weighted-homogeneity premise used by `AKLT.Uniq.encode_decode`. The state polynomial is definitionally the coordinate encoder after identifying its square-root scale factors, so `encode_decode` reconstructs the original polynomial. This dependency handles `p = 0`; its coefficient extensionality covers both encoded exponents and unsupported exponents. The decoder's scale denominators are nonzero by the existing `AKLT.Uniq.basisScale_ne_zero` result.

## Axioms

`#print axioms` output for each exported declaration:

```text
AKLT.W.Q023.siteHomogeneous_isPhysical: [propext, Classical.choice, Quot.sound]
AKLT.W.Q023.encoded_polynomial_eq: [propext, Classical.choice, Quot.sound]
AKLT.W.Q023.main: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.Q023.Main`
- Result: successful; module build reported 7.5 s (whole Lake invocation 14.8 s).
- Axiom inspection: `lake env lean --stdin` with imports and `#print axioms`; successful (8.4 s for all three declarations).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q023.main` with the requested exact type in `AKLT/W/Q023/Main.lean`.
- Build succeeded with `lake build AKLT.W.Q023.Main`.
- The proof reuses `AKLT.Uniq.encode_decode` and its basis-scale nonzero result.
- All exported declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations remain.
