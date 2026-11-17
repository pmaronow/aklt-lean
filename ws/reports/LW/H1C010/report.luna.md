STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C010/AKLT/W/H1C010/Main.lean)

The exact requested declaration `AKLT.W.H1C010.main : AKLT.Cert.H1.Production.Leaves.denominator` is not yet proved. The file contains a compiled conditional assembly and three explicit residual propositions; it does not claim the target theorem unconditionally.

## Exported declarations

- `AKLT.W.H1C010.Residual_momentIdentity`: the universal exact identity between `networkNumerator` and the denominator-scaled, inverted `reducedPolynomial`, under `NetworkGeometry` and the outgoing-site condition.
- `AKLT.W.H1C010.Residual_networkIntegerCoefficients`: every coefficient of `networkNumerator` is an integer.
- `AKLT.W.H1C010.Residual_inversionCoefficientTransfer`: integrality of all scaled coefficients after sign inversion transfers to coefficients of the original polynomial on its support.
- `AKLT.W.H1C010.localTotalDenPositive (s : SiteSpec) : 0 < s.totalDen`.
- `AKLT.W.H1C010.denominator_of_residuals (hMoment) (hNetwork) (hInvert) : AKLT.Cert.H1.Production.Leaves.denominator`.

The last theorem proves the requested denominator conclusion from those three residuals. It also proves positivity of the product of local denominators and chooses an outgoing ring index from `π.Covered`. The missing work is proving the residual propositions from the local moment and polynomial definitions. In particular, no assertion is made that the frozen proposition is false or under-premised.

## Axioms

`#print axioms AKLT.W.H1C010.localTotalDenPositive`:

```text
[propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.H1C010.denominator_of_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the allowed axioms. No `sorry`, `admit`, or user-added axiom occurs in the file.

## Build

Command: `lake build AKLT.W.H1C010.Main`

Result: successful; final incremental module build reported 6.4 seconds (Lake replayed the already-built dependency graph). The generated module reports the axiom lists above.

## Open issues

- `Residual_momentIdentity`: prove the integer network numerator/moment identity from the site moment formulas and `NetworkGeometry`.
- `Residual_networkIntegerCoefficients`: prove integrality of coefficients for the network polynomial assembled from the integer local tables.
- `Residual_inversionCoefficientTransfer`: prove coefficient integrality is preserved when undoing `invertPolynomial`.
- Prove `AKLT.Cert.H1.Production.Leaves.denominator` unconditionally and export it as the exact requested `AKLT.W.H1C010.main`.

## ORCH-SUMMARY

- Delivered a compiled conditional denominator proof in `AKLT/W/H1C010/Main.lean`.
- Proved positivity of every local `SiteSpec.totalDen` and of their list product.
- The conditional proof uses the three residuals named above; none has yet been discharged.
- The requested exact `main` theorem is still open; status is PARTIAL.
- Final build: `lake build AKLT.W.H1C010.Main`, successful, about 6.4 seconds.
- Exported theorem axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
