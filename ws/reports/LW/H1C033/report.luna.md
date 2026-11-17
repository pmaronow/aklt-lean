STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C033/AKLT/W/H1C033/Main.lean)

## Declarations

- `AKLT.W.H1C033.reflectPoint_involutive (x : Plane) : reflectPoint true (reflectPoint true x) = x`
- `AKLT.W.H1C033.mirror_h1Numerator_eq (π ρ : PatternData) (h : MirrorEffectiveData π ρ) : h1Numerator π = h1Numerator ρ`
- `AKLT.W.H1C033.mirror_h1Denominator_eq (π ρ : PatternData) (h : MirrorEffectiveData π ρ) : h1Denominator π = h1Denominator ρ`
- `AKLT.W.H1C033.Residual_inversionDenominatorTransport : Prop` states that a witness's group inversion and cleared denominator can be transported to the mirrored pattern.
- `AKLT.W.H1C033.Residual_orderedSectorTransport : Prop` states that the sector certificates transfer for fixed source and target inversion data while retaining the `Fin t` ordering. This ordering is what preserves the lower-triangular factor.
- `AKLT.W.H1C033.main_of_residuals` proves the requested leaf from those two residual propositions.

The requested theorem `AKLT.W.H1C033.main` is **not** proved. No residual is asserted as a theorem or used as an axiom; both remain explicit closed propositions.

## `#print axioms`

Build output:

```text
reflectPoint_involutive: [propext]
mirror_h1Numerator_eq: [propext, Classical.choice, Quot.sound]
mirror_h1Denominator_eq: [propext, Classical.choice, Quot.sound]
main_of_residuals: [propext, Classical.choice, Quot.sound]
```

Only the standard permitted axioms occur.

## Build

Command: `lake build AKLT.W.H1C033.Main`

Result: succeeded; Lake reported `Built AKLT.W.H1C033.Main (5.7s)` (12.8s wall time for the command, including Lake overhead and replayed dependencies).

## Open issues

The remaining work is to prove both residuals. In particular, the ordered-sector residual needs reflection covariance of the reduced polynomial, inversion signs, and central-basis matrix entries. A reflected central-basis equivalence must be composed with the source `Fin t` index so the original triangular `L` is reused without permuting its rows. The inversion/denominator residual also needs the same token and polynomial transport. These were not established here.

## ORCH-SUMMARY

- Delivered a compiling partial reduction in `AKLT/W/H1C033/Main.lean`.
- Proved reflection involutivity and equality of the mirrored H1 numerator and denominator.
- `main_of_residuals` derives the exact leaf from `Residual_inversionDenominatorTransport` and `Residual_orderedSectorTransport`.
- The exact declaration `AKLT.W.H1C033.main` remains open.
- Neither residual was proved; no axioms, `sorry`, or other escape hatches were added.
- Orchestrator should pass on the two residual propositions, especially the ordered basis/matrix covariance obligation.
