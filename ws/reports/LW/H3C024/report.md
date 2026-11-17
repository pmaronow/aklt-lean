STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C024/AKLT/W/H3C024/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/H3C024/report.md)

## Exported declaration

`AKLT.W.H3C024.main : CertData.H3.Bridge.CentreZeroV2Leaf`

The proof compares the two finite row sums summand by summand. When an edge lands at
`kernelCentre`, the checked centre value makes the legacy summand zero and the V2
coefficient is zero. For every other destination, simplifying the coefficient definitions
shows the coefficients are equal.

## Axioms

`#print axioms AKLT.W.H3C024.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3C024.Main`
- Result: successful; Lake reported `Built AKLT.W.H3C024.Main (5.1s)`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested closed theorem at the exact namespace, name, and type.
- The leaf follows from its checked zero-centre hypothesis and coefficient definitions.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- Build succeeded with `lake build AKLT.W.H3C024.Main`.
- No residual statements or known limitations.
