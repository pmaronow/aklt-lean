STATUS: PARTIAL

# H1C001 — prove one blueprint leaf

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C001/AKLT/W/H1C001/Main.lean)

## Delivered declarations

- `AKLT.W.H1C001.Residual_integrality : Prop` — for every input covered by the statement, each scaled inverted rational sector entry is an integer before taking its floor.
- `AKLT.W.H1C001.Residual_symmetry : Prop` — the rational sector form is symmetric for every input covered by the statement.
- `AKLT.W.H1C001.main (hInt : Residual_integrality) (hSym : Residual_symmetry) : AKLT.Cert.H1.Production.TopLeaves.integerEntries` — proves that these two residuals remove the floor and yield the required symmetric integer matrix.

The requested closed declaration `AKLT.W.H1C001.main : AKLT.Cert.H1.Production.TopLeaves.integerEntries` is not proved. The conditional theorem is the compiled partial result required by the leaf-writer brief.

## Axioms

`#print axioms AKLT.W.H1C001.main`:

```text
[propext, Classical.choice, Quot.sound]
```

No forbidden axioms or placeholders are used.

## Build

- `lake env lean AKLT/W/H1C001/Main.lean` — passed, 6.3 s.
- `lake build AKLT.W.H1C001.Main` — passed, 11.5 s wall time; Lean reported the target module built in 5.3 s.

## Open issues

- `AKLT.W.H1C001.Residual_integrality`: prove coefficient-denominator clearing survives polynomial inversion and the rational Pauli/basis contractions. The key unfinished step is showing that the scaled sum defining each sector entry is integer-valued.
- `AKLT.W.H1C001.Residual_symmetry`: prove symmetry of the compressed real part from Hermiticity of the Pauli form. This remains a separate finite-sum argument.
- The orchestrator must supply proofs of both residuals or continue this leaf proof; until then the requested closed theorem remains open.

## ORCH-SUMMARY

- Delivered one compiled file: `AKLT/W/H1C001/Main.lean`.
- `main` proves `integerEntries` conditional on `Residual_integrality` and `Residual_symmetry`.
- The floor elimination from integer-valued rationals is proved.
- Open declarations: `AKLT.W.H1C001.Residual_integrality`, `AKLT.W.H1C001.Residual_symmetry`.
- The exact closed theorem requested by the brief is not yet established.
- Build passed; axioms are `[propext, Classical.choice, Quot.sound]`.
