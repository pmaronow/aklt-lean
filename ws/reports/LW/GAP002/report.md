STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP002/AKLT/W/GAP002/Main.lean:250)
- This file contains the proof and finite-fibre helper definitions and lemmas; no existing project files were changed.

## Exported declaration

- `AKLT.W.GAP002.main : AKLT.Blueprint.Gap.ConditionalProjectionStatement`

Its proof establishes idempotence, preservation of constants, preservation of `complexMean`, and weighted self-adjointness using `star` on complex values. It groups sums by the exterior configuration and uses strict positivity to justify each represented fibre denominator. Empty and full blocks are covered by the same argument.

The supporting declarations in `AKLT.W.GAP002.FiniteProjection` define finite fibres, their real masses and complex weighted sums, the induced fibre mean, and prove its denominator positivity, conditional-expectation identification, idempotence, mean preservation, constant preservation, and self-adjointness. `agreeOutside_iff_exteriorKey_eq` identifies the statement's exterior relation with equality of exterior assignments.

## Axioms

`#print axioms AKLT.W.GAP002.main`:

```text
'AKLT.W.GAP002.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP002.Main` — passed; module build time 9.2 s, command elapsed 19.29 s.
- Axioms checked with `lake env lean AKLT/W/GAP002/Axioms.lean` (temporary check file removed after inspection).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP002.main` with the exact requested type in `AKLT/W/GAP002/Main.lean`.
- The theorem proves all four conditional projection properties for finite dependent products and strictly positive probabilities.
- Complex self-adjointness uses conjugation via `star`; both endpoint blocks are included.
- Build passed: `lake build AKLT.W.GAP002.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No limitations or deviations; no open issues.
