STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M068/AKLT/W/H1M068/Main.lean)

## Delivered declarations

`AKLT.W.H1M068.main_of_residuals` proves

```lean
(pick : RepresentationSelection) →
Residual_RepresentationInversion pick →
Residual_DenominatorExistence pick →
Residual_SectorWitnesses pick (chooseDenominators pick hdenom) →
AKLT.Blueprint.Top.H1FiniteDataStatementV2
```

The three residual predicates are explicit and closed (with their displayed parameters):

- `Residual_RepresentationInversion pick`: the per-covered-pattern selected representation and inversion set satisfy `GroupInversion`.
- `Residual_DenominatorExistence pick`: each selected representation has a `ClearsDenominator` witness.
- `Residual_SectorWitnesses pick denom`: for each covered pattern, the selected representation, inversion, denominator and fixed H1 numerator/denominator have `H1SectorWitnesses`, quantified over every exchange sign.

`chooseDenominators` selects the denominator witnesses with classical choice; `chooseDenominators_clear` proves their clearing property. This is only a conditional assembly. The requested closed declaration `AKLT.W.H1M068.main : AKLT.Blueprint.Top.H1FiniteDataStatementV2` is not claimed because the residuals have not been established.

## Axioms

Lean printed for `AKLT.W.H1M068.main_of_residuals`:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

All are allowed by the brief.

## Build

- `lake build AKLT.W.H1M068.Main` — successful; Lean module build 6.4 s, command wall time 15.58 s.
- The first build exposed a type mismatch in the local residual statement (`ClearsDenominator` takes the representation and denominator, not the inversion set); corrected before the successful build.

## Open issues

The residual obligations are not proved. The separate CERT_H1 project and its `proof-leaf-index.json` mark relevant mathematical leaves `OPEN`:

- Representation/inversion coverage: `AKLT.Cert.H1.Production.Leaves.inputCovered`, `compilerInversion`, `rawEncoding`, `enumerationSoundness`, `representativeLookup`, `representativeWitnessLookup`, `effectiveCodeClassification`, `sameDataWitness`, and `mirrorDataWitness`.
- Denominator clearing: `AKLT.Cert.H1.Production.Leaves.denominator` is open and depends on the open `momentPolynomial` obligation (and the geometry/compiler route).
- All regenerated sector witnesses: `acceptedLookup`, `parityCoverage`, `basisIndexing`, `acceptedDecode`, `sectorPackingExpansion`, `sectorCoefficientBound`, `signedPacking`, `packingDecode`, `paritySlice`, `momentPolynomial`, `tensorSubstitution`, `sectorLinearity`, `directRowsEntry`, `metadataFacts`, and `AKLT.Cert.H1.Production.TopLeaves.integerEntries` remain open. The CERT_H1 report describes checked prototypes and conditional assemblies, but not a complete all-pattern/all-sign kernel-checked handoff.

No counterexample to the proposition was found; the limitation is missing completed finite-data proofs, not evidence that the statement is false.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M068/Main.lean` with a compiled conditional assembly `main_of_residuals`.
- Residuals: selected valid representation/inversions; justified denominators; all-sign H1 sector witnesses.
- Exact closed theorem `AKLT.W.H1M068.main` is not delivered; no residual proof was available to close it.
- Lean axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Build passed: `lake build AKLT.W.H1M068.Main`.
- CERT_H1 currently marks the listed coverage, denominator, reconstruction, packing and sector leaves OPEN; handoff remains incomplete.
- No statement or pre-existing project file was edited.
