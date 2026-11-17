STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M023/AKLT/W/H1M023/Main.lean)

## Declarations

- `AKLT.W.H1M023.ReducedNoOmittedSpinResidual : Prop` states that a supported monomial has zero exponent at every internal spin coordinate outside `reducedSpinSites`.
- `AKLT.W.H1M023.ReducedFourDegreeResidual : Prop` states that each supported monomial has internal degree at most four at each site.
- `AKLT.W.H1M023.main_of_residuals : ReducedNoOmittedSpinResidual → ReducedFourDegreeResidual → AKLT.Blueprint.H1.ReducedDegreeStatement` combines those two clauses.

The requested theorem `AKLT.W.H1M023.main` with the exact target type is not proved. The residuals are each one clause of the target, with no additional assumptions hidden in other blueprint leaves.

The file also contains private support lemmas: support of a formal dot product consists of coordinatewise products, internal degree is additive on exponent sums, and a retained bond or retained vector factor contributes at most one internal degree at a site.

## Axioms

`#print axioms AKLT.W.H1M023.main_of_residuals`:

```text
'AKLT.W.H1M023.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M023.Main`
- Result: successful.
- Wall time: 13.76 s; Lake reported 6.0 s for the module target. The initial build also compiled the project's 8,955 dependencies.

## Open issues

- `ReducedNoOmittedSpinResidual`: prove that the internal coordinates in every reduced factor, especially a replacement factor's `leafNeighbour`, belong to the retained spin set.
- `ReducedFourDegreeResidual`: prove the covered-template factor count. This requires bounding retained bond incidences plus replaced-leaf incidences at each site, and accounting for the two fields at a retained corner.
- The exact requested declaration `AKLT.W.H1M023.main` remains open until both residuals are proved.

## ORCH-SUMMARY

- Delivered a compiling partial module and this report.
- Exact-name theorem `AKLT.W.H1M023.main` is open.
- Remaining statements are `ReducedNoOmittedSpinResidual` and `ReducedFourDegreeResidual` in `AKLT/W/H1M023/Main.lean`.
- `main_of_residuals` combines them into the frozen target; it does not discharge them.
- No existing project files were edited.
- Build: `lake build AKLT.W.H1M023.Main` succeeded.
- Orchestrator should pass on the two residual proofs or decide whether to reassign the leaf.
