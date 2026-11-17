STATUS: PARTIAL

The requested closed theorem is not proved. The delivered `AKLT.W.H1C006.main` is a compiled reduction with two explicit closed residual inputs. In particular, this is not an exact-type success and must not be entered into the proved-leaf index.

## Files

All Lean files are under `/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/`; all are transitively imported by `Main.lean`.

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Main.lean): final assembly, residual alias, and axiom checks for all 47 exported theorems.
- [Dependencies.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Dependencies.lean): assembles proved MOM/H1M leaves into moments, leaf bounds, reconstruction, polynomial structure, real-scope reduction/inversion/operator structure, and the ladder-sector theorem.
- [Central.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Central.lean): central-weight span identification and conversion of unnormalized coordinate-matrix positivity to Hilbert-subspace positivity.
- [Exchange.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Exchange.lean): swap actions, involutions, self-adjointness, disjoint commutation, sector-vector exchange identities, and common sign eigenvectors.
- [Supported.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Supported.lean): the remaining finite-span completeness definition; supported-sector invariance and full-space semidefiniteness conditional on that definition.
- [Scaling.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Scaling.lean): positive scaling and removal of the supplied indexing equivalence, conditional only on the existing exact entry-scale leaf.
- [RealBridge.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/RealBridge.lean): coefficient embedding commutes with inversion and the Pauli map; uses the repaired arbitrary-real inversion interface to obtain rational-polynomial nonnegativity on the supported product of balls.

The earlier attempt's report remains in `report.luna.md`. Its broad reconstruction and sector-to-ball residuals have been replaced.

## Exported declarations and statements

The complete elaborated signatures of all 54 declarations, including every helper theorem and definition, are in [declarations.txt](/home/ubuntu/aklt/reports/LW/H1C006/declarations.txt). Principal signatures follow; all short names below are in `AKLT.W.H1C006`.

```lean
moments : AKLT.Blueprint.Top.MomentsStatement
threeFactorMean : AKLT.Blueprint.Top.ThreeFactorMeanStatement
leaf : AKLT.Blueprint.Top.LeafStatement
reconstruction : AKLT.Blueprint.H1.SimultaneousLeafReconstructionStatement
reducedStructure : AKLT.Blueprint.H1.ReducedStructureStatement
reducedStructureReal : AKLT.Blueprint.H1.ReducedStructureStatementV2
reduceReal : AKLT.Blueprint.Top.ReduceStatementV2
inversionReal : AKLT.Blueprint.Top.InversionStatementV2
operatorStructure : AKLT.Blueprint.Top.OperatorStructureStatement
operatorStructureReal : AKLT.Blueprint.Top.OperatorStructureStatementV2
sector : AKLT.Blueprint.Top.SectorStatement
```

`commonReconstruction` proves, without residual assumptions:

```lean
∀ (π : PatternData), π.Covered → ∀ (r : Representation)
  (m : Fin 20 → UnitVector),
  ∃ K : ℝ, 0 < K ∧ ∃ u : Fin 20 → Vec3,
    (∀ j ∈ reductionVectors π r, normSq (u j) ≤ 1) ∧
    patternCurrent π m = K * evaluateReduced (reducedPolynomial π r false) u ∧
    patternNext π m = K * evaluateReduced (reducedPolynomial π r true) u
```

The conditional entry points have exactly these signatures:

```lean
main_of_residuals
  (hScale : Residual_thresholdScale)
  (hComplete : Residual_exchangeCompleteness) :
  AKLT.Cert.H1.Production.TopLeaves.sectorPositiveImpliesBound

main
  (hScale : Residual_thresholdScale)
  (hComplete : Residual_exchangeCompleteness) :
  AKLT.Cert.H1.Production.TopLeaves.sectorPositiveImpliesBound
```

These hypotheses are explicitly present in both theorem types; neither residual has been asserted as a theorem.

## What is now proved

1. The same positive factor and the same reduced vectors reconstruct current and next. This discharges the earlier `Residual_commonReconstruction` obligation entirely using indexed, proved leaves.
2. The actual central space equals the span of the central integer-coordinate vectors. The proof selects one eigenspace from a spanning weight family and does not require independence or normalization.
3. Positive definiteness of `complexSectorMatrix` gives `PositiveOn` on that actual central space.
4. Disjoint group swaps commute and square to the identity. Every concrete sector vector has its stated exchange eigenvalues, and the entire exchange space satisfies those identities.
5. An eigenspace invariant under a finite commuting family of involutions contains a nonzero common sign eigenvector. The proof successively uses `v + Xv`, or uses `v` with negative sign when that sum vanishes.
6. A U sandwich `O = P O P` implies `XO = OX = O`. Thus every eigenvector of a nonzero eigenvalue is symmetric in each U pair. Zero eigenvalues are permitted outside the supported space.
7. Conditional only on exchange-space completeness, operator structure gives sector invariance; the proved ladder-sector theorem transfers central positivity to each supported sector; exclusion of negative eigenvalues gives positive semidefiniteness on the full tensor space.
8. Conditional only on `thresholdScale`, the exact positive real factor `15 * D₀ * q` transfers indexed integer positivity to the unindexed complex central form. Optional Sylvester/Bareiss leaves are unnecessary.
9. The repaired real-coefficient inversion theorem, exact rational coefficient embedding, and common reconstruction finish the original pointwise inequality.

The supported-positivity argument uses common exchange eigenvectors and excludes negative spectrum, instead of constructing an explicit orthogonal sum of sector projections. It retains precisely the possibility of kernels on discarded U directions.

## Open obligations

### 1. Existing blueprint leaf: `AKLT.Cert.H1.Production.TopLeaves.thresholdScale`

The local alias is:

```lean
def Residual_thresholdScale : Prop :=
  AKLT.Cert.H1.Production.TopLeaves.thresholdScale
```

This leaf is absent from `/home/ubuntu/aklt/state/lw/proved-index.tsv`. Its conclusion is the exact entry identity

```lean
(thresholdSectorMatrix π r ε I D₀ p q a b : ℂ) =
  (15 * (D₀ : ℂ) * q) * complexSectorMatrix π r ε
    (invertPolynomial I (reducedDifference π r ((p : ℚ) / q))) a b
```

under its frozen coveredness, inversion, denominator, and threshold premises. What remains is reconstruction of the rounded integer entries from denominator clearing and their identification with the complex Pauli form. Positive scaling itself is already proved here as `positiveScale_of_thresholdScale`.

### 2. New finite linear-algebra residual: `AKLT.W.H1C006.Residual_exchangeCompleteness`

Its exact definition is:

```lean
def Residual_exchangeCompleteness : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ ε : ExchangeSigns π,
    ∀ ψ : TensorSpace (reductionVectors π r), ExchangeEigenvectors π r ε ψ →
      ψ ∈ exchangeSpace π r ε
```

Here `ExchangeEigenvectors π r ε ψ` means that for each retained pair, its concrete swap sends `ψ` to `exchangeSign π ε x • ψ`, with sign `-1` exactly for a D pair with `ε x = false`, and `+1` otherwise. `exchangeSpace` is the frozen span of the products of the explicit single, symmetric-pair, and exterior-pair integer vectors.

This residual contains no polynomial, positivity, certificate, threshold, or original-functional hypotheses. Its converse is proved as `exchangeSpace_eigenvectors`. The missing direction is the spanning/completeness argument for products of the local symmetric/exterior bases. It is not a separately named existing blueprint leaf, so it needs a new proof assignment or completion within this directory.

## Axioms and validation

`Main.lean` contains `#print axioms` for every exported theorem: 47 theorem declarations and 47 checks, with no missing checks. Every output is:

```text
[propext, Classical.choice, Quot.sound]
```

The full individual outputs are preserved in [axioms.txt](/home/ubuntu/aklt/reports/LW/H1C006/axioms.txt), including:

```text
'AKLT.W.H1C006.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C006.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build commands passed:

```text
lake build AKLT.W.H1C006.Dependencies
lake build AKLT.W.H1C006.Central
lake build AKLT.W.H1C006.Exchange
lake build AKLT.W.H1C006.Supported
lake build AKLT.W.H1C006.Scaling
lake build AKLT.W.H1C006.RealBridge
lake build AKLT.W.H1C006.Main
```

Lake-reported successful module times included: Dependencies 5.6 s, Central 6.3 s, Exchange 6.5 s, Supported 59 s in the final Main build (68 s in its standalone build), Scaling 5.8 s, RealBridge 15 s, Main 13 s. The final signature audit ran with `lake env lean /tmp/H1C006-declarations.lean`; it passed in 6.78 s; measured timing is in [validation-time.txt](/home/ubuntu/aklt/reports/LW/H1C006/validation-time.txt).

A scan of delivered Lean sources found no forbidden proof escapes. Only this task's directory is untracked in the worktree; no existing project files were edited. No sub-agents were used. The independent con-ron/NanoDa checkers were not run; the validation performed here is Lean/Lake compilation and axiom/signature auditing. The requested unconditional exact-type check remains unsatisfied by design of this partial delivery.

## ORCH-SUMMARY

- STATUS: PARTIAL; do not index `AKLT.W.H1C006.main` as a proved closed leaf.
- Seven Lean files are delivered and imported transitively by `AKLT.W.H1C006.Main`.
- `lake build AKLT.W.H1C006.Main` passed.
- The old common-reconstruction residual is fully discharged.
- Proved central-span identification, matrix-to-subspace positivity, swaps, and common sign eigenvectors.
- Proved supported-sector PSD from central positivity, conditional only on exchange completeness.
- Repaired real-scope reduction/inversion/operator structure and the ladder-sector chain are assembled.
- U antisymmetric kernels are allowed; global positive definiteness is never assumed.
- Open existing leaf: `AKLT.Cert.H1.Production.TopLeaves.thresholdScale`.
- Open new residual: `AKLT.W.H1C006.Residual_exchangeCompleteness`.
- Both residuals are closed transparent Prop definitions; neither is asserted as a fact.
- All 47 theorem axiom outputs are `[propext, Classical.choice, Quot.sound]`.
- Full signatures: `declarations.txt`; individual axioms: `axioms.txt`.
- No frozen files changed; no sub-agents or independent alternate kernels used.
- Orchestrator must supply the exact scale leaf and the finite exchange-span completeness proof.
- Once both are proved, specialize `main_of_residuals` and replace the conditional `main` with the required closed theorem.
