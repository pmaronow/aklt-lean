STATUS: COMPLETE

Namespace for all short names below: `AKLT.Blueprint.H1`. This is a blueprint delivery, not a proof of H1. The H1 assembly exposes the missing finite-data existence contract instead of claiming the two existing soundness implications supply data.

| Leaf / node | Paper label | Difficulty | State |
|---|---|---|---|
| `H1FiniteDataStatementV2` | `t:H1 / p:certificate` | hard | external input |
| `CertificateStatementV2` | `t:H1 / p:certificate` | easy | package |
| `ThresholdSymmetryStatement` | `l:integercheck` | assembly | assembled |
| `CoveredSlotEnumerationStatement` | `l:leaf` | medium | open |
| `CornerMeanBoundsStatement` | `l:leaf` | medium | open |
| `NormalizedMeanFactorStatement` | `l:leaf` | medium | open |
| `PassageSiteMomentsStatement` | `l:Iw` | medium | open |
| `PassageFubiniStatement` | `l:Iw` | hard | open |
| `PassageNetworkPositiveStatement` | `l:Iw` | medium | open |
| `PassageNextLowerBoundStatement` | `l:Iw` | medium | open |
| `PassageSubtractionStatement` | `l:Iw` | easy | proved |
| `OriginalDegreeStatement` | `l:Iw` | medium | open |
| `OriginalFactorStructureStatement` | `l:Iw` | medium | open |
| `OriginalRawEvaluationStatement` | `l:Iw` | easy | open |
| `MomentContractionStatement` | `l:moments / l:Iw / c:reduce` | hard | open |
| `MomentCovarianceTransferStatement` | `l:moments / l:Iw / c:reduce` | hard | open |
| `ContractionAffineStatement` | `l:moments / l:Iw / c:reduce` | medium | open |
| `ContractionSupportStatement` | `l:moments / l:Iw / c:reduce` | easy | open |
| `ActiveStatusesStatement` | `l:Iw` | easy | proved |
| `BlochAlgebraStatement` | `l:inversion` | easy | open |
| `BlochPositivityStatement` | `l:inversion` | medium | open |
| `SinglePauliTraceStatement` | `l:inversion` | easy | proved |
| `PauliExpansionStatement` | `l:inversion` | medium | open |
| `PauliProductTraceStatement` | `l:inversion` | medium | open |
| `InversionPolynomialStatement` | `l:inversion` | medium | open |
| `ProductDensityPositiveStatement` | `l:inversion` | hard | open |
| `TraceProductPositiveStatement` | `l:inversion` | medium | open |
| `InversionBallStatement` | `l:inversion` | easy | proved |
| `ReducedDegreeStatement` | `c:reduce` | medium | open |
| `ReducedFactorStructureStatement` | `c:reduce` | medium | open |
| `PeripheralGeometryStatement` | `c:reduce` | medium | open |
| `PeripheralFubiniStatement` | `c:reduce` | hard | open |
| `PeripheralAssignmentStatement` | `c:reduce` | hard | open |
| `SimultaneousLeafReconstructionStatement` | `c:reduce` | assembly | assembled |
| `BallChordStatement` | `c:reduce` | easy | open |
| `AffineEvaluationStatement` | `c:reduce` | medium | open |
| `ProductBallNonnegativeStatement` | `c:reduce` | medium | open |
| `DifferenceStructureStatement` | `c:reduce` | medium | open |
| `ReducedStructureStatement` | `c:reduce` | assembly | assembled |
| `DifferenceEvaluationStatement` | `c:reduce` | easy | proved |
| `SectorSpinStableStatement` | `l:sector` | hard | open |
| `SectorWeightBasisStatement` | `l:sector` | medium | open |
| `SpanWeightLatticeStatement` | `l:sector` | medium | open |
| `SpinAdjointStatement` | `l:sector` | easy | open |
| `SpinCommutatorStatement` | `l:sector` | medium | open |
| `WeightLadderTransferStatement` | `l:sector` | medium | open |
| `CommonWeightEigenvectorStatement` | `l:sector` | hard | open |
| `LadderWalkStatement` | `l:sector` | hard | open |
| `PositiveSpectrumStatement` | `l:sector` | hard | open |
| `CentralWeightHalfStatement` | `l:sector` | easy | proved |
| `PauliHermitianStatement` | `l:Ostruct` | easy | open |
| `ReflectionParityStatement` | `l:Ostruct` | hard | open |
| `PauliRealityStatement` | `l:Ostruct` | medium | open |
| `InversionCovarianceStatement` | `l:Ostruct` | easy | open |
| `AdjointPauliCoordinatesStatement` | `l:Ostruct` | medium | open |
| `AdjointPauliOrthogonalStatement` | `l:Ostruct` | medium | open |
| `PauliRotationTransferStatement` | `l:Ostruct` | hard | open |
| `CayleyTensorCommutationStatement` | `l:Ostruct` | medium | open |
| `TensorLinearCoefficientStatement` | `l:Ostruct` | hard | open |
| `SpinGeneratorTransferStatement` | `l:Ostruct` | easy | open |
| `MomentPauliInterchangeStatement` | `l:Ostruct` | hard | open |
| `PairExpansionFromRealizationStatement` | `l:Ostruct` | hard | open |
| `RetainedPairExpansionStatement` | `l:Ostruct` | assembly | assembled |
| `UnitPairSupportStatement` | `l:Ostruct` | medium | open |
| `EqualPairExchangeStatement` | `l:Ostruct` | medium | open |
| `PairExpansionTransferStatement` | `l:Ostruct` | easy | open |
| `PairTokensDistinctStatement` | `l:Ostruct` | easy | proved |

## Files and declarations

- [Lean entry point](/home/ubuntu/aklt/wt/BP_H1M/AKLT/Blueprint/H1/All.lean), [Assembly](/home/ubuntu/aklt/wt/BP_H1M/AKLT/Blueprint/H1/Assembly.lean), [Audit](/home/ubuntu/aklt/wt/BP_H1M/AKLT/Blueprint/H1/Audit.lean).
- [Definitions](/home/ubuntu/aklt/wt/BP_H1M/AKLT/Blueprint/H1/Definitions.lean) and the seven `Nodes*.lean` modules in `/home/ubuntu/aklt/wt/BP_H1M/AKLT/Blueprint/H1`.
- [leaves.json](/home/ubuntu/aklt/reports/BP_H1M/leaves.json): 54 independent mathematical leaves and one required external finite-data handoff. Each includes its exact closed Lean declaration, module, label, dependencies, difficulty, proof route, reuse pointers, seven trap checks and the first-attempt proof policy.
- [Exact declarations](/home/ubuntu/aklt/reports/BP_H1M/declarations.md): every node's full statement and every exported theorem's full signature.
- [Per-node trap audit](/home/ubuntu/aklt/reports/BP_H1M/trap-check.md), [raw audit output](/home/ubuntu/aklt/reports/BP_H1M/axioms.txt), [final build log](/home/ubuntu/aklt/reports/BP_H1M/final-build.log), [timings](/home/ubuntu/aklt/reports/BP_H1M/final-build-times.json).

Seven immediate closed nodes are proved: `activeStatuses`, `passageSubtraction`, `differenceEvaluation`, `singlePauliTrace`, `inversionBall`, `pairTokensDistinct`, and `centralWeightHalf`. `reducedStatuses` is also proved as an auxiliary theorem. `gramResidual` proves the complete Top target without any mathematical hypotheses, by direct reuse of `AKLT.Gen.Gram.int_gram_residual_posDef` over both R and C.

The four assembled intermediate statements are `ReducedStructureStatement`, `SimultaneousLeafReconstructionStatement`, `RetainedPairExpansionStatement`, and `ThresholdSymmetryStatement`; these are not additional open leaves. `CertificateStatementV2` packages soundness and actual finite-data coverage.

## Proof ownership update

The author's resumed instruction supersedes the original request to prove short leaves. Every further leaf proof must receive its first attempt from a different, cheaper model. This architect will write no further leaf proofs, including short facts or checker soundness; proved assembly implications remain in scope. Existing proofs are retained under the explicit exception. No new Lean proof was attempted or written after this update.

The following mathematical proofs were already written and are kept:

| Existing proof | Role / closed statement |
|---|---|
| `activeStatuses` | `ActiveStatusesStatement` |
| `passageSubtraction` | `PassageSubtractionStatement` |
| `differenceEvaluation` | `DifferenceEvaluationStatement` |
| `singlePauliTrace` | `SinglePauliTraceStatement` |
| `inversionBall` | `InversionBallStatement` |
| `pairTokensDistinct` | `PairTokensDistinctStatement` |
| `centralWeightHalf` | `CentralWeightHalfStatement` |
| `reducedStatuses` | Auxiliary retained-site U/D fact; its full universally closed signature is in `declarations.md`. |
| `gramResidual` | Existing direct reuse bridge proving `Top.GramResidualStatement`. |

[proof-ownership.json](/home/ubuntu/aklt/reports/BP_H1M/proof-ownership.json) inventories all 25 existing exported theorem signatures and hashes all 11 Lean source files. The other 16 exports are assembly implications or extraction bridges. This resumed update changes only report metadata; Lean source files and the previous kernel build/audit results are unchanged. The 55 open entries in `leaves.json` carry their exact closed declarations and the cheaper-model first-attempt requirement. No H1 checker or new checker soundness proof is introduced here; any such future soundness obligation must first become another closed open leaf.

## Target assemblies

| Export | Conclusion / purpose |
|---|---|
| `integratePassage_of_nodes` | `Top.IntegratePassageStatement` from moment/finite-network inputs and passage/contraction leaves. |
| `leaf_of_nodes` | `Top.LeafStatement` from `Top.MomentsStatement`, `Top.ThreeFactorMeanStatement`, and three local leaves. |
| `reducedStructure_of_nodes` | Rational reduced differences are vector-affine, orthogonally invariant and supported within the declared token set. |
| `simultaneousLeafReconstruction_of_nodes` | Common positive K and common ball vectors from peripheral geometry, Fubini and assignment leaves. |
| `reduce_of_nodes` | `Top.ReduceStatement` from local leaf rules, exact contraction, reconstruction and convex extension. |
| `inversion_of_nodes` | `Top.InversionStatement` from Bloch positivity, Pauli expansion, inversion, tensor-density positivity and PSD trace positivity. |
| `retainedPairExpansion_of_nodes` | Factor the equal-sign pair in each finite Pauli spin summand. |
| `operatorStructure_of_nodes` | `Top.OperatorStructureStatement` from reduced structure, SU(2)/generator transfers, and pair support/exchange leaves. |
| `sector_of_nodes` | `Top.SectorStatement` from explicit tensor spin algebra, common eigenvectors, integer ladder movement, and finite spectral positivity. |
| `gramResidual` | `Top.GramResidualStatement` unconditionally; no triangularity or factor invertibility is used. |
| `thresholdSymmetry_of_integerCheck` | Uses the externally owned `Top.IntegerCheckStatement` to prove reconstructed threshold symmetry. |
| `h1Theorem_of_certificate` | `Top.CertificateStatement → H1FiniteDataStatementV2 → Top.H1TheoremStatement`. |
| `h1Theorem_of_parts` | `Top.IntegerCheckStatement → Top.CertificateStatement → H1FiniteDataStatementV2 → Top.H1TheoremStatement`. |
| `h1_of_theorem` | `Top.H1TheoremStatement → Top.H1Statement`; all four threshold interval checks are proved. |
| `h1_of_parts` | The same three closed inputs as `h1Theorem_of_parts`, concluding `Top.H1Statement`. |
| `h1_of_certificateV2` | `CertificateStatementV2 → Top.H1Statement`. |

All assembly inputs are closed Props. Leaf definitions never take another leaf statement as a hypothesis: they quantify their needed mathematical premises directly. Shared moment and finite-network Top contracts are consumed by assembly, with their relevant mathematical components extracted explicitly. Every leaf and all actual numeric coefficient checks remain visible, with no trusted stored matrix or pivot introduced.

The two largest proof assignments were split a second time. Common reconstruction separates peripheral geometry, finite Fubini, and the common normalizer/vector assignment. Retained-pair support separates generic moment/Pauli interchange, the raw pair realization, local unit-pair support, exchange, and transfer over finite sums. Estimated proof sizes for mathematical leaves are 15–380 lines; these are planning estimates. The external data handoff needs its own certificate shards and is not a one-writer analytic proof assignment.

## #print axioms

The following is the exact audit output for all 25 exported theorems, including every assembly theorem and immediate leaf proof. The only dependencies reported are the allowed `propext`, `Classical.choice`, and `Quot.sound`.

```text
'AKLT.Blueprint.H1.momentInputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.integratePassage_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.leaf_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.reducedStructure_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.simultaneousLeafReconstruction_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.reduce_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.inversion_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.retainedPairExpansion_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.operatorStructure_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.sector_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.gramResidual' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.thresholdSymmetry_of_integerCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.h1Theorem_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.h1Theorem_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.h1_of_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.h1_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.h1_of_certificateV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.passageSubtraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.activeStatuses' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.singlePauliTrace' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.inversionBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.differenceEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.reducedStatuses' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.centralWeightHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.pairTokensDistinct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Top / Defs issues and V2 handoff

1. **Missing finite-data existence interface.** `AKLT/Blueprint/Top/Operator.lean:118` defines `IntegerCheckStatement` as exact reconstruction and optional Bareiss soundness. Line 142 defines `CertificateStatement` as a conditional: if every exchange sector has an indexed Gram witness, then the local pointwise inequality follows. Neither statement asserts that any representation, group inversion, denominator or sector witnesses exist for a given covered pattern. These are valid soundness contracts, but the brief calls them finite data statements. Their antecedents must be supplied to derive `t:H1`. The logical shape `(P → Q)` does not supply `P`.

   **Replacement:** `H1FiniteDataStatementV2` in `NodesCertificate.lean:17` asserts exactly the missing universal pattern coverage with existential reconstructed witnesses at the two fixed thresholds. `CertificateStatementV2` packages it with the existing certificate soundness contract. The proved H1 assemblies build on this V2 and explicitly expose the extra input. `IntegerCheckStatement` is logically redundant in the final H1 wrapper because the existing `CertificateStatement` already concludes the full pointwise inequality; it is separately consumed by `thresholdSymmetry_of_integerCheck`.

   **Evidence / handoff:** REV-PLAN `t:H1`, lines 2296–2323, says all 12,173 exchange-sector blocks were checked outside Lean, but full factor export/reconstruction and a kernel proof remain obligations; only representative factors were retained. No data was fabricated or claimed checked here. The data owner must provide complete coverage and shard kernel checks, or the orchestrator must accept a stronger external certificate input.

2. **Exchange-sign indexing trap, not a false Top statement.** `AKLT/Defs/Operator.lean:160` defines `ExchangeSigns π` as a sign on every group; signs at singles and U pairs are unused. Thus distinct sign functions may define identical exchange spaces. One cannot assert pairwise orthogonality or an orthogonal direct sum over all such functions. The sector target and this blueprint never make that assertion. The external proof of `CertificateStatement` should index only effective D-pair signs (or choose canonical values for unused signs) before using the Appendix D orthogonal decomposition at lines 883–894.

3. **Representation-order detail.** Appendix D describes reduced polynomials after passage integration. The existing `reducedSpinSites`/`reducedIntegrand` retain the passage spin and contract it along with the other retained spins. The blueprint works with these actual Defs and degree bounds, so it does not silently assume that the passage has already been erased. Finite moment contraction supplies the same current/next polynomial semantically; no shared file was edited.

No counterexample to the mathematical Top targets or shared Defs was found. The material issue is the missing data-existence handoff, not an asserted false theorem. All proposed additions are confined to the assigned namespace.

## Trap checks

All 67 statement definitions have a per-node audit in `trap-check.md`; all 55 open entries also carry the full audit in `leaves.json`. The audited categories are missing premises, vacuity/empty cases, coercions, Finset versus Fintype sums, natural subtraction, zero denominators and retained instance arguments. Highlights:

- Degree-four contraction includes internal support; variables outside the contracted set cannot disappear silently. Vector-affine means the sum of three coordinate exponents per token is at most one.
- Removed spins are zero with no site law. Norm bounds are used only for positive-weight atoms. U zero-weight atoms are omitted before claiming unit pair support.
- Every external slot is retained until its exact leaf integration. The reconstruction chooses K and u once for both current and next; unused vector tokens are zero.
- An empty tensor is one-dimensional with density 1. An empty Gram matrix is positive definite vacuously; scales g,d,S must still be positive. L may be singular or zero.
- localMean denominators have explicit positive normalizers; radius is positive. The zero vector has its own chord branch. Cayley normalization uses sqrt(1+t squared)>0.
- Pair support explicitly requires distinct tokens and a unit spin. Exchange remains valid at spin zero. groupSecond never identifies the two tokens.
- Weight movement uses integer offsets and explicit sign cases. The central value is exactly 0 or 1/2. No eigenvalue multiplicities are asserted, and positivity uses the inherited subspace inner product.
- Arbitrary finite-index leaves bind `[Fintype ...]` and `[DecidableEq ...]` explicitly. There are no ambient section variables to be silently dropped.

## Build and validation

Toolchain: Lean 4.35.0-rc2, pinned Mathlib 065356127b. Builds used `PATH="$HOME/.elan/bin:$PATH"` and sequential `lake env lean -o .lake/build/lib/lean/<module>.olean <module>.lean`. At most two Lean processes were live (one small probe alongside a sequential dependency build); final verification used one. No sub-agents, `lake update`, Mathlib rebuild, or package-directory edits were used.

The initial/topological dependency build and final H1 module commands are in `build.log` and `final-build.log`; times are wall-clock seconds on this machine. The final H1 sequence passed:

| Module | Seconds |
|---|---|
| `AKLT.Blueprint.H1.Definitions` | 4.310 |
| `AKLT.Blueprint.H1.NodesPassage` | 3.527 |
| `AKLT.Blueprint.H1.NodesLeaf` | 3.518 |
| `AKLT.Blueprint.H1.NodesReduction` | 3.564 |
| `AKLT.Blueprint.H1.NodesPauli` | 4.552 |
| `AKLT.Blueprint.H1.NodesStructure` | 4.576 |
| `AKLT.Blueprint.H1.NodesSector` | 3.548 |
| `AKLT.Blueprint.H1.NodesCertificate` | 3.357 |
| `AKLT.Blueprint.H1.Assembly` | 3.608 |
| `AKLT.Blueprint.H1.All` | 3.382 |
| `AKLT.Blueprint.H1.Audit` | 3.474 |

Final H1 total: 41.416 seconds. All 67 closure checks and 25 theorem audits passed. A source scan found no forbidden declarations, unchecked computation, effects, or global instance parameters. The only final H1 diagnostic is a style suggestion on the finite Pauli calculation; no proof holes or errors remain.

## ORCH-SUMMARY

- Delivered 11 Lean modules in AKLT/Blueprint/H1, 67 closed nodes, 25 proved exports, and complete metadata/audits.
- All requested analytic Top targets have checked assemblies. gramResidual is proved outright; seven immediate nodes and one helper are proved.
- Open names below are in namespace AKLT.Blueprint.H1 (exact identifiers):
- NodesCertificate: H1FiniteDataStatementV2.
- NodesLeaf: CoveredSlotEnumerationStatement, CornerMeanBoundsStatement, NormalizedMeanFactorStatement.
- NodesPassage: PassageSiteMomentsStatement, PassageFubiniStatement, PassageNetworkPositiveStatement, PassageNextLowerBoundStatement, OriginalDegreeStatement, OriginalFactorStructureStatement, OriginalRawEvaluationStatement, MomentContractionStatement, MomentCovarianceTransferStatement, ContractionAffineStatement, ContractionSupportStatement.
- NodesPauli: BlochAlgebraStatement, BlochPositivityStatement, PauliExpansionStatement, PauliProductTraceStatement, InversionPolynomialStatement, ProductDensityPositiveStatement, TraceProductPositiveStatement.
- NodesReduction: ReducedDegreeStatement, ReducedFactorStructureStatement, PeripheralGeometryStatement, PeripheralFubiniStatement, PeripheralAssignmentStatement, BallChordStatement, AffineEvaluationStatement, ProductBallNonnegativeStatement, DifferenceStructureStatement.
- NodesSector: SectorSpinStableStatement, SectorWeightBasisStatement, SpanWeightLatticeStatement, SpinAdjointStatement, SpinCommutatorStatement, WeightLadderTransferStatement, CommonWeightEigenvectorStatement, LadderWalkStatement, PositiveSpectrumStatement.
- NodesStructure: PauliHermitianStatement, ReflectionParityStatement, PauliRealityStatement, InversionCovarianceStatement, AdjointPauliCoordinatesStatement, AdjointPauliOrthogonalStatement, PauliRotationTransferStatement, CayleyTensorCommutationStatement, TensorLinearCoefficientStatement, SpinGeneratorTransferStatement, MomentPauliInterchangeStatement, PairExpansionFromRealizationStatement, UnitPairSupportStatement, EqualPairExchangeStatement, PairExpansionTransferStatement.
- New rule: all future leaf proofs, including checker soundness, get their first attempt from a different, cheaper model; existing proofs are retained and inventoried in proof-ownership.json.
- Exact declarations are in declarations.md; routes, prerequisites and per-leaf traps are in leaves.json.
- The 55 open names above are 54 mathematical assignments plus the external H1FiniteDataStatementV2 handoff.
- Orchestrator must pass that V2 existence contract to the data owner, or adopt CertificateStatementV2 (soundness plus data coverage).
- Existing IntegerCheckStatement and CertificateStatement provide soundness implications, not witness existence; H1 is conditional on the explicit V2 input.
- Data must cover every corrected pattern at 961/1000 or 187/200, with justified denominators, inversions and regenerated sector witnesses.
- External certificate proof must use effective D-pair signs before invoking an orthogonal direct sum; unused signs duplicate spaces.
- Proof-size estimates are provisional; the external data input requires independent kernel-check shards.
- No shared files changed; no full certificate dataset or completed H1 proof is claimed.
- All builds/closure checks passed. All 25 audits report only propext, Classical.choice and Quot.sound.
