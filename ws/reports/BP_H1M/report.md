STATUS: COMPLETE

The blueprint is retargeted to the merged ARCH_0 statement layer. All 11 pre-existing H1 Lean files, including every old leaf file and every existing proof, are byte-identical. New facts are statements only; the 15 new proved exports are assemblies or reuse bridges. The current entry point is [AllV2.lean](/home/ubuntu/aklt/wt/BP_H1M/AKLT/Blueprint/H1/AllV2.lean).

## Adaptation

The Appendix D referee report [REF2_7](/home/ubuntu/aklt/reports/REF2_7/report.md) is **SOUND**, with no critical, major or minor findings. The changes here address the Lean scope repairs F2/F3/F4 and shared handoffs A1/A2 in [stmt-fix.md](/home/ubuntu/aklt/reports/ARCH_0/stmt-fix.md). Section 8's numerical H1 gap remains explicit; this delivery does not discharge certificate data.

| Old target / handoff | Repaired target / handoff | Changed or new leaves |
|---|---|---|
| `Top.IntegratePassageStatement` | Same target | None; frozen leaves and assembly reused. |
| `Top.LeafStatement` | Same target | None; frozen local mean/radius leaves reused. |
| `Top.ReduceStatement` (rational c) | `Top.ReduceStatementV2` (every real c) | `RationalEmbeddingStructureStatementV2`, `RationalEmbeddingEvaluationStatementV2`, `DifferenceStructureStatementV2`, `DifferenceEvaluationStatementV2`, `AffineEvaluationStatementV2`. |
| `Top.InversionStatement` (rational, 20 tokens) | `Top.InversionStatementV2` (real coefficients, arbitrary finite n) | `PauliExpansionStatementV2`, `PauliProductTraceStatementV2`, `InversionPolynomialStatementV2`, `ProductDensityPositiveStatementV2`, `InversionBallStatementV2`. |
| `Top.OperatorStructureStatement` (rational c) | `Top.OperatorStructureStatementV2` (every real c) | `RealDifferencePauliInterpolationStatementV2`, `OperatorStructureLinearCombinationStatementV2`; the rational structural proof remains a supporting assembly. |
| `Top.SectorStatement` | Same target | None. Both parities, inherited inner product and eigenvalue-set claim unchanged. |
| `Top.GramResidualStatement` | Same target | None. Existing proved Gen/Gram reuse bridge retained. |
| H1-local `H1FiniteDataStatementV2`, `SectorWitnesses` | Shared `Top.H1FiniteDataStatementV2`, `Defs.H1SectorWitnesses` | Private data leaf superseded by shared external data contract; transparent aliases, no new fact. |
| H1-local `CertificateStatementV2` | Shared `Top.CertificateStatementV2` | Package alias; existing mathematical data predicate is definitionally compatible. |
| `Top.H1TheoremStatement` / `Top.H1Statement` | Same semantic targets, using shared data input | No analytic change; shared-certificate assembly bridges added. |
| `Top.InputsStatement` | `Top.InputsStatementV2` | No local numerical leaf. The shared H1 data and other lanes' designated automaton/corrected stationary checks stay explicit. |
| `Top.mainV2_of_parts` | `Top.mainV2_of_partsV2` | `main_of_shared_partsV2` passes the repaired package to the shared proved assembly. Other lanes' closed inputs remain hypotheses. |

### Open leaves and status changes

All names in the next table are in `AKLT.Blueprint.H1` except the explicitly qualified shared Top data contract. Every changed leaf has a fresh name ending in `V2`; the original definitions were not edited.

| New leaf | Label | Difficulty | Ownership |
|---|---|---|---|
| `PauliExpansionStatementV2` | `d:Pauli / l:inversion` | medium | cheaper-model first attempt |
| `PauliProductTraceStatementV2` | `l:inversion` | medium | cheaper-model first attempt |
| `InversionPolynomialStatementV2` | `l:inversion` | medium | cheaper-model first attempt |
| `ProductDensityPositiveStatementV2` | `l:inversion` | hard | cheaper-model first attempt |
| `InversionBallStatementV2` | `l:inversion` | easy | cheaper-model first attempt |
| `RationalEmbeddingStructureStatementV2` | `c:reduce` | easy | cheaper-model first attempt |
| `RationalEmbeddingEvaluationStatementV2` | `c:reduce` | easy | cheaper-model first attempt |
| `DifferenceStructureStatementV2` | `c:reduce` | medium | cheaper-model first attempt |
| `DifferenceEvaluationStatementV2` | `c:reduce` | easy | cheaper-model first attempt |
| `AffineEvaluationStatementV2` | `c:reduce` | medium | cheaper-model first attempt |
| `RealDifferencePauliInterpolationStatementV2` | `l:Ostruct` | medium | cheaper-model first attempt |
| `OperatorStructureLinearCombinationStatementV2` | `l:Ostruct` | medium | cheaper-model first attempt |
| `AKLT.Blueprint.Top.H1FiniteDataStatementV2` | `t:H1 / p:certificate` | hard | external data owner |

`leaves.json` contains **68 records**: all 55 old records are explicitly marked `kept` (50) or `superseded` (5), followed by 12 new mathematical leaves and the new shared external-data record. There are **63 current open obligations**: 62 mathematical leaves and one external finite-data contract. `leaves-v2-active.json` excludes superseded history. Each record includes its exact closed Lean declaration, module, label, difficulty, mathematical/library prerequisites, proof route, ownership policy and seven trap checks.

| Superseded old leaf | Replacement |
|---|---|
| `AKLT.Blueprint.H1.H1FiniteDataStatementV2` | `AKLT.Blueprint.Top.H1FiniteDataStatementV2` |
| `AKLT.Blueprint.H1.PauliExpansionStatement` | `AKLT.Blueprint.H1.PauliExpansionStatementV2` |
| `AKLT.Blueprint.H1.PauliProductTraceStatement` | `AKLT.Blueprint.H1.PauliProductTraceStatementV2` |
| `AKLT.Blueprint.H1.ProductDensityPositiveStatement` | `AKLT.Blueprint.H1.ProductDensityPositiveStatementV2` |
| `AKLT.Blueprint.H1.AffineEvaluationStatement` | `AKLT.Blueprint.H1.AffineEvaluationStatementV2` |

`DifferenceStructureStatement` and `InversionPolynomialStatement` remain **kept** even though wider V2 nodes exist: the unchanged rational operator assembly still needs them. The interpolation bridge then reaches the real threshold. All other kept old statements likewise retain their exact bodies and existing trap checks. Proved old nodes and intermediate/package dispositions are recorded separately in `nodes-adaptation.json`; no previously proved leaf is reopened or rewritten.

### Why the new assemblies cover the repaired scope

Reduction embeds the exact rational current/next polynomials into the real coefficient ring before forming the real-c difference. The old common positive K and the same ball vectors work for every real c; they do not depend on c. Separate-affine interpolation on balls reuses the old finite-product leaf, with a real-coefficient evaluation leaf. No real threshold is rounded or converted to a rational one.

Inversion quantifies every natural n and real polynomial, so irrational constants and more than 20 possible tokens are allowed. Its trace expansion, sign cancellation and product-density positivity have new open leaves; the old 2-by-2 Bloch identities, existing one-slot trace proof and unrestricted finite-index PSD trace bound are reused. Both n=0 and an empty active subset J are explicit cases.

For operator structure, real linearity gives the exact identity

```text
M_real(c) = (2 - 3c) M_rat(1/3) + (3c - 1) M_rat(2/3).
```

The rational structural theorem applies at 1/3 and 2/3, both strictly inside (0,1). Hermiticity, entrywise reality, all commutators and fixed-pair support are real linear in the operator. These are the only properties transferred: there is no positivity assertion in `OperatorStructureAtV2`, and no claim that interpolation preserves PSD. Weights may be negative. This reduces the real structural adaptation to two open leaves rather than duplicating the entire rational Pauli-symmetry proof. An exact Python polynomial prototype verifies the two scalar identities; it is explicitly not a Lean proof, and both leaves remain open.

### Exported assemblies

All exports below are in `AKLT.Blueprint.H1`; their exact full signatures are in [declarations-v2.md](/home/ubuntu/aklt/reports/BP_H1M/declarations-v2.md). Every input at an assembly boundary is a closed Prop.

| Assembly | Conclusion / role |
|---|---|
| `rationalPartitionsStructure_of_nodesV2` | Extract the rational current/next structure from unchanged moment/contraction leaves. |
| `reducedStructure_of_nodesV2` | Assemble the real difference structure from embedding and real scalar-combination leaves. |
| `reduce_of_nodesV2` | `Top.ReduceStatementV2`. |
| `inversion_of_nodesV2` | `Top.InversionStatementV2`. |
| `operatorStructure_of_legacyV2` | Real-threshold target from the rational structural contract and two new transfer leaves. |
| `operatorStructure_of_nodesV2` | Full leaf-facing `Top.OperatorStructureStatementV2`, calling the frozen rational assembly internally. |
| `h1Theorem_of_shared_partsV2` | `Top.H1TheoremStatement` from shared integer/certificate/data contracts. |
| `h1_of_shared_partsV2` | `Top.H1Statement` from those same shared contracts. |
| `h1_of_shared_certificateV2` | `Top.H1Statement` from shared `Top.CertificateStatementV2`. |
| `inputs_of_shared_partsV2` | Exactly `Top.InputsStatementV2`, retaining H1 data and both designated/corrected external checks. |
| `main_of_shared_partsV2` | Conditional `AKLT.Challenge.MainStatementV2` via `Top.mainV2_of_partsV2`. |
| `integratePassage_of_nodesV2` | Reuse unchanged `Top.IntegratePassageStatement` assembly. |
| `leaf_of_nodesV2` | Reuse unchanged `Top.LeafStatement` assembly. |
| `sector_of_nodesV2` | Reuse unchanged `Top.SectorStatement` assembly. |
| `gramResidualV2` | Reuse the already proved `Top.GramResidualStatement`. |

`OtherInputPartsV2` is only the closed conjunction supplied by the other lanes: H2, H3, both fixed-rate comparisons, `Top.Automaton10StatementV2`, and `Top.StationaryCheckStatementV2`. No other lane's theorem or data assertion was silently proved here. `SharedSectorWitnessesV2`, `SharedH1FiniteDataV2` and `SharedCertificateV2` alias the repaired shared definitions rather than introduce another certificate model.

### Referee findings and fidelity limits

- **Appendix D (REF2_7):** all mathematical statements and certificate implications are sound. The exact positive scale remains 15 D0 q; the rational certificate matrices remain Hermitian-form matrices in the unnormalized integer bases. Neither shared reconstruction nor integer witnesses need alteration for the new real-scope analytic targets.
- **Section 8 (REF2_6):** missing exhaustive local representation/inversion records and witness checks still prevent an unconditional H1 claim. `Top.H1FiniteDataStatementV2` is therefore an explicit external open input, and `Top.InputsStatementV2` carries it visibly. Neither enumeration counts nor this blueprint certify those data.
- **Section 7 / Appendix C boundaries:** I read the findings on non-arrival neighbour pairs in closure, the short-order domain, increasing path index within types plus the long-trail qualification, and terminal-data pullback in stopped quotient sums. These are Rec/H3 obligations, not assumptions used inside any H1 analytic leaf. The H1-to-global wrapper retains `Top.RecStatement` and the repaired stationary/automaton inputs as explicit hypotheses; it does not bypass those findings or assert that their proofs are complete.
- **Effective signs:** `EffectiveSectorSignsV2` is exactly the subtype cut out by shared `Defs.EffectiveExchangeSigns`. All-sign certificate checks still permit duplicates. Any external orthogonal-decomposition proof must use effective signs before claiming distinct sectors are orthogonal. No new normalization/orthogonality theorem was assumed.
- **Representation order:** unchanged reduced integrands retain the passage spin and contract it with the other spins. ARCH_0 confirms this is mathematically valid; no need to rewrite the frozen Fubini or degree leaves.
- **No new defect:** no additional counterexample or required repair to Top/Defs was found during adaptation. Legacy rational interfaces remain true supporting specializations, and the three V2 targets now have the wider paper-facing scopes.

### Frozen sources and proof ownership

All 11 pre-existing H1 source hashes match the before-adaptation snapshot. In particular, the seven old leaf files are byte-identical: `NodesPassage.lean`, `NodesLeaf.lean`, `NodesReduction.lean`, `NodesPauli.lean`, `NodesStructure.lean`, `NodesSector.lean`, and `NodesCertificate.lean`. `Definitions.lean`, `Assembly.lean`, `All.lean` and `Audit.lean` are also unchanged. See [adaptation-preservation.json](/home/ubuntu/aklt/reports/BP_H1M/adaptation-preservation.json).

New files are `NodesV2Reduction.lean`, `NodesV2Pauli.lean`, `NodesV2Structure.lean`, `NodesV2Handoff.lean`, `AssemblyV2.lean`, `AllV2.lean` and `AuditV2.lean`. All new mathematical leaves, even the short map/evaluation and norm facts, are unproved. Their first proof attempt must come from a different, cheaper model. No leaf proof or checker-soundness proof was attempted or written in this round. The 15 new proved exports are assemblies/reuse bridges only.

The retained first-round leaf proofs are `activeStatuses`, `passageSubtraction`, `differenceEvaluation`, `singlePauliTrace`, `inversionBall`, `pairTokensDistinct`, and `centralWeightHalf`; `reducedStatuses` is the retained auxiliary fact and `gramResidual` the retained Gram reuse bridge. Their exact statements and 25-proof inventory remain in [proof-ownership.json](/home/ubuntu/aklt/reports/BP_H1M/proof-ownership.json). The 15 new assembly signatures and policy are in [proof-ownership-adaptation.json](/home/ubuntu/aklt/reports/BP_H1M/proof-ownership-adaptation.json).

### Trap checks

Full per-new-leaf checks are in [trap-check-v2.md](/home/ubuntu/aklt/reports/BP_H1M/trap-check-v2.md) and each new manifest entry. Old checks remain intact. New highlights:

- Whole-vector degree is retained; coordinatewise multiaffineness would not suffice. Support inclusion, not equality, is the needed map/subtraction fact.
- The real polynomial may have irrational coefficients. Only exact Q-to-R-to-C embeddings are used; no real-to-rational cast or rational approximation is introduced.
- Arbitrary n, n=0, J empty and unused tokens are allowed in inversion. An empty tensor is one-dimensional with density [1]. Zero-dimensional Gram tests are a different empty case.
- New inversion algebra is stronger than the public I-subset-J premise, while the assembled public statement keeps that premise exactly.
- Interpolation coefficients can vanish or be negative. Structural transfer contains no positivity claim and divides by no variable.
- All new statements are closed; every changed statement has a new name ending in V2. No additional leaf proposition is used as a hypothesis inside a new leaf.
- There are no unguarded natural subtractions, variable denominators or dropped section instances. The one guarded coordinate subtraction is inherited unchanged from `pauliCoordinate`.

### Builds, source checks and #print axioms

Toolchain is Lean 4.35.0-rc2 with pinned Mathlib 065356127b. The full repaired shared dependency chain and all frozen H1 imports were rebuilt sequentially. The additive modules were then compiled with `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -o <olean> <source>`. At most one Lean process ran at a time. No sub-agent, package edit, Mathlib build or lake update was used.

Commands and timings are in [adaptation-build.log](/home/ubuntu/aklt/reports/BP_H1M/adaptation-build.log) and [adaptation-build-times.json](/home/ubuntu/aklt/reports/BP_H1M/adaptation-build-times.json). Latest additive-module times:

| Module | Seconds | Result |
|---|---:|---|
| `NodesV2Reduction` | 4.057 | PASS |
| `NodesV2Pauli` | 4.085 | PASS |
| `NodesV2Structure` | 4.173 | PASS |
| `NodesV2Handoff` | 3.971 | PASS |
| `AssemblyV2` | 4.096 | PASS |
| `AllV2` | 3.558 | PASS |
| `AuditV2` | 3.708 | PASS |

The seven additive modules took 27.648 seconds. All recorded dependency/module builds passed. AuditV2 checks 18 new closed Prop expressions and prints the dependencies of all 40 exported H1 theorems (25 retained, 15 new). The unchanged legacy audit still checks its 67 statement definitions. Every printed dependency is allowed. Exact current output follows; raw closure/audit output is [axioms-v2.txt](/home/ubuntu/aklt/reports/BP_H1M/axioms-v2.txt).

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
'AKLT.Blueprint.H1.rationalPartitionsStructure_of_nodesV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.reducedStructure_of_nodesV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.reduce_of_nodesV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.inversion_of_nodesV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.operatorStructure_of_legacyV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.h1Theorem_of_shared_partsV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.h1_of_shared_partsV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.h1_of_shared_certificateV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.inputs_of_shared_partsV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.main_of_shared_partsV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.integratePassage_of_nodesV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.leaf_of_nodesV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.sector_of_nodesV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.gramResidualV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1.operatorStructure_of_nodesV2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Deliverable pointers

- Current Lean entry: [AllV2.lean](/home/ubuntu/aklt/wt/BP_H1M/AKLT/Blueprint/H1/AllV2.lean); proved implications: [AssemblyV2.lean](/home/ubuntu/aklt/wt/BP_H1M/AKLT/Blueprint/H1/AssemblyV2.lean); audits: [AuditV2.lean](/home/ubuntu/aklt/wt/BP_H1M/AKLT/Blueprint/H1/AuditV2.lean).
- Manifest with all historical statuses: [leaves.json](/home/ubuntu/aklt/reports/BP_H1M/leaves.json); active only: [leaves-v2-active.json](/home/ubuntu/aklt/reports/BP_H1M/leaves-v2-active.json); new only: [new-leaves-v2.json](/home/ubuntu/aklt/reports/BP_H1M/new-leaves-v2.json).
- Exact V2 statements/signatures: [declarations-v2.md](/home/ubuntu/aklt/reports/BP_H1M/declarations-v2.md); retained legacy statements/signatures: [declarations.md](/home/ubuntu/aklt/reports/BP_H1M/declarations.md).
- Frozen-source and old-node statuses: [adaptation-preservation.json](/home/ubuntu/aklt/reports/BP_H1M/adaptation-preservation.json) and [nodes-adaptation.json](/home/ubuntu/aklt/reports/BP_H1M/nodes-adaptation.json).
- The first-round node table, route details and diagnostics remain archived in [report-before-adaptation.md](/home/ubuntu/aklt/reports/BP_H1M/report-before-adaptation.md). The shared layer now repairs the missing existence interface described there, while its numerical inhabitance remains open.

## ORCH-SUMMARY

- Adaptation complete: seven additive Lean modules, 12 new unproved mathematical leaves, one shared external-data record, and 15 proved assemblies.
- All 11 pre-existing Lean files, including all seven old leaf files and all existing proofs, are byte-identical.
- Manifest: 50 old leaves kept, five superseded, 13 new records; 63 current open obligations (62 mathematical + one external data contract).
- New local names below are in AKLT.Blueprint.H1:
- NodesV2Reduction: RationalEmbeddingStructureStatementV2, RationalEmbeddingEvaluationStatementV2, DifferenceStructureStatementV2, DifferenceEvaluationStatementV2, AffineEvaluationStatementV2.
- NodesV2Pauli: PauliExpansionStatementV2, PauliProductTraceStatementV2, InversionPolynomialStatementV2, ProductDensityPositiveStatementV2, InversionBallStatementV2.
- NodesV2Structure: RealDifferencePauliInterpolationStatementV2, OperatorStructureLinearCombinationStatementV2.
- Shared external data: AKLT.Blueprint.Top.H1FiniteDataStatementV2; the private old data leaf is superseded.
- Exact kept old names below are in AKLT.Blueprint.H1:
- NodesPassage: PassageSiteMomentsStatement, PassageFubiniStatement, PassageNetworkPositiveStatement, PassageNextLowerBoundStatement, OriginalDegreeStatement, OriginalFactorStructureStatement, OriginalRawEvaluationStatement, MomentContractionStatement, MomentCovarianceTransferStatement, ContractionAffineStatement, ContractionSupportStatement.
- NodesLeaf: CoveredSlotEnumerationStatement, CornerMeanBoundsStatement, NormalizedMeanFactorStatement.
- NodesReduction: ReducedDegreeStatement, ReducedFactorStructureStatement, PeripheralGeometryStatement, PeripheralFubiniStatement, PeripheralAssignmentStatement, BallChordStatement, ProductBallNonnegativeStatement, DifferenceStructureStatement.
- NodesPauli: BlochAlgebraStatement, BlochPositivityStatement, InversionPolynomialStatement, TraceProductPositiveStatement.
- NodesStructure: PauliHermitianStatement, ReflectionParityStatement, PauliRealityStatement, InversionCovarianceStatement, AdjointPauliCoordinatesStatement, AdjointPauliOrthogonalStatement, PauliRotationTransferStatement, CayleyTensorCommutationStatement, TensorLinearCoefficientStatement, SpinGeneratorTransferStatement, MomentPauliInterchangeStatement, PairExpansionFromRealizationStatement, UnitPairSupportStatement, EqualPairExchangeStatement, PairExpansionTransferStatement.
- NodesSector: SectorSpinStableStatement, SectorWeightBasisStatement, SpanWeightLatticeStatement, SpinAdjointStatement, SpinCommutatorStatement, WeightLadderTransferStatement, CommonWeightEigenvectorStatement, LadderWalkStatement, PositiveSpectrumStatement.
- AssemblyV2 derives ReduceStatementV2, InversionStatementV2 and OperatorStructureStatementV2 and reuses the unchanged targets.
- Shared certificate/data inputs derive H1, InputsStatementV2, and a conditional main result via mainV2_of_partsV2.
- Rational operator structure is reused at 1/3 and 2/3 through real linearity; no positivity is interpolated.
- No numerical certificate coverage, witness dataset, or checker soundness is newly proved. External H1/H3 data obligations remain open.
- Use shared effective D-pair signs for an orthogonal decomposition; duplicate all-sign checks are harmless.
- Rec/H3 own the other referee statement repairs; those contracts remain explicit inputs here.
- All builds passed and all 40 theorem audits use only propext, Classical.choice and Quot.sound.
- First attempts at every new leaf proof, even short ones and soundness lemmas, belong to a different, cheaper model; zero new leaf proofs were attempted.
