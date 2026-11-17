STATUS: COMPLETE

Delivered the closing implication and interface audit. The unconditional headline remains dependent on the separately owned leaf and certificate proofs; no such proof was attempted here.

## Files and exported statement

- [Skeleton.lean](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/Skeleton.lean): exactly one exported theorem, `AKLT.Final.mainV2_of_open`.
- [Audit.lean](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/Audit.lean): dependency-printing commands only; no additional theorem.
- [gen_final.py](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/gen_final.py): inventories the current tree, reports missing proofs, and validates and writes `AKLT/Final/Main.lean` when complete.
- [inventory.json](inventory.json): one entry per hypothesis, in application order, with Lean name, kind, owner, source-proof availability, selected proof, candidates, scheduler state, and whether the argument is explicitly referenced in the assembly body.
- [statement.txt](statement.txt): the complete, exact 420-binder exported statement.
- [missing.txt](missing.txt): every currently missing hypothesis, with its exact Lean name.
- [test_generator.py](test_generator.py), [generator-tests.log](generator-tests.log), [build.log](build.log), [axioms.log](axioms.log), and [generator-run.log](generator-run.log): reproducible validation and logs.

The statement is the explicit curried implication

```text
AKLT.Final.mainV2_of_open : P₁ → … → P₄₂₀ → AKLT.Challenge.MainStatementV2
```

Here the ordered `Pᵢ` are exactly the individual closed propositions in `statement.txt` and `inventory.json`. There is no aggregate open-parts assumption, free mathematical parameter, extra rate assumption, uniqueness assumption, H2 assumption, or bridge assumption.

## Hypothesis inventory

The current campaign map contains 417 active mapped obligations. Of these, 416 are analytic leaves and `H1M068` is the certificate obligation `AKLT.Blueprint.Top.H1FiniteDataStatementV2`. All 417 occur individually and exactly once. Three further certificate contracts give 420 hypotheses in total:

1. `AKLT.Blueprint.Top.CertificateStatement` (H1 certificate soundness).
2. `AKLT.Blueprint.Top.Automaton10StatementV2` (the designated archive quotient).
3. `AKLT.Blueprint.Top.StationaryCheckStatementV2` (the corrected passing tables and prefix ceilings).

The H1 contract `AKLT.Blueprint.Top.CertificateStatementV2` is definitionally `CertificateStatement ∧ H1FiniteDataStatementV2`. Its conjuncts are separate arguments to avoid duplicating the mapped `H1M068` obligation. The proof reconstructs this exact V2 package for `H1.inputs_of_shared_partsV2`. Certificate soundness remains an explicit external obligation; this audit does not claim that the H1 structural leaves prove it.

| Owner | Leaves | Certificates | Proof sources found | Missing | Arguments referenced in assembly body |
|---|---:|---:|---:|---:|---:|
| Q | 61 | 0 | 37 | 24 | 61 |
| Gap | 58 | 0 | 39 | 19 | 37 |
| Win | 74 | 0 | 0 | 74 | 74 |
| Mom | 33 | 0 | 25 | 8 | 31 |
| Rec | 93 | 0 | 15 | 78 | 41 |
| H1 | 62 | 2 | 35 | 29 | 2 |
| H3 | 35 | 2 | 33 | 4 | 37 |
| **Total** | **416** | **4** | **184** | **236** | **283** |

There are **zero bridge hypotheses**. Of the missing hypotheses, **232 are leaves and four are certificates**. Source-proof existence means a public, closed proof declaration was found in the tree, not that the scheduler reports completion. The 184 candidates are exactly the canonical `AKLT/W/<KEY>/Main.lean` sources present in this worktree. The inventory records `source_found_not_rechecked`: this audit did not rebuild all 184 leaf proofs. The real Lean smoke test rechecked `AKLT.W.Q001.main`; complete generator runs recheck every selected proof before publication.

The full checklist intentionally has 137 arguments not referenced in the assembly body: 21 Gap, 2 Mom, 52 Rec, and 62 H1 leaves. The supplied assemblies use a strict subset of the campaign checklist; in particular, the permitted H1 certificate handoff already contains its pointwise soundness conclusion. These retained hypotheses satisfy the requested full-leaf interface and remain prerequisites of generation. The inventory's reference flag is a syntactic use flag, not a claim of a minimal logical dependency set.

The current map already removes the replaced legacy leaves. In particular, the old Rec local-mixture, covered-ratio, covered-lower, one-point, and closure contracts are not reintroduced. The H1 rational leaves still consumed by its V2 development remain on the checklist, alongside the new real-coefficient leaves. All thirty H3 analytic leaves and its five adaptation leaves remain present. The generator rejects an added, removed, or renamed active leaf that no longer matches the frozen skeleton; scheduler-state changes alone do not establish proof availability.

## Interface audit and bridge list

**Bridge list: empty.** Every boundary actually used in the closing implication elaborates against the shared contract. No missing boundary was replaced by a hypothesis.

| Boundary | Discharge inside `mainV2_of_open` |
|---|---|
| Mom → Q and Win | `Mom.all_of_leaves` produces exactly `Top.MomentsStatement`, `FiniteFactsStatement`, `ThreeFactorMeanStatement`, and `ExactStatement`. |
| Uniqueness → TorusKernel → Q, Gap, Top | The proved `AKLT.W.UNIQ_TOP.torusKernel`, which imports `AKLT.Uniq.uniqueness`, supplies the shared `Top.TorusKernelStatement` directly. |
| Q → Win and Gap | `Q.allTargets_of_leaves` assembles the frame, tight, star, QD, and plane-energy contracts from Mom, TorusKernel, and its leaves. |
| Win → Gap | `Win.shellGeometry_of_leaves` supplies exactly `Top.ShellGeometryStatement`. |
| Win → Top | `Win.cutMOS_of_leaves` consumes the shared Mom/Q outputs and produces exactly `Top.CutMOSStatement`. |
| Gap → Top | `Gap.mainW_of_parts` consumes the assembled shell geometry, Q outputs, and proved TorusKernel, producing exactly `Top.MainWStatement`. |
| Rec V2 → Top | `Rec.targets_of_leavesV2` consumes the repaired shared covered-lower leaf and supplies exactly `Top.RecStatement`. |
| H3 V2 → numerical inputs | `H3.h3_of_leaves_and_checksV2` consumes all thirty analytic leaves, five adaptation leaves, and both archive-bound checks, producing exactly `Top.H3Statement`. Existing named H3 bridge *leaves* remain kind `leaf`; none is a newly added `AKLT.Final.Bridge_*` interface gap. |
| H1 V2 and H2 → numerical inputs | `H1.inputs_of_shared_partsV2` consumes the reconstructed H1 V2 certificate, proved `AKLT.Cert.H2.h2`, and assembled H3. Both fixed rational rate comparisons are discharged by `norm_num`. |
| Shared contracts → headline | `Top.mainV2_of_partsV2` composes the assembled `InputsStatementV2`, `RecStatement`, `CutMOSStatement`, `MainWStatement`, and proved TorusKernel. |

`Top.IntegerCheckStatement` is not added as a hypothesis: the selected H1 certificate assembly directly consumes the certificate soundness and finite coverage conjuncts. No integer-check or certificate proof is claimed here.

## Kernel dependency audit

The final output of `#print axioms` is:

```text
'AKLT.Final.mainV2_of_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.UNIQ_TOP.torusKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Uniq.uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H2.h2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three permitted standard axioms occur. A source scan of the delivered Lean files found no forbidden declaration, tactic, effectful command, or kernel-check bypass. `Skeleton.lean` disables only the unused-variable linter locally, since the full checklist is intentional. Kernel checking and heartbeat limits are unchanged.

## Commands, timings, and generator behavior

Run from `/home/ubuntu/aklt/wt/ARCH_FINAL`, with `PATH="$HOME/.elan/bin:$PATH"`:

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -o .lake/build/lib/lean/AKLT/Final/Skeleton.olean AKLT/Final/Skeleton.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false AKLT/Final/Audit.lean
python3 AKLT/Final/gen_final.py --inventory /home/ubuntu/aklt/reports/ARCH_FINAL/inventory.json
python3 /home/ubuntu/aklt/reports/ARCH_FINAL/test_generator.py
```

| Check | Result | Elapsed |
|---|---|---:|
| Compile `Skeleton.lean` with automatic implicit variables disabled | Exit 0; permitted dependency list | 5.438 s |
| Audit closing theorem, TorusKernel, uniqueness, and H2 | Exit 0; all four dependency lists permitted | 4.057 s |
| Generate inventory and missing list | Expected exit 1; 184 found, 236 missing; no `Main.lean` written | 1.532 s |
| Generator contract tests and real Lean smoke test | Exit 0 | 21.303 s |

Generator tests cover exact map/signature membership, all 420 argument positions, detection of newly added or removed leaves, recognition of indented canonical proof declarations, explicit proof overrides, rejection of unknown or executable proof terms, the dependency allowlist, real compilation and exact proof typing, rejection of a wrong-type proof, and preservation of the absent `Main.lean` on the missing path. The positive Lean smoke test uses a transient theorem of `True`; it does not assert the campaign headline or prove a new leaf. A fully provisioned headline generation cannot yet be run because 236 inputs are absent.

The generator reads `state/lw/leaves.json` afresh and scans the tree. It can discover directly typed certificate declarations and can project the two conjuncts of a proof of the shared `Top.CertificateStatementV2`. Alternative named proofs can be supplied with `--proofs proofs.json`, for example:

```json
{
  "AKLT.Blueprint.Top.CertificateStatement": {
    "module": "AKLT.Cert.H1.Main",
    "term": "(AKLT.Cert.H1.main).1"
  }
}
```

This is a future handoff example, not a claim that this module currently exists. Unknown override keys, nonexistent modules, arbitrary tactic terms, and drift from the active checklist are rejected. On completion, project proof modules and the skeleton are compiled sequentially using `lake env lean`; their existing non-root project dependencies and external libraries are imported from the campaign's prebuilt artifacts. No package build, Mathlib build, or `lake update` is invoked. Every selected proof's dependencies and the generated theorem are checked before `Main.lean` is replaced atomically. Existing prebuilt project dependency artifacts are trusted in the same way as in the campaign build setup.

## Open issues and limits

- The exact 232 missing leaf names and four missing certificate names are in `missing.txt` and the `proof_exists: false` entries of `inventory.json`.
- The four certificate hypotheses are `AKLT.Blueprint.Top.H1FiniteDataStatementV2`, `AKLT.Blueprint.Top.CertificateStatement`, `AKLT.Blueprint.Top.Automaton10StatementV2`, and `AKLT.Blueprint.Top.StationaryCheckStatementV2`.
- `AKLT/Final/Main.lean` is deliberately absent until every checklist hypothesis has a proof. The assembly theorem itself is kernel checked and complete.
- Source existence in the inventory does not assert a fresh build of every leaf. Complete generation performs that validation; the current missing run performs discovery only.
- No files outside `AKLT/Final/` and the report directory were edited; normal compiler artifacts were written under `.lake/build`. No leaf, certificate, or bridge statement was proved. No sub-agents were used. At most two Lean processes ran concurrently during validation; generator compilation itself is sequential.

## ORCH-SUMMARY

- Delivered `AKLT.Final.mainV2_of_open : P₁ → … → P₄₂₀ → AKLT.Challenge.MainStatementV2`.
- Exact ordered statement: `statement.txt`; machine inventory: `inventory.json`.
- 417 mapped obligations: 416 leaves and the mapped H1 finite-data certificate.
- Three additional certificate contracts; 420 hypotheses total.
- Bridges: none; all consumed inter-part contracts compose without extra hypotheses.
- H1 `CertificateStatementV2` is split into soundness plus mapped finite-data coverage, with no duplicate argument.
- Dependency audit: `[propext, Classical.choice, Quot.sound]` only.
- Proof sources found: 184; missing: 232 leaves plus four certificates.
- Exact missing leaf and certificate names: `missing.txt` and `inventory.json`.
- Open certificate: `AKLT.Blueprint.Top.H1FiniteDataStatementV2`.
- Open certificate: `AKLT.Blueprint.Top.CertificateStatement`.
- Open certificate: `AKLT.Blueprint.Top.Automaton10StatementV2`.
- Open certificate: `AKLT.Blueprint.Top.StationaryCheckStatementV2`.
- Full requested checklist retained; 137 arguments are unused by current assemblers.
- Inventory reports source discovery, not fresh validation of all 184 leaf proofs.
- `gen_final.py` validates types and dependencies, then writes `AKLT.Final.main` atomically when all inputs exist.
- `Main.lean` is absent; full headline generation remains untested until the missing proofs arrive.
- Prebuilt non-root dependencies are reused; no Mathlib/package build; no proof work outside plumbing.
- Orchestrator: merge remaining proof sources, provide named certificate proofs (or overrides), and rerun the generator.

## round 2

STATUS: COMPLETE

All 416 analytic leaves are now supplied by their merged canonical proofs. The round 2 deliverable is [Conditional.lean](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/Conditional.lean), containing exactly one named theorem:

```lean
AKLT.Final.main_of_certificates :
  AKLT.Blueprint.Top.H1FiniteDataStatementV2 →
  AKLT.Blueprint.Top.CertificateStatement →
  AKLT.Blueprint.Top.Automaton10StatementV2 →
  AKLT.Blueprint.Top.StationaryCheckStatementV2 →
  AKLT.Challenge.MainStatementV2
```

These are exactly the four certificate arguments, in their order in `mainV2_of_open`. The generated body applies `mainV2_of_open` to all 416 terms `AKLT.W.<KEY>.main` and these four hypotheses. No other certificate or bridge is an argument. `Main.lean` remains absent while the four certificate proofs are outstanding.

### Generation, build, and exact type check

The new mode writes the conditional module:

```sh
export PATH="$HOME/.elan/bin:$PATH"
python3 AKLT/Final/gen_final.py --conditional
lake build AKLT.Final.Conditional
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false AKLT/Final/ConditionalAudit.lean
```

The requested Lake build **passed in 24.931 s**. [ConditionalAudit.lean](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/ConditionalAudit.lean) contains the exact four-arrow `example`, assigned `@AKLT.Final.main_of_certificates`; the explicit `@` exposes the full argument list. That check **passed in 6.403 s**. Its printed theorem type has precisely those four hypotheses. The dependency audit is:

```text
'AKLT.Final.main_of_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**The conditional build itself is the leaf-interface recheck.** Elaboration checks each supplied leaf constant against its corresponding statement in the 420-argument application, including the leaf hypotheses that the skeleton's proof body does not reference. The generated source and the **printed, elaborated proof term both contain exactly 416 distinct canonical leaf theorems**, matching the complete active analytic-leaf set. This resolves the earlier discovery-only limitation for leaf statement types.

The worktree's existing build artifacts were supplemented with matching prebuilt artifacts from current `main`, after comparing all 848 existing project sources in the import closure byte-for-byte. Lake then built the missing `AKLT.W.GAP046.TraceHelpers`, `AKLT.W.GAP046.Main`, and `AKLT.Final.Conditional`; other imported proofs used their prebuilt artifacts. No Mathlib or package build was performed. The three fresh Lean compilations were sequential. No leaf proof source was changed.

Validation records and current inventory are under the assigned directory:

- [round2-build.log](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/round2-build.log): the successful `lake build AKLT.Final.Conditional`.
- [round2-audit.log](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/round2-audit.log): exact-type example, permitted axioms, and printed proof containing all 416 leaf references.
- [round2-generator.log](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/round2-generator.log): default discovery reports exactly four missing certificates (expected exit 1); conditional discovery succeeds (exit 0); generator tests pass.
- [round2-inventory.json](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/round2-inventory.json): 416 leaf interfaces checked in the conditional application, four certificate obligations missing, zero bridges.
- [round2-cache.json](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/round2-cache.json): artifact-restoration provenance.
- [test_gen_final.py](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/test_gen_final.py): ordered application, canonical leaf membership, exact certificate boundary, named overrides, backward compatibility, invalid-input rejection, and dependency allowlist tests.

The earlier sections and inventory are the historical round 1 snapshot. The round 2 inventory above gives the current proof availability.

### Final certificate handoff: one command

Default `Main.lean` generation retains its existing complete-proof validation and atomic publication behavior. `--proofs` now accepts a JSON filename or an inline JSON object. Keys may be the four short certificate statement names or their fully qualified Lean names. Values may be qualified proof declaration names or projections, with the declaring module discovered from the tree. The existing explicit `{"module": ..., "term": ...}` form remains supported.

Prepare `AKLT/Final/certificate_proofs.json` with the certificate owners' actual exported proof names. [certificate_proofs.example.json](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/certificate_proofs.example.json) shows the required format:

```json
{
  "H1FiniteDataStatementV2": "AKLT.Cert.H1.finiteData",
  "CertificateStatement": "AKLT.Cert.H1.certificate",
  "Automaton10StatementV2": "AKLT.Cert.Automaton10.main",
  "StationaryCheckStatementV2": "AKLT.Cert.Stationary.main"
}
```

Those values are illustrative names, not claims of existing certificate proofs; replace them with the actual names. The exact final command, from this worktree, is:

```sh
python3 AKLT/Final/gen_final.py --proofs AKLT/Final/certificate_proofs.json
```

That single command resolves all 420 arguments, checks the selected proof terms and permitted dependencies, and writes `AKLT/Final/Main.lean` with `AKLT.Final.main : AKLT.Challenge.MainStatementV2`. Both named certificate terms and full module/term objects are accepted, including projections such as `(AKLT.Cert.H1.main).1`. The conditional mode always keeps the four certificate hypotheses, even if certificate proofs later become discoverable.

### Skeleton hypotheses not used by its assembly body

For information, the following **137** hypotheses of `mainV2_of_open` are not referenced in its proof body: **21 Gap, 2 Mom, 52 Rec, and 62 H1**. This is the syntactic reference inventory from the original assembly, rather than a claim of a minimized transitive dependency set. The conditional term still supplies and type-checks every one of them. The machine-readable list is [round2-unused.json](/home/ubuntu/aklt/wt/ARCH_FINAL/AKLT/Final/round2-unused.json).

| Leaf key | Exact hypothesis statement |
|---|---|
| GAP001 | `AKLT.Blueprint.Gap.FibreNormalizationStatement` |
| GAP002 | `AKLT.Blueprint.Gap.ConditionalProjectionStatement` |
| GAP003 | `AKLT.Blueprint.Gap.ConditionalVarianceStatement` |
| GAP004 | `AKLT.Blueprint.Gap.MaximalCouplingStatement` |
| GAP005 | `AKLT.Blueprint.Gap.CouplingMarginalTVStatement` |
| GAP006 | `AKLT.Blueprint.Gap.MarginalCompletionStatement` |
| GAP007 | `AKLT.Blueprint.Gap.HammingLocalizationStatement` |
| GAP008 | `AKLT.Blueprint.Gap.CommonMinorizationStatement` |
| GAP009 | `AKLT.Blueprint.Gap.SurgeryPreservationStatement` |
| GAP010 | `AKLT.Blueprint.Gap.ConditionalPatchCouplingStatement` |
| GAP011 | `AKLT.Blueprint.Gap.FrameProductReferenceStatement` |
| GAP012 | `AKLT.Blueprint.Gap.FrameInteractionBoundsStatement` |
| GAP013 | `AKLT.Blueprint.Gap.NormalizedInteractionStatement` |
| GAP014 | `AKLT.Blueprint.Gap.SignedFrameBlockStatement` |
| GAP015 | `AKLT.Blueprint.Gap.VariationalCenteringStatement` |
| GAP016 | `AKLT.Blueprint.Gap.ProductTensorizationStatement` |
| GAP017 | `AKLT.Blueprint.Gap.DensityComparisonStatement` |
| GAP020 | `AKLT.Blueprint.Gap.HammingPathStatement` |
| GAP043 | `AKLT.Blueprint.Gap.ShellNestingStatement` |
| GAP044 | `AKLT.Blueprint.Gap.FiniteEnergyChainStatement` |
| GAP051 | `AKLT.Blueprint.Gap.TerminalRadiusStatement` |
| MOM032 | `AKLT.Blueprint.Mom.InteractionDegreeStatement` |
| MOM033 | `AKLT.Blueprint.Mom.OneSiteConditionalReductionStatement` |
| REC001 | `AKLT.Blueprint.Rec.NetworkPositiveStatement` |
| REC002 | `AKLT.Blueprint.Rec.ThreeFactorizationStatement` |
| REC003 | `AKLT.Blueprint.Rec.TwoFactorizationStatement` |
| REC006 | `AKLT.Blueprint.Rec.FreeRemovedPairStatement` |
| REC007 | `AKLT.Blueprint.Rec.LogMeanBasicStatement` |
| REC008 | `AKLT.Blueprint.Rec.LogMeanMonotoneStatement` |
| REC009 | `AKLT.Blueprint.Rec.CrudeLogEnclosureStatement` |
| REC023 | `AKLT.Blueprint.Rec.ReciprocalIntegralStatement` |
| REC026 | `AKLT.Blueprint.Rec.EightTermRemainderStatement` |
| REC029 | `AKLT.Blueprint.Rec.TipReplacementStatement` |
| REC030 | `AKLT.Blueprint.Rec.BallSlotConvexityStatement` |
| REC037 | `AKLT.Blueprint.Rec.UStepMomentStatement` |
| REC038 | `AKLT.Blueprint.Rec.DStepMomentStatement` |
| REC039 | `AKLT.Blueprint.Rec.TraceDynamicsStatement` |
| REC040 | `AKLT.Blueprint.Rec.TraceCoefficientStatement` |
| REC041 | `AKLT.Blueprint.Rec.TraceTelescopeStatement` |
| REC042 | `AKLT.Blueprint.Rec.CoordinateStepStatement` |
| REC043 | `AKLT.Blueprint.Rec.PairExpansionStatement` |
| REC044 | `AKLT.Blueprint.Rec.PairTerminalFactorStatement` |
| REC045 | `AKLT.Blueprint.Rec.PairDegreeStatement` |
| REC046 | `AKLT.Blueprint.Rec.ProductExposureStatement` |
| REC049 | `AKLT.Blueprint.Rec.NormalizeStartStatement` |
| REC050 | `AKLT.Blueprint.Rec.KeptInvariantStatement` |
| REC051 | `AKLT.Blueprint.Rec.RemovedClosureStatement` |
| REC054 | `AKLT.Blueprint.Rec.TerminalDefectStatement` |
| REC055 | `AKLT.Blueprint.Rec.SecondStartStatement` |
| REC057 | `AKLT.Blueprint.Rec.UDepartureInjectiveStatement` |
| REC058 | `AKLT.Blueprint.Rec.DiamondTwelveStatement` |
| REC060 | `AKLT.Blueprint.Rec.KernelOrderingStatement` |
| REC061 | `AKLT.Blueprint.Rec.KernelPositivityStatement` |
| REC063 | `AKLT.Blueprint.Rec.KernelSupportStatement` |
| REC068 | `AKLT.Blueprint.Rec.ShiftPowerIncrementStatement` |
| REC074 | `AKLT.Blueprint.Rec.EnvelopeOrderStatement` |
| REC075 | `AKLT.Blueprint.Rec.ProtectedDistanceFiniteStatement` |
| REC076 | `AKLT.Blueprint.Rec.PairCanonicalGeometryStatement` |
| REC077 | `AKLT.Blueprint.Rec.TraceExposureStatement` |
| REC078 | `AKLT.Blueprint.Rec.PairEnvelopeShiftStatement` |
| REC080 | `AKLT.Blueprint.Rec.ResidualTargetBoundStatement` |
| REC084 | `AKLT.Blueprint.Rec.RenewalActionStatement` |
| REC089 | `AKLT.Blueprint.Rec.LocalMixtureStatementV2` |
| REC090 | `AKLT.Blueprint.Rec.CoveredRatioStatementV2` |
| REC092 | `AKLT.Blueprint.Rec.LegacyCoverComparisonStatementV2` |
| REC093 | `AKLT.Blueprint.Rec.BoundaryExampleCoveredStatementV2` |
| REC094 | `AKLT.Blueprint.Rec.OnePointPointwiseStatementV2` |
| REC095 | `AKLT.Blueprint.Rec.OnePointSumStatementV2` |
| REC096 | `AKLT.Blueprint.Rec.CoveredClosureStatementV2` |
| REC097 | `AKLT.Blueprint.Rec.PairClosureStatementV2` |
| REC098 | `AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2` |
| REC099 | `AKLT.Blueprint.Rec.TerminalExceptionCountStatementV2` |
| REC100 | `AKLT.Blueprint.Rec.ShortKernelOrderingStatementV2` |
| REC101 | `AKLT.Blueprint.Rec.LongKernelOrderingStatementV2` |
| REC102 | `AKLT.Blueprint.Rec.StoppedQuotientSumStatementV2` |
| H1M002 | `AKLT.Blueprint.H1.CoveredSlotEnumerationStatement` |
| H1M003 | `AKLT.Blueprint.H1.CornerMeanBoundsStatement` |
| H1M004 | `AKLT.Blueprint.H1.NormalizedMeanFactorStatement` |
| H1M005 | `AKLT.Blueprint.H1.PassageSiteMomentsStatement` |
| H1M006 | `AKLT.Blueprint.H1.PassageFubiniStatement` |
| H1M007 | `AKLT.Blueprint.H1.PassageNetworkPositiveStatement` |
| H1M008 | `AKLT.Blueprint.H1.PassageNextLowerBoundStatement` |
| H1M009 | `AKLT.Blueprint.H1.OriginalDegreeStatement` |
| H1M010 | `AKLT.Blueprint.H1.OriginalFactorStructureStatement` |
| H1M011 | `AKLT.Blueprint.H1.OriginalRawEvaluationStatement` |
| H1M012 | `AKLT.Blueprint.H1.MomentContractionStatement` |
| H1M013 | `AKLT.Blueprint.H1.MomentCovarianceTransferStatement` |
| H1M014 | `AKLT.Blueprint.H1.ContractionAffineStatement` |
| H1M015 | `AKLT.Blueprint.H1.ContractionSupportStatement` |
| H1M016 | `AKLT.Blueprint.H1.BlochAlgebraStatement` |
| H1M017 | `AKLT.Blueprint.H1.BlochPositivityStatement` |
| H1M020 | `AKLT.Blueprint.H1.InversionPolynomialStatement` |
| H1M022 | `AKLT.Blueprint.H1.TraceProductPositiveStatement` |
| H1M023 | `AKLT.Blueprint.H1.ReducedDegreeStatement` |
| H1M024 | `AKLT.Blueprint.H1.ReducedFactorStructureStatement` |
| H1M025 | `AKLT.Blueprint.H1.PeripheralGeometryStatement` |
| H1M026 | `AKLT.Blueprint.H1.PeripheralFubiniStatement` |
| H1M027 | `AKLT.Blueprint.H1.PeripheralAssignmentStatement` |
| H1M028 | `AKLT.Blueprint.H1.BallChordStatement` |
| H1M030 | `AKLT.Blueprint.H1.ProductBallNonnegativeStatement` |
| H1M031 | `AKLT.Blueprint.H1.DifferenceStructureStatement` |
| H1M032 | `AKLT.Blueprint.H1.SectorSpinStableStatement` |
| H1M033 | `AKLT.Blueprint.H1.SectorWeightBasisStatement` |
| H1M034 | `AKLT.Blueprint.H1.SpanWeightLatticeStatement` |
| H1M035 | `AKLT.Blueprint.H1.SpinAdjointStatement` |
| H1M036 | `AKLT.Blueprint.H1.SpinCommutatorStatement` |
| H1M037 | `AKLT.Blueprint.H1.WeightLadderTransferStatement` |
| H1M038 | `AKLT.Blueprint.H1.CommonWeightEigenvectorStatement` |
| H1M039 | `AKLT.Blueprint.H1.LadderWalkStatement` |
| H1M040 | `AKLT.Blueprint.H1.PositiveSpectrumStatement` |
| H1M041 | `AKLT.Blueprint.H1.PauliHermitianStatement` |
| H1M042 | `AKLT.Blueprint.H1.ReflectionParityStatement` |
| H1M043 | `AKLT.Blueprint.H1.PauliRealityStatement` |
| H1M044 | `AKLT.Blueprint.H1.InversionCovarianceStatement` |
| H1M045 | `AKLT.Blueprint.H1.AdjointPauliCoordinatesStatement` |
| H1M046 | `AKLT.Blueprint.H1.AdjointPauliOrthogonalStatement` |
| H1M047 | `AKLT.Blueprint.H1.PauliRotationTransferStatement` |
| H1M048 | `AKLT.Blueprint.H1.CayleyTensorCommutationStatement` |
| H1M049 | `AKLT.Blueprint.H1.TensorLinearCoefficientStatement` |
| H1M050 | `AKLT.Blueprint.H1.SpinGeneratorTransferStatement` |
| H1M051 | `AKLT.Blueprint.H1.MomentPauliInterchangeStatement` |
| H1M052 | `AKLT.Blueprint.H1.PairExpansionFromRealizationStatement` |
| H1M053 | `AKLT.Blueprint.H1.UnitPairSupportStatement` |
| H1M054 | `AKLT.Blueprint.H1.EqualPairExchangeStatement` |
| H1M055 | `AKLT.Blueprint.H1.PairExpansionTransferStatement` |
| H1M056 | `AKLT.Blueprint.H1.PauliExpansionStatementV2` |
| H1M057 | `AKLT.Blueprint.H1.PauliProductTraceStatementV2` |
| H1M058 | `AKLT.Blueprint.H1.InversionPolynomialStatementV2` |
| H1M059 | `AKLT.Blueprint.H1.ProductDensityPositiveStatementV2` |
| H1M060 | `AKLT.Blueprint.H1.InversionBallStatementV2` |
| H1M061 | `AKLT.Blueprint.H1.RationalEmbeddingStructureStatementV2` |
| H1M062 | `AKLT.Blueprint.H1.RationalEmbeddingEvaluationStatementV2` |
| H1M063 | `AKLT.Blueprint.H1.DifferenceStructureStatementV2` |
| H1M064 | `AKLT.Blueprint.H1.DifferenceEvaluationStatementV2` |
| H1M065 | `AKLT.Blueprint.H1.AffineEvaluationStatementV2` |
| H1M066 | `AKLT.Blueprint.H1.RealDifferencePauliInterpolationStatementV2` |
| H1M067 | `AKLT.Blueprint.H1.OperatorStructureLinearCombinationStatementV2` |

### Remaining obligations and scope

Only the four certificate statements in the displayed theorem remain open. No leaf, certificate, or bridge proof was added. All author edits are under `AKLT/Final/`; this section is appended to the existing report, and compiler/cache artifacts are confined to `.lake/build`. The full unconditional generation path remains dependent on the future certificate proofs. `Skeleton.lean` and the other parts were left unchanged.

### ORCH-SUMMARY

- Round 2 complete: `AKLT.Final.main_of_certificates` is generated and built.
- Its four hypotheses, in order: `AKLT.Blueprint.Top.H1FiniteDataStatementV2`, `AKLT.Blueprint.Top.CertificateStatement`, `AKLT.Blueprint.Top.Automaton10StatementV2`, `AKLT.Blueprint.Top.StationaryCheckStatementV2`.
- Exactly one named theorem in `Conditional.lean`; no additional certificate or bridge hypotheses.
- Exact full type verified by an explicit `@` example in `ConditionalAudit.lean`.
- Axioms: `[propext, Classical.choice, Quot.sound]` only.
- The source and printed proof use exactly 416 distinct canonical leaf theorems.
- The conditional build checks all 416 leaf statement interfaces, including the 137 unused skeleton hypotheses.
- All 137 unused hypothesis names are listed above and in `AKLT/Final/round2-unused.json`.
- Matching prebuilt main artifacts were reused; only GAP046 helper/main and Conditional needed fresh compilation.
- No Mathlib/package build; no proof-source changes outside `AKLT/Final/`.
- `--proofs` accepts short/full certificate names and named terms, from a JSON file or inline object; legacy objects still work.
- Configure actual proof names in `AKLT/Final/certificate_proofs.json`; the supplied example uses illustrative names.
- Final command: `python3 AKLT/Final/gen_final.py --proofs AKLT/Final/certificate_proofs.json`.
- `Main.lean` remains absent until those four certificate proofs are supplied.
