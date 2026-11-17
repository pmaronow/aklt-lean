STATUS: PARTIAL (production source integration requires repository-wide module migration; final independent replays pending)

The splice analysis was written first, before checker implementation. The design chooses the actual-departure V3 route. The standalone finite certificate is now proved in Lean; the semantic and final assemblies are checked implications with explicit new mathematical leaves. No mathematical leaf proof is supplied.

## 1. Splice analysis

`AKLT.Blueprint.Top.H1Statement` is definitionally

```lean
AKLT.Defs.LocalPatternBound (961 / 1000) (187 / 200)
```

`LocalPatternBound cs ct` is the conjunction `0 < cs ∧ cs ≤ 1 ∧ 0 < ct ∧ ct ≤ 1` and

```lean
∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
  (if π.outgoing = .north then cs else ct) * patternNext π m ≤ patternCurrent π m
```

`Defs.patternFunctional` multiplies all twenty slots at nonremoved slot sites. In particular it keeps two artificial fields at a D corner even when that corner has two internal bonds. The written replacement only supplies physical departures, where that corner has zero external factors. There is no derivation of the old universal pattern statement in h1tree.tex. This is a scope distinction, not a disproof of that larger inequality. Choose **(b)**: keep the old statement and all old leaves, introduce actual H1, and version the consumers.

The shared matcher is **`AKLT.Defs.CoveredDepartureV2`**, not the identically named frozen `AKLT.Blueprint.Rec.CoveredDepartureV2`. The shared one matches non-tip statuses and actual internal bonds, allows prospective zero tip fields, and does not match external kept directions. `Departure.auxiliary` fixes protected sites to U; `Departure.start` puts the departure outside original S(G). Thus a physical D corner has no original pins, and present degree at most two gives its `2-k` bound. `ActualFieldCountsStatement` and `ActualRecordCoverageStatement` make the physical/template bridge explicit.

The exact new interface is in [Definitions.lean](/home/ubuntu/aklt/wt/ARCH_H1T/AKLT/Blueprint/H1T/Definitions.lean):

```lean
def H1ActualStatement : Prop :=
  ∀ a : Rec.Departure, a.D.status a.y = .U → ∀ incoming outgoing : Compass,
    a.o = a.y + outgoing.step → AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
    (localThreshold (decide (outgoing = incoming)) : ℝ) *
      (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) ≤
        a.D.partition a.τ true (fun _ => 1)
```

This is exactly the pinned partition inequality consumers need. Existing positivity converts it to the ratio bound; existing two/three-neighbour factorizations convert it to `I₂ ≥ c` and `I ≥ c J`. The free ratio bound, logarithmic-mean analysis, exceptional constant `12/5`, and kernel constants do not change.

[splice-consumers.json](splice-consumers.json) and [splice-consumers.tsv](splice-consumers.tsv) index 56 legacy declarations whose signatures or definitions mention H1 or its certificates, with exact source signatures, file/line and use. The analytic dependency chain is:

| Consumer / owner | What it uses | V3 action |
|---|---|---|
| Legacy `CoveredRatioStatement`, `CoveredIntegratedLowerStatement`; shared V2 REC090 / REC091 | Only `c Znext ≤ Zcur`, positivity and the I/J factorizations | New actual variants; remove the old pattern-mixture proof dependency |
| `Rec.ResponseTypedStatementV2` (frozen matcher), `Top.ResponseTypedStatement`, `Top.ResponseTypedStatementV2`, `TypedLeaves` / `TypedLeavesV2` | Only integrated lower bounds; all analytic enclosures independent | Shared `ResponseTypedStatementV3` and proved `responseTyped_of_leavesV3`; reuse REC004/005/034/035/036 and REC010–028 |
| Legacy unmapped one-point statements; shared REC094 / REC095 | Covered pinned step ratio, free bound, at most twelve other U departures | Actual variants, same `uncoveredCountV2`, original S(G), absent incoming bond and sum of pointwise maxima |
| REC079 `TraceKernelLengthStatement`, including `LocalInputs`, `OrderedExposure`, `LocalLogComparison` helpers | Local step ratio and typed response coefficients along the first trace | Actual variant; use REC092 to convert the frozen cover where needed; retain kernel/order and REC096/097/100/101/102 geometry |
| `FirstTermBoundStatement` | Calls the length comparison and unchanged finite-tail domination | Proved V3 assembly; no new mathematical leaf |
| REC080 `ResidualTargetBoundStatement` | Terminal auxiliary one-point estimate with the fixed protected defect | Actual variant; reuse REC098/099 for exceptions |
| REC081 `SecondTermBoundStatement` | Residual target + first-trace one-point sum | Actual variant; unchanged source constant and `q^(2*d)` |
| `Top.RecStatement`, `rec_of_leaves`, targets assemblies | Calls first/second bounds under H1; remaining renewal algebra independent | `RecStatementV3`, `RecursionLeavesV3`, proved V3 recursion assembly |
| `Top.InputsStatement` / `InputsStatementV2`; H1 input assemblies; H3 `inputs_of_leaves_and_other_partsV2` | Packages old semantic H1 and finite provenance | Bypass old packaging; obtain P directly using actual H1, unchanged H2/H3 |
| `Top.mainV2_of_parts(V2)`, `Rec.responseProperty_of_inputsV2` / `mainV2_of_blueprintV2`, H1 `main_of_shared_partsV2`, H3 `mainV2_of_H3_and_other_partsV2`, Final skeleton/conditional | Pass H1 into Rec, then consume the resulting response property | Reuse the response-to-headline closing tree in `Existing.lean` |

**Exactly seven active consumer leaves need ported proofs:**

| Old writer | New closed Prop in `AKLT.Blueprint.H1T` | Change |
|---|---|---|
| REC090 | `CoveredRatioStatementV3` | Replace H1 premise by actual H1; same ratio conclusion |
| REC091 | `CoveredIntegratedLowerStatementV3` | Replace H1 premise; same two I/J lower bounds |
| REC094 | `OnePointPointwiseStatementV3` | Replace H1 premise; same shared matcher/count and pointwise maximum |
| REC095 | `OnePointSumStatementV3` | Replace H1 premise; same tail bound |
| REC079 | `TraceKernelLengthStatementV3` | Replace H1 premise and port the three local helper interfaces |
| REC080 | `ResidualTargetBoundStatementV3` | Replace H1 premise and terminal local input |
| REC081 | `SecondTermBoundStatementV3` | Replace H1 premise and use the two V3 one-point inputs |

Their complete Lean statements are in [Consumers.lean](/home/ubuntu/aklt/wt/ARCH_H1T/AKLT/Blueprint/H1T/Consumers.lean) and [declarations.json](declarations.json). All premises/conclusions other than the H1 interface are retained. The final assembly directly needs only the REC079 and REC081 variants; the other five are their proof dependencies. REC089's old artificial-pattern mixture is bypassed. Old geometry, normalization, exception-count and ordering leaves remain reusable. No old source file was edited.

## 2. Blueprint and assemblies

Files under [AKLT/Blueprint/H1T/](/home/ubuntu/aklt/wt/ARCH_H1T/AKLT/Blueprint/H1T):

| File | Purpose |
|---|---|
| `FiniteBasic.lean`, `SpecialWeights.lean` | Small executable integer/list primitives, radii, vertices/models, means/scalars, streaming Gram rows |
| `Packed.lean` | Rational-radius moment/Pauli tables, balanced lookup, cached packed contraction, central indices, signed digits and no-carry bound |
| `Coverage.lean` | Kept masks, local consistency/product enumeration, effective corner projection, reflection, branch reducer, common record/key tree |
| `Data/` | 38 models and all integer witnesses as ordinary small definitions and list literals |
| `Finite.lean`, `Bookkeeping.lean` | Closed finite proposition, binding and shape checks, count/maximal-model diagnostics |
| `Definitions.lean` | Actual finite-sum model semantics `Z`, `Cij`, `Zcur`, `Znext`; assignments in the listed balls; actual and conditional H1 |
| `Operators.lean` | Independent rational moment contraction, full Pauli operator, integer symmetric-pair basis, actual central Hermitian form and `15qD₀` reconstruction equality |
| `Nodes.lean` | 45 closed mathematical leaf Props, with paper locator, route, difficulty and traps in docstrings |
| `Consumers.lean` | Seven consumer V3 leaves, typed V3 interface and V3 renewal interface |
| `Assembly.lean` | Checked tree, mean and actual-H1 assemblies from finite input + explicit mathematical leaves |
| `ConsumerAssembly.lean` | Checked V3 typed response, first-term and renewal assemblies |
| `Existing.lean` | Unchanged moment/quantum/window/gap/uniqueness closing tree and unchanged two-input H3 theorem; 238 existing leaf imports |
| `Final.lean` | Requested `AKLT.Final.main_of_certificates_T`, located inside the permitted directory |
| `Checks/`, `Certificates/`, `Certificate.lean` | Kernel receipts and their purely structural assembly; exported `finite_checked : H1TreeFiniteStatement` |
| `Export.lean` | Full standalone finite-receipt export root |
| `leaves.json`, `tools/` | 52-leaf dispatch catalogue; deterministic data generation, bounded build/replay and audit tools |

The catalogue uses the requested seven-field format. [declarations.json](declarations.json) additionally includes every full leaf statement and source location. Routes name proved-index declarations, particularly MOM004/005/006, MOM011/012/013, MOM018–031, H1M003/004/012/013, the generic H1M Pauli/ladder/sector leaves, REC001/002/003/092/096–102, and `AKLT.Cert.H1.packed_outer_product` / moment-contraction soundness / `AKLT.Gen.Gram.checker_sound_complex`. Reuse is through explicit forest/token adapters where the old theorem was wrapped in `PatternData.Covered`.

Paper-to-leaf map:

| h1tree.tex | Closed obligations |
|---|---|
| Definition 1.2 / Lemma 1.3 | Positive site sums, exact leaf summation, ball affinity, two-field U, one-field D and three-field U/D means |
| Definitions 1.4–1.5 | Model/data definitions and `H1TreeStatement` |
| Lemma 1.6 | Cube Bernstein positivity, exact mean polynomial, checked integer transform ⇒ each supplied mean bound |
| Lemma 1.7 | Orthogonal-coordinate estimate and degree-(4,4) coefficient soundness; both repaired radii explicit |
| Lemma 1.8 | Quadratic interval lemma and exact scalar tests ⇒ scalar model inequality |
| Definition 1.9 / Lemma 1.10 | Local tables, packed reconstruction = rational moment tensors, Gram refiner/transport, positive scaling, Hermiticity, covariance, pair support, central-sector promotion and Pauli trace evaluation |
| Proposition 1.11 | Checked 22/16 partition and `tree_of_leaves` |
| Definitions 1.12 / Lemma 1.13 | Shared-matcher realization, original-pin counts and physical D capacity |
| Lemma 1.14, step 1 | Tip reduction, including absent actual tip bonds and common positive normalizers |
| Lemma 1.14, step 2 | D zero-law split; two-bond upper D kernel; exact-one lost-endpoint case |
| Lemma 1.14, step 3(a) | Auxiliary arrival split and positive common `A_L(ξ) A_R(ξ)/12` weights |
| Lemma 1.14, step 3(b) | Opposite corner → S → surviving corner identity, producing radius 1/10 |
| Lemma 1.14, step 3(c) | Arrival-tip identity with radius 3/25 and no-tip/absent-arrival identity |
| Lemma 1.14, step 3(d) | Exact retained lower path, with guard encoded in `reduceBranch` |
| Lemma 1.14, steps 4–5 | U/D upper leaves, retained bridges, path/degree bookkeeping and isolated mean lookup |
| Lemma 1.15 | Cartesian exhaustion, effective-corner projection completeness, record/key lookup soundness and Boolean branch coverage |
| Lemma 1.16 | Path/component relabeling and radius extension, preserving laws and outgoing flags |
| Theorem 1.17 | Explicit conditional-mixture gluing obligation, then outside-sum integration to actual H1 |
| Proposition 1.18 | Seven V3 consumer tasks and checked V3 closing assemblies |

The larger remaining mathematical adapters are explicitly named `ActualRecordCoverageStatement`, `ActualMixtureSoundnessStatement`, `PackedReconstructionSoundnessStatement`, `CentralSectorPromotionStatement`, and `TensorPauliTraceStatement`. In particular the conditional gluing obligation is not declared proved merely because its individual algebraic identities are available. Its route explains the case order and common coefficients; it can be subdivided further by the proof writers if its finite-sum bookkeeping is too large for one sitting.

Repairs are preserved: no artificial D corner slots; no arbitrary two-field U replacement after an activated bridge loses an endpoint; fixed tip D neighbours retain radius 3/25; lost outgoing marks stay absent while the surviving non-outgoing pair remains in next; the lower path is retained in precisely the correlation-preserving case; formal `3R` means are only degree-two tensor encodings; radius enlargement uses separate affinity.

The main assembly signatures are:

```lean
tree_of_leaves : AssemblyLeaves → H1TreeFiniteStatement → H1TreeStatement
means_of_leaves : AssemblyLeaves → H1TreeFiniteStatement →
  (∀ r ∈ meanRows, MeanBound r) ∧ (∀ r ∈ specialRows, SpecialMeanBound r)
actual_of_leaves : AssemblyLeaves → H1TreeFiniteStatement → H1ActualStatement
firstTermBound_of_leavesV3 : TraceKernelLengthStatementV3 →
  Rec.FiniteKernelTailDominationStatement → Rec.EnvelopeBoundsStatement → FirstTermBoundStatementV3
rec_of_leavesV3 : Top.MThetaStatement → Rec.BoundedRenewalStatement →
  RecursionLeavesV3 → RecStatementV3
responseTyped_of_leavesV3 : Top.ResponseStatement → Top.LogMeanBoundsStatement →
  TypedLeavesV3 → ResponseTypedStatementV3
main_of_response_T : Top.PStatement → AKLT.Challenge.MainStatementV2
h3_of_certificates_T : Top.Automaton10StatementV2 →
  Top.StationaryCheckStatementV2 → Top.H3Statement
finite_checked : H1TreeFiniteStatement
```

## 3. Checker design and full finite pilot

`H1TreeFiniteStatement` is a closed conjunction of checked mean rows, required special mean rows, scalar model bindings/tests, sixteen matrix cases, coverage and layout/shape checks. It asserts no analytic soundness implication. The finite matrix cases include model/spec binding, all local moment/Pauli tables, central IDs, a coefficient bound, every reconstructed entry, zero packed imaginary row, and all Gram rows. The coverage keys are defined by `allKeys := coverageTree.keys`; the records checked by `coverageTree.all reductionCheck` are that same tree. Coherence therefore holds by construction.

* Mean arithmetic uses integers with one common positive denominator. Degree-(2,2,2) coefficients are reconstructed from 27 integer evaluations with the exact tensor transform of scale 64. The two-variable degree-four transform has scale 144 in each coordinate. The input coefficient list must match and be nonnegative.
* Scalar tests are division-free: L endpoints, Q endpoints and `4*q0*q2-q1²` only when the positive quadratic vertex is inside the interval. Bindings ensure the tested outgoing/non-outgoing radii are exactly those of the listed model.
* Local tables use the U/D moments through degree four with positive integer LCDs. Nonzero fields, formal mean fields and unit-pair bases use the stated field order. Tables use balanced lookup; cached site matrices avoid recomputing unchanged factors for every mark insertion. All big products use the larger operand first. There are no giant packed Nat literals.
* Central rows use Kronecker packing with a checked coefficient/no-carry bound and exact signed digit extraction. Four-row modules keep retained kernel cells bounded. Full tensors are not materialized. Off-central weight commutation/support is assigned to the explicit analytic forest leaves; the pilot does not replay the native audit's unused full dense off-weight diagnostics.
* Gram checks use symmetric square-matrix/positive-scale/lower-prefix headers and eight-row residual pages. Each row verifies positive diagonal and `sum(abs Erow) < 2*Eii`. The generic soundness refiner targets the existing Gram checker with coefficient **1** on `LLᵀ`; witness `g` belongs to the separate equality `M=gN`.
* Raw masks are the exact 4×5³×8⁴ choices. Corner consistency is factorized locally. Identical effective corner records are collapsed before products; removed isolated factors are common positive normalizers, not silently changed laws. Cartesian and projection completeness are explicit mathematical leaves. Every surviving branch is checked against a listed dominating model, with mean calls accepted only by the supplied 21-row table.

Kernel bookkeeping receipts verify 106,101 consistent raw assignments, 184,914 outgoing choices, 123,339 N/E choices, 7,962 records, 24,741 branches and 981 empty-mark branches; 20 decorated geometries; antichain and attained witnesses for all 38 maximal models. The original 2,048,000 raw count is the exact product above, not a claim to have run an unoptimized two-million-tuple loop. No old pattern catalogue is read.

All final standalone check jobs passed. The scalar family is **22**, not the older 19 boxes. There are 21 ordinary mean rows, two required special rows, and one extra archived `r=1/25` check, excluded from the required special input. The largest matrix is 66; original matrix entries are ≤37 bits and Gram factors ≤19 bits.

The measured per-process commands use one Lean worker. The following timings are sums, not parallel elapsed time:

| Check | Kernel s | Process CPU s | Peak RSS GiB |
|---|---:|---:|---:|
| 21 ordinary mean checks | 2.930 | 3.20 | 0.337 |
| 2 required + 1 extra special mean checks | 0.367 | 0.55 | 0.340 |
| 22 scalar tests | 0.052 | 0.26 | 0.301 |
| 16 sets of local moment/Pauli tables | 83.100 | 86.50 | 0.628 |
| 14,502 central matrix entries + row reality | 342.818 | 361.64 | 0.958 |
| 16 Gram/residual blocks, header + eight-row pages | 39.368 | 55.08 | 0.728 |
| 500 raw-neighbour groups, factorized corners | 202.648 | 298.51 | 0.723 |
| 7,962 records / 24,741 branches | 241.517 | 315.11 | 0.565 |
| bindings, counts, geometries, maximal witnesses | 6.086 | 8.58 | 0.868 |
| **Total** | **918.886** | **1129.43** | **0.958 max** |


The finite-check kernel subtotal is **15.31 minutes**, about **2.1% above a strict 900 s interpretation** of the requested “~15 minutes.” This is not a claim that the future analytic leaf proofs fit in that same budget. Matrix reconstruction dominates (342.8 s); coverage reduction and raw projection together take 444.2 s. To create headroom, first deduplicate local-table checks across identical site specs ignoring `stride` (83.1 s currently), then reduce repeated mean/model lookups or stream smaller central packed row blocks. The checker already caches site matrices: a representative largest four-row reconstruction dropped from about 11 s / 1.8 GiB to about 5.5 s / 0.96 GiB. These proposed additional cuts are not claimed measured.

Exact per-module kernel/CPU/RSS are in [kernel-per-check.csv](kernel-per-check.csv) and [kernel-metrics.json](kernel-metrics.json), with all `--profile` outputs in `measure/`. Pure finite/structural receipt assembly is recorded separately in [final-certificate.log](logs/final-certificate.log): the complete `finite_checked` assembly takes about 0.6 s and adds no mathematical hypothesis. The frozen sweep uses at most four Lean processes; semantic compatibility checks use one.

The new Lean sources total **3,081,671 bytes**, in 1,103 files; maximum **847 physical lines**, maximum integer literal **119 bits**. Every new Lean file has a `module` header. The full source inventory and hashes are [source-manifest.json](source-manifest.json). The audit found no forbidden declaration, tactic, effectful command, zero heartbeat setting or nonstandard axiom in the delivered Lean sources.

Reproduction, without touching Mathlib or `.lake/packages`:

```bash
export PATH="$HOME/.elan/bin:$PATH"
python3 AKLT/Blueprint/H1T/tools/rebuild_data.py --source /home/ubuntu/aklt/reports/H1TREE_PROOF
python3 AKLT/Blueprint/H1T/tools/measure.py --jobs 4 --force-checks
python3 AKLT/Blueprint/H1T/tools/measure.py --jobs 3 --pattern __none__ --targets AKLT.Blueprint.H1T.Certificate
python3 AKLT/Blueprint/H1T/tools/replay.py --phase all
```

The generator writes only task-owned source modules. Submitted builds consume the checked-in literal modules and do not need the external report directory or Python generation. The source input hashes are in `tools/source-manifest.json`. No `lake update`, Mathlib build, package modification or agent delegation was performed.

### Independent replay

Final full finite export: **41,973,221 bytes**, **8,885 selected receipts including `finite_checked`**, **846 imported root modules**, SHA-256 **b9b5523224a3562696bd52ac7c705d1d97d42c6ee77c358a4f5531a97f3bd76c**. It contains the whole finite-certificate dependency closure, not concatenated independent shard receipts. [replay/export-summary.json](replay/export-summary.json) and [replay/tool-hashes.json](replay/tool-hashes.json) record commands/digests.

FINAL_REPLAY_RESULTS

The initial uncached control was a separate 23.7 MB full receipt export. NanoDa accepted all 29,153 declarations in 549.36 s / 2.45 GiB, with “no typechecker errors”; its pretty-printer-only axiom message is preserved in the log. Both one- and two-worker con-ron controls exceeded the local 4 GiB cap while checking the monolithic Gram receipt (24.26 / 19.75 s). These controls motivated eight-row Gram pages. The initial leanchecker command omitted `--from-export`; that invocation checked nothing and is not counted as acceptance. The final invocation uses the official from-export form.

A separate arithmetic control found `2^9216` accepted by con-ron in 0.02 s, whereas the equivalent `Nat.shiftLeft` control was declined for an unsupported Nat.div/mod environment. Consequently the delivered checker keeps powers and does not use that proposed shortcut. Controls are in `probes/`; their large comparison literal is not part of submitted H1T source.

These are local finite-certificate pilots. They are not authenticated Palomar resource evidence or a Comparator run of a completed Solution. The actual Solution export still requires the new mathematical leaves and the repository-wide module migration.

## 4. New final statement, axioms and integration prerequisite

[Final.lean](/home/ubuntu/aklt/wt/ARCH_H1T/AKLT/Blueprint/H1T/Final.lean) exports:

```lean
theorem main_of_certificates_T
    (hTree : H1T.H1TreeFiniteStatement)
    (hAutomaton10 : Top.Automaton10StatementV2)
    (hStationaryCheck : Top.StationaryCheckStatementV2)
    (hLeaves : H1T.AssemblyLeaves)
    (hLength : H1T.TraceKernelLengthStatementV3)
    (hSecond : H1T.SecondTermBoundStatementV3) : AKLT.Challenge.MainStatementV2
```

The proof constructs actual H1 using `actual_of_leaves`; builds unchanged MTheta and bounded renewal from REC062/064/065/066/067/069/070 and REC085–088; uses the V3 recursion with unchanged REC071/072/073/082/083; gets H2 from the existing certificate and H3 from its two unchanged certificate statements; then enters the unchanged window/gap/uniqueness tree at `PStatement`. The two old H1 certificate propositions are absent. `hLeaves` contains 45 closed mathematical statements; `hLength` and `hSecond` are the only direct consumer ports in this minimal final route. The other five consumer ports remain documented proof dependencies.

Every assembly has `#print axioms`. Verbatim final outputs are in [assembly-axioms.txt](assembly-axioms.txt):

```text
'AKLT.Blueprint.H1T.tree_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1T.means_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1T.actual_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1T.firstTermBound_of_leavesV3' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1T.rec_of_leavesV3' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1T.responseTyped_of_leavesV3' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1T.main_of_response_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1T.h3_of_certificates_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Final.main_of_certificates_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Blueprint.H1T.raw_coverage_checked' depends on axioms: [propext, Quot.sound]
'AKLT.Blueprint.H1T.reduction_coverage_checked' depends on axioms: [propext]
'AKLT.Blueprint.H1T.finite_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Production module migration is a real, unresolved integration prerequisite.** Existing `AKLT.Defs.*`, `AKLT.Blueprint.*`, `AKLT.Gen.Gram.*`, leaf and closing modules are non-module sources. Lean 4.35 rejects importing, for example, `AKLT.Blueprint.Rec.Definitions` from a module file. Merely inserting a new H1T module cannot fix that restriction. The task forbids editing the surrounding directories, so those sources were left unchanged.

All eight semantic architecture files were instead checked against the exact existing prebuilt declarations in a temporary compatibility view. [check_architecture.py](/home/ubuntu/aklt/wt/ARCH_H1T/AKLT/Blueprint/H1T/tools/check_architecture.py) removes only the new files' module/visibility syntax in `/tmp`, builds with `autoImplicit=false` and `relaxedAutoImplicit=false`, and retains their statements/proof terms. [final-strict-architecture.log](logs/final-strict-architecture.log) has eight successes. This is a kernel check of the assemblies against legacy dependencies, **not a production module-source build**. Loading the old private Mathlib environment uses about 6.6 GiB in that view; the <1 GiB finite measurements do not describe that legacy compatibility process. Production public-module memory must be remeasured after migration.

The four requested verifier documents were read in the read-only checkout at commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. They specify default 16 CPU / 32 GiB, one 19,800 s setup/cache/fresh-build/comparison/replay allowance, 350 minute job timeout, 95%/98% memory thresholds and at least 20 GiB workspace; the 32 CPU / 64 GiB retry needs authenticated validated resource evidence and has the same budget. Lean and NanoDa must accept the full Solution export. Con-ron has a 30-minute attempt cap; a recognized capacity decline is inconclusive. Every submitted Lean file, including unused old sources, requires module syntax and ≤10,000 lines; Challenge limits remain 1,000 lines / 100 KiB. This task certifies those file constraints only for its own directory.

Open work is therefore explicit: prove the 45 mathematical leaves and seven consumer ports; consider further splitting the conditional reduction gluing and forest-sector adapters; migrate the existing dependency/source closure to public modules and retire the old H1 catalogue from the submission build; create finite-kernel headroom if 900 s is strict; then build/export/compare the actual completed Solution under the production profile. No permission request or outside-namespace edit was needed to make these deliverables reviewable.

## ORCH-SUMMARY

- Splice choice (b): actual H1; the old artificial D-slot pattern statement is not derived.
- Old H1/V2/Final/leaf files are untouched; explicit legacy-use inventory has 56 entries.
- Core: `AKLT/Blueprint/H1T/` models, semantics, checkers, data, leaf catalogue and assemblies.
- 52 closed dispatch leaves: 45 mathematics + REC079/080/081/090/091/094/095 V3.
- Minimal final directly needs V3 REC079 and REC081; the other five are their dependencies.
- `AKLT.Final.main_of_certificates_T` takes tree finite input + unchanged two H3 inputs + explicit new leaves.
- `finite_checked : H1TreeFiniteStatement` is proved from kernel receipts, with no mathematical leaf premise.
- Checks cover 23 required means (+1 extra), 22 scalars, 16 matrices/Gram blocks and full factorized coverage.
- Record/key coherence is definitional through one shared tree; counts/maximal witnesses are checked.
- Finite kernel subtotal 918.886 s (15.31 min); max process RSS 0.958 GiB.
- This exceeds strict 900 s by 2.1% before future analytic proofs; local-table deduplication is the first cut.
- 3.08 MB Lean source, 1,103 files, max 847 lines, max integer literal 119 bits; all module headers.
- REPLAY_SUMMARY_LINE
- All conditional assembly axiom prints contain only propext, Classical.choice, Quot.sound.
- Production semantic source build remains blocked by existing non-module dependencies outside allowed edits.
- Strict compatibility check of all eight architecture files succeeds; that legacy view uses about 6.6 GiB.
- No completed Solution/Comparator acceptance or authenticated Palomar resource outcome is claimed.
- Hand off exact mathematical/consumer names in leaves.json; global module port and final replay are orchestrator work.
