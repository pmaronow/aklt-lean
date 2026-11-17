STATUS: PROVED FROM DEPS

Closing phase complete: the two H1 contracts now have closed, kernel-checked proofs. See the appended **closing phase** section. Earlier sections record the production checkpoint before the leaf theorems were merged.

# Phase 3 — complete finite H1 production

The hand-written handoff and complete finite numeric run are delivered. All **7,964
production owner modules** have successful kernel-build receipts and passed the independent
source/artifact/dependency/exit/axiom audit. They cover **7,962 patterns, 12,173 saved
exchange-sector blocks, 144,554 constructed rows, 158,230 logical components** and
**101,536 logical check components**. All **414,638 exported generated theorem axiom audits**
passed. This includes the full generated conditional Top targets.

The mathematical bridge still has exactly **33 open closed Props**. No mathematical leaf
proof was written by root after the author's rule. The completed deliverable is the finite
computation and conditional assembly; an unconditional H1 certificate is not claimed.

## Merge set and current main

- Exact source merge list: [merge-set.txt](merge-set.txt), **39 hand-written files**.
- Build root: `lake build AKLT.Cert.H1.Production.All`; audit: `lake build AKLT.Cert.H1.Production.Audit`.
- Writer queue: [leaves-open.json](leaves-open.json), exactly 33 real proof obligations, no data blocks.
- Full closed statements, dependency notes and kernel statuses: [leaves.json](leaves.json).
- Attachment instructions: [merge-set.md](merge-set.md), plus `CertData/H1/README.md` in the merge set.

All 17 reusable Lean sources compiled, with strict implicit settings and no existing H1
artifact or generated H1 source visible, on a pristine archive of main
`6f171dccd76d8641416d2609ed2caa5968f6afdb` plus the source set. All 36 Prop checks and nine generic assembly axiom
audits passed. Receipt: [phase3/merge-verification.json](phase3/merge-verification.json).
Documentation/Python changes after that compilation are recorded separately; no reusable
Lean proof or statement source changed.

A final refresh against main `63d176add85a0eae6c862c54849a495434b7d438` found **all 23 external AKLT dependency
sources unchanged** from that clean check. The active worktree has 15 statement-path
mismatches with main, listed in [phase3/main-refresh.json](phase3/main-refresh.json);
the relevant older files include `AKLT/Defs/OperatorContracts.lean` and
`AKLT/Blueprint/Top/Operator.lean`. No statement file was copied or edited. The bridge is
compatible with the current main statement layer and its H1 V2 witness handoff.

Generated modules remain outside `AKLT/`, in `CertData/H1/Generated/`. The separate,
opt-in Lake target is **`CertDataH1`**, with root `CertData.H1.Generated` and globs for
`Batch/` and `Bridge/`. Main's generic `CertData` target and `defaultTargets = ["AKLT"]`
are preserved. The ordinary AKLT library has no generated-certificate imports.
Historical Phase1 prototypes with generated dependencies are archived and excluded
from this standalone source set and the production target.

## Production receipts and reproduction

Authoritative receipt: [phase3/verified-production.json](phase3/verified-production.json).
Manifest SHA256: `50da2835019f02cbf5ac6fae8d3b07d60d4cdba1842472cf051b548009fd4784`.
The receipt verifies every actual generated import is tracked (the manifest may also
track redundant transitive dependencies), every original component has a checked owner,
all dependency keys and artifact hashes match, every GNU-time exit is zero, and every
exported theorem has an allowed complete axiom audit. Logical Data/Check declaration
names retain their namespaces; the owner map identifies their actual Batch/Bridge module.
Unbundled templates are not an additional independent `.olean` set.

The data index and 16 compressed witness chunks were hashed before production and verified
unchanged afterwards: [phase3/data-input-receipt.json](phase3/data-input-receipt.json).
There are 17 input files totaling 12,338,764 bytes. The standalone command
`production_receipts.py inputs` reproduces these hashes and rejects a conflicting receipt.

Executed complete-run commands (PATH includes `$HOME/.elan/bin`):

```sh
python3 AKLT/Cert/H1/tools/production_build.py /home/ubuntu/aklt/reports/CERT_H1/phase3/production.json --jobs 44 --jobs-file /home/ubuntu/aklt/reports/CERT_H1/phase3/workers.txt --cap-gib 9 --seconds 7200 --compact-sources --report-dir /home/ubuntu/aklt/reports/CERT_H1/phase3
python3 AKLT/Cert/H1/tools/production_build.py /home/ubuntu/aklt/reports/CERT_H1/phase3/large-frontier.json --jobs 1 --cap-gib 9 --seconds 7200 --compact-sources --report-dir /home/ubuntu/aklt/reports/CERT_H1/phase3
python3 AKLT/Cert/H1/tools/production_receipts.py verify /home/ubuntu/aklt/reports/CERT_H1/phase3/production.json --report-dir /home/ubuntu/aklt/reports/CERT_H1/phase3
python3 AKLT/Cert/H1/tools/production_leaves.py --manifest /home/ubuntu/aklt/reports/CERT_H1/phase3/production.json --report-dir /home/ubuntu/aklt/reports/CERT_H1/phase3
python3 AKLT/Cert/H1/tools/production_measure.py --verified-production /home/ubuntu/aklt/reports/CERT_H1/phase3/verified-production.json
```

The complete fresh-export recipe is in `CertData/H1/README.md`. Case data, case assemblies
and index-witness exports now carry their 16 GiB caps automatically; final whole-catalogue
modules carry 64 GiB caps. Completed-run metrology and leaf export do not require old pilot
or phase-1 report files; historical attempt metadata is retained when available.

## Measurements, memory and disk

Measured portfolio cost: **139.002 CPU-hours**, including earlier reusable
receipts. Successful phase-3 compilation events consumed **135.524
CPU-hours**; that excludes interrupted jobs and Python/exporter overhead. There were
7,030 successful phase-3 compilation events across the
main run and frontier. The final main traversal reused 3,411 receipts;
this includes work completed during earlier traversals of the same campaign.

Campaign interval: approximately **2026-11-16T19:38:44.381773+00:00**
to **2026-11-16T23:21:08.225892+00:00**, or **3.707
wall-hours**. Start is inferred from GNU-time log modification times minus recorded module
wall durations, rather than a claimed fresh cold rebuild. Full timing details and exclusions:
[phase3/campaign-times.json](phase3/campaign-times.json).

Constructor reductions alone: **109.236 CPU-hours**, maximum GNU-time RSS **7.540 GiB**,
all 144,554 row theorem audits passed. Receipt: [phase3/constructor-log-audit.json](phase3/constructor-log-audit.json).
Gram row reductions: **7.439 CPU-hours**, maximum RSS **6.739 GiB**. Positivity assembly
adds **1.332 CPU-hours**, giving **8.770 CPU-hours** for Gram reduction plus positivity
assembly. Shared matrix/factor data compilation is separate: **1.494 CPU-hours**, with
**10.964 GB** of retained matrix/factor oleans.

The full catalogue witness assembly took 8.267 s wall / 8.25 s CPU, with maximum RSS
11.153 GiB; the final Top target module took 8.017 s wall / 8.00 s CPU, maximum RSS
11.150 GiB. These former unmeasured aggregation stages now have production receipts.
GNU-time peaks cover the launched process tree; sampled live RSS is recorded separately
in the run summaries. Source compression and dependency reuse do not weaken kernel acceptance.

| Stage | Owner modules | CPU-hours | Max RSS (GiB) | Retained olean GB |
|---|---:|---:|---:|---:|
| `all_witness_assembly` | 1 | 0.0023 | 11.153 | 0.0003 |
| `case_assembly` | 249 | 0.4972 | 7.147 | 0.1679 |
| `case_data` | 249 | 0.3479 | 7.160 | 0.1258 |
| `constructor_assembly` | 396 | 0.9166 | 7.103 | 0.4252 |
| `constructor_rows` | 1,161 | 109.2364 | 7.540 | 0.2100 |
| `coverage_assembly` | 1 | 0.0023 | 6.551 | 0.0003 |
| `coverage_data` | 1 | 0.0154 | 7.226 | 0.0386 |
| `coverage_frontier` | 16 | 0.7849 | 7.715 | 0.0055 |
| `coverage_header` | 1 | 0.0049 | 7.827 | 0.0000 |
| `gram_rows` | 1,056 | 7.4385 | 6.739 | 0.0358 |
| `index_all_data` | 1 | 0.0016 | 6.589 | 0.0015 |
| `index_assembly` | 1 | 0.0036 | 7.900 | 0.0006 |
| `index_data` | 16 | 0.0287 | 6.569 | 0.0373 |
| `index_keys` | 16 | 0.0764 | 6.590 | 0.0008 |
| `index_witness_assembly` | 16 | 0.0311 | 9.811 | 0.0165 |
| `input_data` | 249 | 0.4793 | 6.490 | 0.0676 |
| `input_geometry` | 249 | 0.4615 | 6.504 | 0.0217 |
| `local_parameters` | 1,991 | 11.6142 | 7.042 | 0.1566 |
| `matrix_data` | 503 | 1.4937 | 4.696 | 10.9638 |
| `network_data` | 383 | 1.6199 | 6.669 | 0.7749 |
| `pattern_data` | 249 | 0.7095 | 6.541 | 0.2002 |
| `positivity_assembly` | 396 | 1.3318 | 5.865 | 0.0854 |
| `sector_layout` | 381 | 0.9549 | 6.954 | 0.0283 |
| `sector_network_data` | 381 | 0.9473 | 6.564 | 0.4237 |
| `target_assembly` | 1 | 0.0022 | 11.150 | 0.0000 |

Resource policy: before `CERT_H3-p3.done`, at most 24 Lean processes and 245 GB of
reservations within 250 GB; after its appearance the driver ran `free -g` and allowed
up to 44 processes with 410 GB reservations within 420 GB. Conservative 9 GiB normal
caps limited the main pool to 42 jobs. One frontier worker gave a combined bound of 43
Lean processes; its RSS cap plus the main Lean-tree cap was below 420 GB. Physical
MemAvailable was monitored with a 40 GB floor. The largest frontier completed 149/149
jobs, with 138 reuses and 11 new builds, using the same cross-runner module locks.

All **7,964 owner `.olean` files are retained**. Their **317,687,703 source bytes** are
stored in **28,865,465 bytes of `.lean.gz` payload**. All 158,230 unbundled templates
were losslessly compressed from 335,393,678 to 76,907,483 bytes, without deleting oleans.
Every template archive/raw-source hash was verified; all 27,829 frozen pre-rule source
hashes still match. Core source scanning found no forbidden tokens, and the final verifier
also scanned every production owner source. No new written mathematical leaf proof exists.

Measured task disk allocation, including reports and scratch, is about
**17.128 GB**, below 40 GB. Root free space at this report is
**442.0 GiB**, above the 100 GiB abort threshold. Retained artifacts are
already visible to Lean in this worktree. Final proof assembly can import them with
`lake env lean FILE.lean`; a conventional `lake build CertDataH1` after restoring sources
may repeat checks when Lake trace files are absent. Preserve matching dependency/core
versions when transferring the artifact tree.

## Production plan after full measurement

Build order: reusable All/Audit; pattern, network and matrix/factor data; local tensor,
layout and geometry checks; independent packed-constructor rows and Gram rows; constructor
and positivity assemblies; case witnesses; coverage/key catalogue checks and witness chunks;
whole-catalogue witness assembly; final conditional Top targets. The manifest is the exact DAG.
Numerical module batching preserves independent kernel reductions and bounded retained work.
Normal modules reserve 9 GiB, case/index-witness modules 16 GiB, whole-catalogue modules 64 GiB.
The observed maximum is 11.153 GiB. Retain about 17.2 GB of artifacts/reports; keep the 40 GB
ceiling and 100 GiB free-root guard.

Projections below replay measured per-module CPU costs through that DAG, with declared
memory reservations. They are scheduling projections, not additional runs. Engineering
intervals allow import/IO, wrapper and CPU-contention overhead; mathematical proof writing
for the 33 leaves is excluded.

| Requested workers | RSS reservations | Effective max | CPU-cost schedule | Engineering wall range |
|---|---:|---:|---:|---:|
| 24 | 245 GB | 24 | 5.82 h | 6.40–8.73 h |
| 44 | 410 GB | 42 | 3.36 h | 3.70–5.04 h |
| 48 (projection only) | 410 GB | 42 | 3.36 h | 3.70–5.04 h |

The 48-worker projection is hypothetical and was not run: this lane is authorized only
up to 44, and the conservative memory reservations cap both settings at 42 ordinary
jobs under the 420 GB allocation. More process slots alone do not improve this policy.
Detailed measured schedule: [phase3/measurements.json](phase3/measurements.json).

## Final exports and axioms

Reusable generic assemblies remain the nine declarations in
`Production.Assembly` and `Production.TopAssembly` documented below in the accepted
phase-2 statement section. The full generated final module is
`CertData.H1.Generated.Bridge.Targetassembly0000`; its public declarations are in
`CertData.H1.Generated.Check.Targets`:

```lean
theorem finiteData (h : Assembly.ConstructorPremises) (hc : Assembly.CoveragePremises)
    (ha : Leaves.representativesAppend) : AKLT.Blueprint.Top.H1FiniteDataStatementV2 := ...
theorem certificateV2 (h : Assembly.ConstructorPremises) (hc : Assembly.CoveragePremises)
    (ha : Leaves.representativesAppend) (hs : TopLeaves.certificatePremises) :
    AKLT.Blueprint.Top.CertificateStatementV2 := ...
theorem targets (h : Assembly.ConstructorPremises) (hc : Assembly.CoveragePremises)
    (ha : Leaves.representativesAppend) (hs : TopLeaves.certificatePremises)
    (hi : TopLeaves.integerCheckPremises) :
    AKLT.Blueprint.Top.IntegerCheckStatement ∧ AKLT.Blueprint.Top.CertificateStatementV2 := ...
```

For each of `finiteData`, `certificateV2`, and `targets`, actual `#print axioms` output is:

```text
[propext, Classical.choice, Quot.sound]
```

The same allowed set bounds all nine generic assembly outputs and all 414,638 generated
theorem audits. The final targets still take the closed-Prop premise bundles explicitly;
there is no inference from an axiom audit to an unconditional H1 proof.

## Exact mathematical queue and remaining work

[leaves-open.json](leaves-open.json) contains exactly these 33 closed Props, with module,
paper label, difficulty, first-attempt route and trap note. The full exact Lean bodies and
statement-layer repair dependencies are in [leaves.json](leaves.json). The first attempt
must be made by a different cheaper model. `rationalCurrent` is derived by assembly and
is not an additional open leaf; the two premise bundles are not leaves.

- `AKLT.Cert.H1.Production.TopLeaves.integerEntries`
- `AKLT.Cert.H1.Production.TopLeaves.thresholdScale`
- `AKLT.Cert.H1.Production.TopLeaves.positiveScale`
- `AKLT.Cert.H1.Production.TopLeaves.sylvester`
- `AKLT.Cert.H1.Production.TopLeaves.bareiss`
- `AKLT.Cert.H1.Production.TopLeaves.sectorPositiveImpliesBound`
- `AKLT.Cert.H1.Production.Leaves.inputCovered`
- `AKLT.Cert.H1.Production.Leaves.compilerInversion`
- `AKLT.Cert.H1.Production.Leaves.compilerGeometry`
- `AKLT.Cert.H1.Production.Leaves.denominator`
- `AKLT.Cert.H1.Production.Leaves.acceptedLookup`
- `AKLT.Cert.H1.Production.Leaves.parityCoverage`
- `AKLT.Cert.H1.Production.Leaves.basisIndexing`
- `AKLT.Cert.H1.Production.Leaves.acceptedDecode`
- `AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion`
- `AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound`
- `AKLT.Cert.H1.Production.Leaves.signedPacking`
- `AKLT.Cert.H1.Production.Leaves.packingDecode`
- `AKLT.Cert.H1.Production.Leaves.paritySlice`
- `AKLT.Cert.H1.Production.Leaves.momentPolynomial`
- `AKLT.Cert.H1.Production.Leaves.tensorSubstitution`
- `AKLT.Cert.H1.Production.Leaves.sectorLinearity`
- `AKLT.Cert.H1.Production.Leaves.directRowsEntry`
- `AKLT.Cert.H1.Production.Leaves.metadataFacts`
- `AKLT.Cert.H1.Production.Leaves.rawEncoding`
- `AKLT.Cert.H1.Production.Leaves.enumerationSoundness`
- `AKLT.Cert.H1.Production.Leaves.representativeLookup`
- `AKLT.Cert.H1.Production.Leaves.representativeCode`
- `AKLT.Cert.H1.Production.Leaves.representativeWitnessLookup`
- `AKLT.Cert.H1.Production.Leaves.representativesAppend`
- `AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification`
- `AKLT.Cert.H1.Production.Leaves.sameDataWitness`
- `AKLT.Cert.H1.Production.Leaves.mirrorDataWitness`

Only mathematical closure remains: compiler/moment/tensor/packing/basis/coverage and
analytic scaling/Sylvester/Bareiss/operator-bound obligations. Cross-parity and central-weight
spectral completeness and U-kernel facts remain analytic obligations, as in the accepted
design. The production computation uses the split-parity route; the optional unsplit
exporter remains implemented but is not an additional production claim.

## Engineering corrections and validation

A GNU-time exit-zero constructor-assembly build was initially rejected because merged
profiling stderr interrupted the printed name `Quot.sound`. The immutable original log and
repair receipt are in `phase3/diagnostics/`. New builds capture stderr separately; known
profiling records are normalized only when parsing legacy logs. Raw logs remain intact.
The affected assembly was rebuilt, and the final independent audit covered every module.
An overstrict direct-import equality test was also corrected to allow conservative
transitive dependencies while rejecting any omitted actual import. Neither correction
changed a Lean statement, proof source, checker, witness input, or arithmetic outcome.

Cross-runner module locks are shared across report directories. Snapshot writes are batched;
every successful build is separately journaled before reuse. A separate normal-Lake-cache
publication regression rejected a stale artifact and accepted the new artifact after
publication; the final finite test has no axioms. Receipt:
[phase3/publication-test/receipt.json](phase3/publication-test/receipt.json).
The earlier transitive source/dependency cache regression remains in the accepted pilot
records. Full verification recomputed the complete transitive keys and all artifact hashes.

The H3′ lane is outside this delivery. No sub-agents were used, no packages or Defs sources
were edited, no Mathlib build or Lake update was run, and no new mathematical leaf proof
was written. Historical pre-rule proofs are preserved and explicitly listed below.

# Accepted phase 2 report — historical design, pilot and preserved proof list


# H1 production delivery

Scope: CERT_H1. The H3′ case pilot in the broadcast instruction belongs to CERT_H3.
The H1 engineering route is implemented for all 7,962 patterns and all 12,173 saved blocks.
There is no new mathematical leaf proof by root. The 33 active mathematical leaves require a
first attempt by a different cheaper model. Conditional assemblies and permitted kernel
computations are proved; an unconditional H1 theorem is not claimed.

The final route has **7,964 generated production modules**, separate from **17 reusable H1
library modules**. All generated sources and artifacts are below `CertData/`, with an explicit,
non-default Lake `CertData` target. No ordinary AKLT module imports CertData. The sole change
outside the assigned H1 source directory and CertData is the Lake target registration.

# Implemented construction and generation

The constructor uses integer Gaussian local tensors, balanced sparse lookup, 4×4 ring transfer
matrices and signed Kronecker packing. Raw `Input` records compile the covered pattern,
representation, original-token inversion, local degrees/dimensions and strides. Independent
Boolean checks compare this compilation with the exported network. Local moment/Pauli tables
are reconstructed by `localEntry` and `tableCheck`; no rational arithmetic is used in the inner
kernel loops.

Every D exchange parity is split **before packing**. A symmetric D pair uses coordinates
`[0,1,2]`; its exterior sector uses `[3]`. Singles and U pairs keep their supported coordinates.
Original tensor indices are remapped and checked. Kernel basis enumeration verifies the full
central-weight list for each block; parity coverage is checked separately. Unused exchange
signs remain quantified in the semantic leaves and never supply an orthogonality assumption.
Both unreduced representations are supported.

Widths are chosen independently of M from the product of absolute local table sums. Across the
complete export the width counts are 32:1014, 48:3931, 64:2503, 80:464, 96:50. The largest
unsplit tensor has 2,048 columns; after parity splitting the maximum is 864. Each row check
compares the **complete Gaussian packed value** to the sparse encoding of its saved real row,
and checks the signed range of every expected coefficient. This checks the packed imaginary
value and the other magnetic weights in that parity. Coefficientwise interpretation uses the
explicit expansion, complex L1 bound and signed-decoding leaves. Cross-parity decoupling and
the discarded U antisymmetric kernels remain analytic proof obligations. An `--unsplit`
export mode is implemented for every case/block and can also check other parities numerically;
the production Defs bridge uses the split mode.

Constructor checks reference saved M rows with `getD`; matrix literals are not duplicated in
check modules. On the pilot, constructor `.olean` storage fell from about 311 MB to 5.5 MB.
Bundling preserves each independent kernel reduction as its own theorem. Source-size, row,
Gram-work and matrix-cell budgets bound a bundle. Logical Data/Check declaration namespaces
are retained; file ownership is recorded in `owner_modules` / `production_owner_map`.

Coverage now has an executable Lean enumeration: 500 axial frontiers, local corner-consistency
pruning, eight independent first-corner shards per frontier, effective/reflected code
construction and balanced catalogue lookup. The checker covers the normalized
`5^3·4·8^4 = 2,048,000` configurations, including all N/E/W outgoing choices that survive.
Raw normalization and the connection to arbitrary `PatternData.Covered` are explicit open
leaves. The catalogue has 7,962 strictly increasing codes; its complete representative-key
index is also kernel checked. Its append assemblies are balanced, avoiding quadratic
concatenation. A left-associated tuning build reached about 23 GiB; the successful balanced
index assembly peaked at 7.902 GiB.

Replay is a dependency DAG and successful-event journal, with per-module locks, timeouts,
source/artifact hashes and resource guards. The final key version includes **dependency keys
as well as artifact hashes**, plus recursive AKLT library source/artifact fingerprints and
pinned Lean/Mathlib metadata. Thus a transitive change invalidates a child even when an
intermediate data artifact stays byte-identical. The true→false→true regression passed: changing the parent invalidated and rejected
the downstream check while the intermediate artifact remained byte-identical. The source
was restored and checked. Evidence: `phase2/cache-test.json` and its three run logs. Hashes control reuse, never mathematical acceptance. Every acceptance proof
uses `decide +kernel` or a proved assembly from such checks.

# Files and entry points

| File/family | Role |
|---|---|
| `AKLT/Cert/H1/Production/Basic.lean` | Packed row, coefficient-range, parameter, basis, parity, sector-slice and remapping checkers |
| `Production/Input.lean`, `Production/Coverage.lean` | Raw compiler and complete finite coverage/pruning/lookup checkers |
| `Production/Semantics.lean`, `Production/Tensor.lean` | Actual Defs geometry, direct integer contraction, polynomial intermediate, cases and witness predicates |
| `Production/Leaves.lean`, `Production/TopLeaves.lean` | Exact closed mathematical Props; no proofs |
| `Production/Assembly.lean`, `Production/TopAssembly.lean` | Nine kernel-checked conditional assemblies |
| `Production/Audit.lean`, `Production/All.lean` | Closed-Prop/axiom audit and reusable entry point; no generated imports |
| `AKLT/Cert/H1/tools/production_bootstrap.py` | Builds only H1 code against the supplied prebuilt dependencies |
| `production_export.py`, `production_bridge_export.py` | Complete witness/network/sector/row export and raw-input/case assemblies |
| `production_coverage.py`, `production_index.py` | All coverage frontiers, representative indexes and final target source |
| `production_bundle.py`, `production_build.py` | Batching, owner maps, bounded DAG execution and replay |
| `production_leaves.py`, `production_measure.py`, `production_cache_test.py` | Writer registry, measurements/forecast, transitive replay regression |
| `CertData/H1/Generated/Batch/`, `Generated/Bridge/` | Production data/check/assembly owner modules selected by the Lake target |
| `CertData/H1/Phase1/` | Retained historical sources/proofs and tools; excluded from production globs |
| `CertData/H1/README.md` | Complete reproduction commands and resource policy |
| `reports/CERT_H1/phase2/production-ready.json` | Complete build DAG, module kinds, components and dependencies |
| `reports/CERT_H1/leaves.json`, `proof-leaf-index.json` | Exact active leaves, first-attempt routing, revision dependencies and assembly graph |

The old command names `export.py`, `export_packed.py`, `export_leaves.py`, `build.py`,
`coverage.py` and `summarize.py` dispatch to the production route. Original tools are archived.
The independent Python packed audit now supports every block (`--block all`). All production
exporters use only the Python standard library, validate chunk hashes and integer JSON,
reconstruct slot/parity/basis metadata and enforce disk guards.

# Statement corrections and soundness chain

ARCH_0's [stmt-fix.md](/home/ubuntu/aklt/reports/ARCH_0/stmt-fix.md) leaves the rational matrices,
integer target and original certificate soundness target unchanged. A1 adds the actual
`H1SectorWitnesses` / `H1FiniteDataStatementV2` existence handoff and
`CertificateStatementV2`. A2 explains ignored exchange signs. F2/F3/F4 broaden the analytic
real-polynomial contracts. The numerical matrices need no change for these repairs.

**Build dependency:** this worktree's old Defs sources do not yet contain all V2 declarations.
The measured builds use the supplied current `/home/ubuntu/aklt/repo` prebuilt Defs/Top
artifacts, as linked by the bootstrap. The orchestrator must merge ARCH_0 before a source-only
ordinary project rebuild. No Defs, Mathlib or package source was edited here; no `lake update`
or Mathlib build was run.

The bridge separates raw compilation, exact moment-polynomial contraction, Pauli basis
substitution, parity slicing, signed decoding, actual integer-sector reconstruction,
Gram witnesses and raw-pattern coverage/transport. `RawWitness` is the small adapter to the
shared finite-data handoff. The registry marks A1 dependencies on witness transport/list
leaves, A2 on parity/basis leaves, and F2/F3/F4 on the analytic sector-to-bound leaf. The latter
can reuse BP_H1M's repaired analytic proof chain; it is itself a closed rational contract.

The proved assembly chain is:

1. `rationalCurrent_of_leaves`: moment-polynomial identity + tensor substitution + sector
   linearity → exact rational entry reconstruction.
2. `matrix_from_stages`: compiled geometry, justified denominator, explicit basis indexing,
   accepted packed rows, decoding and integer-entry leaves → equality to the actual Defs
   `indexedSectorMatrix`, for every pair of indices.
3. `case_witness`: this equality plus the existing proved Gram and triangularity soundness →
   `RawWitness (inputPattern caseData.input)`, with **all** exchange signs covered.
4. `finiteData_of_checks`: complete coverage checks + representative index + representative
   witnesses + normalization/reflection transport leaves → exact
   `AKLT.Blueprint.Top.H1FiniteDataStatementV2`.
5. `certificateV2_of_checks` combines that existence with exact original certificate soundness.
   `TopAssembly.targets_of_leaves` separately concludes both exact original requested targets.

The full generated `CertData.H1.Generated.Check.Targets` source concludes
`IntegerCheckStatement ∧ CertificateStatementV2` from named closed premise bundles and all
finite check modules. It is generated, not yet built for the complete data set. Its generic
assembly components are kernel checked. The pilot additionally checks aggregation of all
100 concrete case witnesses, conditional on the same mathematical leaves.

# Exported assembly declarations and axiom output

All names below are under `AKLT.Cert.H1.Production`.

| Declaration | Exact conclusion / named premises |
|---|---|
| `TopAssembly.integerCheck_of_leaves` | `TopLeaves.integerCheckPremises → Top.IntegerCheckStatement` |
| `TopAssembly.certificate_of_leaves` | `TopLeaves.certificatePremises → Top.CertificateStatement` |
| `TopAssembly.targets_of_leaves` | The two preceding closed bundles → their exact target conjunction |
| `Assembly.rationalCurrent_of_leaves` | `momentPolynomial → tensorSubstitution → sectorLinearity → rationalCurrent` |
| `Assembly.case_denominator` | `ConstructorPremises → c.MetadataAccepted → ClearsDenominator (inputPattern c.input) (inputRepresentation c.input) c.denominator` |
| `Assembly.matrix_from_stages` | `ConstructorPremises`, metadata/layout/row checks and explicit basis-code equivalence → `Gram.matrix n M = indexedSectorMatrix … index` |
| `Assembly.case_witness` | `ConstructorPremises → c.Accepted → RawWitness (inputPattern c.input)` |
| `Assembly.finiteData_of_checks` | `CoveragePremises`, coverage/index checks and representative witnesses → exact `Top.H1FiniteDataStatementV2` |
| `Assembly.certificateV2_of_checks` | The preceding inputs and `TopLeaves.certificatePremises` → exact `Top.CertificateStatementV2` |

Full checked signatures and all 36 `: Prop` checks are in
[the library audit](phase2/logs/AKLT__Cert__H1__Production__Audit.log). Actual axiom output:

```text
'AKLT.Cert.H1.Production.Assembly.rationalCurrent_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Production.Assembly.case_denominator' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Production.Assembly.matrix_from_stages' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Production.Assembly.case_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Production.Assembly.finiteData_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Production.Assembly.certificateV2_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Production.TopAssembly.integerCheck_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Production.TopAssembly.certificate_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Production.TopAssembly.targets_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All generated exported theorems include `#print axioms`; successful logs contain only the
permitted axioms. The preserved historical audit was rerun after relocation and checks
333 declarations (321 original declarations plus the 12 phase-1 post-rule computation/assembly
declarations): [PreservedAudit.log](phase2/logs/PreservedAudit.log). It contains no `sorryAx`.
The 27,829 frozen proof-source hashes are unchanged.

# Pilot and measurements

The deterministic 100-pattern selection spans dimension quantiles and forces patterns
0, 2180, 7237, 7150, 4691, 3596, 7725 and 711. It includes the 179-dimensional block, both
unreduced cases, the largest full tensor and both 16-parity patterns. All **194 blocks and
3,704 rows** are checked. The complete finite dataset contains 144,554 rows, 4,742,248 full M
entries and 2,184,033 stored factor entries. The full-row Gram checker performs 118,125,077
factor products (the saved lower-triangle accounting is 60,154,555).

Earlier measured cold run: 2,179 unbundled modules, 1,016.10 s wall at 24 processes.
Initial bundled run: 170 modules, 732.35 s wall at 22 processes. After sharing M rows, 169
numerical modules plus 16 case/geometry modules form the final 185-module pilot. Constructor
changes were rechecked in 648.37 s at 24 processes, with unchanged stages replayed; this is
not represented as a cold whole-pilot timing. The final replay-hardened cold run checked **1,125 modules with zero reuse** in
**1,689.74 s wall (28.16 minutes) at 24 processes**, including the complete pilot,
all raw geometries, all coverage frontiers and the full representative index.
Its exact summary is `phase2/run-final-validation.json`.

The following per-stage totals use successful kernel builds; constructor and positivity are
separated. CPU is user+system time; RSS is GNU time's maximum per module.

| Pilot stage | Modules | CPU s | max RSS GiB |
|---|---:|---:|---:|
| case_assembly | 4 | 37.12 | 6.985 |
| case_data | 4 | 31.69 | 6.899 |
| constructor_assembly | 7 | 55.58 | 7.024 |
| constructor_rows | 30 | 16036.92 | 7.499 |
| gram_rows | 61 | 2112.55 | 6.731 |
| input_data | 4 | 19.18 | 6.489 |
| input_geometry | 4 | 34.71 | 6.502 |
| local_parameters | 25 | 732.84 | 7.018 |
| matrix_data | 16 | 253.09 | 4.702 |
| network_data | 5 | 65.09 | 6.654 |
| pattern_data | 4 | 29.09 | 6.521 |
| positivity_assembly | 7 | 142.13 | 5.854 |
| sector_layout | 7 | 69.38 | 6.863 |
| sector_network_data | 7 | 49.48 | 6.534 |

Additional validations already passed: all 500 raw-coverage frontiers / 4,000 reductions;
all 7,962 representative keys; all 7,962 raw input/geometry checks; the 100-pattern witness
aggregate; and six rejection/shape/zero-factor checks. In the final cold run coverage used 2,906.99 CPU s; earlier standalone
coverage also passed (2,125.74 CPU s, peak 7.789 GiB). The full frontend run used 881 modules and 622.43 s wall at 20 processes. The
balanced global index check used about 11 CPU s and 7.902 GiB. The old small unconditional
Defs prototype and 179-dimensional numerical prototype are retained from phase 1.

# Production plan

The final DAG has 503 matrix-data bundles, 383 network-data bundles, 249 pattern bundles,
1,991 local-parameter bundles, 381 sector-layout data bundles, 1,161 constructor-row bundles,
1,056 Gram-row bundles, 396 positivity assemblies and 396 constructor assemblies. Input,
case, coverage, representative and final target stages bring the total to 7,964. Build order:
reusable library → data → local/geometry/basis checks → constructor and Gram reductions →
block/case assemblies → representative witness aggregation → global V2 target. Coverage and
index work can run independently. Mathematical proof attempts are a separate queue.

Calibrated central estimate: **115.4 CPU-hours**. Engineering range:
**92–173 CPU-hours**;
reserve **200 CPU-hours**. These are forecasts, not a completed full numerical
run, and exclude all mathematical leaf-proof work. The final cold measurements replace the
earlier timing samples in this estimate; construction dominates the cost.

At 24 processes, allow **4.4–9.4 hours wall**.
At 48, the projection is **2.3–5.0 hours**, with
additional process/RAM authorization. The current runner deliberately enforces 24; 48 normal
11-GiB reservations require about 600 GB RAM including headroom. Normal modules have an
11 GiB cap (successful observed peak approximately 7.900 GiB). The two final
whole-catalogue aggregation/target modules have a 64 GiB cap; their full-data peak is unmeasured.
The scheduler reserves RAM as well as worker slots, keeping reservations below 285 GB within
the 300 GB pilot allocation. It separately bounds virtual address space and checks GNU time's
peak. Limits are installed with fork-safe `prlimit`, and module locks close on every return.

Full matrix-data artifacts are projected at 10.87 GB. Reserve **30 GB total task disk** under
the 40 GB budget, including sources, factors, check proofs, logs and retained prototypes.
Unbundled compiled artifacts are unnecessary after batching: 2,188 were removed, freeing
1.128 GB. Source and historical proof material remain. Free-root checks abort below 100 GB;
all observed readings stayed above that threshold. Current disk/RAM figures and the complete
stage forecast are in [measurements.json](measurements.json).

Reproduction commands are in [CertData/H1/README.md](/home/ubuntu/aklt/wt/CERT_H1/CertData/H1/README.md).
No Lake `-j` flag is used. Every build is an individually measured `lake env lean` process;
`maxHeartbeats 0` and large recursion limits occur only in certificate sources outside AKLT.

# Final mathematical leaf list

All 33 are exact closed Props with full Lean bodies and elaboration contexts in
[leaves.json](leaves.json). No first attempt was made by root. `integerCheckPremises` and
`certificatePremises` are conjunction bundles; `rationalCurrent` is a conditional assembly
interface derived from three leaves, not an additional proof assignment.

- `AKLT.Cert.H1.Production.TopLeaves.integerEntries`
- `AKLT.Cert.H1.Production.TopLeaves.thresholdScale`
- `AKLT.Cert.H1.Production.TopLeaves.positiveScale`
- `AKLT.Cert.H1.Production.TopLeaves.sylvester`
- `AKLT.Cert.H1.Production.TopLeaves.bareiss`
- `AKLT.Cert.H1.Production.TopLeaves.sectorPositiveImpliesBound`
- `AKLT.Cert.H1.Production.Leaves.inputCovered`
- `AKLT.Cert.H1.Production.Leaves.compilerInversion`
- `AKLT.Cert.H1.Production.Leaves.compilerGeometry`
- `AKLT.Cert.H1.Production.Leaves.denominator`
- `AKLT.Cert.H1.Production.Leaves.acceptedLookup`
- `AKLT.Cert.H1.Production.Leaves.parityCoverage`
- `AKLT.Cert.H1.Production.Leaves.basisIndexing`
- `AKLT.Cert.H1.Production.Leaves.acceptedDecode`
- `AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion`
- `AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound`
- `AKLT.Cert.H1.Production.Leaves.signedPacking`
- `AKLT.Cert.H1.Production.Leaves.packingDecode`
- `AKLT.Cert.H1.Production.Leaves.paritySlice`
- `AKLT.Cert.H1.Production.Leaves.momentPolynomial`
- `AKLT.Cert.H1.Production.Leaves.tensorSubstitution`
- `AKLT.Cert.H1.Production.Leaves.sectorLinearity`
- `AKLT.Cert.H1.Production.Leaves.directRowsEntry`
- `AKLT.Cert.H1.Production.Leaves.metadataFacts`
- `AKLT.Cert.H1.Production.Leaves.rawEncoding`
- `AKLT.Cert.H1.Production.Leaves.enumerationSoundness`
- `AKLT.Cert.H1.Production.Leaves.representativeLookup`
- `AKLT.Cert.H1.Production.Leaves.representativeCode`
- `AKLT.Cert.H1.Production.Leaves.representativeWitnessLookup`
- `AKLT.Cert.H1.Production.Leaves.representativesAppend`
- `AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification`
- `AKLT.Cert.H1.Production.Leaves.sameDataWitness`
- `AKLT.Cert.H1.Production.Leaves.mirrorDataWitness`

The historical 44,035 open mathematical entries remain in `phase1/leaves.json` with their
exact statements and attempt metadata. The production route replaces per-instance proof
assignments by generic compiler/packing/basis/coverage leaves plus finite computations.
No historical mathematical goal is claimed discharged merely by that reorganization.

# Preserved declarations

The following 321 pre-rule audited declarations are retained unchanged; additional phase-1
post-rule computations/assemblies are retained as well. Source locations are mapped by
`phase2/legacy-paths.json`, and SHA-256 inventories remain in `pre-rule-proofs.json`.

- `AKLT.Cert.H1.Check.P0000B00.checked`
- `AKLT.Cert.H1.Check.P0000B00.header_checked`
- `AKLT.Cert.H1.Check.P0000B00.positive_complex`
- `AKLT.Cert.H1.Check.P0000B00.positive_real`
- `AKLT.Cert.H1.Check.P0000B00.rows000_checked`
- `AKLT.Cert.H1.Check.P0000B00.rows_checked`
- `AKLT.Cert.H1.Check.P0000Packed.constructed_positive_real`
- `AKLT.Cert.H1.Check.P0000Packed.denominator_checked`
- `AKLT.Cert.H1.Check.P0000Packed.local0_checked`
- `AKLT.Cert.H1.Check.P0000Packed.local1_checked`
- `AKLT.Cert.H1.Check.P0000Packed.local2_checked`
- `AKLT.Cert.H1.Check.P0000Packed.local3_checked`
- `AKLT.Cert.H1.Check.P0000Packed.local4_checked`
- `AKLT.Cert.H1.Check.P0000Packed.local5_checked`
- `AKLT.Cert.H1.Check.P0000Packed.local6_checked`
- `AKLT.Cert.H1.Check.P0000Packed.local7_checked`
- `AKLT.Cert.H1.Check.P0000Packed.matrix_constructed`
- `AKLT.Cert.H1.Check.P0000Packed.row000_constructed`
- `AKLT.Cert.H1.Check.P0000_bonds`
- `AKLT.Cert.H1.Check.P0000_code`
- `AKLT.Cert.H1.Check.P0000_covered`
- `AKLT.Cert.H1.Check.P0000_gramRows`
- `AKLT.Cert.H1.Check.P0000_triangular`
- `AKLT.Cert.H1.Check.P2180.active`
- `AKLT.Cert.H1.Check.P2180.basisUnique`
- `AKLT.Cert.H1.Check.P2180.bonds`
- `AKLT.Cert.H1.Check.P2180.centralUnique`
- `AKLT.Cert.H1.Check.P2180.clears`
- `AKLT.Cert.H1.Check.P2180.covered`
- `AKLT.Cert.H1.Check.P2180.exponent_zero`
- `AKLT.Cert.H1.Check.P2180.fromDefs`
- `AKLT.Cert.H1.Check.P2180.fromDefs_matrix`
- `AKLT.Cert.H1.Check.P2180.fromDefs_positive`
- `AKLT.Cert.H1.Check.P2180.fromDefs_positive_complex`
- `AKLT.Cert.H1.Check.P2180.groups`
- `AKLT.Cert.H1.Check.P2180.groupsEmpty`
- `AKLT.Cert.H1.Check.P2180.integrand`
- `AKLT.Cert.H1.Check.P2180.inversion_allowed`
- `AKLT.Cert.H1.Check.P2180.operator_one`
- `AKLT.Cert.H1.Check.P2180.polynomial`
- `AKLT.Cert.H1.Check.P2180.sector_one`
- `AKLT.Cert.H1.Check.P2180.spins`
- `AKLT.Cert.H1.Check.P2180.status_center`
- `AKLT.Cert.H1.Check.P2180.status_east`
- `AKLT.Cert.H1.Check.P2180.status_north`
- `AKLT.Cert.H1.Check.P2180.threshold_entry`
- `AKLT.Cert.H1.Check.P2180.vectors`
- `AKLT.Cert.H1.Check.P2180.vectorsEmpty`
- `AKLT.Cert.H1.Check.P2180.weight`
- `AKLT.Cert.H1.Check.P2180B00.checked`
- `AKLT.Cert.H1.Check.P2180B00.header_checked`
- `AKLT.Cert.H1.Check.P2180B00.positive_complex`
- `AKLT.Cert.H1.Check.P2180B00.positive_real`
- `AKLT.Cert.H1.Check.P2180B00.rows000_checked`
- `AKLT.Cert.H1.Check.P2180B00.rows_checked`
- `AKLT.Cert.H1.Check.P2180Packed.constructed_positive_real`
- `AKLT.Cert.H1.Check.P2180Packed.denominator_checked`
- `AKLT.Cert.H1.Check.P2180Packed.local0_checked`
- `AKLT.Cert.H1.Check.P2180Packed.local1_checked`
- `AKLT.Cert.H1.Check.P2180Packed.local2_checked`
- `AKLT.Cert.H1.Check.P2180Packed.local3_checked`
- `AKLT.Cert.H1.Check.P2180Packed.local4_checked`
- `AKLT.Cert.H1.Check.P2180Packed.local5_checked`
- `AKLT.Cert.H1.Check.P2180Packed.local6_checked`
- `AKLT.Cert.H1.Check.P2180Packed.local7_checked`
- `AKLT.Cert.H1.Check.P2180Packed.matrix_constructed`
- `AKLT.Cert.H1.Check.P2180Packed.row000_constructed`
- `AKLT.Cert.H1.Check.P7237B00.checked`
- `AKLT.Cert.H1.Check.P7237B00.header_checked`
- `AKLT.Cert.H1.Check.P7237B00.positive_complex`
- `AKLT.Cert.H1.Check.P7237B00.positive_real`
- `AKLT.Cert.H1.Check.P7237B00.rows000_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows001_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows002_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows003_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows004_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows005_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows006_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows007_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows008_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows009_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows010_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows011_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows012_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows013_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows014_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows015_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows016_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows017_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows018_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows019_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows020_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows021_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows022_checked`
- `AKLT.Cert.H1.Check.P7237B00.rows_checked`
- `AKLT.Cert.H1.Check.P7237Packed.constructed_positive_real`
- `AKLT.Cert.H1.Check.P7237Packed.denominator_checked`
- `AKLT.Cert.H1.Check.P7237Packed.local0_checked`
- `AKLT.Cert.H1.Check.P7237Packed.local1_checked`
- `AKLT.Cert.H1.Check.P7237Packed.local2_checked`
- `AKLT.Cert.H1.Check.P7237Packed.local3_checked`
- `AKLT.Cert.H1.Check.P7237Packed.local4_checked`
- `AKLT.Cert.H1.Check.P7237Packed.local5_checked`
- `AKLT.Cert.H1.Check.P7237Packed.local6_checked`
- `AKLT.Cert.H1.Check.P7237Packed.local7_checked`
- `AKLT.Cert.H1.Check.P7237Packed.matrix_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row000_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row001_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row002_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row003_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row004_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row005_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row006_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row007_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row008_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row009_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row010_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row011_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row012_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row013_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row014_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row015_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row016_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row017_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row018_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row019_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row020_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row021_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row022_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row023_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row024_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row025_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row026_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row027_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row028_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row029_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row030_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row031_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row032_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row033_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row034_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row035_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row036_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row037_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row038_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row039_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row040_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row041_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row042_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row043_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row044_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row045_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row046_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row047_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row048_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row049_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row050_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row051_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row052_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row053_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row054_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row055_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row056_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row057_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row058_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row059_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row060_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row061_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row062_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row063_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row064_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row065_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row066_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row067_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row068_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row069_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row070_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row071_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row072_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row073_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row074_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row075_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row076_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row077_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row078_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row079_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row080_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row081_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row082_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row083_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row084_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row085_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row086_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row087_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row088_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row089_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row090_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row091_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row092_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row093_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row094_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row095_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row096_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row097_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row098_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row099_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row100_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row101_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row102_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row103_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row104_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row105_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row106_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row107_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row108_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row109_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row110_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row111_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row112_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row113_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row114_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row115_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row116_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row117_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row118_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row119_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row120_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row121_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row122_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row123_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row124_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row125_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row126_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row127_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row128_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row129_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row130_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row131_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row132_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row133_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row134_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row135_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row136_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row137_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row138_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row139_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row140_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row141_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row142_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row143_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row144_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row145_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row146_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row147_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row148_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row149_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row150_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row151_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row152_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row153_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row154_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row155_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row156_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row157_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row158_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row159_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row160_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row161_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row162_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row163_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row164_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row165_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row166_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row167_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row168_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row169_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row170_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row171_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row172_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row173_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row174_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row175_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row176_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row177_constructed`
- `AKLT.Cert.H1.Check.P7237Packed.row178_constructed`
- `AKLT.Cert.H1.Check.P7237PackedBatch4.row000_constructed`
- `AKLT.Cert.H1.Check.P7237PackedBatch4.row001_constructed`
- `AKLT.Cert.H1.Check.P7237PackedBatch4.row002_constructed`
- `AKLT.Cert.H1.Check.P7237PackedBatch4.row003_constructed`
- `AKLT.Cert.H1.Check.P7237_bonds`
- `AKLT.Cert.H1.Check.P7237_code`
- `AKLT.Cert.H1.Check.P7237_covered`
- `AKLT.Cert.H1.Check.P7237_gramRows`
- `AKLT.Cert.H1.Check.P7237_triangular`
- `AKLT.Cert.H1.Check.catalogue_length`
- `AKLT.Cert.H1.Check.catalogue_nodup`
- `AKLT.Cert.H1.Check.catalogue_sorted`
- `AKLT.Cert.H1.contractSpins_add`
- `AKLT.Cert.H1.contractSpins_monomial`
- `AKLT.Cert.H1.gramResidualRows_of_checked`
- `AKLT.Cert.H1.lowerTriangularCheck_sound`
- `AKLT.Cert.H1.momentNumerator_sound`
- `AKLT.Cert.H1.packed_outer_product`
- `AKLT.Cert.H1.pauliZ_sound`
- `AKLT.Cert.H1.smallPattern_bonds`
- `AKLT.Cert.H1.smallPattern_covered`
- `AKLT.Cert.H1.small_active`
- `AKLT.Cert.H1.small_fromDefs_positive`
- `AKLT.Cert.H1.small_groups`
- `AKLT.Cert.H1.small_integrand_current`
- `AKLT.Cert.H1.small_integrand_next`
- `AKLT.Cert.H1.small_leafNeighbour`
- `AKLT.Cert.H1.small_packed_fromDefs`
- `AKLT.Cert.H1.small_polynomial_current`
- `AKLT.Cert.H1.small_polynomial_next`
- `AKLT.Cert.H1.small_radius`
- `AKLT.Cert.H1.small_spinSites`
- `AKLT.Cert.H1.small_status_center`
- `AKLT.Cert.H1.small_status_east`
- `AKLT.Cert.H1.strictlyIncreasing_sound`
- `AKLT.Cert.H1.tableCheck_sound`

# Phase 2 orchestrator summary (historical)

- H1 production engine implemented for all 7,962 patterns / 12,173 blocks and both representations.
- Generated data/checks moved outside AKLT; explicit CertData target; ordinary library has no generated imports.
- All parities, basis lists, original-token inversion, adaptive packing and geometry compilers are implemented.
- Packed checks use shared M rows; independent reductions are batched with bounded work.
- Full raw coverage checker: 500 frontiers / 4,000 corner reductions; all passed.
- All 7,962 representative keys and raw input geometries passed kernel checks.
- Cold v2 validation: 1,125 modules / zero reuse / 28.16 min at 24; pilot 100 patterns, all 194 blocks / 3,704 rows.
- Six negative/shape checks, 100-pattern witness aggregation and transitive replay rejection passed.
- Nine generic conditional assemblies kernel checked, including both original Top targets and H1 V2 existence.
- Exact active mathematical queue: 33 closed Props; different cheaper model must make every first attempt.
- Root wrote zero new mathematical leaf proofs; 321 historical audited declarations retained unchanged.
- Historical source preservation: all 27,829 frozen proof-source hashes match; 333-declaration audit reran.
- Full numerical production and full generated Targets build remain unrun; no unconditional H1 proof claimed.
- Merge ARCH_0 first for source builds; measured imports use its current supplied prebuilt Defs/Top.
- Data/Check declaration namespaces differ from bundle file ownership; use the owner maps.
- Imaginary packed values/off-weight checks are within each parity; cross-parity/U-kernel facts are analytic leaves.
- Optional unsplit numeric export covers all cases; the production Defs bridge uses split parity mode.
- Final whole-catalogue aggregation memory is unmeasured; cap 64 GiB with RAM reservations.
- Forecast: about 115 CPU-hours, range 92–173, reserve 200; 24 workers 4.4–9.4 h wall.
- 48-worker forecast 2.3–5.0 h needs authorization and about 600 GB RAM; current cap remains 24/300 GB.
- Disk: reserve 30 GB / cap 40 GB; abort below 100 GB root free; superseded compiled outputs cleaned.
- H3′ pilot belongs to CERT_H3; this delivery is H1 only.
- Orchestrator: assign the 33 first attempts, freeze the statement layer, then run/close the full numerical DAG.

# Phase 3 orchestrator summary (historical)

- COMPLETE: 39-file hand-written merge set; standalone root AKLT.Cert.H1.Production.All/Audit.
- Exactly 33 open closed Props in leaves-open.json; no data blocks; no new root leaf proof.
- All 17 reusable Lean sources built on clean main; all 23 external sources still match latest main.
- Active older statement files were left untouched; 15 path mismatches recorded, including two relevant ones.
- Generated attachment stays outside AKLT: CertDataH1, CertData/H1/Generated/Batch and Bridge.
- Full finite work passed: 7,962 patterns, 12,173 blocks, 144,554 constructed rows.
- All 7,964 owners and 158,230 logical components independently verified; 101,536 logical check components.
- All 414,638 generated theorem axiom audits passed; only propext, Classical.choice, Quot.sound.
- Full generated finiteData/certificateV2/targets assemblies kernel checked, still conditional on the leaves.
- Measured portfolio 139.002 CPU-hours; campaign about 3.707 h wall, including reuse and restarts.
- Constructor rows 109.236 CPU-hours / 7.540 GiB; Gram + positivity assembly 8.770 CPU-hours.
- Global aggregation measured: about 8 s wall each, maximum 11.153 GiB RSS.
- Before H3 done: <=24 processes; afterwards main <=42 plus one frontier, combined <=43.
- All owner oleans retained; owner and unbundled sources compacted losslessly; receipts record all input hashes.
- Disk about 17.2 GB / 40 GB; root free well above 100 GiB; memory availability floor 40 GB.
- 24-worker projection 6.40–8.73 h; 44-worker projection 3.70–5.04 h under declared reservations.
- 48 is hypothetical and also capped at 42 by this RAM reservation policy; no 48-process run occurred.
- Logger interleaving and redundant-transitive-import audit issues fixed; no Lean source/arithmetic change.
- Normal-cache publication and transitive replay regressions passed; final registry marks all numeric modules checked.
- All 27,829 frozen source hashes unchanged; 321 pre-rule audited declarations retained and listed.
- Open work: prove the exact 33 Props, respecting the cheaper-model first-attempt policy, then close Top targets.
- Preserve matched core/dependency artifacts when attaching oleans; source Lake rebuilds can repeat reductions.
- H3 is outside this lane; no remaining finite H1 computation or exporter implementation is pending.

# closing phase

**STATUS: PROVED FROM DEPS.** Both requested H1 contracts now have named,
hypothesis-free proofs of exactly their current types on main. All 33 merged leaf
proofs fit their closed-Prop statements and the existing assembly without a mismatch.
No statement, leaf definition, or previous hand-written bridge was changed.

Fresh worktree: `/home/ubuntu/aklt/wt/CERT_H1/_close_main`. Main revision:
`63d176add85a0eae6c862c54849a495434b7d438`. The old production tree remains the read-only artifact source;
numerical production was not rerun.

## Closed declarations

Both are exported by module **`CertData.H1.Close.Main`**:

```lean
theorem CertData.H1.Close.finiteData :
    AKLT.Blueprint.Top.H1FiniteDataStatementV2

theorem CertData.H1.Close.certificate :
    AKLT.Blueprint.Top.CertificateStatement
```

The module constructs the exact `ConstructorPremises` and `CoveragePremises`
records using `AKLT.W.H1C001.main` through `AKLT.W.H1C033.main`, closes the retained
`CertData.H1.Generated.Check.Targets.targets` assembly, and projects the two results.
The extra IntegerCheck premises are also discharged; no leaf or certificate argument
remains on either exported theorem. Actual `#print` output is:

```text
theorem CertData.H1.Close.finiteData : AKLT.Blueprint.Top.H1FiniteDataStatementV2 :=
closedTargets.right.right
theorem CertData.H1.Close.certificate : AKLT.Blueprint.Top.CertificateStatement :=
closedTargets.right.left
```

For each exported proof, actual `#print axioms` output is:

```text
[propext, Classical.choice, Quot.sound]
```

All 33 merged writer terms were checked with exact-type `example` declarations and
individually audited with `#print axioms`. The private premise/target assemblies
were audited too. A separate module **`CertData.H1.Close.Audit`** imports the built
closing module, repeats the two exact-type checks and both axiom audits, and checks:

```lean
example : AKLT.Blueprint.Top.Automaton10StatementV2 →
    AKLT.Blueprint.Top.StationaryCheckStatementV2 → AKLT.Challenge.MainStatementV2 :=
  AKLT.Final.main_of_certificates CertData.H1.Close.finiteData CertData.H1.Close.certificate
```

This is an integration check for the final project assembly; only the H3 lane's
arguments remain there. The two named H1 proofs themselves are closed.
There is no `sorry` or other forbidden proof mechanism in the closing sources.

## Files and retained-artifact attachment

Hand-written closing sources:

- `CertData/H1/Close/Main.lean`
- `CertData/H1/Close/Audit.lean`
- `lakefile.toml`: adds `CertData.H1.Close.+` only to the opt-in `CertDataH1` globs.

Exact closing merge list: [closing/merge-set.txt](closing/merge-set.txt).
The default AKLT target is unchanged. No generated certificate module enters it.
The attachments created only in the fresh worktree are:

```text
CertData/H1/Generated -> /home/ubuntu/aklt/wt/CERT_H1/CertData/H1/Generated
.lake/build/lib/lean/CertData/H1/Generated -> /home/ubuntu/aklt/wt/CERT_H1/CertData/H1/Generated
```

The first is the optional source/archive view; the second puts the retained owner
oleans on Lean's import path. Existing H3 paths in the fresh cache were preserved.
The fresh ordinary-AKLT artifacts were used for the library and merged writer proofs.
All 17 H1 library sources and all 23 external AKLT source dependencies match the
production versions byte-for-byte. The ordinary-build H1 artifact bytes differ from
the producer's standalone-build artifacts, but the sources and interfaces agree:
the actual closing build and all exact-type examples succeeded. No artifact override
or statement workaround was needed. [closing/compatibility.json](closing/compatibility.json)
records the comparisons; [closing/attachments.json](closing/attachments.json) records
attachment paths.

From the fresh worktree with those attachments already present, the exact build is:

```sh
cd /home/ubuntu/aklt/wt/CERT_H1/_close_main
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake/build/lib/lean/CertData/H1/Close
/usr/bin/time -v lake env lean -DElab.async=false -DautoImplicit=false -DrelaxedAutoImplicit=false -o .lake/build/lib/lean/CertData/H1/Close/Main.olean CertData/H1/Close/Main.lean
/usr/bin/time -v lake env lean -DElab.async=false -DautoImplicit=false -DrelaxedAutoImplicit=false -o .lake/build/lib/lean/CertData/H1/Close/Audit.olean CertData/H1/Close/Audit.lean
```

| Build | Exit | Wall time | User + system CPU | Peak RSS |
|---|---:|---:|---:|---:|
| Closing Main | 0 | 9.09 s | 9.14 s | 11.231 GiB (11,776,620 KiB) |
| Import/final-interface Audit | 0 | 8.61 s | 8.63 s | 11.430 GiB (11,985,700 KiB) |

Complete outputs: [closing/build.stdout](closing/build.stdout),
[closing/build.stderr](closing/build.stderr), [closing/audit.stdout](closing/audit.stdout),
[closing/audit.stderr](closing/audit.stderr). Machine-readable receipt with source
and new olean hashes: [closing/receipt.json](closing/receipt.json).

## Source rebuild requirements and cost

The closing sources have no missing implementation or proof dependency on current main.
A build using the attached, retained oleans takes the times above. A fully clean source
rebuild of the generated numerical library has additional requirements:

- The saved witness index and 16 chunks under `/home/ubuntu/aklt/data/h1/` must be available.
- Generated sources are compact `.lean.gz` files and standalone builds do not supply Lake
  trace files. Materialize/export a fresh generated directory, restore its sources there,
  and build the `CertDataH1` library. Do **not** decompress through the source-view symlink
  above: that would mutate the retained producer tree.
- The complete exporter/checker recipe is in the producer's `CertData/H1/README.md`.
  Preserve the module layout and matched statement/checker versions. There is no logical
  obstacle to regenerating every check from source; the obstacle to a quick clean rebuild
  is the finite computation itself and the deliberately compact source distribution.
- Repeating the numerical library costs about **139.00 measured CPU-hours** and about
  **17.2 GB** of retained data/artifacts/reports. The measured-DAG production plan projects
  **6.40–8.73 h at 24 workers** or **3.70–5.04 h at a requested 44 workers** under the
  conservative RAM reservations (effective maximum 42). The closing step then adds about
  nine seconds, given the ordinary AKLT library and merged leaf modules are built.

No numerical reduction was repeated for this closing task. No new leaf proof was written;
this phase only composes the accepted numerical certificates and merged leaf theorems.

# ORCH-SUMMARY

- PROVED FROM DEPS: both requested H1 contracts are closed on current main.
- Module CertData.H1.Close.Main exports CertData.H1.Close.finiteData and CertData.H1.Close.certificate.
- Exact types: Top.H1FiniteDataStatementV2 and Top.CertificateStatement; no leaf/certificate parameters.
- All 33 H1C writer terms fit; source/statement/interface mismatch list is empty.
- Axioms for both proofs: propext, Classical.choice, Quot.sound only; no forbidden proof mechanisms.
- Main build: 9.09 s wall, 11.231 GiB RSS; Audit: 8.61 s, 11.430 GiB.
- Audit applies AKLT.Final.main_of_certificates; precisely the two H3 arguments remain.
- Fresh-only attachments reuse retained producer oleans; old production tree is unchanged.
- Merge both CertData/H1/Close Lean modules and the opt-in Lake glob change; see closing/merge-set.txt.
- Closing data stays outside default AKLT; no numerical production or leaf proof was rerun.
- Clean numerical source rebuild needs materialized/decompressed sources, witnesses, about 139 CPU-hours.
- Orchestrator: attach both H3 closed proofs and apply the final assembly; preserve retained artifacts.
