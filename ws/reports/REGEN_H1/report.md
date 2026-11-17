STATUS: PARTIAL (kernel rebuild complete; .git is read-only; measured coverage timing regression remains)

# H1 module-system regeneration

All **7,964 generated owners**, **414,638 exported theorems**, and both closed H1 contracts passed fresh kernel checking against the ported release. Numeric compilation used **155.174 CPU-hours**; closing used **12.59 CPU-seconds**. Diagnostic compiles added **267.40 CPU-seconds**. Total campaign compiler CPU: **155.251 hours**. Python export/runner overhead is excluded.

The campaign from the first fresh compiler launch through closing took **4.989 wall-hours**. All 7,964 compiled owners were absent at initial inspection. No legacy compiled artifact was read, copied, linked, or imported. Dependencies were prebuilt; no Lake update or Mathlib build occurred.

## Closed exports

```lean
CertData.H1.Close.finiteData : AKLT.Blueprint.Top.H1FiniteDataStatementV2
CertData.H1.Close.certificate : AKLT.Blueprint.Top.CertificateStatement
```

Both have no hypotheses. The existing Main and Audit modules contain exact-type `example` checks. Main also checks all 33 ported `AKLT.W.H1C001.main` through `AKLT.W.H1C033.main` leaves and all private premise assemblies. Actual axiom output for each closed export is:

```text
[propext, Classical.choice, Quot.sound]
```

See `closing/Main.stdout`, `closing/Audit.stdout`, and `closing/receipt.json` for exact printed types, all axiom output, commands, hashes, and measurements.

## Generators and arithmetic preservation

The reversible module envelope adds public imports, exposed public definitions, and `backward.proofsInPublic`. No checker, arithmetic expression, proof body, or input number changed. No Lean checker visibility repair was necessary. The only existing Lean edit is a documentation sentence in H1 Close.Main. See `REGEN-CHANGES.md` for every hand-written change.

The full independent data-only re-export took 228.63 seconds and regenerated all 158,230 logical components and 7,964 owners. Every owner matched the transformed retained source byte for byte. The exact owner/dependency/component map also matched. Inputs are the index and 16 witness chunks under `/home/ubuntu/aklt/data/h1`; all 17 hashes match the legacy production input receipt.

## Pilot results

Small and large targets were selected for every one of the 25 kinds, by legacy CPU cost for checks or source bytes for data. Every build used a fresh Lean process. Singleton kinds use the same owner for both roles. The two final global singleton assemblies require the entire DAG and were measured at the end of the same initially clean campaign. All other targets and their shared prerequisites form the 5,092-owner pilot plan.

| Kind / sample | Owner | Legacy CPU s | New CPU s | Legacy GiB | New GiB |
|---|---|---:|---:|---:|---:|
| all_witness_assembly / small | `Allwitnessassembly0000` | 8.25 | 5.83 | 11.153 | 5.850 |
| all_witness_assembly / large | `Allwitnessassembly0000` | 8.25 | 5.83 | 11.153 | 5.850 |
| case_assembly / small | `Caseassembly0248` | 5.59 | 5.29 | 6.842 | 3.767 |
| case_assembly / large | `Caseassembly0099` | 16.49 | 17.49 | 7.147 | 3.936 |
| case_data / small | `Casedata0248` | 4.70 | 3.94 | 6.815 | 3.746 |
| case_data / large | `Casedata0022` | 5.81 | 6.34 | 7.112 | 3.801 |
| constructor_assembly / small | `Constructorassembly0395` | 4.82 | 6.11 | 6.811 | 3.741 |
| constructor_assembly / large | `Constructorassembly0250` | 14.24 | 14.74 | 7.061 | 3.959 |
| constructor_rows / small | `Constructorrows0584` | 47.39 | 33.78 | 6.914 | 3.858 |
| constructor_rows / large | `Constructorrows0112` | 1002.07 | 936.94 | 7.522 | 4.454 |
| coverage_assembly / small | `Coverageassembly0000` | 8.26 | 3.76 | 6.551 | 3.691 |
| coverage_assembly / large | `Coverageassembly0000` | 8.26 | 3.76 | 6.551 | 3.691 |
| coverage_data / small | `Coveragedata0000` | 55.40 | 57.26 | 7.226 | 4.373 |
| coverage_data / large | `Coveragedata0000` | 55.40 | 57.26 | 7.226 | 4.373 |
| coverage_frontier / small | `Coveragefrontier0015` | 68.43 | 86.48 | 7.265 | 4.420 |
| coverage_frontier / large | `Coveragefrontier0004` | 403.86 | 516.92 | 7.483 | 4.636 |
| coverage_header / small | `Coverageheader0000` | 17.80 | 16.32 | 7.827 | 4.977 |
| coverage_header / large | `Coverageheader0000` | 17.80 | 16.32 | 7.827 | 4.977 |
| gram_rows / small | `Gramrows0871` | 4.17 | 2.26 | 3.772 | 2.043 |
| gram_rows / large | `Gramrows0096` | 54.78 | 29.59 | 4.719 | 2.997 |
| index_all_data / small | `Indexalldata0000` | 5.80 | 6.27 | 6.589 | 3.692 |
| index_all_data / large | `Indexalldata0000` | 5.80 | 6.27 | 6.589 | 3.692 |
| index_assembly / small | `Indexassembly0000` | 13.03 | 15.67 | 7.900 | 5.017 |
| index_assembly / large | `Indexassembly0000` | 13.03 | 15.67 | 7.900 | 5.017 |
| index_data / small | `Indexdata0015` | 6.63 | 4.42 | 6.519 | 3.656 |
| index_data / large | `Indexdata0013` | 7.33 | 5.19 | 6.569 | 3.695 |
| index_keys / small | `Indexkeys0015` | 11.62 | 11.08 | 6.572 | 3.699 |
| index_keys / large | `Indexkeys0013` | 18.69 | 20.21 | 6.590 | 3.724 |
| index_witness_assembly / small | `Indexwitnessassembly0015` | 5.80 | 4.79 | 7.447 | 4.081 |
| index_witness_assembly / large | `Indexwitnessassembly0013` | 8.35 | 5.90 | 9.811 | 5.119 |
| input_data / small | `Inputdata0248` | 5.13 | 5.82 | 6.488 | 3.637 |
| input_data / large | `Inputdata0022` | 7.87 | 4.60 | 6.487 | 3.654 |
| input_geometry / small | `Inputgeometry0067` | 6.23 | 8.25 | 6.451 | 3.637 |
| input_geometry / large | `Inputgeometry0164` | 8.08 | 7.59 | 6.493 | 3.647 |
| local_parameters / small | `Localparameters1990` | 6.47 | 4.57 | 6.522 | 3.662 |
| local_parameters / large | `Localparameters1787` | 133.48 | 120.48 | 6.979 | 4.117 |
| matrix_data / small | `Matrixdata0236` | 4.05 | 1.80 | 3.763 | 2.040 |
| matrix_data / large | `Matrixdata0198` | 28.17 | 18.08 | 4.650 | 2.904 |
| network_data / small | `Networkdata0189` | 11.28 | 9.32 | 6.617 | 3.772 |
| network_data / large | `Networkdata0027` | 15.33 | 8.91 | 6.617 | 3.775 |
| pattern_data / small | `Patterndata0194` | 8.05 | 6.51 | 6.524 | 3.665 |
| pattern_data / large | `Patterndata0026` | 10.21 | 11.91 | 6.540 | 3.676 |
| positivity_assembly / small | `Positivityassembly0295` | 5.15 | 5.80 | 3.782 | 2.051 |
| positivity_assembly / large | `Positivityassembly0250` | 46.21 | 43.51 | 5.825 | 4.093 |
| sector_layout / small | `Sectorlayout0380` | 5.44 | 6.70 | 6.816 | 3.741 |
| sector_layout / large | `Sectorlayout0154` | 15.81 | 12.46 | 6.925 | 3.843 |
| sector_network_data / small | `Sectornetworkdata0380` | 7.47 | 5.96 | 6.505 | 3.644 |
| sector_network_data / large | `Sectornetworkdata0236` | 10.84 | 10.35 | 6.564 | 3.697 |
| target_assembly / small | `Targetassembly0000` | 8.00 | 5.36 | 11.150 | 5.842 |
| target_assembly / large | `Targetassembly0000` | 8.00 | 5.36 | 11.150 | 5.842 |

The coverage frontier samples use 26–28% more CPU than their legacy receipts. The small profiled control spends 77.3 seconds in kernel type checking versus 61.3 seconds in the legacy profile. Loading private definition bodies (92.17 CPU-seconds) and default private-proof elaboration (88.01 seconds) did not improve the 85.11-second profiled required-header control. No missing exposed body was found and no definition-preserving repair was identified. Production data, checker definitions, and required headers remain unchanged. This timing regression on `AKLT.Cert.H1.Production.coverageShard` is passed to the orchestrator; details and hashed diagnostic receipts are in `coverage-performance.json`.

## Production totals by kind

| Kind | Owners | CPU hours | Peak GiB |
|---|---:|---:|---:|
| `all_witness_assembly` | 1 | 0.0016 | 5.850 |
| `case_assembly` | 249 | 0.5356 | 3.962 |
| `case_data` | 249 | 0.3533 | 3.801 |
| `constructor_assembly` | 396 | 0.8298 | 3.971 |
| `constructor_rows` | 1161 | 123.1241 | 4.459 |
| `coverage_assembly` | 1 | 0.0010 | 3.691 |
| `coverage_data` | 1 | 0.0159 | 4.373 |
| `coverage_frontier` | 16 | 0.8739 | 4.869 |
| `coverage_header` | 1 | 0.0045 | 4.977 |
| `gram_rows` | 1056 | 7.7153 | 5.016 |
| `index_all_data` | 1 | 0.0017 | 3.692 |
| `index_assembly` | 1 | 0.0044 | 5.017 |
| `index_data` | 16 | 0.0284 | 3.695 |
| `index_keys` | 16 | 0.0910 | 3.728 |
| `index_witness_assembly` | 16 | 0.0291 | 5.119 |
| `input_data` | 249 | 0.3745 | 3.655 |
| `input_geometry` | 249 | 0.5506 | 3.650 |
| `local_parameters` | 1991 | 13.2955 | 4.182 |
| `matrix_data` | 503 | 1.5627 | 2.962 |
| `network_data` | 383 | 1.8966 | 3.817 |
| `pattern_data` | 249 | 0.7340 | 3.678 |
| `positivity_assembly` | 396 | 1.3513 | 4.115 |
| `sector_layout` | 381 | 0.9040 | 3.849 |
| `sector_network_data` | 381 | 0.8934 | 3.697 |
| `target_assembly` | 1 | 0.0015 | 5.842 |

Stage costs use the final accepted receipt for each owner; total compiler CPU includes every successful fresh build event, including any repeated pilot build.

## Resource controls and receipts

Limits were 36 Lean processes and 270 GB RAM, with a 40 GB available-memory floor and 100 GiB free-disk floor. The initial pilot used up to four workers, the shared-prerequisite pilot used 32, and the remaining production used up to 35. A one-worker coverage frontier also ran alongside the 32-worker pilot, for at most 33 Lean processes. The overlap with the initial pilot and small validation/header runs remained below 36. The largest module used 5.987 GiB RSS. A conservative sum of the overlapping runners' sampled peaks is 160.028 GB. Minimum recorded available memory was 341.644 GB; minimum recorded disk was 159.986 GiB.

The append-only `events.jsonl`, individual `receipts/`, separate stdout/stderr/GNU-time files in `logs/`, and theorem-by-theorem `.axioms.json` files record source hashes, all modern module artifact parts, exit status, CPU/wall time, peak RSS, and exact theorem names. Independent `production_receipts.py verify` checked all dependency keys, actual import edges, sources, artifacts, and complete axiom sets. Only propext, Classical.choice, and Quot.sound occur. `cache-test.json` records successful unchanged replay, transitive invalidation, expected kernel rejection, and restoration.

All 7,964 production sources remain under `CertData/H1/Generated/Batch/` and `Bridge/`. All modern objects remain under `.lake/build/lib/lean/CertData/H1/Generated/`; closing objects are under the adjacent `Close/`. They are untracked. No production owner source was deleted or compacted. The duplicate scratch tree was removed only after recording all 166,194 hashes in `scratch-sources.sha256`. The complete data-only command recreates it.

`SOURCES.sha256` covers every generated source; `COMPILED.sha256` covers all 23,892 generated compiled artifact parts. `verified-production.json` and `closing/receipt.json` give their typed receipts and timings. The deterministic source archive is `/home/ubuntu/aklt/reports/REGEN_H1/H1-module-sources.tar.gz` (25,987,925 bytes), SHA-256 `a27c7dc50ccf88bf53ddeb1d739764eebe623c763bc31ec3f34fd521af9c543f`. The official installer passed in a fresh scratch project and every installed source hash matched.

## Commands and hand-off

Exact commands to regenerate from inputs, transform retained sources, build/resume the family, verify receipts, and close both contracts are in `REGEN-H1.md`. The final assembly imports `CertData.H1.Close.Main` and the H3 closing module. It needs the H1 source archive and these matching normal artifacts, including `.olean.private` and `.olean.server`. Lake trace files are not synthesized; `lake env lean` consumes the artifacts directly, while `lake build` may repeat reductions.

The official source checks found no generated-source issue. The only two existing package issues are the author/provenance TODO and missing root LICENSE. Lean parsed all 9,079 present first-party headers without error. Combined H3/Solution/Audit and the unconditional Comparator/NanoDa/con-ron pipeline remain the orchestrator’s joint-release work.

## Git delivery constraint

The release mounts `.git` read-only. `git add` failed with `Unable to create .git/index.lock: Read-only file system`; approval escalation is unavailable. A complete hand-written-change commit patch is prepared in a writable scratch clone for application by the orchestrator. No generated source or object belongs in that commit.

Commit artifact: `44af5f59ccd4f3eb2e28f9a1f106ce07e99dd21a` in `/tmp/regen-h1-commit`,
base `d1320320e7cbf2d216d0afc87be92aabb206d690`. All 18 hand-written files in the release match that commit;
no generated source or object is included. Patch: `/home/ubuntu/aklt/reports/REGEN_H1/H1-module-system.patch`, SHA-256
`5e20992f17b6f6320e4afaa9edabce44eaa9b461419b92d80d3c3fe98a865434`. Bundle: `/home/ubuntu/aklt/reports/REGEN_H1/H1-module-system.bundle`, SHA-256
`9d88d204c8193d5d63e603645fb6bc00707c2718f816ea426cedca293880ef80`. The bundle and reverse patch check passed.
In a fresh writable clone at the base commit, apply `git am /home/ubuntu/aklt/reports/REGEN_H1/H1-module-system.patch`;
this release clone itself still has its original Git HEAD because its metadata is read-only.

The final source/header recheck again parsed all 9,079 present sources and found
only the existing package author/provenance TODO and missing LICENSE. See
`final-source-checks.json` and `final-headers.json`.

## ORCH-SUMMARY

- H1 kernel rebuild complete: 7,964 owners and 414,638 exported theorem audits.
- Closed exports: CertData.H1.Close.finiteData and CertData.H1.Close.certificate; exact original types.
- Both exports use only propext, Classical.choice, and Quot.sound; no hypotheses remain.
- Numeric CPU 155.174 h; closing CPU 12.59 s; peak module RSS 5.987 GiB.
- All 25 kinds have paired same-owner legacy comparisons; final global singleton pilots occur after prerequisites.
- All owners match full data-only regeneration byte for byte; all input hashes match legacy production.
- No arithmetic/checker/proof edit; Close.Main has one documentation-only edit.
- Coverage frontier CPU is 26–28% higher; private-body/proof-scope tests did not repair it; see coverage-performance.json.
- All production sources and all modern artifact parts remain in this release; no legacy object reused.
- SHA-256 source/compiled manifests, source archive, installer test, and per-theorem receipts are delivered.
- Full reproduction commands are in REGEN-H1.md; all scratch-source removals followed hashing.
- No dependency rebuild, Lake update, package write, or sub-agent was used.
- Scratch commit 44af5f59ccd4 and patch/bundle delivered; exact open delivery is applying it to writable release Git metadata.
- Existing author/provenance TODO and root LICENSE remain for the orchestrator.
- Joint release still needs H3, final assembly, strict Audit, Comparator, NanoDa, and con-ron.
