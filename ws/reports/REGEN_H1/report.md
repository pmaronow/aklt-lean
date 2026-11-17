STATUS: PARTIAL (fresh kernel checking in progress; release Git metadata is read-only)

# H1 module-system regeneration

Release root: `/home/ubuntu/aklt/rel/H1`. Legacy worktrees are read-only evidence;
no legacy compiled artifact will be imported or copied. The input index and 16
witness chunks are `/home/ubuntu/aklt/data/h1`. The legacy production manifest
contains 7,964 owners, 158,230 logical components, and 414,638 theorem audits.
Its measured cost was 139.002 CPU-hours. Hand-written closing modules are already
ported in this release.

Authorized production limits: at most 36 Lean processes, 270 GB aggregate RAM,
40 GB available-memory floor, and 100 GB free-disk floor. No sub-agents are used.
No Lake update, dependency write, or Mathlib rebuild is permitted.

## Git delivery constraint

The workspace mounts this clone’s `.git` read-only. `git add` failed with
`Unable to create .git/index.lock: Read-only file system`. A commit in this
clone is blocked by that mount; a complete commit patch will be supplied.
Certificate regeneration and verification continue.

## Progress

- Read the release interface, README, port changes, Lake layout, samples, and
  legacy phase 3 and closing reports.
- Initial host memory: 430 GiB available; disk: 302 GiB available.
- All 7,964 transformed owners are byte-identical to full regeneration from the pinned inputs (228.63 s, 158,230 logical components).

## Pilot results

Fresh-process comparisons are recorded in the live table below and `pilot-results.json`. No checker visibility failure has appeared. The official Lean header parser passed all 9,079 present sources. Official source checks found only the release’s existing metadata TODO and missing LICENSE; no generated-source issue was reported. The independent full data-only regeneration passed for every owner; see `data-only-reexport.json`.

<!-- LIVE-PROGRESS -->
Updated UTC: 2026-11-17T06:59:38.198939+00:00

Accepted fresh owners: **2,337 / 7,964**. Exported theorem audits: **101,587**. Accepted CPU time: **51.846 hours**.

Another **1,684** theorem audit prints are present in 32 unfinished module logs; these are not counted as accepted owners.

| Kind | Accepted owners |
|---|---:|
| `constructor_assembly` | 106 |
| `constructor_rows` | 377 |
| `gram_rows` | 866 |
| `local_parameters` | 2 |
| `matrix_data` | 373 |
| `network_data` | 131 |
| `pattern_data` | 2 |
| `positivity_assembly` | 246 |
| `sector_layout` | 112 |
| `sector_network_data` | 122 |

Pilot comparisons (CPU seconds and peak GiB; fresh processes):

| Kind / sample | Owner | Legacy CPU | New CPU | Legacy GiB | New GiB |
|---|---|---:|---:|---:|---:|
| constructor_rows / small | `Constructorrows0584` | 47.39 | 33.78 | 6.914 | 3.858 |
| constructor_rows / large | `Constructorrows0112` | 1002.07 | 936.94 | 7.522 | 4.454 |
| gram_rows / small | `Gramrows0871` | 4.17 | 2.26 | 3.772 | 2.043 |
| gram_rows / large | `Gramrows0096` | 54.78 | 29.59 | 4.719 | 2.997 |
| local_parameters / small | `Localparameters1990` | 6.47 | 4.57 | 6.522 | 3.662 |
| local_parameters / large | `Localparameters1787` | 133.48 | 120.48 | 6.979 | 4.117 |
| matrix_data / small | `Matrixdata0236` | 4.05 | 1.80 | 3.763 | 2.040 |
| matrix_data / large | `Matrixdata0198` | 28.17 | 18.08 | 4.650 | 2.904 |
| network_data / small | `Networkdata0189` | 11.28 | 9.32 | 6.617 | 3.772 |
| network_data / large | `Networkdata0027` | 15.33 | 8.91 | 6.617 | 3.775 |
| positivity_assembly / small | `Positivityassembly0295` | 5.15 | 5.80 | 3.782 | 2.051 |
| positivity_assembly / large | `Positivityassembly0250` | 46.21 | 43.51 | 5.825 | 4.093 |
| sector_layout / large | `Sectorlayout0154` | 15.81 | 12.46 | 6.925 | 3.843 |

The two final singleton assembly kinds require every prerequisite, so their
fresh pilot measurements are recorded at the end of the same clean campaign.
For every singleton kind the small and large samples are the same owner.
All other paired pilot targets are selected by legacy CPU cost for checks or
source bytes for data. Their shared prerequisite closure has 5,092 owners.

<!-- /LIVE-PROGRESS -->

## ORCH-SUMMARY

- Work is in progress; no regenerated certificate is claimed yet.
- Exact open exports: CertData.H1.Close.finiteData and CertData.H1.Close.certificate.
