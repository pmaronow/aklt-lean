STATUS: COMPLETE

The two H3′ certificate statements are proved without hypotheses, at exactly their existing Top V2 types. Both closing modules compiled successfully using the retained numerical certificates and the merged leaf proofs. No numerical production was rerun, and no statement or existing tracked source was changed.

The headline is now closed as well. The appended **final closing** section records the H1 attachment and the four unconditional final theorems.

## Delivered declarations

Module **`CertData.H3.Close.Main`**, source [Main.lean](/home/ubuntu/aklt/wt/CLOSE_H3/CertData/H3/Close/Main.lean):

```lean
CertData.H3.Close.automaton10 : AKLT.Blueprint.Top.Automaton10StatementV2
CertData.H3.Close.stationaryCheck : AKLT.Blueprint.Top.StationaryCheckStatementV2
```

Each declaration has no parameters. The module contains an `example` at each exact Top type, and `#print` confirms both closed theorem types. `automaton10` applies `CertData.H3.Bridge.automatonV2_from_leaves` to the actual generated graph and its checked receipts. `stationaryCheck` applies the retained `CertData.H3.Bridge.All.stationary_from_leaves` to the proved leaf bundles, retaining all five generated stationary cases.

Module **`CertData.H3.Close.Leaves`**, source [Leaves.lean](/home/ubuntu/aklt/wt/CLOSE_H3/CertData/H3/Close/Leaves.lean), also exports these hypothesis-free assembly facts:

```lean
CertData.H3.Close.automatonLeaves : CertData.H3.Bridge.AutomatonBridgeLeaves
CertData.H3.Close.sharedCaseLeaves : CertData.H3.Bridge.SharedCaseLeaves
CertData.H3.Close.productionCaseLeaves : CertData.H3.Bridge.ProductionCaseLeaves
```

`Leaves.lean` imports `AKLT.W.H3C001.Main` through `AKLT.W.H3C056.Main` and checks all 56 `AKLT.W.H3CNNN.main` declarations by exact-type examples, in the original handoff order. The mapping was checked against both `leaves-open.json` and the campaign state map; [leaf-map.json](leaf-map.json) records it. Every leaf fits; there is no type mismatch, residual obligation, or replacement proof.

The source-only merge set is exactly [merge-set.txt](merge-set.txt): the two new files under `CertData/H3/Close/`. They belong to the opt-in `CertData` library. `lakefile.toml`, `CertData.lean`, the hand-written root, and the default `AKLT` target are unchanged. A downstream consumer imports `CertData.H3.Close.Main` explicitly.

## Kernel and soundness checks

The successful build printed:

```text
'CertData.H3.Close.automatonLeaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.H3.Close.sharedCaseLeaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.H3.Close.productionCaseLeaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.H3.Close.automaton10' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.H3.Close.stationaryCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 56 imported leaf theorems were also audited with `#print axioms`; each uses a subset of the same three permitted axioms. All 61 outputs are in [axioms.txt](axioms.txt), with complete compiler output in [build-Leaves.log](build-Leaves.log) and [build-Main.log](build-Main.log). Both new source files pass the forbidden-feature scan, including absence of `sorry`, and compilation produced no warnings or errors. [verification.json](verification.json) records the checks and source/olean hashes; [source-audit.json](source-audit.json) records the source scan.

## Compatibility and attachment

The source base is `63d176add85a0eae6c862c54849a495434b7d438`, using Lean `leanprover/lean4:v4.35.0-rc2` and the project's pinned, prebuilt Mathlib.

All **18 hand-written H3 Lean sources** are byte-identical in this worktree, the read-only certificate lane, and the phase-3 merge-set hash receipt. All **49 retained sources** of the original clean hand-written dependency closure also match their phase-3 hashes, including the Top V2 statements and their definitions. The fiftieth entry was the temporary `CertData.H3.MergeAudit`, which is not an imported dependency. Evidence: [compatibility.json](compatibility.json). **There was no interface drift and no bridge repair.**

The accepted 5,035-module production manifest comprises **5,032 generated modules and three hand-written bridge modules**. The generated modules are attached here as follows:

- **5,032 retained oleans**, totaling **31,572,514,984 bytes**, copied into `.lake/build/lib/lean/CertData/H3/` and verified against every phase-3 SHA-256.
- **2,692 available generated sources**, totaling **21,948,038 bytes**, copied under `CertData/H3/` and verified against the phase-3 source hashes.
- **2,340 compacted plane/endpoint sources** remain absent. Their retained oleans are attached; their numerical checks were not rerun.

The three existing hand-written manifest entries are `CertData.H3.Bridge.Production`, `CertData.H3.Bridge.LegacyTargets`, and `CertData.H3.Bridge.FamilyAssembly`. Existing locally built hand-written artifacts were preserved. Two missing hand-written dependencies, `CertData.H3.Kernel.Literal` and `CertData.H3.Bridge.FamilyAssembly`, were supplied from the lane after source equality checks; their binary hashes are in [supplemental-handwritten.json](supplemental-handwritten.json).

Hard-linking returned `EXDEV` across the managed worktree mounts, so all generated artifacts were copied. The lane was only read. [attachment.json](attachment.json) inventories every attached generated module and the preserved hand-written entries. The final complete hash-verification pass took **31.00 seconds**; this is verification time, not the earlier copy duration.

To reproduce the attachment into this already-built worktree layout:

```sh
python3 /home/ubuntu/aklt/reports/CLOSE_H3/attach.py
```

The script checks compatibility, copies absent artifacts, verifies existing generated artifacts, and never invokes the production runner. Generated attachment sources are build inputs, separate from the two-file source merge set.

## Exact build and measurements

From the supplied ordinary-library build with the generated oleans attached, the exact timed closing build was:

```sh
/usr/bin/time -v -o /home/ubuntu/aklt/reports/CLOSE_H3/build.time \
  bash /home/ubuntu/aklt/reports/CLOSE_H3/build.sh
```

The [build script](build.sh) sets `PATH="$HOME/.elan/bin:$PATH"`, enters `/home/ubuntu/aklt/wt/CLOSE_H3`, and runs these two Lean commands sequentially, with individual timing/output receipts:

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DElab.async=false \
  -o .lake/build/lib/lean/CertData/H3/Close/Leaves.olean CertData/H3/Close/Leaves.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DElab.async=false \
  -o .lake/build/lib/lean/CertData/H3/Close/Main.olean CertData/H3/Close/Main.lean
```

| Build | Wall time | Peak process RSS | Exit |
|---|---:|---:|---:|
| `Close.Leaves` | 4.29 s | 6,854,520 KiB | 0 |
| `Close.Main` | 8.46 s | 18,803,604 KiB | 0 |
| Complete closing build | **12.76 s** | **18,803,604 KiB = 19.255 GB = 17.933 GiB** | **0** |

The complete build used 6.42 user CPU seconds and 6.41 system CPU seconds. At most **one Lean process** ran at a time. Timing receipts: [build.time](build.time), [build-Leaves.time](build-Leaves.time), [build-Main.time](build-Main.time). The build occurred on the shared machine, with attachment hashing also active. It used prebuilt Mathlib and project dependencies; it performed no package updates or Mathlib builds.

An earlier closing attempt passed all leaf checks, then stopped at the missing `Kernel.Literal.olean`; its logs are preserved under [attempt-1](attempt-1/build-Main.log). Attachment bookkeeping initially encountered the three already-built hand-written manifest entries. These were packaging issues, resolved by preserving source-identical local artifacts and supplying the missing hand-written dependencies. No Lean proof or interface was changed to resolve them.

## Disk and clean-source rebuild cost

The attached worktree uses approximately **39.40 GB allocated** (**39.34 GB apparent**), including its preexisting ordinary build, all copied generated oleans, generated sources, and the closing modules. Reports add only a few MB. This is below the 60 GB limit. [disk.json](disk.json) records the directory measurements. No scratch numerical dataset was created for this task.

A clean numerical rebuild was deliberately not run. The accepted production receipts give the cost baseline:

- Rebuilding the 5,035 production-manifest modules previously consumed **19.455275 CPU hours**, with **21.023092 hours** as the sum of measured per-module wall times and **20.10 GB** peak RSS for one process.
- An ideal eight-way CPU-time projection is **2.432 hours**, before scheduling, I/O, dependency serialization, and other work. This is not a measured wall time at this task's 8-process/120-GB limit; a memory-aware scheduler must respect that limit. The lane's earlier 32-worker elapsed time is not a forecast for this budget.
- A source rebuild must first regenerate the **2,340 compacted literal files**, totaling **30,688,053,326 source bytes**, from the archived five potential inputs. Those sources plus the retained production oleans already exceed **62.26 GB**, before the ordinary build. To remain under 60 GB, regenerate/build/compact cases successively rather than retaining every literal source at once.
- The original clean 50-module hand-written closure took **86.31 seconds at three workers**. A fully clean build must additionally compile the merged leaf-proof dependency closure and then the two closing modules. A clean timing for that whole merged closure, source-regeneration time, and a complete 8-process rebuild were not measured here. The **12.76-second** figure measures the closing build with the supplied dependency oleans attached.

The numerical baseline and archived input hashes are recorded in the lane's [production receipt](/home/ubuntu/aklt/reports/CERT_H3/phase3/production-receipt.json), [module receipts](/home/ubuntu/aklt/reports/CERT_H3/phase3/production-modules.json), [compaction inventory](/home/ubuntu/aklt/reports/CERT_H3/phase3/compacted_sources.json), and [input inventory](/home/ubuntu/aklt/reports/CERT_H3/phase3/production-inputs.json). These historical measurements are reported as evidence, not repeated numerical work.

## Open issues

None for the requested two Top statements. There are no remaining leaf hypotheses, no leaf/assembly mismatch, and no statement changes. Independent-checker work and other certificate lanes are outside this delivery.

## H3 certificate handoff summary

- STATUS: COMPLETE; both requested Top V2 statements are closed Lean theorems.
- Module: `CertData.H3.Close.Main`.
- Proof: `CertData.H3.Close.automaton10 : AKLT.Blueprint.Top.Automaton10StatementV2`.
- Proof: `CertData.H3.Close.stationaryCheck : AKLT.Blueprint.Top.StationaryCheckStatementV2`.
- Merge only the two sources in `merge-set.txt`, both under `CertData/H3/Close/`.
- Helper module: `CertData.H3.Close.Leaves`; all 56 original leaf types fit exactly.
- Every exported theorem has no hypotheses and uses only the three permitted axioms.
- All 18 H3 hand-written sources and 49 original dependency sources match; no interface drift or repair.
- Retained numerical work reused: 5,032 generated oleans; three manifest entries are hand-written.
- Attachment uses copies because cross-mount hard links failed; absent handwritten dependencies also attached.
- Build: `bash /home/ubuntu/aklt/reports/CLOSE_H3/build.sh`; timed wall 12.76 s, peak RSS 19.255 GB.
- One Lean process at a time; approximately 39.40 GB allocated worktree storage.
- No numerical production rerun; no existing tracked source or default target changed.
- Clean-source cost is a historical baseline/projection; the whole merged clean closure was not retimed.
- Open theorem names: none. Orchestrator action: merge the two sources and retain/attach the generated artifacts for consumers.

## final closing

**STATUS: COMPLETE.** Module **`CertData.Close.All`**, in [CertData/Close/All.lean](/home/ubuntu/aklt/wt/CLOSE_H3/CertData/Close/All.lean), exports exactly the four requested hypothesis-free theorems. Their actual Lean-printed declaration headers are:

```text
theorem CertData.Close.h1 : AKLT.Blueprint.Top.H1Statement :=
theorem CertData.Close.h2 : AKLT.Blueprint.Top.H2Statement :=
theorem CertData.Close.h3 : AKLT.Blueprint.Top.H3Statement :=
theorem CertData.Close.main : AKLT.Challenge.MainStatementV2 :=
```

Each has an exact-type `example` in the module. The existing analytic assemblies have exactly the needed result types; there is no gap or additional analytic obligation:

- `h1` uses `AKLT.Blueprint.H1.h1Theorem_of_certificate`, followed by `AKLT.Blueprint.H1.h1_of_theorem`, with the accepted H1 `certificate` and `finiteData` proofs.
- `h2` is the existing `AKLT.Cert.H2.h2`.
- `h3` uses `AKLT.Blueprint.H3.h3_of_leaves_and_checksV2`, the thirty merged analytic proofs `AKLT.W.H3M001.main` through `H3M030.main`, the five adaptation proofs `H3M031.main` through `H3M035.main`, and both closed H3 certificate proofs.
- `main` applies `AKLT.Final.main_of_certificates` directly to `CertData.H1.Close.finiteData`, `CertData.H1.Close.certificate`, `CertData.H3.Close.automaton10`, and `CertData.H3.Close.stationaryCheck`.

Actual `#print axioms` output:

```text
'CertData.Close.h1' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.Close.h2' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.Close.h3' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.Close.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete output, including the four proof terms, is [final/build.log](final/build.log). No compiler warning or error occurred. Both lanes and this final assembly use base commit **`63d176add85a0eae6c862c54849a495434b7d438`**.

### H1 attachment and source compatibility

The accepted closing sources `CertData/H1/Close/{Main,Audit}.lean` and their retained oleans were copied from the read-only `/home/ubuntu/aklt/wt/CERT_H1/_close_main`, with all four hashes checked against the H1 [closing receipt](/home/ubuntu/aklt/reports/CERT_H1/closing/receipt.json). The closing proofs retain exactly the accepted names and types.

All **7,964 H1 owner modules** were attached from the producer. For each module, the retained olean's destination SHA-256 matches the H1 authoritative [verified production receipt](/home/ubuntu/aklt/reports/CERT_H1/phase3/verified-production.json). Its archived source was read, decompressed into this worktree, and checked against the original raw-source SHA-256. This materializes **317,687,703 source bytes** and copies **13,788,543,856 olean bytes**. The attachment took **19.72 seconds**. The producer and its fresh closing worktree were only read; no numerical computation was rerun.

The H1 production manifest itself matches receipt pin `50da2835019f02cbf5ac6fae8d3b07d60d4cdba1842472cf051b548009fd4784`. All **17 reusable H1 Lean sources** and **23 external AKLT dependency sources** match the production source pins and the fresh same-base closing checkout. For the external definitions, the authoritative pins are in the H1 `phase3/merge-verification.json`: the producer's old working checkout contains documented older statement files, while its accepted production used the matching frozen dependencies. The accepted interfaces match this worktree; no interface repair was needed. Evidence: [final/h1-compatibility.json](final/h1-compatibility.json).

The opt-in `CertDataH1` target already existed at this base. Its glob was extended by exactly `"CertData.H1.Close.+"`, matching the H1 lane's lakefile byte-for-byte. `defaultTargets = ["AKLT"]`, the ordinary AKLT globs, and the generic CertData root are unchanged.

The current H3 attachment was independently rehashed against the original phase-3 receipt in **33.30 seconds**: all **5,032 generated modules** still match. The production manifest's other three entries remain the source-identical hand-written bridge modules described earlier. Both attached libraries together contain **12,996 generated modules**, all in the final import closure. Per-module source and olean SHA-256 manifests are [final/h1-manifest.json](final/h1-manifest.json) and [final/h3-manifest.json](final/h3-manifest.json).

### Import-closure soundness audit

The audit traversed the actual project import closure from `CertData.Close.All`. It found **1,097 unchanged hand-written modules on the base main commit** and exactly **four hand-written source modules outside main**:

- `CertData.Close.All`
- `CertData.H1.Close.Main`
- `CertData.H3.Close.Main`
- `CertData.H3.Close.Leaves`

Every one of those four passed the full forbidden-token scan, including absence of `sorry`, `admit`, extra `axiom` declarations, `native_decide`, foreign/unsafe mechanisms, effectful commands, kernel-check skipping, and unbounded heartbeat settings. The copied H1 `Close.Audit` source, outside All's import closure, was scanned too and passed. The 2,340 missing H3 literal source files are all identified generated modules with verified retained oleans. Evidence and source hashes: [final/source-closure-audit.json](final/source-closure-audit.json).

### Exact final build and receipt

With the ordinary AKLT library and retained certificate artifacts attached, the successful build command is:

```sh
bash /home/ubuntu/aklt/reports/CLOSE_H3/final/build.sh
```

The script enters this worktree, adds `$HOME/.elan/bin` to PATH, and executes:

```sh
/usr/bin/time -v -o /home/ubuntu/aklt/reports/CLOSE_H3/final/build.time \
  lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DElab.async=false \
  -o .lake/build/lib/lean/CertData/Close/All.olean CertData/Close/All.lean
```

Measured final build: **14.82 seconds wall**, **7.26 seconds user CPU + 7.59 seconds system CPU**, peak **25,955,668 KiB = 26.579 GB = 24.753 GiB RSS**, exit **0**, with **one Lean process**. [Timing receipt](final/build.time). The combined attached worktree and reports use approximately **53.56 GB allocated**, below the 60 GB cap.

Versions verified locally: **Lean 4.35.0-rc2**, commit `11acb17ec6b07a8f9e9173e6845197929540936b`, and **Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`**. Mathlib and the ordinary project dependencies remained prebuilt. No numerical production, package update, Mathlib build, or statement change occurred.

The requested [final-receipt.json](final-receipt.json) contains the base commit, all four theorem headers exactly as printed, their types and axiom lists, complete per-module SHA-256 manifests for both attached libraries, manifest provenance hashes, build command and measurements, output olean hash, versions, source-closure audit reference, and disk measurements.

The complete source handoff is [final/merge-set.txt](final/merge-set.txt): the two earlier H3 closing sources, the two copied H1 closing sources, `CertData/Close/All.lean`, and the one-line opt-in lakefile change. Attachment/re-audit scripts are in `final/`; no existing Lean source was edited. The headline has no remaining certificate hypotheses and no open issue for this task.

## ORCH-SUMMARY

- STATUS: COMPLETE; final module `CertData.Close.All` is kernel checked.
- `CertData.Close.h1 : AKLT.Blueprint.Top.H1Statement`.
- `CertData.Close.h2 : AKLT.Blueprint.Top.H2Statement`.
- `CertData.Close.h3 : AKLT.Blueprint.Top.H3Statement`.
- `CertData.Close.main : AKLT.Challenge.MainStatementV2`.
- All four have no hypotheses; exact-type examples and axiom checks pass.
- Axioms: propext, Classical.choice, Quot.sound only.
- Base `63d176add85a0eae6c862c54849a495434b7d438`; pinned Lean/Mathlib verified.
- Build: `bash /home/ubuntu/aklt/reports/CLOSE_H3/final/build.sh`; 14.82 s, peak 26.579 GB RSS, one Lean process.
- Attached/hashed: H1 7,964 + H3 5,032 generated modules; complete manifests in final-receipt.json.
- Import-closure scan: all four hand-written modules outside main pass; 1,097 existing modules unchanged.
- Allocated worktree plus reports: about 53.56 GB; default AKLT target unchanged.
- Merge six files in `final/merge-set.txt`; preserve the retained generated artifacts.
- Open issues: none. No interface repair, statement edit, or numerical production rerun.
