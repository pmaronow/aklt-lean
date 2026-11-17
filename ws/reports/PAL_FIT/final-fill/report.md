STATUS: COMPLETE

# FINAL_FILL — portable certificate tooling and current source manifests

Workspace: `/home/ubuntu/aklt/wt/PAL_FIT/_fill`.
Baseline: `42b16c34abb52e2e508ae4000cdfd804115ed14c`.
Commit: **`96e4880c7dbb4cf76e92ba82ab5ee1e2f375ecd5`**. Git working tree is clean.

The default cold verifier now contains the complete numeric-input H1 route and requires no external adapter. Operational code and instructions have no fixed user-specific path. Generated source expressions, owner/dependency maps, key calculations, receipt formats, Lean sources, build pins, and Comparator configuration are unchanged. No Lean, Lake, certificate build/verification command, or independent kernel was started. No final-tree or protected report file was written. All work was performed directly without subagents or another model.

## A. H1 tooling

`locations.py` supplies one H1 input setting, `H1_INPUT_DIR`, defaulting to `<repo>/data/h1`, and `H1_REGEN_REPORT`, defaulting to `<repo>/verification/runs/H1`. All five requested numeric readers use that same input constant. It remains anchored to the repository when `H1_REGEN_ROOT` selects a separate scratch output tree. Explicit report options and all existing environment-variable meanings are preserved.

`production_build.py --ram-gb` is an optional aggregate admission/RSS setting, with the existing 270 GB default. The cold driver uses its requested aggregate memory, clamped to the existing 270 GB maximum; H3 keeps its existing 170 GB maximum. Existing per-process caps and the data-only plan's 16/64 GiB reservations are unchanged. An impossible newly lowered reservation is rejected before a compiler query. The normal cold route rejects a memory setting below its fixed 64 GiB terminal-owner reservation. No memory quantity is added to a proof key.

Unused helpers were removed after checking imports, release commands, inventories, and documentation. The numeric route uses none of them:

| Removed tool | Decision |
|---|---|
| `AKLT/Cert/H1/tools/production_bootstrap.py` | Delete: names two nonexistent modules; `lake build Handwritten` already supplies the exact imported prerequisites. |
| `AKLT/Cert/H1/tools/production_merge_check.py` | Delete: development-tree merge validator, not a numeric release step. |
| `AKLT/Cert/H1/tools/production_leaves.py` | Delete: obsolete proof-source export workflow; the release uses the existing hand-written proofs and numeric assemblies. No Lean module was removed. |
| `AKLT/Cert/H1/tools/export_leaves.py` | Delete with its otherwise unused production_leaves wrapper. |
| `AKLT/Cert/H1/tools/production_regen.py` | Delete: retained-source conversion route; release instructions and the driver use complete numeric regeneration. The source conversion functions remain in module_source.py. |
| `AKLT/Cert/H1/tools/production_handoff.py` | Delete: internal report/patch formatter, not a build or receipt-verification dependency. |
| `AKLT/Cert/H1/tools/production_status.py` | Delete: old progress formatter requires paired-sample bookkeeping absent from the numeric route. The portable production_measure.py remains available. |
| `AKLT/Cert/H3/production_plan.py` | Delete: historical planner, unused by the production generator/runner or inventory. |
| `AKLT/Cert/H3/validate_merge.py` | Delete: historical merge validator, unused by the numeric route. |

The other portable wrappers, deterministic archive tool, measurement summarizer, and optional isolated cache test are retained. No surviving tool imports a removed helper. All obsolete instruction references were removed.

## B. H3 tooling

`production.py`, `export.py`, and `generate_prefix.py` use `<repo>/data/h3` and `<repo>/verification/runs/H3` defaults. Explicit `H3_INPUT_DIR` and `H3_REPORT_DIR` values retain their original meaning and are not normalized or rewritten. Prototype emitters retain their exact output expressions. `regen.py` itself is byte-identical to the baseline. The reference command sequence was read from the two supplied final-build shell files; neither file nor build was modified or invoked.

## C. Complete cold verifier

The default 29-stage dry-run contains the existing dependency/cache and hand-written stages, H3 generate/build/close/verify, and the exact H1 sequence:

```text
production_receipts.py inputs --output R/data-input-receipt.json
production_reexport.py --scratch R/export-scratch --install --report-dir R
production_build.py R/data-only-production.json --jobs N --cap-gib 7 --ram-gb M --report-dir R
production_receipts.py verify R/data-only-production.json --report-dir R
production_close.py --report-dir R
```

It then compiles both families' closing modules, `CertData.Close.All`, Solution, and Audit; checks the strict six-export axiom transcript; checks exact Challenge generation, sources, headers, and physical statement comparison with its negative control. Both input/report variables are set explicitly for each family. Reports and temporary numeric exports remain outside the checkout.

The old H1 placeholder and its refusal-to-start branch are gone. `docs/regeneration/H1-INTEGRATION.md` is folded into `H1.md` and removed. The existing `--h1-stage` flag remains an optional custom override with its original argument contract; it is neither needed nor advertised as a prerequisite. Existing uppercase input-family layouts remain accepted, while lowercase directories are the defaults; ambiguous duplicate layouts fail explicitly.

Dry-run tests cover stage order, all five H1 commands, process/aggregate-memory caps, directory names containing spaces, no file creation, invalid job/memory/report arguments, input selection independent of scratch output, and the existing custom override. The H1 argument parser is tested only as an isolated Python AST prefix; its scheduler and compiler query do not run.

## D. Release documentation

`docs/regeneration/H1.md` and `H1-CHANGES.md` now describe the family, pinned inputs, exact portable commands, resources, receipts, archive, and two closed contracts. They include the reference 7,964 owners, 414,638 theorem audits, 25 kinds, 25-row per-kind table, 158,230 logical components, byte-for-byte generation-route agreement, and the measured 26–28% coverage-frontier CPU increase.

Reference numeric work was 155.174 CPU-hours, with 5.987 GiB peak process RSS and a conservative 160.028 GB sampled aggregate bound. These remain explicitly reference measurements. Final combined-tree figures use the existing `TBD-H1-CPU-HOURS`, `TBD-H1-WALL`, `TBD-H1-PROCESS-MEMORY`, `TBD-H1-AGGREGATE-MEMORY`, and `TBD-H1-RECEIPT` fields; no final result was guessed or substituted.

The H1/CertData READMEs, H3 notes, shared interface, artifact guide, README, VERIFICATION, and portability notes now match the executable numeric route. The measured H1 facts were read from the allowed reference report; no measurement was repeated. Author names, ORCIDs, license, and public URLs in formalization.yaml are byte-identical to the baseline.

## E. Current manifests

Both current port tables had **11** stale source entries. `git show ef79c6c --stat` also lists 11 files, rather than the brief's count of 12. Every actual stale source hash was found and refreshed:

- `AKLT/Blueprint/Gap/Assembly.lean`
- `AKLT/Blueprint/Gap/NodesFinite.lean`
- `AKLT/Blueprint/Gap/NodesMain.lean`
- `AKLT/Blueprint/H1/AssemblyV2.lean`
- `AKLT/Blueprint/Q/NodesSplits.lean`
- `AKLT/Cert/H1/Production/Leaves.lean`
- `AKLT/Final/Skeleton.lean`
- `AKLT/Gen/Bellman/Growth.lean`
- `AKLT/W/H3C034/PrefixStep/Accounting.lean`
- `AKLT/W/H3C034/PrefixStep/Main.lean`
- `CertData/H1/Close/Main.lean`

`verification/port/source-manifest.tsv` updates current `ported_sha256` values while retaining original source/provenance columns. `verification/port/port-list.tsv` updates current hashes and actual byte/line counts. `protected-baseline.json.gz` now pins all 1,162 current Lean/pin/interface/tool files and explains the distinction between its immutable Lean baseline and accompanying Python tool hashes.

`verification/statement-sources.json`, `verification/source-inventory.json`, the generated inventory, all machine-readable regeneration interface files, and both H3 numeric/reference pin files remain byte-identical where unaffected. In particular, neither copied Challenge source was among these comment edits. `Challenge.lean` reproduces byte-for-byte.

`scripts/refresh_manifests.py --write/--check` refreshes/checks metadata without writing a Lean file or invoking Lean/Lake. `inventory.py --check` is now a pure-Python entry point that returns before its optional compiler/dependency inspection. `verify_sources.py` checks active manifest expectations rather than silently accepting stale hashes. `verification/source-digest.txt` records the exact unchanged digest:

```text
c875dff024d396b0b78f1fa955ea5d38e8f577e1d8bd69e970fd02bea906bee9
```

An exhaustive old-hash search finds remaining occurrences only in five historical, source-bound receipt/provenance files under fidelity-fix/, fidelity-round2/, and rename/. They were preserved as evidence for their original source commits. No active hash expectation remains stale. Exact paths are recorded in `stale-hash-search.json` beside this report.

## Constraint proof: receipt and source compatibility

The required command produces no output:

```sh
git diff --stat 42b16c3 HEAD -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain comparator.json
```

All 1,117 Lean files and the additional 16 guarded build/configuration/interface files match the baseline byte-for-byte. Numeric/reference pin files and author metadata were checked separately and match exactly. No compiled artifact, journal, log, input, or running-build file was changed.

H1 build_key remains version `h1-module-key-v3`: it hashes source bytes, fixed build pins, recursive library-source/object fingerprints, and generated dependency keys/artifact hashes. H3 context/source_info/dep_hashes still hash the same tracked Lean map, compiler/toolchain/Lean path, generated sources, and dependency artifacts. Neither hashes the edited Python source. The generated inventory and all input pins are unchanged. Their complete verifiers and compilation/receipt bodies are exact AST matches. Thus a valid existing receipt is judged by the same deterministic functions and inputs when using the same selected paths.

When rechecking the running builds' receipts, retain their existing explicit `H1_REGEN_REPORT` / `--report-dir`, `H3_REPORT_DIR`, and `H3_INPUT_DIR` selections. Those selections behave exactly as before. The intentionally changed defaults point to the repository and do not relocate or rewrite an old receipt's stored paths. H1 verify reads the stored numeric input paths; H3 pin_inputs reads its selected input directory as before.

Each edited certificate tool has the following compatibility justification:

| Tool | Why source bytes, maps, keys, and receipt formats are preserved |
|---|---|
| `AKLT/Cert/H1/tools/locations.py` | New shared input/report constants only. The repository anchor is independent of H1_REGEN_ROOT; explicit H1_REGEN_REPORT values retain their exact Path interpretation. No source emission or receipt/hash function is introduced. |
| `AKLT/Cert/H1/tools/packed.py` | Only the command-line input selection uses INPUT_DIR. Packed arithmetic and all emitted expressions are identical ASTs. |
| `AKLT/Cert/H1/tools/production_bridge_export.py` | Only the input iteration location and explanatory doc string change. The whole remaining AST, including input_literal and all generated templates/dependencies, is identical. |
| `AKLT/Cert/H1/tools/production_coverage.py` | Only the records input location changes. Coverage enumeration, emitted sources, and owner/dependency construction are identical. |
| `AKLT/Cert/H1/tools/production_export.py` | Input and report selection use the shared constants; H1_REGEN_ROOT retains its original output-root behavior. All emitters, checks, string templates, module names, and numeric expressions are identical. |
| `AKLT/Cert/H1/tools/production_receipts.py` | The inputs command reads INPUT_DIR. Its record field names, order, bytes, and hashes are unchanged for the same selected files. The complete verify function is an exact AST match, including stored input-path handling. |
| `AKLT/Cert/H1/tools/production_build.py` | Report default and an optional --ram-gb resource setting change. Default memory remains 270,000,000,000 bytes; all existing option defaults remain. build_key, library_fingerprint, artifact_hashes, axiom_audit, and the entire nested compilation/receipt function main.run are exact AST matches. Removing only the new RAM parser/validation/admission additions and location selection makes the complete builder AST identical. No receipt field is added, removed, or renamed. |
| `AKLT/Cert/H3/production.py` | Only the H3 input/report defaults change. All numeric functions, Oracle, source templates, generation, and owner/dependency maps are identical ASTs. |
| `AKLT/Cert/H3/export.py` | Only input/report defaults change. Normalized whole-file AST identity preserves every prototype literal/source template. |
| `AKLT/Cert/H3/generate_prefix.py` | Only the report default changes, anchored through ex.ROOT. Its loaded exporter uses the new archive default. The whole normalized AST is identical, including module-level numeric work. |
| `AKLT/Cert/H3/production_audit.py` | Module doc string only. Dispatch and imported verifier are unchanged. |

The reproducible `check_tool_compatibility.py --baseline 42b16c3` comparison checks complete normalized ASTs, not just selected names. It proves all retained emitter/bundling/verifier functions unchanged, permits only the requested location expressions and the new resource controls, and separately checks the entire H1 compilation/receipt function. Synthetic probes give identical H1 keys, input receipt JSON bytes, axiom results/rejection, H1 module envelopes, H3 emitted templates, and H3 context/dependency hashes. These probes are metadata tests, not mathematical kernel checks.

Full live H1/H3 receipt verification was **not executed**, as explicitly prohibited. The compatibility proof is code identity plus unchanged inputs, supported by the synthetic probes; it is not a claim that unfinished builds have already completed.

## Checks run

All commands ran from the writable clone or used pure-Python fixtures. No compiler command or certificate-runner command ran.

| Check | Result |
|---|---|
| `refresh_manifests.py --check` | PASS: 1,117 source rows and 1,162 current protected hashes |
| `inventory.py --check` | PASS; returns before any Lean query |
| `make_challenge.py --check` | PASS: exact Challenge and source record |
| `source_digest.py --check verification/source-digest.txt` | PASS: required c875dff0…906bee9 digest |
| `verify_sources.py` | No mechanical finding; exit 1 contains only metadata TODO and missing LICENSE findings |
| `check_axioms.py … --mode handwritten` | PASS: 18 prints in the existing accepted transcript; no new Lean audit claimed |
| `verify_inputs.py` | PASS: all 23 actual numeric input sizes and hashes, through temporary read-only aliases removed afterward |
| `check_tool_compatibility.py --baseline 42b16c3` | PASS: AST and synthetic key/receipt/template invariance |
| `self_check.py` | PASS: syntax, 29-stage dry-run, paths, resources, numeric fixtures, exact statement bytes, altered-read rejection |
| Link check | PASS: all 32 local Markdown links resolve |
| Language/path sweep | PASS, with interface/citation token exclusions below |
| Git whitespace and constrained diff | PASS |
| Build-directory check | No `.lake/build` created |

`verify_headers.py`, physical comparison, independent replays, cache fetching, numeric generation, and actual certificate receipt verification were not run because they can start the forbidden tools or alter generated sources. Their complete commands remain in the driver.

## F. Paths, spelling, and unfilled fields

The refreshed path inventory has 6,504 rows. Every remaining user-specific path is confined to existing historical verification receipts or verbatim review/study reports; none appears in operational scripts or working instructions. The only files with such paths are:

- `verification/feasibility/REL_FEAS.md.gz`
- `verification/fidelity-fix/regression-receipt.json`
- `verification/fidelity-fix/summary.json`
- `verification/fidelity-round2/regression-receipt.json`
- `verification/fidelity-round2/summary.json`
- `verification/rename/regression-receipt.json`
- `verification/rename/summary.json`
- `verification/reviews/FID_ASTRA.md.gz`

No new prose uses British spelling or internal process wording. The one spelling exclusion is the exact paper label `l:colour`. Retained technical-token exclusions preserve existing interfaces and generated bytes: `--campaign-report` / `campaign_report`, mathematical `.leaf` constructors, and the external input role `leaf`. These are code/data spellings, not work-assignment prose. The unchanged numeric-data keys and Lean names were not renamed.

Every remaining active `TBD-*` field is listed below and in `verification/layout/placeholders.json`; none was filled:

| Field | Location(s) |
|---|---|
| `TBD-ALL-HEADER-CHECKS` | `VERIFICATION.md` |
| `TBD-ALL-SOURCE-CHECKS` | `VERIFICATION.md` |
| `TBD-FINAL-LEAN-SOURCE-DIGEST` | `VERIFICATION.md` |
| `TBD-FINAL-RECEIPTS` | `VERIFICATION.md` |
| `TBD-FINAL-SOURCE-COMMIT` | `VERIFICATION.md` |
| `TBD-FINAL-STATEMENT-COMPARISON` | `VERIFICATION.md` |
| `TBD-FULL-AUDIT-LOG` | `VERIFICATION.md` |
| `TBD-FULL-THEOREM-AXIOMS` | `VERIFICATION.md` |
| `TBD-H1-AGGREGATE-MEMORY` | `VERIFICATION.md`, `docs/regeneration/H1.md`, `docs/regeneration/H1-CHANGES.md` |
| `TBD-H1-CPU-HOURS` | `VERIFICATION.md`, `docs/regeneration/H1.md`, `docs/regeneration/H1-CHANGES.md` |
| `TBD-H1-PROCESS-MEMORY` | `VERIFICATION.md`, `docs/regeneration/H1.md`, `docs/regeneration/H1-CHANGES.md` |
| `TBD-H1-RECEIPT` | `VERIFICATION.md`, `docs/regeneration/H1.md`, `docs/regeneration/H1-CHANGES.md` |
| `TBD-H1-WALL` | `VERIFICATION.md`, `docs/regeneration/H1.md`, `docs/regeneration/H1-CHANGES.md` |
| `TBD-H3-AGGREGATE-MEMORY` | `VERIFICATION.md` |
| `TBD-H3-CPU-HOURS` | `VERIFICATION.md` |
| `TBD-H3-PROCESS-MEMORY` | `VERIFICATION.md` |
| `TBD-H3-RECEIPT` | `VERIFICATION.md` |
| `TBD-H3-WALL` | `VERIFICATION.md` |
| `TBD-HANDWRITTEN-BUILD` | `VERIFICATION.md` |
| `TBD-HANDWRITTEN-CPU-HOURS` | `VERIFICATION.md` |
| `TBD-HANDWRITTEN-MEMORY` | `VERIFICATION.md` |
| `TBD-HANDWRITTEN-WALL` | `VERIFICATION.md` |
| `TBD-RELEASE-ARCHIVE-PINS` | `docs/ARTIFACTS.md` |
| `TBD-RELEASE-TAG` | `README.md`, `VERIFICATION.md`, `docs/ARTIFACTS.md` |

The separate author TODOs remain untouched: identities, ORCIDs, license/SPDX and LICENSE text, immutable public URLs, and underlying development provenance. No code blocker or unimplemented H1 stage remains. The final-result fields await the explicitly separate build records.

## ORCH-SUMMARY

- Delivered commit 96e4880c7dbb4cf76e92ba82ab5ee1e2f375ecd5 on 42b16c3; clone clean.
- No Lean, Lake pin, toolchain, Comparator, generated inventory, or interface edit.
- Required source digest remains c875dff024d396b0b78f1fa955ea5d38e8f577e1d8bd69e970fd02bea906bee9.
- H1 has one input setting and portable report defaults; H3 defaults are portable.
- Default cold verifier has all five numeric H1 steps; no external adapter is required.
- Optional H1 RAM control preserves the existing 270 GB default and receipt format.
- Both receipt verifiers and all key/hash/emitter/bundling functions are unchanged.
- AST and synthetic probes establish unchanged keys, receipts, templates, and maps.
- Nine unused historical helpers removed; no release import or command references them.
- Eleven stale comment-source entries refreshed; active manifests and exact Challenge pass.
- All 23 numeric pins and 32 documentation links pass; only author metadata/LICENSE findings remain.
- H1 release notes include reference metrics, all 25 kinds, performance comparison, and closed contracts.
- All 24 remaining final-result fields and unchanged author TODOs are listed.
- No compiler, certificate command, independent kernel, or write to final/production reports occurred.
