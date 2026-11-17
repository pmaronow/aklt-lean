STATUS: FIDELITY FIXES COMPLETE

Author direction supersedes the earlier conditional/resource-fit target. The current result is the hand-written port for the complete unconditional formalization; earlier phases below are historical. See the final complete-release section.

Current deliverable: the two-input standalone release is materialized and ported; all three checker engines and protected statement comparison accept. The earlier four-premise feasibility study below is historical. See the final [release package](#release-package) section for current scope, package commit, measurements and remaining author/infrastructure work.

## Historical feasibility study

PAL_FIT establishes a sound four-premise conditional theorem and identifies concrete packaging and resource blockers. **The present source tree is not an admissible Palomar submission at either profile.** Direct Lean and NanoDa accept the conditional theorem's complete 889.806 MB export; a fresh legacy source build and con-ron do not complete under the conservative local memory envelope. The larger profile does not parallelize the mandatory Lean replay or extend the 30-minute con-ron cap.

This is a design/feasibility delivery, not an unconditional AKLT proof or a production acceptance receipt. Worktree pin: `889daa73a71fdb1ed868ed6a96a1290ae4e5db03`. Official verifier pin: `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. Lean/leanexport/leanchecker/NanoDa: 4.35.0-rc2; Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Con-ron is the official checker override, 4.36.0-rc1, SHA-256 `4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`.

The four requested verifier documents and checker revision pin were read and snapshotted in [inputs.json](inputs.json). The earlier author's verify scripts, comparator configuration and verification README were read for conventions; they do not override today's official rules. All nine dependency checkout HEADs match the pinned manifest: [dependency-pins.json](dependency-pins.json). No `lake update`, Mathlib build, package-directory write, producer edit, main edit or sub-agent was used. The final [disk receipt](disk-receipt.json) records more than 366 GiB free and about 2.03 GiB allocated to this report/study directory, satisfying the 20-GB free-workspace check locally. `git status --short` shows only the new `AKLT/PALFit/` directory.

**1. Conditional package and core measurements**

Delivered worktree sources are [Statement.lean](/home/ubuntu/aklt/wt/PAL_FIT/AKLT/PALFit/Statement.lean), [Solution.lean](/home/ubuntu/aklt/wt/PAL_FIT/AKLT/PALFit/Solution.lean), [Audit.lean](/home/ubuntu/aklt/wt/PAL_FIT/AKLT/PALFit/Audit.lean), [Challenge.lean](/home/ubuntu/aklt/wt/PAL_FIT/AKLT/PALFit/Challenge.lean) and [comparator.json](/home/ubuntu/aklt/wt/PAL_FIT/AKLT/PALFit/comparator.json). The source-only candidate is [package/](package/), with a pinned Lake manifest, minimal TOML library and source hashes in [package-sources.json](package-sources.json). It has **852 Lean sources / 8,833,186 bytes**: the 850-module Solution closure plus Challenge and Audit. Generated H1/H3 numeric certificates are excluded.

The exported theorem has exactly this explicit type, taken from `AKLT.Final.mainV2_of_open`:

```lean
AKLT.PALFit.conditionalMain
  (hH1M068 : AKLT.Blueprint.Top.H1FiniteDataStatementV2)
  (hCertificate : AKLT.Blueprint.Top.CertificateStatement)
  (hAutomaton10 : AKLT.Blueprint.Top.Automaton10StatementV2)
  (hStationaryCheck : AKLT.Blueprint.Top.StationaryCheckStatementV2)
  : AKLT.Challenge.MainStatementV2
```

`AKLT.PALFit.ConditionalMainStatement : Prop` is the corresponding four-arrow proposition. `Solution.lean` supplies all **416** non-certificate arguments to the closing theorem from the canonical leaf proofs on this main snapshot. **No additional unproved main leaf is a premise.** The generated closing-contract inventory has 420 arguments, 416 leaves plus these four certificates; exact statement/term mappings and source hashes are in [hypotheses.json](hypotheses.json).

The strict Audit imports the constructed theorem and prints the axiom sets of the headline, the closing theorem and all 416 supplied leaves, 418 prints in total. Their union is precisely the allowed three. Actual output:

```text
'AKLT.PALFit.conditionalMain' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Final.mainV2_of_open' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is [strict-audit/stdout.log](measurements/strict-audit/stdout.log). These four premises are part of the theorem's claim; this report does not present it as `MainStatementV2` without premises. New Lean sources contain no proof holes or additional axioms. The existing named H2 certificate's unlimited-heartbeat option is the explicit campaign exception; the isolated H2 probe instead uses a finite heartbeat budget.

The Challenge file currently imports the exact proposition and has **no theorem target**. A standard Palomar Challenge theorem placeholder would conflict with the campaign's ban on proof holes. No exception was received, so no such placeholder was inserted. More substantively, its candidate-local imports are not permitted in the protected Challenge. Thus the configuration parses, but **there is no independent, admissible Challenge comparison**. This is a concrete unfinished part of item 1, not a claimed Comparator pass.

Resource enforcement was checked before timing. `systemd-run --user --scope` fails with `Failed to connect to bus: No data available`; `/sys/fs/cgroup` is read-only, and the inherited cgroup has `cpu.max = max 100000`, `memory.max = max`, `memory.swap.max = max`. The session cannot create an authentic 16×32 cgroup. The limit probe confirms the actual hard 31-GiB address-space limit and demonstrates that a 32-GiB allocation is refused with `ENOMEM`; this verifies the fallback limit, not a cgroup RAM limit. Basic bubblewrap user/PID namespaces **do work**; namespace unavailability is not the blocker.

All timed diagnostic children inherit CPU affinity **0–15**, checked repeatedly through `/proc`. Single tools have a hard **31 GiB virtual-address limit**, with a 512 MiB supervisor; the source build used two hard 15 GiB workers, then one hard 31 GiB worker. Queued orchestration processes have small address-space limits, and a global file lock serializes heavyweight stages; simultaneous controlled reservations stayed below 32 GiB, with at most two Lean compiler processes. `wait4`, monotonic clocks and sampled `/proc` RSS/VMS/thread counts are retained per stage. Core dumps were disabled; later runs also disable dumpability to avoid the host crash handler. See [limited.py](tools/limited.py), [build_core.py](tools/build_core.py), [limit-probe](measurements/limit-probe/result.json) and [scope-attempt.log](scope-attempt.log).

This is a **conservative address-space/affinity diagnostic**, not an equal resident-memory/page-cache cgroup or an enforced swap ban. Allocation failures can happen below Palomar's resident-memory ceiling. They do not constitute authenticated OOM/timeout evidence for the larger profile. The JSON field `accepted_envelope` only records this harness's affinity/descendant checks. The supplied [default_scope.sh](tools/default_scope.sh) is a non-fallback launcher for a host shell with systemd delegation; it verifies 1600% quota, exactly 32 GiB `memory.max` and zero swap before executing anything. An actual production-equivalent timing run remains open.

The **broader source-build survey** in [candidate/](candidate/) deliberately includes all 1,104 original AKLT files, both root aggregators, 19 handwritten CertData support files and four new files: **1,129 Lean sources**, without generated finite attachments. Project output objects started empty. Dependencies came from the existing pinned, read-only dependency cache through an explicit `LEAN_PATH`; no dependency source was rebuilt. The official source-check implementation and pinned checker/export binaries were used. A cold cache fetch and the official sandboxed Lake invocation were not reproduced.

| Stage | Wall s | CPU s | Peak RSS GiB | Result |
|---|---:|---:|---:|---|
| Actual default-profile cgroup/setup | — | — | — | Blocked: systemd delegation unavailable |
| Official source eligibility scanner | 0.51 | 0.50 | 0.036 | Scanner completed; 1,104 missing module headers |
| H1 final source-archive audit | 2.17 | 2.16 | 0.055 | 7,964 archives hash-match; 7,964 missing headers |
| Fresh broad source build, two workers | 4,418.71 | 8,715.31 | 15.514 aggregate | 1,062 pass; 6 fail; 61 blocked |
| Continue fresh build, one worker | 733.81 | 595.22 | 25.426 aggregate | Cumulative 1,119 pass; H2.Check fails; 9 blocked |
| Protected Challenge compile | 0.21 | 0.17 | 0.188 | Fails: candidate-local AKLT import |
| Strict headline + 416-leaf Audit | 5.76 | 5.75 | 6.734 | Pass, after disclosed warm H2 reuse |
| Worktree conditional Solution | 5.11 | 5.07 | 6.734 | Pass, disclosed warm dependencies |
| Stock full Solution export | 79.49 | 79.44 | 7.434 | Pass, 889,805,659 bytes |
| Full Solution Lean replay | 471.37 | 471.34 | 23.252 | Accept |
| Full Solution NanoDa, four threads | 519.24 | 695.45 | 19.171 | Accept |
| Full Solution con-ron, two workers | 255.54 | 459.11 | 27.705 | Allocation failure; censored AS cap |

Times are seconds; memory is GiB. Source-build CPU is the sum of compiler children, and build RSS is the sampled sum of worker RSS; it is not cgroup resident/page-cache accounting. Direct tool RSS is the larger of sampled high-water RSS and `wait4` maxRSS. Supervisor/controller CPU is excluded. Receipts and complete command lines are in [measurements/](measurements/), [clean-build/](clean-build/) and [clean-resume/](clean-resume/). The report recorded each result immediately as it became available. The append-only [measurements/ledger.jsonl](measurements/ledger.jsonl) retains those records; [chronological-report.md](measurements/chronological-report.md) is a later receipt index, not an original report backup.

The initial two-worker survey passed 1,062 modules, had six resource failures and blocked 61 dependents. The single-worker continuation brought the total to **1,119 passed, one failed, nine blocked**. Five failures of thread creation near the smaller virtual limit passed on retry; there was no mathematical source error. `AKLT.Cert.H2.Check` alone still failed. The combined diagnostic elapsed source-build cost is **5,152.52 s / 9,310.53 CPU s**; it includes failures/retries and omits the blocked finishing build, so it is not a successful clean-build duration.

To exercise the closing theorem and independent kernels anyway, a separate [warm-overlay/](warm-overlay/) reuses exactly one pre-existing project object, `AKLT.Cert.H2.Check.olean`, with matching source/artifact hashes in [warm-reuse.json](warm-reuse.json); its remaining dependent modules were freshly compiled. **Warm construction is not clean-build evidence.** The resulting full export is replayed from scratch, without project oleans, by Lean and NanoDa. Its SHA-256 is `4a4854afea0980059928b3abc4a80a227a8a4726bbd866c219ddc583a50b1e51`; all three export hashes/root lists are in [exports.json](exports.json) and [export-targets.json](export-targets.json). NanoDa checks 82,596 declarations with no typechecker errors; its one “Unable to print axioms” pretty-printer warning accompanies exit zero.

The Comparator plumbing control uses this same export on both sides, so it cannot establish statement independence. At a conservative inherited 7.5 GiB limit per process, its NanoDa and Lean child kernels exhaust their limits; the control exits nonzero. Its recorded 486.67 s wall / 99.38 CPU s and 1.963 GiB maxRSS are **not valid full-tree Comparator resource totals**: the initial sampler missed children spawned by an IO worker thread. The harness was subsequently fixed to inspect every thread's children. The control is excluded from the budget baseline; it is neither a proof rejection nor a Comparator pass.

The actual official sequence stops before the downstream stages on source/metadata/Challenge failures. The downstream measurements above are direct component diagnostics, not an official end-to-end verdict. In particular, no cold Mathlib download, protected Challenge export or successful independent structural comparison is claimed. The official source at `verify_submission.py:6428` builds the selected Solution closure, rather than every unused library glob; the broader all-source survey here fulfills the brief's stronger whole-tree check. Source eligibility still covers every submitted Lean file.

The two requested hazards were isolated with their full dependency closures and the official primitive roots:

| Stage | Wall s | CPU s | Peak RSS GiB | Result |
|---|---:|---:|---:|---|
| H2 original source module | 258.87 | 157.71 | 25.426 | Censored AS limit |
| H2 Lean replay | 182.78 | 182.74 | 22.684 | Accept |
| H2 NanoDa | 247.72 | 247.87 | 18.208 | Accept |
| H2 con-ron | 146.00 | 146.32 | 28.671 | Allocation failure; censored |
| deadMask source module | 5.42 | 5.39 | 6.523 | Accept |
| deadMask Lean replay | 2.48 | 2.48 | 0.146 | Accept |
| deadMask NanoDa | 284.61 | 285.27 | 22.381 | Allocation failure; censored |
| deadMask con-ron | 691.65 | 692.77 | 26.480 | Allocation failure; censored |

The H2 original full module hits 31 GiB VMS; the isolated first theorem with asynchronous elaboration disabled also fails at 148.43 s / 148.31 CPU s / 25.42 GiB RSS. That is stronger evidence than the invalid `h2-serial-module` launch, which used an incorrect module root and is excluded. A pure module-system pilot of H2 is reported below. The dead-mask source module builds quickly in Lean, yet both independent checkers exhaust the diagnostic cap. These are conversion/normalization hazards, not large input-file hazards. Their resource failures are censored observations, not upper bounds.

**The conditional Solution closure excludes `AKLT.W.H3C026.DeadMask`**: [source-closures.json](source-closures.json). The minimal 852-file package can omit it; the all-tree source survey included it. H2 is actually required by the conditional theorem. Do not infer that an 11 MB or 25 MB hazard export is safe from the byte size. Meaning-preserving proof changes, such as symbolic conversion lemmas and bounded intermediate checks instead of a single large reduction, need separate validation; none was smuggled into this package.

**All source and packaging findings**

The official source scanner reports the following, with full path/line diagnostics in [source-checks-final.json](source-checks-final.json), [package-source-checks.json](package-source-checks.json), [attachment-source-checks.json](attachment-source-checks.json) and [h1-archive-source-checks.json](h1-archive-source-checks.json):

| Surface | Files inspected | Missing module headers | Physical line result |
|---|---:|---:|---|
| Original AKLT tree | 1,104 | 1,079; 25 already ported | Maximum 1,631; none above 10,000 |
| Whole diagnostic candidate | 1,129 | 1,104 | None above 10,000 |
| Minimal conditional package | 852 | 852 | None above 10,000 |
| H3 phase-3 attachment, still-present manifest sources | 2,695 of 5,035 | 2,695 | Maximum 1,052; no violation among present files |
| H1 final production owner archives, decompressed read-only and hash-verified | 7,964 | 7,964 | Maximum 1,685; none above 10,000 |

The H3 producer deliberately compacted 2,340 source literals after checking them. Their archived hashes/inputs are preserved, but the missing text cannot be source-scanned or freshly built until regenerated. The initial H1 phase-2-path scan found 4,864 present / 3,100 missing; the final **phase-3 archive audit supersedes that incomplete scan**, reading all 317,687,703 owner-source bytes from the 7,964 `.lean.gz` files and checking each receipt hash. It changes no producer file. Compressed archives are not source files that Lake can clean-build without restoring them.

No invalid UTF-8, forbidden source symlink or 10,000-line violation was reported among the inspected candidate sources. The Challenge stub itself fits 1,000 lines / 100 KiB; its semantics/import policy/target are the problem. Additional blockers are:

- Missing root `formalization.yaml` and `LICENSE`; author/classification/license metadata has not been invented. Existing vendor license notices are preserved for the retained source directories. [source_check.py](tools/source_check.py) checks their presence in addition to the official Lean scanner; it does not pretend to validate absent metadata.
- The protected Challenge is compiled using trusted dependency paths, with no candidate AKLT import available. Its actual compilation fails with `unknown module prefix AKLT`: [canonical-challenge-compile](measurements/canonical-challenge-compile/). A candidate-supplied statement import cannot replace independent Challenge source.
- The **exact** Automaton10 and StationaryCheck premises name `Automaton10Data.supplied`. Its fixed raw-class source is 3,282,597 bytes / 1,631 lines. Verbatim inlining alone violates both Challenge caps. An independently reviewed compact algorithmic encoding with equivalence proofs, or a revised generic/existential interface with proved bridges, is needed. This is not an impossibility proof for every compressed encoding. The unconditional mathematical headline itself is small; this extra table obstacle arises from the exact four-premise conditional surface.
- Comparator recursively compares the referenced helper declarations, not only their names or definitional equivalence. Private helpers and the fixed table must agree across the independent surfaces. `definition_names` is not a license to erase the table semantics. A revised interface must be declared and reviewed, not silently substituted for these four contracts.
- The official checked-out repository has a **500 MiB cap** (`MAX_SOURCE_BYTES` in the verifier), in addition to per-file caps. H3's old plane literals alone imply about 29.75 GB of hex characters; its compressed input payload is already about 2.60 GB. Keeping either inside the submitted root exceeds the cap. The complete H1 owner source is about 318 MB and can fit alone with this core, but retaining all unbundled raw templates adds about 335 MB and exceeds the cap. Exclude unused histories/prototypes, not just their imports. Public, full-SHA-pinned Git dependency data can alter where the root cap applies, subject to the official dependency rules; it cannot remove build, replay, memory or export costs. Neither profile relaxes these source rules.

The scan does not certify nonexistent/regenerated sources, and no metadata, license or statement-identity approval is implied by a successful source-header scan.

**2. Module-system port**

[port-inventory.json](port-inventory.json) sizes the original tree: **166,352 physical lines / 10,854,154 bytes**, 1,079 legacy files to convert, **4,195 explicit private declarations in 389 files**, and 894 files with a noncomputable section. Generated attachments add a separate **12,999** producer modules; they are not included in the 1,104-file estimate and must be emitted correctly by their generators.

The mechanical procedure in [port_modules.py](tools/port_modules.py) writes a separate overlay, never the source tree. It prepends `module`, makes old re-exporting imports `public import`, and puts ordinary declarations in `@[expose] public section`. Explicit `private` modifiers and all proof bodies remain intact. It uses `backward.privateInPublic true` and `backward.proofsInPublic true` as migration options, without suppressing their warnings or bypassing kernel checking. This is a conservative compatibility start, not the desired final public API. The script assumes this tree's regular import layout; it is not a general Lean syntax refactoring engine.

A dependency-order procedure is necessary: new modules cannot import non-module files (`Lean/Environment.lean` rejects this); prepending headers to an arbitrary upper directory fails. Convert the selected part **and its legacy prerequisites**, compile bottom-up, repair the public/exposed/private boundary, then rebuild consumers and export/replay them. `VisibilityStrict.lean` is a negative fixture: a public exposed definition referring to a private helper fails. The compatibility fixture builds and its theorem prints no axioms. Where compatibility is undesirable, promote the helper deliberately or hide the implementation behind an appropriate public theorem. Check elaborator/meta imports, instances, attributes and notation as part of each boundary repair.

The first pilot converts the complete `AKLT/Challenge` directory (Main, MainV2, Sanity), whose external imports are already modules. All three build, followed by a strict axiom audit. Main's import RSS drops from **6.486 GiB legacy to 3.630 GiB module-system** on this machine; this is a controlled import-memory observation, not a claim that all files or kernel reductions improve by that ratio. Ported Main takes 5.05 s versus 3.33 s legacy, so no general CPU speedup is inferred.

The stronger successful pilots port the complete **AKLT/Defs (23 files, 24-module prerequisite closure)** and **AKLT/Gen/Gram (five files, five-module closure)** directories. Defs exercises private fixed-table helpers; Gram exercises the checker/soundness library. All compile without a proof-body repair. The Gram strict audit prints every public theorem, with statements in its existing CoreAudit output; axiom sets remain within the permitted three. Exact source manifests and results are [pilot-AKLT-Defs-result.json](pilot-AKLT-Defs-result.json) and [pilot-AKLT-Gen-Gram-result.json](pilot-AKLT-Gen-Gram-result.json).

| Stage | Wall s | CPU s | Peak RSS GiB | Result |
|---|---:|---:|---:|---|
| Challenge.Main | 5.05 | 5.04 | 3.630 | Pass |
| Challenge.MainV2 | 4.19 | 4.19 | 3.620 | Pass |
| Challenge.Sanity | 7.17 | 7.15 | 3.646 | Pass |
| Challenge strict axiom audit | 3.64 | 3.61 | 3.589 | Pass |
| Complete AKLT/Defs part: 23 files / 24 closure | 36.76 newly compiled | 36.67 | 3.710 max | Pass; 18 prerequisites reused from successful pilot |
| AKLT/Defs strict public-theorem audit | 3.59 | 3.56 | 3.586 | Pass; 0 theorem prints |
| Complete AKLT/Gen/Gram part: 5 files / 5 closure | 14.47 newly compiled | 14.34 | 1.910 max | Pass; 0 prerequisites reused from successful pilot |
| AKLT/Gen/Gram strict public-theorem audit | 2.13 | 2.09 | 1.857 | Pass; 23 theorem prints |
| H2.Check after module port | 101.77 | 101.69 | 23.929 | Allocation failure; not a successful H2 part port |
| H2 successful public-theorem audit | 3.74 | 3.71 | 3.586 | Pass; successful H2 submodules only |

The H2 attempt selected 34 modules: 29 pass (including reused Challenge.Main), one numerical module fails, and four dependents are blocked. Ported H2.Check is censored at 101.77 s / 101.69 CPU s / 23.929 GiB RSS and 31 GiB VMS. Its lower import memory is insufficient to finish the reduction. The 65 public theorems in successful H2 part modules pass their separate strict axiom audit. The open modules are exactly `AKLT.Cert.H2.Check`, `AKLT.Cert.H2.Finite`, `AKLT.Cert.H2.Main`, `AKLT.Cert.H2.All`, `AKLT.Cert.H2.Audit`; details in [pilot-h2-result.json](pilot-h2-result.json). In total 47 original sources were transformed across these overlapping pilots, under 5% of the tree. The compatibility fixture exports `AKLT.PALFit.VisibilityCompat.checked : AKLT.PALFit.VisibilityCompat.visible = 7`, whose axiom list is empty; the strict visibility fixture intentionally fails.

The script preserves source bodies; the pilots do not port the whole tree. For a compatibility-first conversion of the existing 1,104-file tree, allow **1–3 experienced Lean engineer working days** if these body-preserving pilots generalize; for a reviewed public API and independently checked release, estimate **5–10 working days**: a fraction of a day for inventory/overlay automation, 2–5 days for privacy/exposure and downstream repairs, 1–2 days for source/axiom/statement audits, and 1–2 days for a real clean build and checker regressions. The generator changes and representative attachment pilots add roughly **1–3 days**, plus numerical regeneration/rechecks; they are not included in that source-only estimate. The 389 private-heavy files and untested meta/notation boundaries make this an engineering estimate, not a measured failure count. The original numerical certificates total about 158.5 successful Lean CPU-hours at the latest receipts, before independent replays; rechecking them is substantial computer work even if the header port is mechanical.

Example reproducible overlay commands (the actual measurements ran their Lean commands inside `limited.py`; use `default_scope.sh` on a delegated host):

```sh
export PATH="$HOME/.elan/bin:$PATH"
python3 /home/ubuntu/aklt/reports/PAL_FIT/tools/port_modules.py \
  --input /home/ubuntu/aklt/wt/PAL_FIT \
  --output /home/ubuntu/aklt/reports/PAL_FIT/pilot --part AKLT/Challenge
python3 /home/ubuntu/aklt/reports/PAL_FIT/tools/pilot_h2.py
```

The pilot uses direct `lean -j1 -DElab.async=false -DautoImplicit=false -DrelaxedAutoImplicit=false FILE -o OBJECT` in dependency order, with the pilot library first in `LEAN_PATH` and only pinned external libraries after it. The initial broad build uses [build_core.py](tools/build_core.py); exports/replays use [after_core.py](tools/after_core.py). No `lake build -j` is used. The source-only candidate's official future build target is `lake build AKLT.PALFit.Solution`; project scheduling/RAM under that exact Lake invocation still needs validation. The model's chosen compiler worker counts are assumptions, not a demonstrated Lake concurrency flag.

**3. Budget model: what fits, and what cannot be inferred**

The inputs changed during the study. Both the original read snapshots and final snapshots/hashes are preserved in [inputs.json](inputs.json) and [inputs-final.json](inputs-final.json). At the final snapshot H1 has completed production: **139.002 CPU-hours portfolio**, 135.524 CPU-hours of successful phase-3 compilation events, with 109.236 h constructors, 7.439 h Gram, 11.614 h local checks, and 11.153 GiB observed maximum. These supersede the brief's 115-hour forecast and unmeasured 64-GiB caps. H3's accepted phase-3 run is **19.455 CPU-hours**, not isolated pure kernel time: plane loading 10.887 h, endpoints 2.043 h, rows 2.227 h, prefixes 3.516 h, and the remainder 0.782 h. [h3-cost-breakdown.json](h3-cost-breakdown.json) and [final-H1-measurements.json](inputs/final-H1-measurements.json) preserve the numbers used.

The REL_FEAS sample timings were used, not rerun. At the initial snapshot fresh Lean-replay/Comparator scheduling evidence was absent, so this study added only the missing Lean-reader/replay probes on existing immutable sample exports; the concurrently updated REL_FEAS report now also contains its own later Lean-replay results. No REL_FEAS source build, NanoDa or con-ron timing was repeated. Current REL_FEAS establishes a complete H1 constructor owner at **166.49 source CPU s → 132.64 Lean replay CPU s** (q≈0.80), NanoDa/source CPU factor 0.80 and con-ron/source CPU factor 1.93. Its measured Gram and packed rows plus explicit unmeasured allowances are the source of the planning bands below, not a guarantee for all constructors.

**Parallelism is decisive.** Pinned `Lake/CLI/Check.lean:464` calls the external kernels in a serial loop and Lean last; the actual control prints NanoDa before Lean. `LeanChecker.lean:72` calls `Kernel.Environment.replay`, and `Lean/Replay.lean:176` loops declarations sequentially. Our full Lean replay uses **471.34 CPU s / 471.37 wall s**, confirming one effective CPU despite runtime helper threads. NanoDa is configured by Comparator to four check threads; its full-core measurement uses **695.45 CPU s / 519.24 wall s = 1.34 effective CPUs**, with a long tail. Parsing/install and an individual hard declaration are not automatically four-way. Official con-ron uses two workers, serial parsing/install and a global 1,800-second cap. Giving the host 32 CPUs does not change these checker settings. Never divide all three replays by 16 or 32, and do not run Lean and NanoDa concurrently in the model.

The new stock Lean-reader measurements are [lean-replay-ratios.json](lean-replay-ratios.json):

| Existing immutable sample | Source CPU s from REL_FEAS | New Lean replay wall / CPU s | Result |
|---|---:|---:|---|
| H1 Gram small | 34.28 | 31.09 / 31.09 | Accept, 1.238 GiB |
| H1 packed 711 | 12.94 | 7.59 / 7.55 | Accept, 0.733 GiB |
| H3 prefix large | 92.87 | 900.07 / 899.98 | Timeout, 0.132 GiB |
| H3 raw large | 38.94 | 900.10 / 899.98 | Timeout, 0.126 GiB |

Those H3 timeouts are dominated by a huge literal reader, not a measured numerical replay ratio. `LeanExport/Parse.lean:228` uses `String.toNat?`; `Init/Data/String/Slice.lean:1014` implements decimal parsing by successive `n*10+digit`. The raw sample contains an unused **3,787,833-decimal-digit / 12,582,912-bit** `denseClass` Nat. It dominates the sum of squared literal widths: [reader-literal-profile.json](reader-literal-profile.json).

A controlled parser probe retains **identical declaration records**, with or without that one extra unused expression record. The 5.383 MB prefix accepts in **0.508 s / 0.487 CPU s / 0.106 GiB**; adding the 3.788 MB literal causes a **180.07 s timeout / 180.00 CPU s / 0.126 GiB**, before any acceptance. [reader-probe/metadata.json](reader-probe/metadata.json) describes the construction. This is a parser control, not a submitted proof export. It establishes why **no universal “GB that fit” bound can be deduced from byte count alone**: a 9 MB file can be worse than the accepted 890 MB core. REL_FEAS separately measures the stock formatter's digit-by-digit bottleneck. Both the encoder and the reader matter.

A valid accounting model has separate terms, with hours converted to seconds:

```text
T = setup + measured/repaired core + structural comparison
    + 3600 * Bcert / p_build
    + 3600 * sum(qLean_i * K_i)                   # serial Lean replay
    + 3600 * sum(rNano_i * K_i) / pNano_effective # at most 4
    + literal export/read/install cost(E, widths, term shape)
    + conron attempt
T <= 19,800 seconds
Ccore + Ccert + conron parse/install <= 1,800 seconds  # for complete third-checker acceptance
M_shared_environment + sum(worker workspaces) + overhead < host ceiling
```

`B` is source-build process CPU, `K` a numerical CPU proxy; they are not interchangeable. Use `K_H1=128.289 h` for constructor+Gram+local CPU, and `K_H3=6.276 h` for the listed numeric/check stages, with source totals 139.002/19.455 h. H3's proxy still contains import overhead; it is not a pure-kernel timer. Do not multiply H3's entire 19.455 h by a numerical-check factor and also separately charge the same literal loading. Conversely, do not remove genuine H1 constructor arithmetic by subtracting an import floor per theorem: owners already batch many theorems.

[budget_model.py](tools/budget_model.py) generates [budget-model.json](budget-model.json). Its **illustrative**, deliberately explicit baseline reserves 600 s for setup/cache (unmeasured), 60 s for a future valid Challenge/comparison (unmeasured), the observed 5,152.52 s diagnostic source-build cost, and measured core Audit/export/Lean/NanoDa. Reserving the full 1,800 s advisory con-ron attempt leaves **11,111.62 s = 3.087 h** for certificate build and mandatory replays. The unfinished clean build can increase this cost; excluding unused sources or a module port can reduce it. Holding this same core cost fixed across profiles avoids claiming an unmeasured larger-host speedup.

| Budget item | Default 16×32 | Larger 32×64 |
|---|---:|---:|
| Host CPU / RAM | 16 / 32 GiB | 32 / 64 GiB |
| Host pressure / ceiling | 30.40 / 31.36 GiB | 60.80 / 62.72 GiB |
| Solo checker envelope after 1 GiB overhead | 30.36 GiB | 61.72 GiB |
| Redesigned build concurrency / ceiling envelope per process | 4 / 7.590 GiB | 8 / 7.715 GiB |
| Pressure-aware envelope per build process, same 1 GiB overhead | 7.350 GiB | 7.475 GiB |
| Residual ideal total CPU-hours, all work perfectly parallel | 49.38 | 98.77 |
| Reference new numerical K-hours, mandatory kernels, no literal cost | 2.058 | 2.245 |
| Lean / NanoDa / con-ron check parallelism | 1 / ≤4 / ≤2 | 1 / ≤4 / ≤2 |
| All-three K-hours with rConron=2, 600-s repaired core con-ron | ≤0.333 | ≤0.333 |
| Byte-only export allowance | Not identifiable | Not identifiable |
| Conservative new-export design target, not an admission guarantee | 0.30 GB; total ≈1.19 GB | Same |

These RAM calculations use nominal 32/64 GiB hosts; the verifier reads actual host memory and applies its percentages there (the profile minima are 28/60 GiB). The ceiling envelopes are upper shares, not pressure-free working targets: four/eight workers should aim below **7.350/7.475 GiB each** after the same 1-GiB overhead. H1's ordinary 7.540-GiB peak needs about **1.026×/1.009×** reduction for those uniform pressure-aware slots, or fewer concurrent processes. The execution budget is 19,800 s inside the 350-minute job timeout. The first CPU row is an unattainable-in-general aggregate upper intercept, not available serial kernel work. The reference K row assumes B=K, qLean=1 and NanoDa CPU ratio 1 with perfect four-way checks, before any new literal costs. For **all three accepting**, additionally assume a repaired core con-ron cost of 600 s, leaving 1,200 s of its cap, and rConron=2; the K intercept is only **0.333 CPU-hours at either profile**. The measured con-ron core is censored, so 600 s is a scenario, not a completion measurement. An authenticated capacity decline can permit an inconclusive con-ron outcome; it does not make con-ron accept, and its 30-minute attempt still spends the execution budget.

Separating the lane proxies gives the following required **uniform reductions of current source-build and numerical costs**, one lane at a time, excluding the unresolved giant-literal I/O. H1 uses qLean=.80 and stage-weighted NanoDa factors .735–1.548, con-ron 1.885–2.941. H3 uses an explicitly unmeasured numerical-only qLean=1 after fixing literal representation, NanoDa .5–2 and con-ron 2–8; censored rows mean there is no validated finite upper factor.

| Separate-lane reduction scenario | Default | Larger |
|---|---:|---:|
| H1 mandatory build + Lean + NanoDa | 55.9–64.3× | 47.3–55.8× |
| H1 complete con-ron within unchanged cap too | 362.7–565.9× | 362.7–565.9× |
| H3 mandatory build + Lean + NanoDa | 4.4–5.2× | 3.2–4.0× |
| H3 complete con-ron within unchanged cap too | 18.8–75.3× | 18.8–75.3× |

These are **optimistic scheduling scenarios, not exact necessary/sufficient factors**: legacy normal processes are budgeted at approximately 8 GiB, giving three/seven concurrent source workers; target redesigned builds use four/eight smaller workers. The local campaign itself never ran more than two. The lane intercepts cannot both be spent in full, nor can the time and byte intercepts both be spent in full. If NanoDa's certificate work has only one effective check CPU, H1's mandatory reduction rises to **79–113× default / 70–104× larger**. Independently of source scheduling, H1's q=.80 replay alone is about **102.63 serial CPU-hours**, at least 18.7× the entire 5.5-hour budget before setup, core, NanoDa or con-ron. The 115-hour historical forecast has the same qualitative obstruction; the completed production makes it stronger.

Memory reductions must be stated against real measurements, rather than reservation labels:

| Lane/process | Observed / declared | Default requirement | Larger-profile requirement |
|---|---|---|---|
| H1 ordinary constructor | 7.540 GiB observed | Fits a 7.590-GiB target slot narrowly; whole environment/scheduling still matters | Fits 7.715-GiB target slot |
| H1 largest aggregation | 11.153 GiB observed | Fits alone; 1.47× smaller to fit every uniform four-worker slot, or serialize | Fits alone; 1.45× smaller for every eight-worker slot, or serialize |
| H1 historic 64-GiB cap | Reservation, not observed demand | If actually used: 2.11× smaller for the solo 30.36-GiB envelope | If actually used: 1.04× for solo 61.72 GiB; latest measured aggregation uses much less |
| H3 largest original aggregation | 18.721 GiB observed | Fits alone; 2.47× smaller for uniform four-worker slots | Fits alone; 2.43× smaller for uniform eight-worker slots |
| Original independent row/prefix checks | Some runs censored; full environment unmeasured | No established finite full-export memory factor; core/H2/dead-mask already have censored independent-checker runs | 64 GiB could help a workspace, but no full-export bound or proof of fit follows |

There is no demonstrated intrinsic per-process 64-GiB requirement for either completed producer build. Both have measured largest Lean processes below 32 GiB. Their concurrency, full-export installed environment and independent-checker workspaces are the issue. Memory shared within one checker process differs from separately imported compiler processes; the inequalities above must be measured on the combined export. RSS sums may double-count shared mappings, but source builds also need headroom for runtime stacks and page cache.

For export volume, **stock unbounded literals have no identified admissible GB allowance**, at either profile. A useful bounded-representation sensitivity is available: the H3 phase-4 full-row **stock 8,192-bit-leaf** pilot takes export/Lean/NanoDa/con-ron 16.49/6.54/26.16/16.99 s for 16.587 MB. Scaling that entire term/work mixture, with no other certificate cost and the model's remaining core allowances, gives **3.747 GB mandatory / 1.172 GB all-three** intercepts. This includes sample computation; it is not a measured parser-only slope. The newer structured-potential pilot's mixture instead gives about **0.569 GB** for the same con-ron allowance. These different values are precisely why they are sensitivity calculations, not production byte limits; full installed-environment memory may bind earlier.

Thus H3's original **35.8 GB plane decimal digits alone** would need about **31–63×** volume reduction against those all-three sensitivities; even its compact uint32 route's **14.33 GB** needs **12–25×**. Endpoints, term metadata and H1 are additional. An engineering go/no-go target of **≤0.30 GB total new certificate export**, bounded small literals, and **≤0.20 CPU-hours total new numerical work** leaves some joint time margin under the phase-4 mixture; measured core+certificate export would be about **1.19 GB**. This is a deliberately conservative research target, not a proof that 0.30 GB always fits. It implies **≥119×** reduction of old H3 plane digits, or **≥47.8×** beyond the compact uint32 digit payload. H1's complete export size has not been measured: 10.964 GB of matrix/factor **oleans is not its export size**. Its exact volume reduction is therefore **unknown**, `E_H1 / allocated_GB`; quoting an exact numerical H1 export factor would invent a missing measurement.

Without a successful authentic core run, a complete H1/H3 export, bounded literal shapes and installed-memory measurements, the requested exact sufficient total CPU/GB/memory allowance is not identifiable. The tables give reproducible conditional allowances and necessary architectural changes rather than fabricating that missing certainty.

**4. Ranked options and concrete decisions**

**(a) First for a near-term independently checked result: register the explicit conditional theorem, with external finite-certificate receipts.** This establishes exactly the four-premise implication above; it gives Palomar neither the four premises nor the unconditional headline. Its core full export already passes the two mandatory direct kernels in this study. Finish the module port of the selected source closure, H2 source/replay resource work, a permitted independently frozen Challenge surface and author metadata/license, then run the actual default-profile cold pipeline. The campaign's Challenge-placeholder constraint needs an explicit author/Palomar-compatible resolution; no permission is inferred here.

External receipts should bind one source/toolchain/Mathlib pin, exact theorem types and values, primitive roots, standard axiom audits, the complete dependency closures, and hashes of every overlapping declaration. Shard names, file hashes or final olean names alone do not prove a coherent combined environment. Check the final assembly and the bridge to these **exact four** contracts; use definitionally correct projections from H1's `CertificateStatementV2 = CertificateStatement ∧ H1FiniteDataStatementV2`. H1 production is now numerically complete but retains **33 mathematical closed Props** ([H1 leaves-open.json](/home/ubuntu/aklt/reports/CERT_H1/leaves-open.json)); H3's accepted assembly retains its **56-leaf** mathematical bridge ([H3 report](/home/ubuntu/aklt/reports/CERT_H3/report.md)). Main's 416 supplied leaves do not automatically discharge those attachment-specific obligations. Receipts can document progress and independent finite checks; they do not silently close these proof premises or substitute for Palomar's required monolithic Solution export.

**(b) First for an unconditional standard-profile submission: redesign the certificates, not just the scheduler.** This requires proof work, but current evidence now supports a particularly concrete H3 route:

- **H1:** constructors are 109.236 of 139.002 CPU-hours; Gram plus positivity is 8.770 h, matrix/factor loading only 1.494 h, and local tensor checks 11.614 h. The production already shares matrix rows and bundles independent checks. Removing all import/data overhead, adding shards or taking 32 CPUs cannot remove the compulsory serial replay of constructor reductions. A symbolic tensor/network construction theorem, reusable local configuration identities and smaller algebraic PSD/Gram/Sylvester certificates are plausible ways to eliminate repeated enumeration. Any common subproblem must be proved once and reused by theorem references, not merely generated into multiple modules. The model asks for roughly 50–65× mandatory-cost reduction, or hundreds-fold if full con-ron acceptance must finish in its unchanged cap. No measured H1 redesign presently demonstrates it; this is substantial mathematical/representation work.
- **Old H3 engineering route:** data loading and duplicated catalog compilation dominate the producer cost; the plane data and plane catalogs account for about **30.15 of 31.57 GB** of retained oleans. Sharing/import privacy, Init-only Boolean kernels, a natively compiled untrusted balanced-expression elaborator, `noncomputable` data where runtime code is unnecessary, a canonical data view and work-balanced batches are justified. The phase-4 report demonstrates a 5.2× prefix-time / 6.2× prefix-RSS improvement and projects an 8–11× full build reduction, but uint32 storage still leaves 14.33 GB decimal data. The archive has 14,962 distinct B1 planes out of 14,964; simple whole-plane deduplication cannot give the required volume factor. Chunk with `low + Nat.shiftLeft high cutBits`; a multiplication-by-power encoding and putting a small coefficient before a huge operand both have measured con-ron normalization hazards. Remove unused `denseClass`, and bound literals in both Solution and independently protected statement data. Do not ship a patched trusted serializer/parser without explicit upstream/verifier adoption.
- **New H3 structured route:** the concurrently updated phase-5 report has five exact-native-valid cases using inverse-polynomial/Bernstein residuals. Its preferred memory-ten/radius-ten/offset-24 single-exterior-interval model has **529 coefficients / 841 residual rows per state/phase**, about **118.74 MB binary / 286 MB decimal digits**, with two native contraction values below .98. This is a roughly **125× digit-payload reduction** from old planes and is in the scale this budget demands. A real 64-state, four-phase, all-row kernel pilot checks 214,784 inequalities: **3.97 s type checking, 13.26 s build / 2.14 GiB, 6.86 MB stock export, 4.72 s fresh Lean / 1.04 GiB, 3.32 s NanoDa / .59 GiB, 14.47 s con-ron / 1.55 GiB**; theorem axioms `[propext]`. These are reused lane receipts, not new measurements. Copies are in [inputs/H3-phase5-SpatialCheck-stock-replay.json](inputs/H3-phase5-SpatialCheck-stock-replay.json). The 286 MB figure is **literal payload, not a measured full-case export**. Metadata, routing, prefix, soundness and the full installed environment are pending. Verify the exact original five ceilings, supplied quotient and radius-70 constant-outside `StationaryData.PassesV2` contract; combined contraction below one by itself does not prove this unchanged premise. A changed stationary statement needs an explicit revised bridge and Challenge. This is a credible size/time research direction, not a delivered replacement certificate.

Both redesigns require proved soundness/refinement bridges to the chosen public contracts. Native searches and floating or exact external arithmetic are candidate discovery, never Lean proofs. Benchmark complete owners, complete cases and then the combined export; subsecond arithmetic ratios do not include installation and auxiliary bounds.

**(c) A larger/longer-profile request is a fallback for a defined architecture, not evidence of standard-profile fit.** The existing approved request is **32 CPU / 64 GiB, still 19,800 s and a 1,800 s con-ron cap**, only after an authenticated default OOM/timeout. This study's AS-censored failures do not qualify. It may allow the current core/checker workspaces or more compile workers; it does not solve source limits, the protected Challenge, a 100-hour serial replay or original huge literals.

For the **as-built numerical architecture after literal-path fixes**, a numerical request must be much longer. H1 alone gives roughly **102.6 h serial Lean replay**, **23.6–49.6 h NanoDa at ideal four-way checks**, and **34.8–46.3 h default source build / 17.4–19.9 h larger source build** at four/three or eight/seven normal workers. Add H3, core, export/parse and setup: approximately **175–215 h default / 155–190 h larger for mandatory work** is an illustrative planning scale, not a validated upper bound. Requesting **at least 7–9 days of execution (~600,000–800,000 s)** on the larger host would address that scale; a 12-hour allowance would not.

Full con-ron acceptance adds approximately **127–214 h** from the stage-weighted H1/H3 numerical factors at two ideal workers, before giant-catalog parsing or worst single declarations. It therefore needs a separate con-ron cap of order **460,000–770,000 s**, not 1,800, and an aggregate execution/job allowance of roughly **1.1–1.5 million seconds (13–17 days)** on the larger host. The old unchunked stock literal path has censored runs, so even these are not finite completion guarantees. With a redesigned H1/H3 certificate these requests should be recalculated, not carried forward automatically.

Ask initially for the validated 64-GiB profile, measure full installed-environment memory, and request a higher memory tier only with those results; neither 64 nor an arbitrary 128 GiB can currently be certified sufficient for the original full export. Provision **150–200 GiB workspace with ≥20 GiB free throughout**, since old H3 oleans (31.6 GB), H1 matrix/factor oleans (11.0 GB), H3 plane decimal data (35.8 GB), restored H3 hex sources (~29.8 GB), Mathlib and temporary/export copies already approach/exceed 100 GB before H1 export. Separately resolve the 500-MiB submitted-root cap through real compression/representation, an allowed pinned dependency layout, or an explicit source-cap policy change. No contact or profile request was sent.

**Reproduction and remaining limits**

Build/export/checker command lines, start timestamps, exit status, CPU, RSS, VMS, threads and hashes are in the linked JSON receipts. [make_candidate.py](tools/make_candidate.py) and [make_minimal.py](tools/make_minimal.py) recreate the source layouts; [pilot_h2.py](tools/pilot_h2.py) builds only the selected part and prerequisites; [probe_reader.py](tools/probe_reader.py) isolates the unused-literal effect; [h1_archive_sources.py](tools/h1_archive_sources.py) audits final archived owner sources without restoration. These scripts are study helpers, not an approved Palomar submission runner. The existing dependency cache and one warm H2 proof are explicitly disclosed. The invalid early launches and under-sized Comparator control are retained for audit but excluded from performance conclusions. No full certificate, cold-cache timing, authentic cgroup memory peak, complete protected statement comparison, successful core con-ron run or sufficient full-export upper bound has been manufactured.

Historical campaign handoff
- Delivered exact `AKLT.PALFit.conditionalMain`: four explicit certificate premises; all 416 main leaves supplied.
- Open contract names: `AKLT.Blueprint.Top.H1FiniteDataStatementV2`, `AKLT.Blueprint.Top.CertificateStatement`, `AKLT.Blueprint.Top.Automaton10StatementV2`, `AKLT.Blueprint.Top.StationaryCheckStatementV2`.
- Strict 418-print audit: only propext, Classical.choice, Quot.sound; no extra main leaf premise.
- Source-only minimal package: 852 files; whole-tree benchmark: 1,129 files, no generated numeric attachments.
- Full conditional export 889.806 MB; direct Lean and NanoDa accept; con-ron is memory-censored.
- Fresh-build blocker: `AKLT.Cert.H2.Check`; warm reuse disclosed. Blocked: `AKLT.Cert.H2.Finite`, `AKLT.Cert.H2.Main`, `AKLT.Cert.H2.All`, `AKLT.Cert.H2.Audit`, `AKLT.Final.Skeleton`, `AKLT.Final.Audit`, `AKLT.W.REC095.Main`, `AKLT.PALFit.Solution`, `AKLT.PALFit.Audit`.
- H2 and deadMask measured separately in all three replay engines; deadMask is outside minimal closure.
- Authentic 16×32 cgroup/swap enforcement unavailable; affinity and conservative AS bounds enforced instead.
- Cold Mathlib fetch and an official successful end-to-end run remain open.
- Protected Challenge lacks a target and imports local source; exact fixed-table surface needs redesign/approval.
- Missing metadata/license and module headers are independent source blockers; no line-cap violations found.
- H3 has 2,340 compacted sources to regenerate; all 7,964 H1 owner archives scanned/hash-verified.
- Module port script and building pilots delivered; whole-tree port intentionally not performed.
- Updated H1: 139.0 CPU-h, max 11.15 GiB; old 64-GiB cap is not demand.
- Mandatory Lean replay is serial; NanoDa four threads, con-ron two, stages serial.
- H1 needs roughly 50–65× mandatory cost reduction in the optimistic model; larger profile alone cannot do it.
- Original H3 literal format cannot be budgeted by GB; bounded chunks and a much smaller potential are needed.
- New H3 structured pilot reaches ~286 MB decimal payload; full export and semantic bridges are still open.
- External certificate bridges still have H1's 33 and H3's 56 closed Props; follow their exact queues.
- Decide conditional registration versus H1/H3 redesign; a full as-built replay request is measured in days.
- No unconditional theorem, independent Challenge comparison, production acceptance or profile retry entitlement claimed.


## release package

The standalone release is [_pkg/README.md](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/README.md), with its own Git repository. Current package commit: **`125b6ceb182a2e68f86e76033109352da984f4a4`**. First commit: **`933e99cddadb1ae6b85d5f4aff551b6f14f91f42`**, the exact unported copy from main **`d77c3ca85754582f91354dd848ac5a830f73727d`**. [Materialization receipt](release/materialization.json) verifies every input blob against `port-list.tsv`. Main and the original legacy worktree were never ported or edited. The package has **618 first-party Lean files / 7,297,224 bytes**, exactly the 616-file Solution closure plus Challenge and Audit. All 615 legacy source files were converted; no extra experiment or probe Lean file is in the release root. External dependency source under `.lake/packages` is excluded from this first-party inventory.

The result proved and checked is exactly:

```lean
AKLT.Final.main_of_inputs :
  AKLT.Blueprint.Top.H1Statement → AKLT.Blueprint.Top.H3Statement →
  AKLT.Challenge.MainStatementV2

AKLTPalomar.h1_iff : AKLTPalomar.H1 ↔ AKLT.Blueprint.Top.H1Statement
AKLTPalomar.h3_iff : AKLTPalomar.H3 ↔ AKLT.Blueprint.Top.H3Statement
AKLTPalomar.main_iff : AKLTPalomar.Main ↔ AKLT.Challenge.MainStatementV2
AKLTPalomar.aklt_gap_of_inputs : AKLTPalomar.H1 → AKLTPalomar.H3 → AKLTPalomar.Main
```

The three equivalences retain their original `Iff.rfl` proofs; Solution and Audit themselves are byte-unchanged from the skeleton. H1 and H3 are the paper's semantic inputs, explicitly assumed, with H2 proved internally. No additional premise, finite-certificate attachment, or H1/H3 certificate/semantic assembly is imported. The independent Challenge imports only Mathlib and is now **575 lines / 26,919 bytes**. Its one intentional placeholder is the only proof hole. Its slight increase retains an original auxiliary definition, described below; the three advertised statement definitions are unchanged.

**Proof-body changes: none.** [PORT-CHANGES.md](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/PORT-CHANGES.md), [PORT-MANIFEST.tsv](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/PORT-MANIFEST.tsv), and [port-fidelity.json](release/port-fidelity.json) record the transformation. All 616 closure files match the documented mechanical visibility transform (including the already-modern Solution); every original definition and proof body is preserved. The two additional interface adjustments are:

| File / declaration | Change | Reason |
|---|---|---|
| All 615 `AKLT/` files | `module`; public imports; public/exposed section; `backward.privateInPublic` and `backward.proofsInPublic` | Preserve the legacy exported interfaces under the module system; no kernel bypass |
| `AKLT/Challenge/Main.lean`, `AKLT.Challenge.size_neZero` | Explicit `@[expose]` on the Prop-valued instance; original proof unchanged | A public/exposed section alone does not expose this instance |
| `Challenge.lean`, `AKLT.Defs.moment` | Add the original definition verbatim at its original position; update the generator | `spinWeight` reuses `moment._proof_1` in the tree. Omitting its owner created a different helper name in Challenge |

The known `Compass.step` matcher difference is fixed by the module conversion itself. The first post-port comparison then exposed the `spinWeight` helper difference; retaining `moment` fixes it without changing `spinWeight`. The final recursive statement comparison passes with **no definition exemptions**. Generator fixes recognize the exposed instance and use the standalone root by default. No theorem was renamed. No new axiom, unsafe implementation, native proof, external implementation, or opaque declaration was introduced. The original H2 unlimited-heartbeat setting remains the named campaign exception.

The strict Audit prints exactly `[propext, Classical.choice, Quot.sound]` for all five exported theorems. Full transcript: [final serial Audit](release/stages/serial-strict-audit/stdout.log) and the package's [axioms.log](/home/ubuntu/aklt/reports/PAL_FIT/rename/baseline-records/verification/axioms.log). The automated axiom transcript checker passes. These remain conditional theorems, not a proof of the two premises.

| Stage (16-CPU affinity) | Wall s | CPU s | Peak tree RSS GiB | Result |
|---|---:|---:|---:|---|
| Source/configuration | 1.41 | 1.35 | 0.062 | All 618 headers/line caps and config pass; only author TODOs and root LICENSE remain |
| Lean header parser | 0.10 | 0.06 | 0.001 | 618/618 parsed as modules, no header errors |
| Fresh default build, four compilers (development baseline) | 666.13 | 3191.07 | 35.136 | Pass; existing pinned dependency cache; no project artifacts |
| Fresh default build, one compiler (cold-run scheduling) | 2595.60 | 3170.19 | 26.331 | Pass; empty .lake/build, no reused project objects |
| Challenge + Solution + Audit after serial rebuild | 10.27 | 10.15 | 3.803 | Pass; one authorized Challenge placeholder warning |
| Strict Audit after serial rebuild | 2.82 | 2.75 | 4.502 | Pass; all five expected axiom prints and exact types |
| Canonical Challenge, trusted dependency paths only | 3.94 | ≈3.83 | 3.663 | Pass; independent random alias; source is Mathlib-only |
| Canonical Challenge stock export | 8.57 | ≈8.42 | 6.366 | Pass |
| Solution stock export, protected policy | 32.98 | ≈32.82 | 7.084 | Pass; full target closure |
| Protected Comparator: NanoDa then Lean | 553.58 | ≈599.91 | 23.226 | Statement comparison and both mandatory kernels accept |
| Official pinned con-ron, verified, two workers | 420.76 | ≈519.88 | 47.189 | Accepts 63,516 declarations; local peak exceeds default RAM |
| Stock export after final serial rebuild | 33.05 | 32.99 | 7.873 | Pass; byte identity to the independently checked export |

All timed stages inherit affinity **0–15**, and the monitor samples descendants through **every thread's** children. The four-worker and one-worker builds each started with an empty project `.lake/build`; only the pinned, prebuilt dependency cache was reused. All nine dependency Git heads match the manifest. No `lake update`, Mathlib source build, package-store write or legacy project olean was used. The largest line count is 1636, below 10,000. Challenge also satisfies 1,000 lines / 100 KiB, although 575 lines exceeds the preferred 300-line review surface (a warning, not a hard failure).

The local resource authorization was up to 48 Lean processes / 300 GB; observed compiler concurrency was four, then one. The measurement harness uses 16-CPU affinity, a per-process 240-GiB virtual-address backstop, and a 260-GB sampled tree-RSS abort threshold. Independent-checker runs overlapped part of the serial build locally; combined observed use stayed well below 300 GB and CPU affinity stayed inside the same 16 CPUs. The budget total below adds stage wall times serially and takes no credit for that overlap. **This is not a 32-GiB cgroup acceptance run.** RSS sums may double-count shared mappings; parent/controller overhead and page-cache accounting need the real cgroup.

The official supervisor probe fails here because cgroup delegation is unavailable (`sudo` is blocked by the inherited no-new-privileges setting; the cgroup filesystem is read-only). [Supervisor receipt](release/stages/official-supervisor/result.json) and [error](release/stages/official-supervisor/stderr.log) preserve the actual result. The installed bubblewrap was 0.9.0; the official pinned 0.12.0 installer was successfully run into a writable local tools directory after rootless build-tool/header setup. The final canonical build, exports and judge use the official namespace/read-allowlist policy and Comparator's nested sandbox. The official supervisor's authenticated cgroup/status/seccomp protocol was not reproduced, so no registry/production acceptance or validated profile retry is asserted.

Namespace PID 1 does not propagate descendant CPU rusage. The unadjusted wrapper `wait4` totals are preserved in raw receipts; **≈ CPU values** use sampled process-tree sums instead. This correction is in [metrics.json](release/metrics.json), without rewriting raw evidence. The Comparator's internal observed processes used approximately **332.38 CPU s NanoDa / 240.50 CPU s Lean**, with peaks **18.842 / 23.118 GiB**. Parsing/comparison adds approximately 26.61 CPU s. NanoDa is configured for four check threads, Lean replay is serial, and they execute sequentially. Con-ron used approximately **519.68 process CPU s**, two workers, and **47.19 GiB**. These internal wall/CPU estimates have sampling error; they are not independent duplicate replay measurements.

The full stock Solution export is **671,987,125 bytes**, SHA-256 **`9a6aba195545920cd2b62a256cb9b64d3681de90d91f32193cc6071ec503ae1a`**. The canonical Challenge export is **154,767,051 bytes**. Both are frozen outside the source root. The final serial re-export equality receipt is [serial-export-equality.json](release/serial-export-equality.json); byte identity binds the earlier three-kernel acceptance to the final fresh source build without repeating those expensive checks. Full primitive/root lists are [export-roots.json](release/export-roots.json). The con-ron used is the official 4.36.0-rc1 override, binary SHA-256 `4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`.

The measured serial component path totals **3630.03 s (1.008 h)**, including source/header checks, the fresh default build, explicit targets, strict Audit, both exports, protected Comparator and full con-ron. CPU for that path totals approximately **4349.36 s (1.208 CPU-hours)**. The redundant final re-export is shown separately. Add an explicitly **unmeasured cold Mathlib-cache fetch estimate of 600–1,800 s**, 60–180 s for pinned dependency checkout, and 120–600 s for a missing checker override/tool bootstrap: approximately **4410–6210 s (1.23–1.73 h)**, versus **19,800 s**. This is conditional on the pinned cache being available; slow/unavailable providers are not bounded by the estimate. The cold runner refuses a missing/stale cache instead of building Mathlib. This local study does not claim a measured cold fetch.

**Memory conclusion:** the measured serial build (26.33 GiB aggregate RSS) and mandatory Comparator (23.23 GiB) are below the nominal 32-GiB ceiling, with no physical-cgroup claim. Full con-ron acceptance as measured requires more than 32 GiB; its 47.19-GiB footprint fits a nominal 64-GiB host. On the default profile an authenticated con-ron capacity limit may leave that advisory replay inconclusive. The local numbers do not authorize the larger profile. Also, the cold runner deliberately sets `LEAN_NUM_THREADS=1`, whereas the production verifier currently strips that variable from its outer sandbox; its actual automatic Lake scheduling still needs an official run. No claim that the four-worker RSS sum is a cgroup OOM is made.

**Cold runner.** [scripts/cold-verify.sh](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/scripts/cold-verify.sh) clones a given full package commit and invokes only the clone's verification code. It has no dependency on this worktree, its build objects, reports, the original main repository, or the shared package store. Required external inputs are the Git repository/commit, official verifier checkout, installed toolchain, network-accessible pinned dependencies/cache, and normal Linux build utilities. Homes, caches, bootstrap tools, canonical source copies, logs and JSON receipts stay under the chosen output directory, outside the source root. The pipeline fetches exact pins through the official helper without update hooks, gets the trusted Mathlib cache, checks it with `--no-build`, then runs all mechanical stages and verified con-ron with the shared execution deadline and 30-minute replay cap.

```sh
systemd-run --user --scope -p CPUQuota=1600% -p MemoryMax=32G -p MemorySwapMax=0 \
  bash /path/to/package/scripts/cold-verify.sh \
  --repository /path/to/package --commit 125b6ceb182a2e68f86e76033109352da984f4a4 \
  --verifier /path/to/PalomarSubmission --output /tmp/aklt-cold-release
```

The output path must be new. It inherits the caller's cgroup throughout, never creates a sibling scope, and records stage checkpoints as they complete. Exit 0 means all mechanical components accepted, with registry preparation still required. Exit 2 means mandatory acceptance plus locally evidenced con-ron deadline/OOM capacity; this is not an authenticated Palomar verdict. Other failures exit 1. The committed-clone/budget smoke test ([receipt](release/cold-budget-smoke/receipt.json)) checks an exact clean package checkout and noninteractive JSON failure under a deliberately tiny shared budget, before fetching dependencies. The full network/cold-cache path has not been executed here; it is the supplied orchestrator rerun, and its cache timing remains estimated. Script syntax, source inventory, source hashes and strict axiom checks were also checked.

**Remaining findings owned by the author/maintainers:** `formalization.yaml` still explicitly marks formalization author and responsible maintainer identities/ORCIDs, manuscript and companion authors, SPDX license/root LICENSE text, immutable public manuscript/companion URLs/commits/manifests/receipts, and underlying proof-development provenance as TODO. The official metadata minimum rejects the placeholder identities; the source helper reports `package.metadata_todo` and `package.license_missing`. Existing QICLean license notices are preserved. Independent review of FIDELITY remains pending. None of these TODOs was filled with an invented identity or license. Authenticated 16×32 production/cold-cache evidence and any advisory con-ron capacity classification remain for the orchestrator/official service.

All findings in the module port, public interfaces, declaration matching and local mechanical checks that are ours to fix have been fixed. Development harness corrections (header JSON nesting, filtering nonexistent optional dependency library paths, and namespace CPU accounting) are recorded in the retained attempts; no failed development control is presented as a theorem rejection or final acceptance. Port and verification source code is committed; source proofs remain unchanged.

ORCH-SUMMARY
- Release root: `/home/ubuntu/aklt/wt/PAL_FIT/_pkg`; independent Git repository.
- Package commit: `125b6ceb182a2e68f86e76033109352da984f4a4`; unported first commit: `933e99cddadb1ae6b85d5f4aff551b6f14f91f42`.
- Origin pin: main `d77c3ca85754582f91354dd848ac5a830f73727d`; legacy tree untouched.
- Exactly 618 first-party Lean files; all module-system, all under line caps; Challenge 575 lines.
- The reduction is exactly H1Statement → H3Statement → MainStatementV2; H2 proved internally.
- `h1_iff`, `h3_iff`, `main_iff` remain Iff.rfl; original proof-body changes: none.
- Compass matcher fixed by port; size_neZero explicitly exposed; moment retained for helper identity.
- Fresh builds, strict five-theorem Audit, independent statement comparison, Lean and NanoDa pass.
- Verified con-ron accepts 63,516 declarations in 421 s, peak ≈47.19 GiB.
- Serial fresh build: 2,596 s / 3,170 CPU s / 26.33 GiB; final export identity checked.
- Measured serial mechanical path ≈3630 s; cold setup estimate gives ≈4410–6210 s < 19,800 s.
- Default RAM fits observed build/mandatory replay; full con-ron needs more than 32 GiB.
- Namespace-stage CPU uses approximate process-tree sampling; raw wrapper usage is preserved.
- Full official cgroup/status/seccomp supervision unavailable; no production verdict or retry entitlement.
- Cold clone runner, logs, JSON receipts and deadline smoke test delivered; actual cache fetch estimated.
- Production Lake scheduling may differ because it strips LEAN_NUM_THREADS; run the real cgroup check.
- Author identities/ORCIDs, license, public provenance/companion receipts and fidelity review remain TODO.

## complete release — hand-written port

The assigned hand-written port phase is complete. The release now targets the
**unconditional** `AKLTPalomar.aklt_gap : AKLTPalomar.Main`, with proof source
`main_iff.mpr CertData.Close.main`. The two-input reduction remains the ordinary
library theorem `AKLT.Final.main_of_inputs`. The generated certificate sources
are deliberately absent pending the two regeneration agents; no unproved
certificate or analytic assertion was inserted to make the closing modules build.
The unconditional Solution/export is therefore **not yet verified**.

### Package, files, and exact scope

Release root: [`_pkg`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/README.md). Source revision:
`8f59d336acf2fc13428893faf26097890f4f288b`. Package commit: **`169a4007abea6cc73e4630ef99b797491a1708a7`**.
The first commit of the independent package remains the exact unported copy
`933e99cddadb1ae6b85d5f4aff551b6f14f91f42`. The legacy development and certificate
objects were not changed or reused as project build inputs.

- **1,104 original hand-written files**: the 1,102-file hand-written closure of
  `CertData.Close.All` plus the empty H1 generation root and its closing Audit.
  This extends the previous 615 original AKLT files by 489 original sources.
- **1,115 first-party Lean files** in the final package, totaling
  **10,654,396 bytes**. All use `module`; the longest is
  `AKLT/Defs/Automaton10Data.lean`, **1,636 lines**. No line-cap violation remains.
- Root Challenge imports **Mathlib only**, has **161 lines / 7,736 bytes**, has no
  H1/H3 premise definitions, and contains the one conventional placeholder.
  Main and MainStatementV2 retain the original physical statement and definitions.
- Root Solution imports `CertData.Close.All`; Audit prints the four closed inputs/
  headline and the two Solution theorems once regenerated certificates are present.
- [`port-list.tsv`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/port-list.tsv), [`PORT-MANIFEST.tsv`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/PORT-MANIFEST.tsv),
  and `verification/source-inventory.json` give the exact source paths and hashes.
  Generated sources are excluded from Git. The generated inventory has exactly
  **7,964 H1 + 5,032 H3 = 12,996** module names; 2,340 legacy H3 literal sources
  were compacted, so their regeneration cannot be replaced by copying old files.

Lake libraries separate `AKLT`, hand-written `CertKernels`, `CertDataH1`,
`CertDataH3`, and `CertDataClose`; default targets are Solution and Audit.
Challenge is explicit. `Handwritten` covers all original unblocked sources and
the samples. All **1,109 currently buildable Lean files** now have fresh project
objects; the dependency packages are the existing pinned cache, not a Mathlib
source build. No `lake update` ran and `.lake/packages` was not changed.

### Visibility, proof bodies, exposed declarations, and prose

**Original proof-code changes: none.** The 1,104-file token fidelity check passes
against the pinned source after comment removal and exactly the visibility edits
below. Statements, definition bodies, theorem names, and existing private
modifiers are preserved. `h1_iff`, `h3_iff`, and `main_iff` in the retained regression
still use their original `Iff.rfl` proofs.

| File / declarations | Required change | Proof-body change |
| --- | --- | --- |
| Newly imported legacy modules | `module`, public imports, public/exposed section, the two backward visibility migration options | None |
| `AKLT/Challenge/Main.lean`, `AKLT.Challenge.size_neZero` | Retain the prior explicit `@[expose]` on the Prop-valued instance | None |
| `AKLT/Cert/H1/Literals.lean`, `rowExpr`, `elabIntRow` | `meta section`, required for term elaborators under modules | None |
| `CertData/H3/Kernel/Literal.lean`, `decodeHexBalanced`, `elabH3Hex` | `meta section`; output remains an ordinary numeral | None |
| `CertData/H3/Kernel/PrefixView.lean`, `mergeFuel_eq`, `mergeSortFuel_eq` | `import all Init.Data.List.Sort.Basic` makes the original sort bodies visible | None |
| Root Solution | Authorized new unconditional wrapper `aklt_gap := main_iff.mpr CertData.Close.main`; old conditional wrapper retained unchanged in Regression.Solution | New package wrapper only |
| RegenSamples.H1/H1Consumer/H3/H3Consumer | New tiny kernel reductions and applications of existing soundness lemmas | New interface tests only |

The module port exposes public checker/arithmetic bodies for downstream kernel
reduction. The actual compiled interface inventory records **1,153 H1** and
**1,083 H3** available bodies in their dependency surfaces. More focused reduction
lists identify **410 H1** and **392 H3** entries, including generated matchers and
projections. Representative names are H1 `Gaussian.mul`, `Table.get`,
`packedThresholdRow`, production `sparsePack`, `packedRowCheck`, `RowsAccepted`,
`constructedSectorRows`, `Block.Accepted`, and `Case.Accepted`; H3 `PlaneTree.get`,
`packedRowCheck`, and production `Graph.quotient`, `Tables.data`, `planeBatch`,
`rawBatch`, `prefixBatch`, and `sumResults`. Full names, modules, and actual body
visibility are in [`verification/regen-interface/`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/regen-interface/resolution.json).
The complete named API surfaces cover implicit constructors, projections,
instances, and conservative short-name resolution; the 100/69 lexical candidate
lists are not represented as exact elaboration traces of every generated file.

[`REGEN-INTERFACE.md`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/REGEN-INTERFACE.md) lists H1's eight and H3's nine direct
hand-written imports, unchanged module/declaration names, public/exposed generated
headers, and the actual compiling sample/consumer pair for each family. It also
names the `h1_row%` and `h3_hex%` syntax registrations and handlers. No original
mathematical proof is rewritten. Detailed edits are in
[`PORT-CHANGES.md`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/PORT-CHANGES.md) and the fidelity/prose receipts.

American English and serial commas are applied to authored prose and imported
comments/doc strings. Identifiers are not renamed; **419 identifier tokens** with
British spellings and their source locations are listed in
[`BRITISH-IDENTIFIERS.tsv`](/home/ubuntu/aklt/reports/PAL_FIT/rename/baseline-records/BRITISH-IDENTIFIERS.tsv), including external Mathlib
names. Manuscript labels, such as `l:colour`, retain their exact spelling. Raw
checker transcripts remain verbatim. `ClosedTrail` has a one-line first-hit-path
doc comment everywhere it is defined, including the regression template.
References now use `d:model` in `sec1-result.tex` for the model, Hamiltonian, and
VBS product; `d:poly` in `sec3-quantum-frames.tex` for normalization; and `t:main`
for nonvanishing. The nonexistent old labels are removed from the current Lean comments.

### Builds, strict Audit, and protected regression

The final clean build starts with a newly empty `.lake/build`, uses 12 compiler
workers with affinity 0–15, and completes all unblocked originals plus Challenge
and the regression targets. The corrected audit helper is then built, and the
post-edit builds and final strict Audit pass. Inherited trailing whitespace from
copied legacy proofs is retained to preserve the source bodies; it causes no
official source finding. Earlier development failures are retained under
`full-port/stages/`: literal meta marking, private standard sort bodies, the H1
empty-root glob, and audit-helper type inference. An initial overlapping Lake
repair invocation also caused stale-object lookup failures; the independent
final clean build has no such failure.

Commands (PATH begins with `$HOME/.elan/bin`):

```sh
LEAN_NUM_THREADS=12 lake build Handwritten Challenge Regression.Solution Regression.Audit
lake build AuditHandwritten
lake env lean -j1 -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true AuditHandwritten.lean
python3 scripts/check_axioms.py AUDIT_LOG --mode handwritten
python3 scripts/verify_headers.py --verifier VERIFIER --report HEADERS_JSON
python3 scripts/release_verify.py --verifier VERIFIER --work NEW_OUTPUT --existing-dependencies --regression-inputs
```

| Stage | Wall, s | CPU, s | Peak tree RSS, GiB | Result |
| --- | ---: | ---: | ---: | --- |
| Official source/configuration checks | 3.426 | 3.342 | 0.065 | 2 author-owned TODO findings |
| Lean header parser, all 1,115 files | 2.242 | 2.272 | 1.712 | PASS |
| Fresh hand-written + Challenge + regression build | 699.726 | 8624.126 | 56.848 | PASS |
| Available-source Audit target build | 13.307 | 13.789 | 4.029 | PASS |
| Paper-reference comment rebuild | 13.954 | 21.059 | 3.831 | PASS |
| Serial-comma comment rebuild | 39.499 | 154.899 | 17.940 | PASS |
| Final American English comment rebuild | 25.681 | 92.067 | 23.582 | PASS |
| Strict available-source Audit | 5.665 | 5.630 | 4.761 | PASS |
| Axiom transcript guard | 0.103 | 0.095 | 0.001 | PASS |
| Protected two-input Challenge build | 8.845 | ≈8.750 | 3.667 | PASS |
| Protected two-input Challenge export | 17.114 | ≈16.940 | 6.366 | PASS |
| Regression.Solution full export | 49.483 | ≈49.300 | 7.084 | PASS |
| Protected Comparator: NanoDa, then Lean | 662.867 | ≈740.070 | 23.226 | PASS |
| Verified con-ron, two workers | 627.995 | ≈740.140 | 47.186 | PASS |
| Final-source export identity check | 46.557 | ≈46.370 | 7.081 | PASS |


The accounting sum of these stages is **2216.464 wall seconds** and
**10518.850 CPU seconds (2.922 CPU-hours)**. Stages overlapped;
this is not an isolated cold end-to-end timing. All timing processes and their
children inherit a verified 16-CPU affinity mask. The measured builds use at most
12 Lean compiler processes; occasional header probes remain below the 48-process
allowance. Local diagnostics use 240-GiB per-process virtual-address limits and
285-GB sampled RSS watchdogs. The observed cgroup high-water mark during overlapping
stages is 93.94 GB, below the authorized 300 GB. Its limits are not a Palomar
profile. No 32-GiB cgroup run is claimed or required by the author's revised target.
RSS sums may double-count shared mappings. Namespace wrapper `wait4` can omit
child CPU; stage receipts use sampled child totals where necessary and mark them
approximate. These resource observations are not used as acceptance limits.

Comparator runs NanoDa, then Lean, sequentially. Sampled internal times are
approximately **344.85 s wall / 423.17 s CPU** for NanoDa and
**281.93 s wall / 282.00 s CPU** for Lean replay.
Verified con-ron uses two workers. The actual protected Comparator compiles a
randomly named independent Challenge with trusted dependency paths only and
replays both exports without candidate sources/objects in the judge sandbox.
Official verifier checkout: `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`;
con-ron override: 4.36.0-rc1, official pinned digest
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`.
The toolchain and all nine dependency Git pins match the manifest.

**Lean and NanoDa accept the full two-input Solution export; con-ron accepts
63,516 declarations.** The export is **671,987,125 bytes**, SHA-256
`9a6aba195545920cd2b62a256cb9b64d3681de90d91f32193cc6071ec503ae1a`.
The final source re-export is byte-identical to that three-checker export and to
the earlier two-input release export. The later source changes are documentation
and the independent audit helper, with an explicit source-binding receipt.
These independent checker claims apply to Regression.Solution. The new certificate
kernels/leaf proofs are Lean-built and axiom-audited; their independent full
unconditional export replay remains a task after certificate regeneration.

Strict Audit checks **21,855 declaration entries** through Lean.collectAxioms,
the same API used by `#print axioms`; module-local realizations can repeat names.
The AKLT/CertData interface inventory has 18,955 distinct names, plus sample and
regression declarations. The explicit axiom prints for all 15 available package/
sample exports pass. The six reduction/identity prints have exactly
`[propext, Classical.choice, Quot.sound]`. H1's Boolean/signed-packing reductions
and H3's packed-row check use `[propext]`; literal reductions and the H3 walk step
use no axioms; the two soundness-consumer proofs use the three permitted axioms.
The full exact transcript is
[`verification/full-port/axioms-and-interface.log`](/home/ubuntu/aklt/reports/PAL_FIT/rename/baseline-records/verification/full-port/axioms-and-interface.log).

Available ordinary statement:

```lean
AKLT.Final.main_of_inputs :
  AKLT.Blueprint.Top.H1Statement → AKLT.Blueprint.Top.H3Statement →
  AKLT.Challenge.MainStatementV2
```

New root source statements, awaiting generated imports:

```lean
AKLTPalomar.main_iff : AKLTPalomar.Main ↔ AKLT.Challenge.MainStatementV2
AKLTPalomar.aklt_gap : AKLTPalomar.Main
```

The H1 sample exports `checked : lowerTriangularCheck rows = true` and
`packed_reduces : packed = -15`; its consumer proves the actual matrix's
above-diagonal entries vanish for every finite index and repeats the literal
and packed reductions. The H3 sample exports its true packed-row check and the
one-step walk equation; its consumer proves the actual component bound using
`packedRowCheck_sound` and repeats the literal reduction. All full signatures
and source are in the four small RegenSamples modules.

### Pending generated dependencies and remaining findings

Only `CertData.H1.Close.Main` and `CertData.H3.Close.Main` directly import generated
modules. Their direct requirements are respectively
`CertData.H1.Generated.Bridge.Targetassembly0000` and `CertData.H3.Bridge.All`.
The exact 12,996 transitive generated names, direct imports, and six blocked
hand-written targets are in `verification/generated-modules.json`:

1. `CertData.H1.Close.Main` — the H1 target assembly and its generated closure.
2. `CertData.H1.Close.Audit` — transitively the same H1 closure.
3. `CertData.H3.Close.Main` — the H3 bridge and its generated closure.
4. `CertData.Close.All` — both families.
5. `Solution` — both families through CertData.Close.All.
6. `Audit` — the complete Solution.

The regeneration agents must update generator output headers, regenerate the
compacted literal shards, build every generated module against this release,
and supply input pins, source archives, manifests, and per-theorem receipts.
If they split files, update the exact module inventory, Lake globs, and ignore
rules together. Then build the six closing targets, run strict root Audit,
and run the **unconditional** protected Comparator/export/con-ron pipeline.
No remaining mathematical leaf premise is introduced in the root theorem.

Official source/header checks report no mechanical tree violation. The remaining
author-owned fields are author/maintainer identities and verified ORCIDs,
manuscript/artifact authorship and immutable public provenance, release SPDX
license and matching root LICENSE, and underlying proof-development provenance.
Independent fidelity review remains pending. This project is not being submitted
to Palomar; no registry preparation or production capacity approval is requested.

The fresh-clone runner supports hash-pinned H1/H3 generated-source archives,
fetches the exact dependency/cache pins, and runs the full workflow. It has no
default wall limit; optional wall, RSS, and virtual-address watchdogs are
configurable and recorded. `--regression-inputs` selects the available historical
reduction while certificates are absent. A two-second committed-clone smoke test
correctly retains an incomplete JSON receipt at its intentional deadline; no
cold dependency/cache fetch or full cold run is claimed. The archive installer
passed digest/install/overwrite/path-escape smoke checks outside the release.
All runner code uses paths relative to the clone, the supplied verifier, and
explicit artifact inputs, not this campaign's report directory or package store.

Receipts: [`verification/full-port/README.md`](/home/ubuntu/aklt/reports/PAL_FIT/rename/baseline-records/verification/full-port/README.md),
[`summary.json`](/home/ubuntu/aklt/reports/PAL_FIT/rename/baseline-records/verification/full-port/summary.json),
[`port-fidelity.json`](/home/ubuntu/aklt/reports/PAL_FIT/rename/baseline-records/verification/full-port/port-fidelity.json),
and the complete stage logs under [`reports/PAL_FIT/full-port`](/home/ubuntu/aklt/reports/PAL_FIT/full-port/metrics.json).

## Previous phase summary

- FULL PORT COMPLETE for the assigned hand-written phase; package commit 169a4007abea.
- Root Challenge/Solution now state the unconditional main theorem; no H1/H3 antecedents.
- 1,104 original hand-written files; 1,115 Lean files total; all module headers, max 1,636 lines.
- Challenge: 161 lines / 7,736 bytes, Mathlib only, one conventional placeholder.
- No original proof-code changes; only recorded visibility/exposure and prose edits.
- Both literal elaborators are meta; PrefixView imports all standard sort implementation bodies.
- 1,109 available sources build from fresh project objects; strict axiom audit passes.
- Protected two-input regression accepted by Lean, NanoDa, and con-ron; final export hash unchanged.
- REGEN-INTERFACE.md gives APIs, headers, exposed bodies, and compiling H1/H3 sample consumers.
- Regenerate 7,964 H1 and 5,032 H3 modules against this package; legacy objects cannot be reused.
- Pending: CertData.H1.Close.Main/Audit, CertData.H3.Close.Main, CertData.Close.All, Solution, Audit.
- Then verify the unconditional full build, root Audit, Comparator, and con-ron export.
- Author metadata/provenance, LICENSE, and independent fidelity review remain TODO.
- Authored prose is American English; 419 British identifier tokens are listed without renaming.
- No Palomar resource profile is an acceptance constraint; cached-dependency timings are recorded.
- No cold full run or unconditional export acceptance is claimed; clone/archive smoke checks are scoped.

## American-English identifier rename

**STATUS: RENAME COMPLETE.** All first-party identifiers in the release now use
American English, including declarations, namespaces, structure fields, local
binders/definitions, imports, analytic source filenames, generator output names,
and references in comments, notes, and inventories. No compatibility aliases with
the old spellings remain. The package is committed and clean.

Package commit: **`d1320320e7cbf2d216d0afc87be92aabb206d690`**. Verified source commit:
`e0597c0c7910b671f8bc816983e4ba61a26160eb`; later commits add records only.
Baseline: `169a4007abea6cc73e4630ef99b797491a1708a7`.
Release root: [`_pkg`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/README.md).

### Map, counts, and renamed paths

The following substitutions apply inside identifiers, case-insensitively.
Character case is retained through the corresponding character positions, so
lowercase, uppercase, title case, and mixed-case occurrences are covered.

| British spelling | American spelling |
| --- | --- |
| `neighbour` | `neighbor` |
| `colour` | `color` |
| `fibre` | `fiber` |
| `centre` | `center` |
| `labelled` | `labeled` |
| `labelling` | `labeling` |
| `catalogue` | `catalog` |

These seven rules cover the original list. The first-party source contained no
additional spelling family from that list requiring another rule.

- **419 listed source identifier-token spellings** updated. These include
  qualified references and local names, so they are not a declaration count.
- **646 compiled declaration names** change, including private/generated helper
  names: 422 public names under AKLT, 223 private AKLT names, and one CertData name.
- **356 Lean files** receive spelling edits, plus the independent regression
  Challenge template. **Eight Lean files** change names; **zero directories**
  require renaming. Imports and private module-name components change together.
- The source/docs/archive commit has **393 changed-path entries**: 368 modified
  files, eight detected renames, one new current-name inventory, and 16 obsolete
  historical records removed from the current tree. Eleven current verification
  files are added afterward, for **404 changed-path entries** across the phase.
- There are **1,199 tracked files**, including **1,115 Lean files**. The available
  **1,109** Lean files have fresh project objects; the same six closing targets
  remain blocked on generated certificates.

| Original source path | Current source path |
| --- | --- |
| `AKLT/W/REC004/FibreExpansion.lean` | `AKLT/W/REC004/FiberExpansion.lean` |
| `AKLT/W/REC005/Fibres.lean` | `AKLT/W/REC005/Fibers.lean` |
| `AKLT/W/REC012/Fibres.lean` | `AKLT/W/REC012/Fibers.lean` |
| `AKLT/W/REC019/R4/FibreExpansion.lean` | `AKLT/W/REC019/R4/FiberExpansion.lean` |
| `AKLT/W/REC021/Fibres.lean` | `AKLT/W/REC021/Fibers.lean` |
| `AKLT/W/REC043/Fibres.lean` | `AKLT/W/REC043/Fibers.lean` |
| `AKLT/W/REC082/PE/Fibres.lean` | `AKLT/W/REC082/PE/Fibers.lean` |
| `AKLT/W/REC089/FibreFactors.lean` | `AKLT/W/REC089/FiberFactors.lean` |

[`AMERICAN-ENGLISH-IDENTIFIERS.tsv`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/AMERICAN-ENGLISH-IDENTIFIERS.tsv) replaces
the old identifier inventory. The exact old-to-new declaration map is retained
outside the current source tree in [`declaration-map.tsv`](/home/ubuntu/aklt/reports/PAL_FIT/rename/declaration-map.tsv),
so stale first-party names are not left in tracked notes. Source/import lists,
PORT-MANIFEST.tsv, statement-source hashes, the regeneration API inventories,
README, FIDELITY.md, PORT-CHANGES.md, and REGEN-INTERFACE.md contain current names.
Both Comparator configurations were checked; their headline theorem names needed
no spelling change.

### Exclusions and semantic checks

**Paper labels:** every original citation-label multiset is preserved. The only
remaining affected spellings in tracked files are **`l:colour`** and
**`l:quantumfibre`**. In Lean comments these occur in
`AKLT/Blueprint/Gap/NodesPeriodic.lean` (one),
`AKLT/Blueprint/Q/NodesPolynomial.lean` (two), and
`AKLT/Blueprint/Q/NodesQuantum.lean` (six). REGEN-INTERFACE.md cites `l:colour`,
and the search/semantic receipts record the same exact labels. The final scan
finds **15 matching lines**, all within these allowed citation-label strings.
All other paper labels, including those without affected spelling, are unchanged.

**External names:** Mathlib, Lean, and other dependency names are unchanged, as
are all nine dependency pins and their sources. A read-only inventory of the
loaded dependency environment found 52 case-insensitive spelling matches,
including `Lean.labelled`, Quiver's labelling API, FibreFunctor names, and a
case-insensitive false positive in `Real.fibRec`. The complete preserved list is
[`external-names.json`](/home/ubuntu/aklt/reports/PAL_FIT/rename/external-names.json). None is an affected reference in
the current tracked Lean source. No dependency source was edited or rebuilt.

**External data keys:** all **27 certificate-generator scripts** were reviewed.
The ten affected string literals are eight emitted Lean code fragments in the
H1 coverage/index generators and two Lean leaf-name metadata values in the H3
audit generator. There is **no affected external input key to rename**. All
**851 literal string-key accesses** compare identically before and after the
change, and all Lean string-literal values compare identically. Numeric literals,
packed input data, binary formats, input filenames, and arithmetic are unchanged.
The generators now emit/use `Catalog`, `catalog`, `catalogCheck`, and
`CenterZeroV2Leaf`, consistently with the new kernel API.

Every one of the **1,115 Lean sources plus the regression template** is checked
against the exact mechanical spelling transform of the baseline, with citations
and external names protected. No extra proof rewrite, axiom, premise, or semantic
workaround was introduced. Fresh compilation validates the resulting resolution
of the renamed references. The available alias theorems `h1_iff`, `h3_iff`, and
`main_iff` retain `Iff.rfl` and pass the strict audit.

Root **Challenge.lean is byte-identical to the baseline**: its own physical
statement definitions already had American names. It remains Mathlib-only,
**161 lines / 7,736 bytes**, with one conventional placeholder and no H1/H3
premise definitions. It has **no spelling-pattern match at all**, including
comments. The conditional regression template's analytic names are updated to
match the in-tree definitions.

### Collision check

Before editing, the complete 18,955-name compiled first-party declaration set
was mapped to proposed names. No proposed full declaration name collides with
another declaration. Target paths have no collision. A conservative per-file
check found neither an old name and existing new counterpart together nor a
many-to-one local-name mapping. No alternative spelling or guessed resolution
was needed.

A baseline prefix audit also checks **23,952 namespace/declaration prefixes**,
with zero merging collisions. After the fresh build, the current compiled set is
**exactly** the expected renamed image of the baseline: **18,955 names, zero
missing, zero extra**. Every current regeneration-interface name resolves in that
fresh environment. These results are in
[`declaration-bijection.json`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/rename/declaration-bijection.json)
and [`collision-check.json`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/rename/collision-check.json).

### Verification and measurements

The original `.lake/build` was moved outside the release root, and all available
sources were rebuilt with **12 Lean compiler workers**. No legacy project olean
was used. The pinned Mathlib/dependency artifacts were already cached; no
`lake update` or Mathlib source build occurred. All measured stages run under
verified CPU affinity 0–15 with the authorized local memory envelope.

| Stage | Wall, s | CPU, s | Peak tree RSS, GiB | Result |
| --- | ---: | ---: | ---: | --- |
| External-name inventory (read only) | 19.743 | 19.714 | 4.742 | PASS |
| Fresh hand-written tree + Challenge + audit + samples | 738.088 | 8985.206 | 55.378 | PASS |
| Strict whole available-tree Audit | 5.164 | 5.160 | 4.761 | PASS |
| Explicit axiom transcript guard | 0.204 | 0.104 | 0.001 | PASS |
| Official Lean header parser, all files | 2.246 | 2.232 | 1.660 | PASS |
| New-name generator ABI probe | 4.656 | 4.593 | 4.426 | PASS |
| Official source/configuration checks | 2.517 | 2.495 | 0.062 | 2 author-owned TODOs |
| Protected pipeline header parse | 0.104 | 0.087 | 0.001 | PASS |
| Regression explicit targets | 10.480 | 11.392 | 0.949 | PASS |
| Strict regression Audit | 3.437 | 3.399 | 4.505 | PASS |
| Explicit axiom transcript guard | 0.103 | 0.028 | 0.001 | PASS |
| Protected independent regression Challenge | 4.446 | ≈4.340 | 3.678 | PASS |
| Protected Challenge export | 9.196 | ≈9.030 | 6.365 | PASS |
| Full renamed regression export | 35.353 | ≈35.190 | 7.082 | PASS |
| Comparator: NanoDa then Lean | 719.238 | ≈792.710 | 23.226 | PASS |
| Verified con-ron replay (two workers) | 579.757 | ≈727.110 | 47.182 | PASS |


The full official source/configuration check reports only the existing
**author metadata TODOs and missing root LICENSE**. Every module header is parsed
by Lean; there is no line-cap or soundness-token finding. The maximum Lean source
length remains **1,636 lines**. Strict Audit passes for **21,855 declaration
entries** (18,955 distinct AKLT/CertData names plus samples/regression and repeated
module-local realizations), allowing only `propext`, `Classical.choice`, and
`Quot.sound`. All 15 explicit available-export axiom prints pass.

Both existing regeneration sample/consumer pairs build from the fresh tree.
An additional fixture outside the release executes the actual H1 generator tree
printer and compiles a small `Catalog` lookup, checks the `catalogCheck` ABI,
resolves `CenterZeroV2Leaf`, and kernel-proves `kernelCenter = (0, 0)`. It is an
interface test, not a production coverage certificate.

The protected independent two-input Challenge and full regression Solution pass
**both NanoDa and Lean**, followed by **con-ron acceptance of 63,516 declarations**.
The new export is **671,986,654 bytes**, SHA-256:
`ea82aaec07c458ff23d38403de8cc22fc93b488cebc3a99ebe4ed6701d7fab6d`.
It is expected to differ from the baseline: serialized identifier spellings,
generated hygiene fingerprints, and name interning change. A positional wire
comparison is not a semantic comparison, and no byte-equivalence claim is made.
The exact source substitution, collision/bijection checks, data invariants,
fresh Lean kernel build, and independent checkers are the evidence for this phase.

The Compiler/NanoDa/Lean/con-ron resource measurements are recorded above; namespace
CPU accounting may use sampled child totals, and summed RSS can double-count
shared mappings. Comparator runs NanoDa and Lean serially; con-ron uses two workers.
No Palomar production resource ceiling is an acceptance constraint for this task.

### Records and next phase

Historical transcripts were archived **without modifying them** in
[`rename/baseline-records`](/home/ubuntu/aklt/reports/PAL_FIT/rename/baseline-records/verification/README.md) and remain
in Git history at the baseline commit. Their removal from the current source
prevents stale first-party names from surviving in tracked logs/notes and avoids
misrepresenting old receipts as verification of renamed sources. Current records
are in [`verification/rename/README.md`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/rename/README.md) and
[`summary.json`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/rename/summary.json).

The final search covers every tracked text file and path, including scripts,
generators, notes, inventories, API tables, and fresh logs. It reports **zero
unexcluded matches**. The exact search receipt is
[`tracked-search.json`](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/rename/tracked-search.json); the full
matching-line list is in [`tracked-search-final.json`](/home/ubuntu/aklt/reports/PAL_FIT/rename/tracked-search-final.json).

This is ready for regeneration against the committed current names. The pending
builds remain `CertData.H1.Close.Main`, `CertData.H1.Close.Audit`,
`CertData.H3.Close.Main`, `CertData.Close.All`, root Solution, and root Audit.
Regenerate the **7,964 H1 and 5,032 H3** modules, then run the unconditional closing
build and full export/checker pipeline. The ordinary reduction remains available.
Author metadata, LICENSE, and independent fidelity review are unchanged TODOs.
No other rename or collision resolution remains open.

## Earlier ORCH-SUMMARY

- RENAME COMPLETE; package commit d1320320e7cb (verified source e0597c0c7910).
- All 419 listed source spellings updated; 646 compiled declaration names change.
- Seven case-insensitive rules, including catalog and relabeling, are listed above.
- 356 Lean files edited; eight analytic files renamed; no directory rename.
- No declaration, namespace-prefix, local-name, or target-path collision.
- Exact compiled-name image: 18,955 declarations; zero missing or extra.
- Numeric data, Lean string literals, and 851 generator key accesses unchanged.
- All 27 generators reviewed; new emitted Lean/leaf names match the kernels.
- Fresh 1,109-source build, all headers, strict Audit, samples, and ABI probe pass.
- Protected two-input regression accepted by Lean, NanoDa, and con-ron (63,516 declarations).
- Root Challenge byte-identical, 161 lines / 7,736 bytes, no affected identifier.
- Tracked search: zero unexcluded matches; only two exact paper labels remain.
- Old transcripts archived unchanged; current records contain current names only.
- Regeneration can proceed: 7,964 H1 and 5,032 H3 modules, then six closing targets.
- Metadata/LICENSE/review TODOs remain; no rename issue remains open.

## fidelity fix round

Package: `/home/ubuntu/aklt/wt/PAL_FIT/_pkg`. Final package commit: **`61f109327968ca76e99c22c4564de56387df96b5`**. The verified Lean source
commit is `24c9476bce8985f17ac1dea113a283eef3f7d6dc`; later changes add verification records only.
The original main repository and the official verifier checkout remain unchanged.

Both reviews were read in full: [Fable](/home/ubuntu/aklt/reports/FID_FABLE/report.md)
and [Astra](/home/ubuntu/aklt/reports/FID_ASTRA/report.md), each **FAITHFUL WITH REMARKS**,
with no Fatal or Major finding. The fixes preserve all existing mathematical
statements, definitions, and proof bodies. They add proofs of all remaining sanity
propositions and remove the two unneeded Challenge cache resets.

### Protected certificate dependency closure

The requested traversal was computed **before editing**, using the 17 modules in
`verification/regen-interface/H1-imports.tsv` and `H3-imports.tsv` as roots.
It contains **65**, rather than the estimated 35, hand-written modules. Lean's
`--deps-json` header parser independently confirmed every import edge. Each edit
path was checked against this closure; a final Git changed-path check has an
empty intersection, and all 65 SHA-256 hashes remain identical to baseline
`d1320320e7cbf2d216d0afc87be92aabb206d690`.

The complete names, hashes, and shortest import paths are in
[protected-closure.json](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/fidelity-fix/protected-closure.json).
Two material paths are:

- `AKLT.Cert.H1.Production.Semantics → AKLT.Blueprint.Top.Operator → Top.Common → AKLT.Defs.FrameModel → AKLT.Defs.Polynomial → AKLT.Challenge.Main`.
- `CertData.H3.Bridge.Interface → AKLT.Blueprint.Top.ComputationV2 → Top.Computation → Top.Coefficients → Top.Response`.

Thus both Main.lean and Top/Response.lean are protected. Their comments and the
unused old MainStatement remain unchanged under the hard freeze. This is the
reason those requested source edits are documented instead. No certificate
kernel, checker, packed arithmetic, literal consumer, or generator interface
changed. Certificate rebuilding can continue against the identical dependencies.

### Review findings and their disposition

| Review finding | Result |
|---|---|
| Fable Minor 1; Astra Minor 4: paper locations | MainV2 and the regenerated Challenge cite Definition 1.1 (`d:model`, `sec1-result.tex`) for the torus, bonds, determinant, VBS product, and Hamiltonian; Definition 3.1 (`d:poly`, `sec3-quantum-frames.tex`) for the polynomial model and norm; and Theorem 1.2 (`t:main`) for the headline. Revision-plan and FIDELITY.md references are absent from these statement files. Main.lean is frozen, so the generator corrects copied comments only and the notes record the library exception. |
| Fable Minor 2; Astra Minor 1: old MainStatement | Search confirms no Lean caller of the old definition. Deletion or relocation would modify protected Main.lean, so it is deferred under the freeze. Notes explicitly identify its even-only, eventual-kernel, no-nonvanishing differences. Sanity references now select MainStatementV2, and the even-size check is described as auxiliary arithmetic. The independent Challenge omits the obsolete definition. |
| Fable Minor 3: main_iff and copying | Solution and regression doc comments say main_iff is Iff.rfl on its alias, not a comparison of separate environments. The generator has a read-only `--check` mode. Both source verification and the end-to-end runner require exact Challenge and source-record bytes. A one-byte negative test is rejected without rewriting the file. |
| Fable Minor 4: environment modification | Both run_elab cache resets are removed from the release Challenge. No library restructuring was necessary. Lean and NanoDa accept the physical statement comparison without them. The separate conditional regression template retains its naming machinery and is identified as a distinct test surface. |
| Fable Minor 5; Astra Minor 4: spin convention | The generated spinZ doc comment states that e_k has the negative of the paper's displayed monomial weight, preserving the Casimir, projection, and Hamiltonian. The frozen library comment is covered in the reader notes. No spin matrix changes. |
| Fable Minor 6: sanity propositions | BNonzero, BondRank, and FourByFourNondegenerate now all have downstream proofs. The rank attempt completed in 14.65 minutes, within the requested hour. No unproved sanity proposition remains. |
| Fable Minor 7; Astra Minor 2: trails, legacy matchers, and stationary operators | docs/STATEMENT-NOTES.md explains first-hit trails T_n^X (Definition 7.7), unconditional insertion of the outgoing neighbor, the two distinct Rec/Defs V2 matcher names, and exactly which legacy/V2 interfaces use each operator. It records the 1/5-versus-zero center-entry example, center-zero operator agreement, stopped-iterate agreement, and the passing-predicate equivalence with proved bridge names. All affected dependency files are frozen. |
| Fable Minor 7: modified kernel | Top/Response.lean is protected transitively; the notes state the correct term, type-dependent kernel. The source phrase is preserved as required by the freeze. |
| Astra Minor 3: redundant signs | Notes distinguish raw ExchangeSigns from EffectiveExchangeSigns, explain ignored signs on singles and U pairs, and restrict nonredundant decompositions or enumeration to the latter. The relevant source files remain frozen. |
| Fable Minor 8: review bundle limits | The release contains the hand-written proof development and closing modules. The checks below cover what currently builds, plus the physical statement identity and the complete two-input export. Unconditional Solution/Audit replays still await generated certificates; no stronger claim is inferred from the statement-only reviews. |

Reader-facing notes: [STATEMENT-NOTES.md](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/docs/STATEMENT-NOTES.md).
Generation and copying: [make_challenge.py](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/scripts/make_challenge.py),
[source verification](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/scripts/verify_sources.py), and
[the runner](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/scripts/release_verify.py).

### New sanity proofs and proof-body changes

**No existing declaration's proof body changed.** Comment-stripped code for
Main.lean, MainV2.lean, Sanity.lean, Solution.lean, and Regression/Solution.lean
is identical to baseline. Challenge code is identical after removing exactly
its two cache-reset commands. `main_iff`, `h1_iff`, and `h3_iff` retain their
reflexive proofs. Comparator configuration and permitted axioms are unchanged.
See [semantic checks](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/fidelity-fix/semantic-checks.json).

The added files are [BondRank.lean](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/AKLT/Challenge/BondRank.lean) and
[SanityProofs.lean](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/AKLT/Challenge/SanityProofs.lean).
The public convenience theorems have exactly these statements:

```lean
AKLT.Challenge.b_nonzero (L N : Size) : BNonzero L N
AKLT.Challenge.bond_rank (L N : Size) : BondRank L N
AKLT.Challenge.four_by_four_nondegenerate : FourByFourNondegenerate
```

The existing polynomial edge factorization identifies ker P_e with polynomials
of site degrees (3,3,4,…,4). A general coefficient-coordinate linear equivalence
proves that this space has dimension 16·5^(LN−2). Rank-nullity in the actual
normalized physical Hilbert space gives rank 9·5^(LN−2). This handles all
spectator sites and all permitted periods. Nonvanishing reuses the existing
proved AKLT.Uniq.B_ne_zero. The 4×4 result combines those facts with the proved
bond geometry. No finite spectral fact or sanity proposition is assumed.

BondRank.lean adds 14 public helper theorems; SanityProofs exports the three
convenience theorems above. All 17 exact signatures and `#print axioms` outputs
are in [sanity-exports.log](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/fidelity-fix/sanity-exports.log).
Every axiom set is a subset of propext, Classical.choice, and Quot.sound.
An independent exact rational two-site Casimir calculation also proved
multiplicity nine at eigenvalue 20 during the attempt; the shipped proof does
not depend on that calculation. Its valid scratch source and transcript are
retained under `fidelity-fix/RankProbe.lean` and `stages/finite-casimir-rank-proof/`.
Failed intermediate attempts remain outside the package and are not proof evidence.

### Verification and measurements

The release has **1,117 Lean files**, all tracked and all with module headers.
The longest has 1,636 lines. Challenge has **159 lines / 7,973 bytes**, imports
only Mathlib, contains its one conventional placeholder, and has no run_elab.
All current manifest hashes match. No British-spelled identifier was introduced;
only the preserved paper labels l:colour and l:quantumfibre match the spelling scan.

The first fresh build removed 896 artifacts over 61 affected modules. After the
rank proof closed, another 656 artifacts over 46 affected modules were removed
and rebuilt, followed by a forced fresh Challenge build for the last paper-comment
correction. All available targets build, including both regeneration consumers:

```sh
LEAN_NUM_THREADS=12 lake build Handwritten Challenge Regression.Solution Regression.Audit AuditHandwritten RegenSamples.H1Consumer RegenSamples.H3Consumer
lake env lean -j1 -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true AuditHandwritten.lean
python3 scripts/make_challenge.py --check
```

Strict Audit checks **21,899** available constant entries and all **18** explicitly
required exports; all pass the allowed-axiom guard. The full source/configuration
check has only the two preexisting author-owned findings: metadata/provenance TODOs
and the missing selected root LICENSE. There are no mechanical source, header,
line-cap, forbidden-token, generation, or axiom findings.

| Stage | Wall (s) | CPU (s) | Peak tree RSS (GiB) | Outcome |
|---|---:|---:|---:|---|
| Affected sources: fresh objects (first pass) | 247.333 | 488.287 | 26.515 | PASS |
| Completed sanity proofs: fresh affected objects | 125.908 | 346.511 | 18.051 | PASS |
| Final Challenge: fresh objects | 13.459 | 17.583 | 3.769 | PASS |
| Strict hand-written Audit | 6.289 | 6.240 | 4.754 | PASS |
| Explicit Audit transcript guard | 0.205 | 0.105 | 0.012 | PASS |
| All Lean headers | 2.652 | 2.566 | 1.711 | PASS |
| All 17 new theorem signatures and axioms | 5.463 | 5.366 | 4.383 | PASS |
| Physical statement: build-FidelityStatementChallenge | 5.862 | 5.685 | 3.621 | PASS |
| Physical statement: build-FidelityStatementSolution | 4.752 | 4.689 | 3.607 | PASS |
| Physical statement: export-challenge | 15.058 | 14.969 | 6.359 | PASS |
| Physical statement: export-solution | 14.927 | 14.885 | 6.359 | PASS |
| Physical statement: statement-comparator | 60.348 | 73.910 | 0.588 | PASS |
| Negative spin-matrix control | 17.458 | 17.310 | 0.434 | EXPECTED REJECTION |
| Two-input: statement-generation-check | 0.104 | 0.057 | 0.001 | PASS |
| Two-input: source-configuration | 5.437 | 5.320 | 0.066 | AUTHOR TODOs ONLY |
| Two-input: lean-header-parser | 0.206 | 0.121 | 0.091 | PASS |
| Two-input: explicit-targets | 8.996 | 12.531 | 0.941 | PASS |
| Two-input: strict-audit | 5.567 | 5.487 | 4.502 | PASS |
| Two-input: axiom-transcript | 0.104 | 0.048 | 0.000 | PASS |
| Two-input: protected-challenge-build | 7.531 | 7.370 | 3.662 | PASS |
| Two-input: challenge-export | 15.133 | 14.970 | 6.366 | PASS |
| Two-input: solution-export | 60.874 | 60.670 | 7.080 | PASS |
| Two-input: protected-comparator | 1036.709 | 1112.660 | 23.227 | PASS |
| Two-input: conron-replay | 697.830 | 862.920 | 47.190 | PASS |


Every timed stage used affinity CPUs 0–15, enforced by sched_setaffinity and
checked for its descendant processes by measure_stage.py. The final fresh build
used at most seven concurrent Lean processes (12 requested Lake worker threads),
well below 48. Large replay stages used a 150 GB sampled RSS watchdog and a
140 GiB per-process address-space limit. These are recorded local safeguards,
not a Palomar 32 GiB cgroup; the author removed the production resource caps.
RSS is the sampled sum across the process tree and can double-count shared pages.
Dependencies and Mathlib objects were already pinned and cached; no Mathlib source
build or cold cache fetch was repeated. Some independent stages ran concurrently,
so summing their wall times is not a cold end-to-end production measurement.

The physical statement test compares separate reflexive main_iff adapters for
the exact generated Challenge definitions and the library definitions. It uses
no definition exemptions. Both kernels accept; changing only the independent
spinZ constant from 2 to 3 is rejected at AKLT.Challenge.bondCasimir. This
establishes statement identity, not the unavailable unconditional proof.

The protected two-input pipeline compiles its canonical Challenge independently,
then Lean and NanoDa accept the full Regression.Solution export. Verified con-ron
accepts that same export. It has **671,986,654 bytes**
and SHA-256 `ea82aaec07c458ff23d38403de8cc22fc93b488cebc3a99ebe4ed6701d7fab6d`.
The final receipt records the clean verified source commit and all 1,117 source
hashes. The export is also byte-for-byte identical to the previously accepted
two-input export in the rename-phase receipt. A preliminary pipeline was interrupted after the sanity proofs closed;
its receipt is explicitly marked interrupted and is not used as final evidence.
The initial cross-mount object-archive attempt failed before removing objects;
the subsequent explicit deletion and successful fresh builds above provide the
required fresh-object evidence.

Evidence: [summary](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/fidelity-fix/summary.json),
[protected regression receipt](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/fidelity-fix/regression-receipt.json),
[statement comparison](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/fidelity-fix/statement-comparison.log), and
[Audit](/home/ubuntu/aklt/wt/PAL_FIT/_pkg/verification/fidelity-fix/axioms-and-interface.log).
Full per-stage logs and samples remain under `/home/ubuntu/aklt/reports/PAL_FIT/fidelity-fix`.

### Remaining scope

The hard freeze defers deleting or correcting the unused MainStatement and editing
comments in Main.lean and Top/Response.lean. The reader notes provide the requested
corrections without changing certificate dependencies. Generated certificates
are being rebuilt separately. The six dependent modules (`CertData.H1.Close.Main`, `CertData.H1.Close.Audit`,
`CertData.H3.Close.Main`, `CertData.Close.All`, `Solution`, and `Audit`), and the
full unconditional export and independent replays, remain pending that
materialization. Author identities, ORCIDs, provenance, and license metadata are
still author-owned TODOs. There are no remaining unproved sanity propositions.

## ORCH-SUMMARY
STATUS: FIDELITY FIXES COMPLETE.
Package commit: 61f109327968ca76e99c22c4564de56387df96b5.
Verified Lean source commit: 24c9476bce8985f17ac1dea113a283eef3f7d6dc.
Both fidelity reviews read; all Minor findings fixed or documented under the freeze.
Actual certificate dependency closure is 65 modules; all hashes remain unchanged.
Main.lean and Top/Response.lean are frozen transitively; obsolete text is covered in notes.
Challenge: 159 lines, 7,973 bytes, Mathlib only, one placeholder, no cache resets.
Generation is checked byte-for-byte; positive and negative controls pass.
Existing statements, definitions, and theorem proof bodies remain unchanged.
BNonzero, BondRank, and FourByFourNondegenerate are all proved downstream.
Rank proof completed in 14.65 minutes using polynomial coordinates and rank-nullity.
Fresh affected builds, all 1,117 headers, strict Audit, and regeneration consumers pass.
Physical statement identity passes Lean/NanoDa; the altered-spin control is rejected.
Protected two-input Regression.Solution passes Lean, NanoDa, and verified con-ron.
Full unconditional Solution/Audit replays still await generated certificates.
Metadata, provenance, ORCIDs, and LICENSE remain author-owned TODOs.
No subagents, Mathlib builds, main-tree edits, or certificate dependency edits.
Orchestrator: preserve the frozen interface and pass the statement notes to the author.
