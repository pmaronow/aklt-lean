STATUS: PORT PARTIAL (release materialized; port and verification in progress)

The earlier PAL_FIT feasibility study below is historical; the new two-input release work is recorded in the final release package section.

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

ORCH-SUMMARY
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

Release source pin: d77c3ca85754582f91354dd848ac5a830f73727d; unported package first commit: 933e99cddadb1ae6b85d5f4aff551b6f14f91f42. Materialization hashes and exact 618-file inventory: `release/materialization.json`. The legacy tree is unchanged.

Release stage `source-configuration`: wall 1.409 s, CPU 1.340 s, peak tree RSS 0.062 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/stages/source-configuration/result.json`.

Release stage `official-supervisor`: wall 0.203 s, CPU 0.117 s, peak tree RSS 0.032 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/stages/official-supervisor/result.json`.

Release stage `official-bwrap-install`: wall 0.203 s, CPU 0.062 s, peak tree RSS 0.016 GiB, exit 127, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/stages/official-bwrap-install/result.json`.

Release stage `build-default-a1`: wall 666.134 s, CPU 3191.072 s, peak tree RSS 35.136 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/stages/build-default-a1/result.json`.

Release stage `official-bwrap-install-a2`: wall 0.707 s, CPU 0.552 s, peak tree RSS 0.057 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/stages/official-bwrap-install-a2/result.json`.

Release stage `official-bwrap-debug`: wall 0.606 s, CPU 0.538 s, peak tree RSS 0.052 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/stages/official-bwrap-debug/result.json`.

Release stage `official-bwrap-install-a3`: wall 1.010 s, CPU 1.000 s, peak tree RSS 0.064 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/stages/official-bwrap-install-a3/result.json`.

Release stage `official-bwrap-debug-a2`: wall 0.908 s, CPU 0.978 s, peak tree RSS 0.051 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/stages/official-bwrap-debug-a2/result.json`.

Release stage `official-bwrap-install-a4`: wall 0.909 s, CPU 0.982 s, peak tree RSS 0.066 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/stages/official-bwrap-install-a4/result.json`.

Release stage `source-configuration`: wall 1.410 s, CPU 1.345 s, peak tree RSS 0.062 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a1/stages/source-configuration/result.json`.

Release stage `lean-header-parser`: wall 0.103 s, CPU 0.061 s, peak tree RSS 0.001 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a1/stages/lean-header-parser/result.json`.

Release stage `source-configuration`: wall 1.409 s, CPU 1.348 s, peak tree RSS 0.062 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a2/stages/source-configuration/result.json`.

Release stage `lean-header-parser`: wall 0.103 s, CPU 0.061 s, peak tree RSS 0.001 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a2/stages/lean-header-parser/result.json`.

Release stage `explicit-targets`: wall 10.582 s, CPU 10.370 s, peak tree RSS 3.806 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a2/stages/explicit-targets/result.json`.

Release stage `strict-audit`: wall 3.027 s, CPU 2.970 s, peak tree RSS 4.500 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a2/stages/strict-audit/result.json`.

Release stage `axiom-transcript`: wall 0.102 s, CPU 0.026 s, peak tree RSS 0.001 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a2/stages/axiom-transcript/result.json`.

Release stage `protected-challenge-build`: wall 0.102 s, CPU 0.004 s, peak tree RSS 0.001 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a2/stages/protected-challenge-build/result.json`.

Release stage `source-configuration`: wall 1.409 s, CPU 1.343 s, peak tree RSS 0.062 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a3/stages/source-configuration/result.json`.

Release stage `lean-header-parser`: wall 0.103 s, CPU 0.061 s, peak tree RSS 0.000 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a3/stages/lean-header-parser/result.json`.

Release stage `explicit-targets`: wall 7.052 s, CPU 6.191 s, peak tree RSS 0.931 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a3/stages/explicit-targets/result.json`.

Release stage `strict-audit`: wall 3.026 s, CPU 2.961 s, peak tree RSS 4.502 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a3/stages/strict-audit/result.json`.

Release stage `axiom-transcript`: wall 0.102 s, CPU 0.026 s, peak tree RSS 0.001 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a3/stages/axiom-transcript/result.json`.

Release stage `protected-challenge-build`: wall 4.038 s, CPU 0.003 s, peak tree RSS 3.663 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a3/stages/protected-challenge-build/result.json`.

Release stage `challenge-export`: wall 8.676 s, CPU 0.003 s, peak tree RSS 6.366 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a3/stages/challenge-export/result.json`.

Release stage `solution-export`: wall 33.387 s, CPU 0.003 s, peak tree RSS 7.084 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a3/stages/solution-export/result.json`.

Release stage `protected-comparator`: wall 22.793 s, CPU 0.003 s, peak tree RSS 1.143 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a3/stages/protected-comparator/result.json`.

Release stage `source-configuration`: wall 1.409 s, CPU 1.337 s, peak tree RSS 0.062 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a4/stages/source-configuration/result.json`.

Release stage `lean-header-parser`: wall 0.103 s, CPU 0.061 s, peak tree RSS 0.001 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a4/stages/lean-header-parser/result.json`.

Release stage `explicit-targets`: wall 10.272 s, CPU 10.153 s, peak tree RSS 3.783 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a4/stages/explicit-targets/result.json`.

Release stage `source-configuration`: wall 1.409 s, CPU 1.350 s, peak tree RSS 0.062 GiB, exit 1, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a5/stages/source-configuration/result.json`.

Release stage `lean-header-parser`: wall 0.102 s, CPU 0.059 s, peak tree RSS 0.001 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a5/stages/lean-header-parser/result.json`.

Release stage `explicit-targets`: wall 10.478 s, CPU 10.275 s, peak tree RSS 3.804 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a5/stages/explicit-targets/result.json`.

Release stage `strict-audit`: wall 2.925 s, CPU 2.844 s, peak tree RSS 4.501 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a5/stages/strict-audit/result.json`.

Release stage `axiom-transcript`: wall 0.102 s, CPU 0.026 s, peak tree RSS 0.001 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a5/stages/axiom-transcript/result.json`.

Release stage `protected-challenge-build`: wall 3.935 s, CPU 0.003 s, peak tree RSS 3.663 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a5/stages/protected-challenge-build/result.json`.

Release stage `challenge-export`: wall 8.574 s, CPU 0.003 s, peak tree RSS 6.366 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a5/stages/challenge-export/result.json`.

Release stage `solution-export`: wall 32.975 s, CPU 0.003 s, peak tree RSS 7.084 GiB, exit 0, limit None. Receipt: `/home/ubuntu/aklt/reports/PAL_FIT/release/verify-a5/stages/solution-export/result.json`.
