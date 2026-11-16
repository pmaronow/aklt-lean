STATUS: NOT READY (2 blocking)

Re-audited the installed `tools/v2`, dispatch wrappers, legacy `aklt-gate`, PORT1 specification, builder report and GUIDE on 2026-11-16. Four of the six prior findings are fixed; two have reproducible bypasses. The revised queue budget is sound on the tested inputs, but the retained manual gate still opens incorrectly. Integration still loses some uncommitted MERGE edits. One additional Major finding prevents full validation of otherwise accepted private or Unicode-named declarations. No production fixes were applied.

| V-ORCH-1 finding | Fixed? | Test and evidence |
| --- | --- | --- |
| Blocking 1: quota freshness exceeds 15 minutes | **Yes** | `QuotaAudit.test_refuse_readings_older_than_fifteen_minutes`; `Regression.test_fifteen_minutes_future_and_configuration_bound`; `BudgetBypasses.test_acquired_snapshot_ages_during_tick`. Both defaults and installed configuration enforce ≤900 s; the synthetic 900 s boundary accepts, 901 s/future/nonfinite ages reject, relaxation to 901/1800/bool rejects, and an acquired snapshot expires as time passes. [Boundary results](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/fifteen-minute-limit.json). |
| Blocking 2: quoted resource-option names bypass bounds | **Yes** | Original quoted unlimited-heartbeat/recursion task is rejected. `Regression.test_quoted_options_same_bounds_and_exact_certificate_exemption` compiles and integrates bounded quoted options. `OptionBypasses.test_quoted_local_nested_and_malformed_options` rejects local `in`, multiline and comment-separated zero settings and malformed syntax. Exact certificate identity, 4-hour timeout and effect rejection still pass. [Rejected task](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/quoted-options.json). |
| Blocking 3: integration deletes dirty MERGE edits | **Partial; still Blocking** | Original tracked edit + untracked note test passes; staged and ignored Lean edits also hold. Journal recovery preserves exact archive bytes and refuses unrelated notes. However, `RepoBypasses.test_ignored_nonlean_merge_edit_is_preserved` fails: an ignored operator note is overwritten and `validated` advances. [Byte-level evidence](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/ignored-merge-loss.json). |
| Blocking 4: retry permits timeout kills and foreign roots | **Yes, supported v2 entry points** | Obsolete `--driver` and unsafe flags are rejected before delegation. Direct bound-task and stored-resume-metadata overrides reject. Positive mocked delegation for both Luna/xhigh and Sol/max, including resumes, uses original effort, registered cwd/report roots, workspace-write and `communicate(timeout=None)`; no kill call. Transient retry retains the same session. [Original unsafe input rejection](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/retry-unsafe-flags.json); tests in [test_v2.py](/home/ubuntu/aklt/scratch/V-ORCH-2/tests/test_v2.py:133) and [test_bypasses.py](/home/ubuntu/aklt/scratch/V-ORCH-2/tests/test_bypasses.py:183). |
| Blocking 5: unsafe alternative manual launch gate | **Partial; still Blocking** | Original stale/secondary-exhaustion cases now reject. New `aklt-budget` and `aklt-budget-check` share the corrected policy. Retained executable `aklt-gate` fails six added cases: future readings, spend-control hold, missing newest limits, reset hold, manual pause, and newest event outside its 60-file mtime selection. [Gate comparison tests](/home/ubuntu/aklt/scratch/V-ORCH-2/tests/test_bypasses.py:43), [public v2 command matrix](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/public-budget-entrypoints.json). |
| Major 1: missing reset-triggered launch pause | **Yes in the shared v2 budget** | Original reset test passes. Added cases accept a rise of exactly 5 points, latch on >5, preserve the latch across restart/deleted marker files, and require explicit acknowledgement. Acknowledgement preserves manual PAUSE and baseline bytes. Legacy gate divergence is included in Blocking 5. [Reset evidence](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/guide-reset.json), [threshold test](/home/ubuntu/aklt/scratch/V-ORCH-2/tests/test_bypasses.py:106). |

**Blocking — Git-ignored MERGE files can still be destroyed (remaining V-ORCH-1 Blocking 3).**

Locations: [aklt_common.py:210](/home/ubuntu/aklt/tools/v2/aklt_common.py:210), especially the `.lean`-only ignored-file filter at line 215; [aklt_integrate.py:21](/home/ubuntu/aklt/tools/v2/aklt_integrate.py:21), [aklt_integrate.py:155](/home/ubuntu/aklt/tools/v2/aklt_integrate.py:155).

`clean_head` excludes ignored untracked files from Git status, then checks ignored files only when their names end in `.lean`. In a disposable clone, the shared local exclude list ignores `AKLT/W/IGNORED/operator-note.txt`. MERGE contains uncommitted operator bytes at that path. A finished writer has a different, explicitly staged file at the same allowed path, plus a harmless theorem. All admission gates accept; Git merge overwrites the ignored file. Integration returns normally, the task is `integrated`, and `validated` moves. The operator bytes `operator uncommitted notes\x00\xff\n` become `writer replacement\n`, without a recovery backup. The existing journal does not prevent this because MERGE was incorrectly classified as clean.

Test: `PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=tests python3 -B -m unittest test_bypasses.RepoBypasses.test_ignored_nonlean_merge_edit_is_preserved -v`. The failing assertion and exact before/after hex bytes are retained in [complete-suite.log](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/complete-suite.log) and [ignored-merge-loss.json](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/ignored-merge-loss.json).

Fix: refuse ignored uncommitted files that integration/reset could replace, regardless of extension. Exempt only explicitly tool-owned build/cache locations; enumerate ignored source-tree files before any reset or merge. Preserve or back up unexpected files before mutation. Keep this regression alongside the tracked, staged, untracked and ignored-Lean cases. No `git clean` is needed to trigger the loss.

**Blocking — The installed alternative gate still violates the launch policy (remaining V-ORCH-1 Blocking 5).**

Locations: [aklt-gate:9](/home/ubuntu/aklt/bin/aklt-gate:9), [aklt-gate:15](/home/ubuntu/aklt/bin/aklt-gate:15), [aklt-gate:23](/home/ubuntu/aklt/bin/aklt-gate:23), [aklt-gate:28](/home/ubuntu/aklt/bin/aklt-gate:28), [aklt-gate:38](/home/ubuntu/aklt/bin/aklt-gate:38).

The current legacy gate has fixed the prior 900-second, secondary-window and Decimal credit examples, but remains a separate implementation. Six new tests observe exit **0 / GATE: OPEN** when the same fixture makes installed `aklt-budget-check` exit nonzero:

| Input that must hold | Legacy defect | Evidence |
| --- | --- | --- |
| Event timestamp 120 seconds in the future | Only `age > 900` is checked | [legacy-future.json](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/legacy-future.json) |
| Fresh event with `spend_control_reached=true` | Checks only `rate_limit_reached_type` | [legacy-spend-control.json](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/legacy-spend-control.json) |
| Newest token_count has `rate_limits=null`; preceding event is open | Skips the newest event and uses older limits | [legacy-missing-latest.json](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/legacy-missing-latest.json) |
| Observed allowance reset from 20% to 100% | Ignores persisted reset latch | [legacy-reset.json](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/legacy-reset.json) |
| Manual launch PAUSE | Does not consult campaign pause state | [legacy-manual-pause.json](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/legacy-manual-pause.json) |
| Newest event shows 0% remaining, but its file has the oldest mtime among 61 files | Discards it before comparing event timestamps | [legacy-file-cap.json](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/legacy-file-cap.json) |

Tests: the six `BudgetBypasses.test_legacy_*` methods in [test_bypasses.py](/home/ubuntu/aklt/scratch/V-ORCH-2/tests/test_bypasses.py:43). Only legacy discovery and process enumeration are intercepted; its installed source runs unchanged through `runpy`. The new CLI runs as a real subprocess against each disposable campaign. No model is called.

Fix: retire `aklt-gate` or delegate it directly to `aklt-budget-check N`, preserving exit status and prospective reserve. Remove its independent timestamp/file selection and policy logic. Documentation directing operators to the replacement does not close an executable launch gate that still reports OPEN. This is one policy-divergence finding, not six separate blockers.

**Major — Full validation cannot export ordinary private or Unicode declarations.**

Locations: [aklt_validate.py:268](/home/ubuntu/aklt/tools/v2/aklt_validate.py:268), [aklt_common.py:42](/home/ubuntu/aklt/tools/v2/aklt_common.py:42), reached by [aklt_validate.py:313](/home/ubuntu/aklt/tools/v2/aklt_validate.py:313).

Both valid writer modules compile, pass axiom audit and integrate, then full validation fails before export:

```lean
namespace AKLT.W.PRIVATE
private theorem helper : True := True.intro
theorem public_result : True := helper
end AKLT.W.PRIVATE
```

The inventoried private name is `_private.AKLT.W.PRIVATE.Work.0.AKLT.W.PRIVATE.helper`. `chunks` passes it through the source-identifier regex, which forbids numeric components. A separate module declaring `theorem ε_lemma : True := True.intro` fails through the same regex's ASCII restriction. Neither source violates the stated writer policy. The README's ASCII metadata limitation does not make Lean-generated private names usable at milestones. This is a reproducible full-validation availability defect; it does not publish a false verification receipt.

Tests: `RepoBypasses.test_full_validation_accepts_private_theorem` and `test_full_validation_accepts_unicode_declaration`. Both fail, after successful integration. [Private evidence](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/private-full-validation.json), [Unicode evidence](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/unicode-full-validation.json).

Fix: handle inventoried Lean names with an exporter-compatible representation, including private numeric components, quoted components and Unicode. Keep strict source-identifier validation for operator metadata where appropriate, but do not apply that grammar to every kernel declaration name. Add real export/con-ron/nanoda regression cases for these modules.

No separate Minor findings.

**Commands, retained suites and results.**

All commands run from `/home/ubuntu/aklt/scratch/V-ORCH-2`, using installed v2 modules. Test roots contain disposable shared clones; production implementation modules were not copied or patched. Tests and evidence are under this audit directory.

```sh
# A: retained/adapted 43 cases, 11 builder v2 regressions, 15 new adversarial cases
PYTHONDONTWRITEBYTECODE=1 python3 -B -u run_suite.py tests evidence \
  > evidence/complete-suite.log 2>&1

# B: original V-ORCH-1 assertions, with only tools/v1 imports changed to tools/v2
PYTHONDONTWRITEBYTECODE=1 python3 -B -u run_suite.py original/tests original/evidence \
  > original/evidence/replay.log 2>&1

# C: additional real public-command matrix, added after A had discovered its tests
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=tests:supplemental python3 -B -u -m unittest test_extra -v \
  > evidence/extra.log 2>&1

# D: immutable install/repository checks, static review and disposable-build cleanup
PYTHONDONTWRITEBYTECODE=1 python3 -B verify_audit.py > evidence/verification.log 2>&1
```

A: **69 tests, 60 passed, 9 failed, 0 errors/skips**, 262.612 s, exit 1. All **54/54** retained/adapted auditor and builder regressions pass. The nine failures are exactly the six legacy-gate bypasses, ignored-MERGE data loss, and two export-name cases. [Complete log](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/complete-suite.log), [structured result](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/suite-result.json).

B: **43 tests, 39 passed, 2 failed, 2 errored, 0 skipped**, 206.308 s, exit 1. [Original-assertion log](/home/ubuntu/aklt/scratch/V-ORCH-2/original/evidence/replay.log), [provenance](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/raw-replay-provenance.json).

C: **1 passed**, exercising both installed public budget commands across nine real event fixtures. Together A+C cover **70 distinct cases: 61 pass, 9 fail**. The supplemental file now lives outside `tests/`, so rerunning A retains its 69-case inventory. [Supplemental log](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/extra.log).

D: **passed**, exit 0. [Verification log](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/verification.log).

The adapted suite retains all original cases. Four assertions/seams require v2 adaptation: reject obsolete unsafe driver invocation before Popen; replace the removed subprocess retry seam with a bound-driver mock and an actual reservation; expect 20 help entry points instead of 19; acknowledge the new reset latch explicitly before expecting reopening. [Exact original-to-adapted diff](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/suite-adaptations.diff). B independently preserves the original assertions and records their two failures/two interface errors; none are skipped or silently counted as passing. An initial harness run lacked `test-runs` before the auditor cases; that invalid attempt is retained in `evidence/bootstrap-replay.log`, and B is the corrected full replay.

The following checklist entries passed. The two blocking bypasses and Major export-name limitation above qualify their corresponding general guarantees.

| Checklist item | Command / test evidence | Observed behavior |
| --- | --- | --- |
| Forbidden tokens/effects and lexical correctness | A: `PureGates.test_lexical_forbidden_and_effect_gates` | Accepts harmless source and forbidden text in nested comments/strings/raw strings; rejects specified primitives, executable/metaprogram commands, IO/FS/process access, interpolants and malformed lexical input. |
| Resource options and exact certificate exemption | A: `PureGates.test_resource_options_certificate_exemption`, both quoted-option tests, `AuditRepo.test_certificate_allow_list_is_exact_and_keeps_effect_guard` | Accepts bounded ordinary/quoted settings; rejects zero/excessive/nonliteral/malformed settings outside the exact allow-list. Exact certificate path/dotted name accepts; near-match denies; 14,400-second timeout is selected; effects remain denied. |
| Frozen hashes, clean HEAD and writer ownership | A: `RepoGates.test_frozen_hashes_dirty_head_and_scope`, `AuditRepo.test_writer_edits_deletions_foreign_stage_and_modes` | Own additions accept; frozen edits/unlisted Defs, foreign staging/additions, edits/deletions, source symlinks and executable modes reject. Dirty validation checkouts reject. |
| Certificate cache integrity | A: both `RepoGates.test_certificate_*` methods | Real content-keyed restoration across distinct worktrees; changed sources invalidate key; corrupted cache refuses restoration. |
| Exact type, theorem kind and axioms | A: `RepoGates.test_exact_type_good_wrong_conditional_and_axioms`, infrastructure-deferral test | Correct theorem and explicitly declared arrow dependencies accept; wrong target, undeclared dependencies and disallowed axioms reject. Node/dependency registration is checked. Infrastructure failure defers instead of escalating. |
| Ladder, one owner, first report line | A: three ladder outcome/inheritance tests; `PureGates.test_report_only_exact_first_line`; capacity/reservation tests | Luna/xhigh → Sol/max → EXHAUSTED; no third/repeated attempt, no overlapping leaf ownership. Sol inherits compiled Luna work or exact inert archive plus first-line verdict. Exact proof despite PARTIAL stops escalation; claimed PROVED without theorem does not. Body text has no authority. |
| Resume effort, retry boundaries, no agent kills | A: original-effort test; three retry/driver regressions; `RepoBypasses.test_both_driver_models_pin_resume_effort_and_roots`; D static review | Explicit original effort on constructed and transient resumes for the same session; absent/mismatched/duplicate effort and timeout/full-access/foreign-root/metadata overrides reject. Positive mocks for both models confirm no timeout/kill. Queue agent call has no timeout; validation signals target its newly created child process group. |
| Shared budget and public command decisions | A: quota/launch/budget tests; C public-command matrix | Newest token_count timestamp wins over mtime. Both windows, exact Decimal credit decrease, 900-second freshness, future/nonfinite age, missing newest limits, zero allowance, credit/spend flags and absent baseline hold. `aklt-budget` and `aklt-budget-check` both accept 2% remaining, preserving the author's zero floor rather than GUIDE's older 3% stop. |
| Prospective reserve and snapshot ageing | A: `Regression.test_budget_new_count_and_external_deduplication`, queue/CLI reserve test, acquired-snapshot test | Strict `remaining − 0.3×(running+N) − 1 > 0`; N=0/1/4, 1.3% strict boundary, external/registered dedup and total cap tested. Queue, status and budget-check use N=1. Expired acquired snapshots block launch calls. |
| Reset/restart/acknowledgement policy | A: original reset case; both persistent-reset regressions | >5-point rise latches JSON + queue/wrap-up markers. Deleted markers/restart cannot reopen; explicit acknowledgement preserves baseline/manual pause. Running tasks are not killed. |
| Concurrency and durable launch reservations | A: cap and reservation tests | Accept below/reject at 48 Lean-writing, 24 Sol and 56 total; leaf overlap blocks. Reservation persists before mocked tmux call. Uncertain launch stays orphaned and is not repeated. |
| Preserve main and ordinary MERGE edits; recovery | A: dirty-main integration, dirty-MERGE tests, staged/ignored-Lean test, explicit recovery regression | Detached MERGE leaves main edits untouched. Tracked/staged/untracked/ignored-Lean MERGE edits refuse. Interrupted archive recovery saves exact bytes, patches and receipt and refuses unrelated edits. Ignored non-Lean collision remains the Blocking exception. |
| Validation precedes `validated` publication | A: integration, failed-validation and publication-journal tests | Full aggregate `lake build AKLT` and fast validation precede ref update. Injected unavailable validation preserves old `validated` and retryable finished task. Publication journal settles ref-update crashes. |
| Timeout attribution and batch removal | A: runtime timeout, per-task archive, duplicate collision and iterated culprit/fallback tests | Private Lean timeout attributes `CLOCK`; injected integration timeout rejects/archives the owner. Culprit removal iterates, unknown blame falls back to singles, real duplicate declarations keep a valid survivor. Only disposable validation children are terminated. |
| Full export and independent checkers | A: `RepoGates.test_composition_generator_and_full_independent_validation`, `AuditRepo.test_export_and_each_checker_failure_is_loud` | Real leanexport → con-ron `--verified --jobs=1` → nanoda passes on the tiny full fixture. Exporter/con-ron/nanoda failures and missing verified acceptance are loud, without success manifest. Private/Unicode acceptance fails as the Major above. |
| ARG_MAX and semantic composition | A: byte/environment chunking, fixed-point, composition/full tests | Oversized argv rejected; cyclic rules without bases do not close; theorem heads/named-Prop dependencies close by fixed point; generated explicit final term compiles and passes axiom audit. |
| Pipefail / failure propagation | A: stage-failure matrix; D AST/static review | No tool-owned shell pipelines or `shell=True`: checked argv subprocesses run sequentially. No pipeline requires adding pipefail. Failure of an earlier stage cannot be masked by a later successful stage. |
| Status, digest, CLI and sandbox | A: installed CLI/digest tests, status/digest test, real read-only-controller bwrap regression | All 20 dispatcher entry points accept help; source rejection exits nonzero. Status/digest display queue/model/effort/key/ladder/integrator/validated/disk/memory/quota/credits/stale and exhausted/unladdered state. Digest writes its log and mocked loop sleeps 600 s. Digest-start tmux call is mocked. Real Lean works with only writer/report roots writable. |
| Cleaner, disk and campaign isolation | A: cleaner/config/disk tests; D resource/immutability checks | Cleaner deletes only finished private builds; preserves main, active, MERGE*/VENDOR*/PROBE*, symlinks and foreign worktrees. Fixed caps/disk floors reject relaxation; low disk aborts. Audit writes remain inside the authorized directories; foreign driver cases are mocked/rejected. |

**Install integrity and resource record.**

All **138** pre-audit installed/repository file or symlink records match after testing, including Git metadata, tracked/untracked main source/config files, wrappers and v2 modules. All **13** historical v1 files (including existing bytecode), the original credit baseline, frozen manifest and task ledger match the pre-v2 builder snapshot. Both installation receipts match installed source hashes. Main remains clean at original install commit `6ef9d9c2d9587a4522a2e942cc98ef58dcfe0921`; all 16 existing main build files predate v2 installation. Frozen file contents match the manifest. Shared package-cache contents were not recursively hashed or edited. [Integrity record](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/immutability.json), [static review](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/static-review.json).

Real full validation requested **8** names, exported **7,284 bytes**, and con-ron accepted **11 declarations with --verified**. NanoDa checked **16 declarations with no typechecker errors**, with one pretty-printer diagnostic, “Unable to print axioms.” [Export manifest](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/independent-export-manifest.json), [con-ron](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/independent-con-ron-0.log), [nanoda](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/independent-nanoda-0.log).

Cleanup verifies **245** package symlinks resolve to the prescribed shared cache and **zero private `.lake/build` directories remain**. Scratch use is approximately **145.9 MB**, below 10 GB; `/` has approximately **190.5 GB** free. Each of the two overlapping foreground suites observed at most one Lean process, so at most two audit Lean processes could overlap, below the limit of four. [Resources](/home/ubuntu/aklt/scratch/V-ORCH-2/evidence/final-resources.json).

The real checker fixture exercises tiny declarations and generated final terms; it is not a production-certificate corpus run or a four-hour computation. There were no live agent/model tests. No sub-agent, daemon, agent or tmux session was started. No reset was acknowledged in live campaign state, no credits baseline was rebased, and no foreign campaign was modified.
