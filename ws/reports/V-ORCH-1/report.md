STATUS: NOT READY (5 blocking)

Audited the installed `/home/ubuntu/aklt/tools/v1/` implementation, its `aklt-*` entry points, installed configuration, PORT1 specification, builder report/tests, and GUIDE. The 28 builder tests pass against the **installed** modules. Fifteen independent audit tests give **9 passes and 6 failures**, exposing five blocking findings and one additional Major guide-policy gap. No production fix was applied.

**Blocking 1 — Quota readings between 15 and 30 minutes old permit launches.**

Location: [aklt_common.py:18](/home/ubuntu/aklt/tools/v1/aklt_common.py:18), [config.json:16](/home/ubuntu/aklt/state/config.json:16), enforced by [aklt_queue.py:75](/home/ubuntu/aklt/tools/v1/aklt_queue.py:75).

Both the default and installed freshness limit are **1800 seconds**, exceeding the requested 900 seconds. `QuotaAudit.test_refuse_readings_older_than_fifteen_minutes` supplies a reading aged 901 seconds with sufficient allowance and unchanged-or-higher credits; both configurations return `allowed: true`. The 900-second accepting boundary also passes. [Evidence](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/fifteen-minute-limit.json).

Fix: change both defaults and installed configuration to 900 seconds, and disallow configuration values above 900 so this invariant cannot be weakened. Retain refusal of missing readings, future readings, depleted quota, and credit decreases.

**Blocking 2 — Quoted option identifiers bypass the certificate allow-list.**

Location: [aklt_guard.py:83](/home/ubuntu/aklt/tools/v1/aklt_guard.py:83).

The resource-option regex recognizes only unquoted names. `AuditRepo.test_quoted_resource_option_names_require_allow_list` delivers this valid Lean source in an ordinary writer module, with no certificate allow-list entry:

```lean
set_option «maxHeartbeats» 0
set_option «maxRecDepth» 10001
theorem escaped_options : True := True.intro
```

The real pinned compiler accepts it, integration reports `state: integrated`, and `validated` advances. Thus neither the unlimited-heartbeat rejection nor the recursion bound is enforced for this spelling. [Integration receipt](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/quoted-options.json).

Fix: tokenize and canonicalize Lean option identifiers, including quoted components, before checking values. Reject unrecognized option syntax conservatively. Apply exactly the same resource bounds after normalization, with exemptions confined to the exact certificate-module allow-list. Add accepting bounded-quoted and rejecting unbounded-quoted regression cases.

**Blocking 3 — Integration silently deletes uncommitted MERGE edits.**

Location: [aklt_integrate.py:12](/home/ubuntu/aklt/tools/v1/aklt_integrate.py:12), [aklt_integrate.py:22](/home/ubuntu/aklt/tools/v1/aklt_integrate.py:22).

`merge_worktree` verifies repository membership and detached HEAD but never requires a clean checkout. `reset` then runs `git reset --hard` and `git clean -fd -- AKLT`. In `AuditRepo.test_integrator_refuses_dirty_merge_checkout`, an uncommitted tracked edit and an untracked note in MERGE both disappear; integration raises no error and advances `validated`. The separate builder test correctly confirms that dirty **main** edits survive; it does not cover dirty MERGE. [Evidence](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/dirty-merge.json).

Fix: require a clean existing MERGE checkout before integration changes it. Refuse and preserve unexpected edits. Handle any tool-owned interrupted merge through explicit journal recovery, without silently treating arbitrary dirty files as disposable. Test that refusal leaves both edits and `validated` unchanged.

**Blocking 4 — Retry entry points expose agent-kill and foreign-write flags.**

Location: [aklt_retry.py:34](/home/ubuntu/aklt/tools/v1/aklt_retry.py:34), [aklt_retry.py:64](/home/ubuntu/aklt/tools/v1/aklt_retry.py:64), [aklt_retry.py:70](/home/ubuntu/aklt/tools/v1/aklt_retry.py:70). The delegated implementation kills on timeout at [codex_sol.py:129](/home/ubuntu/bin/codex_sol.py:129).

A matching running reservation verifies model/effort, but arbitrary driver arguments and the parsed task's timeout, working directory, sandbox, and writable roots are not bound to that reservation. `DriverAudit.test_retry_rejects_agent_kill_timeout_and_foreign_full_access` supplies `--timeout 1 --cd /home/ubuntu/dbl --full-access` at the delegation boundary. A **mocked** agent process receives `cwd=/home/ubuntu/dbl` and `sandbox_mode="danger-full-access"`; its mocked timeout invokes `proc.kill()`. [Captured command and kill observation](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/retry-unsafe-flags.json).

The normal queue-generated command omits these flags. This finding concerns the callable retry interface, including its internal `--driver` route, under an existing running reservation. No real agent was created or killed, and no foreign directory was modified.

Fix: construct the driver task from registered state and validate it immediately before delegation. Force the registered worktree/report roots, workspace-write sandbox, original effort/model, and `timeout=None`; reject timeout/full-access/foreign-path overrides, including overrides recovered from resume metadata. Keep the same-session retry behavior and explicit effort.

**Blocking 5 — The still-installed legacy `aklt-gate` can approve credit-only or stale launches.**

Location: [aklt-gate:8](/home/ubuntu/aklt/bin/aklt-gate:8), [aklt-gate:20](/home/ubuntu/aklt/bin/aklt-gate:20), [aklt-gate:29](/home/ubuntu/aklt/bin/aklt-gate:29).

This pre-existing executable remains beside the new wrappers. It has no age check, considers only the primary window, searches a hard-coded November 2026 directory and only the 30 newest files by mtime, and tolerates a small credit decrease through floating-point comparison. It does not share the new budget implementation.

`QuotaAudit.test_legacy_gate_refuses_stale_and_exhausted_secondary` intercepts log discovery and process enumeration and observes **exit 0 / GATE: OPEN** for both a one-day-old reading and a fresh reading with primary allowance available but secondary allowance exhausted. [Evidence](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/legacy-gate.json). The new queue itself uses `aklt_queue.budget`; this is an unsafe alternative manual launch gate, not an alternate path inside that queue.

Fix: retire this executable or make it delegate to the single corrected budget implementation, preserving any requested-new-agent reserve conservatively. Remove the hard-coded date/file cap, primary-only decision, and credit tolerance. Test all advertised budget entry points with the same fixtures.

**Major 1 — The GUIDE's reset-triggered launch pause is absent.**

Location: [aklt_queue.py:67](/home/ubuntu/aklt/tools/v1/aklt_queue.py:67); policy at [GUIDE.md:230](/home/ubuntu/aklt/briefs/GUIDE.md:230).

`QuotaAudit.test_guide_quota_reset_pauses_new_launches` observes allowance rising from 20% to 100%. The next budget result is immediately open, with no pause latch. [Evidence](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/guide-reset.json). The implementation tracks the newest event but has no reset/minimum-allowance state. GUIDE calls for wrap-up and queue pause on a rise greater than five points. PORT1 specifies the fixed author formula without restating reset behavior; this is a guide-policy gap, separate from the five explicit blocking invariants above.

Fix: persist reset detection and latch a launch pause on an observed reset, without killing running agents or rebasing credits. Alternatively, record an explicit author replacement for that GUIDE policy before unattended operation. The current author's floor-zero rule governs exhaustion; this finding does not propose GUIDE's older 3% exhaustion stop.

No separate Minor findings are reported.

**Commands and checks that passed**

All commands below ran from `/home/ubuntu/aklt/scratch/V-ORCH-1`. Tests are retained in [test_port1.py](/home/ubuntu/aklt/scratch/V-ORCH-1/tests/test_port1.py) and [test_audit.py](/home/ubuntu/aklt/scratch/V-ORCH-1/tests/test_audit.py). The builder suite was copied into this audit area and its import path changed to the installed modules; production sources were not copied or patched for testing.

Command A:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B -u -m unittest discover -s tests -p test_port1.py -v > evidence/builder-suite.log 2>&1
```

**28/28 passed, 198.827 seconds.** [Log](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/builder-suite.log).

Command B:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=tests python3 -B -u -m unittest test_audit -v > evidence/audit-final.log 2>&1
```

**15 tests, 9 passed and 6 failed, 22.696 seconds, exit 1.** The failures correspond to the six findings above. The nonzero result is preserved. [Log](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/audit-final.log).

The following are the successful checks within those commands; test selectors identify their evidence in the logs.

| Check | Command / test evidence | Passing behavior |
| --- | --- | --- |
| Forbidden tokens and effect guard | A: `PureGates.test_lexical_forbidden_and_effect_gates` | Accepts harmless Lean and forbidden words inside nested comments/strings/raw strings; rejects every specified forbidden primitive, skipKernelTC, tactic macros, executable commands, IO/FS/process access, interpolation and malformed lexical input. |
| Ordinary resource bounds | A: `PureGates.test_resource_options_certificate_exemption` | Accepts literal bounds of 1,000,000 heartbeats and 10,000 recursion depth; rejects unquoted zero/excessive heartbeats, excessive recursion and nonliteral values. Quoted-name hole is Blocking 2. |
| Certificate identity, timeout and cache | A: both certificate-cache tests; B: `AuditRepo.test_certificate_allow_list_is_exact_and_keeps_effect_guard` | Exact path/dotted-name allow-list; near-matching module denied; listed module receives 14,400-second build timeout; effects still denied. Real cache restoration works across distinct worktrees; source changes invalidate the key; corruption stops restoration. |
| Frozen hashes and writer ownership | A: `RepoGates.test_frozen_hashes_dirty_head_and_scope`; B: `AuditRepo.test_writer_edits_deletions_foreign_stage_and_modes` | Own additions accepted. Frozen changes/unlisted Defs, foreign additions/staging, edits/deletions, executable files and source symlinks rejected. Dirty validation checkout rejected. |
| Exact type and independent axiom audit | A: `RepoGates.test_exact_type_good_wrong_conditional_and_axioms` and infrastructure-failure test | Correct theorem accepted; wrong target rejected; dependencies accepted only at the explicit arrow type. A deliberately source-scan-bypassed bad axiom is rejected by the axiom audit and exact check. Invalid node/dependency registrations fail. Infrastructure failure defers a verdict. |
| Ladder and first report line | A: three ladder outcome/inheritance tests and `PureGates.test_report_only_exact_first_line` | Luna/xhigh → Sol/max → EXHAUSTED, with no repeated tier or third attempt. Repeated ticks do not duplicate tasks. Sol inherits Luna's validated source or byte-exact inert archive and receives its first-line verdict. A real proof despite PARTIAL stops escalation; a PROVED report without the exact theorem does not stop escalation. Body prose has no authority. |
| Explicit resume effort | A: launch-reservation and retry tests | Both constructed resumes and transient-error retry resumes carry original `-e`; absent/mismatched effort rejected. Driver/model/session paths remain campaign-local for standard calls. Unsafe override gap is Blocking 4. |
| Quota calculation and holds | A: newest-event/strict-budget, launch-budget and cap tests; B: quota-window/reset/credit test and `AuditRepo.test_budget_holds_prevent_launch_calls` | Newest event timestamp wins over file mtime; primary/secondary minimum used; exact `remaining − 0.3×active − 1 > 0` boundary enforced. Missing newest rate_limits, absent readings, credit-only flags, zero allowance, credit decrease below install baseline and very stale readings hold; launch mocks are not called. A past reset timestamp alone does not mint allowance. Freshness gap is Blocking 1; reset-pause gap is Major 1. |
| Concurrency and durable reservations | A: caps and launch-reservation tests | 48 Lean-writing / 24 Sol / 56 total caps accept below and reject at limits. Leaf ownership blocks overlap. Reservations persist before mocked tmux launch; uncertain starts remain counted as orphaned and are not repeated. |
| Timeout attribution and culprit removal | A: timeout, iterated-culprit/fallback and duplicate-declaration tests; B: `AuditRepo.test_runtime_timeout_attribution` | Real private Lean timeout returns `kind=timeout`, owner `CLOCK`; integration timeout rejection/archive is tested separately by injection. Iterated removal preserves survivors; unknown blame falls back to singles. Real duplicate declaration collision keeps one valid task. |
| Validate before publishing | A: integration and publication-journal tests; B: `AuditRepo.test_failed_validation_never_moves_validated` | Uses detached MERGE, preserves dirty main, and settles publication journals. Injected unavailable validation leaves `validated` unchanged and task retryable. Dirty MERGE protection fails as Blocking 3. |
| Full validation and failure propagation | A: `RepoGates.test_composition_generator_and_full_independent_validation`; B: `AuditRepo.test_export_and_each_checker_failure_is_loud` | Real export → con-ron `--verified --jobs=1` → nanoda succeeds on the same tiny fixture export. Injected failure of each stage, and con-ron exit zero without verified acceptance, raises an error without a success manifest. |
| ARG_MAX and composition | A: chunking/fixed-point tests and composition/full-validation test | Byte/environment-aware export chunking; oversized arguments rejected. Cycles do not close without a base. Named-Prop theorem heads close through a fixed point; generated explicit final proof compiles and passes axiom audit. |
| Status, digest and wrappers | A: status/digest test; B: installed-CLI and digest-loop tests | Real installed status/digest show queue, model/effort/key, ladder, integrator, validated commit, disk/memory, quota/credits and exhausted leaves; fixture tests cover stale flags, missing semantic inventory and disk alarm. All 19 installed dispatch entry points accept `--help`. Digest writes its log; mocked loop waits exactly 600 seconds; mocked start constructs the tmux command. Forbidden-source CLI exits 1. |
| Cleaner and disk limits | A: cleaner and config/disk tests | Deletes finished private builds only; protects main repo, active tasks, MERGE*, VENDOR*, PROBE* and symlink targets. Fixed floors/caps cannot be relaxed through the tested config fields; low disk aborts. |

The real independent-checker run requested **8 names**, exported **7,284 bytes**, and con-ron accepted **11 declarations** with `--verified`; nanoda checked **16 declarations with no typechecker errors**. Its one pretty-printer diagnostic was “Unable to print axioms.” [Export manifest](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/independent-export-manifest.json), [con-ron log](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/independent-con-ron-0.log), [nanoda log](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/independent-nanoda-0.log). This tests tooling on tiny fixtures, not a full production certificate corpus or four-hour computation.

Command C:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B verify_audit.py > evidence/verification.log 2>&1
```

Passed: installed source/entry-point/configuration hashes match their pre-test snapshots; the production frozen manifest matches its files; installed Python parses; subprocess calls do not request `shell=True`. Code review found **no shell pipelines** in the installed v1 execution paths: validation uses sequential checked argv subprocesses, so there is no tool-owned pipeline needing `set -o pipefail`. Command B's stage-failure tests establish that a later successful stage cannot mask an earlier failure. [Static review](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/static-review.json), [verification log](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/verification.log).

Every test repository was a disposable `git clone --shared` under this scratch directory, with `.lake/packages` symlinked to `/home/ubuntu/aklt/repo/.lake/packages`. The tiny fixtures replace campaign sources only inside those clones. Package links were not traversed for cleanup or edited. All **137** retained package symlinks resolve to the prescribed cache; **zero private `.lake/build` directories remain**. Scratch use is approximately **78.5 MB**, below 10 GB; root disk had approximately **195.5 GB free** at completion. At most two audit Lean processes could overlap, below the four-process cap. No daemon, agent or tmux session was started. Actual timeout termination applied only to disposable validation children. No files in `/home/ubuntu/dbl`, `/home/ubuntu/sharp`, `/home/ubuntu/md` or `/home/ubuntu/sal` were changed; the foreign-cwd driver test was fully mocked. [Resource/cleanup record](/home/ubuntu/aklt/scratch/V-ORCH-1/evidence/final-resources.json).
