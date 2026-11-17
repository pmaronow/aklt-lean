STATUS: COMPLETE

Installed `tools/v3` and repointed `bin/aklt-tool` and its existing command links to v3. Both remaining V-ORCH-2 findings are fixed. V1, v2, the orchestrator-owned `aklt-gate`, configuration, credit baseline, frozen manifest, task ledger and main repository are unchanged. No daemon, tmux session, model agent or sub-agent was started.

The installed release passes **44/44 builder/regression tests**, **69/69 re-audit tests**, and **1/1 supplemental public-budget test**. These suites include all maintained earlier builder/auditor cases. The historical original-assertion replay is reported separately below and is not counted as passing.

## resume3

The fixes were developed and tested under `/home/ubuntu/aklt/scratch/PORT1/v3/`, then installed in one locked step. The current full tool/usage/state/gate reference is [tools/v3/README.md](/home/ubuntu/aklt/tools/v3/README.md). The complete v2 report follows this section as history; its v2-specific outcome statements describe that earlier installation.

| Finding | Fix and validation |
| --- | --- |
| Remaining Blocking 3: ignored non-Lean MERGE edits overwritten | `Context.ignored_uncommitted` enumerates ignored untracked paths from the whole checkout with Git's NUL-delimited output. Clean admission refuses every nonexempt ignored file, regardless of extension, before integration/reset. Exemptions are limited to `.lake/build/`, `.lake/packages/`, exact `.lake/config/<numeric-version>/lakefile.olean[.trace]`, and legacy `.lake/lakefile.olean[.trace]` outputs. Notes elsewhere under `.lake/` refuse admission. Explicit journal recovery includes all nonexempt ignored paths in its byte backups and refuses unrelated dirt before reset. The auditor's binary-note collision regression now preserves the exact bytes, validated ref and finished task state. Added tests cover binary/no-extension/newline paths, root files, fake cache notes, valid cache exemptions and recovery backups. |
| Major: private/Unicode declarations cannot reach full validation | Inventory renders each actual kernel Name with `Name.toStringWithSep "." true` and checks equality after the same `Syntax.decodeNameLit` decoder used by the pinned `leanexport`. JSON framing preserves quoted dots/spaces, numeric string components, tabs/newlines and Unicode. Numeric private-name components retain their numeric identity. Chunking counts UTF-8 argv bytes without applying the separate ASCII operator-metadata grammar; empty/NUL/option-like arguments refuse. Real `leanexport`, `con-ron --verified --jobs=1` and NanoDa pass for both original auditor modules and a two-chunk fixture containing private helpers, Unicode, quoted numeric/dotted/spaced names, multiline names, a Unicode line separator and `«--flag»`. |

The orchestrator had already replaced `aklt-gate` with its shell `exec aklt-budget-check` wrapper before this turn. PORT1 left its bytes unchanged. The six formerly failing gate bypasses now pass through that actual executable; the queue continues to call the same internal budget implementation directly. Budget, retry, ladder and source-policy modules are unchanged from v2.

The auditor's three regression methods (`test_ignored_nonlean_merge_edit_is_preserved`, `test_full_validation_accepts_private_theorem`, `test_full_validation_accepts_unicode_declaration`) are preserved **verbatim** in [test_bypasses.py](/home/ubuntu/aklt/scratch/PORT1/v3/auditor/tests/test_bypasses.py). The integrity verifier compares their source text against V-ORCH-2. Before the fix all three failed against installed v2; after the fix all three pass. [Before log](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/before-regressions.log), [after log](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/after-regressions.log), [provenance](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/regression-provenance.json), [source diff](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/v2-to-v3.diff).

Only three implementation modules changed: `aklt_common.py`, `aklt_integrate.py` and `aklt_validate.py`, plus the README and dispatcher version. The v3 installation receipt is `state/installation-v3.json`; both earlier receipts remain intact. Nothing new was copied from DBL in resume3; the earlier DBL adaptations described below remain unchanged.

### Commands and outcomes

Run from `/home/ubuntu/aklt/scratch/PORT1`; every writable test fixture/evidence path is under this scratch root. Shared Mathlib packages are symlinked read-only. Agent/tmux starts are mocked. Lean and independent checker runs are real.

```sh
# Installed builder suite (39 retained cases + 5 resume3 cases)
AKLT_TEST_TOOLS=/home/ubuntu/aklt/tools/v3 PYTHONDONTWRITEBYTECODE=1 \
  python3 -B -u v3/run_suite.py v3/tests v3/evidence/release-builder

# Entire retained/adapted re-audit: 28 builder + 15 V-ORCH-1 + 11 v2 + 15 V-ORCH-2
AKLT_TEST_TOOLS=/home/ubuntu/aklt/tools/v3 PYTHONDONTWRITEBYTECODE=1 \
  python3 -B -u v3/run_suite.py v3/auditor/tests v3/auditor/evidence/release-suite

# Auditor's supplemental real public-command matrix
AKLT_TEST_TOOLS=/home/ubuntu/aklt/tools/v3 PYTHONDONTWRITEBYTECODE=1 \
  PYTHONPATH=v3/auditor/tests:v3/auditor/supplemental \
  python3 -B -u -m unittest test_extra -v

# Preserved original assertions: import target only changed to staged v3
AKLT_TEST_TOOLS=/home/ubuntu/aklt/scratch/PORT1/v3/stage/tools \
  AKLT_TEST_BIN=/home/ubuntu/aklt/scratch/PORT1/v3/preview/bin \
  AKLT_TEST_INSTALLED_HOME=/home/ubuntu/aklt/scratch/PORT1/v3/preview \
  PYTHONDONTWRITEBYTECODE=1 \
  python3 -B -u v3/run_suite.py v3/original/tests v3/original/evidence/stage-replay

python3 -B v3/verify.py
python3 -B v3/auditor/verify_audit.py
```

| Run | Outcome | Evidence |
| --- | --- | --- |
| Staged builder suite | 44 passed; 0 failures/errors/skips | [Log](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/stage-builder.log) |
| Staged auditor suite + supplemental | 69 + 1 passed; 0 failures/errors/skips | [Suite](/home/ubuntu/aklt/scratch/PORT1/v3/auditor/evidence/stage-suite.log), [supplemental](/home/ubuntu/aklt/scratch/PORT1/v3/auditor/evidence/stage-extra.log) |
| Installed builder suite | 44 passed in 242.361 s; exit 0 | [Log](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/release-builder.log), [result](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/release-builder/suite-result.json) |
| Installed auditor suite | 69 passed in 267.278 s; exit 0 | [Log](/home/ubuntu/aklt/scratch/PORT1/v3/auditor/evidence/release-suite.log), [result](/home/ubuntu/aklt/scratch/PORT1/v3/auditor/evidence/release-suite/suite-result.json) |
| Installed supplemental matrix | 1 passed; exit 0 | [Log](/home/ubuntu/aklt/scratch/PORT1/v3/auditor/evidence/release-extra.log) |
| Original-assertion replay | 38/43 passed; 2 failed, 3 errored; exit 1 | [Log](/home/ubuntu/aklt/scratch/PORT1/v3/original/evidence/stage-replay.log), [result](/home/ubuntu/aklt/scratch/PORT1/v3/original/evidence/stage-replay/suite-result.json) |
| Builder + copied auditor integrity/static/resource verifiers | Both passed; exit 0 | [Builder](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/release-verification.log), [auditor](/home/ubuntu/aklt/scratch/PORT1/v3/auditor/evidence/release-verification.log) |

The original-assertion replay deliberately retains obsolete interfaces: its 19-command count, immediate reopening after quota reset, removed subprocess retry seam, and expectation that unsafe `--driver` reaches a mocked driver. Those four incompatibilities were documented in v2. The fifth is new because the orchestrator retired the Python manual gate: `runpy.run_path` now tries to parse its Bash `exec` as Python. The maintained auditor copy executes that shell wrapper as a real subprocess against the disposable campaign and preserves every acceptance/rejection assertion. No case is skipped or silently counted as passing.

The maintained auditor harness changes only imports/output roots and the current shell-gate execution seam; its public-command paths can select the scratch preview for pre-install tests. All three failing re-audit regression methods are unchanged. [Exact harness diff](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/auditor-adaptations.diff), [import-only original replay diff](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/original-replay-adaptations.diff). Original V-ORCH-1/V-ORCH-2 sources and evidence are untouched. The copied integrity script changes only its source/dispatcher target, snapshot/output roots and shell syntax check; it continues to verify historical receipts, frozen/main files, package links and cleanup.

The additional name fixture requests **15 declarations across two real exports**, with con-ron accepting **19 declarations including dependencies**. Both NanoDa invocations return success. [Names, hashes and receipts](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/export-names.json), [first con-ron log](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/name-checkers/con-ron-0.log), [second con-ron log](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/name-checkers/con-ron-1.log), [first NanoDa log](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/name-checkers/nanoda-0.log), [second NanoDa log](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/name-checkers/nanoda-1.log). All 20 supported dispatcher/help entry points are exercised by the installed auditor CLI test.

### Preservation, resources and limitations

The final verification compares 136 protected file/symlink records against the start of this turn, verifies all three installation receipts, and checks complete historical v1/v2 file sets. The manual gate SHA-256 remains `23d218f12f4e7625fce58a648466b8edada9fcdd5c2fdfa61452c53969dfa107`. Config, original baseline, frozen manifest, task ledger, repository files/Git metadata and existing command links are unchanged; only the shared dispatcher was repointed. [Deployment](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/deployment.log), [integrity/resource record](/home/ubuntu/aklt/scratch/PORT1/v3/evidence/verification.json).

Scratch use is **0.964 GB**, below 20 GB, and `/` has **189.8 GB** free, above the 150 GB abort floor. All disposable `.lake/build` directories are removed; 514 shared-package links resolve to the prescribed read-only cache. At most three foreground test runners overlapped, each with one sequential compiler/checker child: at most three such children, or six processes counting their Lake parents, below eight. Each runner's sampled maximum visible Lean count is in its result JSON. No production logs, refs, quota-reset acknowledgement or model sessions were created by these tests.

Operator metadata selectors still use unquoted ASCII identifiers; exported kernel names use their separate round-tripped representation. A kernel name that the pinned exporter cannot represent, or that argv cannot carry (NUL), refuses validation explicitly. This is a trusted-operator controller and the lexical policy remains conservative. Independent validators were exercised on tiny real modules, not a future full AKLT certificate corpus or four-hour certificate. Live agent/daemon behavior was not exercised because the brief forbids starting them.

## Historical v2 report

Installed `tools/v2` and repointed the campaign wrappers to v2. Every Blocking and Major finding from V-ORCH-1 is addressed within the scope authorized by the orchestrator. `tools/v1`, `bin/aklt-gate`, the original credits baseline, frozen manifest and task ledger are unchanged. No daemon, agent, Claude/Codex process, or sub-agent was started by this work.

The maintained suites pass **39/39 builder/regression tests** and **43/43 auditor-suite tests** (15 audit cases plus its 28 copied builder cases). The original v1 assertions were also replayed without assertion changes: **39/43 pass**, with **two failures and two errors** reflecting the four interface/policy assumptions documented below. The updated test copies retain every case and explicitly test the stronger v2 behavior; their exact diffs and both replay outcomes are preserved.

For manual launch budgeting, use:

```sh
/home/ubuntu/aklt/bin/aklt-budget-check N
```

Exit 0 means the shared quota/credit/reset budget permits N additional agents; any nonzero exit holds. Queue launches use the same function with N=1. Budget approval does not allocate model/Lean/leaf slots; the queue enforces those separately. PORT1 never edits or invokes the manual `aklt-gate` for queue decisions.

After a detected quota reset and operator wrap-up, the explicit acknowledgement is `aklt-budget-check 0 --ack-reset`. It retains manual pause files and the original credit baseline. No reset was acknowledged on the live campaign during these tests.

## Finding resolution

| Audit finding | V2 change | Evidence |
| --- | --- | --- |
| Blocking 1: 15–30-minute readings launch | Default and installed configuration are 900 s. Context rejects values above 900. The common gate accepts the 900-second boundary, rejects 901 seconds and future readings, and ages an acquired snapshot while a queue tick runs. | Builder freshness regression; auditor fifteen-minute test; `state/config.json` and `aklt_common.py`. |
| Blocking 2: quoted option bypass | Every `set_option` is parsed conservatively; quoted identifier components are normalized before the same resource bounds are applied. Bounded quoted settings compile and integrate; unlimited/excessive quoted settings are rejected outside the exact certificate allow-list. | Real Lean bounded-quoted integration and auditor rejected-quoted integration; ordinary and certificate source-gate tests. |
| Blocking 3: dirty MERGE deleted | Existing MERGE must be clean before any task/state recovery or reset. No broad `git clean` remains. Merge/archive mutations record an intent. Interrupted work halts for explicit `aklt-integrator --recover-merge`; recovery backs up exact file bytes, index/worktree patches and a receipt, refuses unrelated dirt, and checks archived bytes. | Auditor dirty-MERGE test; regression preserving tracked edits, untracked notes and validated; interrupted-archive recovery regression with backup and unrelated-note refusal. |
| Blocking 4: retry permits kill/foreign-write flags | Driver tasks are constructed from the running reservation. Model, original effort/search, worktree, report roots, workspace-write and `timeout=None` are checked before delegation and command construction. Writable roots are explicitly pinned on new and resumed turns. Unsafe CLI flags, unsafe resume metadata and the obsolete `--driver` route are rejected before Popen. The retry loop calls the bound driver library directly. | Positive mocked driver delegation verifies `communicate(timeout=None)` and safe argv; unsafe CLI/task/metadata cases assert zero delegation and zero kill calls; transient retry test preserves the same session and effort. |
| Blocking 5: alternate manual gate | Added `aklt-budget-check [N=1]`, using exactly `aklt_queue.budget`, which the queue calls with N=1. The formula conservatively includes requested new agents: `remaining - 0.3*(running+N) - 1 > 0`. Both windows, strict Decimal credits, freshness, future events, credit-only flags, reset/manual holds and the total cap are checked. Registered reservations and observed external Codex exec roots are deduplicated. | Same 1.3% boundary blocks both queue and CLI for one new agent; N=0/1/4 tests; observed-process/ledger dedup regression; installed CLI/live gate results. The orchestrator-owned gate's hash is unchanged. Its retained legacy test now passes against the version already present at the start of this turn; PORT1 made no change to it. |
| Major 1: reset pause absent | Fresh acquired quota events persist their minimum and observation time. A rise greater than five points latches `state/quota-reset.json`, `QUEUE_PAUSE` and `WRAPUP_MODE`. Missing/deleted marker files cannot clear the JSON latch. Resume requires explicit acknowledgement. No running agent is killed and no credit baseline is rebased. The floor-zero rule remains; no old 3% exhaustion floor was added. | Auditor GUIDE reset case; restart, deleted-marker and explicit-ack regressions; credit baseline byte-preservation assertion. |

No Minor findings were listed in V-ORCH-1. Two further integration issues were fixed cheaply: status/digest now display the same one-new-agent budget as the queue, and the shared Lean admission lock works with controller state mounted read-only inside a writer sandbox. The latter was reproduced as a real read-only-filesystem failure before the fix, then verified with real `bwrap` and Lean after the controller began precreating the inode and writers began flocking a read-only descriptor. No additional writable root is granted to agents.

## Reproduction and outcomes

All commands ran from `/home/ubuntu/aklt/scratch/PORT1`. The auditor files were copied from `/home/ubuntu/aklt/scratch/V-ORCH-1/tests/` and `verify_audit.py`; the referenced evidence supplied the failing inputs. The original audit area was never modified.

```sh
AKLT_TEST_TOOLS=/home/ubuntu/aklt/tools/v2 PYTHONDONTWRITEBYTECODE=1 \
  python3 -B -u -m unittest discover -s v2/tests -v

AKLT_TEST_TOOLS=/home/ubuntu/aklt/tools/v2 PYTHONDONTWRITEBYTECODE=1 \
  PYTHONPATH=v2/auditor/tests python3 -B -u -m unittest discover \
  -s v2/auditor/tests -p 'test_*.py' -v

PYTHONDONTWRITEBYTECODE=1 python3 -B -u v2/replay_original.py
PYTHONDONTWRITEBYTECODE=1 python3 -B v2/auditor/verify_audit.py
PYTHONDONTWRITEBYTECODE=1 python3 -B v2/verify.py
```

| Check | Outcome |
| --- | --- |
| Builder + V-ORCH-1 regressions against installed v2 | 39 tests passed, 217.574 s. [Log](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/release-builder-regressions.log). |
| Auditor's retained 15 cases + copied builder suite against installed v2 | 43 tests passed, 208.086 s. [Log](/home/ubuntu/aklt/scratch/PORT1/v2/auditor/evidence/release-all.log). |
| Original assertions replay, actual installed v2 | 43 cases; 39 pass, 2 failures, 2 errors, 210.155 s, exit 1. [Unfiltered log](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/release-original-replay.log). No failure was omitted or turned into a skipped test. |
| Auditor's verification script | Passed against a v2 pre-test hash snapshot; source version and evidence destination were relocated. Confirms unchanged installed hashes, matching frozen files, Python syntax, no `shell=True`, package links, cleanup and disk bounds. [Log](/home/ubuntu/aklt/scratch/PORT1/v2/auditor/evidence/release-verification.log). |
| Additional immutable/archive verification | Passed: complete v1 file set/hashes unchanged; manual gate, credits, frozen and ledger hashes unchanged; v2 source/document hashes match its receipt; wrapper points to v2; configuration cap is enforced. [Record](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/verification.json). |
| Installed help entry points | All 20 return exit 0, including the new budget-check command and shared dispatcher. [Results](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/wrappers-release.json). |
| Writer sandbox | Real Lean compiles with only worktree/report writable and controller state read-only. The original failure and corrected test are retained: [before](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/writer-sandbox-before.log), [after](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/writer-sandbox-fixed.log). |
| Independent kernels | The installed suites rerun the real Lean build/axiom/type checks, leanexport, con-ron `--verified` and nanoda on disposable fixtures, including generated final terms. Injected exporter/checker failures remain loud and cannot publish a success receipt. |

## Exact test adaptations

The original assertions were deliberately replayed to distinguish harness changes from code regressions. The four incompatible assumptions are:

1. The original builder transient-retry test patches `aklt_retry.subprocess.run` and supplies a minimal unbound task. V2 has no subprocess-based retry passthrough. The maintained test mocks the bound driver's task callback, supplies an actual registered task and verifies the resumed session, explicit original effort, cwd and `timeout=None`.
2. The original unsafe-driver audit expects the unsafe call to reach a mocked Popen, then inspects its arguments. V2 rejects `--driver` and unsafe flags before delegation, so that original invocation raises GateError. The maintained case explicitly expects GateError, `Popen.assert_not_called()` and no kill call. Additional cases directly exercise the bound driver guard and reject timeout/foreign-root metadata.
3. The original installed-CLI test hard-codes 19 entry points. Adding the requested budget-check command produces 20. The maintained case tests all 20.
4. The original mixed quota-window test expects automatic reopening immediately after 0% rises to 100%. That conflicts with Major 1's reset latch. The maintained case first asserts the reset hold, explicitly acknowledges it, then asserts reopening. Its credit-decrease, stale, missing and secondary-exhaustion checks remain.

The remaining edits relocate imports/output into PORT1 scratch, provide an optional preview-bin/config path for testing before deployment, and label copied verifier metadata for v2 and the measured concurrency bound. [Exact unittest diff](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/auditor-test-adaptations.diff). The replay compiles the original files unchanged, preloads installed v2 modules and relocates only their writable test roots; original source snapshots are preserved under `v2/raw-replay/tests/`.

## Deployment and operation

Development and all new tests were staged under `scratch/PORT1/v2/` before deployment. V2 was deployed with atomic replacements within each destination filesystem; candidate deployment snapshots are retained in scratch. The final deployment and hash receipt are in [deployment.json](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/deployment.json) and `state/installation-v2.json`. The original `state/installation.json` and `tools/v1` remain the v1 record. The earlier report is retained as [report-v1.md](/home/ubuntu/aklt/reports/PORT1/report-v1.md).

New operational state is limited to the documented reset tracker/markers, MERGE operation intents/recovery backups, and the read-only-compatible admission lock. A clean existing MERGE with an interrupted tool intent requires explicit recovery rather than automatic discarding. Unexpected dirty MERGE files are preserved and require operator reconciliation. The initial task ledger remains untouched; no actual queue task was launched.

The final v2 deployment was recorded at 2026-11-16T04:32:40.190481+00:00. The live `aklt-budget-check 1` returned exit **0**, `allowed=true`, remaining **99.00%**, and prospective launch margin **97.70**. The live command and status performed no launches. [Budget JSON](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/live-budget-check.json), [status](/home/ubuntu/aklt/scratch/PORT1/v2/evidence/live-status.txt).

Cleanup found **zero** private `.lake/build` directories remaining. PORT1 scratch uses approximately **676.3 MB**, below 20 GB; root disk had **194.9 GB** free at verification, above the 150 GB abort floor. All retained test package links resolve to the prescribed shared read-only cache. At most six private Lean processes could overlap across successive three-runner groups, below the cap of eight. No daemon or agent was started, and no files in another campaign were modified.

The inherited limits remain documented: trusted operator/toolchain/package assumptions; conservative lexical Lean policy; explicit semantic compose refreshes; ASCII metadata identifiers; no live model/daemon test; future four-hour certificate workloads not yet exercised. The read-only `bwrap` regression covers the writer filesystem boundary without a model call.

The complete installed tool reference follows.

# AKLT campaign tools v2

Python 3 standard library, Git, tmux, and the pinned Lean toolchain are the only
dependencies. The public commands are `~/aklt/bin/aklt-*`; implementation modules
live here. V1 is retained unchanged for reference. The shared dispatcher is `aklt-tool COMMAND [ARGS...]`. `AKLT_HOME` defaults to `/home/ubuntu/aklt` and may select a disposable
campaign for testing. Imports, installation, and `--help` never start a daemon or
an agent. The main checkout is never used as the integration working tree.


This version addresses V-ORCH-1: a non-relaxable 900-second quota lifetime; quoted Lean option normalization; clean MERGE admission plus explicit, backed-up journal recovery; reservation-bound agent tasks without agent-kill flags; one prospective-reserve budget shared by queue and `aklt-budget-check N`; and the GUIDE reset pause. The original floor-zero/no-credit rule remains in force. No 3% exhaustion floor is introduced.

For the orchestrator, switch budget calls to `~/aklt/bin/aklt-budget-check N`. It returns JSON and exit 0 only when the common budget gate permits N additional agents. Model/Lean/leaf scheduling still belongs to the queue; a budget approval alone does not allocate those slots. A reset rise above the observed minimum by more than five points sets a persistent pause. After wrap-up, explicitly run `aklt-budget-check 0 --ack-reset`; ordinary fresh allowance never clears that pause automatically.

V2 deployment preserves the original credits baseline, frozen manifest, task ledger, author files, and all of tools/v1. It lowers only an excessive quota freshness configuration to 900 seconds and repoints the common wrapper to tools/v2.

## Start-up and normal operation

The original campaign installation recorded the Yale credit baseline and frozen
hashes. This v2 upgrade preserves those records and the task ledger; it only
lowers an excessive quota freshness limit to 900 seconds. It **does not create or advance a repository ref**, run validation,
or start tmux. For a campaign without a validated ref, the explicit operator action is:

```sh
~/aklt/bin/aklt-init
```

This checks the clean main checkout, validates `main` in a detached `MERGE_INIT`
worktree, and creates `validated` if it does not exist. An existing `validated`
is retained. `main` and its working files are never advanced by the integrator.
Keep `validated` as a ref, without checking it out in a worktree.

As the author adds the statement layer, commit it through the author workflow and
validate that commit. Register its hashes with `aklt-freeze --blueprint PATH`
(repeat for each Blueprint statement file). Challenge and Defs files are included
automatically. Existing frozen hashes cannot be rewritten by this command.
Blueprint assemblies can be separate, unfrozen files. Author-controlled changes
to the statement layer and adoption of a new author commit into `validated` are
explicit Git operations; writer tasks cannot do them.

Register a leaf with `aklt-ladder add ~/aklt/briefs/leaf.json`:

```json
{
  "key": "GAP01",
  "node": "AKLT.Blueprint.Gap.Leaf01",
  "module": "AKLT.Blueprint.Gap.Statements",
  "brief": "/home/ubuntu/aklt/briefs/GAP01.md",
  "deps": []
}
```

This verifies the frozen, nullary `def : Prop`, creates `GAP01_L` from
`validated`, and queues Luna/xhigh. The expected theorem is
`AKLT.W.GAP01_L.Leaf01_holds`; optional `theorem_luna` and `theorem_sol` fields
override the conventional theorem names. `deps` lists frozen named propositions
only. Keys and generated Lean names use ASCII identifiers; keys cannot contain
hyphens, dots, whitespace, or shell syntax.

After reviewing the queue, the operator can run the loops in separate tmux
sessions. These commands are examples, not actions taken by installation:

```sh
tmux new-session -d -s aklt-queue '~/aklt/bin/aklt-queue --loop'
tmux new-session -d -s aklt-integrator '~/aklt/bin/aklt-integrator --loop'
tmux new-session -d -s aklt-ladder '~/aklt/bin/aklt-ladder --loop'
~/aklt/bin/aklt-digest --start
```

To pause new launches, create `state/PAUSE`; remove it to resume. Running agents
are never killed by quota, credit, or concurrency gates. No tooling automatically
repeats a lost or failed agent attempt.

## Every public command

| Command | Usage and result |
| --- | --- |
| `aklt-init` | Explicit initial validation and creation of `validated`; no agents or loops. |
| `aklt-mkwt` | `KEY [BASE=validated]`: creates `wt/KEY`, branch `task/KEY`, private `.lake/build`, and a symlink to the main repo's prebuilt `.lake/packages`. Existing paths/branches are not reset. |
| `aklt-cleaner` | `[--dry-run] [--loop]`: removes only `.lake/build` in registered finished task worktrees, after fresh completion flags and idle-process checks. Retains sources, branches, worktrees, certificate cache, and all main-repo outputs. Never cleans names beginning `MERGE`, `VENDOR`, or `PROBE`; refuses symlink builds and foreign worktrees. A loop checks every five minutes. |
| `aklt-budget` | Prints the budget for one additional agent using the same implementation as the queue. Exit 0 allows the quota/credit/reset gate; nonzero holds. |
| `aklt-budget-check` | `[N=1] [--ack-reset]`: command-line equivalent of the queue budget, reserving N new agents. Exit 0 iff that budget permits them. Negative/noninteger N is refused. `--ack-reset` explicitly releases the reset latch after wrap-up, then evaluates the requested budget; it preserves the credit baseline and manual pause files. This is the supported replacement for manual gate calls. PORT1 does not edit or call the orchestrator-owned `aklt-gate`. |
| `aklt-queue` | `[tick] [--dry-run] [--loop]`; `add TASK.json`; `list`; `recover KEY [--finished]`. A tick launches eligible tasks in tmux sessions `aklt-KEY`. Dry-run evaluates one next eligible task without reserving or launching it. `recover` settles an explicitly selected lost session only after tmux, runner-lock and live-worktree-process checks; it never relaunches. |
| `aklt-ladder` | `[tick] [--loop]`; `add LEAF.json`; `list`. The two possible attempts are `KEY_L` (Luna/xhigh) and `KEY_S` (Sol/max). Success or exhaustion is determined by compiled exact checks after integration. |
| `aklt-sol-retry` | Internal queue runner: `EFFORT SEARCH(0\|1) -- run\|resume REGISTERED_ARGS`, including explicit `-e EFFORT`. Only the original worktree/report/name/brief/search settings are accepted. There is no arbitrary driver passthrough: `--timeout`, `--full-access`, foreign roots and the obsolete `--driver` route are rejected. The driver task and writable roots are constructed from state, validated before delegation and command construction, with workspace-write and timeout=None. Retries transport/capacity errors up to eight times in the same session. |
| `aklt-luna-retry` | Same interface and behavior, using the Luna driver. These wrappers do not create new attempts. |
| `aklt-freeze` | `[--blueprint AKLT/Blueprint/Part/Statements.lean ...]`: records clean committed statement files in `state/frozen.sha256`, retaining and verifying every previous entry. No hash replacement or unfreezing. |
| `aklt-effect-guard` | `FILE_OR_DIR ...`: lexically scans Lean files; no Lean execution. It applies the resource-option exception only to canonical main-repo paths explicitly present in the certificate list. Integration validates worktree paths relative to their roots. |
| `aklt-exact` | `KEY NODE THEOREM STATEMENT_MODULE [--dep NODE ...]`: builds task imports, checks the frozen node, compiles `example : NODE := THEOREM`, prints its axioms, and audits the theorem's declaration kind and axioms. Exit 2 means unproved. With declared dependencies it additionally tries the exact arrow type `D₁ → ... → NODE`. No report text can create a success. |
| `aklt-integrator` | `[--once\|--loop] [--recover-merge]`: one integration tick by default; batches finished tasks, removes identified culprits iteratively, and then tries deferred/unattributed tasks one at a time. Uses only the detached `wt/MERGE` for merge/reset/validation. Publication uses a journal and a compare-and-swap ref update. Existing MERGE must be clean. Interrupted merge/archive intents halt normal processing; `--recover-merge` explicitly creates a lossless backup before reverting only journal-owned changes. Unrelated dirt is preserved and refused. |
| `aklt-validate-fast` | `WORKTREE BASE [--tag TAG]`: checks a clean worktree, frozen files, sources, complete library build, duplicate declaration names, and axioms of changed declarations. Does not publish a ref. |
| `aklt-validate` | `TAG`: independent milestone validation of a pinned `validated` head in a fresh detached worktree. Checks a clean main checkout first, builds/audits the full campaign, exports names in byte-bounded chunks, and runs both independent checkers. The unique tag determines `logs/validation/TAG/`. |
| `aklt-status` | One compact screen: task queue states, active model/effort/key groups, ladder counts, integrator state, `validated` and milestone commits, disk/memory, Yale quota/credits, stale flags, unladdered open leaf candidates, and exhausted nodes. Long key lists may wrap in a narrow terminal. |
| `aklt-digest` | One status/completion digest by default; `--loop` writes it every 600 seconds; `--start` creates the `aklt-digest` tmux loop. Appends to `logs/digest.log`. No model calls. |
| `aklt-compose` | Dumps theorem/constructor heads with closed named-Prop hypotheses and conclusions from a pinned validated snapshot, audits axioms, computes the least fixed point, and saves theorem heads, closed nodes and semantic Blueprint inventory. Cycles without a proved base never close. |
| `aklt-genfinal` | `WORKTREE TOP_NODE [--key KEY]`: uses a fresh composition receipt to write `AKLT/W/KEY/Final.lean`, with explicit named intermediate proofs and an explicit term chain for the goal. Lean compiles it and the axiom auditor checks it. A stale receipt, open goal, wrong base, dirty worktree, or existing final file is refused. Queue this final task normally to integrate it. |

General non-leaf queue tasks can be added after `aklt-mkwt KEY`:

```json
{
  "key": "HELPER01",
  "model": "sol",
  "effort": "max",
  "brief": "/home/ubuntu/aklt/briefs/HELPER01.md",
  "worktree": "/home/ubuntu/aklt/wt/HELPER01",
  "report_dir": "/home/ubuntu/aklt/reports/HELPER01",
  "lean_writer": true
}
```

Model and effort are mandatory. `lean_writer` defaults to true. Use the ladder for
every leaf; direct queue registration of a leaf is refused. Reports have exactly
one recognized first line: `STATUS: PROVED`, `STATUS: PROVED FROM DEPS`,
`STATUS: PARTIAL`, or `STATUS: FALSE`. Later report text is never parsed. The
queue freezes a copy of each brief and checks its hash before launch. Each task
gets its own writable report directory. Agents use workspace-write, the pinned
Yale home and model drivers, and the ordinary service tier.

## State, logs, and recovery

| Path under `~/aklt/` | Meaning |
| --- | --- |
| `state/config.json` | Caps and durations. Defaults: Lean writers 48, Sol 24, total 56, task 1800 s, certificate 14400 s, milestone checker 14400 s, batch 12, controller tick 20 s. Caps may only be lowered. Floor 0, reserve 0.3 and margin 1 are fixed policy. Quota freshness defaults to 900 s and configuration cannot raise it above 900 s. Disk abort floor defaults to 150 GB; status alarm is 120 GB. |
| `state/credits-baseline.json` | Numeric decimal balance, event time/source, and installation time. Never automatically rebased after spending. |
| `state/disk-baseline.json` | Existing non-repo campaign bytes at installation; monitored growth budget is 20 GB. Symlinked package caches are not traversed. |
| `state/frozen.sha256` | SHA-256 hashes of all Challenge/Defs files and explicitly registered Blueprint statement files. Empty initially if no statement layer exists. |
| `state/certificate-modules.txt` | One exact repo-relative `.lean` path (or dotted module name) per line; blank lines and `#` comments accepted. No globs or directory exemptions. Only these files receive resource-option and build-time exemptions. |
| `state/campaign.json` | Versioned authoritative tasks, leaves, integrator journal and last validated receipt. Updates use `state.lock`, atomic replacement, and fsync. Back it up together with frozen hashes and the credits baseline. |
| `state/PAUSE` | Presence pauses new queue launches; reset handling never overwrites it. |
| `state/quota-reset.json`, `state/QUEUE_PAUSE`, `state/WRAPUP_MODE` | Fresh acquired readings track their minimum. A rise greater than five percentage points latches a reset pause and wrap-up mode. Deleting a marker does not clear the persisted latch. Use `aklt-budget-check 0 --ack-reset` after wrap-up; unrelated/manual markers remain. |
| `state/merge-operation.json`, `scratch/merge-recovery/` | Intent before each MERGE merge/archive mutation, plus explicit recovery backups containing file bytes, index/worktree patches and receipts. A dirty MERGE is never silently reset or cleaned. |
| `state/quota-index.json` | Per-rollout size/mtime and last token event, to avoid reparsing unchanged session logs. The newest **event timestamp across every rollout**, not the newest file mtime, determines quota. The newest event lacking rate_limits holds launches. |
| `state/briefs/`, `state/ladder-briefs/` | Immutable queued prompts and generated ladder prompts. |
| `state/agent-sessions/`, `state/agent-session-efforts/` | Private driver session metadata and task/model/original-effort binding. Resumes explicitly pass and verify the original effort. |
| `state/certificate-cache/HASH/` | Content/dependency/toolchain/configuration keyed trusted artifacts and their SHA-256 manifest. Corrupt entries stop validation. |
| `state/lean-sysroot/`, `*.lock`, `runners/`, `retry-runners/` | Private toolchain facade and advisory locks. No shared toolchain or package file is changed. Lock files can remain after process exit; the kernel releases the locks. |
| `state/compose.json`, `state/theorem-heads.tsv`, `state/blueprint-nodes.json` | Pinned semantic node/rule inventory and closure. Status flags stale/missing inventory; rerun compose when author statements change. Open nodes without an incoming assembly rule are the unladdered leaf candidates. |
| `state/last-milestone.json`, `state/digest.json` | Latest independent-validation receipt and digest timestamp. |
| `flags/KEY.done` | JSON completion receipt written only after the agent driver and retries return, including failures. A report alone does not imply completion. |
| `flags/int-KEY.done` | Integration/archive receipt pinned to the published commit. |
| `logs/agents/`, `logs/agent-runs/` | Wrapper output and private generic-driver transcripts/results. |
| `logs/integration/`, `logs/validation/`, `logs/ladder/`, `logs/compose/`, `logs/genfinal/` | Source/type/axiom/build/export/checker logs and receipts. |
| `logs/integrator.log`, `logs/certificates.log`, `logs/cleaner.log`, `logs/digest.log` | Operator event and digest logs. |
| `scratch/retry/MODEL-SESSION-N.md` | Unique transient continuation prompts, adapted from the campaign-local retry wrappers. |

Task states are queued → launching → running → finished → integrating →
integrated/rejected. An uncertain tmux launch becomes orphaned and still consumes
capacity/quota reservation. It is never automatically launched again. A crash
during integration retries validation, never the writer. Dirty or interrupted MERGE operations require explicit recovery; automatic startup preserves their files. A crash on either side
of ref publication is settled from the journal and commit ancestry on the next
integrator tick. A disappeared running tmux session remains held until the
operator uses `aklt-queue recover KEY --finished`; this avoids accidental overlap.

Sol is queued only after Luna's attempt is published into `validated` and its
exact check returns unproved. Safe partial code is integrated normally. Rejected
or empty attempts are stored at `AKLT/W/LUNA_KEY/Attempt.json`, with exact owned
file bytes encoded as base64, the first-line verdict, and rejection diagnostics.
Sol's worktree descends from that receipt and its brief points to the previous
attempt/report/verdict. No invalid Lean source enters the validated library.
After Sol is unproved, the leaf is EXHAUSTED. Conditional proofs stop the writer
ladder as PROVED FROM DEPS; composition determines whether their dependencies
actually close the top statement.

## Gates and invariants

1. **Launch:** all active/uncertain reservations count, including between ticks.
   Re-evaluate before every launch, respecting all three caps and leaf ownership. The queue uses N=1; the manual budget checker uses its supplied N. Quota snapshots also count observed external `codex exec` roots, deduplicating wrapper/native ancestry and registered runner descendants.
   Let remaining be the minimum remaining percentage of the available primary and
   secondary Yale windows. Launch iff `remaining - 0.3*(running + N) - 1 > 0`, credits
   have not decreased below the install baseline, the snapshot is at most 900 seconds old, is not from the future, no reset/manual pause is latched, and no
   rate/spend-limit flag indicates credit-only operation. Missing/malformed quota
   or credits holds the queue. There are no credit/unlimited/floor override files.
2. **Ownership:** a task starts from a commit already in validated. Its entire
   delta since the registered base may contain only additions under its own
   `AKLT/W/KEY/`; foreign staged files, edits/deletions, executable/symlink files,
   foreign worktrees, shared build directories, and changed frozen hashes fail.
   Integration captures uncommitted owned additions before merging the exact tip.
3. **Sources before elaboration:** strip nested comments, ordinary/raw strings
   and character literals. Reject interpolation, admissions/axioms, native_decide,
   implemented_by, extern, unsafe/opaque, skipKernelTC, tactic/syntax/macro
   redefinitions, executable commands, IO/FS/Process and filesystem access.
   The policy conservatively rejects all run_cmd/run_elab/run_tac/run_meta,
   custom elaborators and simprocs, including pure ones.
4. **Resources:** outside the exact certificate allow-list, reject maxHeartbeats
   0 or greater than 1,000,000, and maxRecDepth 0 or greater than 10,000. These options must be
   literal numerals. A certificate exemption never permits effects or forbidden
   proof primitives. Certificate builds get their own 4 h deadline, excluded
   from ordinary per-task time; ordinary build/audit work shares an 1800 s task
   deadline. Timeouts kill only the tool's own validation process group and
   reject that task, preserving its inert attempt. Queue agents have no kill
   timeout. Disk is checked before commands and every five seconds during long
   validation commands; crossing the floor/growth budget defers integration.
5. **Kernel validation:** build every local AKLT module, including writer modules
   not imported by the bootstrap root, then run full `lake build AKLT`. Import all
   campaign modules for duplicate-name detection and audit all declarations in
   changed modules using Lean's module provenance and collectAxioms. Only propext,
   Classical.choice, Quot.sound are accepted. Full milestones audit every campaign
   declaration. The working tree is compared to HEAD before/after validation;
   orphaned private oleans are removed when MERGE changes source snapshots.
6. **Exact check:** verify the named frozen def has type Prop and the right module;
   compile the literal typed example; require a theorem declaration; run
   `#print axioms T` and collectAxioms. A type error means unproved; timeout or
   unavailable infrastructure defers the verdict. Report prose has no authority.
7. **Certificate cache:** hashes cover source bytes, the complete local import
   closure, toolchain pin/path, lakefile, and package manifest. Cache artifact
   hashes are checked on restoration. Lake's required final library build still
   checks dependency traces. Package immutability is an operational assumption.
8. **Milestones:** pin validated, verify clean sources, export in chunks below
   ARG_MAX (accounting for environment, argv pointers, and per-argument limits),
   require con-ron's explicit `--verified` acceptance, and run nanoda on each same
   export with only the three permitted axioms. Declines/nonzero exits fail.
   `unpermitted_axiom_hard_error=false` omits unused prelude axioms; a proof that
   uses one still fails. Export bytes are deleted after successful checking;
   SHA-256, sizes, requested/accepted counts, logs, configs and receipts remain.
9. **Lean process admission:** the private sysroot wraps every Lake-spawned Lean,
   serializes this campaign's Lean processes, and waits while eight external
   Lean processes are observed. The controller precreates the admission-lock inode;
   writers acquire it using a read-only file descriptor, so their sandbox needs
   no writable access to controller state. A real read-only `bwrap` regression
   checks this boundary without launching an agent. It uses `/proc` exact process names, never
   pgrep/pkill patterns. Other campaigns must respect their own process limits;
   this tool cannot reserve resources against an unrelated process racing it.

## Validation and limitations

The reproducible unit/integration suites are
`~/aklt/scratch/PORT1/v2/tests/` (builder tests and V-ORCH-1 regressions) and
`~/aklt/scratch/PORT1/v2/auditor/tests/` (the copied independent audit). It uses tiny Lean modules in disposable
`git clone --shared` clones, with symlinks to the read-only Mathlib package cache.
It exercises both accepting and rejecting paths for the gates, full external
validation, exact checks, two-step exhaustion, rejected-attempt inheritance,
batch conflict isolation, publication recovery, and generated final proofs.
Agent and tmux starts are mocked; no Codex/Claude process is launched. All test
logs stay under scratch, and disposable `.lake/build` directories are removed.
See `reports/PORT1/report-v2.md` for the audit findings, test adaptations, exact commands and final outcomes.

This is a trusted-operator campaign controller, not a hostile multi-user sandbox.
The source gate is intentionally conservative rather than a complete Lean parser.
It assumes the pinned prebuilt packages/toolchain stay immutable. Long-running
agents may themselves consume quota/credits after a launch; the requested reserve
formula and baseline stop new launches, and no running agent is killed. An
inactive Yale session log eventually becomes stale and holds the queue until a
fresh rate-limit event appears. Status needs a current compose inventory to
classify unladdered leaves semantically; it displays UNKNOWN/stale explicitly.
Composition handles closed named-Prop proof arguments, not arbitrary term
parameters or typeclass search, and the generated chain is always rechecked by
Lean. Independent validators were exercised on tiny exports, not a future full
AKLT certificate corpus; a checker decline remains a failed milestone.

The implementation adapts DBL's worktree isolation, first-line verdict handling,
exact-type checks, iterative batch isolation, verified exports, and composition
fixed point/term generation. It drops DBL's dynamic credit policies, multi-stage
ladder, speculative pipelines, repair/profile/hold frameworks and vendor
exceptions. The AKLT versions use one durable state document, short state locks,
one integrator, and explicit controller loops.
