STATUS: COMPLETE

Installed the AKLT v1 tooling at `/home/ubuntu/aklt/tools/v1/`, with 18 named commands and the `aklt-tool` dispatcher in `/home/ubuntu/aklt/bin/`. Installation completed at 2026-11-16T03:08:53.627323+00:00. No daemon, tmux agent session, Codex agent, Claude agent, or sub-agent was started by PORT1.

The Yale credit baseline was recorded at installation: `85075.0939670000`. The existing author-owned `state/frozen.sha256` was verified and preserved byte for byte. It now lists Challenge/Main.lean and Challenge/Sanity.lean. The author's `validated` ref is `6ef9d9c2d9587a4522a2e942cc98ef58dcfe0921`; PORT1 did not create or advance the real repository's refs or alter its working files. The installed controller state starts with an empty queue and an uninitialized integrator; its first tick reconciles the existing ref. `aklt-init` is available for an explicit first bootstrap if a campaign has no validated ref.

The full tool README follows. `aklt-tool COMMAND [ARGS...]` is the common dispatcher behind the named wrappers; `_run KEY` is its internal reserved-task entry point, not a second launch interface.

# AKLT campaign tools v1

Python 3 standard library, Git, tmux, and the pinned Lean toolchain are the only
dependencies. The public commands are `~/aklt/bin/aklt-*`; implementation modules
live here. `AKLT_HOME` defaults to `/home/ubuntu/aklt` and may select a disposable
campaign for testing. Imports, installation, and `--help` never start a daemon or
an agent. The main checkout is never used as the integration working tree.

## Start-up and normal operation

Installation records the current Yale credits baseline, configuration, and initial
frozen hashes. An existing author-owned frozen manifest is verified and retained
byte for byte. It **does not create or advance a repository ref**, run validation,
or start tmux. The first operator action is:

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
| `aklt-budget` | Prints the newest Yale quota, credits, launch margin, and hold reasons as JSON. Exit 0 means launch quota is available; exit 2 means the budget gate holds. It does not launch anything. |
| `aklt-queue` | `[tick] [--dry-run] [--loop]`; `add TASK.json`; `list`; `recover KEY [--finished]`. A tick launches eligible tasks in tmux sessions `aklt-KEY`. Dry-run evaluates one next eligible task without reserving or launching it. `recover` settles an explicitly selected lost session only after tmux, runner-lock and live-worktree-process checks; it never relaunches. |
| `aklt-ladder` | `[tick] [--loop]`; `add LEAF.json`; `list`. The two possible attempts are `KEY_L` (Luna/xhigh) and `KEY_S` (Sol/max). Success or exhaustion is determined by compiled exact checks after integration. |
| `aklt-sol-retry` | Internal queue runner: `EFFORT SEARCH(0\|1) -- run\|resume DRIVER_ARGS`, including explicit `-e EFFORT`. Requires a matching running queue reservation (`AKLT_TASK_KEY`). Retries transient transport/capacity errors up to eight times by resuming the same session. |
| `aklt-luna-retry` | Same interface and behavior, using the Luna driver. These wrappers do not create new attempts. |
| `aklt-freeze` | `[--blueprint AKLT/Blueprint/Part/Statements.lean ...]`: records clean committed statement files in `state/frozen.sha256`, retaining and verifying every previous entry. No hash replacement or unfreezing. |
| `aklt-effect-guard` | `FILE_OR_DIR ...`: lexically scans Lean files; no Lean execution. It applies the resource-option exception only to canonical main-repo paths explicitly present in the certificate list. Integration validates worktree paths relative to their roots. |
| `aklt-exact` | `KEY NODE THEOREM STATEMENT_MODULE [--dep NODE ...]`: builds task imports, checks the frozen node, compiles `example : NODE := THEOREM`, prints its axioms, and audits the theorem's declaration kind and axioms. Exit 2 means unproved. With declared dependencies it additionally tries the exact arrow type `D₁ → ... → NODE`. No report text can create a success. |
| `aklt-integrator` | `[--once\|--loop]`: one integration tick by default; batches finished tasks, removes identified culprits iteratively, and then tries deferred/unattributed tasks one at a time. Uses only the detached `wt/MERGE` for merge/reset/validation. Publication uses a journal and a compare-and-swap ref update. |
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
| `state/config.json` | Caps and durations. Defaults: Lean writers 48, Sol 24, total 56, task 1800 s, certificate 14400 s, milestone checker 14400 s, batch 12, controller tick 20 s. Caps may only be lowered. Floor 0, reserve 0.3 and margin 1 are fixed policy. Quota freshness defaults to 1800 s. Disk abort floor defaults to 150 GB; status alarm is 120 GB. |
| `state/credits-baseline.json` | Numeric decimal balance, event time/source, and installation time. Never automatically rebased after spending. |
| `state/disk-baseline.json` | Existing non-repo campaign bytes at installation; monitored growth budget is 20 GB. Symlinked package caches are not traversed. |
| `state/frozen.sha256` | SHA-256 hashes of all Challenge/Defs files and explicitly registered Blueprint statement files. Empty initially if no statement layer exists. |
| `state/certificate-modules.txt` | One exact repo-relative `.lean` path (or dotted module name) per line; blank lines and `#` comments accepted. No globs or directory exemptions. Only these files receive resource-option and build-time exemptions. |
| `state/campaign.json` | Versioned authoritative tasks, leaves, integrator journal and last validated receipt. Updates use `state.lock`, atomic replacement, and fsync. Back it up together with frozen hashes and the credits baseline. |
| `state/PAUSE` | Presence pauses new queue launches. |
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
during integration retries validation, never the writer. A crash on either side
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
   Re-evaluate before every launch, respecting all three caps and leaf ownership.
   Let remaining be the minimum remaining percentage of the available primary and
   secondary Yale windows. Launch iff `remaining - 0.3*running - 1 > 0`, credits
   have not decreased below the install baseline, the snapshot is fresh, and no
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
   Lean processes are observed. It uses `/proc` exact process names, never
   pgrep/pkill patterns. Other campaigns must respect their own process limits;
   this tool cannot reserve resources against an unrelated process racing it.

## Validation and limitations

The reproducible unit/integration suite is
`~/aklt/scratch/PORT1/tests/test_port1.py`. It uses tiny Lean modules in disposable
`git clone --shared` clones, with symlinks to the read-only Mathlib package cache.
It exercises both accepting and rejecting paths for the gates, full external
validation, exact checks, two-step exhaustion, rejected-attempt inheritance,
batch conflict isolation, publication recovery, and generated final proofs.
Agent and tmux starts are mocked; no Codex/Claude process is launched. All test
logs stay under scratch, and disposable `.lake/build` directories are removed.
See `reports/PORT1/report.md` for the exact commands and final outcomes.

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


## PORT1 verification record

All development, clones, test output, and deployment preparation stayed under `/home/ubuntu/aklt/scratch/PORT1/`. The final deployment wrote only tools, wrappers, and state; this report is under the explicitly authorized reports directory. Other campaigns were read for reference only. The supplied campaign-local `bin/sol-retry.py` and `bin/luna-retry.py` were read and adapted; the original files remain intact.

Commands were run from `/home/ubuntu/aklt/scratch/PORT1`:

| Command / check | Outcome and evidence |
| --- | --- |
| `python3 -u -m unittest discover -s tests -v` | **28 tests passed**, 193.095 s. [Full log](/home/ubuntu/aklt/scratch/PORT1/evidence/test-final.log). |
| `PYTHONPATH=tests python3 -u -m unittest test_port1.RepoGates.test_luna_actual_proof_stops_even_when_report_partial test_port1.RepoGates.test_composition_generator_and_full_independent_validation` | **2 passed**, 230.259 s, after adding composition aliases for exact proofs with definitionally equal theorem heads. [Log](/home/ubuntu/aklt/scratch/PORT1/evidence/compose-final.log). |
| `PYTHONPATH=tests python3 -u -m unittest test_port1.RepoGates.test_composition_generator_and_full_independent_validation` | **1 passed**, 35.007 s, after making the fixture discard author source files inside its disposable clone. This keeps future unit tests tiny even as the real campaign grows. [Log](/home/ubuntu/aklt/scratch/PORT1/evidence/current-head-fixture.log). |
| `python3 -m compileall -q stage/tools tests install.py` | Passed. Installed modules exclude development bytecode. |
| Original bootstrap clone: `fast(c, clone, HEAD, logs, all_declarations=True)` | Passed with the original `import Mathlib`, using the real prebuilt package symlink and private build outputs. [Log](/home/ubuntu/aklt/scratch/PORT1/evidence/production-smoke.log). |
| Staged and installed command help checks | All **19 entry points** returned exit 0 with `--help`; no model calls or tmux starts. [Installed results](/home/ubuntu/aklt/scratch/PORT1/evidence/installed-smoke.json). |
| Installed file manifest + `frozen(Context(), repo)` | All 11 installed source/document hashes matched; the existing frozen manifest matched the author's files. |
| Installed `aklt-status` | Exit 0, compact live status; quota/credits and historical unknown flags displayed. [Captured screen](/home/ubuntu/aklt/scratch/PORT1/evidence/installed-status.txt). |
| `python3 install.py` | Successful final deployment in one invocation, recording baseline/configuration and retaining the author manifest. [Receipt](/home/ubuntu/aklt/scratch/PORT1/evidence/install.json). Earlier attempts stopped before public tools/wrappers were replaced: one detected newly added author state, and one encountered separate sandbox filesystems. The final installer handles both cases. |
| Throwaway build cleanup and resource check | **Zero** remaining throwaway `.lake/build` directories. Scratch use 123.8 MB, within the 20 GB budget; `/` free 198.2 GB, above the 150 GB abort floor. Shared packages were never traversed for cleanup. [Resource record](/home/ubuntu/aklt/scratch/PORT1/evidence/final-resources.json). |

The initial development pass found an invalid synthetic ARG_MAX test setup and a real duplicate-declaration integration hole. Both were corrected before the passing runs. The duplicate-name audit now imports every campaign module, even when the axiom audit targets only changed declarations.

The suite exercises accepting and rejecting inputs for source/effect/resource gates, frozen hashes and ownership, dirty HEAD checks, all three concurrency caps, the strict quota inequality, stale/missing quota, credit spending, brief immutability, persistent launch reservation, exact types and axioms, conditional dependencies, certificate cache/hash corruption, timeout attribution, and cleanup boundaries. It also exercises iterative culprit removal, unattributed one-at-a-time fallback, real duplicate-import rejection, publication-journal recovery, both ladder outcomes, rejected Luna inheritance, false success reports, actual proofs despite PARTIAL reports, and deferred infrastructure verdicts. Actual tmux starts and agent subprocesses are mocked.

A successful scratch milestone exported 99 campaign declarations into 157,016,579 bytes. `con-ron --verified --jobs=1` accepted 28,560 declarations; nanoda reported **no typechecker errors** over 30,146 declarations. The recorded export included the author's Challenge layer: **true**. Nanoda also reported its harmless pretty-printer diagnostic “Unable to print axioms”; its typecheck and exit status succeeded. The export SHA-256, checker logs/configuration, and receipts are retained in [independent-checkers.json](/home/ubuntu/aklt/scratch/PORT1/evidence/independent-checkers.json). Successful export bytes are removed, as designed.

## Adaptation from DBL

- `dbl_common.py`, `dbl_worktree.py`, and process/receipt patterns supplied the worktree, atomic-state, timeout, and publication concepts. AKLT shares only the prebuilt packages, keeps private outputs, serializes its Lean children, and uses one state document with short state locks.
- `dbl_guard.py` supplied the nested-comment/string lexer. AKLT uses a smaller conservative token/effect policy, explicit certificate options, and regular-file ownership checks; it omits DBL's vendor and registration-exemption frameworks.
- `dbl_quota.py` supplied durable queue/reservation ideas. AKLT reads Yale rollout events directly, uses the author's exact fixed reservation formula and three caps, records an immutable credit baseline, and has no credit-mode or unlimited-mode override.
- `dbl_ladder.py` and `dbl_ladder_check.py` supplied exact-type escalation. AKLT has exactly Luna/xhigh then Sol/max, keeps report text advisory, preserves failed source as inert data in validated, and never creates another attempt for the same tier/leaf.
- `dbl_integrator.py` supplied iterative culprit removal and fallback. AKLT validates and merges in detached MERGE, journals compare-and-swap publication, attributes task timeouts, and drops speculative workers, repair controllers, profile migration, and multi-stage orchestration.
- `dbl_validate.py` supplied full-library builds, module-provenance axiom audits, and verified exports. AKLT adds nanoda, byte-aware ARG_MAX chunking, duplicate declaration checks, content/dependency-keyed certificate caching, and clean-HEAD comparisons.
- `dbl_compose.py` / `dbl-genfinal` supplied the named-Prop rule dump, least fixed point, and explicit term chain. AKLT pins the receipt, includes compiled aliases for successful exact proofs whose heads unfold to the target, and recompiles/audits generated terms.
- DBL operations supplied cleanup/digest ideas. AKLT's cleaner deletes build directories only and explicitly protects all MERGE*, VENDOR*, PROBE* worktrees. Its digest is an opt-in tmux loop every ten minutes with no model calls.
- The **current AKLT-local** retry wrappers supplied the eight transient retries and unique `scratch/retry/MODEL-SESSION-N.md` convention. DBL's private-driver loader supplied model verification and isolated run/session paths. AKLT additionally records the original task/model/effort binding and requires an explicit matching effort on resume.

## Remaining operational limits

The README's limitations apply. In particular, no live agent or daemon launch was exercised because the brief prohibited them; the launch boundary was tested with mocks. Future kernel-heavy certificate corpora and four-hour workloads have not been run. Package/toolchain immutability and cooperative external process limits remain operational assumptions. The first Yale index scanned 14,010 historical rollout files (about 24 GB of existing log bytes); subsequent snapshots reuse per-file metadata and only reparse changed files. This reads existing logs and does not copy them into the campaign.

A fresh semantic inventory requires `aklt-compose` after author Blueprint changes; status identifies stale or unavailable inventory. Its unladdered candidates are closed named-Prop nodes with no incoming assembly rule. Composition intentionally excludes arbitrary term parameters, quoted/unicode metadata names, and implicit typeclass synthesis. The source guard deliberately rejects pure custom elaboration and interpolation as well as effectful variants. These restrictions are documented rather than silently weakening the proof gates.

No further installation, author-file change, daemon start, or model launch is pending from PORT1.
