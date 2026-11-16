# PORT1 — campaign tooling for the AKLT Lean formalization (adapt the design-based pipeline)

**Goal.** Build the workstation tooling for a new Lean formalization campaign in `/home/ubuntu/aklt`, by adapting
the production pipeline of an earlier campaign, `/home/ubuntu/dbl/bin` (Python modules `dbl_*.py` and wrappers
`dbl-*`), which ran writer waves, integration and validation successfully. Read it to understand it; do NOT modify
anything under `/home/ubuntu/dbl`, `/home/ubuntu/sharp`, `/home/ubuntu/md`, `/home/ubuntu/sal` or any other
campaign. You may read `/home/ubuntu/sharp/tools/current` for ideas, but keep the new tools simple and robust:
prefer fewer moving parts over defence in depth.

**The new campaign.** Repo `/home/ubuntu/aklt/repo` (Lean 4.35.0-rc2, Mathlib 065356127b; library `AKLT`;
branch `main`; Mathlib packages prebuilt in `repo/.lake/packages`, shared read-only by worktrees via symlink —
see `/home/ubuntu/aklt/bin/aklt-mkwt`). Agents: Codex CLI via `/home/ubuntu/bin/codex_sol.py` (model gpt-6.1-sol)
and `/home/ubuntu/bin/codex_luna.py` (gpt-6-luna), with `CODEX_HOME=/home/ubuntu/.codex-yale`; transient-error
retries via `/home/ubuntu/bin/sol-retry.py` / `luna-retry.py` (copy and adapt; their scratch path points at another
campaign). Namespaces: frozen statement layer under `AKLT/Challenge/`, `AKLT/Defs/`, `AKLT/Blueprint/<Part>/`
(statements + proved assemblies), writer work under `AKLT/W/<KEY>/` (one directory per task key).

**Required features** (install under `/home/ubuntu/aklt/tools/v1/` with wrappers in `/home/ubuntu/aklt/bin/`, all
named `aklt-*`; state under `/home/ubuntu/aklt/state/`; logs under `/home/ubuntu/aklt/logs/`):
1. `aklt-mkwt` (exists; keep or improve) and a cleaner that deletes `.lake/build` of finished task worktrees
   (never the repo's, never worktrees named MERGE*, VENDOR*, PROBE*).
2. A launch queue: tasks with model (luna|sol), effort, brief file, worktree, writable report dir; launched in tmux
   sessions; completion flags `~/aklt/flags/<KEY>.done`; resumes must pass the original effort explicitly.
   Concurrency caps (config file): Lean-writing agents ≤ 48, Sol ≤ 24, total ≤ 56. A budget gate reading the Yale
   Codex `rate_limits` (newest `token_count` event in `~/.codex-yale/sessions/**/rollout-*.jsonl`): launch only while
   `remaining% − 0.3 × running_agents − 1 > FLOOR`, with FLOOR = 0 (author's rule: "Go to 0%, no credits" —
   never launch on credits; never kill running agents). Also refuse to launch when `credits.balance` has decreased
   since the campaign baseline (record the baseline at install).
3. Proof ladder per leaf: Luna (xhigh) → Sol (max) → EXHAUSTED. One agent per leaf at a time (no redundant
   attempts, ever). The Sol attempt starts in a worktree from `validated` that contains Luna's attempt, and its
   brief lists that attempt and Luna's verdict. Escalation is driven by the exact-type check below, never by words
   in reports; only the report's first line (`STATUS: PROVED | PROVED FROM DEPS | PARTIAL | FALSE`) is parsed.
4. Exact-type check: for a claimed leaf `N : Prop` (a frozen `def ... : Prop` in the Blueprint) and a theorem
   `T`, compile `example : N := T` in a scratch file importing the task's modules, plus `#print axioms T` (only
   propext, Classical.choice, Quot.sound allowed).
5. Integrator daemon: merges finished tasks into `validated` (batching, culprit removal iterated until the batch
   validates, then one-at-a-time fallback), never in the main checkout's working tree with uncommitted edits (use a
   MERGE worktree). Fast validation per batch: full `lake build AKLT`, frozen-file hashes (Challenge, Defs,
   Blueprint statement files listed in `state/frozen.sha256`), a forbidden-token scan of new/changed files
   (`sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `macro_rules`
   redefining tactics, `set_option debug.skipKernelTC`), an effect guard (no `#eval`, `IO`, `initialize`,
   `run_cmd`/`run_elab` with effects, file-system or process access in Lean sources — strip comments and strings
   first), and an axiom audit of new declarations. Writers may only add files under their own `AKLT/W/<KEY>/`.
   A per-task build timeout (default 1800 s) that rejects the task attributably instead of wedging the queue.
   **Certificate modules:** the campaign will have kernel-heavy computation modules (exact certificate checks by
   kernel reduction). Support an allow-list `state/certificate-modules.txt` of module paths that may use
   `set_option maxHeartbeats 0` / `maxRecDepth` and get a longer timeout (default 4 h) and are built once and
   cached by content hash; everywhere else reject `maxHeartbeats 0`, `maxHeartbeats` > 10^6, `maxRecDepth` > 10^4.
6. Full validation at milestones: `leanexport` + `con-ron --verified` + `nanoda_bin` on the export of the validated
   head (binaries are in `~/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/`); chunk the export if the name
   list exceeds ARG_MAX. Before validation, compare the working tree with HEAD.
7. A status script `aklt-status` printing in one screen: queue, running agents (by model/effort/key), ladder
   counts, integrator state, last validated commit, disk free (alarm < 120 GB), memory, Yale quota and credits,
   stale flags, unladdered open leaves, and any EXHAUSTED leaves.
8. A digest written every 10 min to `logs/digest.log` by a tmux loop (no model calls).
9. A compose tool: dump of theorem heads (conclusion + named-Prop hypotheses) for proved nodes and a fixed-point
   computation of which Blueprint nodes are closed, plus a generator of the explicit term chain for the top
   statement that Lean then checks (see `dbl_compose.py`, `dbl-genfinal`).

**Rules.** Develop under `/home/ubuntu/aklt/scratch/PORT1/` and install into `tools/v1` + `bin/` only at the end,
in one step. Do not start any daemon (I will). Write unit tests that confirm each gate accepts correct input and
rejects incorrect input (use tiny throwaway Lean files and a throwaway clone of the repo under scratch; delete
their `.lake/build` afterwards). Disk budget: 20 GB; abort if free disk on `/` drops below 150 GB. At most 8 Lean
processes at a time (other agents share the machine). Never use `pkill -f`/`pgrep -f` with patterns that can
match your own command line. Do not launch sub-agents or any Codex/Claude agent.

**Deliverable.** `/home/ubuntu/aklt/reports/PORT1/report.md`, first line `STATUS: COMPLETE` or
`STATUS: PARTIAL (reason)`; then a README of every tool (usage, state files, invariants, what each gate checks),
the test results (commands and outcomes), what was taken from `dbl` and what was changed, and known limitations.
Also install `tools/v1/README.md`.
