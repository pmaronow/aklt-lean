# V-ORCH-1 — quality audit of the campaign tooling before first use

**Context.** A Lean 4 formalization campaign in `/home/ubuntu/aklt` will run agent writers, an integrator and
validators with the tools just installed in `/home/ubuntu/aklt/tools/v1/` (wrappers in `/home/ubuntu/aklt/bin/`,
state in `/home/ubuntu/aklt/state/`). The specification they were built to is
`/home/ubuntu/aklt/briefs/PORT1.md`; the builder's report is `/home/ubuntu/aklt/reports/PORT1/report.md` and its
development area `/home/ubuntu/aklt/scratch/PORT1/`. The general campaign guide is
`/home/ubuntu/aklt/briefs/GUIDE.md`; the author's budget rule is "Go to 0%, no credits" (launch only while the Yale
Codex allowance is above 0% after a reserve for running agents; never launch on credits; never kill running agents).

**Task.** Confirm, by reading the code and by running unit tests in a throwaway area under
`/home/ubuntu/aklt/scratch/V-ORCH-1/` (clone the repo there; link Mathlib packages from
`/home/ubuntu/aklt/repo/.lake/packages` by symlink, never modify them), that each component meets the
specification: each gate accepts correct input and rejects incorrect input (forbidden tokens, effect guard,
frozen-file hashes, axiom audit, writer path restrictions, heartbeat/recursion limits and the certificate-module
allow-list, exact-type check, per-task timeout attribution, culprit removal); the ladder is Luna (xhigh) → Sol (max)
→ EXHAUSTED with exactly one agent per leaf and escalation driven only by the exact-type check and the report's
first status line; resumes pass effort explicitly; the budget gate implements the author's rule (including a stale
or missing quota reading, a reset, and a credit decrease — it must refuse to launch when the reading is older than
15 minutes or credits fall); the integrator never operates in a checkout with uncommitted edits and validates
before moving `validated`; full validation runs export + con-ron --verified + nanoda and fails loudly; the status
script and digest work; shell pipelines propagate failures (pipefail); no tool can kill agents or edit other
campaigns (`/home/ubuntu/dbl`, `/home/ubuntu/sharp`, `/home/ubuntu/md`, `/home/ubuntu/sal` must be untouched).
Do not start any daemon, agent, or tmux session, and do not modify anything outside your scratch and report dirs.
At most 4 Lean processes; disk ≤ 10 GB (delete `.lake/build` of your clones at the end).

**Deliverable.** `/home/ubuntu/aklt/reports/V-ORCH-1/report.md`, first line `STATUS: READY` or
`STATUS: NOT READY (n blocking)`; then findings (Blocking / Major / Minor) with the file:line, the test that shows
it, and the fix; then the list of checks that passed with their commands.
