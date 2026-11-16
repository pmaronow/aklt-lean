# V-ORCH-4 — focused re-audit of the integrator race fix (tools v4 or latest)

**Context.** `/home/ubuntu/aklt/reports/V-ORCH-3/report.md` (tests in `/home/ubuntu/aklt/scratch/V-ORCH-3/`) left one
Blocking issue in the campaign tools: a write to an ignored file in MERGE arriving after the cleanliness check was
overwritten by the merge. The builder's fix is described in the "resume4" section of
`/home/ubuntu/aklt/reports/PORT1/report.md` (latest tools under `/home/ubuntu/aklt/tools/`, wrappers
`/home/ubuntu/aklt/bin/`). The repo's lakefile now has `globs = ["AKLT", "AKLT.+"]`, and benchmark modules were
moved to `bench/` outside the library.

**Task.** Verify by test that the race is closed (disposable-checkout merges; `validated` advanced only from a
validated disposable commit; the auditor's interleaving regression and variants), that the validator works with
the current repo layout (root module, globs, `bench/` ignored), re-run the complete V-ORCH-2/3 suites against the
installed tools, and run one end-to-end dry run on a disposable clone of `/home/ubuntu/aklt/repo` at `main`:
integrate a tiny correct writer task and reject a tiny incorrect one. Work only under
`/home/ubuntu/aklt/scratch/V-ORCH-4/` and `/home/ubuntu/aklt/reports/V-ORCH-4/`; no daemons, agents or tmux
sessions; at most 4 Lean processes; disk ≤ 10 GB.

**Deliverable.** `/home/ubuntu/aklt/reports/V-ORCH-4/report.md`, first line `STATUS: READY` or
`STATUS: NOT READY (n blocking)`; findings with tests; passed suite; ORCH-SUMMARY (≤ 20 lines). No sub-agents.
