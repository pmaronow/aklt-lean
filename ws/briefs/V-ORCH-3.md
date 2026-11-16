# V-ORCH-3 — focused re-audit of two tooling fixes

**Context.** `/home/ubuntu/aklt/reports/V-ORCH-2/report.md` (tests in `/home/ubuntu/aklt/scratch/V-ORCH-2/`) found in
the campaign tools (`/home/ubuntu/aklt/tools/v2/` or a later `v3`, wrappers `/home/ubuntu/aklt/bin/`): (a) a
remaining Blocking issue — ignored uncommitted non-Lean files in the MERGE worktree can be overwritten by
integration; (b) a Major issue — full validation cannot export private or Unicode-named declarations. The builder's
account of the fixes is the "resume3" section of `/home/ubuntu/aklt/reports/PORT1/report.md`. The manual gate
`/home/ubuntu/aklt/bin/aklt-gate` now only execs `aklt-budget-check` (check that too).

**Task.** Verify by test that (a) and (b) are fixed and cannot be bypassed (add cases: other extensions, nested
ignored directories, files ignored via .git/info/exclude, names with `«»`, private and auxiliary names, very many
names exceeding ARG_MAX), re-run the full V-ORCH-2 suite against the installed tools, and confirm nothing else
regressed. Work only under `/home/ubuntu/aklt/scratch/V-ORCH-3/` and `/home/ubuntu/aklt/reports/V-ORCH-3/`; do not
start daemons, agents or tmux sessions; at most 4 Lean processes; disk ≤ 10 GB.

**Deliverable.** `/home/ubuntu/aklt/reports/V-ORCH-3/report.md`, first line `STATUS: READY` or
`STATUS: NOT READY (n blocking)`; findings with tests; the passed suite. Do not launch sub-agents.
