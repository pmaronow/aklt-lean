# V-ORCH-2 — re-audit of the campaign tooling (tools/v2) before first use

**Context.** The campaign tools in `/home/ubuntu/aklt/tools/v2/` (wrappers in `/home/ubuntu/aklt/bin/`, state in
`/home/ubuntu/aklt/state/`) were revised to fix the findings of the audit `/home/ubuntu/aklt/reports/V-ORCH-1/report.md`
(5 Blocking, majors). The builder's account is `/home/ubuntu/aklt/reports/PORT1/report.md`; the specification is
`/home/ubuntu/aklt/briefs/PORT1.md` and the campaign guide `/home/ubuntu/aklt/briefs/GUIDE.md`. Author's budget rule:
"Go to 0%, no credits" on the Yale Codex account (launch only while allowance remains above 0% after a reserve;
never on credits; never kill running agents).

**Task.** (1) For every Blocking and Major finding of V-ORCH-1, verify by test that it is fixed in v2 (reuse the
auditor test suite in `/home/ubuntu/aklt/scratch/V-ORCH-1/` and add cases where the fix could be bypassed).
(2) Re-run the complete checklist of V-ORCH-1 against v2 (gates accept correct input and reject incorrect input;
ladder Luna xhigh -> Sol max -> EXHAUSTED, one agent per leaf, escalation from exact-type check + first status line
only; explicit effort on resumes; budget/reset/credit/staleness behavior including `aklt-budget-check`; integrator
never loses uncommitted edits and validates before moving `validated`; full validation export + con-ron --verified
+ nanoda; pipefail; no agent kills; other campaigns untouched). (3) Check that the v2 install does not change
`tools/v1`, the credit baseline, `state/frozen.sha256`, or the repo. Work only under
`/home/ubuntu/aklt/scratch/V-ORCH-2/` and `/home/ubuntu/aklt/reports/V-ORCH-2/`; do not start daemons, agents or
tmux sessions; at most 4 Lean processes; disk ≤ 10 GB (delete `.lake/build` of your clones at the end).

**Deliverable.** `/home/ubuntu/aklt/reports/V-ORCH-2/report.md`, first line `STATUS: READY` or
`STATUS: NOT READY (n blocking)`; then a table finding → fixed? (test, evidence); new findings (Blocking / Major /
Minor) with file:line, test and fix; the passed checklist with commands. Do not launch sub-agents.
