# Rolling check of the orchestrator's actions (CK-NNN)

You are an independent checker of the work of the orchestrator (a Claude agent) of a Lean formalization campaign.
Read `ACTIONS.md` in your working directory: each entry gives an action, the command, the reason and the claimed
outcome. Verify each claim against the evidence (the Mac campaign folder mirrored at `/home/ubuntu/aklt/orchcheck-mirror/aklt-lean/`, including the
text mirror of the workstation in `/home/ubuntu/aklt/ (the workstation itself)`, and the log `/home/ubuntu/aklt/orchcheck-mirror/aklt-lean/RESUME.md`).
Also check that each action is consistent with the campaign rules in `RESUME.md` (author decisions are quoted there)
and with the default guide `/home/ubuntu/aklt/briefs/GUIDE.md`.

Look for: claims not supported by evidence; errors in commands (wrong paths, wrong flags, wrong effort, wrong
account); rule violations (redundant agents on one task, blind briefs that disclose earlier findings, hypotheses
introduced without the author, native_decide or forbidden axioms, pushes of unvalidated work, spending Codex credits);
risks to other campaigns' files on the workstation; missing steps the guide requires at this phase.

Do not modify anything outside your working directory. No network access is needed. Do not launch sub-agents.

Deliverable: `report.md` in your working directory, first line `STATUS: OK` or `STATUS: FINDINGS (n)`, then one
entry per finding: severity (Major = could invalidate later work or break a rule; Minor), the action concerned,
the evidence, and the fix you recommend. End with a list of the claims you verified.

The orchestrator transcript (JSONL) is at `/home/ubuntu/aklt/orchcheck-mirror/transcript.jsonl` (cite ORCH:<line>). Memories: `/home/ubuntu/aklt/orchcheck-mirror/memory/`. Write your report to `/home/ubuntu/aklt/reports/CK-004/report.md`.
