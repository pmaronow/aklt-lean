Orchestrator message: the disk was enlarged (the author approved it): `/` now has about 620 GB free. I restored
`state/config.json` to the defaults (floor 150, budget 20) and removed my premature `state/disk-policy.json`.
Please now INSTALL v5 as you prepared it (tools/v5, dispatcher repointed, v1–v4 kept), and then apply this
operator policy on my behalf, exactly: `disk_abort_gb = 100`, `campaign_budget_gb = 350`, with
`state/disk-policy.json` = {"disk_abort_gb": 100, "campaign_budget_gb": 350, "reason": "production phase: leaf
worktree builds (~1 GB each, up to 48 live) and H1/H3 certificate pilots/production; volume grown to 1.7 TB with
the author's approval on 2026-11-16", "set_by": "orchestrator", "time": <now, ISO-8601 with timezone>}. Run your
post-install smoke checks (status, digest, budget-check, a dry `aklt-queue tick --dry-run`), confirm that the four
running loops (tmux aklt-queue, aklt-integrator, aklt-ladder, aklt-cleaner — started under v4) must be restarted
to pick up v5 and say exactly how (do not restart them yourself), and add a "resume6" section with an ORCH-SUMMARY.
