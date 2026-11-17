Orchestrator message: one operational policy in your tools must become operator-adjustable, because the campaign
has entered its production phase. Currently `aklt_common.py` hard-codes `disk_abort_gb >= 150` and
`campaign_budget_gb <= 20` ("disk limits may only be tightened"), and the campaign-budget check counts all of
`wt/`, `scratch/`, … against a 20 GB growth budget. A leaf wave needs ~1 GB of private build per live worktree
(up to 48 at once) and the certificate pilots hold tens of GB under `wt/`, so every `aklt-ladder add` now aborts.
Change (as tools/v5, wrappers repointed, v1–v4 kept): the disk floor and campaign budget are read from
`state/config.json` with hard bounds `disk_abort_gb >= 40` and `campaign_budget_gb <= 400`; any change relative to
the installation defaults must be accompanied by an operator record `state/disk-policy.json`
{"disk_abort_gb":…, "campaign_budget_gb":…, "reason":…, "set_by":"orchestrator", "time":…} whose values match
the config (otherwise refuse); the status/digest print the active policy and free space; nothing else changes.
Add regression tests (default policy unchanged without the record; mismatch refused; bounds enforced; a set policy
works) and re-run your suites. Do not start daemons or agents. Add a "resume5" section to
/home/ubuntu/aklt/reports/PORT1/report.md with the diff summary and test results, ending with an ORCH-SUMMARY.
