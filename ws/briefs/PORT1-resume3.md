Orchestrator message: the re-audit /home/ubuntu/aklt/reports/V-ORCH-2/report.md (tests and evidence in
/home/ubuntu/aklt/scratch/V-ORCH-2/) found two remaining problems in your tools. Fix both in tools/v2 (or install
tools/v3 if you prefer; keep v1/v2 for the record and repoint the wrappers):
1. Blocking 3 (remaining): ignored uncommitted non-Lean files in MERGE can be overwritten by integration. Refuse or
   back up ANY ignored uncommitted file that a merge/reset could replace, regardless of extension (exempt only
   tool-owned build/cache paths), and keep the auditor's regression test.
2. Major: full validation cannot export private or Unicode-named declarations (see the report's "Major" section);
   make the export inventory and leanexport invocation handle them, with a regression test.
Blocking 5 (the manual gate) is handled: /home/ubuntu/aklt/bin/aklt-gate now just execs aklt-budget-check; do
not modify it. Re-run all suites (yours and the auditor's) and update /home/ubuntu/aklt/reports/PORT1/report.md
(add a "resume3" section). Same writable roots and rules as before; do not start daemons or agents.
