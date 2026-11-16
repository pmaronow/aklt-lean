Orchestrator message: an independent audit of your installed tools is at /home/ubuntu/aklt/reports/V-ORCH-1/report.md
(status NOT READY, 5 blocking) with test evidence in /home/ubuntu/aklt/scratch/V-ORCH-1/evidence/. Fix every Blocking
and Major finding (and the Minor ones where cheap), in scratch first, then reinstall as tools/v2 (keep v1 untouched for
the record) with wrappers in bin/ pointing to v2. Blocking 5 concerns /home/ubuntu/aklt/bin/aklt-gate, which is the
orchestrator's manual gate: do not edit it; instead make sure your own budget implementation is the one the queue
uses, and provide aklt-budget-check as a command-line equivalent (same logic, exit 0 iff a launch of N new agents is
allowed) that the orchestrator can switch to. Re-run all tests (yours and the auditor's, from the evidence folder)
and report. Same writable roots and rules as before; do not start daemons or agents.
