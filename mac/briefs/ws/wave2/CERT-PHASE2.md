Orchestrator message — phase 2 of your certificate task. Your phase-1 report is accepted as a design and prototype.
Now make the route production-ready, still without writing leaf proofs yourself (those go to another model first):
1. Implement everything your report lists as a missing implementation or as handled only for selected prototypes
   (exporters for all cases/parities, generators, indexes, frontier replay, batching), as executable Lean checkers
   and Python exporters, so that the complete finite work can be generated and kernel-checked mechanically.
2. Fix the exact closed statements of every open soundness/refinement/coverage obligation (the bridge from the
   Boolean checks to the Defs statements) in `leaves.json`, small enough for one writer each, with the proved
   ASSEMBLY from those leaves plus the check modules to your Top targets. Note that the statement layer is being
   revised for a few declarations flagged by reviewers (see /home/ubuntu/aklt/reports/ARCH_0/stmt-fix.md when it
   appears); design your bridge so that it survives such corrections, and say which of your leaves depend on them.
3. Run a production PILOT that is representative, and measure it: for (H1) all blocks of 100 patterns spread
   over sizes (including the largest), constructor and positivity; for (H3′) one complete case (all planes, all
   Bellman rows, its automaton check, its full prefix with frontier sharding). Use up to 24 Lean processes and
   300 GB RAM for the pilot (the machine is otherwise lightly loaded); keep disk under your budget and delete
   build outputs you do not need. Keep generated data and check modules OUT of the `AKLT/` library tree (put
   them under a separate top-level directory, e.g. `CertData/H1/…`, with its own Lake library target), so that
   ordinary builds of the proof library stay fast.
4. Report: updated production plan (modules, CPU-hours, wall time at 24 and at 48 processes, memory, disk), the
   pilot measurements, the final leaf list, and an ORCH-SUMMARY (≤ 25 lines). First line
   `STATUS: COMPLETE | PARTIAL (reason)`.
