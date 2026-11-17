Orchestrator message — phase 3. Your pilot is accepted. Do two things, in this order of priority:
1. MERGE SET (needed first, quickly): write `/home/ubuntu/aklt/reports/<your key>/merge-set.txt` listing exactly the
   source files (relative to your worktree root) that must go into the main repository so that your open leaf
   statements, checker definitions, exporters and assembly theorems are available to other writers: everything
   hand-written, NOT the generated data/check modules. Make sure that set builds on its own from a clean checkout
   of `main` plus the set (state the root module to build and how the generated modules are attached later:
   the separate Lake library target and its directory), that the ordinary `lake build` of the `AKLT` library is
   not slowed by it, and that the statements refer to the current statement layer on `main` (`git merge main`
   has been done in your worktree by the orchestrator if you see new commits; otherwise copy nothing — just report
   mismatches). Also write `leaves-open.json`: the open closed-Prop leaves in the usual format
   ({"lean_name","module","paper_label","difficulty","suggested_proof_route","trap_note"}), only real proof
   obligations (no data blocks).
2. PRODUCTION: run the complete finite numeric work for all remaining cases with your generators (use
   `--compact-sources`; up to 32 Lean processes and 300 GB RAM; the machine is also running many proof writers, so
   expect CPU contention; keep free disk above 100 GiB), verify every generated check module was kernel-checked
   (exit status and axioms), and record receipts (module counts, hashes of data inputs, times). Keep the built
   `.olean` files of the check modules (they will be needed for the final assembly) but compact sources.
Report: update `report.md` (first line `STATUS: COMPLETE | PARTIAL (reason)`) with a "phase 3" section and an
ORCH-SUMMARY. Still no written leaf proofs by you.
