Orchestrator message — adaptation round. (1) The statement layer was repaired after independent fidelity review:
see /home/ubuntu/aklt/reports/ARCH_0/stmt-fix.md (changed declarations, new `…V2` contracts, `InputsStatementV2`,
`mainV2_of_partsV2`, and the list of downstream files to adapt). I have merged the repaired layer into your
worktree (`git merge main` done; your files are intact). (2) The assembled paper was refereed part by part with
the whole paper available; the reports relevant to you are /home/ubuntu/aklt/reports/REF2_5/report.md (§7),
REF2_6/report.md (§8 and Appendix C) and REF2_7/report.md (Appendix D) — read the one(s) for your part, in
particular their findings on statements (closure lemma neighbour pairs; domain of the short-trail orderings; the
exact within-type order and long-trail qualification in the phase expansion; the terminal-data hypothesis in the
stopped quotient intertwining).
Task: retarget your blueprint to the repaired statement layer. Keep every existing leaf file byte-identical (the
truth sweep found all current leaves true, and unchanged leaves will be frozen as they are); put changed or new
leaf statements in NEW files (`NodesV2*.lean`), give every changed leaf a new name ending in `V2`, and prove new
assembly theorems (`AssemblyV2.lean`) deriving the V2 Top targets (and whatever `mainV2_of_partsV2` needs from your
part) from the unchanged leaves plus the new ones. Do not prove leaves. Update `leaves.json` in your report
directory: mark each old leaf `kept` or `superseded` and list the new leaves with the usual fields; add a section
"Adaptation" to your report with a table old target → new target → changed leaves, and an ORCH-SUMMARY.
