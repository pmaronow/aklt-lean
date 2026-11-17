STATUS: PROVED

Files changed (all under /home/ubuntu/aklt/wt/LW_REC019/AKLT/W/REC019/):
- R4/{Algebra,Conditioning,Expansion,FibreExpansion,Free,Geometry,Local,Main}.lean (new): verbatim copy of the proved REC004 development (/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/, commit 2205930, not yet on main), with namespace and imports renamed AKLT.W.REC004 -> AKLT.W.REC019.R4 and the in-file `#print axioms` lines removed. It imports the leaf AKLT.W.REC002.Bonds, which is on main. AKLT/Defs, AKLT/Blueprint/Rec and AKLT/W/REC002 are byte-identical between the two worktrees (diff -rq). Theorem AKLT.W.REC019.R4.main : AKLT.Blueprint.Rec.RemovedMeanIntervalsStatement.
- Main.lean: imports AKLT.W.REC019.R4.Main and adds
    removedMeanIntervals : RemovedMeanIntervalsStatement := R4.main
    residual_tripleLower : Residual_TripleLower    (from 41/50 <= responseI true)
    residual_pairUpper   : Residual_PairUpper      (from responseJ b <= 134/125)
    main : AlphaUniformStatement := main_of_residuals residual_tripleLower residual_pairUpper
  The earlier Sol content (alpha_bound_of_intervals, main_of_residuals, and the residual definitions) is unchanged. The previous Main.lean is backed up at /home/ubuntu/aklt/reports/LW/REC019/Main.sol.lean.bak.
- Audit.lean: adds #print axioms for R4.main, removedMeanIntervals, residual_tripleLower, residual_pairUpper and main, plus an exact-type `example`/`#check`.
No file outside AKLT/W/REC019/ was edited. `git status` shows only `?? AKLT/W/REC019/`.

Final theorem as it compiles:
  theorem AKLT.W.REC019.main : AKLT.Blueprint.Rec.AlphaUniformStatement

#print axioms (from lake build AKLT.W.REC019.Audit):
  AKLT.W.REC019.main depends on axioms: [propext, Classical.choice, Quot.sound]
  AKLT.W.REC019.R4.main, removedMeanIntervals, residual_tripleLower, residual_pairUpper: the same three axioms.

Build: cd /home/ubuntu/aklt/wt/LW_REC019 && lake build AKLT.W.REC019.Main
Result: Build completed successfully (8974 jobs), 80 s wall including the first build of the REC002 and R4 modules. No errors or warnings. lake build AKLT.W.REC019.Audit also succeeds (8975 jobs).
Source scan of AKLT/W/REC019: no sorry, admit, axiom, native_decide, implemented_by, unsafe, opaque, extern, #eval, run_cmd, initialize or macro_rules. The only heartbeat option is Sol's finite `set_option maxHeartbeats 800000 in` in SiteMoments.lean.

How it was closed: the three Sol residuals are true. Both moment residuals are linear consequences of the REC004 intervals. 41/50 <= I(true) = 1 + S/3 gives S >= -27/50, and J(b) = 1 + m/5 <= 134/125 gives m <= 9/25. Sol's main_of_residuals then gives the target. Residual_ConditionalMixture is not needed and remains an unproved definition only; no theorem depends on it.

Remaining residuals: none.
Note for the merge: once lw/REC004 is merged into main, R4/ duplicates AKLT.W.REC004 under another namespace. Main.lean can then import AKLT.W.REC004.Main and use AKLT.W.REC004.main in place of R4.main, after which R4/ can be deleted.
