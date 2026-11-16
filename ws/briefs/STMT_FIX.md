Orchestrator message: your statement layer (AKLT/Defs, AKLT/Blueprint/Top, Challenge V2) has been merged to `main`
and reviewed in groups by independent fidelity readers: 85 groups PASS; six groups report blocking problems with
these declarations: `ResponseTypedStatement` (/home/ubuntu/aklt/reports/FID_S002/report.md), `ReduceStatement`,
`InversionStatement`, `OperatorStructureStatement` (FID_S004), `binaryActionPolynomial` (FID_S059),
`H2DihedralStatement` (FID_S071), `Automaton10Statement`, `PhaseExpansionStatement` (FID_S072),
`stationaryCoefficient`, `stationaryApply` (FID_S083). In addition, the part architects and certificate engineers
who built on your layer list problems and proposed `…V2` replacements in their reports
(/home/ubuntu/aklt/reports/{BP_Q,BP_GAP,BP_WIN,BP_MOM,BP_REC,BP_H3M,BP_H1M,CERT_H1,CERT_H2,CERT_H3}/report.md —
sections on Top/Defs problems and ORCH-SUMMARY; BP_REC also has a Counterexample.lean). The assembled paper is
/home/ubuntu/aklt/manuscript-v2/.
Task: for every reported problem decide whether it is real (compare with the paper), and repair the statement layer
in place in your worktree (it is not frozen yet; first run `git merge main` is NOT possible for you — instead start
from the files as they are in /home/ubuntu/aklt/repo: copy AKLT/Defs, AKLT/Blueprint/Top and AKLT/Challenge/MainV2.lean
from there over your worktree copies before editing). Keep names stable where the meaning is unchanged; when a
statement changes, keep the old name for the corrected statement only if no proved theorem depends on the old
meaning (CERT_H2 has proved the H2 statements; `AKLT/Uniq` proves uniqueness) — otherwise add a `…V2` and say so.
Re-prove `mainV2_of_parts` and rebuild. Deliver in /home/ubuntu/aklt/reports/ARCH_0/: `stmt-fix.md` with first line
`STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`, one row per reported problem (source report, real?, change made,
declarations whose meaning changed), the list of downstream blueprint files that must be adapted, and an
ORCH-SUMMARY. Do not prove anything other than the top assembly.
