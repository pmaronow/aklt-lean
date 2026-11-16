# PROBE2 — time the proposed kernel certificate checkers (Lean 4.35.0-rc2 + Mathlib 065356127b)

**Context.** A feasibility study proposed kernel-only certificate designs for three computer-assisted inputs of a
proof we will formalize to Palomar standards (no native_decide/implemented_by/extern/unsafe/axiom/sorry/opaque;
axioms only propext, Classical.choice, Quot.sound). Its report is `/home/ubuntu/aklt/compfeas/report.md` (read the
H1, H2, H3′ sections and the "Ranked workstation probe plan"); its uncompiled Lean probe files are in
`/home/ubuntu/aklt/compfeas/probes/` (README.md there). An earlier probe of basic kernel speeds is
`/home/ubuntu/aklt/reports/PROBE1/report.md` (use its methods: `decide +kernel`, structural recursion,
`/usr/bin/time -v`, external memory caps, LEAN_NUM_THREADS; Lake here rejects `lake build -j`).

**Workspace.** Worktree `/home/ubuntu/aklt/wt/PROBE2` (Lake project; Mathlib prebuilt and linked; never run
`lake update` or build Mathlib). Copy the probe files into `AKLT/Probe2/` (fix module headers/imports as needed;
record every change). Write only there and in `/home/ubuntu/aklt/reports/PROBE2/`. At most 8 Lean processes and
128 GB RAM total; other agents share the machine. PATH needs `$HOME/.elan/bin`.

**Measure, in the report's ranked order:** Baseline; BellmanGuard1/16 and Bellman9Guard1/16 (packed guarded
comparison at the real plane sizes); Packed1/16/128 (packed periodic step; does memory grow with steps?); H2Small
(the complete small H2 test generated from the trail definition — does it pass, how long?); H1Gram (one 131-dim
Gram/residual check); PrefixLeaves8/10/12/14; Nat*/Int* calibration and ListZip/ListIndex. For each: wall time,
max RSS, exit status, `#print axioms`. Then extrapolate, with stated assumptions, (a) the H3′ stationary
certificate check (m=10, R=70, five cases; and the m=9, R=80 alternative), including how the ~1.2 GB-per-case
literal data could be represented in Lean source/olean (packed Nat literals per module? how big can one literal or
module be before parsing/elaboration/olean size becomes the bottleneck? measure one module with a 1 MB, 10 MB and
50 MB packed literal); (b) H1 at the 12,173-block scale; (c) H2. Recommend go/no-go for each route and the module
sharding.

**Deliverable.** `/home/ubuntu/aklt/reports/PROBE2/report.md`, first line `STATUS: COMPLETE` or
`STATUS: PARTIAL (reason)`; a table of every measurement (command, wall, RSS, outcome, axioms); the literal-size
experiment; extrapolations labelled as such; recommendations. Do not launch sub-agents.
