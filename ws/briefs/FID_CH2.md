# FID_CH2 — fidelity review of a Lean statement (blind)

**Inputs (read-only)** in `/home/ubuntu/aklt/review/FID_CH2/`: `MainV2.lean` (defines `MainStatementV2`),
`Main.lean` (the definitions it imports: torus, bonds, spin-2 space, projections P, Hamiltonian H, VBS vector B),
and `target-statement.md` (the theorem it must state). Definitions of the objects: the manuscript
`/home/ubuntu/aklt/manuscript/bundle/manuscript/` (§1, §2). You may read Mathlib sources under
`/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`. Read nothing else on this machine.

**Job.** Decide whether `MainStatementV2` says exactly what the target statement says: nothing weaker, nothing
stronger, no vacuous or degenerate reading (quantifier order of c and L₀, the threshold, the range of L, N via the
`Size` subtype, "every nonzero eigenvalue" via `HasEigenvalue` and the real/complex coercion, `B ≠ 0`, `ker` vs
span). Also check that the imported definitions are used consistently (same H and B for all sizes, no hidden
parity assumption). You may run small Lean checks in a scratch copy under your own directory (link Mathlib
packages from `/home/ubuntu/aklt/repo/.lake/packages` by symlink; at most 2 Lean processes).

**Deliverable.** `/home/ubuntu/aklt/reports/FID_CH2/report.md`: first line `STATUS: PASS` or `STATUS: FAIL`, second
line `BLOCKING: n`, then `DECL: MainStatementV2 PASS|FAIL` with reasoning, then non-blocking remarks. Do not
launch sub-agents. Do not modify inputs.
