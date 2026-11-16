# FID_S060 — fidelity review of Lean statements (blind)

**Your declarations:** in `/home/ubuntu/aklt/review/FID_S/lean/AKLT/Defs/Polynomial.lean`: `physicalEval`, `hamiltonian`, `vbs`.
Your working directory is `/home/ubuntu/aklt/reports/FID_S060/`.

**Inputs (read-only).** `/home/ubuntu/aklt/review/FID_S/lean/` — Lean 4 + Mathlib files stating the definitions
(`AKLT/Defs/`), the interface statements (`AKLT/Blueprint/Top/`, each a closed `Prop`) and the headline
(`AKLT/Challenge/`) of a mathematics paper; `/home/ubuntu/aklt/review/FID_S/paper/` — the paper's LaTeX section
files (`sec*.tex`, `app-*.tex`). You may read Mathlib sources under
`/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`. Read nothing else on this machine.

**Job.** For each of your declarations decide whether it says exactly what the paper says (find the matching
definition or statement in the paper; the Lean docstrings name paper labels): nothing weaker, nothing stronger, no
vacuous or degenerate reading. Check every Mathlib notion used, coercions, `ℕ` subtraction, division by zero,
index and sign conventions, quantifier order, domains and side conditions, finiteness/instance arguments, and
whether hypotheses the paper states are present (and none added). For an auxiliary definition with no direct paper
counterpart, check that it is the right object for the declarations that use it. Read the whole file and the files
it imports for context; judge only your declarations. You may run small checks (Python, or Lean in a scratch copy
under your directory with Mathlib packages symlinked from `/home/ubuntu/aklt/repo/.lake/packages`; at most 2 Lean
processes).

**Deliverable.** `report.md` in your working directory: first line exactly `STATUS: PASS` or `STATUS: FAIL`; second
line exactly `BLOCKING: n`; then for each declaration a line `DECL: <name> PASS` or `DECL: <name> FAIL` followed by
your reasoning (paper location file:line, the Mathlib meaning you checked); then non-blocking remarks. A problem is
blocking if the Lean meaning differs from the paper or the statement could be proved or refuted for a reason the
paper does not intend. Do not launch sub-agents. Do not modify inputs.
