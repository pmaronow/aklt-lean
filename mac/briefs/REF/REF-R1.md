# Referee brief, lane R1

**Lane R1.** Sections 1 and 2 (sec1-intro-statement.tex, sec2-frames-Q.tex): the model, the frames (icosahedron/dodecahedron coherent states, spherical designs), the frame map, the Gibbs measure mu_D, and Theorem 2.x (QD): the quantum gap is bounded below by a multiple of the heat-bath gap, and uniqueness of the ground state. Include every quantum-mechanical and representation-theoretic fact used.

Your working directory is `/Users/paronow/aklt-lean/reports/REF-R1/`; write `report.md` there.

# Referee brief (common part)

You are an independent referee of a mathematics manuscript. The proof will later be formalized in Lean 4 with
Mathlib, so a precise, adversarial check of every step in your lane matters: every gap you miss becomes a stuck or
false Lean node.

**Inputs (read-only).** The bundle `/Users/paronow/aklt-lean/bundle/`:
- `manuscript/` — the LaTeX source (`main.tex` inputs the section files) and `main.pdf`. This is the paper.
- `programs/` — the programs and data cited by the paper (see `bundle/README.md`).
Read only files inside the bundle and your own directory. Do not read any other file on this machine and do not
search the web for this manuscript or its programs.

**Your lane** is given below. Read the whole paper for context (definitions and statements used in your lane live
elsewhere), but check your lane line by line. For every statement in your lane, check: the statement is well-posed
(all objects defined, quantifiers and domains explicit); every step of its proof follows; every cited result is used
within its hypotheses (quote the hypotheses you rely on); constants and inequalities are correct; edge cases
(small sizes, empty sets, boundary, parity, degenerate configurations, zero denominators) are covered.

You may run small computations (Python 3 at /opt/homebrew/bin/python3.12, or C) to test claims numerically or on
small cases; label such evidence as numerical. Limits: at most 4 cores, 6 GB RAM and 2 GB of disk; write only
inside your own directory.

**Deliverable:** `report.md` in your working directory. It must start with one status line:
`VERDICT: SOUND` | `VERDICT: SOUND WITH FIXES` | `VERDICT: GAP` | `VERDICT: ERROR`
followed by:
1. **Findings**, numbered, each with severity (Critical = a statement in the lane is false or its proof cannot be
   repaired locally; Major = a proof step is missing or wrong but repairable; Minor = imprecision, typo, missing
   hypothesis that is clearly intended), location (file:line and statement label), the exact claim, why it fails
   (counterexample or the missing argument), and a proposed correction or repair.
2. **Statement table**: every numbered statement in the lane, with: label, one-line content, verdict
   (correct / correct after fix / unproved / false), and what it depends on (labels and cited results).
3. **Formalization notes**: hidden hypotheses, implicit standard facts the proof uses without proof (each would be a
   Lean node), definitions that are ambiguous or need a precise choice, and any step whose natural Lean statement
   differs from the text (e.g. limits, measures, "for L large", continuous vs. finite spaces).
4. **External inputs**: each cited or folklore result used in the lane, stated exactly as used, with the locator
   the paper gives, and whether the use stays within the cited statement's hypotheses.

Work until the report is complete; do not stop at a plan. Do not launch sub-agents.
