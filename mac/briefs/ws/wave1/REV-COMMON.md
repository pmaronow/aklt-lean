
**Inputs (read-only).** The revision plan `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` (the contract: statement
inventory with exact LaTeX statements, labels, proof sources, dependencies, lane ownership and acceptance criteria;
items marked [AMENDED] are current), `interfaces.tex` and `RISKS.md` in the same folder. Proof sources the plan
cites: the current manuscript `/home/ubuntu/aklt/manuscript-corrected/` (git HEAD 9faa0ee),
`/home/ubuntu/aklt/reports/STRENGTHEN-ALL/proof.tex`, `/home/ubuntu/aklt/reports/MOSPROOF/proof.tex`,
`/home/ubuntu/aklt/reports/OPPORTUNITIES/report.md`, and (for the computational inputs)
`/home/ubuntu/aklt/compfeas/` (report.md, programs, data).

**Task.** Write, as complete LaTeX (amsart section files that will be `\input` into the revised paper), every
statement and proof the plan assigns to your files below, in the plan's order, with the plan's labels and exact
statements. Proofs must be complete and rigorous at the level of a journal paper, detailed enough to formalize in
Lean (every case, constant and hypothesis explicit). Cite statements owned by other files only by their plan label
and only as the plan's interface rules allow. If a planned statement is false, unprovable as stated, or needs a
change, do NOT silently change it: give a counterexample or reason, propose the minimal corrected statement, use
the corrected version in your text, and list it under "Deviations". You may run exact computations (Python with
fractions/sympy, C) to test claims; at most 4 cores.

**Deliverables** in your report directory: the section file(s) named below; `report.md` with first line
`STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`, then a table label → written? → depends on, the "Deviations"
list (each with justification), and checks run. The files must compile when included in an amsart document with
the macros of `/home/ubuntu/aklt/manuscript-corrected/main.tex` (test with a small wrapper in your directory; other
lanes' labels may show as undefined references — list them). Do not launch sub-agents. Do not modify inputs.
