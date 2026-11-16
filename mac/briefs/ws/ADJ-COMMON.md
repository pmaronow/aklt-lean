
**Inputs (read-only).** The manuscript `/home/ubuntu/aklt/manuscript/bundle/manuscript/` (main.pdf and .tex; the
version under formalization, frozen); the programs and data it cites in `/home/ubuntu/aklt/manuscript/bundle/programs/`;
the full project tree it came from, `/home/ubuntu/aklt/source-full/` (agent folders with code, outputs and notes —
use it only to settle questions about what programs and outputs exist); and the referee report(s) named below in
`/home/ubuntu/aklt/referee/`.

**Your job.** You are an independent adjudicator. For every finding listed below, decide on your own evidence —
re-derive the mathematics, recompute counterexamples exactly (Python with fractions, or C), read the cited lines —
whether it is CONFIRMED (the manuscript is wrong or incomplete as the referee says), CONFIRMED-MODIFIED (wrong or
incomplete, but the referee's diagnosis or repair is not right; give the right one), or REJECTED (the manuscript is
right; explain). Do not defer to the referee. For every confirmed finding, write the minimal correction to the
manuscript as exact LaTeX: replacement text for the affected statement(s) and proof step(s), keeping labels and
numbering, changing nothing that is not needed, and saying which other statements (anywhere in the paper) must
change in consequence. Corrections must keep the paper's main theorem and constants unless that is impossible —
say so explicitly if it is.

**Limits.** Write only in your working directory. At most 4 cores and 16 GB RAM. Do not launch sub-agents.

**Deliverable.** `report.md` in your working directory. First line `STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`.
Then one section per finding: `FINDING <id>: CONFIRMED | CONFIRMED-MODIFIED | REJECTED`, the evidence (with
commands and outputs for computations), and the correction (LaTeX, in a fenced block, with the target file and
line range). End with a consolidated list of all manuscript edits in file order.
