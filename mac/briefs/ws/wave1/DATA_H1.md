# DATA_H1 — export the complete Gram/residual witness set for the (H1) operator blocks (no Lean)

**Context.** A feasibility study (`/home/ubuntu/aklt/compfeas/report.md`, H1 sections; code in
`/home/ubuntu/aklt/compfeas/experiments/` — `profile_h1_chol.py`, `profile_h1_chol_extra.py`, `profile_h1_operator.py`,
`h1_dimensions.py`, `enumerate_patterns.py`; pattern data under `/home/ubuntu/aklt/compfeas/programs/`) generated and
exactly checked, in memory, a division-free positivity witness for every exchange-sector block of the
operator-only (H1) certificates of all 7,962 patterns (12,173 blocks; 8,439 already strictly diagonally dominant),
but kept only samples. A Lean checker will need the full data.

**Task.** Regenerate and SAVE the complete witness set under `/home/ubuntu/aklt/data/h1/` (create it): for every
pattern id and every exchange-sector block: the pattern record needed to reconstruct it (status/kept-bond data,
type straight/turn, threshold p/q, the chosen representation and inversion mask), the block's dimension and sector
label, the integer matrix M (the exact matrix 5qA − 3pA′ restricted to the sector, as the checker reconstructs
it), and the witness (g, d, S, L) with E = d·S²·M − g·L·Lᵀ strictly diagonally dominant with positive diagonal
(L = 0 allowed). Then verify every block with an independent exact-integer checker that reads only the saved files
(not the generator's memory), and record totals (blocks, sizes, bit lengths, products). Use a compact documented
format (e.g. one gzip JSON-lines file per 500 patterns plus an index with sha256), deterministic output, and a
README describing every field precisely enough for a Lean exporter. Up to 16 cores, 64 GB RAM, 20 GB disk.
Write only under `/home/ubuntu/aklt/data/h1/`, `/home/ubuntu/aklt/scratch/DATA_H1/` and
`/home/ubuntu/aklt/reports/DATA_H1/`.

**Deliverable.** `/home/ubuntu/aklt/reports/DATA_H1/report.md`, first line `STATUS: COMPLETE` or
`STATUS: PARTIAL (reason)`; the format description; totals; the verification log; then a section
`ORCH-SUMMARY` (≤ 25 lines: what exists, where, limitations, what the Lean side must still prove). No sub-agents.
