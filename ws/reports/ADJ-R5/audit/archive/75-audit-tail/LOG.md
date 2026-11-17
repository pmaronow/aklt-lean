# Agent 75 log

## 2026-11-15 23:31 UTC
Started. Read writeup main.tex, sec7, sec8; agent 62 REPORT and NOTES (Entries 0-25). Wrote NOTES header and plan.
Next: writeup sec6 (exposure, response lemmas), agent 59 kernel definitions and code, agent 69 audit notes, then 62's code.

## 2026-11-15 23:44 UTC
Established (NOTES Entries 1-6): the code's kernel = write-up M_1 (PROVED reading); exposure orders admissible
(PROVED); over-count lemma re-derived incl. the mode-A range n <= 107 (PROVED); remainder lemma and assembly (PROVED);
code audit of tailmem4/5: no defect; only the build flags are undocumented (GCC ignores FENV_ACCESS; -frounding-math
needed). Own exact enumerator exact75.c reproduces agent 69's and agent 62's exact values (<= 7e-13).
Running: re-run of 62's certificate at a = 0.18094, b = 0.36751 (7 runs, scratchpad/agents/75/rerun); exact
straights-first values to n = 26 (5 classes); small-m comparison of my own Python chain (memchain75.py) with tailmem5.
Next: collect, domination tables, then appendix.

## 2026-11-15 23:57 UTC
Done: independent checks (i) exact n <= 20 (agreement 7e-13 with 62 and with 69), (ii) true straights-first values to
n = 26 vs 62's m = 10 over-count (all ratios >= 1; rows 1.05/1.08 at n = 22), (iii) own Python memory chain agrees
with tailmem5 at m = 4, 6 (<= 1e-5) and dominates the exact values; remainder test at m = 8. Type-dependent
coefficients re-verified by my own arb branch and bound (62's B&B had a bookkeeping flaw, harmless here). Finding:
no lambda < 1 guard in the remainder code (latent). Exact re-assembly of 62's original outputs: 0.987730103.
Appendix writeup/app-tail.tex drafted (numbers TBD from the re-run). Running: re-run modes A (C_2, C_3) and B.

## 2026-11-16 00:03 UTC
Mode-A re-run at (0.18094, 0.36751) finished (5 classes; exact part agrees with exact75 at the new constants to 7e-13);
before mode B: row B 0.924179873, row C (unnormalized) 1.132351918. Forward kernel n <= 22 agrees with 59's symbolic data
(3.6e-10). tailmem6 cross-checked at small m (type-dependent). Appendix compiles in the scratch copy (no warnings in
app-tail). Waiting for the two mode-B runs; then fill Table 1 and finish.

## 2026-11-16 00:17 UTC
Re-run complete: rho(M_1) <= 0.987762443 (row B), row C 0.968623402, at a = 0.18094, b = 0.36751 directly; source of
tailmem4.c sha256 9a8410802158c2f905177afd045547485cd2c35ec9477a2b469961ad75607360, tailmem5.c
070f1bf697ccd9dd51ee0ba55ff549f6f10201411553caf6c28637144c386118 (copies of 62's code/, unmodified).
Appendix writeup/app-tail.tex filled and test-compiled (scratch copy with \input{app-tail} and the proposed sec8 block):
no errors, no undefined references, no overfull boxes in the appendix. Next: commit, final report.
