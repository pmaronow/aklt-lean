# EDIT4_DELTA — check a set of edits to a paper, and two factual questions against a Lean formalization

Paper: git repository `/home/ubuntu/aklt/manuscript-v2` (LaTeX; `main.tex`, `sec*.tex`, `app-*.tex`). The working
tree has uncommitted edits relative to the last commit. The most recent group of edits changed only the
description of the status of the computer verification; the editor's account, with every old → new text, is
`/home/ubuntu/aklt/reports/EDIT_4/report.md`, and the pre-edit files are in
`/home/ubuntu/aklt/reports/EDIT_4/pre-edit/`. The Lean formalization is `/home/ubuntu/aklt/repo` (branch `main`;
closing module `CertData/Close/All.lean`; receipts `receipts/closing/`; hand-written certificate checkers
`AKLT/Cert/H1/**`, `AKLT/Cert/H2/**`, `CertData/H3/**`, `AKLT/Cert/H3/**`), with the generated certificate
libraries in `/home/ubuntu/aklt/wt/CLOSE_H3` (H3′) and `/home/ubuntu/aklt/wt/CERT_H1` (H1), the certificate lanes'
reports `/home/ubuntu/aklt/reports/CERT_H1/report.md`, `/home/ubuntu/aklt/reports/CERT_H3/report.md`,
`/home/ubuntu/aklt/reports/CLOSE_H3/report.md` (+ `final-receipt.json`), and validation records of the
certificate-free part under `/home/ubuntu/aklt/val/` (latest `RESULT` files) and
`/home/ubuntu/aklt/logs/VALCORE.log`.

Read-only on the paper and the formalization; write only your report. Tasks:
1. For every statement about the verification that the paper now makes (abstract, Section 1, the new paragraph at
   the beginning of Section 8, the proof of the (H1) theorem, the "certification scope" passage, Appendix C's
   opening and closing sentences): is it TRUE of the formalization as it stands, and supported by a record you
   can point to (file and line/field)? Check each number (pattern, block and module counts, CPU-hours, Lean
   version, axioms, "no native_decide", what the two independent kernels checked). Report any overclaim or
   underclaim with the exact corrected sentence.
2. Question A: `sec8-inputs.tex` contains a sentence of the form "As an additional finite check, all 3734 blocks
   … pass this fallback too." Is that additional check performed inside the Lean formalization (where?), or only
   by an external program? Propose the exact wording that is true (or deletion).
3. Question B: Section 8 and Appendix C describe the finite assertions as checks of named archive files (for
   example `h2_exact_m6k1_r5.json`, `stationary_*_coarse.bin.gz`). For each named file: does the Lean certificate
   check the content of that same file (same values — compare hashes or values where you can), a regenerated
   equivalent, or something different? List each file with the finding and propose the minimal true wording
   where the paper's description and the formalization differ.
4. Confirm that the latest group of edits changed no mathematics (compare with the pre-edit files) and that the
   paper compiles without undefined references (compile a COPY under your report directory).
Report `/home/ubuntu/aklt/reports/EDIT4_DELTA/report.md`: first line `VERDICT: CLEAN | FIXES NEEDED`, then
findings with file, line, and exact replacement text, then the answers to A and B with evidence.
