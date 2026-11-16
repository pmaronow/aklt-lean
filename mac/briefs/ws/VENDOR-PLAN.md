# VENDOR-PLAN — which donor Lean code to vendor, and at which pin

**Context.** Campaign repo `/home/ubuntu/aklt/repo` (Lean 4.35.0-rc2, Mathlib 065356127b; library `AKLT`). We will
formalize the manuscript in `/home/ubuntu/aklt/manuscript/bundle/manuscript/` to Palomar standards (kernel only;
no native_decide/sorry/axioms; allowed axioms propext, Classical.choice, Quot.sound). A donor search is in
`/home/ubuntu/aklt/manuscript/DONORS-2026-11-16.md` (read §§4–6). Nothing depends on our pin yet except a small
Challenge file being written now (Mathlib only).

**Task.** For each priority-1 and priority-2 donor in §6 of the donor report (Mathlib modules, HexPosDefTheory,
QICLean, Physlib sl₂, pmaronow/fluctuations-palomar finite-chain modules, TauCeti sphere moments, TNLean AKLT
pieces, balaban-lean Timár/boundary connectivity, PottsDiscontinuity-lean cut lemmas, Econlib/llm-audit finite
conditioning, LeanCert dyadic core, RealRooted Perron–Frobenius):
1. clone it at the stated commit into `/home/ubuntu/aklt/donors/<name>` (blobless/shallow; read-only use);
2. determine its Lean/Mathlib pin, the exact import closure of the modules we would use, its size in lines, its
   licence and attribution requirements, and whether it uses `sorry`, axioms, native_decide or other forbidden
   features anywhere in that closure (grep + `#print axioms` on its key theorems if you can build it);
3. estimate the porting effort to our pin (try it for the two or three most valuable closures: copy the closure
   into `/home/ubuntu/aklt/scratch/VENDOR-PLAN/port-<name>/` as a Lake project depending on our Mathlib —
   symlink `/home/ubuntu/aklt/repo/.lake/packages`, never modify it — and count the errors after a first build);
4. compare with the alternative of moving the campaign to a newer pin (e.g. Lean 4.36.0-rc1, already installed in
   `~/.elan`): which donors become direct imports, and what that costs (Mathlib cache download/build time, Comparator
   availability in that toolchain — check for `leanexport`, `con-ron`, `nanoda_bin` in its bin directory).
Recommend one pin and a vendoring list (module closures, target namespace `AKLT.Vendor.<Donor>`, licence/NOTICE
handling).

**Limits.** Write only under `/home/ubuntu/aklt/donors/`, `/home/ubuntu/aklt/scratch/VENDOR-PLAN/` and
`/home/ubuntu/aklt/reports/VENDOR-PLAN/`. Disk ≤ 40 GB in total (delete build outputs of trial ports at the end,
keep the logs); abort if free disk on `/` falls below 150 GB. At most 8 Lean processes. Do not modify
`/home/ubuntu/aklt/repo` or any other campaign. Do not launch sub-agents.

**Deliverable.** `/home/ubuntu/aklt/reports/VENDOR-PLAN/report.md`, first line `STATUS: COMPLETE` or
`STATUS: PARTIAL (reason)`; per donor: commit, pin, closure (module list), lines, licence, forbidden-feature scan,
port result (error count and the main kinds of breakage); then the pin recommendation with its costs and the
vendoring list.
