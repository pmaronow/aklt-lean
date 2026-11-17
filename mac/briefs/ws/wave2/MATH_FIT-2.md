Orchestrator message — round 2 (author-directed; the machine is now almost idle: you may use up to 40 CPU-heavy
processes and 200 GB RAM). Your H1-tree and H3-line results are accepted as the working designs: H1-tree has an
independent written proof and an independent numerical confirmation; H3-line is being written up by another agent
(do not write proofs). Measured facts since your report: the verifier's Lean replay is serial and NanoDa uses
four threads; the engineered H3 kernels of the certificate lane (`/home/ubuntu/aklt/reports/CERT_H3/report.md`,
section "phase 4 — fit") cut plane/row work by roughly 10x but the exact length-12 PREFIX evaluation then
dominates (old prefix stage 3.5 CPU-hours, about 0.7 CPU-hours after engineering, unchanged by the patch
redesign), followed by literal volume (your ~826 MB).

Task: shrink the remaining H3-line finite work by a further factor ≥ 3 overall, by experiments (exact or
rigorously rounded at the end), spending the new contraction margin (.032) where it buys the most:
1. PREFIX: the smallest prefix length L (and the cheapest prefix formulation — e.g. coarser rounding of phase
   products, grouping of stems, bounding long prefixes by the potential earlier) for which the exact bounds still
   give `M₁h ≤ ρ₀h` with some ρ₀ < 1 (ρ₀ up to about .995 is acceptable); report the bound and the prefix work
   (number of stems/visits) for L = 6, 8, 10, 12.
2. PATCH: the trade-off between patch radius (12, 14, 16, 18, 20), memory (9 or 10 with your line caps), rate r,
   value scales (fewer bits per value: 16? 12?) and the bound; also what exact symmetries (the y-reflection found
   by the certificate lane, any x-reflection or diagonal symmetry per case) allow storing half a patch; and
   whether the five patches can share data (e.g. a common patch with case-dependent small corrections).
3. Report for each successful combination the exact finite work (rows, values, bits, prefix visits) and the
   resulting ρ₀, and recommend ONE design with the smallest total work whose every inequality you verified
   exactly, with its data files, ready for the proof writer and the certificate lane.
Append a section "round 2" to `report.md` (update the first line), keep it current as experiments finish, and end
with an updated ORCH-SUMMARY.
