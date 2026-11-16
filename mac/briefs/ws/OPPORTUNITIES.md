# OPPORTUNITIES — other easy strengthenings and streamlining of the AKLT gap paper

**Context.** We are about to formalize in Lean 4 (kernel-checked only, no native_decide) the manuscript
`/home/ubuntu/aklt/manuscript/bundle/manuscript/` ("The spectral gap of the spin-2 AKLT model on the square
lattice"; main.pdf + .tex). The author wants the strongest result we can reasonably get before formalizing, and
proofs as streamlined as possible. A separate agent is already extending Theorem 1.1 from even tori to all tori and
uniqueness of the ground state to all sizes (do not work on that). Material to use:
- `/home/ubuntu/aklt/reports/MOSPROOF/proof.tex` (+ `report.md`): a direct proof replacing the cited MO94/MOS94
  results in §4 (being refereed);
- referee and adjudication reports `/home/ubuntu/aklt/referee/REF-*/report.md`, `/home/ubuntu/aklt/reports/ADJ-*/`;
- kernel-speed measurements `/home/ubuntu/aklt/reports/PROBE1/report.md` (the Lean kernel does roughly 2–3·10⁴
  elementary Nat operations per second and retains ~48 KB per Bareiss cell update; the (H3′) computation as
  written, ~10¹¹ floating-point operations over 3.8·10⁸ states, cannot be replayed in the kernel).

**Task.** Find and assess opportunities of two kinds.
A. Strengthenings of the main result that are true and cheap given the paper's machinery, for example (do not limit
   yourself to these): explicit constants c and L₀ (are all constants in the chain explicit?); exponential decay of
   correlations in the VBS state B (or in the classical measure) uniformly in the volume; uniqueness of the
   infinite-volume classical Gibbs measure; statements about the infinite-volume quantum model (unique
   frustration-free ground state, gap of the GNS Hamiltonian) and what extra machinery they need; other boundary
   conditions or geometries (cylinders, thin tori L fixed and N → ∞) and whether the method reaches them; a better
   gap constant.
B. Streamlining: steps that can be removed or replaced by shorter arguments (e.g. avoiding the continuous measure on
   S² entirely by exact frame averages, since every integrand has degree ≤ 4 per site; avoiding the 2×2 cell
   blocking; simplifying the cut lemma, the walk expansion or the recursion; weakening what is needed from (H1),
   (H2), (H3′)); and, with the highest priority, any change to the argument or to the constants that makes the
   computer-assisted inputs — above all (H3′) — cheap enough for kernel checking (smaller certificates, a different
   splitting of the trail sums, using the slack in (H1) or the type-dependent coefficients, a cruder bound on long
   trails, a sub-invariant-vector certificate on a small state space, …). Run small computations (C or Python; at
   most 8 cores, 32 GB RAM, 20 GB disk, under your own directory) to test whether a proposed cheaper (H3′) or (H2)
   certificate still closes, and report the trade-off with measured sizes.

**Deliverable.** `/home/ubuntu/aklt/reports/OPPORTUNITIES/report.md`, first line `STATUS: COMPLETE` or
`STATUS: PARTIAL (reason)`; then one entry per opportunity: precise statement (strengthened theorem or simplified
step), whether it is true with a proof or proof sketch (or a counterexample/obstruction), the cost to the paper and
to a Lean formalization, the value, and your recommendation (do / do not / ask the author). Rank the list. Write only
in `/home/ubuntu/aklt/reports/OPPORTUNITIES/`. Do not launch sub-agents.
