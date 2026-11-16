# Feasibility of kernel-checked computer-assisted inputs — AKLT spectral-gap formalization

**Context.** The manuscript in `/Users/paronow/aklt-lean/bundle/manuscript/` (read it; Sections 6–8 and Appendices
C and D matter most) proves a spectral gap with three computer-assisted inputs, (H1), (H2) and (H3′) (Theorem 8.1).
The programs and data it cites are in `/Users/paronow/aklt-lean/bundle/programs/` (see `bundle/README.md`). We will
formalize the whole paper in Lean 4 + Mathlib to Palomar standards: kernel-checked only, no `native_decide`, no
`implemented_by`, no axioms beyond propext, Classical.choice, Quot.sound. So every computation must either be
replayed by the Lean kernel (`decide`/`rfl`-style reduction, where the kernel accelerates Nat arithmetic with GMP)
or be replaced by a certificate whose check the kernel can afford, or be replaced by mathematics.

**Questions.**
1. For each input (H1, H2, H3′): what exactly must be computed, how many elementary operations and how much memory
   (measure it: instrument or rerun the programs, at reduced parameters if needed, and extrapolate), and what is the
   cheapest certificate format whose kernel check proves the statement *as defined in the paper* (the check must
   start from the definitions, e.g. H1 matrices must be computed from the pattern data inside Lean, not trusted).
2. Estimate kernel cost. Use what is known about Lean 4 kernel reduction speed for Nat/Int-heavy code (GMP-accelerated
   `Nat.add/mul/div/mod/ble/beq/gcd`, structural recursion over lists, no mutable arrays, `Nat.rec` vs well-founded
   recursion pitfalls, `decide +kernel`); give a range, and say what a probe on our 32-core workstation should time
   first. (No Lean is installed on this Mac; a later probe will measure.)
3. H3′ is the critical one (a 3.8·10^8-entry memory walk run for 260 steps in binary32 with upward rounding).
   Search for a kernel-affordable route that keeps Theorem 8.1's conclusion (or any conclusion still sufficient for
   Theorem 7.x, i.e. ρ(M₁) < 1 at constants for which (H1) is proved): smaller memory, smaller quotient, fewer exact
   steps, cruder remainder, a different splitting of the trail sum, sub-invariant-vector certificates instead of
   long iterations, symmetry reduction, the type-dependent variant (Remark C.x, ρ ≤ 0.918, which needs extra
   coefficient bounds), or a different mathematical bound on the long trails. Run the C programs at reduced
   parameters on this Mac to map the trade-off (ρ bound vs. state-space size and steps). Report the cheapest
   parameter set you find that still gives ρ(M₁) < 1, with its operation count.
4. Same for H2 (M_8 over 938 dihedral classes in exact rationals) and H1 (7,962 patterns, Bareiss on integer matrices
   up to 245×245; are there cheaper PD certificates, e.g. LDL^T or a rational Cholesky with a diagonally dominant
   residual, or smaller sectors?).

**Limits.** At most 6 cores, 8 GB RAM per process, 5 GB disk, all inside
`/Users/paronow/aklt-lean/reports/COMPFEAS/` (copy programs there before modifying them; never modify the bundle).
Keep the total compute under about 3 hours of wall-clock. Do not launch sub-agents.

**Deliverable:** `/Users/paronow/aklt-lean/reports/COMPFEAS/report.md`, starting with a status line
`STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`, then: per input, the operation counts (measured, with commands),
the proposed certificate design, the estimated kernel cost range, the risks; for H3′, the trade-off table and your
recommended route; finally a ranked plan for a workstation probe (exact Lean snippets to time). Label every
numerical claim as measured or estimated.
