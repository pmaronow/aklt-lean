# REV-PLAN — plan the streamlined, strengthened proof of the AKLT gap theorem

**Goal.** Before formalizing in Lean 4 (kernel-checked, no hypotheses), the author wants the manuscript's proof
strengthened and streamlined. You write the PLAN for an integrated revision: the exact statements, their order, the
interfaces between parts, and an assignment of proof-writing to three independent lanes. Proof writers will then
work in parallel from your plan, so the interface statements must be exact and complete.

**Inputs (read all of them).**
- Corrected manuscript (current baseline): `/home/ubuntu/aklt/manuscript-corrected/` (git HEAD 9faa0ee; main.tex and
  section files; build a PDF in a copy under your own directory if you want one).
- Refereed strengthening to ALL torus sizes and uniqueness for all L,N ≥ 3:
  `/home/ubuntu/aklt/reports/STRENGTHEN-ALL/proof.tex` (+ report.md); its referee reports
  `/home/ubuntu/aklt/reports/REF-SA-A/report.md` (SOUND) and `REF-SA-B/report.md` (one minor fix).
- Refereed direct proof replacing the cited MO94/MOS94 results: `/home/ubuntu/aklt/reports/MOSPROOF/proof.tex`
  (+ report.md); referee `/home/ubuntu/aklt/reports/REF-MOS/report.md` (one minor fix: assume α ∈ (0,1]).
- Streamlining assessment: `/home/ubuntu/aklt/reports/OPPORTUNITIES/report.md`.

**Author decisions (binding).**
- Main theorem: there exist c > 0 and L₀ such that for ALL L, N ≥ L₀ (any parity), ker H_{L,N} = span{B} and every
  nonzero eigenvalue of H_{L,N} is ≥ c; and for ALL L, N ≥ 3, ker H_{L,N} = span{B}. Constants stay existential.
  No general-graph ground-space theorem in the paper (the algebraic argument may be stated for the torus only).
  No infinite-volume corollaries, no thin-torus results, no explicit-constant appendix.
- ADOPT the streamlining package from OPPORTUNITIES: #1 together with #16 (a direct periodic block argument on
  PHYSICAL SITES for every torus — no §3 Knabe criterion, no 2×2 cell blocking — combined with STRENGTHEN-ALL's
  three rotated icosahedral frames, proper 3-colouring, antiferromagnetic torus measure and local gauge on plane
  boxes; the stopped coupling of MOSPROOF at site scale); #2 a finite fourth-moment functional instead of the
  continuous measure on S² (keep unit-vector pins and the (H1) quantifier over unit vectors); #3 thickened cut;
  #4 revisit mass in the walk coefficient; #5 ladder-operator proof of the sector lemma; #6 Cartan multiplication
  edge lemma if it shortens the proof; #7 explicit finite-energy/comparison constants by density comparison (adapt
  to the new frames); #9 positive-vector contraction witness and renewal lemma instead of spectral radii; #10 common
  minorization for cut laws and simplified removal constants; #20 narrowed interfaces for (H1)–(H3′); #21 the
  operator-only (H1) path (closed forms and the FKG radius lemma leave the main proof; they may stay as remarks).
- The computer-assisted inputs keep their meaning; their certificates are being redesigned separately (another agent
  owns the (H2)/(H3′) certificate search). Your plan states (H1), (H2), (H3′) — or their narrowed replacements per
  #9/#20 — as exact mathematical statements with the constants they need.
- Every corrected statement of the baseline that is not replaced must be kept as corrected.

**Deliverables** (write only in `/home/ubuntu/aklt/reports/REV-PLAN/`):
1. `PLAN.md`, first line `STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`: the new section structure; for every
   statement in the revised paper its label, exact LaTeX statement, status (kept as is / kept with edits / new /
   replaces X), source of its proof (baseline label, STRENGTHEN-ALL, MOSPROOF, OPPORTUNITIES entry, or "to be
   written"), and dependencies; the list of baseline statements removed; the interface statements between lanes; and
   the lane assignment: Lane A = model, frames, uniqueness, quantum–classical comparison, periodic block gap
   argument and assembly of the main theorem; Lane B = window estimate at site scale from (P) (cut, removal,
   geometry, topology); Lane C = walk expansion, pair recursion, (P) from (H1)–(H3′), the (H1) reduction to
   operator positivity (Appendix D, operator-only) and the statements of the computational inputs. For each lane:
   what it must write, what it may cite from other lanes (only interface statements), and acceptance criteria.
2. `interfaces.tex`: the interface statements as compilable LaTeX (amsart), with labels.
3. A risk list: any adopted item that does not fit the new structure, with your recommendation.
Do not write the proofs themselves beyond short sketches needed to fix statements. Do not launch sub-agents.
