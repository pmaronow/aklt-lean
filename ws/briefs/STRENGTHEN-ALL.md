# STRENGTHEN-ALL — extend the main theorem from even tori to all tori

**Context.** We are about to formalize in Lean 4 the manuscript `/home/ubuntu/aklt/manuscript/bundle/manuscript/`
("The spectral gap of the spin-2 AKLT model on the square lattice"; main.pdf + .tex). Its Theorem 1.1 is stated
for even L, N ≥ L₀. The author wants the strongest result we can reasonably prove before formalizing, and asked
specifically to extend it to all torus sizes. Related material you should use:
- `/home/ubuntu/aklt/reports/MOSPROOF/proof.tex` (+ `report.md`): a direct finite-state proof that the window
  estimate implies a uniform heat-bath gap on large boxes, replacing the cited MO94/MOS94 theorems in §4 (under
  independent refereeing now);
- adjudicated corrections to the manuscript: `/home/ubuntu/aklt/reports/ADJ-*/report.md` (some may still be in
  progress; use what exists).

**Goals (prove, in order of priority):**
1. Theorem 1.1 for all sizes: there exist c > 0 and L₀ such that for all L, N ≥ L₀ (any parities) the kernel of
   H_{L,N} is spanned by the valence-bond-solid state B and every nonzero eigenvalue is ≥ c.
2. Uniqueness for every size: for all L, N ≥ 3, ker H_{L,N} = span{B} (if true; if some small or degenerate sizes
   fail, say exactly which and prove the rest).
3. Anything else that comes for free from the same changes (state it precisely).

**Starting idea (verify or replace).** Evenness seems to enter mainly through §2: the checkerboard frame
(icosahedron on one sublattice, dodecahedron on the other) and the rotation of one sublattice, which need a
bipartite torus. A possible route: keep the antiferromagnetic weights 1 − n_x·n_y (no rotation) and assign frames by
a proper 3-colouring of the torus graph using three pairwise disjoint spherical 5-designs (icosahedron, dodecahedron
and, e.g., a rotated icosahedron, or any other choice), so all bond weights stay strictly positive and the frame map
is still an isometry; the classical Knabe criterion of §3 and the box conditional laws only see ℓ×ℓ boxes, which are
bipartite, and window laws are frame-independent because every site has at most four factors and every frame is a
4-design (cut lemma §5), so (P) and the window estimate (proved for the continuous model with arbitrary unit pins)
should carry over; the box-gap argument (MOSPROOF) must then work with site-dependent finite alphabets and the
2×2 cell blocking without translation invariance (MOSPROOF says its Theorem 6.3 needs none if coupling bounds hold
at every translate). Check every place where parity, bipartiteness, translation invariance, the specific frames,
or the sublattice rotation is used (§§1–8, appendices), including Lemma 4.1 (box/cell identification, its parity
remark), the frame weights bound γ₊ and the finite-energy constant, Theorem QD's orientation/sign conventions
(c_x), and small-size issues (L or N = 3, ℓ + 1 = L). If a different route is simpler (e.g. a quantum finite-size
criterion on boxes), use it and explain why.

**Deliverables** (write only in `/home/ubuntu/aklt/reports/STRENGTHEN-ALL/`):
- `proof.tex`: complete proofs of the new or changed statements, written as replacement/added manuscript text,
  section by section, with labels;
- `report.md`, first line `STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`: the strengthened statements; a table of
  every manuscript statement that changes (label, before, after, why); every place parity was used and how it is
  handled; what remains unproved, if anything; and the expected effect on a Lean formalization (new definitions or
  lemmas, statements that become simpler or harder).
You may run exact computations (Python with fractions or sympy) to check claims about the frames (design property,
disjointness, the minimum weight). At most 8 cores. Do not launch sub-agents. Do not stop before both files exist.
