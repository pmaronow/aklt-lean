# H3LINE_PROOF — write the complete proof of a new finite-to-global certificate for the paper

**Context.** Paper `/home/ubuntu/aklt/manuscript-v2` ("The spectral gap of the spin-2 AKLT model on the square
lattice"): `sec7-recursion.tex` (response kernel, types, prefix ordering, the inequality `M₁h ≤ ρ₀h`, renewal),
`sec8-inputs.tex` and Appendix C (`app-*.tex`: the input (H3′): a stationary Bellman supersolution on a radius-70
square for a memory-ten quotient automaton, exact prefixes of length 12, and the lemma turning the finite check
into a bound for all trails). A proposed replacement is described in `/home/ubuntu/aklt/reports/MATH_FIT/report.md`,
sections "Selected H3 replacement: line potentials plus a small patch", "Optional removal of the separate H2 input",
"Modified closing argument" and "Kernel cost…", with data/programs/logs under
`/home/ubuntu/aklt/reports/MATH_FIT/{data,programs,logs}`: witness `h=(1,6/5)`, `ρ₀=967725/10⁶`, four tilted
vectors `z_σ` with ratio `r=12/13`, two shared line arrays on `|k|≤70` extended by exponential caps, the global
potential `F∞ = min` of the two line potentials, and for each of five first-direction cases a patch on
`[-20,20]²` with `0 ≤ U ≤ F∞`, plus exact prefix evaluation of length 12.

**Task.** Write this as mathematics a referee can check line by line, working from the PAPER'S definitions:
1. Definitions and the exact finite statement **H3-line** (every array, scale, rounding direction, every finite
   inequality that is checked, including caps, terminals, boundary rows, the prefix sums and their ordering).
2. The theorem: H3-line implies `M₁h ≤ ρ₀h` for the true-trail kernel exactly as Section 7 uses it. Prove every
   step: the tilted free inequality ⇒ exponential tails are free supersolutions beyond radius 70 (with the
   rational tilt coefficients and the ceiling/floor rounding handled explicitly); the line arrays are
   one-coordinate supersolutions and why a function of one coordinate satisfies the two-dimensional free row;
   `T(min(f,g)) ≤ min(Tf,Tg)` and the choice of minimizing line at C/D rows with coordinate zero; `F∞ ≥` the
   terminal reward; the patch-to-global step (rows inside the patch with `F∞` substituted outside; rows outside by
   monotonicity) — check carefully what happens at the patch boundary, at the centre/target, with the permanent
   initial-edge/site rules and with the first-direction split; the finite-horizon induction giving every suffix
   bound; the exact prefix ordering argument with the new `h`; and the resulting constants in the closing
   argument (state the modified inequalities of Section 7 with every constant explicit).
3. Wherever the description in the report is incomplete, ambiguous or wrong against the paper's definitions, say
   so and repair it if you can; if a step fails, give the precise obstruction. Test doubtful steps numerically
   with the programs/data (and say what you tested). Do not assume the claim is true. Also state exactly which
   parts of the present Appendix C remain valid and which are replaced.
Deliver `/home/ubuntu/aklt/reports/H3LINE_PROOF/h3line.tex` (self-contained LaTeX section, compiled with a minimal
wrapper), an exact replay program of the finite statement written from your text (it may reuse the data files but
not the logic of the existing checkers), and `report.md` with first line
`VERDICT: PROVED (complete written proof) | PROVED WITH REPAIRS (list) | GAP (list) | FALSE (counterexample)`,
then repairs/gaps and a table of the finite inputs with sizes (rows, value widths, counts). Write only under
`/home/ubuntu/aklt/reports/H3LINE_PROOF`. Up to 8 CPU-heavy processes and 40 GB RAM. This task was issued by the
orchestrator (Fable); write the proof yourself.
