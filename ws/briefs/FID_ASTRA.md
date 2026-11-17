# Fidelity review: do the Lean statements say what the paper says?

Materials (read-only), all under `/home/ubuntu/aklt/review/FID`:
- `manuscript/` — the paper "The spectral gap of the spin-2 AKLT model on the square lattice" (`main.tex`,
  `sec1-result.tex` … `sec8-inputs.tex`, appendices `app-*.tex`, and `main.pdf`). The main theorem and the model
  are in `sec1-result.tex`; the polynomial realization of the spin space in `sec3-quantum-frames.tex`; the walk
  expansion, local patterns and trails in `sec6-walks.tex`; the response kernel and recursion in
  `sec7-recursion.tex`; the three finite inputs, which the paper calls (H1), (H2) and (H3) with a subscript, in
  `sec6`–`sec8`.
- `lean/Challenge.lean` — a self-contained Lean 4 file (imports Mathlib only) that defines the model and states
  one theorem, intended to be the paper's main theorem. Its proof is a placeholder by convention; ignore that.
- `lean/Solution.lean` and `lean/comparator.json` — how the proof is attached to the Challenge statement.
- `lean/AKLT/Challenge/*.lean`, `lean/AKLT/Defs/*.lean`, `lean/AKLT/Blueprint/Top/Response.lean`,
  `lean/AKLT/Final/Inputs.lean` — the statement layer of the formalization: the same main theorem as stated
  inside the library, the definitions it uses, the Lean statements intended to be the paper's inputs
  (`H1Statement`, `H2Statement`, `H3Statement` and the definitions they unfold to), and the statement of the
  reduction theorem `main_of_inputs`.

Task. Read the Lean files as mathematics and compare them with the paper, definition by definition and clause by
clause. Decide for yourself; assume nothing about correctness.
1. THE CHALLENGE (most important). Is the theorem in `Challenge.lean` exactly the paper's main theorem? Check the
   lattice and its bonds, the local spin space and its inner product, the spin operators, the projection in the
   Hamiltonian, the Hamiltonian itself and its normalization, the valence-bond state, the ground-space claim, the
   gap claim, every quantifier and its range (sizes, parities, aspect ratios), and the constants. Hunt for ways
   the Lean statement could be weaker, stronger, vacuous or mean something else: degenerate sizes, empty types,
   junk values of division/subtraction/square root, coercions between ℕ, ℤ, ℚ, ℝ, ℂ, `Fin`/`ZMod` arithmetic,
   orientation and double counting of bonds on small tori, the convention of which argument the inner product is
   conjugate-linear in, whether "eigenvalue" means what the paper means, whether the stated state could be zero.
   For every definition in the file say what mathematical object it is and where the paper defines it.
2. CONSISTENCY INSIDE THE FORMALIZATION. Is the theorem stated in `Challenge.lean` the same statement as the
   library's own main statement (the one `Solution.lean` proves it from)? How does `Solution.lean` connect them,
   and is that connection a genuine identity of statements?
3. THE INPUTS. For each of `H1Statement`, `H2Statement`, `H3Statement` (follow the definitions down to Mathlib):
   is it the paper's corresponding input, with the same objects, constants, and quantifiers, as the paper's
   proof uses it? Equivalent, weaker, or stronger — with the reasoning. Could any be unsatisfiable or trivially
   true? And does the statement of `main_of_inputs` say what the paper's reduction says?
4. Anything a reader would be misled by: names, doc comments, or references to the paper that do not match what
   the definition is or where the paper states it.
Write your report to `/home/ubuntu/aklt/reports/FID_ASTRA/report.md`: first line `VERDICT: FAITHFUL | FAITHFUL WITH REMARKS | MISMATCH`; then
findings by severity (Fatal / Major / Minor), each with the Lean file and line, the paper location (file and
label or line), what differs, why it matters, and what would fix it; then a table mapping every definition and
statement you checked to the paper. Be concrete and complete; do not edit any file other than your report.
