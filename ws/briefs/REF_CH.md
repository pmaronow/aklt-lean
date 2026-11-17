# REF_CH — does a Lean statement file say what a paper says?

Paper: `/home/ubuntu/aklt/manuscript-v2` ("The spectral gap of the spin-2 AKLT model on the square lattice";
`main.tex`, `sec1-result.tex` for the main theorem and the model, `sec2-moments.tex`, `sec6-walks.tex` and
`sec7-recursion.tex` for the walk expansion, the local patterns, the trail kernel and the two finite inputs the
paper calls (H1) and (H3) [the latter with a subscript], `sec8-inputs.tex` for how the inputs are stated).
Lean file: `/home/ubuntu/aklt/repo/palomar/Challenge.lean` (imports Mathlib only). It defines the model and the
objects needed, states two propositions intended to be the paper's inputs (H1) and (H3), and one theorem
`aklt_gap_of_inputs` (its proof is a placeholder by convention; ignore that) intended to say: if (H1) and (H3)
hold then the paper's main theorem holds.

Task (read-only; write only your report): read the Lean file as mathematics and compare it with the paper,
definition by definition and clause by clause.
1. The conclusion: is it exactly the paper's main theorem (the Hamiltonian, the torus, the ground space, the
   uniform gap, the quantifiers and ranges of L, N, the constants)? Is anything weaker, stronger, vacuous or
   differently quantified? Check degenerate cases (small sizes, empty types, zero denominators, coercions,
   `Real`/`ℚ`/`ℕ` subtraction and division conventions) that could make the Lean statement mean something else.
2. Each premise: is it exactly the paper's input as the paper's proof uses it — every object (patterns, slots,
   fields, laws, pins; trails, types, kernel, weights, ordering, cutoffs) defined as in the paper, every constant
   equal, every quantifier in the right place? Would a premise be unsatisfiable (making the theorem vacuous) or
   trivially true? State for each whether the Lean premise is equivalent to, weaker than, or stronger than the
   paper's statement, with the reasoning.
3. Anything in the file a reader could be misled by (names, comments, definitions that silently differ from
   their documented meaning).
Report `/home/ubuntu/aklt/reports/REF_CH/report.md`: first line
`VERDICT: FAITHFUL | FAITHFUL WITH REMARKS | MISMATCH`, then findings by severity (Fatal / Major / Minor) with
Lean line numbers, the paper location, what differs and what would fix it; then a table mapping every Lean
definition and proposition to the paper's statement (file, label or line).
