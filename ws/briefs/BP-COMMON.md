
## Blueprint architect brief (common part)

**Context.** We formalize to Palomar standards (kernel-checked, no hypotheses) the streamlined proof that the
spin-2 AKLT Hamiltonian on the square-lattice torus has a unique ground state (all L, N ≥ 3) and a uniform gap (all
L, N ≥ L₀). The statement layer is in your worktree: `AKLT/Challenge/` (frozen headline), `AKLT/Defs/` (shared
definitions) and `AKLT/Blueprint/Top/` (one closed `…Statement : Prop` per interface result, with the proved top
assembly `mainV2_of_parts`). The revision plan with the exact LaTeX statements is
`/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` (labels in the Top docstrings). Generic proved libraries:
`AKLT/Gen/Bellman`, `AKLT/Gen/Gram`, `AKLT/Gen/Packed`; vendored donors `AKLT/Vendor/` with the reuse map
`/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md`. The statement layer is under fidelity review in parallel: if
you find a Top or Defs declaration that is false, unprovable as stated, ill-typed for its purpose, or different
from the paper, do NOT edit it — report it precisely (with a counterexample or the paper text) and propose a
`…V2` replacement in your own directory, then build on your V2.

**Your job is the blueprint of your part, not the proofs.** Deliver, in your directory:
1. `Nodes*.lean`: closed leaf statements `def <Name>Statement : Prop` covering every step of the paper proof of your
   targets, each small enough for one writer (≤ ~400 lines of Lean proof, 1–2 hours); split hard steps a second
   time; give each a docstring with the paper label/line and the idea of the proof. Add definitions you need.
2. `Assembly.lean`: PROVED theorems deriving each of your target Top statements from your leaf statements (and
   from other parts' Top statements where the paper uses them) — every hypothesis a closed Prop.
3. Proofs of leaves that are immediate (a few lines); leave the rest open.
4. `leaves.json` in your report directory: for each open leaf: Lean name, module, paper label, difficulty
   (easy/medium/hard), dependencies (other leaves it may use as hypotheses are NOT allowed — leaves are closed;
   list instead the definitions and library lemmas it needs), and a suggested proof route with donor/reuse pointers.
5. A trap check of every leaf: missing premises (the conclusion must follow from the hypotheses stated IN the leaf),
   vacuity, empty/degenerate cases, coercions, `Finset` vs `Fintype` sums, `ℕ` subtraction, division by zero,
   instance arguments silently dropped.
Report first line `STATUS: COMPLETE | PARTIAL (reason)`, then the node table (leaf → paper label → difficulty),
`#print axioms` of every assembly theorem, the list of Top/Defs problems found, and the ORCH-SUMMARY.
