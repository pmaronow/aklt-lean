# H1TREE_PROOF — write the complete proof of a reduction lemma for the paper

**Context.** Paper `/home/ubuntu/aklt/manuscript-v2` ("The spectral gap of the spin-2 AKLT model on the square
lattice"; `main.tex`, `sec6-walks.tex` defines the local passage, the departure types and the input (H1);
`sec8-inputs.tex` and `app-input-contracts.tex` state how (H1) is at present verified: a finite catalogue of 7,962
local patterns with one operator inequality each). A proposed replacement of that finite input is described in
`/home/ubuntu/aklt/reports/MATH_FIT/report.md`, sections "Selected H1 replacement: 38 universal trees", "Why these
trees cover every actual local passage", "The small mean and scalar inputs" and "Modified closing argument", with
data in `/home/ubuntu/aklt/reports/MATH_FIT/data/` (`cores_universal_final.json`, `universal_certificates.jsonl`,
`universal_mean_checks.json`, `mean_unit_pair.json`, `closed_boxes.json`) and programs in `programs/`. In short:
after integrating the arrival site with a positive splitting, bounding conditional means of corner spins by small
balls, expanding D laws convexly and discarding common positive factors, every actual local passage is claimed to
be dominated by one of 38 path-shaped models ("H1-tree"): for each model and all unit field directions,
`Zcur ≥ c_type · Znext` with the paper's two constants unchanged.

**Task.** Write this as mathematics a referee can check line by line, working from the PAPER'S definitions (not
from the catalogue):
1. Definitions: the models (vertices with U/D law, marks, field radii, mean vertices), `Z`, `Cij`, `Zcur`,
   `Znext`; the statement **H1-tree** as a finite list of inequalities; the exact finite inputs that certify it
   (the mean bounds with their Bernstein-coefficient checks, the scalar quadratic tests, the sector matrices with
   Gram/residual witnesses) each as a precise lemma with what is checked by computer.
2. The reduction theorem: H1-tree implies the conclusion of (H1) exactly as sec6 uses it (for every actual
   non-exceptional U departure, with arbitrary pins and outside spins, `Z_E^τ ≥ c_type Z_{E+}^τ`). Give the full
   case analysis — which sites are integrated in which order, every positive representation with its weights,
   every mean bound invoked with its hypotheses verified (number of fields at the site, their radii), the
   treatment of pins (which sites can carry pins, why D sites cannot), the correlation-preserving case, why
   the weights of every convex decomposition are the same for the current and the next configuration, and why
   enlarging radii/adding zero fields/identifying isomorphic paths is legitimate. Every claim must be proved or
   referred to a numbered statement of the paper.
3. Wherever the description in the report is incomplete, ambiguous or wrong against the paper's definitions, say
   so explicitly and repair it if you can; if a case is not covered by the 38 models, or an inequality used is
   false, give the precise configuration. Use the programs/data to test doubtful steps numerically (e.g. random
   actual patterns against the chain of inequalities), and say what you tested. Do not assume the claim is true.
Deliver `/home/ubuntu/aklt/reports/H1TREE_PROOF/h1tree.tex` (a self-contained LaTeX section with numbered
definitions, lemmas, proofs; compile it with a minimal wrapper to check it builds) and `report.md` with first line
`VERDICT: PROVED (complete written proof) | PROVED WITH REPAIRS (list) | GAP (list) | FALSE (counterexample)`,
followed by the list of repairs/gaps and of computer-checked finite inputs with their sizes. Write only under
`/home/ubuntu/aklt/reports/H1TREE_PROOF`. Up to 4 CPU-heavy processes. This task was issued by the orchestrator
(Fable); write the proof yourself.
