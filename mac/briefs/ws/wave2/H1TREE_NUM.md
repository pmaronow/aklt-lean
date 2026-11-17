# H1TREE_NUM — independent numerical examination of a claimed finite reduction

**Setting.** Paper `/home/ubuntu/aklt/manuscript-v2` (`sec6-walks.tex`: local passage, departure types, input (H1)
with constants c_s = 961/1000 and c_t = 187/200; `sec8-inputs.tex`, `app-input-contracts.tex`: the finite
catalogue of 7,962 local patterns, data in `/home/ubuntu/aklt/data/h1` and `/home/ubuntu/aklt/compfeas`).
A document `/home/ubuntu/aklt/reports/MATH_FIT/report.md` (sections on "H1 replacement") claims: every actual
local passage inequality of (H1) follows from the inequality `Zcur ≥ c_type · Znext` on a list of 38 path-shaped
models (`/home/ubuntu/aklt/reports/MATH_FIT/data/cores_universal_final.json`), and that these 38 inequalities hold
and are certified by listed exact data (`universal_certificates.jsonl`, `universal_mean_checks.json`,
`mean_unit_pair.json`).

**Task.** Examine these claims numerically with programs YOU write from the definitions (you may read the other
programs to understand file formats, but do not reuse their logic for the checks):
1. For each of the 38 models: implement `Z`, `Cij`, `Zcur`, `Znext` from the model description in the document,
   and (a) search hard for violations of `Zcur ≥ c·Znext` over unit field directions (many random starts +
   local optimisation; report the minimum of Zcur/Znext found per model and its margin to c); (b) verify the
   listed exact certificates in exact rational arithmetic with your own checker (mean-bound Bernstein
   coefficients, scalar tests, Gram/residual witnesses against matrices you reconstruct yourself).
2. For the reduction: sample actual local passages directly from the paper's definitions and from the 7,962
   catalogue (all of them if feasible, with random pins/outside spins/field directions, many samples each) and
   test (a) the target inequality itself, and (b) each intermediate inequality of the claimed reduction chain
   for that passage (the conditional means really lie in the claimed balls; the passage really maps to a listed
   model with fields within the listed radii). Report any passage not covered by a listed model, any mean outside
   its claimed ball, any violated intermediate step — with the explicit configuration.
3. Re-derive the count of models independently if you can (enumerate geometries under the stated rules) and
   compare with 38.
Report `/home/ubuntu/aklt/reports/H1TREE_NUM/report.md`: first line
`RESULT: NO VIOLATION FOUND | VIOLATION FOUND (where)`, then per-model table (minimum ratio found, margin, exact
certificate verified yes/no), the coverage test results with sample counts, and precise descriptions of anything
that failed or that you could not interpret. Write only under `/home/ubuntu/aklt/reports/H1TREE_NUM`. Up to 8
CPU-heavy processes and 30 GB RAM.
